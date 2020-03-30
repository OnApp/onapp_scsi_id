/*
 * Copyright (C) IBM Corp. 2003
 *
 * Author:
 *     Patrick Mansfield<patmans@us.ibm.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <sys/types.h>
#include <sys/ioctl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <scsi/sg.h>
#include <scsi/scsi.h>
#include <uuid/uuid.h>
#include <stdbool.h>
#include <linux/nvme_ioctl.h>
#include "nvme.h"

/*
 *  * Default 5 second timeout
 *   */
#define DEF_TIMEOUT     5000

#define SENSE_BUFF_LEN  32

/*
 * The request buffer size passed to the SCSI INQUIRY commands, use 254, 
 * as this is a nice value for some devices, especially some of the usb
 * mass storage devices.
 */
#define SCSI_INQ_BUFF_LEN       254

/*
 * SCSI INQUIRY vendor and model (really product) lengths.
 */
#define VENDOR_LENGTH   8
#define MODEL_LENGTH    16
#define REVISION_LENGTH 4

#define INQUIRY_CMD     0x12
#define INQUIRY_CMDLEN  6

#define PAGE_83	0x83
#define PAGE_80	0x80

/*
 * id type values of id descriptors. These are assumed to fit in 4 bits.
 */
#define SCSI_ID_VENDOR_SPECIFIC 0
#define SCSI_ID_T10_VENDOR      1
#define SCSI_ID_EUI_64          2
#define SCSI_ID_NAA             3
#define SCSI_ID_RELPORT         4
#define SCSI_ID_TGTGROUP        5
#define SCSI_ID_LUNGROUP        6
#define SCSI_ID_MD5             7
#define SCSI_ID_NAME            8

/*
 * Supported NAA values. These fit in 4 bits, so the "don't care" value
 * cannot conflict with real values.
 */
#define SCSI_ID_NAA_DONT_CARE           0xff
#define SCSI_ID_NAA_IEEE_REG            5
#define SCSI_ID_NAA_IEEE_REG_EXTENDED   6

/*
 * Supported Code Set values.
 */
#define SCSI_ID_BINARY  1
#define SCSI_ID_ASCII   2

struct scsi_id_search_values
{
	u_char id_type;
	u_char naa_type;
	u_char code_set;
};

/*
 * A priority based list of id, naa, and binary/ascii for the identifier
 * descriptor in VPD page 0x83.
 *
 * Brute force search for a match starting with the first value in the
 * following id_search_list. This is not a performance issue, since there
 * is normally one or some small number of descriptors.
 */
static const struct scsi_id_search_values id_search_list[] = { {
		SCSI_ID_TGTGROUP, SCSI_ID_NAA_DONT_CARE, SCSI_ID_BINARY }, {
		SCSI_ID_NAA, SCSI_ID_NAA_IEEE_REG_EXTENDED, SCSI_ID_BINARY }, {
		SCSI_ID_NAA, SCSI_ID_NAA_IEEE_REG_EXTENDED, SCSI_ID_ASCII }, {
		SCSI_ID_NAA, SCSI_ID_NAA_IEEE_REG, SCSI_ID_BINARY }, { SCSI_ID_NAA,
		SCSI_ID_NAA_IEEE_REG, SCSI_ID_ASCII },
/*
 * Devices already exist using NAA values that are now marked
 * reserved. These should not conflict with other values, or it is
 * a bug in the device. As long as we find the IEEE extended one
 * first, we really don't care what other ones are used. Using
 * don't care here means that a device that returns multiple
 * non-IEEE descriptors in a random order will get different
 * names.
 */
{ SCSI_ID_NAA, SCSI_ID_NAA_DONT_CARE, SCSI_ID_BINARY }, { SCSI_ID_NAA,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_ASCII }, { SCSI_ID_EUI_64,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_BINARY }, { SCSI_ID_EUI_64,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_ASCII }, { SCSI_ID_T10_VENDOR,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_BINARY }, { SCSI_ID_T10_VENDOR,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_ASCII }, { SCSI_ID_VENDOR_SPECIFIC,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_BINARY }, { SCSI_ID_VENDOR_SPECIFIC,
		SCSI_ID_NAA_DONT_CARE, SCSI_ID_ASCII }, };

/*
 * NVME specific defines
 */
#define NVME_ADMIN_CMD_OPCODE_IDENTIFY 0x06

static const char hex_str[] = "0123456789abcdef";
static int serial_printed = 0;

static int check_scsi_serial(unsigned char *buf,
		const struct scsi_id_search_values *id_search, char *serial,
		const char *vendor, const char *model)
{
	int i, j, s, len;
	/*
	 * ASSOCIATION must be with the device (value 0)
	 * or with the target port for SCSI_ID_TGTPORT
	 */
	if ((buf[1] & 0x30) == 0x10) {
		if (id_search->id_type != SCSI_ID_TGTGROUP) {
			return -1;
		}
	}
	else if ((buf[1] & 0x30) != 0) {
		return -1;
	}

	if ((buf[1] & 0x0f) != id_search->id_type) {
		return -1;
	}

	/*
	 * Possibly check NAA sub-type.
	 */
	if ((id_search->naa_type != SCSI_ID_NAA_DONT_CARE)
			&& (id_search->naa_type != (buf[4] & 0xf0) >> 4)) {
		return -1;
	}

	/*
	 * Check for matching code set - ASCII or BINARY.
	 */
	if ((buf[0] & 0x0f) != id_search->code_set) {
		return -1;
	}

	/*
	 * buf[3]: identifier length
	 */
	len = buf[3];
	if ((buf[0] & 0x0f) != SCSI_ID_ASCII) {
		/*
		 * If not ASCII, use two bytes for each binary value.
		 */
		len *= 2;
	}

	/*
	 * Add one byte for the NUL termination, and one for the id_type.
	 */
	len += 2;
	if (id_search->id_type == SCSI_ID_VENDOR_SPECIFIC) {
		len += VENDOR_LENGTH + MODEL_LENGTH;
	}

	if (id_search->id_type == SCSI_ID_TGTGROUP) {
		unsigned int group;

		group = ((unsigned int) buf[6] << 8) | buf[7];
		printf ("Target: %x\n", group);
		return -1;
	}

	if (id_search->id_type == SCSI_ID_VENDOR_SPECIFIC) {
		strncpy (serial + 1, vendor, VENDOR_LENGTH);
		strncat (serial + 1, model, MODEL_LENGTH);
		s = j = strlen (serial);
	}
	else if (id_search->id_type == SCSI_ID_NAA) {
		serial[0] = hex_str[id_search->id_type];
		s = j = 1;
	}
	else {
		return -1;
	}
	i = 4; /* offset to the start of the identifier */
	if ((buf[0] & 0x0f) == SCSI_ID_ASCII) {
		/*
		 * ASCII descriptor.
		 */
		while (i < (4 + buf[3]))
			serial[j++] = buf[i++];
	}
	else {
		/*
		 * Binary descriptor, convert to ASCII, using two bytes of
		 * ASCII for each byte in the buf.
		 */
		while (i < (4 + buf[3])) {
			serial[j++] = hex_str[(buf[i] & 0xf0) >> 4];
			serial[j++] = hex_str[buf[i] & 0x0f];
			i++;
		}
	}

	return 0;
}

static int make_scsi_request(int fd, int evpd, int pageno, unsigned char *buf,
		size_t buflen)
{
	unsigned char inq_cmd[] = { INQUIRY_CMD, evpd, pageno, 0, buflen, 0 };
	unsigned char sense[SENSE_BUFF_LEN];
	struct sg_io_hdr io_hdr;

	memset (buf, 0, buflen);
	memset (&io_hdr, 0, sizeof(struct sg_io_hdr));
	io_hdr.interface_id = 'S';
	io_hdr.cmd_len = sizeof(inq_cmd);
	io_hdr.mx_sb_len = sizeof(sense);
	io_hdr.dxfer_direction = SG_DXFER_FROM_DEV;
	io_hdr.dxfer_len = buflen;
	io_hdr.dxferp = buf;
	io_hdr.cmdp = inq_cmd;
	io_hdr.sbp = sense;
	io_hdr.timeout = DEF_TIMEOUT;

	if (ioctl (fd, SG_IO, &io_hdr) == -1) {
		return -1;
	}
	return 0;
}

static int make_nvme_request(int fd, struct nvme_id_ctrl* ctrl, struct nvme_id_ns* ns)
{
	int nsid, ret = 0;
	struct nvme_admin_cmd cmd;

	if (ctrl == NULL || ns == NULL) {
		return -1;
	}
	memset(&cmd, 0, sizeof(cmd));
	memset(ctrl, 0, sizeof(struct nvme_id_ctrl));
	cmd.opcode = NVME_ADMIN_CMD_OPCODE_IDENTIFY;
	cmd.nsid = 0;
	cmd.addr = (unsigned long)(ctrl);
	cmd.data_len = 4096;
	cmd.cdw10 = 1;
	ret = ioctl(fd, NVME_IOCTL_ADMIN_CMD, &cmd);
	if (ret != 0) {
		return ret;
	}
	nsid = ioctl(fd, NVME_IOCTL_ID);
	memset(ns, 0, sizeof(struct nvme_id_ns));
	memset(&cmd, 0, sizeof(cmd));
	cmd.opcode = NVME_ADMIN_CMD_OPCODE_IDENTIFY;
	cmd.nsid = nsid;
	cmd.addr = (unsigned long)(ns);
	cmd.data_len = 4096;
	cmd.cdw10 = 0;
	ret = ioctl(fd, NVME_IOCTL_ADMIN_CMD, &cmd);
	if (ret != 0) {
		return ret;
	}
	return 0;
}

static void replace_whitespace(const char *str, char *to, size_t len)
{
	size_t i, j;

	/* strip trailing whitespace */
	len = strnlen (str, len);
	while (len && isspace (str[len - 1]))
		len--;

	/* strip leading whitespace */
	i = 0;
	while (isspace (str[i]) && (i < len))
		i++;

	j = 0;
	while (i < len) {
		/* substitute multiple whitespace with a single '_' */
		if (isspace (str[i])) {
			while (isspace (str[i]))
				i++;
			to[j++] = '_';
		}
		to[j++] = str[i++];
	}
	to[j] = '\0';
}

static int is_whitelisted(char c, const char *white)
{
	if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z')
			|| (c >= 'a' && c <= 'z') || strchr ("#+-.:=@_", c) != NULL
			|| (white != NULL && strchr (white, c) != NULL)) {
		return 1;
	}
	return 0;
}

/* allow chars in whitelist, plain ascii, hex-escaping and valid utf8 */
static int replace_chars(char *str, const char *white)
{
	size_t i = 0;
	int replaced = 0;

	while (str[i] != '\0') {
		int len;

		if (is_whitelisted (str[i], white)) {
			i++;
			continue;
		}

		/* accept hex encoding */
		if (str[i] == '\\' && str[i + 1] == 'x') {
			i += 2;
			continue;
		}

		/* if space is allowed, replace whitespace with ordinary space */
		if (isspace (str[i]) && white != NULL && strchr (white, ' ') != NULL) {
			str[i] = ' ';
			i++;
			replaced++;
			continue;
		}

		/* everything else is replaced with '_' */
		str[i] = '_';
		i++;
		replaced++;
	}

	return replaced;
}

static int print_all = 0;

int main(int argc, char **argv)
{
	int i, j, fd, page = 0, len;
	char *dev, vendor[VENDOR_LENGTH + 1], model[MODEL_LENGTH + 1],
			revision[REVISION_LENGTH + 1];
	unsigned char buf[SCSI_INQ_BUFF_LEN];
	char serial[SCSI_INQ_BUFF_LEN], unit_serial[SCSI_INQ_BUFF_LEN];
	struct nvme_id_ctrl  ctrl;
	struct nvme_id_ns ns;

	memset (serial, 0, sizeof(serial));
	memset (unit_serial, 0, sizeof(unit_serial));

	if (argc < 2) {
		exit (EXIT_FAILURE);
	}

	for (i = 1; i < argc; i++) {
		if (*argv[i] == '-') {
			/* Skip args with - at the begin */
			if (!strcmp(argv[i], "-A"))
				print_all = 1;
			continue;
		}
		else {
			dev = argv[i];
			break;
		}
	}

	fd = open (dev, O_RDONLY);
	if (fd == -1) {
		perror ("open failed");
		exit (EXIT_FAILURE);
	}

	/* Make page 0 request to get vendor data */
	if (!make_scsi_request (fd, 0x0, 0x0, buf, sizeof(buf))) {
		if (buf[1] != 0x0 && buf[1] != 0x80 && buf[1] != 0x83) {
			printf ("invalid page: %x\n", (int) buf[1]);
			goto try_nvme;
		}

		memcpy (vendor, buf + 8, VENDOR_LENGTH);
		vendor[8] = '\0';
		memcpy (model, buf + 16, MODEL_LENGTH);
		model[16] = '\0';
		memcpy (revision, buf + 32, REVISION_LENGTH);
		revision[4] = '\0';
	}

	/* Get the best supported page */
	/* Make page 0 request to get available pages */
	if (!!make_scsi_request (fd, 0x1, 0x0, buf, sizeof(buf))) {
		perror ("ioctl failed.");
		goto try_nvme;
	}
	for (i = 4; i <= buf[3] + 3; i++) {
		if (buf[i] == PAGE_83) {
			page = PAGE_83;
		}
	}

	if (page == 0) {
		for (i = 4; i <= buf[3] + 3; i++) {
			if (buf[i] == PAGE_80) {
				page = PAGE_80;
			}
		}
	}
	/* Make page 83 request to get serial */
	if (page == PAGE_83) {
		/* Get unit serial by page80 request */
		make_scsi_request (fd, 0x1, PAGE_80, buf, sizeof(buf));
		len = buf[3];
		memcpy (unit_serial, &buf[4], len);
		make_scsi_request (fd, 0x1, PAGE_83, buf, sizeof(buf));
		if (buf[1] != page) {
			printf ("invalid page: %x\n", (int) buf[1]);
			goto try_nvme;
		}
		/*
		 * Search for a match in the prioritized id_search_list - since WWN ids
		 * come first we can pick up the WWN in check_fill_0x83_id().
		 */
		for (i = 0; i < sizeof(id_search_list) / sizeof(id_search_list[0]);
			i++) {
			/*
			 * Examine each descriptor returned. There is normally only
			 * one or a small number of descriptors.
			 */
			for (j = 4; j <= (unsigned int) buf[3] + 3; j += buf[j + 3] + 4) {
				memset (serial, 0, sizeof(serial));
				if (check_scsi_serial (&buf[j], &id_search_list[i], serial,
					vendor, model) == 0) {
					if (print_all) {
						replace_whitespace (serial, serial, sizeof(serial));
						replace_chars (serial, NULL);
						printf ("ID_SERIAL_%d=%s\n", i, serial);
						continue;
					}
					goto out;
				}
			}
		}
	} else {
		/* Parse page80 simply */
		len = buf[3];
		serial[0] = 'S';
		strncpy (serial + 1, vendor, VENDOR_LENGTH);
		strncat (serial + 1, model, MODEL_LENGTH);
		i = strlen (serial);
		for (j = 4; j < len + 4; j++, i++) {
			serial[i] = buf[j];
		}
	}
	try_nvme:
	if (strnlen(serial, SCSI_INQ_BUFF_LEN) < 2 && strnlen(unit_serial, SCSI_INQ_BUFF_LEN) < 2) {
		// assuming NVME
		if (make_nvme_request(fd, &ctrl, &ns) != 0) {
			perror ("ioctl failed.");
			exit (EXIT_FAILURE);
		}
		snprintf(vendor, sizeof(vendor), "%#x", ctrl.vid);
		snprintf(revision, sizeof(revision), "%4d", ctrl.vid);
		memcpy(serial, ctrl.sn, sizeof(ctrl.sn));
		serial[sizeof(serial)] = '\0';
		memcpy(model, ctrl.mn, sizeof(model));
		model[sizeof(model)] = '\0';
		snprintf(unit_serial, sizeof(unit_serial), "%x%x%x%x%x%x%x%x", ns.eui64[0],
			ns.eui64[1], ns.eui64[2], ns.eui64[3], ns.eui64[4], ns.eui64[5], ns.eui64[6],
			ns.eui64[7]);
	}
	out: replace_whitespace (vendor, vendor, sizeof(vendor));
	replace_chars (vendor, NULL);
	replace_whitespace (model, model, sizeof(model));
	replace_chars (model, NULL);
	replace_whitespace (revision, revision, sizeof(revision));
	replace_chars (revision, NULL);
	printf ("ID_VENDOR=%s\n", vendor);
	printf ("ID_REVISION=%s\n", revision);
	printf ("ID_MODEL=%s\n", model);

	if (!print_all) {
		replace_whitespace (serial, serial, sizeof(serial));
		replace_chars (serial, NULL);
		printf ("ID_SERIAL=%s\n", serial);
	}

	if (unit_serial[0] != '\0') {
		replace_whitespace (unit_serial, unit_serial, sizeof(unit_serial));
		replace_chars (unit_serial, NULL);
		printf ("ID_SCSI_SERIAL=%s\n", unit_serial);
	}

	return 0;
}
