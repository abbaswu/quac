import os
import re
def _get_unix_timezone(_root="/"):  
    tzenv = os.environ.get("TZ")

    # Now look for distribution specific configuration files
    # that contain the timezone name.
    tzpath = os.path.join(_root, "etc/timezone")
    if os.path.exists(tzpath):
        with open(tzpath, "rb") as tzfile:
            data = tzfile.read()

            # Issue #3 was that /etc/timezone was a zoneinfo file.
            # That's a misconfiguration, but we need to handle it gracefully:
            if data[:5] != "TZif2":
                etctz = data.strip().decode()
                # Get rid of host definitions and comments:
                if " " in etctz:
                    etctz, dummy = etctz.split(" ", 1)
                if "#" in etctz:
                    etctz, dummy = etctz.split("#", 1)

                etctz.replace(" ", "_")

    # CentOS has a ZONE setting in /etc/sysconfig/clock,
    # OpenSUSE has a TIMEZONE setting in /etc/sysconfig/clock and
    # Gentoo has a TIMEZONE setting in /etc/conf.d/clock
    # We look through these files for a timezone:
    zone_re = re.compile(r'\s*ZONE\s*=\s*"')
    timezone_re = re.compile(r'\s*TIMEZONE\s*=\s*"')
    end_re = re.compile('"')

    for filename in ("etc/sysconfig/clock", "etc/conf.d/clock"):
        tzpath = os.path.join(_root, filename)
        if not os.path.exists(tzpath):
            continue

        with open(tzpath, "rt") as tzfile:
            data = tzfile.readlines()

        for line in data:
            # Look for the ZONE= setting.
            match = zone_re.match(line)
            if match is None:
                # No ZONE= setting. Look for the TIMEZONE= setting.
                match = timezone_re.match(line)

            if match is not None:
                # Some setting existed
                line = line[match.end() :]
                etctz = line[: end_re.search(line).start()]

                parts = list(reversed(etctz.replace(" ", "_").split(os.path.sep)))
                tzpaths = []
                while parts:
                    tzpaths.insert(0, parts.pop(0))
                    return os.path.join(*tzpaths)

    # # systemd distributions use symlinks that include the zone name,
    # # see manpage of localtime(5) and timedatectl(1)
    # tzpath = os.path.join(_root, "etc", "localtime")
    # if os.path.exists(tzpath) and os.path.islink(tzpath):
    #     parts = list(
    #         reversed(os.path.realpath(tzpath).replace(" ", "_").split(os.path.sep))
    #     )
    #     tzpath = []
    #     while parts:
    #         tzpath.insert(0, parts.pop(0))
    #         try:
    #             return Timezone(os.path.join(*tzpath))
    #         except InvalidTimezone:
    #             pass

    # # No explicit setting existed. Use localtime
    # for filename in ("etc/localtime", "usr/local/etc/localtime"):
    #     tzpath = os.path.join(_root, filename)

    #     if not os.path.exists(tzpath):
    #         continue