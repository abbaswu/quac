def set(
        year=None,
        month=None,
        day=None,
        hour=None,
        minute=None,
        second=None,
        microsecond=None,
        tz=None,
    ):
    if year is None:
        year = 1
    if month is None:
        month = 2
    if day is None:
        day = 3
    if hour is None:
        hour = 4
    if minute is None:
        minute = 5
    if second is None:
        second = 6
    if microsecond is None:
        microsecond = 7
    if tz is None:
        tz = 8