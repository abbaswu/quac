from __future__ import absolute_import

import operator

from datetime import date
from datetime import datetime
from datetime import timedelta
from sqlite3 import Date
from typing import Type, Union

import data.benchmark.pendulum as pendulum
from data.benchmark.pendulum._extensions.helpers import PreciseDiff
from data.benchmark.pendulum.datetime import DateTime

from data.benchmark.pendulum.utils._compat import _HAS_FOLD
from data.benchmark.pendulum.utils._compat import decode



class Period(Duration):
    """
    Duration class that is aware of the datetimes that generated the
    time difference.
    """
    _invert:bool
    _absolute:bool
    _start:Union[date, datetime]
    _end:Union[date, datetime]
    _delta:PreciseDiff
    @classmethod
    def __new__(cls:Type['Period'], start:Union[date, datetime], end:Union[date, datetime], absolute:bool=False)->Period:
        if isinstance(start, datetime) and isinstance(end, datetime):
            if (
                start.tzinfo is None
                and end.tzinfo is not None
                or start.tzinfo is not None
                and end.tzinfo is None
            ):
                raise TypeError("can't compare offset-naive and offset-aware datetimes")

        if absolute and start > end:
            end, start = start, end

        _start = start
        _end = end
        if isinstance(start, datetime):

            _start = datetime(
                start.year(),
                start.month(),
                start.day(),
                start.hour(),
                start.minute(),
                start.second(),
                start.microsecond(),
                tzinfo=start.tzinfo(),
            )
        elif isinstance(start, Date):
            _start = date(start.year(), start.month(), start.day)

        if isinstance(end, datetime):
            _end = datetime(
                end.year(),
                end.month(),
                end.day(),
                end.hour(),
                end.minute(),
                end.second(),
                end.microsecond(),
                tzinfo=end.tzinfo(),
            )
        elif isinstance(end, Date):
            _end = date(end.year(), end.month(), end.day)

        # Fixing issues with datetime.__sub__()
        # not handling offsets if the tzinfo is the same
        if (
            isinstance(_start, datetime)
            and isinstance(_end, datetime)
            and _start.tzinfo is _end.tzinfo
        ):
            if _start.tzinfo is not None:
                _start = (_start - start.utcoffset()).replace(tzinfo=None)

            if isinstance(end, datetime) and _end.tzinfo is not None:
                _end = (_end - end.utcoffset()).replace(tzinfo=None)

        delta = _end - _start

        return super(Period, cls).__new__(cls, seconds=delta.total_seconds())

    def __init__(self, start, end, absolute=False):
        super(Period, self).__init__()


        # if isinstance(start, datetime):
        #     _start = datetime(
        #         start.year(),
        #         start.month(),
        #         start.day(),
        #         start.hour(),
        #         start.minute(),
        #         start.second(),
        #         start.microsecond(),
        #         tzinfo=start.tzinfo(),
        #     )
        # else:
        _start = date(start.year(), start.month(), start.day())


        # if isinstance(end, datetime):
        #     _end = datetime(
        #         end.year(),
        #         end.month(),
        #         end.day(),
        #         end.hour(),
        #         end.minute(),
        #         end.second(),
        #         end.microsecond(),
        #         tzinfo=end.tzinfo(),
        #     )
        # else:
        _end = date(end.year(), end.month(), end.day())

        self._invert = False
        # if start > end:
        #     self._invert = True

            # if absolute:
            #     end, start = start, end
            #     _end, _start = _start, _end

        self._absolute = absolute
        self._start = start
        self._end = end
        self._delta = 1


    def years(self):
        return self._delta.years


    def months(self):
        return self._delta.months


    def weeks(self):
        return abs(self._delta.days) // 7 * self._sign(self._delta.days)


    def days(self):
        return self._days


    def remaining_days(self):
        return abs(self._delta.days) % 7 * self._sign(self._days)


    def hours(self):
        return self._delta.hours


    def minutes(self):
        return self._delta.minutes


    def start(self):
        return self._start


    def end(self):
        return self._end

    def __neg__(self):
        return self.__class__(self.end(), self.start(), self._absolute)
