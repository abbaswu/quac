from __future__ import absolute_import
from __future__ import division
from typing import Type
from datetime import timedelta

import data.benchmark.pendulum as pendulum

from data.benchmark.pendulum.utils._compat import PYPY
from data.benchmark.pendulum.utils._compat import decode

from .constants import SECONDS_PER_DAY
from .constants import SECONDS_PER_HOUR
from .constants import SECONDS_PER_MINUTE
from .constants import US_PER_SECOND


def _divide_and_round(a, b):
    """divide a by b and round result to the nearest integer

    When the ratio is exactly half-way between two integers,
    the even integer is returned.
    """
    # Based on the reference implementation for divmod_near
    # in Objects/longobject.c.
    q, r = divmod(a, b)
    # round up if either r / b > 0.5, or r / b == 0.5 and q is odd.
    # The expression r / b > 0.5 is equivalent to 2 * r > b if b is
    # positive, 2 * r < b if b negative.
    r *= 2
    greater_than_half = r > b if b > 0 else r < b
    if greater_than_half or r == b and q % 2 == 1:
        q += 1

    return q

class Duration(timedelta):
    """
    Replacement for the standard timedelta class.

    Provides several improvements over the base class.
    """

    _y:int = None
    _m:int = None
    _w:int = None
    _d:int = None
    _h:int = None
    _i:int = None
    _s:int = None
    _invert:int = None

    _total:int
    _microseconds:int
    _seconds:int
    _days:int 
    _remaining_days:int
    _weeks:int
    _months:int
    _years:int

    min:Duration
    max:Duration
    resolution:Duration
    def __new__(
        cls:Type[Duration],
        days:int=0,
        seconds:int=0,
        microseconds:int=0,
        milliseconds:int=0,
        minutes:int=0,
        hours:int=0,
        weeks:int=0,
        years:int=0,
        months:int=0,
    )->Duration:
        if not isinstance(years, int) or not isinstance(months, int):
            raise ValueError("Float year and months are not supported")

        self = timedelta.__new__(
            cls,
            days + years * 365 + months * 30,
            seconds,
            microseconds,
            milliseconds,
            minutes,
            hours,
            weeks,
        )

        # Intuitive normalization
        total = self.total_seconds() - (years * 365 + months * 30) * SECONDS_PER_DAY
        self._total = total

        m = 1
        if total < 0:
            m = -1

        self._microseconds = round(total % m * 1e6)
        self._seconds = abs(int(total)) % SECONDS_PER_DAY * m

        _days = abs(int(total)) // SECONDS_PER_DAY * m
        self._days = _days
        self._remaining_days = abs(_days) % 7 * m
        self._weeks = abs(_days) // 7 * m
        self._months = months
        self._years = years

        return self

    def total_minutes(self):
        return self.total_seconds() / SECONDS_PER_MINUTE

    def total_hours(self):
        return self.total_seconds() / SECONDS_PER_HOUR

    def total_days(self):
        return self.total_seconds() / SECONDS_PER_DAY

    def total_weeks(self):
        return self.total_days() / 7


    def total_seconds(self):
        days = 0

        if hasattr(self, "_years"):
            days += self._years * 365

        if hasattr(self, "_months"):
            days += self._months * 30

        if hasattr(self, "_remaining_days"):
            days += self._weeks * 7 + self._remaining_days
        else:
            days += self._days

        return int((
            (days * SECONDS_PER_DAY + self._seconds) * US_PER_SECOND
            + self._microseconds
        ) / US_PER_SECOND)


    def years(self):
        return self._years


    def months(self):
        return self._months


    def weeks(self):
        return self._weeks


    
    def days(self):
        return self._years * 365 + self._months * 30 + self._days


    def remaining_days(self):
        return self._remaining_days


    def hours(self):
        if self._h is None:
            seconds = self._seconds
            self._h = 0
            if abs(seconds) >= 3600:
                self._h = (abs(seconds) // 3600 % 24) * self._sign(seconds)

        return self._h


    def minutes(self):
        if self._i is None:
            seconds = self._seconds
            self._i = 0
            if abs(seconds) >= 60:
                self._i = (abs(seconds) // 60 % 60) * self._sign(seconds)

        return self._i


    def seconds(self):
        return self._seconds


    def remaining_seconds(self):
        if self._s is None:
            self._s = self._seconds
            self._s = abs(self._s) % 60 * self._sign(self._s)

        return self._s


    def microseconds(self):
        return self._microseconds


    def invert(self):
        if self._invert is None:
            self._invert = self.total_seconds() < 0

        return self._invert

    def in_weeks(self):
        return int(self.total_weeks())

    def in_days(self):
        return int(self.total_days())

    def in_hours(self):
        return int(self.total_hours())

    def in_minutes(self):
        return int(self.total_minutes())

    def in_seconds(self):
        return int(self.total_seconds())


 

    def _sign(self, value):
        if value < 0:
            return -1

        return 1

    def as_timedelta(self):
        """
        Return the interval as a native timedelta.

        :
        """
        return timedelta(seconds=self.total_seconds())

    # def __str__(self):
    #     return self.in_words()

    def __repr__(self):
        rep = "{}(".format(self.__class__.__name__)

        if self._years:
            rep += "years={}, ".format(self._years)

        if self._months:
            rep += "months={}, ".format(self._months)

        if self._weeks:
            rep += "weeks={}, ".format(self._weeks)

        if self._days:
            rep += "days={}, ".format(self._remaining_days)

        if self.hours():
            rep += "hours={}, ".format(self.hours())

        if self.minutes():
            rep += "minutes={}, ".format(self.minutes())

        if self.remaining_seconds():
            rep += "seconds={}, ".format(self.remaining_seconds())

        if self.microseconds():
            rep += "microseconds={}, ".format(self.microseconds())

        rep += ")"

        return rep.replace(", )", ")")

    def __add__(self, other):
        if isinstance(other, timedelta):
            return self.__class__(seconds=self.total_seconds() + other.total_seconds())

        return NotImplemented

    __radd__ = __add__

    def __sub__(self, other):
        if isinstance(other, timedelta):
            return self.__class__(seconds=self.total_seconds() - other.total_seconds())

        return NotImplemented

    def __neg__(self):
        return self.__class__(
            years=-self._years,
            months=-self._months,
            weeks=-self._weeks,
            days=-self._remaining_days,
            seconds=-self._seconds,
            microseconds=-self._microseconds,
        )

    def _to_microseconds(self):
        return (self._days * (24 * 3600) + self._seconds) * 1000000 + self._microseconds

    def __mul__(self, other):
        if isinstance(other, int):
            return self.__class__(
                years=self._years * other,
                months=self._months * other,
                seconds=self._total * other,
            )

        if isinstance(other, float):
            usec = self._to_microseconds()
            a, b = other.as_integer_ratio()

            return self.__class__(0, 0, _divide_and_round(usec * a, b))

        return NotImplemented

    __rmul__ = __mul__

    def __floordiv__(self, other):
        if not isinstance(other, (int, timedelta)):
            return NotImplemented
        
        usec = self._to_microseconds()
        if isinstance(other, timedelta):
            return usec // other._to_microseconds()

        if isinstance(other, int):
            return self.__class__(
                0,
                0,
                usec // other,
                years=self._years // other,
                months=self._months // other,
            )

    def __truediv__(self, other):
        if not isinstance(other, (int, float, timedelta)):
            return NotImplemented

        usec = self._to_microseconds()
        if isinstance(other, timedelta):
            return usec / other._to_microseconds()

        if isinstance(other, int):
            return self.__class__(
                0,
                0,
                _divide_and_round(usec, other),
                years=_divide_and_round(self._years, other),
                months=_divide_and_round(self._months, other),
            )

        if isinstance(other, float):
            a, b = other.as_integer_ratio()

            return self.__class__(
                0,
                0,
                _divide_and_round(b * usec, a),
                years=_divide_and_round(self._years * b, a),
                months=_divide_and_round(self._months, other),
            )

    __div__ = __floordiv__

    def __mod__(self, other):
        if isinstance(other, timedelta):
            r = self._to_microseconds() % other._to_microseconds()

            return self.__class__(0, 0, r)

        return NotImplemented

    # def __divmod__(self, other):
    #     if isinstance(other, timedelta):
    #         q, r = divmod(self._to_microseconds(), other._to_microseconds())

    #         return q, self.__class__(0, 0, r)

    #     return NotImplemented
