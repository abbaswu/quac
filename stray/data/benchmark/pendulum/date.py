from __future__ import absolute_import
from __future__ import division

import calendar
import math

from datetime import date
from datetime import timedelta
from typing import Dict, List, Type

import data.benchmark.pendulum as pendulum

from .constants import FRIDAY
from .constants import MONDAY
from .constants import MONTHS_PER_YEAR
from .constants import SATURDAY
from .constants import SUNDAY
from .constants import THURSDAY
from .constants import TUESDAY
from .constants import WEDNESDAY
from .constants import YEARS_PER_CENTURY
from .constants import YEARS_PER_DECADE
from .exceptions import PendulumException
from .helpers import add_duration
from .mixins.default import FormattableMixin
from .period import Period

class Date(FormattableMixin, date):

    # Names of days of the week
    _days:Dict[int,str] = {
        SUNDAY: "Sunday",
        MONDAY: "Monday",
        TUESDAY: "Tuesday",
        WEDNESDAY: "Wednesday",
        THURSDAY: "Thursday",
        FRIDAY: "Friday",
        SATURDAY: "Saturday",
    }

    _MODIFIERS_VALID_UNITS:List[str] = ["day", "week", "month", "year", "decade", "century"]

    # Getters/Setters

    def set(self, year=None, month=None, day=None):
        return self.replace(year=year, month=month, day=day)


    def day_of_week(self):
        """
        Returns the day of the week (0-6).

        :
        """
        return self.isoweekday() % 7


    def day_of_year(self):
        """
        Returns the day of the year (1-366).

        :
        """
        k = 1 if self.is_leap_year() else 2

        return (275 * self.month()) // 9 - k * ((self.month() + 9) // 12) + self.day() - 30


    def week_of_year(self):
        return self.isocalendar()[1]


    def days_in_month(self):
        return calendar.monthrange(self.year(), self.month())[1]


    def week_of_month(self):
        first_day_of_month = self.replace(day=1)

        return self.week_of_year() - first_day_of_month.week_of_year() + 1


    def age(self):
        return self.diff(abs=False).in_years()


    def quarter(self):
        return int(math.ceil(self.month() / 3))

    # String Formatting

    def to_date_string(self):
        """
        Format the instance as date.

        :
        """
        return self.strftime("%Y-%m-%d")

    def to_formatted_date_string(self):
        """
        Format the instance as a readable date.

        :
        """
        return self.strftime("%b %d, %Y")

    def __repr__(self):
        return (
            "{klass}("
            "{year}, {month}, {day}"
            ")".format(
                klass=self.__class__.__name__,
                year=self.year(),
                month=self.month(),
                day=self.day(),
            )
        )

    # COMPARISONS

    def closest(self, dt1, dt2):
        """
        Get the closest date from the instance.

        :
        :

        :
        """
        dt3 = self.__class__(dt1.year(), dt1.month(), dt1.day())
        dt4 = self.__class__(dt2.year(), dt2.month(), dt2.day())

        if self.diff(dt3).in_seconds() < self.diff(dt4).in_seconds():
            return dt3

        return dt4

    def farthest(self, dt1, dt2):
        """
        Get the farthest date from the instance.

        :
        :

        :
        """
        dt3 = self.__class__(dt1.year(), dt1.month(), dt1.day())
        dt4 = self.__class__(dt2.year(), dt2.month(), dt2.day())

        if self.diff(dt3).in_seconds() > self.diff(dt4).in_seconds():
            return dt3

        return dt4

    def is_future(self):
        """
        Determines if the instance is in the future, ie. greater than now.

        :
        """
        return self > self.today()

    def is_past(self):
        """
        Determines if the instance is in the past, ie. less than now.

        :
        """
        return self < self.today()

    def is_leap_year(self):
        """
        Determines if the instance is a leap year.

        :
        """
        return calendar.isleap(self.year())

    def is_long_year(self):
        """
        Determines if the instance is a long year

        See link `<https://en.wikipedia.org/wiki/ISO_8601#Week_dates>`_

        :
        """
        return Date(self.year(), 12, 28).isocalendar()[1] == 53

    def is_same_day(self, dt):
        """
        Checks if the passed in date is the same day as the instance current day.

        :

        :
        """
        return self == dt

    def is_anniversary(self, dt=None):
        """
        Check if its the anniversary.

        Compares the date/month values of the two dates.

        :
        """
        if dt is None:
            dt = Date.today()

        instance = self.__class__(dt.year(), dt.month(), dt.day())

        return (self.month(), self.day()) == (instance.month(), instance.day())

    # the additional method for checking if today is the anniversary day
    # the alias is provided to start using a new name and keep the backward compatibility
    # the old name can be completely replaced with the new in one of the future versions
    is_birthday = is_anniversary

    # ADDITIONS AND SUBSTRACTIONS

    def add(self, years=0, months=0, weeks=0, days=0):
        """
        Add duration to the instance.

        :param years: The number of years
        :

        :param months: The number of months
        :

        :param weeks: The number of weeks
        :

        :param days: The number of days
        :

        :
        """
        dt = add_duration(
            date(self.year(), self.month(), self.day()),
            years=years,
            months=months,
            weeks=weeks,
            days=days,
        )

        return self.__class__(dt.years(), dt.months(), dt.days())

    def subtract(self, years=0, months=0, weeks=0, days=0):
        """
        Remove duration from the instance.

        :param years: The number of years
        :

        :param months: The number of months
        :

        :param weeks: The number of weeks
        :

        :param days: The number of days
        :

        :
        """
        return self.add(years=-years, months=-months, weeks=-weeks, days=-days)

    def _add_timedelta(self, delta):
        """
        Add timedelta duration to the instance.

        :param delta: The timedelta instance
        :

        :
        """
        # if isinstance(delta, pendulum.Duration):
        #     return self.add(
        #         years=delta.years(),
        #         months=delta.months(),
        #         weeks=delta.weeks(),
        #         days=delta.remaining_days(),
        #     )

        return self.add(days=delta.days())

    def _subtract_timedelta(self, delta):
        """
        Remove timedelta duration from the instance.

        :param delta: The timedelta instance
        :

        :
        """
        # if isinstance(delta, pendulum.Duration):
        #     return self.subtract(
        #         years=delta.years(),
        #         months=delta.months(),
        #         weeks=delta.weeks(),
        #         days=delta.remaining_days(),
        #     )

        return self.subtract(days=delta.days())

    def __add__(self, other):
        if not isinstance(other, timedelta):
            return NotImplemented

        return self._add_timedelta(other)

    def __sub__(self, other):
        if isinstance(other, timedelta):
            return self._subtract_timedelta(other)

        if not isinstance(other, date):
            return NotImplemented

        dt = self.__class__(other.year(), other.month(), other.day())

        return dt.diff(self, False)

    # DIFFERENCES

    def diff(self, dt=None, abs=True):
        """
        Returns the difference between two Date objects as a Period.

        :

        :param abs: Whether to return an absolute interval or not
        :

        :
        """
        if dt is None:
            dt = self.today()

        return Period(self, dt, absolute=abs)

    def diff_for_humans(self, other=None, absolute=False, locale=None):
        """
        Get the difference in a human readable format in the current locale.

        When comparing a value in the past to default now:
        1 day ago
        5 months ago

        When comparing a value in the future to default now:
        1 day from now
        5 months from now

        When comparing a value in the past to another value:
        1 day before
        5 months before

        When comparing a value in the future to another value:
        1 day after
        5 months after

        :

        :param absolute: removes time difference modifiers ago, after, etc
        :

        :param locale: The locale to use for localization
        :

        :
        """
        is_now = other is None

        if is_now:
            other = self.today()

        diff = self.diff(other)

        return diff

    # MODIFIERS

    def start_of(self, unit:str)->Date:
        """
        Returns a copy of the instance with the time reset
        with the following rules:

        * day: time to 00:00:00
        * week: date to first day of the week and time to 00:00:00
        * month: date to first day of the month and time to 00:00:00
        * year: date to first day of the year and time to 00:00:00
        * decade: date to first day of the decade and time to 00:00:00
        * century: date to first day of century and time to 00:00:00

        :param unit: The unit to reset to
        :

        :
        """
        if unit not in self._MODIFIERS_VALID_UNITS:
            raise ValueError('Invalid unit "{}" for start_of()'.format(unit))

        return getattr(self, "_start_of_{}".format(unit))()

    def end_of(self, unit:str)->Date:
        """
        Returns a copy of the instance with the time reset
        with the following rules:

        * week: date to last day of the week
        * month: date to last day of the month
        * year: date to last day of the year
        * decade: date to last day of the decade
        * century: date to last day of century

        :param unit: The unit to reset to
        :

        :
        """
        if unit not in self._MODIFIERS_VALID_UNITS:
            raise ValueError('Invalid unit "%s" for end_of()' % unit)

        return getattr(self, "_end_of_%s" % unit)()

    def _start_of_day(self):
        """
        Compatibility method.

        :
        """
        return self

    def _end_of_day(self):
        """
        Compatibility method

        :
        """
        return self

    def _start_of_month(self):
        """
        Reset the date to the first day of the month.

        :
        """
        return self.set(self.year(), self.month(), 1)

    def _end_of_month(self):
        """
        Reset the date to the last day of the month.

        :
        """
        return self.set(self.year(), self.month(), self.days_in_month())

    def _start_of_year(self):
        """
        Reset the date to the first day of the year.

        :
        """
        return self.set(self.year(), 1, 1)

    def _end_of_year(self):
        """
        Reset the date to the last day of the year.

        :
        """
        return self.set(self.year(), 12, 31)

    def _start_of_decade(self):
        """
        Reset the date to the first day of the decade.

        :
        """
        year = self.year() - self.year() % YEARS_PER_DECADE

        return self.set(year, 1, 1)

    def _end_of_decade(self):
        """
        Reset the date to the last day of the decade.

        :
        """
        year = self.year() - self.year() % YEARS_PER_DECADE + YEARS_PER_DECADE - 1

        return self.set(year, 12, 31)

    def _start_of_century(self):
        """
        Reset the date to the first day of the century.

        :
        """
        year = self.year() - 1 - (self.year() - 1) % YEARS_PER_CENTURY + 1

        return self.set(year, 1, 1)

    def _end_of_century(self):
        """
        Reset the date to the last day of the century.

        :
        """
        year = self.year() - 1 - (self.year() - 1) % YEARS_PER_CENTURY + YEARS_PER_CENTURY

        return self.set(year, 12, 31)

    def _start_of_week(self):
        """
        Reset the date to the first day of the week.

        :
        """
        dt = self

        if self.day_of_week() != 1:
            dt = self.previous(1)

        return dt.start_of("day")

    def _end_of_week(self):
        """
        Reset the date to the last day of the week.

        :
        """
        dt = self

        if self.day_of_week() != 1:
            dt = self.next(1)

        return dt.end_of("day")

    def next(self, day_of_week=None):
        """
        Modify to the next occurrence of a given day of the week.
        If no day_of_week is provided, modify to the next occurrence
        of the current day of the week.  Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :param day_of_week: The next day of week to reset to.
        :

        :
        """
        if day_of_week is None:
            day_of_week = self.day_of_week()

        if day_of_week < SUNDAY or day_of_week > SATURDAY:
            raise ValueError("Invalid day of week")

        dt = self.add(days=1)
        while dt.day_of_week != day_of_week:
            dt = dt.add(days=1)

        return dt

    def previous(self, day_of_week=None):
        """
        Modify to the previous occurrence of a given day of the week.
        If no day_of_week is provided, modify to the previous occurrence
        of the current day of the week.  Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :param day_of_week: The previous day of week to reset to.
        :

        :
        """
        if day_of_week is None:
            day_of_week = self.day_of_week()

        if day_of_week < SUNDAY or day_of_week > SATURDAY:
            raise ValueError("Invalid day of week")

        dt = self.subtract(days=1)
        while dt.day_of_week != day_of_week:
            dt = dt.subtract(days=1)

        return dt
    # Edit: attr
    def first_of(self, unit:str, day_of_week:int=None)->'Date':
        """
        Returns an instance set to the first occurrence
        of a given day of the week in the current unit.
        If no day_of_week is provided, modify to the first day of the unit.
        Use the supplied consts to indicate the desired day_of_week, ex. pendulum.MONDAY.

        Supported units are month, quarter and year.

        :param unit: The unit to use
        :

        :

        :
        """
        if unit not in ["month", "quarter", "year"]:
            raise ValueError('Invalid unit "{}" for first_of()'.format(unit))

        return getattr(self, "_first_of_{}".format(unit))(day_of_week)
    # Edit: attr
    def last_of(self, unit:str, day_of_week:int=None)->Date:
        """
        Returns an instance set to the last occurrence
        of a given day of the week in the current unit.
        If no day_of_week is provided, modify to the last day of the unit.
        Use the supplied consts to indicate the desired day_of_week, ex. pendulum.MONDAY.

        Supported units are month, quarter and year.

        :param unit: The unit to use
        :

        :

        :
        """
        if unit not in ["month", "quarter", "year"]:
            raise ValueError('Invalid unit "{}" for first_of()'.format(unit))

        return getattr(self, "_last_of_{}".format(unit))(day_of_week)
    # Edit: attr
    def nth_of(self, unit:str, nth:int, day_of_week:int)->Date:
        """
        Returns a new instance set to the given occurrence
        of a given day of the week in the current unit.
        If the calculated occurrence is outside the scope of the current unit,
        then raise an error. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        Supported units are month, quarter and year.

        :param unit: The unit to use
        :

        :

        :

        :
        """
        if unit not in ["month", "quarter", "year"]:
            raise ValueError('Invalid unit "{}" for first_of()'.format(unit))

        dt = getattr(self, "_nth_of_{}".format(unit))(nth, day_of_week)
        return dt

    def _first_of_month(self, day_of_week):
        """
        Modify to the first occurrence of a given day of the week
        in the current month. If no day_of_week is provided,
        modify to the first day of the month. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :
        """
        dt = self

        if day_of_week is None:
            return dt.set(day=1)

        month = calendar.monthcalendar(dt.year(), dt.month())

        calendar_day = (day_of_week - 1) % 7

        if month[0][calendar_day] > 0:
            day_of_month = month[0][calendar_day]
        else:
            day_of_month = month[1][calendar_day]

        return dt.set(day=day_of_month)

    def _last_of_month(self, day_of_week=None):
        """
        Modify to the last occurrence of a given day of the week
        in the current month. If no day_of_week is provided,
        modify to the last day of the month. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :
        """
        dt = self

        if day_of_week is None:
            return dt.set(day=self.days_in_month())

        month = calendar.monthcalendar(dt.year(), dt.month())

        calendar_day = (day_of_week - 1) % 7

        if month[-1][calendar_day] > 0:
            day_of_month = month[-1][calendar_day]
        else:
            day_of_month = month[-2][calendar_day]

        return dt.set(day=day_of_month)

    def _nth_of_month(self, nth, day_of_week):
        """
        Modify to the given occurrence of a given day of the week
        in the current month. If the calculated occurrence is outside,
        the scope of the current month, then return False and no
        modifications are made. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :

        :
        """
        if nth == 1:
            return self.first_of("month", day_of_week)

        dt = self.first_of("month")
        check = dt.format("YYYY-MM")
        for i in range(nth - (1 if dt.day_of_week == day_of_week else 0)):
            dt = dt.next(day_of_week)

        if dt.format("YYYY-MM") == check:
            return self.set(day=dt.day())

        return False

    def _first_of_quarter(self, day_of_week=None):
        """
        Modify to the first occurrence of a given day of the week
        in the current quarter. If no day_of_week is provided,
        modify to the first day of the quarter. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :
        """
        return self.set(self.year(), self.quarter() * 3 - 2, 1).first_of(
            "month", day_of_week
        )

    def _last_of_quarter(self, day_of_week=None):
        """
        Modify to the last occurrence of a given day of the week
        in the current quarter. If no day_of_week is provided,
        modify to the last day of the quarter. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :
        """
        return self.set(self.year(), self.quarter() * 3, 1).last_of("month", day_of_week)

    def _nth_of_quarter(self, nth, day_of_week):
        """
        Modify to the given occurrence of a given day of the week
        in the current quarter. If the calculated occurrence is outside,
        the scope of the current quarter, then return False and no
        modifications are made. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :

        :
        """
        if nth == 1:
            return self.first_of("quarter", day_of_week)

        dt = self.replace(self.year(), self.quarter() * 3, 1)
        last_month = dt.month()
        year = dt.year()
        dt = dt.first_of("quarter")
        for i in range(nth - (1 if dt.day_of_week == day_of_week else 0)):
            dt = dt.next(day_of_week)

        if last_month < dt.month() or year != dt.year():
            return False

        return self.set(self.year(), dt.month(), dt.day())

    def _first_of_year(self, day_of_week=None):
        """
        Modify to the first occurrence of a given day of the week
        in the current year. If no day_of_week is provided,
        modify to the first day of the year. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :
        """
        return self.set(month=1).first_of("month", day_of_week)

    def _last_of_year(self, day_of_week=None):
        """
        Modify to the last occurrence of a given day of the week
        in the current year. If no day_of_week is provided,
        modify to the last day of the year. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :
        """
        return self.set(month=MONTHS_PER_YEAR).last_of("month", day_of_week)

    def _nth_of_year(self, nth, day_of_week):
        """
        Modify to the given occurrence of a given day of the week
        in the current year. If the calculated occurrence is outside,
        the scope of the current year, then return False and no
        modifications are made. Use the supplied consts
        to indicate the desired day_of_week, ex. pendulum.MONDAY.

        :

        :

        :
        """
        if nth == 1:
            return self.first_of("year", day_of_week)

        dt = self.first_of("year")
        year = dt.year()
        for i in range(nth - (1 if dt.day_of_week == day_of_week else 0)):
            dt = dt.next(day_of_week)

        if year != dt.year():
            return False

        return self.set(self.year(), dt.month(), dt.day())

    def average(self, dt=None):
        """
        Modify the current instance to the average
        of a given instance (default now) and the current instance.

        :

        :
        """
        if dt is None:
            dt = Date.today()

        return self.add(days=int(self.diff(dt, False).in_days() / 2))

    # Native s override
    # Edit: classmethod
    @classmethod
    def today(cls:Type[Date])->Date:
        return pendulum.today().date()
    # Edit: classmethod
    @classmethod
    def fromtimestamp(cls:Type[Date], t:float)->Date:
        dt = super(Date, cls).fromtimestamp(t)

        return cls(dt.year(), dt.month(), dt.day())
    # Edit: classmethod
    @classmethod
    def fromordinal(cls:Type[Date], n:int)->Date:
        dt = super(Date, cls).fromordinal(n)

        return cls(dt.year(), dt.month(), dt.day()())

    def replace(self, year=None, month=None, day=None):
        year = year if year is not None else self.year()
        month = month if month is not None else self.month()
        day = day if day is not None else self.day()

        return self.__class__(year, month, day)
