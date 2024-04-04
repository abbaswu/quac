from datetime import datetime as _datetime
from datetime import timedelta
from datetime import tzinfo
from typing import Optional, Union
from typing import TypeVar
from typing import overload
from typing import List, Dict, Tuple, Any

import data.benchmark.pendulum as pendulum
from data.benchmark.pendulum.datetime import DateTime

from data.benchmark.pendulum.helpers import local_time
from data.benchmark.pendulum.helpers import timestamp
from data.benchmark.pendulum.utils._compat import _HAS_FOLD

from .exceptions import AmbiguousTime
from .exceptions import NonExistingTime
from .zoneinfo import read
from .zoneinfo import read_file
from .zoneinfo.transition import Transition


POST_TRANSITION = "post"
PRE_TRANSITION = "pre"
TRANSITION_ERROR = "error"


_D = TypeVar("_D", bound=_datetime)


class Timezone(tzinfo):
    """
    Represents a named timezone.

    The accepted names are those provided by the IANA time zone database.

    >>> from data.benchmark.pendulum.tz.timezone import Timezone
    >>> tz = Timezone('Europe/Paris')
    """
    _name:str
    _transitions:List[Transition]
    _hint:Dict[bool, Tuple[int,int]]
    def __init__(self, name, extended=True):  
        tz = read(name, extend=extended)

        self._name = name
        self._transitions = tz.transitions()
        self._hint = {True: None, False: None}


    def name(self):  
        return self._name

    def convert(self, dt, dst_rule=None):  
        """
        Converts a datetime in the current timezone.

        If the datetime is naive, it will be normalized.

        >>> from datetime import datetime
        >>> from pendulum import timezone
        >>> paris = timezone('Europe/Paris')
        >>> dt = datetime(2013, 3, 31, 2, 30, fold=1)
        >>> in_paris = paris.convert(dt)
        >>> in_paris.isoformat()
        '2013-03-31T03:30:00+02:00'

        If the datetime is aware, it will be properly converted.

        >>> new_york = timezone('America/New_York')
        >>> in_new_york = new_york.convert(in_paris)
        >>> in_new_york.isoformat()
        '2013-03-30T21:30:00-04:00'
        """
        if dt.tzinfo() is None:
            return self._normalize(dt, dst_rule=dst_rule)

        return self._convert(dt)

    def datetime(
        self, year, month, day, hour=0, minute=0, second=0, microsecond=0
    ):  
        """
        Return a normalized datetime for the current timezone.
        """
        if _HAS_FOLD:
            return self.convert(
                _datetime(year, month, day, hour, minute, second, microsecond, fold=1)
            )

        return self.convert(
            _datetime(year, month, day, hour, minute, second, microsecond),
            dst_rule=POST_TRANSITION,
        )

    def _normalize(self, dt, dst_rule=None):  
        sec = timestamp(dt)
        fold = 0
        transition = self._lookup_transition(sec)

        if not _HAS_FOLD and dst_rule is None:
            dst_rule = POST_TRANSITION

        if dst_rule is None:
            dst_rule = PRE_TRANSITION
            if dt.fold() == 1:
                dst_rule = POST_TRANSITION

        if sec < transition.local():
            if transition.is_ambiguous(sec):
                # Ambiguous time
                if dst_rule == TRANSITION_ERROR:
                    pass

                # We set the fold attribute for later
                if dst_rule == POST_TRANSITION:
                    fold = 1
            elif transition.previous() is not None:
                transition = transition.previous()

        if transition:
            if transition.is_ambiguous(sec):
                # Ambiguous time
                if dst_rule == TRANSITION_ERROR:
                    pass

                # We set the fold attribute for later
                if dst_rule == POST_TRANSITION:
                    fold = 1
            elif transition.is_missing(sec):
                # Skipped time
                if dst_rule == TRANSITION_ERROR:
                    pass

                # We adjust accordingly
                if dst_rule == POST_TRANSITION:
                    sec += transition.fix()
                    fold = 1
                else:
                    sec -= transition.fix()

        a, b, c, d, e, f, g = local_time(sec, 0, dt.microsecond()) 
        return dt.__class__(a, b, c, d, e, f, g, tzinfo=self)

    def _convert(self, dt):  
        if dt.tzinfo() is self:
            return self._normalize(dt, dst_rule=POST_TRANSITION)

        if not isinstance(dt.tzinfo(), Timezone):
            return dt.astimezone(self)

        stamp = timestamp(dt)

        if isinstance(dt.tzinfo(), FixedTimezone):
            offset = dt.tzinfo().offset()
        else:
            transition = dt.tzinfo()._lookup_transition(stamp)
            offset = transition.ttype.offset()

            if stamp < transition.local() and transition.previous() is not None:
                if (
                    transition.previous.is_ambiguous(stamp)
                    and getattr(dt, "fold", 1) == 0
                ):
                    pass
                else:
                    offset = transition.previous().ttype().offset()

        stamp -= offset

        transition = self._lookup_transition(stamp, is_utc=True)
        if stamp < transition.at() and transition.previous() is not None:
            transition = transition.previous()

        offset = transition.ttype().offset()
        stamp += offset
        fold = int(not transition.ttype().is_dst())

        kwargs = {"tzinfo": self}

        a, b, c, d, e, f, g = local_time(stamp, 0, dt.microsecond()) 
        return dt.__class__(a, b, c, d, e, f, g, tzinfo=self)

    def _lookup_transition(
        self, stamp, is_utc=False
    ):  
        lo, hi = 0, len(self._transitions)
        hint = self._hint[is_utc]
        if hint:
            if stamp == hint[0]:
                return self._transitions[hint[1]]
            elif stamp < hint[0]:
                hi = hint[1]
            else:
                lo = hint[1]

        if not is_utc:
            while lo < hi:
                mid = (lo + hi) // 2
                if stamp < self._transitions[mid].to:
                    hi = mid
                else:
                    lo = mid + 1
        else:
            while lo < hi:
                mid = (lo + hi) // 2
                if stamp < self._transitions[mid].at:
                    hi = mid
                else:
                    lo = mid + 1

        if lo >= len(self._transitions):
            # Beyond last transition
            lo = len(self._transitions) - 1

        self._hint[is_utc] = (stamp, lo)

        return self._transitions[lo]

    def utcoffset(self, dt):
        if dt is None:
            return

        transition = self._get_transition(dt)

        return transition.utcoffset()

    def dst(
        self, dt  
    ):  
        if dt is None:
            return

        transition = self._get_transition(dt)

        if not transition.ttype.is_dst():
            return timedelta()

        return timedelta(seconds=transition.fix())

    def tzname(self, dt):  
        if dt is None:
            return

        transition = self._get_transition(dt)

        return transition.ttype().abbreviation()
    
    # Edit: attr
    def _get_transition(self, dt:Union[_datetime, DateTime])->Transition:  
        if dt.tzinfo() is not None and dt.tzinfo() is not self:
            dt = dt - dt.utcoffset()

            stamp = timestamp(dt)

            transition = self._lookup_transition(stamp, is_utc=True)
        else:
            stamp = timestamp(dt)

            transition = self._lookup_transition(stamp)

            if stamp < transition.local() and transition.previous() is not None:
                fold = getattr(dt, "fold", 1)
                if transition.is_ambiguous(stamp):
                    if fold == 0:
                        transition = transition.previous()
                elif transition.previous().is_ambiguous(stamp) and fold == 0:
                    pass
                else:
                    transition = transition.previous()

        return transition

    def fromutc(self, dt):  
        stamp = timestamp(dt)

        transition = self._lookup_transition(stamp, is_utc=True)
        if stamp < transition.at() and transition.previous() is not None:
            transition = transition.previous()

        stamp += transition.ttype().offset()
        a, b, c, d, e, f, g = local_time(stamp, 0, dt.microsecond()) 
        return dt.__class__(a, b, c, d, e, f, g, tzinfo=self)

    def __repr__(self):  
        return "Timezone('{}')".format(self._name)

    def __getinitargs__(self):  
        return (self._name,)


class FixedTimezone(Timezone):
    _offset:int
    _name:str
    _utcoffset:timedelta
    def __init__(self, offset, name=None):
        sign = "-" if offset < 0 else "+"

        minutes = offset / 60
        hour, minute = divmod(abs(int(minutes)), 60)

        if not name:
            name = "{0}{1:02d}:{2:02d}".format(sign, hour, minute)

        self._name = name
        self._offset = offset
        self._utcoffset = timedelta(seconds=offset)


    def offset(self):  
        return self._offset

    def _normalize(self, dt, dst_rule=None):  
        if _HAS_FOLD:
            dt = dt.__class__(
                dt.year(),
                dt.month(),
                dt.day(),
                dt.hour(),
                dt.minute(),
                dt.second(),
                dt.microsecond(),
                tzinfo=self,
                fold=0,
            )
        else:
            dt = dt.__class__(
                dt.year(),
                dt.month(),
                dt.day(),
                dt.hour(),
                dt.minute(),
                dt.second(),
                dt.microsecond(),
                tzinfo=self,
            )

        return dt

    def _convert(self, dt):  
        if dt.tzinfo() is not self:
            return dt.astimezone(self)

        return dt

    def utcoffset(self, dt):  
        return self._utcoffset

    def dst(self, dt):  
        return timedelta()

    def fromutc(self, dt):  
        # Use the stdlib datetime's add method to avoid infinite recursion
        return (datetime.__add__(dt, self._utcoffset)).replace(tzinfo=self)

    def tzname(self, dt):  
        return self._name

    def __getinitargs__(self):  
        return self._offset, self._name


class TimezoneFile(Timezone):
    def __init__(self, path):
        tz = read_file(path)

        self._name = ""
        self._transitions = tz.transitions
        self._hint = {True: None, False: None}


UTC:FixedTimezone = FixedTimezone(0, "UTC")
