from datetime import datetime
from typing import List, Union, Any
from typing import Optional

from data.benchmark.pendulum.constants import DAYS_PER_YEAR
from data.benchmark.pendulum.constants import SECS_PER_YEAR
from data.benchmark.pendulum.helpers import is_leap
from data.benchmark.pendulum.helpers import local_time
from data.benchmark.pendulum.helpers import timestamp
from data.benchmark.pendulum.helpers import week_day

from .posix_timezone import PosixTimezone
from .transition import Transition
from .transition_type import TransitionType

class Timezone:
    _transitions: List[Transition]
    _posix_rule:PosixTimezone
    def __init__(
        self,
        transitions,
        posix_rule=None, 
        extended=True,
    ):
        self._posix_rule = posix_rule
        self._transitions = transitions

        if extended:
            self._extends()


    def transitions(self):  
        return self._transitions


    def posix_rule(self):
        return self._posix_rule

    def _extends(self):
        if not self._posix_rule:
            return

        posix = self._posix_rule

        if not posix.dst_abbr():
            # std only
            # The future specification should match the last/default transition
            t
            if not self._check_ttype(ttype, posix.std_offset(), False, posix.std_abbr()):
                raise ValueError("Posix spec does not match last transition")

            return

        if len(self._transitions) < 2:
            raise ValueError("Too few transitions for POSIX spec")

        # Extend the transitions for an additional 400 years
        # using the future specification

        # The future specification should match the last two transitions,
        # and those transitions should have different is_dst flags.
        tr0 = self._transitions[-1]
        tr1 = self._transitions[-2]
        tt0 = tr0.ttype()
        tt1 = tr1.ttype()
        if tt0.is_dst():
            dst = tt0
            std = tt1
        else:
            dst = tt1
            std = tt0

        self._check_ttype(dst, posix.dst_offset(), True, posix.dst_abbr())
        self._check_ttype(std, posix.std_offset(), False, posix.std_abbr())

        # Add the transitions to tr1 and back to tr0 for each extra year.
        last_year = local_time(tr0.local(), 0, 0)[0]
        leap_year = is_leap(last_year)
        jan1 = datetime(last_year, 1, 1)
        jan1_time = timestamp(jan1)
        jan1_weekday = week_day(jan1.year(), jan1.month(), jan1.day()) % 7

        if local_time(tr1.local(), 0, 0)[0] != last_year:
            # Add a single extra transition to align to a calendar year.
            if tt0.is_dst():
                pt1 = posix.dst_end()
            else:
                pt1 = posix.dst_start()

            tr1_offset = pt1.trans_offset(leap_year, jan1_weekday)
            tr = Transition(jan1_time + tr1_offset - tt0.offset(), tr1.ttype(), tr0)
            tr0 = tr
            tr1 = tr0
            tt0 = tr0.ttype()
            tt1 = tr1.ttype()

        if tt0.is_dst():
            pt1 = posix.dst_end()
            pt0 = posix.dst_start()
        else:
            pt1 = posix.dst_start()
            pt0 = posix.dst_end()

        tr = tr0
        for year in range(last_year + 1, last_year + 401):
            jan1_time += SECS_PER_YEAR[leap_year]
            jan1_weekday = (jan1_weekday + DAYS_PER_YEAR[leap_year]) % 7
            leap_year = not leap_year and is_leap(year)

            tr1_offset = pt1.trans_offset(leap_year, jan1_weekday)
            tr = Transition(jan1_time + tr1_offset - tt0.offset(), tt1, tr)
            self._transitions.append(tr)

            tr0_offset = pt0.trans_offset(leap_year, jan1_weekday)
            tr = Transition(jan1_time + tr0_offset - tt1.offset(), tt0, tr)
            self._transitions.append(tr)

    def _check_ttype(
        self,
        ttype, 
        offset,
        is_dst,
        abbr,
    ):
        return (
            ttype.offset() == offset
            and ttype.is_dst() == is_dst
            and ttype.abbreviation() == abbr
        )
