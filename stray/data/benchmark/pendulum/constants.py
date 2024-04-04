from typing import Tuple
# The day constants
SUNDAY:int= 0
MONDAY:int= 1
TUESDAY:int= 2
WEDNESDAY:int= 3
THURSDAY:int= 4
FRIDAY:int= 5
SATURDAY:int= 6

# Number of X in Y.
YEARS_PER_CENTURY:int= 100
YEARS_PER_DECADE:int= 10
MONTHS_PER_YEAR:int= 12
WEEKS_PER_YEAR:int= 52
DAYS_PER_WEEK:int= 7
HOURS_PER_DAY:int= 24
MINUTES_PER_HOUR:int= 60
SECONDS_PER_MINUTE:int= 60
SECONDS_PER_HOUR:int= MINUTES_PER_HOUR * SECONDS_PER_MINUTE
SECONDS_PER_DAY:int= HOURS_PER_DAY * SECONDS_PER_HOUR
US_PER_SECOND:int= 1000000

# Formats
ATOM:str= "YYYY-MM-DDTHH:mm:ssZ"
COOKIE:str= "dddd, DD-MMM-YYYY HH:mm:ss zz"
ISO8601:str= "YYYY-MM-DDTHH:mm:ssZ"
ISO8601_EXTENDED:str= "YYYY-MM-DDTHH:mm:ss.SSSSSSZ"
RFC822:str= "ddd, DD MMM YY HH:mm:ss ZZ"
RFC850:str= "dddd, DD-MMM-YY HH:mm:ss zz"
RFC1036:str= "ddd, DD MMM YY HH:mm:ss ZZ"
RFC1123:str= "ddd, DD MMM YYYY HH:mm:ss ZZ"
RFC2822:str= "ddd, DD MMM YYYY HH:mm:ss ZZ"
RFC3339:str= ISO8601
RFC3339_EXTENDED:str= ISO8601_EXTENDED
RSS:str= "ddd, DD MMM YYYY HH:mm:ss ZZ"
W3C:str= ISO8601


EPOCH_YEAR:int= 1970

DAYS_PER_N_YEAR:int= 365
DAYS_PER_L_YEAR:int= 366

USECS_PER_SEC:int= 1000000

SECS_PER_MIN:int= 60
SECS_PER_HOUR:int= 60 * SECS_PER_MIN
SECS_PER_DAY:int= SECS_PER_HOUR * 24

# 400-year chunks always have 146097 days (20871 weeks).
SECS_PER_400_YEARS:int= 146097 * SECS_PER_DAY

# The number of seconds in an aligned 100-year chunk, for those that
# do not begin with a leap year and those that do respectively.
SECS_PER_100_YEARS:Tuple[int,int]= (
    (76 * DAYS_PER_N_YEAR + 24 * DAYS_PER_L_YEAR) * SECS_PER_DAY,
    (75 * DAYS_PER_N_YEAR + 25 * DAYS_PER_L_YEAR) * SECS_PER_DAY,
)

# The number of seconds in an aligned 4-year chunk, for those that
# do not begin with a leap year and those that do respectively.
SECS_PER_4_YEARS:Tuple[int,int]= (
    (4 * DAYS_PER_N_YEAR + 0 * DAYS_PER_L_YEAR) * SECS_PER_DAY,
    (3 * DAYS_PER_N_YEAR + 1 * DAYS_PER_L_YEAR) * SECS_PER_DAY,
)

# The number of seconds in non-leap and leap years respectively.
SECS_PER_YEAR:Tuple[int,int]= (DAYS_PER_N_YEAR * SECS_PER_DAY, DAYS_PER_L_YEAR * SECS_PER_DAY)

DAYS_PER_YEAR:Tuple[int,int]= (DAYS_PER_N_YEAR, DAYS_PER_L_YEAR)

# The month lengths in non-leap and leap years respectively.
DAYS_PER_MONTHS:Tuple[Tuple[int,int, int, int, int, int, int, int, int, int, int, int, int], Tuple[int,int, int, int, int, int, int, int, int, int, int, int, int]]= (
    (-1, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31),
    (-1, 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31),
)

# The day offsets of the beginning of each (1-based) month in non-leap
# and leap years respectively.
# For example, in a leap year there are 335 days before December.
MONTHS_OFFSETS:Tuple[Tuple[int,int, int, int, int, int, int, int, int, int, int, int, int, int], Tuple[int,int, int, int, int, int, int, int, int, int, int, int, int, int]]= (
    (-1, 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334, 365),
    (-1, 0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335, 366),
)

DAY_OF_WEEK_TABLE:Tuple[int,int, int, int, int, int, int, int, int, int, int, int]= (0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4)

TM_SUNDAY:int= 0
TM_MONDAY:int= 1
TM_TUESDAY:int= 2
TM_WEDNESDAY:int= 3
TM_THURSDAY:int= 4
TM_FRIDAY:int= 5
TM_SATURDAY:int= 6

TM_JANUARY:int= 0
TM_FEBRUARY:int= 1
TM_MARCH:int= 2
TM_APRIL:int= 3
TM_MAY:int= 4
TM_JUNE:int= 5
TM_JULY:int= 6
TM_AUGUST:int= 7
TM_SEPTEMBER:int= 8
TM_OCTOBER:int= 9
TM_NOVEMBER:int= 10
TM_DECEMBER:int= 11
