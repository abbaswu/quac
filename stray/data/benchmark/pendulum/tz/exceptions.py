class TimezoneError(ValueError):

    pass


class NonExistingTime(TimezoneError):

    message:str = "The datetime {} does not exist."

    def __init__(self, dt):
        message = self.message.format(dt)

        super(NonExistingTime, self).__init__(message)


class AmbiguousTime(TimezoneError):

    message:str = "The datetime {} is ambiguous."

    def __init__(self, dt):
        message = self.message.format(dt)

        super(AmbiguousTime, self).__init__(message)
