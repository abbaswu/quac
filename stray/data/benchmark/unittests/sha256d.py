import hashlib
def sha256d(s):
    """A double SHA-256 hash."""
    if not isinstance(s, bytes):
        s1 = s.encode() # Edit: change to SSA
    else:
        s1 = s
    return hashlib.sha256(hashlib.sha256(s1).digest()).hexdigest()
