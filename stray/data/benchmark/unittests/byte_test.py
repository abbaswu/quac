
import hashlib

def sha256d(s):
    """A double SHA-256 hash."""
    if not isinstance(s, bytes):
        s1 = s.encode()

    return hashlib.sha256(hashlib.sha256(s1).digest()).hexdigest()