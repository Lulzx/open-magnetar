"""Hash profiles per docs/spec/02-transcript.md section 2.1."""

from __future__ import annotations

import hashlib

PROFILES = {
    "sha256": hashlib.sha256,
    "sha3-256": hashlib.sha3_256,
    "sha384": hashlib.sha384,
}


class Hasher:
    """Thin wrapper over a fixed hash profile. `profile_id` (ASCII) is absorbed
    by the transcript at init."""

    def __init__(self, profile: str = "sha256"):
        if profile not in PROFILES:
            raise ValueError(f"unknown hash profile {profile!r}")
        self.profile = profile
        self._fn = PROFILES[profile]
        self.digest_size = self._fn().digest_size

    @property
    def profile_id(self) -> bytes:
        return self.profile.encode("ascii")

    def digest(self, data: bytes) -> bytes:
        return self._fn(data).digest()
