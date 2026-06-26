#!/usr/bin/env python3
"""Export selected binary certificates as canonical hexadecimal text.

The output is data, not a proof: Lean decodes and checks it. Keeping the
export deterministic makes review and regeneration straightforward.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIR = ROOT / "data" / "lean"

# Payloads embedded directly into Lean as canonical hexadecimal text. PR4 now
# includes the 2.88 MB restricted matrix so Lean can check the released
# eigenvector residual, not only its metadata.
HEX_FILES = [
    Path("data/certs/visible76.poly"),
    Path("data/certs/Trel_plus_eigen50.vec"),
    Path("data/blocks/Tall_finish.vec"),
    Path("data/blocks/Trel_plus.kmc"),
]

# The full reachable symmetric matrix remains metadata-only until the
# restricted residual path is measured in CI.
METADATA_ONLY_FILES = [
    Path("data/blocks/Tall_plus.kmc"),
]


def write_if_changed(path: Path, content: str) -> None:
    if path.exists() and path.read_text(encoding="ascii") == content:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="ascii")


def canonical_hex(data: bytes, width: int = 96) -> str:
    encoded = data.hex()
    return "\n".join(encoded[i : i + width] for i in range(0, len(encoded), width)) + "\n"


def file_record(relative: Path, data: bytes) -> dict[str, object]:
    return {
        "size": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def main() -> None:
    manifest: dict[str, dict[str, object]] = {}
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    for relative in HEX_FILES:
        source = ROOT / relative
        data = source.read_bytes()
        output = OUTPUT_DIR / f"{source.name}.hex"
        write_if_changed(output, canonical_hex(data))
        record = file_record(relative, data)
        record["hex_file"] = str(output.relative_to(ROOT))
        manifest[str(relative)] = record

    for relative in METADATA_ONLY_FILES:
        source = ROOT / relative
        manifest[str(relative)] = file_record(relative, source.read_bytes())

    manifest_text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    write_if_changed(OUTPUT_DIR / "manifest.json", manifest_text)


if __name__ == "__main__":
    main()
