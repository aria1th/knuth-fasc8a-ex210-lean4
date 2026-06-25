#!/usr/bin/env python3
"""Export selected binary certificates as canonical hexadecimal text.

The output is data, not a proof: Lean decodes and checks it.  Keeping the
export deterministic makes review and regeneration straightforward.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIR = ROOT / "data" / "lean"
FILES = [
    Path("data/certs/visible76.poly"),
    Path("data/certs/Trel_plus_eigen50.vec"),
]


def write_if_changed(path: Path, content: str) -> None:
    if path.exists() and path.read_text(encoding="ascii") == content:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="ascii")


def canonical_hex(data: bytes, width: int = 96) -> str:
    encoded = data.hex()
    return "\n".join(encoded[i : i + width] for i in range(0, len(encoded), width)) + "\n"


def main() -> None:
    manifest: dict[str, dict[str, object]] = {}
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    for relative in FILES:
        source = ROOT / relative
        data = source.read_bytes()
        output = OUTPUT_DIR / f"{source.name}.hex"
        write_if_changed(output, canonical_hex(data))
        manifest[str(relative)] = {
            "hex_file": str(output.relative_to(ROOT)),
            "size": len(data),
            "sha256": hashlib.sha256(data).hexdigest(),
        }

    manifest_text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    write_if_changed(OUTPUT_DIR / "manifest.json", manifest_text)


if __name__ == "__main__":
    main()
