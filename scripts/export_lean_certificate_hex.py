#!/usr/bin/env python3
"""Export finite certificates as canonical hexadecimal text.

The output is data, not a proof: Lean decodes and checks it.  Large sparse
matrices are exported as independently checkable contiguous row blocks so that
ordinary CI never has to elaborate one multi-megabyte residual computation.
"""

from __future__ import annotations

import hashlib
import json
import struct
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIR = ROOT / "data" / "lean"
TREL_CHUNK_DIR = OUTPUT_DIR / "trel_residual"
TREL_MATRIX = Path("data/blocks/Trel_plus.kmc")
TREL_CHUNK_ROWS = 1024

HEX_FILES = [
    Path("data/certs/visible76.poly"),
    Path("data/certs/Trel_plus_eigen50.vec"),
    Path("data/blocks/Tall_finish.vec"),
]

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


def file_record(data: bytes) -> dict[str, object]:
    return {
        "size": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def parse_kmc201(data: bytes) -> tuple[int, int, list[int], list[int], bytes]:
    """Return dimension, prime, row pointers, columns, and values."""
    if len(data) < 32 or data[:6] != b"KMC201":
        raise ValueError("bad KMC201 magic")
    dimension, prime = struct.unpack_from("<II", data, 8)
    nnz = struct.unpack_from("<Q", data, 16)[0]
    offset = 32

    row_count = dimension + 1
    row_bytes = 8 * row_count
    row_ptr = list(struct.unpack_from(f"<{row_count}Q", data, offset))
    offset += row_bytes

    column_bytes = 4 * nnz
    columns = list(struct.unpack_from(f"<{nnz}I", data, offset))
    offset += column_bytes

    values = data[offset : offset + nnz]
    offset += nnz

    representative_bytes = 8 * dimension
    if offset + representative_bytes != len(data):
        raise ValueError("unexpected KMC201 length")
    if row_ptr[0] != 0 or row_ptr[-1] != nnz:
        raise ValueError("invalid KMC201 row pointers")
    return dimension, prime, row_ptr, columns, values


def encode_residual_chunk(
    dimension: int,
    start_row: int,
    row_count: int,
    row_ptr: list[int],
    columns: list[int],
    values: bytes,
) -> bytes:
    first = row_ptr[start_row]
    stop = row_ptr[start_row + row_count]
    local_ptr = [value - first for value in row_ptr[start_row : start_row + row_count + 1]]
    local_columns = columns[first:stop]
    local_values = values[first:stop]
    nnz = stop - first

    header = struct.pack(
        "<8sIIIQ",
        b"KRC101\0\0",
        dimension,
        start_row,
        row_count,
        nnz,
    )
    pointers = struct.pack(f"<{len(local_ptr)}Q", *local_ptr)
    column_data = struct.pack(f"<{len(local_columns)}I", *local_columns)
    return header + pointers + column_data + local_values


def export_trel_chunks(manifest: dict[str, dict[str, object]]) -> None:
    source = ROOT / TREL_MATRIX
    matrix_data = source.read_bytes()
    dimension, prime, row_ptr, columns, values = parse_kmc201(matrix_data)
    if prime != 101:
        raise ValueError("Trel matrix is not over F_101")

    TREL_CHUNK_DIR.mkdir(parents=True, exist_ok=True)
    expected_paths: set[Path] = set()
    chunks: list[dict[str, object]] = []

    for index, start_row in enumerate(range(0, dimension, TREL_CHUNK_ROWS)):
        row_count = min(TREL_CHUNK_ROWS, dimension - start_row)
        payload = encode_residual_chunk(
            dimension, start_row, row_count, row_ptr, columns, values
        )
        name = f"Trel_plus.rows.{start_row:05d}.{row_count:05d}.krc.hex"
        output = TREL_CHUNK_DIR / name
        expected_paths.add(output)
        write_if_changed(output, canonical_hex(payload))
        chunks.append(
            {
                "index": index,
                "start_row": start_row,
                "row_count": row_count,
                "nnz": row_ptr[start_row + row_count] - row_ptr[start_row],
                "hex_file": str(output.relative_to(ROOT)),
                **file_record(payload),
            }
        )

    for stale in TREL_CHUNK_DIR.glob("*.krc.hex"):
        if stale not in expected_paths:
            stale.unlink()

    obsolete_full_hex = OUTPUT_DIR / "Trel_plus.kmc.hex"
    if obsolete_full_hex.exists():
        obsolete_full_hex.unlink()

    record = file_record(matrix_data)
    record.update(
        {
            "dimension": dimension,
            "prime": prime,
            "chunk_rows": TREL_CHUNK_ROWS,
            "row_chunks": chunks,
        }
    )
    manifest[str(TREL_MATRIX)] = record


def main() -> None:
    manifest: dict[str, dict[str, object]] = {}
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    for relative in HEX_FILES:
        source = ROOT / relative
        data = source.read_bytes()
        output = OUTPUT_DIR / f"{source.name}.hex"
        write_if_changed(output, canonical_hex(data))
        record = file_record(data)
        record["hex_file"] = str(output.relative_to(ROOT))
        manifest[str(relative)] = record

    export_trel_chunks(manifest)

    for relative in METADATA_ONLY_FILES:
        source = ROOT / relative
        manifest[str(relative)] = file_record(source.read_bytes())

    manifest_text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    write_if_changed(OUTPUT_DIR / "manifest.json", manifest_text)


if __name__ == "__main__":
    main()
