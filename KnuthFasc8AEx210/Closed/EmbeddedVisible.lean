import KnuthFasc8AEx210.Closed.FastHex
import KnuthFasc8AEx210.Closed.Formats

namespace KnuthFasc8AEx210
namespace Closed
namespace EmbeddedVisible

open ByteParsing Formats

/-!
# Embedded visible-factor payloads

The canonical hexadecimal text is generated deterministically from the two
checked-in binary files.  Lean decodes and parses the text itself.
-/

/-- Canonical text representation of `visible76.poly`. -/
def visible76Hex : String :=
  include_str ".." / ".." / "data" / "lean" / "visible76.poly.hex"

/-- Canonical text representation of `Trel_plus_eigen50.vec`. -/
def eigen50Hex : String :=
  include_str ".." / ".." / "data" / "lean" / "Trel_plus_eigen50.vec.hex"

/-- Decoded byte arrays of the two certificates. -/
def visible76ByteArray : ByteArray :=
  (FastHex.decode? visible76Hex).getD ByteArray.empty

def eigen50ByteArray : ByteArray :=
  (FastHex.decode? eigen50Hex).getD ByteArray.empty

/-- List views consumed by the small format parsers. -/
def visible76Bytes : Bytes :=
  FastHex.toNatList visible76ByteArray

def eigen50Bytes : Bytes :=
  FastHex.toNatList eigen50ByteArray

/-- Parsed polynomial certificate. -/
def visible76 : KMP101 :=
  (parseKMP101File? visible76Bytes).getD default

/-- Parsed eigenvector certificate. -/
def eigen50 : KMV101 :=
  (parseKMV101File? eigen50Bytes).getD default

/-- The embedded polynomial text decodes without error. -/
theorem visible76_decode_ok :
    FastHex.decode? visible76Hex = some visible76ByteArray := by
  native_decide

/-- The embedded eigenvector text decodes without error. -/
theorem eigen50_decode_ok :
    FastHex.decode? eigen50Hex = some eigen50ByteArray := by
  native_decide

/-- The complete polynomial file has the expected format and field-valued coefficients. -/
theorem visible76_parse_ok : parseKMP101File? visible76Bytes = some visible76 := by
  native_decide

/-- The complete eigenvector file has the expected format and a nonzero pivot. -/
theorem eigen50_parse_ok : parseKMV101File? eigen50Bytes = some eigen50 := by
  native_decide

/-- The polynomial payload is valid by the parser soundness theorem. -/
theorem visible76_valid : visible76.Valid :=
  parseKMP101File?_sound visible76_parse_ok

/-- The eigenvector payload is valid by the parser soundness theorem. -/
theorem eigen50_valid : eigen50.Valid :=
  parseKMV101File?_sound eigen50_parse_ok

/-- Boolean parse/check form for the embedded polynomial payload. -/
theorem visible76_check_ok : checkKMP101File visible76Bytes = true := by
  native_decide

/-- Boolean parse/check form for the embedded eigenvector payload. -/
theorem eigen50_check_ok : checkKMV101File eigen50Bytes = true := by
  native_decide

/-- The polynomial file contains coefficients `0` through `4106`. -/
theorem visible76_coefficient_count : visible76.coeffs.length = 4107 := by
  native_decide

/-- The embedded eigenvector is for the `16831`-dimensional symmetric `Trel` block. -/
theorem eigen50_dimension : eigen50.dimension = 16831 := by
  native_decide

/-- The released certificate uses coordinate zero as its nonzero pivot. -/
theorem eigen50_pivot : eigen50.pivot = 0 := by
  native_decide

/-- The pivot coordinate is the nonzero field element `37`. -/
theorem eigen50_pivot_value : eigen50.entries.getD eigen50.pivot 0 = 37 := by
  native_decide

/-- The decoded file sizes agree with the release manifest. -/
theorem visible76_file_size : visible76ByteArray.size = 4119 := by
  native_decide

theorem eigen50_file_size : eigen50ByteArray.size = 16847 := by
  native_decide

end EmbeddedVisible
end Closed
end KnuthFasc8AEx210
