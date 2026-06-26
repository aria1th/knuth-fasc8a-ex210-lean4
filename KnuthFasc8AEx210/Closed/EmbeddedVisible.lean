import KnuthFasc8AEx210.Closed.FastHex
import KnuthFasc8AEx210.Closed.Formats

namespace KnuthFasc8AEx210
namespace Closed
namespace EmbeddedVisible

open ByteParsing Formats

/-! Embedded visible-factor payloads decoded and parsed by Lean. -/

def visible76Hex : String :=
  include_str ".." / ".." / "data" / "lean" / "visible76.poly.hex"

def eigen50Hex : String :=
  include_str ".." / ".." / "data" / "lean" / "Trel_plus_eigen50.vec.hex"

def visible76ByteArray : ByteArray :=
  (FastHex.decode? visible76Hex).getD ByteArray.empty

def eigen50ByteArray : ByteArray :=
  (FastHex.decode? eigen50Hex).getD ByteArray.empty

def visible76Bytes : Bytes :=
  FastHex.toNatList visible76ByteArray

def eigen50Bytes : Bytes :=
  FastHex.toNatList eigen50ByteArray

def visible76 : KMP101 :=
  (parseKMP101File? visible76Bytes).getD default

def eigen50 : KMV101 :=
  (parseKMV101File? eigen50Bytes).getD default

theorem visible76_decode_ok :
    FastHex.decode? visible76Hex = some visible76ByteArray := by
  native_decide

theorem eigen50_decode_ok :
    FastHex.decode? eigen50Hex = some eigen50ByteArray := by
  native_decide

theorem visible76_parse_ok : parseKMP101File? visible76Bytes = some visible76 := by
  native_decide

theorem eigen50_parse_ok : parseKMV101File? eigen50Bytes = some eigen50 := by
  native_decide

theorem visible76_check_ok : checkKMP101File visible76Bytes = true := by
  native_decide

theorem eigen50_check_ok : checkKMV101File eigen50Bytes = true := by
  native_decide

theorem visible76_valid : visible76.valid = true := by
  native_decide

theorem eigen50_valid : eigen50.valid = true := by
  native_decide

theorem visible76_coefficient_count : visible76.coeffs.length = 4107 := by
  native_decide

theorem eigen50_dimension : eigen50.dimension = 16831 := by
  native_decide

theorem eigen50_pivot : eigen50.pivot = 0 := by
  native_decide

theorem eigen50_pivot_value : eigen50.entries.getD eigen50.pivot 0 = 37 := by
  native_decide

theorem visible76_file_size : visible76ByteArray.size = 4119 := by
  native_decide

theorem eigen50_file_size : eigen50ByteArray.size = 16847 := by
  native_decide

end EmbeddedVisible
end Closed
end KnuthFasc8AEx210
