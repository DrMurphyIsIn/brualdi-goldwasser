/-
  R3Cert.BGEnvCert.Decode -- kernel-side decoding of packed certificate data (2026-09-25).

  Large list literals are slow to elaborate, hex literals are not.  The generator therefore ships
  witness lists, tangent entries and root entries as hex numbers, and these functions unpack them
  inside the kernel.  Soundness never depends on how the data was decoded: every check runs on
  whatever lists these functions return.  No proofs here.
-/
import Mathlib

namespace R3Cert
namespace EnvCert

/-- Byte stream to lists of `h` values: byte `b ∈ 1..254` means `h = b - 1`, byte `255` ends a list. -/
def decRow : ℕ → ℕ → List ℕ → List (List ℕ) → List (List ℕ)
  | 0, _, _, acc => acc.reverse
  | fuel + 1, x, cur, acc =>
    if x = 0 then acc.reverse
    else if x % 256 = 255 then decRow fuel (x / 256) [] (cur.reverse :: acc)
    else decRow fuel (x / 256) ((x % 256 - 1) :: cur) acc

/-- Witness lists of one level (one list of `h` per grid point). -/
def decW (x : ℕ) : List (List ℕ) := decRow 1000000 x [] []

/-- A signed 64-bit field (stored with offset `2^63`). -/
def sfield (x : ℕ) : ℤ := (x : ℤ) - 2 ^ 63

/-- Tangent entries `(h, u·2^30, m, A, N)`: 5 fields of 64 bits each, `h` stored as `h + 1`. -/
def decTan : ℕ → ℕ → List (ℕ × ℕ × ℤ × ℤ × ℤ)
  | 0, _ => []
  | fuel + 1, x =>
    if x = 0 then []
    else
      let e := x % 2 ^ 320
      (e % 2 ^ 64 - 1, e / 2 ^ 64 % 2 ^ 64, sfield (e / 2 ^ 128 % 2 ^ 64),
        sfield (e / 2 ^ 192 % 2 ^ 64), sfield (e / 2 ^ 256 % 2 ^ 64)) :: decTan fuel (x / 2 ^ 320)

/-- Root entries `(n, k, g, Troot, m)`: 5 fields of 64 bits each, `n` stored as `n + 1`. -/
def decRoots : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℤ × ℤ)
  | 0, _ => []
  | fuel + 1, x =>
    if x = 0 then []
    else
      let e := x % 2 ^ 320
      (e % 2 ^ 64 - 1, e / 2 ^ 64 % 2 ^ 64, e / 2 ^ 128 % 2 ^ 64,
        sfield (e / 2 ^ 192 % 2 ^ 64), sfield (e / 2 ^ 256 % 2 ^ 64)) :: decRoots fuel (x / 2 ^ 320)

end EnvCert
end R3Cert
