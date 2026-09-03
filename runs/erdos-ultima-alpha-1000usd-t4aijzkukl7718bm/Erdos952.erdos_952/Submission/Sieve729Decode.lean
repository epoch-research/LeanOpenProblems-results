import FormalConjecturesUtil

/-!\nA data-only elaborator for compactly stored natural-number masks.
It emits a natural-number literal, not a proof. Every claimed property of the
resulting masks is checked independently by kernel reduction.
-/

namespace Erdos952Investigation.Sieve729

private def packWords (a : Array ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, start, len =>
    if len = 0 then 0 else if len = 1 then a[start]!
    else
      let lo := len / 2
      Nat.lor (packWords a fuel start lo)
        (Nat.shiftLeft (packWords a fuel (start + lo) (len - lo)) (64 * lo))

private def decodeRow (s : String) : ℕ := Id.run do
  let mut a : Array ℕ := Array.replicate 10515 0
  for segment in s.splitOn ";" do
    if segment != "" then
      let parts := segment.splitOn ":"
      let start := (parts[0]!.toNat?).getD 0
      let chars := parts[1]!.toUTF8
      for j in [:chars.size / 16] do
        let mut word : ℕ := 0
        for k in [:16] do
          let c := chars[16 * j + k]!.toNat
          let d := if c ≤ 57 then c - 48 else c - 87
          word := 16 * word + d
        a := a.set! (start + j) word
  return packWords a 32 0 a.size

open Lean Elab Term in
elab "rowData% " s:str : term => do
  return mkNatLit (decodeRow s.getString)

example : (rowData% "0:0000000000000003;2:0000000000000005;" : ℕ) =
    3 + (5 <<< 128) := by decide +kernel

end Erdos952Investigation.Sieve729
