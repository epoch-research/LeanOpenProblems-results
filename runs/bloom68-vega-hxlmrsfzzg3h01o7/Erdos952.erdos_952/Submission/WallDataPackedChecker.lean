import Submission.WallDataListChecker

/-!
# Compact base-forty words

Each natural-number word contains a nonempty block of codes in little-endian
base forty, followed by a most-significant sentinel digit `1`. This encodes
leading zero codes without ambiguity. Several words form a `List Nat`.

Only the word currently being read is divided by forty. In particular, the
kernel never needs to materialize the full list of decoded vertex codes or
Gaussian positions. The word size is not trusted or fixed by this checker.
-/

namespace Erdos952.WallData

/-- Read one compact code. Reject empty/malformed words. A quotient of one
is the end-of-word sentinel, so the next code will come from the next word. -/
def popCode : List ℕ → Option (ℕ × List ℕ)
  | [] => none
  | word :: words =>
      if word < 40 then none
      else some (word % 40, if word / 40 = 1 then words else word / 40 :: words)

/-- Check a word-packed list certificate of exactly `n` edges.
The final vertex is checked without taking its outgoing direction. -/
def checkPacked (target : GaussianInt) : ℕ → List ℕ → GaussianInt → Bool
  | 0, words, p =>
      match popCode words with
      | some (c, []) => packedVertexCheck c p && (p.re == target.re && p.im == target.im)
      | _ => false
  | n + 1, words, p =>
      match popCode words with
      | some (c, rest) =>
          packedVertexCheck c p && checkPacked target n rest (move p (c % 4))
      | none => false

/-- Accepting a word-packed certificate proves a black path of exactly `n` edges. -/
theorem checkPacked_sound (target : GaussianInt) (n : ℕ) (words : List ℕ)
    (p : GaussianInt) (h : checkPacked target n words p = true) : BlackPath n p target := by
  induction n generalizing words p with
  | zero =>
      simp only [checkPacked] at h
      split at h
      · rename_i c hpop
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        have hp : p = target := Zsqrtd.ext h.2.1 h.2.2
        subst target
        exact .single (packedVertexCheck_sound h.1)
      · contradiction
  | succ n ih =>
      simp only [checkPacked] at h
      split at h
      · rename_i c rest hpop
        have hh := Bool.and_eq_true_iff.mp h
        have ht := ih rest (move p (c % 4)) hh.2
        exact .cons ⟨packedVertexCheck_sound hh.1, ht.black_start,
          move_norm p _ (Nat.mod_lt _ (by decide))⟩ ht
      · contradiction

end Erdos952.WallData
