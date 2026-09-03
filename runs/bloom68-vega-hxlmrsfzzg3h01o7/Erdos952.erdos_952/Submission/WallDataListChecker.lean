import Submission.WallDataChecker

/-!
# List-of-natural-number encoding of black-wall chunks

A code is `4 * label + direction` in `0,...,39`. This avoids conversion of a
large string literal to its byte array during kernel reduction. All checks and
path-length semantics agree with the byte checker in `WallDataChecker`.
-/

namespace Erdos952.WallData

/-- Validate a compact code and its claimed blackness label. -/
def packedVertexCheck (c : ℕ) (p : GaussianInt) : Bool :=
  c < 40 && labelCheck p.re p.im (c / 4)

theorem packedVertexCheck_sound {c : ℕ} {p : GaussianInt}
    (h : packedVertexCheck c p = true) : Black p :=
  ⟨c / 4, labelCheck_sound _ _ _ (Bool.and_eq_true_iff.mp h).2⟩

/-- Check exactly `n` edges encoded by exactly `n + 1` compact codes. -/
def checkCodes (target : GaussianInt) : ℕ → List ℕ → GaussianInt → Bool
  | 0, [c], p => packedVertexCheck c p && (p.re == target.re && p.im == target.im)
  | n + 1, c :: cs, p =>
      packedVertexCheck c p && checkCodes target n cs (move p (c % 4))
  | _, _, _ => false

/-- Kernel-checker soundness with an exact edge count. -/
theorem checkCodes_sound (target : GaussianInt) (n : ℕ) (cs : List ℕ)
    (p : GaussianInt) (h : checkCodes target n cs p = true) : BlackPath n p target := by
  induction n generalizing cs p with
  | zero =>
      cases cs with
      | nil => simp [checkCodes] at h
      | cons c cs =>
          cases cs with
          | nil =>
              simp only [checkCodes, Bool.and_eq_true, beq_iff_eq] at h
              have hp : p = target := Zsqrtd.ext h.2.1 h.2.2
              subst target
              exact .single (packedVertexCheck_sound h.1)
          | cons d ds => simp [checkCodes] at h
  | succ n ih =>
      cases cs with
      | nil => simp [checkCodes] at h
      | cons c cs =>
          have hh := Bool.and_eq_true_iff.mp h
          have ht := ih cs (move p (c % 4)) hh.2
          exact .cons ⟨packedVertexCheck_sound hh.1, ht.black_start,
            move_norm p _ (Nat.mod_lt _ (by decide))⟩ ht

end Erdos952.WallData
