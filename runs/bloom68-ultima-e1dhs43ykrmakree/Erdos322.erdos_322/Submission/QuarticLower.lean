import Submission.Spec

/-!
# An unconditional logarithmic lower bound for four fourth powers

The recurrence `(u, v) ↦ (u - 12v, 4u + v)` preserves the quadratic form
`u² + 3v²` up to a factor of 49. Its first quartic base is a 7-adic unit,
so scaling the first `t + 1` states gives distinct ordered representations of
`2 * 7^(4*t)` as four fourth powers (the fourth base is zero).

This proves unboundedness, not a positive-power lower bound. Neither of the
conjectural theorems in `Submission.Spec` is used; only `representationCount` is.
-/

namespace Erdos322.QuarticLower

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The integer recurrence used to generate the representations. -/
def state : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | i + 1 => ((state i).1 - 12 * (state i).2, 4 * (state i).1 + (state i).2)

/-- The norm of the `i`th state. -/
theorem state_norm (i : ℕ) :
    (state i).1 ^ 2 + 3 * (state i).2 ^ 2 = (7 : ℤ) ^ (2 * i) := by
  induction i with
  | zero => norm_num [state]
  | succ i ih =>
    change ((state i).1 - 12 * (state i).2) ^ 2 +
      3 * (4 * (state i).1 + (state i).2) ^ 2 = 7 ^ (2 * (i + 1))
    calc
      _ = 49 * ((state i).1 ^ 2 + 3 * (state i).2 ^ 2) := by ring
      _ = 7 ^ (2 * (i + 1)) := by
        rw [ih, show 2 * (i + 1) = 2 * i + 2 by omega, pow_add]
        ring

/-- From the first step on, the residues are `(2^i, 4*2^i)` modulo 7. -/
theorem state_mod_seven (i : ℕ) :
    ((state (i + 1)).1 : ZMod 7) = 2 ^ i ∧
      ((state (i + 1)).2 : ZMod 7) = 4 * 2 ^ i := by
  induction i with
  | zero => norm_num [state]
  | succ i ih =>
    change (((state (i + 1)).1 - 12 * (state (i + 1)).2 : ℤ) : ZMod 7) =
        2 ^ (i + 1) ∧
      (((4 * (state (i + 1)).1 + (state (i + 1)).2 : ℤ) : ZMod 7)) =
        4 * 2 ^ (i + 1)
    push_cast
    rw [ih.1, ih.2]
    constructor
    · calc
        _ = (1 - 12 * 4 : ZMod 7) * 2 ^ i := by ring
        _ = 2 ^ (i + 1) := by
          rw [show (1 - 12 * 4 : ZMod 7) = 2 by decide, pow_succ]
          ring
    · ring

/-- The unscaled first coordinate is never divisible by 7. -/
theorem first_unit (i : ℕ) : ¬ 7 ∣ ((state i).1 - (state i).2).natAbs := by
  cases i with
  | zero => norm_num [state]
  | succ i =>
    intro h
    have hz : (((state (i + 1)).1 - (state (i + 1)).2 : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 (Int.natCast_dvd.mpr h)
    push_cast at hz
    rw [(state_mod_seven i).1, (state_mod_seven i).2] at hz
    have heq : (2 : ZMod 7) ^ i - 4 * 2 ^ i = (1 - 4) * 2 ^ i := by ring
    rw [heq] at hz
    exact (mul_ne_zero (by decide : (1 - 4 : ZMod 7) ≠ 0)
      (pow_ne_zero i (by decide : (2 : ZMod 7) ≠ 0))) hz

/-- The quartic identity underlying the construction. -/
theorem quartic_identity (u v : ℤ) :
    (u - v) ^ 4 + (2 * v) ^ 4 + (u + v) ^ 4 = 2 * (u ^ 2 + 3 * v ^ 2) ^ 2 := by
  ring

/-- Taking natural absolute values does not change a fourth power. -/
theorem natAbs_fourth (z : ℤ) : (z.natAbs : ℤ) ^ 4 = z ^ 4 := by
  rw [Int.natCast_natAbs]
  exact (by decide : Even 4).pow_abs z

/-- The four nonnegative bases at scale `t`. -/
def bases (t i : ℕ) : Fin 4 → ℕ :=
  ![7 ^ (t - i) * ((state i).1 - (state i).2).natAbs,
    7 ^ (t - i) * (2 * (state i).2).natAbs,
    7 ^ (t - i) * ((state i).1 + (state i).2).natAbs, 0]

/-- These bases give the required sum of fourth powers. -/
theorem bases_sum (t i : ℕ) (hi : i ≤ t) :
    ∑ j : Fin 4, (bases t i j) ^ 4 = 2 * 7 ^ (4 * t) := by
  rw [Fin.sum_univ_four]
  change (7 ^ (t - i) * ((state i).1 - (state i).2).natAbs) ^ 4 +
    (7 ^ (t - i) * (2 * (state i).2).natAbs) ^ 4 +
    (7 ^ (t - i) * ((state i).1 + (state i).2).natAbs) ^ 4 + 0 ^ 4 = _
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_pow, natAbs_fourth, zero_pow (by decide : 4 ≠ 0), add_zero]
  calc
    _ = (7 ^ (t - i) : ℤ) ^ 4 *
        (((state i).1 - (state i).2) ^ 4 + (2 * (state i).2) ^ 4 +
          ((state i).1 + (state i).2) ^ 4) := by ring
    _ = 2 * 7 ^ (4 * t) := by
      rw [quartic_identity, state_norm]
      simp only [← pow_mul]
      rw [show (2 * i) * 2 = 4 * i by omega]
      calc
        (7 : ℤ) ^ ((t - i) * 4) * (2 * 7 ^ (4 * i)) =
            2 * (7 ^ ((t - i) * 4) * 7 ^ (4 * i)) := by ring
        _ = _ := by rw [← pow_add, show (t - i) * 4 + 4 * i = 4 * t by omega]

/-- Each base satisfies the finite bound in `representationCount`. -/
theorem bases_le (t i : ℕ) (hi : i ≤ t) (j : Fin 4) :
    bases t i j ≤ 2 * 7 ^ (4 * t) := by
  calc
    bases t i j ≤ (bases t i j) ^ 4 := Nat.le_self_pow (by decide) _
    _ ≤ ∑ k : Fin 4, (bases t i k) ^ 4 :=
      Finset.single_le_sum (fun k _ ↦ Nat.zero_le ((bases t i k) ^ 4)) (Finset.mem_univ j)
    _ = 2 * 7 ^ (4 * t) := bases_sum t i hi

/-- The first coordinate has exactly `t - i` factors of 7. -/
theorem first_exact_divisibility (t i : ℕ) :
    7 ^ (t - i) ∣ bases t i 0 ∧ ¬ 7 ^ (t - i + 1) ∣ bases t i 0 := by
  change 7 ^ (t - i) ∣ 7 ^ (t - i) * ((state i).1 - (state i).2).natAbs ∧ _
  refine ⟨dvd_mul_right _ _, ?_⟩
  change ¬ 7 ^ (t - i + 1) ∣ 7 ^ (t - i) * ((state i).1 - (state i).2).natAbs
  rw [pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)]
  exact first_unit i

/-- A tuple in exactly the bounded type used by `representationCount`. -/
def boundedTuple (t i : ℕ) (hi : i ≤ t) : Fin 4 → Fin (2 * 7 ^ (4 * t) + 1) :=
  fun j ↦ ⟨bases t i j, Nat.lt_succ_of_le (bases_le t i hi j)⟩

/-- Different indices have different first coordinates, hence different tuples. -/
theorem boundedTuple_injective (t : ℕ) :
    Function.Injective (fun i : Fin (t + 1) ↦
      boundedTuple t i (Nat.le_of_lt_succ i.isLt)) := by
  intro i j hij
  have hzero := congrArg (fun a : Fin 4 → Fin (2 * 7 ^ (4 * t) + 1) ↦ (a 0).val) hij
  change bases t i 0 = bases t j 0 at hzero
  have hnotlt (a b : Fin (t + 1)) (heq : bases t a 0 = bases t b 0) : ¬ a < b := by
    intro hab
    have hexp : t - (b : ℕ) + 1 ≤ t - (a : ℕ) := by
      have ha := a.isLt
      have hb := b.isLt
      have hab' : (a : ℕ) < b := hab
      omega
    have hd : 7 ^ (t - (b : ℕ) + 1) ∣ bases t a 0 :=
      (pow_dvd_pow 7 hexp).trans (first_exact_divisibility t a).1
    rw [heq] at hd
    exact (first_exact_divisibility t b).2 hd
  exact le_antisymm (le_of_not_gt (hnotlt j i hzero.symm)) (le_of_not_gt (hnotlt i j hzero))

/-- Unconditional logarithmic partial result for four fourth powers. -/
theorem representationCount_lower_bound (t : ℕ) :
    t + 1 ≤ Erdos322.representationCount 4 (2 * 7 ^ (4 * t)) := by
  classical
  let f : Fin (t + 1) → (Fin 4 → Fin (2 * 7 ^ (4 * t) + 1)) :=
    fun i ↦ boundedTuple t i (Nat.le_of_lt_succ i.isLt)
  let s := (Finset.univ : Finset (Fin 4 → Fin (2 * 7 ^ (4 * t) + 1))).filter
    (fun a ↦ ∑ j, (a j : ℕ) ^ 4 = 2 * 7 ^ (4 * t))
  have hmem (i : Fin (t + 1)) : f i ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact bases_sum t i (Nat.le_of_lt_succ i.isLt)
  calc
    t + 1 = (Finset.univ : Finset (Fin (t + 1))).card := by simp
    _ ≤ s.card := Finset.card_le_card_of_injOn f (fun i _ ↦ hmem i)
      (boundedTuple_injective t).injOn
    _ = representationCount 4 (2 * 7 ^ (4 * t)) := rfl

/-- In particular the quartic representation counts are unbounded. -/
theorem representationCount_unbounded (B : ℕ) :
    ∃ n : ℕ, B < Erdos322.representationCount 4 n := by
  refine ⟨2 * 7 ^ (4 * B), ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self B) (representationCount_lower_bound B)

/-- The targets in the lower bound are distinct. -/
theorem target_injective : Function.Injective (fun t : ℕ ↦ 2 * 7 ^ (4 * t)) := by
  intro a b hab
  apply Nat.mul_left_cancel (n := 4) (by decide)
  exact Nat.pow_right_injective (by decide) (Nat.mul_left_cancel (by decide) hab)

/-- Beyond any fixed count there are infinitely many quartic targets. -/
theorem infinite_large_count (B : ℕ) :
    {n : ℕ | B < Erdos322.representationCount 4 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ ↦ 2 * 7 ^ (4 * (B + m)))
  · intro a b hab
    exact Nat.add_left_cancel (target_injective hab)
  · intro m
    change B < representationCount 4 (2 * 7 ^ (4 * (B + m)))
    have h := representationCount_lower_bound (B + m)
    omega

end Erdos322.QuarticLower

#print axioms Erdos322.QuarticLower.state_norm
#print axioms Erdos322.QuarticLower.state_mod_seven
#print axioms Erdos322.QuarticLower.first_unit
#print axioms Erdos322.QuarticLower.quartic_identity
#print axioms Erdos322.QuarticLower.natAbs_fourth
#print axioms Erdos322.QuarticLower.bases_sum
#print axioms Erdos322.QuarticLower.bases_le
#print axioms Erdos322.QuarticLower.first_exact_divisibility
#print axioms Erdos322.QuarticLower.boundedTuple_injective
#print axioms Erdos322.QuarticLower.representationCount_lower_bound
#print axioms Erdos322.QuarticLower.representationCount_unbounded
#print axioms Erdos322.QuarticLower.target_injective
#print axioms Erdos322.QuarticLower.infinite_large_count
