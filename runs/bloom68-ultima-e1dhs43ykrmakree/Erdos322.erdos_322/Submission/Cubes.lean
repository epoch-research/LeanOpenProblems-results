import Submission.Spec

/-!
# The cubic instance of Erdős problem 322

Mahler's identity gives an explicit family of nonnegative, ordered representations
as three cubes. In particular, the exponent `1 / 24` works for `k = 3`.
This is partial progress only: no assertion for `k ≥ 4` or the universal conjecture
is proved here, and neither conjectural theorem from `Submission.Spec` is used.
-/

namespace Erdos322
namespace Cubes

/-- Mahler's polynomial identity, before passing to natural-number subtraction. -/
theorem mahler_identity (u v : ℤ) :
    (9 * u ^ 4) ^ 3 + (3 * u * v ^ 3 - 9 * u ^ 4) ^ 3 +
      (v ^ 4 - 9 * u ^ 3 * v) ^ 3 = v ^ 12 := by
  ring

/-- The three natural bases in Mahler's identity. -/
def bases (u v : ℕ) : Fin 3 → ℕ :=
  ![9 * u ^ 4, 3 * u * v ^ 3 - 9 * u ^ 4, v ^ 4 - 9 * u ^ 3 * v]

/-- In the range `3u ≤ v`, neither natural-number subtraction is truncated. -/
theorem subtraction_bounds (u v : ℕ) (h : 3 * u ≤ v) :
    9 * u ^ 4 ≤ 3 * u * v ^ 3 ∧ 9 * u ^ 3 * v ≤ v ^ 4 := by
  have hcube : 27 * u ^ 3 ≤ v ^ 3 := by
    simpa only [mul_pow, show (3 : ℕ) ^ 3 = 27 from rfl] using
      Nat.pow_le_pow_left h 3
  have hsmall : 9 * u ^ 3 ≤ v ^ 3 := by omega
  constructor
  · calc
      9 * u ^ 4 = u * (9 * u ^ 3) := by ring
      _ ≤ u * v ^ 3 := Nat.mul_le_mul_left u hsmall
      _ ≤ 3 * u * v ^ 3 := Nat.mul_le_mul_right (v ^ 3) (by omega)
  · nlinarith [Nat.mul_le_mul_right v hsmall]

/-- Mahler's identity holds for the natural bases when `3u ≤ v`. -/
theorem bases_sum (u v : ℕ) (h : 3 * u ≤ v) :
    ∑ i : Fin 3, (bases u v i) ^ 3 = v ^ 12 := by
  obtain ⟨hb, hc⟩ := subtraction_bounds u v h
  rw [Fin.sum_univ_three]
  change (9 * u ^ 4) ^ 3 + (3 * u * v ^ 3 - 9 * u ^ 4) ^ 3 +
    (v ^ 4 - 9 * u ^ 3 * v) ^ 3 = v ^ 12
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hb, Nat.cast_sub hc]
  exact mahler_identity (u : ℤ) (v : ℤ)

/-- Every base is within the bound used by `representationCount`. -/
theorem bases_le (u v : ℕ) (h : 3 * u ≤ v) (i : Fin 3) :
    bases u v i ≤ v ^ 12 := by
  calc
    bases u v i ≤ (bases u v i) ^ 3 := Nat.le_self_pow (by decide) _
    _ ≤ ∑ j : Fin 3, (bases u v j) ^ 3 :=
      Finset.single_le_sum (fun j _ ↦ Nat.zero_le ((bases u v j) ^ 3))
        (Finset.mem_univ i)
    _ = v ^ 12 := bases_sum u v h

/-- A tuple of exactly the bounded type appearing in `representationCount`. -/
def boundedTuple (u v : ℕ) (h : 3 * u ≤ v) : Fin 3 → Fin (v ^ 12 + 1) :=
  fun i ↦ ⟨bases u v i, Nat.lt_succ_of_le (bases_le u v h i)⟩

/-- Varying `u` from `0` to `t` supplies `t + 1` distinct representations. -/
theorem representationCount_lower_bound (t : ℕ) :
    t + 1 ≤ representationCount 3 ((3 * t) ^ 12) := by
  classical
  let f : Fin (t + 1) → (Fin 3 → Fin ((3 * t) ^ 12 + 1)) :=
    fun u ↦ boundedTuple u (3 * t)
      (Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ u.isLt))
  have hf : Function.Injective f := by
    intro a b hab
    have hzero := congrArg (fun x : Fin 3 → Fin ((3 * t) ^ 12 + 1) ↦ (x 0).val) hab
    change 9 * (a : ℕ) ^ 4 = 9 * (b : ℕ) ^ 4 at hzero
    exact Fin.ext (Nat.pow_left_injective (by decide)
      (Nat.mul_left_cancel (by decide) hzero))
  let s := (Finset.univ : Finset (Fin 3 → Fin ((3 * t) ^ 12 + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ 3 = (3 * t) ^ 12)
  have hmem (u : Fin (t + 1)) : f u ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change ∑ i : Fin 3, (bases (u : ℕ) (3 * t) i) ^ 3 = (3 * t) ^ 12
    exact bases_sum _ _ (Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ u.isLt))
  calc
    t + 1 = (Finset.univ : Finset (Fin (t + 1))).card := by simp
    _ ≤ s.card := Finset.card_le_card_of_injOn f (fun u _ ↦ hmem u) hf.injOn
    _ = representationCount 3 ((3 * t) ^ 12) := rfl

/-- For `v = 9m²`, the target is `(3m)^24` and there are at least `3m² + 1` tuples. -/
theorem representationCount_special (m : ℕ) :
    3 * m ^ 2 + 1 ≤ representationCount 3 ((3 * m) ^ 24) := by
  have heq : (3 * (3 * m ^ 2)) ^ 12 = (3 * m) ^ 24 := by ring
  rw [← heq]
  exact representationCount_lower_bound (3 * m ^ 2)

/-- Each member of the explicit family satisfies the desired strict power bound. -/
theorem special_power_bound (m : ℕ) :
    (((3 * m) ^ 24 : ℕ) : ℝ) ^ (1 / 24 : ℝ) <
      representationCount 3 ((3 * m) ^ 24) := by
  have hrpow : (((3 * m) ^ 24 : ℕ) : ℝ) ^ (1 / 24 : ℝ) = 3 * (m : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, one_div] using
      (Real.pow_rpow_inv_natCast (x := 3 * (m : ℝ)) (n := 24)
        (by positivity) (by decide))
  rw [hrpow]
  have hstrict : 3 * m < 3 * m ^ 2 + 1 := by
    have hs : m ≤ m ^ 2 := Nat.le_self_pow (by decide) m
    omega
  have hlt := lt_of_lt_of_le hstrict (representationCount_special m)
  exact_mod_cast hlt

/-- The cubic power lower bound holds for infinitely many natural targets. -/
theorem infinite_power_bound :
    {n : ℕ | (n : ℝ) ^ (1 / 24 : ℝ) < representationCount 3 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ ↦ (3 * m) ^ 24)
  · intro a b hab
    exact Nat.mul_left_cancel (by decide) (Nat.pow_left_injective (by decide) hab)
  · intro m
    exact special_power_bound m

end Cubes

/-- Validated partial progress on Erdős problem 322: only the instance `k = 3`. -/
theorem erdos_322_cubes :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite := by
  exact ⟨1 / 24, by norm_num, Cubes.infinite_power_bound⟩

end Erdos322

#print axioms Erdos322.Cubes.infinite_power_bound
#print axioms Erdos322.erdos_322_cubes
