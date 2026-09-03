import Submission.FixedGapCubes
import Submission.SparseHarmonic
import Submission.SummableDivisorCover

/-!
Summable divisor sieves for individual fixed-gap cubic collision families.
No uniform bound over all gap pairs is asserted.
-/

namespace Erdos1206
open scoped Classical

lemma quadratic_abscissae_reciprocals_summable {A B : ℕ} {C : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : C ≠ 0) :
    Summable (fun n : ℕ => if n ∈ quadraticPositiveAbscissae A B C then (1 : ℝ) / n else 0) :=
  summable_reciprocals_of_pow_prefix_bound (quadratic_abscissae_pow_prefix_bound hA hB hC)

/-- Upper endpoints of the first prescribed cubic difference. -/
def fixedGapUpperRoots (h k : ℕ) : Set ℕ :=
  (fun x : ℕ => x + h) '' fixedGapCubeBases h k

lemma fixedGapUpperRoots_reciprocals_summable {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hne : h ≠ k) :
    Summable (fun n : ℕ => if n ∈ fixedGapUpperRoots h k then (1 : ℝ) / n else 0) := by
  let C : ℤ := (k : ℤ) ^ 3 - h ^ 3
  have hC : C ≠ 0 := by
    intro he
    have he' : k ^ 3 = h ^ 3 := by exact_mod_cast sub_eq_zero.mp he
    exact hne (Nat.pow_left_injective (by decide : 3 ≠ 0) he').symm
  let K := (3 * h) * (2 * (3 * k + C.natAbs + 1) + 1) + 2
  apply summable_reciprocals_of_pow_prefix_bound (C := 8 * K)
  intro j
  have hmap : ∀ r ∈ fixedGapUpperRoots h k ∩ Set.Iio (16 ^ j),
      2 * r - h ∈ quadraticPositiveAbscissae (3 * h) (3 * k) C ∩ Set.Iio (16 ^ (j + 1)) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hlt⟩
    have he : 2 * (x + h) - h = 2 * x + h := by omega
    refine ⟨?_, ?_⟩
    · rw [he]
      exact fixedGapCubeBase_centered hh hk hx
    · change 2 * ((fun x : ℕ => x + h) x) - h < 16 ^ (j + 1)
      change x + h < 16 ^ j at hlt
      dsimp only
      rw [pow_succ]
      omega
  have hinj : Set.InjOn (fun r : ℕ => 2 * r - h)
      (fixedGapUpperRoots h k ∩ Set.Iio (16 ^ j)) := by
    rintro _ ⟨⟨x, hx, rfl⟩, _⟩ _ ⟨⟨y, hy, rfl⟩, _⟩ he
    dsimp only at he ⊢
    omega
  have hc := Set.ncard_le_ncard_of_injOn (fun r : ℕ => 2 * r - h) hmap hinj
  have hq := quadratic_abscissae_pow_prefix_bound
    (Nat.mul_pos (by decide : 0 < 3) hh) (Nat.mul_pos (by decide : 0 < 3) hk) hC (j + 1)
  change _ ≤ K * 8 ^ (j + 1) at hq
  rw [pow_succ 8] at hq
  nlinarith

lemma one_not_mem_fixedGapUpperRoots {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hne : h ≠ k) :
    1 ∉ fixedGapUpperRoots h k := by
  rintro ⟨x, ⟨y, he⟩, hx⟩
  dsimp only at hx
  have hh1 : h = 1 := by omega
  have hx0 : x = 0 := by omega
  subst h x
  simp only [zero_add, zero_pow (by decide : 3 ≠ 0)] at he
  have hyk : (y + 1) ^ 3 ≤ (y + k) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hy0 : y = 0 := by nlinarith
  subst y
  norm_num at he
  have hk1 : k = 1 := Nat.pow_left_injective (by decide : 3 ≠ 0) (by simpa using he.symm)
  exact hne hk1.symm

/-- All integer dilates of one fixed-gap family can be excluded at positive
lower density. This is not simultaneous avoidance of all gap pairs. -/
lemma positive_density_sieve_for_fixed_gaps {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hne : h ≠ k) :
    ∃ A : Set ℕ, 0 < A.lowerDensity ∧
      ∀ x y q : ℕ, (x + h) ^ 3 + y ^ 3 = x ^ 3 + (y + k) ^ 3 →
        q * (x + h) ∉ A := by
  let A := divisorAvoider (fixedGapUpperRoots h k)
  refine ⟨A, divisorAvoider_positive_density_of_summable
    (one_not_mem_fixedGapUpperRoots hh hk hne)
    (fixedGapUpperRoots_reciprocals_summable hh hk hne), ?_⟩
  intro x y q he hmem
  exact hmem.2 (x + h) ⟨x, ⟨y, he⟩, rfl⟩ (dvd_mul_left (x + h) q)

/-- Any finite list of fixed-gap families, including all their integer dilates,
can be avoided simultaneously by a set of positive lower density. -/
lemma positive_density_sieve_for_finite_gap_pairs (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2) :
    ∃ A : Set ℕ, 0 < A.lowerDensity ∧
      ∀ p ∈ P, ∀ x y q : ℕ,
        (x + p.1) ^ 3 + y ^ 3 = x ^ 3 + (y + p.2) ^ 3 →
          q * (x + p.1) ∉ A := by
  classical
  let B : Set ℕ := ⋃ p ∈ P, fixedGapUpperRoots p.1 p.2
  let w : (ℕ × ℕ) → ℕ → ℝ := fun p n =>
    if n ∈ fixedGapUpperRoots p.1 p.2 then 1 / n else 0
  have hw (p : ℕ × ℕ) (n : ℕ) : 0 ≤ w p n := by
    dsimp [w]; split_ifs <;> positivity
  have hs : Summable (fun n => ∑ p ∈ P, w p n) := by
    apply summable_sum
    intro p hp
    exact fixedGapUpperRoots_reciprocals_summable (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2
  have hBsum : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ) / n else 0) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) hs
    split_ifs with hn
    · obtain ⟨p, hp, hn⟩ := Set.mem_iUnion₂.mp hn
      have hh := Finset.single_le_sum (fun p _ => hw p n) hp
      simpa only [w, if_pos hn] using hh
    · exact Finset.sum_nonneg (fun p _ => hw p n)
  have hB1 : 1 ∉ B := by
    intro hn
    obtain ⟨p, hp, hn⟩ := Set.mem_iUnion₂.mp hn
    exact one_not_mem_fixedGapUpperRoots (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2 hn
  refine ⟨divisorAvoider B, divisorAvoider_positive_density_of_summable hB1 hBsum, ?_⟩
  intro p hp x y q he hmem
  have hm : x + p.1 ∈ B := Set.mem_iUnion₂.mpr ⟨p, hp, ⟨x, ⟨y, he⟩, rfl⟩⟩
  exact hmem.2 (x + p.1) hm (dvd_mul_left (x + p.1) q)

#print axioms positive_density_sieve_for_finite_gap_pairs
#print axioms quadratic_abscissae_reciprocals_summable
#print axioms fixedGapUpperRoots_reciprocals_summable
#print axioms positive_density_sieve_for_fixed_gaps

end Erdos1206
