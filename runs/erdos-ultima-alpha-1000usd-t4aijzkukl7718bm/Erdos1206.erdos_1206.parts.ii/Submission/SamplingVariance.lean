import Submission.FiniteProductSampling

/-! A bounded-degree second-moment estimate for finite coordinate sampling. -/
namespace Erdos1206.SamplingVariance
open Finset FiniteProductSampling
open scoped BigOperators Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [NeZero k]

omit [Fintype V] in
lemma overlap_card_le (E : Finset I) (F : I → Finset V) {i : I} {r D : ℕ}
    (hi : (F i).card ≤ r) (hD : ∀ v, (E.filter (fun j => v∈F j)).card ≤ D) :
    (E.filter (fun j => ¬Disjoint (F i) (F j))).card ≤ r*D := by
  have hs : E.filter (fun j => ¬Disjoint (F i) (F j)) ⊆
      (F i).biUnion (fun v => E.filter (fun j => v∈F j)) := by
    intro j hj
    obtain ⟨hj,hov⟩ := mem_filter.mp hj
    obtain ⟨v,hvi,hvj⟩ := not_disjoint_iff.mp hov
    exact mem_biUnion.mpr ⟨v,hvi,mem_filter.mpr ⟨hj,hvj⟩⟩
  calc
    _ ≤ ((F i).biUnion (fun v => E.filter (fun j => v∈F j))).card := card_le_card hs
    _ ≤ ∑ v ∈ F i, (E.filter (fun j => v∈F j)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ F i, D := sum_le_sum (fun v _ => hD v)
    _ = (F i).card*D := by simp
    _ ≤ r*D := Nat.mul_le_mul_right _ hi

/-- The bound allows repeated supports and requires only an upper bound on
support size, not uniformity of the family. -/
theorem variance_le (E : Finset I) (F : I → Finset V) {r D : ℕ}
    (hr : ∀ i∈E, (F i).card ≤ r)
    (hD : ∀ v, (E.filter (fun i => v∈F i)).card ≤ D) :
    (𝔼 ω : V → Fin k, (∑ i∈E, centered (F i) ω)^2) ≤ (E.card:ℝ)*r*D := by
  have he (ω : V → Fin k) : (∑ i∈E, centered (F i) ω)^2=
      ∑ i∈E, ∑ j∈E, centered (F i) ω*centered (F j) ω := by
    rw [pow_two,sum_mul_sum]
  simp_rw [he]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm]
  have hrow (i : I) (hi : i∈E) :
      (∑ j∈E, (𝔼 ω : V → Fin k, centered (F i) ω*centered (F j) ω)) ≤ (r*D:ℕ) := by
    calc
      _ ≤ ∑ j∈E, if ¬Disjoint (F i) (F j) then (1:ℝ) else 0 := by
        apply sum_le_sum
        intro j hj
        by_cases hd : Disjoint (F i) (F j)
        · rw [if_neg (not_not.mpr hd),covariance_zero_of_disjoint hd]
        · rw [if_pos hd]
          exact covariance_le_one _ _
      _ = ((E.filter (fun j => ¬Disjoint (F i) (F j))).card:ℝ) := by rw [sum_boole]
      _ ≤ _ := by exact_mod_cast overlap_card_le E F (hr i hi) hD
  calc
    _ ≤ ∑ _i∈E, ((r*D:ℕ):ℝ) := sum_le_sum hrow
    _ = _ := by simp [Nat.cast_mul,mul_assoc]

/-- Simultaneous finite score bands from a total second-moment budget.
This is a finite averaging statement, not an assertion about limiting density. -/
theorem exists_simultaneous_bands {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    (T : Finset J) (f : J → Ω → ℝ) (c : J → ℝ)
    (hvar : ∀ j∈T, (𝔼 ω, (f j ω)^2) ≤ c j)
    (hcost : ∑ j∈T, c j < 1) :
    ∃ ω : Ω, ∀ j∈T, |f j ω| < 1 := by
  have he : (𝔼 ω, ∑ j∈T, (f j ω)^2) < 1 := by
    rw [expect_sum_comm]
    exact (sum_le_sum hvar).trans_lt hcost
  obtain ⟨ω,_,hω⟩ := exists_lt_of_expect_lt univ_nonempty he
  refine ⟨ω,fun j hj => ?_⟩
  have hsingle := single_le_sum (fun j _ => sq_nonneg (f j ω)) hj
  have hs : (f j ω)^2 < 1 := hsingle.trans_lt hω
  nlinarith [sq_abs (f j ω),abs_nonneg (f j ω)]

/-- A joint budget for two scores at every scale. -/
theorem exists_simultaneous_two_bands {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    (T : Finset J) (f g : J → Ω → ℝ) (c : J → ℝ)
    (hvar : ∀ j∈T, (𝔼 ω, (f j ω)^2)+(𝔼 ω, (g j ω)^2) ≤ c j)
    (hcost : ∑ j∈T, c j < 1) :
    ∃ ω : Ω, ∀ j∈T, |f j ω| < 1 ∧ |g j ω| < 1 := by
  have he : (𝔼 ω, ∑ j∈T, ((f j ω)^2+(g j ω)^2)) < 1 := by
    rw [expect_sum_comm]
    simp_rw [expect_add_distrib]
    exact (sum_le_sum hvar).trans_lt hcost
  obtain ⟨ω,_,hω⟩ := exists_lt_of_expect_lt univ_nonempty he
  refine ⟨ω,fun j hj => ?_⟩
  have hsingle := single_le_sum (fun j _ => add_nonneg (sq_nonneg (f j ω)) (sq_nonneg (g j ω))) hj
  have hs : (f j ω)^2+(g j ω)^2 < 1 := hsingle.trans_lt hω
  constructor
  · nlinarith [sq_abs (f j ω),abs_nonneg (f j ω),sq_nonneg (g j ω)]
  · nlinarith [sq_abs (g j ω),abs_nonneg (g j ω),sq_nonneg (f j ω)]

#print axioms exists_simultaneous_two_bands
#print axioms variance_le
#print axioms exists_simultaneous_bands
end Erdos1206.SamplingVariance
