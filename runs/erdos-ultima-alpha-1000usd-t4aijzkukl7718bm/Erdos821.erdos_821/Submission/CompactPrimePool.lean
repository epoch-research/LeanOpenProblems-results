import Submission.LogarithmicOverlap

/-!
# A compact logarithmic input-prime pool supports only subpower families

This controls the hypothesis that would make the logarithmic overlap bound
produce a fixed positive pair proportion. It concerns families inside a
specified pool, not the unrestricted inverse-totient multiplicity.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.LogarithmicOverlap
set_option maxHeartbeats 2000000

lemma squarefree_family_card_le_pool_powerset (F P : Finset ℕ)
    (hF : ∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P) :
    F.card ≤ 2^P.card := by
  have hmap : Set.MapsTo Nat.primeFactors (↑F : Set ℕ) (↑P.powerset : Set (Finset ℕ)) := by
    intro a ha
    exact mem_powerset.mpr (hF a ha).2
  have hinj : Set.InjOn Nat.primeFactors (↑F : Set ℕ) := by
    intro a ha b hb he
    have ha' := Nat.prod_primeFactors_of_squarefree (hF a ha).1
    have hb' := Nat.prod_primeFactors_of_squarefree (hF b hb).1
    rw [← ha', ← hb', he]
  simpa only [card_powerset] using card_le_card_of_injOn Nat.primeFactors hmap hinj

lemma pool_card_le_weight (P : Finset ℕ) (R : ℕ) (hR : 2 ≤ R) :
    (P.card : ℝ) ≤ ((R : ℝ)+1)+poolWeight P/Real.log (R : ℝ) := by
  let S := P.filter (fun p => p ≤ R)
  let T := P.filter (fun p => ¬p ≤ R)
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hcardS : S.card ≤ R+1 := by
    apply le_trans (card_le_card (t := range (R+1)) ?_) (card_range _).le
    intro p hp
    exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
  have htail : (T.card : ℝ)*Real.log (R : ℝ) ≤ poolWeight P := by
    calc
      _ = ∑ _p ∈ T, Real.log (R : ℝ) := by simp
      _ ≤ ∑ p ∈ T, primeWeight p := by
        apply sum_le_sum
        intro p hp
        have hpR : R ≤ p-1 := by have := (mem_filter.mp hp).2; omega
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < R)) (by exact_mod_cast hpR)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => primeWeight_nonneg p)
  have hT := (le_div_iff₀ hlogR).mpr htail
  have hsum : S.card+T.card=P.card := card_filter_add_card_filter_not (fun p => p ≤ R)
  have hsumR : (S.card : ℝ)+T.card=P.card := by exact_mod_cast hsum
  have hSR : (S.card : ℝ) ≤ (R : ℝ)+1 := by exact_mod_cast hcardS
  linarith only [hT, hsumR, hSR]

/-- A quantitative entropy bound, with an arbitrary finite cutoff R. -/
theorem log_family_card_le_pool_weight (F P : Finset ℕ) (hFne : F.Nonempty)
    (hF : ∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P)
    (R : ℕ) (hR : 2 ≤ R) :
    Real.log (F.card : ℝ) ≤ ((R : ℝ)+1)*Real.log 2 +
      (Real.log 2/Real.log (R : ℝ))*poolWeight P := by
  have hcard : (F.card : ℝ) ≤ (2 : ℝ)^P.card := by
    exact_mod_cast squarefree_family_card_le_pool_powerset F P hF
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hFne
  have hlog := Real.log_le_log hFpos hcard
  rw [Real.log_pow] at hlog
  have hb := mul_le_mul_of_nonneg_right (pool_card_le_weight P R hR)
    (show 0 ≤ Real.log 2 from Real.log_nonneg (by norm_num))
  apply hlog.trans
  convert hb using 1
  ring

/-- Uniform over all pools and squarefree families: a pool with logarithmic
weight at most C log n cannot contain a positive-power-size family. -/
theorem eventually_compact_pool_family_subpower (C ε : ℝ) (_hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ F P : Finset ℕ,
      (∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P) →
      poolWeight P ≤ C*Real.log (n : ℝ) →
      (F.card : ℝ) ≤ (n : ℝ)^ε := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max 2 (Real.exp (2*C*Real.log 2/ε)))
  have hR2 : 2 ≤ R := by
    have hh : (2 : ℝ) < R := (le_max_left _ _).trans_lt hR
    exact_mod_cast hh.le
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hcoef' : 2*C*Real.log 2/ε < Real.log (R : ℝ) :=
    (Real.lt_log_iff_exp_lt hR0).mpr ((le_max_right _ _).trans_lt hR)
  have hcoef : (Real.log 2/Real.log (R : ℝ))*C ≤ ε/2 := by
    have hh := (div_lt_iff₀ hε).mp hcoef'
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (mul_le_mul_iff_left₀ hlogR).mp
    field_simp
    nlinarith only [hh]
  have hlim : Tendsto (fun n : ℕ => (ε/2)*Real.log (n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  filter_upwards [hlim.eventually (eventually_ge_atTop (((R : ℝ)+1)*Real.log 2)),
    eventually_ge_atTop 1] with n hnA hn
  intro F P hF hW
  by_cases hFne : F.Nonempty
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hσ : 0 ≤ Real.log 2/Real.log (R : ℝ) :=
      div_nonneg (Real.log_nonneg (by norm_num)) hlogR.le
    have hlog : Real.log (F.card : ℝ) ≤ ε*Real.log (n : ℝ) := by
      calc
        _ ≤ ((R : ℝ)+1)*Real.log 2 + (Real.log 2/Real.log (R : ℝ))*poolWeight P :=
          log_family_card_le_pool_weight F P hFne hF R hR2
        _ ≤ (ε/2)*Real.log (n : ℝ) + (Real.log 2/Real.log (R : ℝ))*(C*Real.log (n : ℝ)) :=
          add_le_add hnA (mul_le_mul_of_nonneg_left hW hσ)
        _ = (ε/2)*Real.log (n : ℝ) + ((Real.log 2/Real.log (R : ℝ))*C)*Real.log (n : ℝ) := by ring
        _ ≤ (ε/2)*Real.log (n : ℝ) + (ε/2)*Real.log (n : ℝ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hlogn)
        _ = _ := by ring
    have hFpos : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hFne
    apply (Real.log_le_log_iff hFpos (Real.rpow_pos_of_pos hnR ε)).mp
    simpa only [Real.log_rpow hnR] using hlog
  · simp only [not_nonempty_iff_eq_empty.mp hFne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Thus polynomial-size squarefree families require arbitrarily large
pool weight relative to log n. This is not an upper bound for g(n). -/
theorem eventually_large_family_requires_large_pool (C α : ℝ) (hC : 0 < C) (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, ∀ F P : Finset ℕ,
      (∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P) →
      (n : ℝ)^α < (F.card : ℝ) → C*Real.log (n : ℝ) < poolWeight P := by
  filter_upwards [eventually_compact_pool_family_subpower C α hC hα] with n hn
  intro F P hF hcard
  by_contra h
  exact hcard.not_ge (hn F P hF (le_of_not_gt h))


/-- For a polynomial-size family, the Cauchy--Schwarz lower bound above
has a negative left coefficient at every fixed positive overlap exponent.
This only limits that particular lower estimate, not the actual overlap. -/
theorem eventually_large_family_cauchy_coefficient_negative (α η : ℝ)
    (hα : 0 < α) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ F P : Finset ℕ,
      (∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P) →
      (n : ℝ)^α < (F.card : ℝ) →
      Real.log (n : ℝ)-η*poolWeight P < 0 := by
  filter_upwards [eventually_large_family_requires_large_pool (1/η) α (by positivity) hα]
    with n hn
  intro F P hF hg
  have h := mul_lt_mul_of_pos_left (hn F P hF hg) hη
  have he : η*((1/η)*Real.log (n : ℝ)) = Real.log (n : ℝ) := by field_simp
  rw [he] at h
  linarith only [h]

end Erdos821.LogarithmicOverlap
