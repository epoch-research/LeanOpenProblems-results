import Submission.IntegerThreeAPBound

/-! Summability from dyadic density-level thresholds. -/
namespace Erdos3GeometricThresholdSummability
open Finset Erdos3IntegerThreeAPBound Erdos3PolynomialThreeAPThreshold Erdos3DyadicThreeAPBound
open scoped BigOperators Classical
set_option maxHeartbeats 2500000

lemma exists_dyadic_band {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ l : ℕ, (1/2 : ℝ)^l < x ∧ x ≤ 2*(1/2 : ℝ)^l := by
  have hex : ∃ l : ℕ, (1/2 : ℝ)^l < x := exists_pow_lt_of_lt_one hx (by norm_num)
  have hmin := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by intro he; simp only [he,pow_zero] at hmin; linarith
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hp : x ≤ (1/2 : ℝ)^k := le_of_not_gt (Nat.find_min hex (by omega : k < Nat.find hex))
  refine ⟨Nat.find hex,hmin,?_⟩
  rw [hk,pow_succ]
  linarith

/-- If the number of exceptional scales at density 2^-l has summable geometric
weight, then the scale densities themselves are summable. -/
theorem summable_of_dyadic_thresholds (f : ℕ → ℝ) (P : ℕ → ℕ)
    (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (hP : Summable (fun l : ℕ ↦ (P l : ℝ)*(1/2 : ℝ)^l))
    (hbound : ∀ l j, P l ≤ j → f j ≤ (1/2 : ℝ)^l) : Summable f := by
  let g : ℕ × ℕ → ℝ := fun p ↦ if p.2 < P p.1 then (1/2 : ℝ)^p.1 else 0
  have hg : 0 ≤ g := by intro p; dsimp [g]; split_ifs <;> positivity
  have hsupport (l j : ℕ) (hj : j ∉ range (P l)) : g (l,j) = 0 := by
    simp only [mem_range] at hj
    simp only [g,if_neg hj]
  have hrows (l : ℕ) : Summable (fun j : ℕ ↦ g (l,j)) := summable_of_ne_finset_zero (hsupport l)
  have hrow_sum (l : ℕ) : (∑' j : ℕ, g (l,j)) = (P l : ℝ)*(1/2 : ℝ)^l := by
    rw [tsum_eq_sum (hsupport l)]
    have he : (∑ j ∈ range (P l), g (l,j)) = ∑ _j ∈ range (P l), (1/2 : ℝ)^l := by
      apply sum_congr rfl
      intro j hj
      simp only [g,if_pos (mem_range.mp hj)]
    rw [he]
    simp
  have hprod : Summable g := (summable_prod_of_nonneg hg).mpr ⟨hrows, by simpa only [hrow_sum] using hP⟩
  have hswap : Summable (fun p : ℕ × ℕ ↦ g (p.2,p.1)) :=
    hprod.comp_injective (i := fun p : ℕ × ℕ ↦ (p.2,p.1)) (Equiv.prodComm ℕ ℕ).injective
  have hcols : ∀ j, Summable (fun l ↦ g (l,j)) :=
    ((summable_prod_of_nonneg (fun p ↦ hg (p.2,p.1))).mp hswap).1
  apply ((hswap.prod).mul_left 2).of_nonneg_of_le (fun j ↦ (hf j).1)
  intro j
  by_cases hj : f j = 0
  · rw [hj]
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun l ↦ hg (l,j)))
  · obtain ⟨l,hl,hfl⟩ := exists_dyadic_band (lt_of_le_of_ne (hf j).1 (Ne.symm hj)) (hf j).2
    have hjP : j < P l := by
      by_contra hn
      have hh := hbound l j (by omega)
      linarith
    have hh : g (l,j) ≤ ∑' k : ℕ, g (k,j) := (hcols j).le_tsum l (fun k _ ↦ hg (k,j))
    simp only [g,if_pos hjP] at hh
    linarith

lemma summable_shifted_threshold_weight :
    Summable (fun l : ℕ ↦ (thresholdExponent (l+2) : ℝ)*(1/2 : ℝ)^l) := by
  have hh := ((summable_nat_add_iff 2).mpr summable_threshold_weight).mul_left (4 : ℝ)
  convert hh using 1
  funext l
  rw [pow_add]
  norm_num
  ring

noncomputable def initialCount (A : Set ℕ) (N : ℕ) : Finset ℕ := (range N).filter (fun n ↦ n ∈ A)
noncomputable def scaleDensity (A : Set ℕ) (j : ℕ) : ℝ := (initialCount A (2^j)).card/(2 : ℝ)^j

lemma initialCount_subset (A : Set ℕ) (N : ℕ) : (initialCount A N : Set ℕ) ⊆ A := by
  intro n hn
  exact (mem_filter.mp (show n ∈ (range N).filter (fun n ↦ n ∈ A) from hn)).2

lemma scaleDensity_bounds (A : Set ℕ) (j : ℕ) : 0 ≤ scaleDensity A j ∧ scaleDensity A j ≤ 1 := by
  constructor
  · unfold scaleDensity; positivity
  · unfold scaleDensity
    apply (div_le_one (by positivity : (0 : ℝ) < 2^j)).mpr
    have hh : (initialCount A (2^j)).card ≤ 2^j := (card_le_card (filter_subset _ _)).trans_eq (card_range _)
    exact_mod_cast hh

/-- Integer three-term bounds make the dyadic counting densities summable. -/
theorem threeAPFree_scaleDensity_summable (A : Set ℕ) (hfree : ThreeAPFree A) :
    Summable (scaleDensity A) := by
  apply summable_of_dyadic_thresholds (scaleDensity A) (fun l ↦ thresholdExponent (l+2))
    (scaleDensity_bounds A) summable_shifted_threshold_weight
  intro l j hj
  have hS : initialCount A (2^j) ⊆ range (2^j) := filter_subset _ _
  have hfreeS : ThreeAPFree (initialCount A (2^j) : Set ℕ) := by
    intro a ha b hb c hc he
    exact hfree (initialCount_subset A _ ha) (initialCount_subset A _ hb) (initialCount_subset A _ hc) he
  have hh := integer_threeAP_density_lt (2^j) l (by positivity)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hj) (initialCount A (2^j)) hS hfreeS
  have he : dyadicDensity l = (1/2 : ℝ)^l := by unfold dyadicDensity; rw [div_pow,one_pow]
  simpa only [scaleDensity, Nat.cast_pow, Nat.cast_ofNat, he] using hh.le

#print axioms summable_of_dyadic_thresholds
#print axioms threeAPFree_scaleDensity_summable
end Erdos3GeometricThresholdSummability
