import Submission.WindowLargePrimeLower
import Submission.PositiveComparison

/-! Both orientations of the actual largest-prime-factor comparison have
positive lower proportions in every fixed relative terminal window. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

lemma filter_count_shifted_Ico_le_add_one (P : ℕ → Prop) [DecidablePred P]
    (L M : ℕ) (hLM : L ≤ M) :
    ((Ico L M).filter (fun n => P (n+1))).card ≤ ((Ico L M).filter P).card+1 := by
  have h := sum_Ico_sub (fun n => if P n then (1 : ℤ) else 0) hLM
  rw [sum_sub_distrib] at h
  simp only [sum_boole] at h
  change (((Ico L M).filter (fun n => P (n+1))).card : ℤ) -
    (((Ico L M).filter P).card : ℤ) = (if P M then 1 else 0) - (if P L then 1 else 0) at h
  split_ifs at h <;> omega

lemma large_factor_window_count_le_rises_add_both (L M : ℕ) (u : ℝ) :
    ((Ico L M).filter (fun n => (M : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ))).card ≤
      ((Ico L M).filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))).card +
        (bothLargePrimeSet M u).card := by
  classical
  have hsub : (Ico L M).filter (fun n => (M : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ)) ⊆
      ((Ico L M).filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))) ∪ bothLargePrimeSet M u := by
    intro n hn
    obtain ⟨hnM,hq⟩ := mem_filter.mp hn
    by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
    · exact mem_union_left _ (mem_filter.mpr ⟨hnM,h⟩)
    · have h' : (Nat.maxPrimeFac (n+1) : ℝ) ≤ Nat.maxPrimeFac n := by exact_mod_cast (not_lt.mp h)
      exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hnM).2,hq.trans_le h',hq⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

lemma large_factor_window_count_le_falls_add_both (L M : ℕ) (hLM : L ≤ M) (u : ℝ) :
    ((Ico L M).filter (fun n => (M : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ))).card ≤
      ((Ico L M).filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n)).card +
        (bothLargePrimeSet M u).card+1 := by
  classical
  have hshift := filter_count_shifted_Ico_le_add_one
    (fun n => (M : ℝ)^(1-u) < (Nat.maxPrimeFac n : ℝ)) L M hLM
  have hsub : (Ico L M).filter (fun n => (M : ℝ)^(1-u) < (Nat.maxPrimeFac n : ℝ)) ⊆
      ((Ico L M).filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n)) ∪ bothLargePrimeSet M u := by
    intro n hn
    obtain ⟨hnM,hp⟩ := mem_filter.mp hn
    by_cases h : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n
    · exact mem_union_left _ (mem_filter.mpr ⟨hnM,h⟩)
    · have h' : (Nat.maxPrimeFac n : ℝ) ≤ Nat.maxPrimeFac (n+1) := by exact_mod_cast (not_lt.mp h)
      exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hnM).2,hp,hp.trans_le h'⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  exact hshift.trans (Nat.add_le_add_right hc 1)

/-- The lower bound holds simultaneously for every terminal interval with
length at least `θ*M`. It is not deduced by subtracting lower prefix bounds. -/
theorem rising_falling_positive_window_proportions (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ M : ℕ in atTop, ∀ L ≤ M, (L : ℝ) ≤ (1-θ)*(M : ℝ) →
      δ ≤ (((Ico L M).filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))).card : ℝ)/M ∧
      δ ≤ (((Ico L M).filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n)).card : ℝ)/M := by
  classical
  have hK : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  let u : ℝ := θ/(8*(largePairConstant+1))
  have hden : 0 < 8*(largePairConstant+1) := by positivity
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu : u ≤ 1/8 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hKu : largePairConstant*u ≤ θ/8 := by
    dsimp only [u]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hKu2 : largePairConstant*u^2 ≤ θ*u/8 := by
    have h := mul_le_mul_of_nonneg_right hKu hu0.le
    nlinarith
  have heps : 0 < θ*u/8 := by positivity
  have hhigh := largePrime_power_window_eventually_ge (1-u) θ (by linarith) (by linarith)
    hθ.le (θ*u/8) heps
  have hboth := bothLargePrimeSet_eventually_ratio_le u hu0.le hu (θ*u/8) heps
  have hone := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const heps
  refine ⟨θ*u/4,by positivity,?_⟩
  filter_upwards [hhigh,hboth,hone] with M hh hb ho
  intro L hLM hL
  have hh := hh L hLM hL
  have hcr := div_le_div_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (large_factor_window_count_le_rises_add_both L M u))
    (Nat.cast_nonneg (α := ℝ) M)
  have hcf := div_le_div_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (large_factor_window_count_le_falls_add_both L M hLM u))
    (Nat.cast_nonneg (α := ℝ) M)
  simp only [Nat.cast_add,Nat.cast_one,add_div] at hcr hcf
  constructor <;> nlinarith

/-- In particular both directions occur with positive lower proportions on
`[a*N,b*N)` for every fixed pair of natural numbers `a<b`. -/
theorem rising_falling_positive_integer_windows (a b : ℕ) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ ≤ (((Ico (a*N) (b*N)).filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))).card : ℝ)/N ∧
      δ ≤ (((Ico (a*N) (b*N)).filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n)).card : ℝ)/N := by
  have hb : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  let θ : ℝ := ((b : ℝ)-a)/b
  have hθ : 0 < θ := div_pos (sub_pos.mpr habR) hbR
  have hθ1 : θ ≤ 1 := by dsimp [θ]; apply (div_le_iff₀ hbR).mpr; have := Nat.cast_nonneg (α := ℝ) a; linarith
  obtain ⟨δ,hδ,hw⟩ := rising_falling_positive_window_proportions θ hθ hθ1
  have hmul : Tendsto (fun N : ℕ => b*N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [eventually_ge_atTop R] with N hRN
    nlinarith
  refine ⟨δ*(b : ℝ),by positivity,?_⟩
  filter_upwards [hmul.eventually hw,eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hL : (a*N : ℕ) ≤ b*N := Nat.mul_le_mul_right N hab.le
  have hθeq : ((a*N : ℕ) : ℝ) = (1-θ)*((b*N : ℕ) : ℝ) := by
    simp only [Nat.cast_mul]
    dsimp [θ]
    field_simp
    ring
  obtain ⟨hr,hf⟩ := hN (a*N) hL hθeq.le
  have hbn : (0 : ℝ) < (b*N : ℕ) := by positivity
  have hr' := (le_div_iff₀ hbn).mp hr
  have hf' := (le_div_iff₀ hbn).mp hf
  simp only [Nat.cast_mul] at hr' hf'
  constructor <;> apply (le_div_iff₀ hNr).mpr <;> nlinarith

#print axioms rising_falling_positive_window_proportions
#print axioms rising_falling_positive_integer_windows
end Erdos371
