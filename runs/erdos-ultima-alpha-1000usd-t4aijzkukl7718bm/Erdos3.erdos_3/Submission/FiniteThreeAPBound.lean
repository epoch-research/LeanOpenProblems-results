import Submission.LocalDensityStep

/-! Iteration of the stable local three-term increment, with an explicit finite bound. -/
namespace Erdos3FiniteThreeAPBound
open Finset Erdos3LocalDensityStep Erdos3LocalThreeAPIncrement Erdos3RelativeStableBohr
  Erdos3StableSupportedIncrement Erdos3BohrIncrementParameters Erdos3FiniteBohr
  Erdos3BohrCovering Erdos3CorrelationSifting Erdos3BohrLocalAverages
  Erdos3LocalCorrelationCentering Erdos3DoubledWeights Erdos3AsymmetricSifting
  Erdos3CrootSisaskL2
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4500000

def generatorDenominator (m : ℕ) : ℕ := 2048*(rankBudget m+1)*2^m
def iterationScale (b z m : ℕ) : ℕ := 2*stepShrinkDenominator b z m*generatorDenominator m
def iterationVolume (b z m t : ℕ) : ℕ := (4*(iterationScale b z m)^t+1)^(2*b)

lemma generatorDenominator_pos (m : ℕ) : 0 < generatorDenominator m := by
  unfold generatorDenominator
  positivity
lemma generatorRadius_eq (m : ℕ) : generatorRadius m (rankBudget m) = 1/(generatorDenominator m : ℝ) := by
  unfold generatorRadius generatorDenominator
  push_cast
  rfl
lemma iterationScale_pos (b m : ℕ) {z : ℕ} (hz : 0 < z) : 0 < iterationScale b z m := by
  unfold iterationScale
  exact Nat.mul_pos (Nat.mul_pos (by decide) (stepShrinkDenominator_pos b m hz)) (generatorDenominator_pos m)
lemma iterationVolume_pos (b z m t : ℕ) : 0 < iterationVolume b z m t := by
  unfold iterationVolume
  positivity

lemma windowDenominator_mono {d b z : ℕ} (h : d ≤ b) : windowDenominator d z ≤ windowDenominator b z := by
  unfold windowDenominator
  gcongr
lemma localShrinkDenominator_mono {d b z m : ℕ} (h : d ≤ b) :
    localShrinkDenominator d z m ≤ localShrinkDenominator b z m := by
  unfold localShrinkDenominator
  gcongr <;> exact windowDenominator_mono h
lemma stepShrinkDenominator_mono {d b z m : ℕ} (h : d ≤ b) :
    stepShrinkDenominator d z m ≤ stepShrinkDenominator b z m := by
  unfold stepShrinkDenominator
  gcongr
  · exact windowDenominator_mono h
  · exact localShrinkDenominator_mono h
lemma coverFactor_mono {d b z : ℕ} (h : d ≤ b) : coverFactor d z ≤ coverFactor b z := by
  unfold coverFactor
  calc
    _ ≤ (16*windowDenominator b z+1)^(2*d) := by gcongr; exact windowDenominator_mono h
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

lemma step_radius_lower {d b z m : ℕ} (hz : 0 < z) (hdb : d ≤ b)
    {r s : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : min (r/(stepShrinkDenominator d z m : ℝ)) (generatorRadius m (rankBudget m))/2 ≤ s) :
    r/(iterationScale b z m : ℝ) ≤ s := by
  have hS : (0 : ℝ) < stepShrinkDenominator b z m := by exact_mod_cast stepShrinkDenominator_pos b m hz
  have hS1 : (1 : ℝ) ≤ stepShrinkDenominator b z m := by exact_mod_cast stepShrinkDenominator_pos b m hz
  have hSd : (0 : ℝ) < stepShrinkDenominator d z m := by exact_mod_cast stepShrinkDenominator_pos d m hz
  have hQ : (0 : ℝ) < generatorDenominator m := by exact_mod_cast generatorDenominator_pos m
  have hQ1 : (1 : ℝ) ≤ generatorDenominator m := by exact_mod_cast generatorDenominator_pos m
  have hSdb : (stepShrinkDenominator d z m : ℝ) ≤ stepShrinkDenominator b z m := by
    exact_mod_cast stepShrinkDenominator_mono hdb
  have h₁ : r/((stepShrinkDenominator b z m : ℝ)*generatorDenominator m) ≤
      r/(stepShrinkDenominator d z m : ℝ) := by
    apply div_le_div_of_nonneg_left hr hSd
    exact hSdb.trans (by nlinarith)
  have h₂ : r/((stepShrinkDenominator b z m : ℝ)*generatorDenominator m) ≤ generatorRadius m (rankBudget m) := by
    rw [generatorRadius_eq, ← div_div]
    apply div_le_div_of_nonneg_right _ hQ.le
    exact (div_le_one hS).mpr (hr1.trans hS1)
  have hmin := le_min h₁ h₂
  calc
    _ = (r/((stepShrinkDenominator b z m : ℝ)*generatorDenominator m))/2 := by
      unfold iterationScale
      push_cast
      ring
    _ ≤ _ := (div_le_div_of_nonneg_right hmin (by norm_num)).trans hs

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma iteration_card_lower (D : Finset (AddChar G ℂ)) {b z m t : ℕ}
    (hz : 0 < z) (hD : D.card ≤ b) {r : ℝ}
    (hr : 1/(iterationScale b z m : ℝ)^t ≤ r) :
    Fintype.card G ≤ iterationVolume b z m t*(bohr D r).card := by
  let L := iterationScale b z m
  have hL : 0 < L := iterationScale_pos b m hz
  have hq : 0 < 2*L^t := Nat.mul_pos (by decide) (pow_pos hL _)
  have hh := card_bohr_lower D hq
  have he : 2/((2*L^t : ℕ) : ℝ) = 1/(L : ℝ)^t := by push_cast; ring
  rw [he] at hh
  have hpow : (2*(2*L^t)+1)^(2*D.card) ≤ (4*L^t+1)^(2*b) := by
    rw [show 2*(2*L^t)+1 = 4*L^t+1 by omega]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact hh.trans (Nat.mul_le_mul hpow (card_le_card (bohr_mono D hr)))

lemma large_base_of_large_group (D : Finset (AddChar G ℂ)) {b z m t : ℕ}
    (hz : 0 < z) (hD : D.card ≤ b) {r a : ℝ}
    (hr : 1/(iterationScale b z m : ℝ)^t ≤ r)
    (hN : 32*(coverFactor b z : ℝ)*iterationVolume b z m t ≤ a^2*(Fintype.card G : ℝ)) :
    32*(coverFactor D.card z : ℝ) ≤ a^2*((bohr D r).card : ℝ) := by
  have hc : (Fintype.card G : ℝ) ≤ (iterationVolume b z m t : ℝ)*((bohr D r).card : ℝ) := by
    exact_mod_cast iteration_card_lower D hz hD hr
  have hM : (0 : ℝ) < iterationVolume b z m t := by exact_mod_cast iterationVolume_pos b z m t
  have hb : 32*(coverFactor b z : ℝ) ≤ a^2*((bohr D r).card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hM).mp
    nlinarith [hN.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg a))]
  have hcf : (coverFactor D.card z : ℝ) ≤ coverFactor b z := by exact_mod_cast coverFactor_mono hD
  linarith

lemma bohr_empty (r : ℝ) : bohr (∅ : Finset (AddChar G ℂ)) r = univ := by
  ext x
  simp [mem_bohr]

lemma relativeStable_empty (z : ℕ) (r : ℝ) : RelativeStable (∅ : Finset (AddChar G ℂ)) z r := by
  unfold RelativeStable
  rw [bohr_empty, bohr_empty]
  have h : (0 : ℝ) ≤ (1/(z : ℝ))*(Fintype.card G : ℝ) := by positivity
  simp only [card_univ]
  nlinarith

lemma relativeDensity_univ (A : Finset G) : relativeDensity A univ = density A := by
  simp [relativeDensity,density]

/-- An explicit finite-group bound obtained by iterating the local step.
No reciprocal-summability conclusion or higher-length extension is asserted here. -/
theorem finite_threeAP_bound (h2 : Function.Bijective (fun x : G ↦ x+x))
    (A : Finset G) (hA : A.Nonempty) (hfree : ThreeAPFree (A : Set G))
    {a : ℝ} (ha : 0 < a) (haA : a ≤ density A)
    {z p m t : ℕ} (hz : 0 < z) (hp : 67 ≤ p) (hpeven : Even p) (hm : 0 < m)
    (hmeanError : 1/(z : ℝ) ≤ a/2048)
    (hmassParam : (2/3 : ℝ)^p ≤ a/2)
    (hcenterError : (1/(z : ℝ))*(4/a+1) ≤ 1/256)
    (hlocalError : (1/(z : ℝ))*(2/a)^(8*p) ≤ (17/16 : ℝ)^(8*p)-(67/64 : ℝ)^(8*p))
    (hbudget : 4 ≤ (2 : ℝ)^(2*m)*(a/2)^(2*(8*p)))
    (ht : 1 < (1025/1024 : ℝ)^t*a) :
    a^2*(Fintype.card G : ℝ) <
      32*(coverFactor (t*rankBudget m) z : ℝ)*iterationVolume (t*rankBudget m) z m t := by
  by_contra! hN
  let b := t*rankBudget m
  let L := iterationScale b z m
  have hL : 0 < L := iterationScale_pos b m hz
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hiter : ∀ i ≤ t, ∃ D : Finset (AddChar G ℂ), D.card ≤ i*rankBudget m ∧
      ∃ B : Finset G, B.Nonempty ∧ ThreeAPFree (B : Set G) ∧
        ∃ r : ℝ, 1/(L : ℝ)^i ≤ r ∧ 0 < r ∧ r ≤ 1 ∧ RelativeStable D z r ∧
          B ⊆ bohr D r ∧ (1025/1024 : ℝ)^i*a ≤ relativeDensity B (bohr D r) := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨∅,by simp,A,hA,hfree,1,by simp,by norm_num,le_rfl,relativeStable_empty z 1,?_,?_⟩
      · rw [bohr_empty]
        exact subset_univ _
      · simpa only [pow_zero, one_mul, bohr_empty, relativeDensity_univ] using haA
    | succ i ih =>
      intro hi
      obtain ⟨D,hD,B,hB,hfreeB,r,hrLo,hr,hr1,hstable,hBD,hden⟩ := ih (by omega)
      have hib : D.card ≤ b := hD.trans (Nat.mul_le_mul_right _ (by omega : i ≤ t))
      have hrGlobal : 1/(L : ℝ)^t ≤ r :=
        (one_div_le_one_div_of_le (pow_pos hLpos i) (pow_le_pow_right₀ hL1 (by omega : i ≤ t))).trans hrLo
      have hlarge := large_base_of_large_group D hz hib hrGlobal hN
      have haB : a ≤ relativeDensity B (bohr D r) := by
        have hpow : (1 : ℝ) ≤ (1025/1024 : ℝ)^i := one_le_pow₀ (by norm_num)
        have hh : a ≤ (1025/1024 : ℝ)^i*a := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow ha.le
        exact hh.trans hden
      obtain ⟨F,hF,s,hsLo,hs,hsr,hsStable,x,hx⟩ := local_density_step h2 D hr ha hz hp hpeven hm
        hstable B hB hBD hfreeB haB hmeanError hmassParam hcenterError hlocalError hbudget hlarge
      let B' := window B (bohr F s) x
      have hden' : (1025/1024 : ℝ)^(i+1)*a ≤ relativeDensity B' (bohr F s) := by
        rw [relativeDensity_window]
        calc
          _ = (1025/1024 : ℝ)*((1025/1024 : ℝ)^i*a) := by rw [pow_succ]; ring
          _ ≤ (1025/1024 : ℝ)*relativeDensity B (bohr D r) := mul_le_mul_of_nonneg_left hden (by norm_num)
          _ ≤ _ := hx
      have hB' : B'.Nonempty := nonempty_of_relative_pos B' (bohr F s)
        (lt_of_lt_of_le (by positivity) hden')
      have hrStep : r/(L : ℝ) ≤ s := step_radius_lower hz hib hr.le hr1 hsLo
      have hrNext : 1/(L : ℝ)^(i+1) ≤ s := by
        rw [pow_succ, ← div_div]
        exact (div_le_div_of_nonneg_right hrLo hLpos.le).trans hrStep
      refine ⟨F,?_,B',hB',window_threeAPFree B (bohr F s) hfreeB x,
        s,hrNext,hs,hsr.trans hr1,hsStable,window_subset ..,hden'⟩
      simpa only [Nat.add_mul, Nat.one_mul] using hF.trans (Nat.add_le_add_right hD (rankBudget m))
  obtain ⟨D,hD,B,hB,hfreeB,r,hrLo,hr,hr1,hstable,hBD,hden⟩ := hiter t le_rfl
  have hupper := relativeDensity_le_one B (bohr D r) (hB.mono hBD)
  linarith

#print axioms finite_threeAP_bound
end Erdos3FiniteThreeAPBound
