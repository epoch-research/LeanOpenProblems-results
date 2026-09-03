import Submission.BuchstabSectorSums
import Submission.BuchstabLowerDeficitSum

/-! Exact logarithmic bins for the Buchstab grid and their finite-sector mass.
The terminal small-prime tail is kept separate. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
open scoped Topology

noncomputable def gridPrimeCut (L : ℝ) (j : ℕ) : ℕ := ⌊exp (L/((j : ℝ)/50+1))⌋₊
noncomputable def gridPrimeBin (L : ℝ) (j : ℕ) : Finset ℕ :=
  (Ioc (gridPrimeCut L (j+1)) (gridPrimeCut L j)).filter Nat.Prime

lemma grid_den_pos (j : ℕ) : (0 : ℝ) < (j : ℝ)/50+1 := by positivity

lemma gridPrimeCut_antitone (L : ℝ) (hL : 0 ≤ L) : Antitone (gridPrimeCut L) := by
  intro i j hij
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  apply div_le_div_of_nonneg_left hL (grid_den_pos i)
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

lemma gridPrimeCut_terminal (L : ℝ) : gridPrimeCut L 600 = tailPrimeCut L := by
  norm_num [gridPrimeCut,tailPrimeCut]

lemma gridPrimeCut_scaled (s L : ℝ) (j : ℕ) :
    gridPrimeCut (s*L) j = expFloor (s/((j : ℝ)/50+1)) L := by
  unfold gridPrimeCut expFloor
  congr 2
  ring

lemma gridPrimeCut_root (a p : ℕ) (ha : 50 ≤ a) (hp : 0 < p) :
    gridPrimeCut (((a : ℝ)/50)*log (p : ℝ)) (a-50) = p := by
  have haR : (50 : ℝ) ≤ a := by exact_mod_cast ha
  have he : (((a-50 : ℕ) : ℝ)/50+1) = (a : ℝ)/50 := by
    rw [Nat.cast_sub ha]
    push_cast
    ring
  rw [gridPrimeCut,he,mul_div_cancel_left₀ _ (by linarith : (a : ℝ)/50 ≠ 0),
    exp_log (by exact_mod_cast hp),Nat.floor_natCast]

lemma gridPrimeBin_log_bounds (L : ℝ) (j p : ℕ) (hp : p ∈ gridPrimeBin L j) :
    p.Prime ∧ L/(((j+1 : ℕ) : ℝ)/50+1) < log (p : ℝ) ∧
      log (p : ℝ) ≤ L/((j : ℝ)/50+1) := by
  obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo,hphi⟩ := mem_Ioc.mp hpI
  have hlo : exp (L/(((j+1 : ℕ) : ℝ)/50+1)) < (p : ℝ) := Nat.lt_of_floor_lt hplo
  have hhi : (p : ℝ) ≤ exp (L/((j : ℝ)/50+1)) :=
    (show (p : ℝ) ≤ gridPrimeCut L j by exact_mod_cast hphi).trans (Nat.floor_le (exp_pos _).le)
  have h1 := log_lt_log (exp_pos _) hlo
  have h2 := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos) hhi
  rw [log_exp] at h1 h2
  exact ⟨hpp,h1,h2⟩

lemma gridPrimeBin_child_level (L : ℝ) (j p : ℕ) (hp : p ∈ gridPrimeBin L j) :
    exp (((j : ℝ)/50)*log (p : ℝ)) ≤ exp L/(p : ℝ) := by
  obtain ⟨hpp,_,hhi⟩ := gridPrimeBin_log_bounds L j p hp
  have hh := (le_div_iff₀ (grid_den_pos j)).mp hhi
  rw [← exp_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos),← exp_sub,log_exp]
  apply exp_le_exp.mpr
  nlinarith only [hh]

lemma gridPrimeBin_above_tail (L : ℝ) (hL : 0 ≤ L) (j p : ℕ) (hj : j < 600)
    (hp : p ∈ gridPrimeBin L j) : tailPrimeCut L < p := by
  obtain ⟨hpI,_⟩ := mem_filter.mp hp
  rw [← gridPrimeCut_terminal]
  exact (gridPrimeCut_antitone L hL (show j+1 ≤ 600 by omega)).trans_lt (mem_Ioc.mp hpI).1

lemma gridPrimeBins_sum (L : ℝ) (hL : 0 ≤ L) (a b : ℕ) (hab : a ≤ b) (f : ℕ → ℝ) :
    (∑ j ∈ Ico a b, ∑ p ∈ gridPrimeBin L j, f p) =
      ∑ p ∈ (Ioc (gridPrimeCut L b) (gridPrimeCut L a)).filter Nat.Prime, f p := by
  have ha := gridPrimeCut_antitone L hL
  unfold gridPrimeBin
  simp_rw [sum_prime_Ioc_eq_sub f _ _ (ha (Nat.le_succ _))]
  rw [sum_prime_Ioc_eq_sub f _ _ (ha hab)]
  have hh := sum_Ico_sub (fun j => ∑ p ∈ range (gridPrimeCut L j+1), if p.Prime then f p else 0) hab
  rw [← neg_sub,← hh,← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  ring

lemma prime_prefix_le_tail_add_bins (k a : ℕ) (ha : 50 ≤ a) (ha' : a ≤ 650)
    (f : ℕ → ℝ) (hf : ∀ p, p.Prime → 0 ≤ f p) :
    (∑ p ∈ (nthPrime k).primesBelow, f p) ≤
      (∑ p ∈ smallPrimePart k (((a : ℝ)/50)*log (nthPrime k : ℝ)), f p)+
      ∑ j ∈ Ico (a-50) 600, ∑ p ∈ gridPrimeBin (((a : ℝ)/50)*log (nthPrime k : ℝ)) j, f p := by
  let L := ((a : ℝ)/50)*log (nthPrime k : ℝ)
  have hL : 0 ≤ L := mul_nonneg (by positivity) (log_natCast_nonneg _)
  rw [gridPrimeBins_sum L hL (a-50) 600 (by omega),gridPrimeCut_terminal,
    gridPrimeCut_root a (nthPrime k) ha (nthPrime_prime k).pos]
  have hs := sum_filter_add_sum_filter_not (nthPrime k).primesBelow
    (fun p => p ≤ tailPrimeCut L) f
  change (∑ p ∈ (nthPrime k).primesBelow, f p) ≤
    (∑ p ∈ (nthPrime k).primesBelow.filter (fun p => p ≤ tailPrimeCut L), f p)+_
  rw [← hs]
  apply add_le_add le_rfl
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hcut⟩ := mem_filter.mp hp
    obtain ⟨hpk,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hpk.le⟩,hpp⟩
  · intro p hp _
    exact hf p (mem_filter.mp hp).2

lemma grid_sector_mass_value (s : ℝ) (hs : 0 < s) (j : ℕ) :
    1/(s/(((j+1 : ℕ) : ℝ)/50+1))-1/(s/((j : ℝ)/50+1)) = 1/(50*s) := by
  push_cast
  field_simp
  <;> ring

/-- A fixed finite grid of step majorants transfers to its rectangle integral,
with arbitrary positive slack. No infinite-tail estimate is hidden here. -/
theorem eventually_grid_sector_upper (s : ℝ) (hs : 0 < s) (a b : ℕ)
    (c : ℕ → ℝ) (f : ℝ → ℕ → ℝ)
    (hbound : ∀ᶠ L : ℝ in atTop, ∀ j ∈ Ico a b, ∀ p ∈ gridPrimeBin (s*L) j,
      f L p ≤ c j*((1/(p : ℝ))*(1/eulerMass p.primesBelow)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, initialEulerMass (expFloor 1 L)*
      (∑ j ∈ Ico a b, ∑ p ∈ gridPrimeBin (s*L) j, f L p) <
      (∑ j ∈ Ico a b, c j/50)/s+ε := by
  have hh := eventually_step_profile_upper (Ico a b) 1 (by norm_num)
    (fun j => s/(((j+1 : ℕ) : ℝ)/50+1)) (fun j => s/((j : ℝ)/50+1)) c
    (fun j _ => div_pos hs (grid_den_pos (j+1))) (by
      intro j hj
      apply div_le_div_of_nonneg_left hs.le (grid_den_pos j)
      push_cast
      linarith)
    f (by simpa only [gridPrimeBin,gridPrimeCut_scaled] using hbound) ε hε
  have he : (∑ j ∈ Ico a b, c j*(1/(s/(((j+1 : ℕ) : ℝ)/50+1))-
      1/(s/((j : ℝ)/50+1)))) = (∑ j ∈ Ico a b, c j/50)/s := by
    simp_rw [grid_sector_mass_value s hs]
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    ring
  rw [he] at hh
  simpa only [gridPrimeBin,gridPrimeCut_scaled] using hh

#print axioms prime_prefix_le_tail_add_bins
#print axioms eventually_grid_sector_upper
end Erdos970.RecursiveSieve.Buchstab
