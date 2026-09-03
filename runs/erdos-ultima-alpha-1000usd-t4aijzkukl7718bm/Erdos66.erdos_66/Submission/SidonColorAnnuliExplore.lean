import Submission.SidonColorBlockEnergyExplore

/-! Multiscale occupancy forces more distinct-difference colors than a
single-scale cardinality argument does. These are finite necessary bounds. -/
namespace Erdos66SidonColorAnnuli
open Erdos66SidonColorBlockEnergy
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def shellBins (J j : ℕ) : Finset ℕ := Finset.Ico (4^(j-J)) (4^(j+1-J))

lemma shellBins_card {J j : ℕ} (hj : J ≤ j) :
    (shellBins J j).card=3*4^(j-J) := by
  have he : j+1-J=j-J+1 := by omega
  simp only [shellBins,Nat.card_Ico,he,pow_succ]
  omega

lemma shellBins_disjoint (J : ℕ) : (Finset.Ico J (2*J) : Set ℕ).PairwiseDisjoint (shellBins J) := by
  intro i hi j hj hij
  change i∈Finset.Ico J (2*J) at hi
  change j∈Finset.Ico J (2*J) at hj
  obtain ⟨hi,hi'⟩ := Finset.mem_Ico.mp hi
  obtain ⟨hj,hj'⟩ := Finset.mem_Ico.mp hj
  apply Finset.disjoint_left.mpr
  intro b hbi hbj
  obtain ⟨hbi,hbi'⟩ := Finset.mem_Ico.mp hbi
  obtain ⟨hbj,hbj'⟩ := Finset.mem_Ico.mp hbj
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hpow := Nat.pow_le_pow_right (by decide : 0<4) (show i+1-J ≤ j-J by omega)
    omega
  · have hpow := Nat.pow_le_pow_right (by decide : 0<4) (show j+1-J ≤ i-J by omega)
    omega

lemma mem_shellBins_div {J j n : ℕ} (hj : J ≤ j) :
    n/4^J∈shellBins J j ↔ 4^j ≤ n ∧ n<4^(j+1) := by
  have h₁ : 4^(j-J)*4^J=4^j := by rw [← pow_add,Nat.sub_add_cancel hj]
  have h₂ : 4^(j+1-J)*4^J=4^(j+1) := by rw [← pow_add,Nat.sub_add_cancel (by omega : J ≤ j+1)]
  simp only [shellBins,Finset.mem_Ico,Nat.le_div_iff_mul_le (pow_pos (by decide : 0<4) J),
    Nat.div_lt_iff_lt_mul (pow_pos (by decide : 0<4) J),h₁,h₂]

noncomputable def shellMass (S : Finset ℕ) (j : ℕ) : ℕ :=
  (S.filter (fun n ↦ 4^j ≤ n ∧ n<4^(j+1))).card

lemma shellMass_eq_sum_bins (S : Finset ℕ) {J j : ℕ} (hj : J ≤ j) :
    shellMass S j=∑ b∈shellBins J j, binMass S (4^J) b := by
  have he := Finset.sum_card_fiberwise_eq_card_filter S (shellBins J j) (fun a ↦ a/4^J)
  simpa only [binMass,mem_shellBins_div hj,shellMass] using he.symm

lemma shell_cauchy (S : Finset ℕ) {J j : ℕ} (hj : J ≤ j) :
    (shellMass S j : ℝ)^2  ≤  3*(4 : ℝ)^(j-J)*
      ∑ b∈shellBins J j, (binMass S (4^J) b : ℝ)^2 := by
  have hs : (shellMass S j : ℝ)=∑ b∈shellBins J j, (binMass S (4^J) b : ℝ) := by
    exact_mod_cast shellMass_eq_sum_bins S hj
  rw [hs]
  have he := sq_sum_le_card_mul_sum_sq (s := shellBins J j) (f := fun b ↦ (binMass S (4^J) b : ℝ))
  simpa only [shellBins_card hj,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using he

/-- The same finite coloring must pay for short differences in every annulus
between 4^J and 4^(2J). A sqrt(n log n)-type shell profile makes the resulting
lower bound quadratic in J. -/
theorem annular_color_budget {I : Type*} [Fintype I]
    (S : Finset ℕ) (col : ℕ → I) (hcol : DistinctColorDifferences S col)
    (J : ℕ) (a : ℝ)
    (hprofile : ∀ j∈Finset.Ico J (2*J), a^2*(4 : ℝ)^j*J ≤ (shellMass S j : ℝ)^2) :
    a^2*(4 : ℝ)^J*(J : ℝ)^2  ≤ 
      3*(Fintype.card I : ℝ)*S.card+6*(Fintype.card I : ℝ)^2*(4 : ℝ)^J := by
  have hjbound (j : ℕ) (hj : j∈Finset.Ico J (2*J)) :
      a^2*(4 : ℝ)^J*J  ≤  3*∑ b∈shellBins J j, (binMass S (4^J) b : ℝ)^2 := by
    have hjJ := (Finset.mem_Ico.mp hj).1
    have hl := (hprofile j hj).trans (shell_cauchy S hjJ)
    have he : (4 : ℝ)^j=(4 : ℝ)^J*(4 : ℝ)^(j-J) := by
      rw [← pow_add,Nat.add_sub_of_le hjJ]
    rw [he] at hl
    have hp : (0 : ℝ)<(4 : ℝ)^(j-J) := by positivity
    apply le_of_mul_le_mul_right (a := (4 : ℝ)^(j-J)) ?_ hp
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.Ico J (2*J)) (fun j hj ↦ hjbound j hj)
  have hc : (Finset.Ico J (2*J)).card=J := by simp only [Nat.card_Ico]; omega
  simp only [Finset.sum_const,hc,nsmul_eq_mul] at hs
  rw [← Finset.mul_sum,← Finset.sum_biUnion (shellBins_disjoint J)] at hs
  have hu : 0<4^J := pow_pos (by decide) J
  have he := block_energy_bound S col hcol (4^J) hu ((Finset.Ico J (2*J)).biUnion (shellBins J))
  push_cast at he
  nlinarith

/-- After bounding the total number of points, the exponential scale
cancels. This is the useful constraint on the number of colors. -/
theorem color_quadratic_bound {I : Type*} [Fintype I]
    (S : Finset ℕ) (col : ℕ → I) (hcol : DistinctColorDifferences S col)
    (J : ℕ) (a b : ℝ)
    (hprofile : ∀ j∈Finset.Ico J (2*J), a^2*(4 : ℝ)^j*J ≤ (shellMass S j : ℝ)^2)
    (hsize : (S.card : ℝ) ≤ b*(4 : ℝ)^J*J) :
    a^2*(J : ℝ)^2  ≤  3*b*(Fintype.card I : ℝ)*J+6*(Fintype.card I : ℝ)^2 := by
  have he := annular_color_budget S col hcol J a hprofile
  have hm := mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ 3*(Fintype.card I : ℝ))
  have hp : (0 : ℝ)<(4 : ℝ)^J := by positivity
  apply le_of_mul_le_mul_right (a := (4 : ℝ)^J) ?_ hp
  nlinarith

/-- An explicit positive lower coefficient for the number of colors. -/
lemma linear_bound_of_quadratic (a b m t : ℝ) (ha : 0<a) (hb : 0 ≤ b) (hm : 0 ≤ m) (ht : 0<t)
    (he : a^2*t^2 ≤ 3*b*m*t+6*m^2) :
    min 1 (a^2/(3*b+6))*t ≤ m := by
  by_cases hmt : t ≤ m
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le).trans (by simpa using hmt)
  · have hmt : m<t := lt_of_not_ge hmt
    have hsq : m^2 ≤ m*t := by nlinarith
    have hden : 0<3*b+6 := by positivity
    have hd : a^2*t ≤ (3*b+6)*m := by nlinarith
    have hr : a^2/(3*b+6)*t ≤ m := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hden).mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le).trans hr

end Erdos66SidonColorAnnuli
