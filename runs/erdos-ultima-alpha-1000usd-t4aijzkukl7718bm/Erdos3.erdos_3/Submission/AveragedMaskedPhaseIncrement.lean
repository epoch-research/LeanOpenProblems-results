import Submission.MaskedPhaseIncrement

/-! Averaging over translates eliminates the complement-cell alternative:
centered averaged correlations yield a positive increment inside the mask. -/
namespace Erdos3AveragedMaskedPhaseIncrement
open Finset Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {I : Type*} [Fintype I] [Nonempty I]

lemma positive_cell_of_L1_plus_mean (m u : I → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hms : ∑ i, m i ≤ 1) (hu : ∀ i, |u i| ≤ m i)
    {s : ℝ} (hs : 0 < s) (hL : s ≤ (∑ i, |u i|)+(∑ i, u i)) :
    ∃ i : I, s/(8*(Fintype.card I : ℝ)) ≤ m i ∧ (s/8)*m i ≤ u i := by
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hc : 0 < s/(8*(Fintype.card I : ℝ)) := by positivity
  by_contra! hn
  have hbound (i : I) : u i ≤ (s/8)*m i+s/(8*(Fintype.card I : ℝ)) := by
    by_cases hi : s/(8*(Fintype.card I : ℝ)) ≤ m i
    · have hh := hn i hi
      linarith
    · have hh : u i ≤ m i := (le_abs_self _).trans (hu i)
      have hh' : 0 ≤ (s/8)*m i := mul_nonneg (by positivity) (hm i)
      linarith
  have habs (i : I) : |u i|+u i ≤ 2*((s/8)*m i+s/(8*(Fintype.card I : ℝ))) := by
    have hh : 0 ≤ (s/8)*m i := mul_nonneg (by positivity) (hm i)
    rcases le_total 0 (u i) with hi | hi
    · rw [abs_of_nonneg hi]; linarith [hbound i]
    · rw [abs_of_nonpos hi]; linarith
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) ↦ habs i)
  rw [sum_add_distrib,← mul_sum,sum_add_distrib,← mul_sum] at hsum
  have hc' : (∑ _i : I, s/(8*(Fintype.card I : ℝ))) = s/8 := by
    simp only [sum_const,card_univ,nsmul_eq_mul]
    field_simp
  rw [hc'] at hsum
  have hh := mul_le_mul_of_nonneg_left hms (by positivity : 0 ≤ s/8)
  nlinarith

variable {V : Type*} [Fintype V] [Nonempty V]

lemma inside_mass_sum_le_one (n : ℕ) (B : Finset V) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1) :
    ∑ i : PhaseGrid n, cellMass (maskedLabel n B q hq) (some i) ≤ 1 := by
  have hh := sum_cellMass (maskedLabel n B q hq)
  rw [Fintype.sum_option] at hh
  have hn := cellMass_nonneg (maskedLabel n B q hq) none
  linarith

lemma inside_charge_sum (n : ℕ) (B : Finset V) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1) (f : V → ℝ) :
    (∑ i : PhaseGrid n, cellCharge (maskedLabel n B q hq) f (some i)) =
      𝔼 x, if x ∈ B then f x else 0 := by
  unfold cellCharge
  rw [← expect_sum_comm]
  apply expect_congr rfl
  intro x _
  by_cases hx : x ∈ B <;> simp [maskedLabel,hx]

/-- The exterior cell contributes no correlation. Only signed charges of the
interior phase-grid cells are needed to bound the masked test correlation. -/
lemma masked_correlation_L1_bound (B : Finset V) (f : V → ℝ) (q : V → ℂ)
    (hf : ∀ x, |f x| ≤ 1) (hq : ∀ x, ‖q x‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖𝔼 x, if x ∈ B then (f x : ℂ)*conj (q x) else 0‖ ≤ 2/(n : ℝ)+
      ∑ i : PhaseGrid n, |cellCharge (maskedLabel n B q hq) f (some i)| := by
  let c := maskedLabel n B q hq
  let v := maskedTest B q
  obtain ⟨w₀,hw₀,happrox₀⟩ := exists_cell_representatives c v
    (maskedTest_bound B q hq) (by positivity : 0 ≤ 2/(n : ℝ))
    (fun _ _ he ↦ maskedLabel_oscillation hn B q hq he)
  let w : Option (PhaseGrid n) → ℂ := fun i ↦ match i with
    | none => 0
    | some j => w₀ (some j)
  have hw (i : PhaseGrid n) : ‖w (some i)‖ ≤ 1 := hw₀ _
  have happrox (x : V) : ‖v x-w (c x)‖ ≤ 2/(n : ℝ) := by
    by_cases hx : x ∈ B
    · simpa only [c,maskedLabel,if_pos hx,w] using happrox₀ x
    · simp only [v,maskedTest,c,maskedLabel,if_neg hx,w,sub_self,norm_zero]
      positivity
  have herr : ‖(𝔼 x, (f x : ℂ)*v x)-(𝔼 x, (f x : ℂ)*w (c x))‖ ≤ 2/(n : ℝ) := by
    rw [← expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)).trans_eq (one_mul _)).trans (happrox x)
  have hp : ‖𝔼 x, (f x : ℂ)*w (c x)‖ ≤ ∑ i : PhaseGrid n, |cellCharge c f (some i)| := by
    rw [cellCharge_pairing,Fintype.sum_option]
    simp only [w,mul_zero,zero_add]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hw₀ _) (abs_nonneg _)).trans_eq (mul_one _)
  have hh := (norm_le_norm_sub_add (𝔼 x, (f x : ℂ)*v x) (𝔼 x, (f x : ℂ)*w (c x))).trans (add_le_add herr hp)
  simpa only [v,maskedTest,mul_ite,mul_zero] using hh

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma mean_inside_charge_zero (n : ℕ) (B : Finset G) (f : G → ℝ) (hf0 : 𝔼 x, f x = 0)
    (q : G → G → ℂ) (hq : ∀ a x, ‖q a x‖ ≤ 1) :
    (𝔼 a, ∑ i : PhaseGrid n, cellCharge (maskedLabel n B (q a) (hq a)) (fun x ↦ f (a+x)) (some i)) = 0 := by
  simp_rw [inside_charge_sum]
  rw [expect_comm]
  have hz (x : G) : (𝔼 a, if x ∈ B then f (a+x) else 0) = 0 := by
    by_cases hx : x ∈ B
    · simp only [if_pos hx]
      exact (Fintype.expect_equiv (Equiv.addRight x) _ f (fun _ ↦ rfl)).trans hf0
    · simp [hx]
  simp only [hz,Fintype.expect_const]

/-- An averaged masked correlation of a globally centered function yields a
positive increment on an INTERIOR phase cell. No exterior alternative remains. -/
theorem averaged_masked_phase_inside_increment (B : Finset G) (f : G → ℝ) (q : G → G → ℂ)
    (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0) (hq : ∀ a x, ‖q a x‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) (hmesh : 2/(n : ℝ) ≤ r/2)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x, if x ∈ B then (f (a+x) : ℂ)*conj (q a x) else 0‖^2) :
    ∃ a : G, ∃ i : PhaseGrid n,
      r/(16*((2*n+1)^2 : ℕ)) ≤ cellMass (maskedLabel n B (q a) (hq a)) (some i) ∧
      r/16 ≤ 𝔼 x : cell (maskedLabel n B (q a) (hq a)) (some i), f (a+x) := by
  let corr : G → ℝ := fun a ↦ ‖𝔼 x, if x ∈ B then (f (a+x) : ℂ)*conj (q a x) else 0‖
  let u : G → PhaseGrid n → ℝ := fun a i ↦
    cellCharge (maskedLabel n B (q a) (hq a)) (fun x ↦ f (a+x)) (some i)
  have hnorm (a : G) : corr a ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    by_cases hx : x ∈ B
    · rw [if_pos hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_conj]
      exact (mul_le_mul (hf _) (hq a x) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    · simp only [if_neg hx,norm_zero,zero_le_one]
  have hnormsq (a : G) : (corr a)^2 ≤ corr a := by
    have hh : 0 ≤ corr a := norm_nonneg _
    nlinarith [hnorm a]
  have hl (a : G) : corr a ≤ 2/(n : ℝ)+∑ i, |u a i| :=
    masked_correlation_L1_bound B (fun x ↦ f (a+x)) (q a) (fun x ↦ hf _) (hq a) hn
  have hL : r/2 ≤ 𝔼 a, ((∑ i, |u a i|)+(∑ i, u a i)) := by
    have hh := hcorr.trans (expect_le_expect (fun a _ ↦ (hnormsq a).trans (hl a)))
    rw [expect_add_distrib,Fintype.expect_const] at hh
    rw [expect_add_distrib,mean_inside_charge_zero n B f hf0 q hq,add_zero]
    linarith
  obtain ⟨a,_,ha⟩ := exists_max_image univ (fun a ↦ (∑ i, |u a i|)+(∑ i, u a i)) univ_nonempty
  have hLa := hL.trans (expect_le univ_nonempty ha)
  obtain ⟨i,hi,hinc⟩ := positive_cell_of_L1_plus_mean
    (fun i ↦ cellMass (maskedLabel n B (q a) (hq a)) (some i)) (u a)
    (fun i ↦ cellMass_nonneg _ _) (inside_mass_sum_le_one n B (q a) (hq a))
    (fun i ↦ abs_cellCharge_le _ _ (fun x ↦ hf _) _) (by positivity : 0 < r/2) hLa
  have hpos : 0 < cellMass (maskedLabel n B (q a) (hq a)) (some i) :=
    (by positivity : 0 < (r/2)/(8*(Fintype.card (PhaseGrid n) : ℝ))).trans_le hi
  have hcell : (cell (maskedLabel n B (q a) (hq a)) (some i)).Nonempty := by
    by_contra hn
    rw [cellMass_eq_card,Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero,zero_div] at hpos
    exact (lt_irrefl 0) hpos
  change (r/2/8)*cellMass (maskedLabel n B (q a) (hq a)) (some i) ≤
    cellCharge (maskedLabel n B (q a) (hq a)) (fun x ↦ f (a+x)) (some i) at hinc
  rw [cellCharge_eq_mean _ _ _ hcell] at hinc
  refine ⟨a,i,?_,?_⟩
  · have hM : Fintype.card (PhaseGrid n) = (2*n+1)^2 := by simp [PhaseGrid,pow_two]
    rw [hM] at hi
    convert hi using 1 <;> ring
  · rw [show r/2/8 = r/16 by ring] at hinc
    nlinarith only [hinc,hpos]

#print axioms averaged_masked_phase_inside_increment
end Erdos3AveragedMaskedPhaseIncrement
