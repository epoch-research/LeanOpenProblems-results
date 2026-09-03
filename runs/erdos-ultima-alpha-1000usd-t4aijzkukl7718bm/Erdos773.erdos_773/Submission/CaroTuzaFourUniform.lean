import Submission.PriorityIntegralSelection

/-!
An explicit four-uniform Caro--Tuza bound. This improves the constant in an
alteration estimate, not its exponent, and does not settle Erdős 773.
-/
namespace Erdos773.CaroTuzaFourUniform
open Finset PriorityIntegralSelection
set_option maxHeartbeats 1500000

noncomputable def coefficient (d : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (1-x^3)^d

lemma coefficient_zero : coefficient 0 = 1 := by simp [coefficient]

lemma coefficient_pos (d : ℕ) : 0 < coefficient d := by
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro x hx
    exact pow_nonneg (sub_nonneg.mpr (pow_le_one₀ hx.1.le hx.2)) d
  · exact ⟨0,by norm_num,by simp⟩

lemma coefficient_recurrence (d : ℕ) :
    (3*(d:ℝ)+4)*coefficient (d+1) = (3*(d:ℝ)+3)*coefficient d := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x*(1-x^3)^(d+1))
      ((1-x^3)^(d+1)-3*((d:ℝ)+1)*x^3*(1-x^3)^d) x := by
    convert (hasDerivAt_id x).mul
      (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_pow 3 x)).pow (d+1)) using 1;
      simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun x _ => hd x)
    ((show Continuous (fun x : ℝ => (1-x^3)^(d+1)-3*((d:ℝ)+1)*x^3*(1-x^3)^d)
      by fun_prop).intervalIntegrable 0 1)
  have hi : (∫ x in (0:ℝ)..1, x^3*(1-x^3)^d) = coefficient d-coefficient (d+1) := by
    have he (x : ℝ) : x^3*(1-x^3)^d = (1-x^3)^d-(1-x^3)^(d+1) := by rw [pow_succ]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub
      ((show Continuous (fun x : ℝ => (1-x^3)^d) by fun_prop).intervalIntegrable 0 1)
      ((show Continuous (fun x : ℝ => (1-x^3)^(d+1)) by fun_prop).intervalIntegrable 0 1)]
    rfl
  have he (x : ℝ) : 3*((d:ℝ)+1)*x^3*(1-x^3)^d = 3*((d:ℝ)+1)*(x^3*(1-x^3)^d) := by ring
  simp_rw [he] at hint
  rw [intervalIntegral.integral_sub
      ((show Continuous (fun x : ℝ => (1-x^3)^(d+1)) by fun_prop).intervalIntegrable 0 1)
      ((show Continuous (fun x : ℝ => 3*((d:ℝ)+1)*(x^3*(1-x^3)^d)) by fun_prop).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, hi] at hint
  change coefficient (d+1)-3*((d:ℝ)+1)*(coefficient d-coefficient (d+1)) = _ at hint
  simp only [one_pow, sub_self, zero_pow (by omega : d+1 ≠ 0), mul_zero, zero_mul] at hint
  nlinarith only [hint]

/-- A convenient explicit lower bound on the cubed integral coefficient. -/
lemma coefficient_cube_lower (d : ℕ) : 2 ≤ (coefficient d)^3*(3*(d:ℝ)+2) := by
  induction d with
  | zero => norm_num [coefficient_zero]
  | succ d ih =>
    have hc := coefficient_pos d
    have hb : 0 < 3*(d:ℝ)+4 := by positivity
    have hpoly : (3*(d:ℝ)+2)*(3*(d:ℝ)+4)^3 ≤
        (3*(d:ℝ)+3)^3*(3*(d:ℝ)+5) := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    have hr := coefficient_recurrence d
    simp only [Nat.cast_succ]
    apply (mul_le_mul_iff_left₀ (pow_pos hb 3)).mp
    calc
      2*(3*(d:ℝ)+4)^3 ≤ ((coefficient d)^3*(3*(d:ℝ)+2))*(3*(d:ℝ)+4)^3 :=
        mul_le_mul_of_nonneg_right ih (pow_nonneg hb.le 3)
      _ = (coefficient d)^3*((3*(d:ℝ)+2)*(3*(d:ℝ)+4)^3) := by ring
      _ ≤ (coefficient d)^3*((3*(d:ℝ)+3)^3*(3*(d:ℝ)+5)) :=
        mul_le_mul_of_nonneg_left hpoly (pow_nonneg hc.le 3)
      _ = ((3*(d:ℝ)+3)*coefficient d)^3*(3*(d:ℝ)+5) := by ring
      _ = ((3*(d:ℝ)+4)*coefficient (d+1))^3*(3*(d:ℝ)+5) := by rw [hr]
      _ = ((coefficient (d+1))^3*(3*((d:ℝ)+1)+2))*(3*(d:ℝ)+4)^3 := by ring

/-- A polynomial form of the power-mean inequality needed below. -/
lemma inverse_cube_tangent (C D m : ℝ) (hC : 0 < C) (hm : 0 ≤ m)
    (hCD : 1 ≤ C^3*D) : 4*m ≤ D*m^4+3*C := by
  apply (mul_le_mul_iff_left₀ (pow_pos hC 3)).mp
  have hh := mul_le_mul_of_nonneg_right hCD (pow_nonneg hm 4)
  have hp := mul_nonneg (sq_nonneg (C-m))
    (show 0 ≤ 3*C^2+2*C*m+m^2 by positivity)
  nlinarith only [hh,hp]

lemma inverse_cube_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (C D : ι → ℝ)
    (hC : ∀ i ∈ s, 0 < C i) (hCD : ∀ i ∈ s, 1 ≤ (C i)^3*D i) :
    (s.card:ℝ)^4 ≤ (∑ i ∈ s, C i)^3*(∑ i ∈ s, D i) := by
  by_cases hs : s.Nonempty
  · have hn : (0:ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
    have hS : 0 < ∑ i ∈ s, C i := sum_pos (fun i hi => hC i hi) hs
    let m : ℝ := (∑ i ∈ s, C i)/s.card
    have hm : 0 < m := div_pos hS hn
    have hmn : m*s.card = ∑ i ∈ s, C i := div_mul_cancel₀ _ hn.ne'
    have ht := sum_le_sum (s := s) (fun i hi => inverse_cube_tangent (C i) (D i) m (hC i hi) hm.le (hCD i hi))
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at ht
    rw [← sum_mul, ← mul_sum] at ht
    have h1 : (s.card:ℝ) ≤ m^3*(∑ i ∈ s, D i) := by
      apply (mul_le_mul_iff_left₀ hm).mp
      nlinarith only [ht,hmn]
    have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hn.le 3)
    calc
      _ ≤ m^3*(∑ i ∈ s, D i)*(s.card:ℝ)^3 := by nlinarith only [h2]
      _ = (m*s.card)^3*(∑ i ∈ s, D i) := by ring
      _ = _ := by rw [hmn]
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma sum_degrees (H : Finset (Finset α)) :
    (∑ v : α, ((H.filter (fun e => v ∈ e)).card : ℝ)) = ∑ e ∈ H, (e.card:ℝ) := by
  have he (v : α) : ((H.filter (fun e => v ∈ e)).card : ℝ) =
      ∑ e ∈ H, if v ∈ e then (1:ℝ) else 0 := by simp
  simp_rw [he]
  rw [sum_comm]
  simp

/-- An actual independent set with a cubic bound in terms of the total edge
count. This is valid without linearity or codegree hypotheses. -/
theorem four_uniform_selection (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.card=4) :
    ∃ B : Finset α, (∀ e ∈ H, ¬e ⊆ B) ∧
      (Fintype.card α)^4 ≤ B.card^3*(6*H.card+Fintype.card α) := by
  obtain ⟨B,hB,hcard⟩ := uniform_integral_selection H 3 (by simpa using hH)
  let d (v : α) := (H.filter (fun e => v ∈ e)).card
  let C (v : α) := coefficient (d v)
  let D (v : α) : ℝ := (3*(d v:ℝ)+2)/2
  have hc : ∀ v ∈ (univ : Finset α), 0 < C v := fun v _ => coefficient_pos (d v)
  have hCD : ∀ v ∈ (univ : Finset α), 1 ≤ (C v)^3*D v := by
    intro v _
    have hh := coefficient_cube_lower (d v)
    dsimp [C,D]
    nlinarith only [hh]
  have hsum := inverse_cube_sum univ C D hc hCD
  have hdeg : (∑ v : α, (d v:ℝ)) = 4*(H.card:ℝ) := by
    dsimp [d]
    rw [sum_degrees]
    have he : (∑ e ∈ H, (e.card:ℝ)) = ∑ _e ∈ H, (4:ℝ) := by
      apply sum_congr rfl
      intro e he
      rw [hH e he]
      norm_num
    rw [he, sum_const, nsmul_eq_mul]
    ring
  have hD : (∑ v : α, D v) = 6*(H.card:ℝ)+Fintype.card α := by
    dsimp [D]
    rw [← sum_div, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ, hdeg]
    ring
  have hCcard : (∑ v : α, C v) ≤ B.card := hcard
  have hC0 : 0 ≤ ∑ v : α, C v := sum_nonneg (fun v hv => (hc v hv).le)
  rw [card_univ,hD] at hsum
  have hp := pow_le_pow_left₀ hC0 hCcard 3
  have hb := mul_le_mul_of_nonneg_right hp
    (show (0:ℝ) ≤ 6*(H.card:ℝ)+Fintype.card α by positivity)
  refine ⟨B,hB,?_⟩
  have hh := hsum.trans hb
  exact_mod_cast hh

/-- The same cubic estimate on an arbitrary finite ambient set. -/
theorem finite_selection {β : Type*} [DecidableEq β]
    (A : Finset β) (H : Finset (Finset β))
    (hsub : ∀ e ∈ H, e ⊆ A) (hfour : ∀ e ∈ H, e.card=4) :
    ∃ B ⊆ A, (∀ e ∈ H, ¬e ⊆ B) ∧ A.card^4 ≤ B.card^3*(6*H.card+A.card) := by
  classical
  let J : Finset (Finset A) := H.image (Finset.subtype (fun x => x ∈ A))
  have hjfour : ∀ e ∈ J, e.card=4 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    rw [card_subtype, filter_eq_self.mpr (hsub f hf), hfour f hf]
  obtain ⟨C,hC,hcard⟩ := four_uniform_selection J hjfour
  let B : Finset β := C.image Subtype.val
  have hBA : B ⊆ A := by
    rintro x hx
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hx
    exact c.property
  have hBcard : B.card=C.card := card_image_of_injective _ Subtype.val_injective
  have hJcard : J.card ≤ H.card := card_image_le
  refine ⟨B,hBA,?_,?_⟩
  · intro e he heB
    apply hC (e.subtype (fun x => x ∈ A)) (mem_image.mpr ⟨e,he,rfl⟩)
    intro c hc
    have hcB := heB (mem_subtype.mp hc)
    obtain ⟨d,hd,heq⟩ := mem_image.mp hcB
    have hdc : d=c := Subtype.ext heq
    simpa only [← hdc] using hd
  · rw [hBcard]
    simp only [Fintype.card_coe] at hcard
    exact hcard.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hJcard) _))

#print axioms coefficient_recurrence
#print axioms coefficient_cube_lower
#print axioms inverse_cube_sum
#print axioms four_uniform_selection
#print axioms finite_selection
end Erdos773.CaroTuzaFourUniform
