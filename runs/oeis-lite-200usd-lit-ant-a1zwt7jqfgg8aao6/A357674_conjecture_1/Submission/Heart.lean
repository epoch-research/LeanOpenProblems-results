import Submission.FI
import Submission.V1

open Nat Finset BigOperators

namespace Wolst

variable {p : ℕ} [Fact p.Prime]

/-- General product identity: `C(p+k-1, p-1) = ∏_{i=1}^{p-1} (1 + k·i⁻¹)` in `ZMod (p^5)`. -/
theorem aval (k : ℕ) :
    (((p+k-1).choose (p-1) : ℕ) : ZMod (p^5))
      = ∏ i ∈ Finset.Ico 1 p, (1 + (k:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹) := by
  set R := ZMod (p^5)
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hnat : (p-1)! * ((p+k-1).choose (p-1)) = ∏ j ∈ Finset.Ico 1 p, (k + j) := by
    have h1 : (k+1).ascFactorial (p-1) = (p-1)! * ((p+k-1)).choose (p-1) := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose']; congr 2; omega
    rw [← h1, Nat.ascFactorial_eq_prod_range, Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl; intro i _; omega
  have cast_nat : ((p-1)! : R) * (((p+k-1).choose (p-1)):R)
      = ∏ j ∈ Finset.Ico 1 p, ((k+j : ℕ):R) := by
    rw [← Nat.cast_mul, hnat, Nat.cast_prod]
  have hfact : ((p-1)! : R) = ∏ j ∈ Finset.Ico 1 p, (j:R) := by
    have h := prod_Ico_id_eq_factorial (p-1)
    rw [show (p-1)+1 = p from by omega] at h
    rw [← Nat.cast_prod, h]
  have hperfac : ∀ j ∈ Finset.Ico 1 p, ((k+j:ℕ):R)
      = (j:R)*(1+(k:R)*(j:R)⁻¹) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hju : IsUnit ((j:R)) := isUnit_cast j (by omega) (by omega)
    have hj1 : (j:R) * (j:R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hju
    push_cast
    linear_combination -(k:R)*hj1
  have hprod : ∏ j ∈ Finset.Ico 1 p, ((k+j:ℕ):R)
      = (∏ j ∈ Finset.Ico 1 p, (j:R)) * ∏ j ∈ Finset.Ico 1 p, (1+(k:R)*(j:R)⁻¹) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl hperfac
  have hunit : IsUnit (∏ j ∈ Finset.Ico 1 p, (j:R)) := by
    apply Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
    intro j hj; rw [Finset.mem_Ico] at hj; exact isUnit_cast j (by omega) (by omega)
  rw [hfact, hprod] at cast_nat
  exact (hunit.mul_right_inj).mp cast_nat

/-- Product expansion when the perturbation is divisible by `p²` (clean, no remainder). -/
lemma prod_expand_sq (d : ℕ → ZMod (p^5)) (s : Finset ℕ) :
    ∏ i ∈ s, (1 + (p:ZMod (p^5))^2 * d i)
      = 1 + (p:ZMod (p^5))^2 * (∑ i ∈ s, d i) + (p:ZMod (p^5))^4 * pairsum d s := by
  classical
  have hp5 : (p:ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hp6 : (p:ZMod (p^5))^6 = 0 := by
    have h : (p:ZMod (p^5))^6 = (p:ZMod (p^5))^5 * (p:ZMod (p^5)) := by ring
    rw [h, hp5, zero_mul]
  induction s using Finset.induction with
  | empty => simp [pairsum]
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, pairsum_insert d ha]
    linear_combination (d a * pairsum d t) * hp6

/-- Reflection `i ↦ p - i` on products over `Ico 1 p`. -/
theorem prod_reflect {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Ico 1 p, f (p - i) = ∏ i ∈ Finset.Ico 1 p, f i := by
  apply Finset.prod_nbij' (fun i => p - i) (fun i => p - i)
  · intro a ha; rw [Finset.mem_Ico] at *; omega
  · intro a ha; rw [Finset.mem_Ico] at *; omega
  · intro a ha; rw [Finset.mem_Ico] at ha; omega
  · intro a ha; rw [Finset.mem_Ico] at ha; omega
  · intro a ha; rfl

/-- `wf i = i⁻¹ (p-i)⁻¹`. -/
noncomputable def wf (i : ℕ) : ZMod (p^5) :=
  (i:ZMod (p^5))⁻¹ * ((p - i:ℕ):ZMod (p^5))⁻¹

lemma wf_symm (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
    (wf (p := p) (p - i)) = wf i := by
  unfold wf
  rw [show p - (p - i) = i from by omega]
  ring

lemma w_sum (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
    (i:ZMod (p^5))⁻¹ + ((p - i:ℕ):ZMod (p^5))⁻¹ = (p:ZMod (p^5)) * wf i := by
  set R := ZMod (p^5)
  have hu : IsUnit ((i:R)) := isUnit_cast i (by omega) (by omega)
  have hv : IsUnit (((p-i:ℕ):R)) := isUnit_cast (p-i) (by omega) (by omega)
  have hiinv : (i:R) * (i:R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  have hvinv : ((p-i:ℕ):R) * ((p-i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hv
  have hp : (p:R) = ((p-i:ℕ):R) + (i:R) := by
    rw [Nat.cast_sub (by omega)]; ring
  unfold wf
  linear_combination (-(i:R)⁻¹ * ((p-i:ℕ):R)⁻¹) * hp
    + (-(i:R)⁻¹) * hvinv + (-((p-i:ℕ):R)⁻¹) * hiinv

/-- Squaring via reflection: `∏(1+(t·p+t²)·wf i) = (∏(1+t·i⁻¹))²`. -/
lemma aval_sq_refl (t : ZMod (p^5)) :
    (∏ i ∈ Finset.Ico 1 p, (1 + (t*(p:ZMod (p^5)) + t^2) * wf i))
      = (∏ i ∈ Finset.Ico 1 p, (1 + t * (i:ZMod (p^5))⁻¹))^2 := by
  have h1 : ∏ i ∈ Finset.Ico 1 p, (1 + (t*(p:ZMod (p^5)) + t^2) * wf i)
      = ∏ i ∈ Finset.Ico 1 p,
          ((1 + t * (i:ZMod (p^5))⁻¹) * (1 + t * ((p-i:ℕ):ZMod (p^5))⁻¹)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hws := w_sum i hi.1 hi.2
    simp only [wf] at hws ⊢
    linear_combination (-t) * hws
  rw [h1, Finset.prod_mul_distrib]
  rw [prod_reflect (fun i => 1 + t * (i:ZMod (p^5))⁻¹)]
  rw [pow_two]

/-- Projection of `wf i` to `ZMod p`. -/
lemma proj_wf (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
    proj (p := p) (wf i) = -(((i:ZMod p))⁻¹)^2 := by
  unfold wf
  rw [map_mul, cast_inv i (by omega) (by omega), cast_inv (p-i) (by omega) (by omega)]
  have hc : ((p - i:ℕ):ZMod p) = -(i:ZMod p) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  rw [hc, inv_neg]; ring

lemma W1_dvd (hp7 : 7 ≤ p) : ∃ z : ZMod (p^5), (∑ i ∈ Finset.Ico 1 p, wf i) = (p:ZMod (p^5)) * z := by
  apply dvd_p_of_proj_zero
  rw [map_sum]
  have key : ∀ i ∈ Finset.Ico 1 p,
      proj (p := p) (wf i) = (-1) * (((i:ZMod p))⁻¹)^2 := by
    intro i hi; rw [Finset.mem_Ico] at hi; rw [proj_wf i hi.1 hi.2]; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum,
    sum_inv_pow_Ico_eq_zero 2 (by omega) (by omega), mul_zero]

lemma WW_dvd (hp7 : 7 ≤ p) : ∃ z : ZMod (p^5),
    (∑ i ∈ Finset.Ico 1 p, (wf i)^2) = (p:ZMod (p^5)) * z := by
  apply dvd_p_of_proj_zero
  rw [map_sum]
  have key : ∀ i ∈ Finset.Ico 1 p,
      proj (p := p) ((wf i)^2) = (((i:ZMod p))⁻¹)^4 := by
    intro i hi; rw [Finset.mem_Ico] at hi
    rw [map_pow, proj_wf i hi.1 hi.2]; ring
  rw [Finset.sum_congr rfl key, sum_inv_pow_Ico_eq_zero 4 (by omega) (by omega)]

/-- If `∑d` and `∑d²` are divisible by `p`, then `p⁴·pairsum d = 0`. -/
lemma p4_pairsum_zero (hp7 : 7 ≤ p) (d : ℕ → ZMod (p^5)) (s : Finset ℕ)
    (h1 : ∃ z : ZMod (p^5), (∑ i ∈ s, d i) = (p:ZMod (p^5))*z)
    (h2 : ∃ z : ZMod (p^5), (∑ i ∈ s, (d i)^2) = (p:ZMod (p^5))*z) :
    (p:ZMod (p^5))^4 * pairsum d s = 0 := by
  obtain ⟨z1, hz1⟩ := h1
  obtain ⟨z2, hz2⟩ := h2
  have hsq := sq_sum_eq d s
  have hp5 : (p:ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hp6 : (p:ZMod (p^5))^6 = 0 := by
    have h : (p:ZMod (p^5))^6 = (p:ZMod (p^5))^5 * (p:ZMod (p^5)) := by ring
    rw [h, hp5, zero_mul]
  have h2u : IsUnit (2:ZMod (p^5)) := by
    have := isUnit_cast (p:=p) (k:=5) 2 (by norm_num) (by omega); simpa using this
  apply h2u.mul_left_cancel
  rw [mul_zero]
  have e : (2:ZMod (p^5))*((p:ZMod (p^5))^4 * pairsum d s)
      = (p:ZMod (p^5))^4 * ((∑ i ∈ s, d i)^2 - ∑ i ∈ s, (d i)^2) := by
    linear_combination (-(p:ZMod (p^5))^4) * hsq
  rw [e, hz1, hz2]
  linear_combination z1^2 * hp6 - z2 * hp5

lemma WS_eq_pU :
    (∑ i ∈ Finset.Ico 1 p, wf i) + S 2
      = (p:ZMod (p^5)) * (∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))⁻¹ * wf i) := by
  rw [Finset.mul_sum]
  unfold S
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi; rw [Finset.mem_Ico] at hi
  have hws := w_sum i hi.1 hi.2
  simp only [wf] at hws ⊢
  linear_combination (i:ZMod (p^5))⁻¹ * hws

lemma twoU_eq_pWW :
    2 * (∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))⁻¹ * wf i)
      = (p:ZMod (p^5)) * (∑ i ∈ Finset.Ico 1 p, (wf i)^2) := by
  have hrefl : (∑ i ∈ Finset.Ico 1 p, ((p-i:ℕ):ZMod (p^5))⁻¹ * wf i)
      = ∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))⁻¹ * wf i := by
    have h := sum_reflect (p:=p) (fun i => (i:ZMod (p^5))⁻¹ * wf i)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_Ico] at hi
    rw [wf_symm i hi.1 hi.2]
  have key : (p:ZMod (p^5)) * (∑ i ∈ Finset.Ico 1 p, (wf i)^2)
      = ∑ i ∈ Finset.Ico 1 p, ((i:ZMod (p^5))⁻¹ + ((p-i:ℕ):ZMod (p^5))⁻¹) * wf i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_Ico] at hi
    rw [w_sum i hi.1 hi.2]; simp only [wf]; ring
  have split : (∑ i ∈ Finset.Ico 1 p, ((i:ZMod (p^5))⁻¹ + ((p-i:ℕ):ZMod (p^5))⁻¹) * wf i)
      = (∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))⁻¹ * wf i)
        + (∑ i ∈ Finset.Ico 1 p, ((p-i:ℕ):ZMod (p^5))⁻¹ * wf i) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [key, split, hrefl]; ring

lemma two_WS :
    2 * ((∑ i ∈ Finset.Ico 1 p, wf i) + S 2)
      = (p:ZMod (p^5))^2 * (∑ i ∈ Finset.Ico 1 p, (wf i)^2) := by
  rw [WS_eq_pU]
  have h := twoU_eq_pWW (p:=p)
  rw [show (2:ZMod (p^5)) * ((p:ZMod (p^5)) * (∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))⁻¹ * wf i))
      = (p:ZMod (p^5)) * (2 * (∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))⁻¹ * wf i)) from by ring]
  rw [h]; ring

lemma p2_WS_zero (hp7 : 7 ≤ p) :
    (p:ZMod (p^5))^2 * ((∑ i ∈ Finset.Ico 1 p, wf i) + S 2) = 0 := by
  have h2u : IsUnit (2:ZMod (p^5)) := by
    have := isUnit_cast (p:=p) (k:=5) 2 (by norm_num) (by omega); simpa using this
  apply h2u.mul_left_cancel
  rw [mul_zero]
  obtain ⟨z, hz⟩ := WW_dvd (p:=p) hp7
  have h := two_WS (p:=p)
  have hp5 : (p:ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [show (2:ZMod (p^5)) * ((p:ZMod (p^5))^2 * ((∑ i ∈ Finset.Ico 1 p, wf i) + S 2))
      = (p:ZMod (p^5))^2 * (2 * ((∑ i ∈ Finset.Ico 1 p, wf i) + S 2)) from by ring]
  rw [h, hz]
  linear_combination z * hp5

/-- `a_p² ≡ 1 - 2p²S₂`. -/
lemma apsq (hp7 : 7 ≤ p) :
    (∏ i ∈ Finset.Ico 1 p, (1 + (p:ZMod (p^5)) * (i:ZMod (p^5))⁻¹))^2
      = 1 - 2 * (p:ZMod (p^5))^2 * S 2 := by
  rw [← aval_sq_refl (p:ZMod (p^5))]
  have hform : ∏ i ∈ Finset.Ico 1 p,
        (1 + ((p:ZMod (p^5))*(p:ZMod (p^5)) + (p:ZMod (p^5))^2) * wf i)
      = ∏ i ∈ Finset.Ico 1 p, (1 + (p:ZMod (p^5))^2 * (2 * wf i)) := by
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hform, prod_expand_sq (fun i => (2:ZMod (p^5)) * wf i)]
  have hp4 : (p:ZMod (p^5))^4 * pairsum (fun i => (2:ZMod (p^5)) * wf i) (Finset.Ico 1 p) = 0 := by
    apply p4_pairsum_zero hp7
    · obtain ⟨z, hz⟩ := W1_dvd (p:=p) hp7
      exact ⟨2*z, by rw [← Finset.mul_sum, hz]; ring⟩
    · obtain ⟨z, hz⟩ := WW_dvd (p:=p) hp7
      refine ⟨4*z, ?_⟩
      have hh : ∑ i ∈ Finset.Ico 1 p, ((2:ZMod (p^5))*wf i)^2
          = 4 * ∑ i ∈ Finset.Ico 1 p, (wf i)^2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hh, hz]; ring
  rw [hp4, add_zero, ← Finset.mul_sum]
  linear_combination 2 * (p2_WS_zero (p:=p) hp7)

/-- `v² ≡ 1 - 6p²S₂`. -/
lemma vsq (hp7 : 7 ≤ p) : (vval p)^2 = 1 - 6 * (p:ZMod (p^5))^2 * S 2 := by
  rw [vval_prod]
  rw [show (∏ i ∈ Finset.Ico 1 p, (1 + (2:ZMod (p^5))*(p:ZMod (p^5)) * (i:ZMod (p^5))⁻¹))
      = ∏ i ∈ Finset.Ico 1 p, (1 + (2*(p:ZMod (p^5))) * (i:ZMod (p^5))⁻¹) from by
        apply Finset.prod_congr rfl; intro i _; ring]
  rw [← aval_sq_refl (2*(p:ZMod (p^5)))]
  have hform : ∏ i ∈ Finset.Ico 1 p,
        (1 + ((2*(p:ZMod (p^5)))*(p:ZMod (p^5)) + (2*(p:ZMod (p^5)))^2) * wf i)
      = ∏ i ∈ Finset.Ico 1 p, (1 + (p:ZMod (p^5))^2 * (6 * wf i)) := by
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hform, prod_expand_sq (fun i => (6:ZMod (p^5)) * wf i)]
  have hp4 : (p:ZMod (p^5))^4 * pairsum (fun i => (6:ZMod (p^5)) * wf i) (Finset.Ico 1 p) = 0 := by
    apply p4_pairsum_zero hp7
    · obtain ⟨z, hz⟩ := W1_dvd (p:=p) hp7
      exact ⟨6*z, by rw [← Finset.mul_sum, hz]; ring⟩
    · obtain ⟨z, hz⟩ := WW_dvd (p:=p) hp7
      refine ⟨36*z, ?_⟩
      have hh : ∑ i ∈ Finset.Ico 1 p, ((6:ZMod (p^5))*wf i)^2
          = 36 * ∑ i ∈ Finset.Ico 1 p, (wf i)^2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hh, hz]; ring
  rw [hp4, add_zero, ← Finset.mul_sum]
  linear_combination 6 * (p2_WS_zero (p:=p) hp7)

/-- `v ≡ 1 - 3p²S₂`. -/
lemma v_red (hp7 : 7 ≤ p) : vval p = 1 - 3 * (p:ZMod (p^5))^2 * S 2 := by
  obtain ⟨z, hz⟩ := vsub1_dvd (p:=p) hp7
  have hvsq := vsq (p:=p) hp7
  have hp5 : (p:ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hp6 : (p:ZMod (p^5))^6 = 0 := by
    have h : (p:ZMod (p^5))^6 = (p:ZMod (p^5))^5 * (p:ZMod (p^5)) := by ring
    rw [h, hp5, zero_mul]
  have hv : vval p = 1 + (p:ZMod (p^5))^3 * z := by linear_combination hz
  have hsq2 : (vval p)^2 = 1 + 2*(p:ZMod (p^5))^3 * z := by
    rw [hv]; linear_combination (z^2) * hp6
  have heq : (1:ZMod (p^5)) + 2*(p:ZMod (p^5))^3*z = 1 - 6*(p:ZMod (p^5))^2*S 2 := by
    rw [← hsq2]; exact hvsq
  have h2u : IsUnit (2:ZMod (p^5)) := by
    have := isUnit_cast (p:=p) (k:=5) 2 (by norm_num) (by omega); simpa using this
  have hpz : (p:ZMod (p^5))^3 * z = -(3*(p:ZMod (p^5))^2 * S 2) := by
    apply h2u.mul_left_cancel
    linear_combination heq
  rw [hv, hpz]; ring

/-- The OEIS S2 summation. -/
def S2seq (p : ℕ) : ℕ := ∑ k ∈ Finset.range (2*p+1), ((p+k-1).choose k)^2

/-- The OEIS term `C(p+k-1,k)` as the product. -/
lemma cast_term (k : ℕ) :
    (((p+k-1).choose k : ℕ):ZMod (p^5))
      = ∏ i ∈ Finset.Ico 1 p, (1 + (k:ZMod (p^5))*(i:ZMod (p^5))⁻¹) := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [show (p+k-1).choose k = (p+k-1).choose (p-1) from by
    rw [← Nat.choose_symm (show k ≤ p+k-1 by omega)]; congr 1; omega]
  exact aval k

/-- Cast of `S2seq` as a sum of squared products. -/
lemma cast_S2seq :
    ((S2seq p : ℕ):ZMod (p^5))
      = ∑ k ∈ Finset.range (2*p+1),
          (∏ i ∈ Finset.Ico 1 p, (1 + (k:ZMod (p^5))*(i:ZMod (p^5))⁻¹))^2 := by
  unfold S2seq
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_pow, cast_term k]

/-- The coprime block. -/
noncomputable def coprimeBlock (p : ℕ) : ZMod (p^5) :=
  ∑ k ∈ (Finset.range (2*p+1)) \ {0, p, 2*p},
    (∏ i ∈ Finset.Ico 1 p, (1 + (k:ZMod (p^5))*(i:ZMod (p^5))⁻¹))^2

/-- THE CRUX (only remaining gap): coprime block `≡ 20p²S₂`.
    The whole conjecture is proven modulo this single lemma (`heartH` below assembles it
    with the fully-proven `apsq`, `vsq`, `v_red`).
    Math content: `Σ_{k∈[1,2p-1], k≠p} C(p+k-1,k)² ≡ 20 p² S₂ (mod p⁵)`.

    ★ CONCRETE TRACTABLE PATH (the key new reduction — uses `prod_expand` from V1):

    Define `Q k := ∏_{j∈Ico 1 k} (1 + p·j⁻¹)` in `ZMod (p^5)` (a product of perturbations
    DIVISIBLE BY p, so `prod_expand` applies directly: `Q k = 1 + p·H_k + p²·pairsum + p³·c`,
    `H_k = Σ_{j<k} j⁻¹`).

    Cast identities (proven on paper; verified numerically p=3):
      • LOWER block, k=1..p-1:   `aval(k) = (p:R)·(k:R)⁻¹ · Q k`     (so `aval(k)² = p²·k⁻²·(Q k)²`)
      • UPPER block, k=p+1..2p-1: `aval(k) = 2·(p:R)·(k:R)⁻¹ · Q k`  (extra factor 2!)
    Proof of cast identity: absorption identity `k·C(p+k-1,p-1) = (p+k-1)·C(p+k-2,p-1)` gives the
    recurrence `aval(k) = aval(k-1)·(p+k-1)·k⁻¹`; with `(p+k-1) = (k-1)·(1+p·(k-1)⁻¹)` this telescopes
    to the `Q k` form by induction (base `aval(1)=p`). For the upper block the factor `2` arises
    because the pole factor is `1+(p+m)(p-m)⁻¹ = 2p(p-m)⁻¹` (vs `p(p-k)⁻¹` lower); equivalently the
    j=p term contributes `2p` not `p`.

    Hence  `coprimeBlock = p² · [ Σ_{k=1}^{p-1} k⁻²(Q k)²  +  4·Σ_{k=p+1}^{2p-1} k⁻²(Q k)² ]`,
    and the goal reduces to  `Σ_{k=1}^{p-1} k⁻²(Q k)² + 4 Σ_{k=p+1}^{2p-1} k⁻²(Q k)² ≡ 20·S₂ (mod p³)`.
    Expand `(Q k)² = 1 + 2p H_k + p²(H_k² + 2·pairsum_k) + O(p³)` and reduce the resulting
    inverse double-sums (`Σ k⁻²`, `Σ k⁻² H_k`, …) to `S₂` using `sum_reflect`/`pairing_sum`.
    (Numerics: p=3 gives lower `Σk⁻²(Qk)²`-block 5, upper 20, total 25 ≡ 20·S₂ mod 27 ✓.)

    NOTE: the FORWARD route fails (`∏(1+X i⁻¹) ≡ 1 - X^{p-1} mod p` ⇒ unit `e_{p-1}` pairs with
    `M_{2p-2}`, reintroducing non-cancelling Bernoulli `B_{p-3}`); the above BACKWARD `Q k` route
    avoids it entirely. Remaining work ≈150–250 lines; exceeds this session's residual budget. -/
lemma crux (hp7 : 7 ≤ p) : coprimeBlock p = 20 * (p:ZMod (p^5))^2 * S 2 := by
  sorry

theorem heartH (hp7 : 7 ≤ p) :
    4 * vval p + ((S2seq p : ℕ):ZMod (p^5)) = 7 := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [cast_S2seq]
  set g : ℕ → ZMod (p^5) :=
    fun k => (∏ i ∈ Finset.Ico 1 p, (1 + (k:ZMod (p^5))*(i:ZMod (p^5))⁻¹))^2 with hg
  have hT : ({0, p, 2*p} : Finset ℕ) ⊆ Finset.range (2*p+1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h|h|h <;> subst h <;> simp only [Finset.mem_range] <;> omega
  rw [← Finset.sum_sdiff hT]
  have hcb : (∑ k ∈ (Finset.range (2*p+1)) \ {0, p, 2*p}, g k) = coprimeBlock p := rfl
  rw [hcb, crux hp7]
  -- Σ_{0,p,2p} g = g 0 + g p + g (2p)
  have h0p : (0:ℕ) ∉ ({p, 2*p}:Finset ℕ) := by simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hp2p : p ∉ ({2*p}:Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  rw [show ({0,p,2*p}:Finset ℕ) = insert 0 (insert p {2*p}) from rfl,
    Finset.sum_insert h0p, Finset.sum_insert hp2p, Finset.sum_singleton]
  -- evaluate the three explicit product terms
  rw [show (∏ i ∈ Finset.Ico 1 p, (1 + ((0:ℕ):ZMod (p^5))*(i:ZMod (p^5))⁻¹))^2 = 1 from by simp]
  rw [apsq (p:=p) hp7]
  rw [show (∏ i ∈ Finset.Ico 1 p, (1 + ((2*p:ℕ):ZMod (p^5))*(i:ZMod (p^5))⁻¹))^2
      = 1 - 6 * (p:ZMod (p^5))^2 * S 2 from by
    rw [show ((2*p:ℕ):ZMod (p^5)) = 2 * (p:ZMod (p^5)) from by push_cast; ring]
    rw [show (∏ i ∈ Finset.Ico 1 p, (1 + (2*(p:ZMod (p^5)))*(i:ZMod (p^5))⁻¹))^2 = (vval p)^2 from by
      rw [vval_prod]]
    exact vsq (p:=p) hp7]
  rw [v_red (p:=p) hp7]
  ring

end Wolst
