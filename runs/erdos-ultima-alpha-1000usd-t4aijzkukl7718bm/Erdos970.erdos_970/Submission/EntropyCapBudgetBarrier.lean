import Submission.FiniteHerbstBound

/-! Limitation of the particular deterministic-cap Herbst certificate.
This is not a counterexample to any Jacobsthal upper bound. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling
set_option maxHeartbeats 1200000

lemma density_le_half_of_two_mem (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h2 : 2 ∈ P) : density P ≤ 1/2 := by
  classical
  have ho : ∀ p ∈ P.erase 2, p.Prime := fun p hp => hP p (mem_of_mem_erase hp)
  have hsmall : density (P.erase 2) ≤ 1 := by
    apply prod_le_one
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (ho p hp).one_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (ho p hp).pos
      exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
    · intro p hp
      exact sub_le_self _ (by positivity)
  have he : density P = (1/2 : ℝ)*density (P.erase 2) := by
    unfold density
    rw [← insert_erase h2,prod_insert (notMem_erase 2 P)]
    norm_num
  rw [he]
  linarith only [hsmall]

lemma half_card_le_cap_two (S : Finset ℕ) (B : ℝ)
    (hcap : ∀ a : Fin 2, classHits S 2 a ≤ B) : (S.card : ℝ)/2 ≤ B := by
  have hh := residueMean_mono 2 hcap
  simpa only [classHits_mean S 2 (by norm_num),residueMean_const 2 (by norm_num),
    Nat.cast_ofNat] using hh

/-- No choice of nonnegative tilt and valid caps makes this particular
Herbst exponent large when prime two is present. -/
theorem cap_herbst_exponent_le_half (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h2 : 2 ∈ P) (B : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hcap : ∀ p ∈ P, ∀ a : Fin p, classHits S p a ≤ B p) :
    (S.card : ℝ)*density P*T/(1+entropyCapBudget P B T*T) ≤ 1/2 := by
  have hμ : (S.card : ℝ)*density P ≤ B 2 := by
    have hh := mul_le_mul_of_nonneg_left (density_le_half_of_two_mem P hP h2)
      (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
    have hc := half_card_le_cap_two S (B 2) (hcap 2 h2)
    nlinarith only [hh,hc]
  have hD : (1+exp (T*B 2))*B 2/2 ≤ entropyCapBudget P B T := by
    have hh := single_le_sum (s := P) (f := fun p => (1+exp (T*B p))*B p/(p : ℝ))
      (fun p hp => div_nonneg (mul_nonneg (by positivity) (hB p hp)) (by positivity)) h2
    simpa only [entropyCapBudget,Nat.cast_ofNat] using hh
  have hDT := mul_le_mul_of_nonneg_right hD hT
  have hx : 0 ≤ T*B 2 := mul_nonneg hT (hB 2 h2)
  have hex := mul_le_mul_of_nonneg_right (add_one_le_exp (T*B 2)) hx
  have hμT := mul_le_mul_of_nonneg_right hμ hT
  have hs := sq_nonneg (T*B 2-1)
  have hden : 0 < 1+entropyCapBudget P B T*T := by
    have hh := entropyCapBudget_nonneg P B T hB
    positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hDT,hex,hμT,hs]

lemma two_le_phase_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h2 : 2 ∈ P) :
    2 ≤ Fintype.card (Phase P) := by
  classical
  let e : Fin 2 → Phase P := fun a q =>
    if h : q.val = 2 then ⟨a.val,by simpa only [h] using a.isLt⟩
    else ⟨0,(hP q.val q.property).pos⟩
  have hi : Function.Injective e := by
    intro a b hab
    have hh := congrArg (fun r : Phase P => (r ⟨2,h2⟩).val) hab
    simp only [e,dif_pos rfl] at hh
    exact Fin.ext hh
  have hh := Fintype.card_le_of_injective e hi
  simpa only [Fintype.card_fin] using hh

/-- Exact failure of the auxiliary certificate's strict cost inequality.
It says nothing negative about the existence of survivors themselves. -/
theorem cap_herbst_cost_impossible_of_two_mem
    (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h2 : 2 ∈ P)
    (B : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hcap : ∀ p ∈ P, ∀ a : Fin p, classHits S p a ≤ B p) :
    ¬log (Fintype.card (Phase P) : ℝ) <
      (S.card : ℝ)*density P*T/(1+entropyCapBudget P B T*T) := by
  have hl : (1/2 : ℝ) ≤ log 2 := by
    have hh := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hc : (2 : ℝ) ≤ Fintype.card (Phase P) := by exact_mod_cast two_le_phase_card P hP h2
  have hg := log_le_log (by norm_num : (0 : ℝ) < 2) hc
  exact not_lt_of_ge ((cap_herbst_exponent_le_half P S hP h2 B T hT hB hcap).trans (hl.trans hg))

#print axioms cap_herbst_exponent_le_half
#print axioms cap_herbst_cost_impossible_of_two_mem
end Erdos970.FiniteGibbs
