import FormalConjecturesUtil
import Submission.ThetaZeroLinks

/-! A degree alternative retaining the exact global singleton-codegree budget. -/
open Finset
namespace Erdos713ThetaSingletonDegree
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaZeroPairs
open Erdos713ThetaZeroAlternative Erdos713ThetaZeroLinks Erdos713ThetaCross
set_option maxHeartbeats 2000000

lemma ninth_from_zero_alternative {n d D K e k z Z : ℕ} (hn : 0 < n)
    (he : d*(d-1) ≤ e) (hD : D ≤ K*d) (hk : k ≤ K*d) (hz : n*z ≤ Z)
    (halt : e ≤ 200*n ∨ e^2 ≤ 640*n*k^2 ∨ e^6 ≤ 3932160000*n^4*D*k^2*z) :
    d^2 ≤ 2560*(K+1)^2*n ∨ d^9 ≤ 251658240000*K^3*n^3*Z := by
  by_cases hd : 2 ≤ d
  · have hsub : d-1+1 = d := Nat.sub_add_cancel (by omega)
    have hd2 : d^2 ≤ 2*e := by nlinarith
    rcases halt with hl | hm | hh
    · apply Or.inl
      have hdsq : d^2 ≤ 400*n := by omega
      have hK1 : 1 ≤ (K+1)^2 := one_le_pow₀ (by omega)
      exact hdsq.trans (Nat.mul_le_mul_right _ (by nlinarith only [hK1]))
    · apply Or.inl
      have hd4 := Nat.pow_le_pow_left hd2 2
      have hk2 := Nat.pow_le_pow_left hk 2
      have he2 : e^2 ≤ 640*n*(K*d)^2 := hm.trans (Nat.mul_le_mul_left _ hk2)
      have hc : d^2*d^2 ≤ (2560*K^2*n)*d^2 := by
        calc
          _ = (d^2)^2 := by ring
          _ ≤ (2*e)^2 := hd4
          _ = 4*e^2 := by ring
          _ ≤ 4*(640*n*(K*d)^2) := Nat.mul_le_mul_left _ he2
          _ = _ := by ring
      have hdsq : d^2 ≤ 2560*K^2*n := Nat.le_of_mul_le_mul_right hc (by positivity)
      exact hdsq.trans (by gcongr; omega)
    · apply Or.inr
      have hd12 := Nat.pow_le_pow_left hd2 6
      have hk2 := Nat.pow_le_pow_left hk 2
      have he6 : e^6 ≤ 3932160000*n^4*(K*d)*(K*d)^2*z :=
        hh.trans (Nat.mul_le_mul_right z (Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) hk2))
      have hb : d^9*d^3 ≤ (251658240000*K^3*n^4*z)*d^3 := by
        calc
          _ = (d^2)^6 := by ring
          _ ≤ (2*e)^6 := hd12
          _ = 64*e^6 := by ring
          _ ≤ 64*(3932160000*n^4*(K*d)*(K*d)^2*z) := Nat.mul_le_mul_left _ he6
          _ = _ := by ring
      have hcancel := Nat.le_of_mul_le_mul_right hb (by positivity : 0 < d^3)
      have hh : d^9*n ≤ (251658240000*K^3*n^3*Z)*n := by
        calc
          _ ≤ (251658240000*K^3*n^4*z)*n := Nat.mul_le_mul_right n hcancel
          _ = (251658240000*K^3*n^3*(n*z))*n := by ring
          _ ≤ (251658240000*K^3*n^3*Z)*n :=
            Nat.mul_le_mul_right n (Nat.mul_le_mul_left _ hz)
      exact Nat.le_of_mul_le_mul_right hh hn
  · apply Or.inl
    have hd1 : d^2 ≤ 1 := by interval_cases d <;> decide
    have hK1 : 1 ≤ (K+1)^2 := one_le_pow₀ (by omega)
    have hn1 : 1 ≤ n := hn
    have hh := Nat.mul_le_mul hK1 hn1
    nlinarith

lemma link_incidence_lower {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (a : A) (d : ℕ)
    (hrow : d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) :
    d*(d-1) ≤ Nat.card {p : {x : A // x ≠ a} × {b : B // R a b} // link R a p.1 p.2} := by
  classical
  rw [Erdos713ThetaSplit.edge_card_eq_cols]
  have hc (b : {b : B // R a b}) : d-1 ≤ Nat.card {x : {x : A // x ≠ a} // link R a x b} := by
    have hh := link_column_add_one R a b
    have hd := hcols b.val
    omega
  calc
    _ ≤ Nat.card {b // R a b}*(d-1) := Nat.mul_le_mul_right _ hrow
    _ = ∑ _b : {b : B // R a b}, (d-1) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := sum_le_sum (fun b _ => hc b)

open scoped Classical in
/-- This is a same-relation statement. The forbidden condition is explicit
oriented-theta exclusion in every punctured row link. -/
theorem degree_alternative {n d D K : ℕ} (hn : 0 < n)
    (R : Fin n → Fin n → Prop)
    (hFree : ∀ a, ¬ HasTheta (link R a))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hRowMax : ∀ a, Nat.card {b // R a b} ≤ D)
    (hColMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d) :
    d^2 ≤ 2560*(K+1)^2*n ∨ d^9 ≤ 251658240000*K^3*n^3*(singleSet R).card := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨a,ha⟩ := exists_row_with_few_zero_pairs R
  simp only [Fintype.card_fin] at ha
  have hCap (b : {b // R a b}) : Nat.card {x : {x : Fin n // x ≠ a} // link R a x b} ≤ D := by
    have hh := link_column_add_one R a b
    have hh' := hColMax b.val
    omega
  have hm : Fintype.card {x : Fin n // x ≠ a} ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ≠ a)
  have hAlt := zero_sixth_power_alternative (hFree a) n D hn hm hCap
  have hlo := link_incidence_lower R a d (hrows a) hcols
  have hk : Fintype.card {b // R a b} ≤ K*d := by
    simpa only [Nat.card_eq_fintype_card] using (hRowMax a).trans hRatio
  exact ninth_from_zero_alternative hn hlo hRatio hk ha hAlt

#print axioms ninth_from_zero_alternative
#print axioms degree_alternative
end Erdos713ThetaSingletonDegree
