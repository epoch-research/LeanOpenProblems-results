import FormalConjecturesUtil
import Submission.GlobalThetaLinks
import Submission.ThetaCrossCompletion

/-! A conditional reduction, not an asserted local theta estimate.
The capped weighted hypothesis below remains unproved. -/
open Finset SimpleGraph
namespace Erdos713ConditionalThetaWeighted
open Erdos713GlobalLight Erdos713GlobalTheta Erdos713ThetaGram
open Erdos713ThetaCross Erdos713ThetaSplit
set_option maxHeartbeats 2000000

lemma card_restrict_ne_add_one {A : Type*} [Fintype A]
    (P : A → Prop) (d : A) (hd : P d) :
    Nat.card {a : {a : A // a ≠ d} // P a.val}+1 = Nat.card {a : A // P a} := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) P)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : (univ.filter (fun a => a ≠ d ∧ P a)) = (univ.filter P).erase d := by
    ext a
    simp [and_comm]
  rw [he]
  exact card_erase_add_one (by simp [hd])

lemma link_codegree_add_one {A B : Type*} [Fintype A]
    (R : A → B → Prop) (d : A) (x y : {b : B // R d b}) :
    codegree (link R d) x y+1 = codegree R x.val y.val :=
  card_restrict_ne_add_one (fun a => R a x.val ∧ R a y.val) d ⟨x.property,y.property⟩

lemma link_column_add_one {A B : Type*} [Fintype A]
    (R : A → B → Prop) (d : A) (x : {b : B // R d b}) :
    Nat.card {a : {a : A // a ≠ d} // link R d a x}+1 = Nat.card {a : A // R a x.val} :=
  card_restrict_ne_add_one (fun a => R a x.val) d x.property

open scoped Classical in
lemma link_lightCount {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (d : A) :
    lightCount (link R d) = (lightPairs R 3 d).card := by
  classical
  let e : {p : {b : B // R d b} × {b : B // R d b} // codegree (link R d) p.1 p.2 ≤ 2} ≃
      ↥(lightPairs R 3 d) :=
    { toFun := fun p => ⟨(p.val.1.val,p.val.2.val),by
        have hc := link_codegree_add_one R d p.val.1 p.val.2
        have hp := p.property
        simp only [lightPairs,mem_filter,mem_univ,true_and]
        exact ⟨p.val.1.property,p.val.2.property,by omega⟩⟩
      invFun := fun p => by
        have hp := p.property
        simp only [lightPairs,mem_filter,mem_univ,true_and] at hp
        let x : {b : B // R d b} := ⟨p.val.1,hp.1⟩
        let y : {b : B // R d b} := ⟨p.val.2,hp.2.1⟩
        exact ⟨(x,y),by
          change codegree (link R d) x y ≤ 2
          have hc := link_codegree_add_one R d x y
          have hp' : codegree R x.val y.val ≤ 3 := hp.2.2
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

lemma link_incidence_lower {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (a : A) (d : ℕ)
    (hrow : d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) :
    d*(d-1) ≤ Nat.card {p : {x : A // x ≠ a} × {b : B // R a b} // link R a p.1 p.2} := by
  classical
  rw [edge_card_eq_cols]
  have hc (b : {b : B // R a b}) : d-1 ≤ Nat.card {x : {x : A // x ≠ a} // link R a x b} := by
    have hh := link_column_add_one R a b
    have hd := hcols b.val
    omega
  calc
    _ ≤ Nat.card {b // R a b}*(d-1) := Nat.mul_le_mul_right _ hrow
    _ = ∑ _b : {b : B // R a b}, (d-1) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := sum_le_sum (fun b _ => hc b)

/-- This is a hypothesis, not a theorem asserted for theta-free relations. -/
def CappedWeighted (K C : ℝ) : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop) (D : ℕ),
    ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ D) →
    (D : ℝ) ≤ K*Nat.card B →
    (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
      C*((Nat.card A : ℝ)+(D : ℝ)*Real.sqrt (lightCount R))

/-- A balanced, globally pattern-free host yields the claimed quadratic
inequality IF the capped weighted estimate is supplied. The same host
supplies both the theta exclusion and the light-pair budget. -/
lemma degree_inequality {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hBound : CappedWeighted K C) {n d D : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (R : Fin n → Fin n → Prop) (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : (D : ℝ) ≤ K*d) :
    (d : ℝ)*((d : ℝ)-1) ≤ C*((n : ℝ)+(D : ℝ)*Real.sqrt (3*(n : ℝ))) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨a,ha⟩ := exists_row_with_few_light_pairs R 3
  simp only [Fintype.card_fin] at ha
  have ht : (lightPairs R 3 a).card ≤ 3*n := by
    have ht' : n*(lightPairs R 3 a).card ≤ n*(3*n) := by nlinarith only [ha]
    exact Nat.le_of_mul_le_mul_left ht' hn
  have htR : (lightCount (link R a) : ℝ) ≤ 3*(n : ℝ) := by
    rw [link_lightCount]
    exact_mod_cast ht
  have hCap (b : {b // R a b}) : Nat.card {x : {x : Fin n // x ≠ a} // link R a x b} ≤ D := by
    have hh := link_column_add_one R a b
    have hh' := hMax b.val
    omega
  have hRatio' : (D : ℝ) ≤ K*Nat.card {b // R a b} := hRatio.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hrows a) hK)
  have hb := hBound {x : Fin n // x ≠ a} {b : Fin n // R a b} (link R a) D
    (no_theta_links hFree a) hCap hRatio'
  have hm : Nat.card {x : Fin n // x ≠ a} ≤ n := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      (fun x : {x : Fin n // x ≠ a} => x.val) Subtype.val_injective
  have hlo := link_incidence_lower R a d (hrows a) hcols
  have hloR : (d : ℝ)*((d : ℝ)-1) ≤
      (Nat.card {p : {x : Fin n // x ≠ a} × {b : Fin n // R a b} // link R a p.1 p.2} : ℝ) := by
    exact_mod_cast hlo
  apply hloR.trans (hb.trans _)
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add (by exact_mod_cast hm)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htR) (Nat.cast_nonneg _))

lemma quadratic_sqrt_bound {K C n d : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hn : 1 ≤ n) (hd : 0 ≤ d)
    (h : d*(d-1) ≤ C*(n+K*d*Real.sqrt (3*n))) :
    d ≤ (C*K+C+2)*Real.sqrt (3*n) := by
  let s := Real.sqrt (3*n)
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s^2 = 3*n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    have hh : Real.sqrt (1 : ℝ) ≤ Real.sqrt (3*n) := Real.sqrt_le_sqrt (by linarith)
    simpa only [Real.sqrt_one] using hh
  have hCK : 0 ≤ C*K := mul_nonneg hC hK
  by_contra hh
  have hbad : (C*K+C+2)*s < d := lt_of_not_ge hh
  have h1 : (C+1)*s < d := by nlinarith [mul_pos (show 0 < C*K+1 by positivity) hspos]
  have h2 : (C+1)*s < d-(C*K+1)*s := by nlinarith only [hbad]
  have hbs : 0 < (C+1)*s := mul_pos (by positivity) hspos
  have hdpos : 0 < d := hbs.trans h1
  have hprod : ((C+1)*s)^2 < d*(d-(C*K+1)*s) := by
    calc
      _ = ((C+1)*s)*((C+1)*s) := sq _
      _ < d*((C+1)*s) := mul_lt_mul_of_pos_right h1 hbs
      _ < d*(d-(C*K+1)*s) := mul_lt_mul_of_pos_left h2 hdpos
  have hlower : C*n ≤ ((C+1)*s)^2 := by
    calc
      _ ≤ C*(3*n) := mul_le_mul_of_nonneg_left (by linarith) hC
      _ ≤ (C+1)^2*(3*n) := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (by linarith)
      _ = ((C+1)*s)^2 := by rw [← hs2]; ring
  have hupper : d*(d-(C*K+1)*s) ≤ C*n := by
    change d*(d-1) ≤ C*(n+K*d*s) at h
    have hds := mul_nonneg hd (sub_nonneg.mpr hs1)
    nlinarith only [h,hds]
  exact (not_lt_of_ge (hupper.trans hlower)) hprod

/-- The unproved capped estimate would force the square-root degree scale
in every balanced almost-regular globally pattern-free host. -/
lemma degree_le_sqrt {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hBound : CappedWeighted K C) {n d D : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (R : Fin n → Fin n → Prop) (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : (D : ℝ) ≤ K*d) :
    (d : ℝ) ≤ (C*K+C+2)*Real.sqrt (3*(n : ℝ)) := by
  apply quadratic_sqrt_bound hK hC (by exact_mod_cast hn) (Nat.cast_nonneg _) 
  apply (degree_inequality hK hC hBound hn hd R hFree hrows hcols hMax hRatio).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hRatio (Real.sqrt_nonneg _))

#print axioms card_restrict_ne_add_one
#print axioms link_codegree_add_one
#print axioms link_lightCount
#print axioms link_incidence_lower
#print axioms degree_inequality
#print axioms quadratic_sqrt_bound
#print axioms degree_le_sqrt
end Erdos713ConditionalThetaWeighted
