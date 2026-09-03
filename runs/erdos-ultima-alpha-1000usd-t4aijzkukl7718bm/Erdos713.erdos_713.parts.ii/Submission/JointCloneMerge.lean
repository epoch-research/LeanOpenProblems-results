import FormalConjecturesUtil
import Submission.FlatSupportContacts

/-! Full clone saturation and a lower backward extremal increment at the
SAME enlarged host order. -/
open SimpleGraph Finset
namespace Erdos713JointCloneMerge
open Erdos713Cloning Erdos713CloneSaturation Erdos713CloneSymm
open Erdos713ExactCloneSaturation Erdos713FlatSupportContacts
variable {V W : Type*}
set_option maxHeartbeats 2000000

/-- A sufficiently flat quadratic support permits an exactly extremal
clone-saturated host at a uniformly bounded distance in order. -/
theorem exact_saturated_with_backward [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) {n D : ℕ} (hn : 0 < n) (hQD : Fintype.card W ≤ D)
    (G : SimpleGraph (Fin n)) (hopt : OrdinaryOptimal H G)
    (he : Nat.card G.edgeSet = extremalNumber n H) {ε : ℝ} (hε : 0 < ε)
    (hrec : QuadSupport (fun m => extremalNumber m H) ε n)
    (hD : (D : ℝ) ≤ ε*(2*(n : ℝ)-1))
    (hsmall : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2 +
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ) + (2 : ℝ)) < 1) :
    ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      n ≤ Fintype.card U ∧
      Fintype.card U ≤ n+(Fintype.card W+1)*(Fintype.card W)^2 ∧
      H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧ (∀ x, SingleFold H J x) ∧
      ε*(2*(n : ℝ)-1) ≤ (extremalNumber (Fintype.card U) H : ℝ)-
        (extremalNumber (Fintype.card U-1) H : ℝ) := by
  classical
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  have hsmall' : ε*((L : ℝ)^2+L+2) < 1 := by simpa [L] using hsmall
  have htwo : 2*ε < 1 := by
    have hL : 0 ≤ (L : ℝ)^2+(L : ℝ) := by positivity
    nlinarith
  have hdeg (v : Fin n) : D ≤ Nat.card (G.neighborSet v) := by
    exact_mod_cast hD.trans (record_degree H hn G hopt.free he hrec v)
  have hmin (v : Fin n) : Fintype.card W ≤ Nat.card (G.neighborSet v) := (hQD.trans (hdeg v))
  by_cases hs : ∃ v, H.Free (clone G v)
  · obtain ⟨v,hv⟩ := hs
    let d := Nat.card (G.neighborSet v)
    have hdlo : ε*(2*(n : ℝ)-1) ≤ (d : ℝ) := record_degree H hn G hopt.free he hrec v
    have hdhi : (d : ℝ) ≤ ε*(2*(n : ℝ)+1) := record_safe_degree H G he hrec v hv
    have hdmin (w : Fin n) : d ≤ Nat.card (G.neighborSet w) := by
      by_contra hbad
      have hbad' : (Nat.card (G.neighborSet w) : ℝ)+1 ≤ d := by
        exact_mod_cast (show Nat.card (G.neighborSet w)+1 ≤ d by omega)
      have hw := record_degree H hn G hopt.free he hrec w
      nlinarith only [hbad',hw,hdhi,htwo]
    obtain ⟨S,hS,hfree,_,_,hdegree,hfold⟩ := exists_saturated H hH G hopt.free hmin
    have hnS : n ≤ S.card := by simpa using vertex_lower hS
    have hSbound : S.card ≤ n+L := by
      simpa only [Fintype.card_fin] using
        bounded_extra_vertices H hH G hopt.cloneOptimal hopt.free hmin S hS hfree
    let t := S.card-n
    have ht : t ≤ L := by dsimp [t]; omega
    have hnt : S.card = n+t := by dsimp [t]; omega
    have hntR : (S.card : ℝ) = (n : ℝ)+t := by exact_mod_cast hnt
    have htR : (t : ℝ) ≤ L := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have herr : ε*((t : ℝ)^2+t) < 1 := by
      have hsq : (t : ℝ)^2 ≤ (L : ℝ)^2 := by nlinarith
      have hp := mul_le_mul_of_nonneg_left (show (t : ℝ)^2+t ≤ (L : ℝ)^2+L+2 by linarith) hε.le
      exact hp.trans_lt hsmall'
    have hupperR : (extremalNumber S.card H : ℝ) <
        (extremalNumber n H : ℝ)+(d : ℝ)*t+1 := by
      have hr := hrec S.card
      rw [hntR] at hr
      have hm := mul_le_mul_of_nonneg_right hdlo ht0
      nlinarith only [hr,hm,herr]
    have hupper : extremalNumber S.card H ≤ extremalNumber n H+d*t := by
      have hh : extremalNumber S.card H < extremalNumber n H+d*t+1 := by exact_mod_cast hupperR
      omega
    have hlower : extremalNumber n H+d*t ≤ Nat.card (subgraph G (Fintype.card W) S).edgeSet := by
      simpa only [Fintype.card_fin,he] using linear_edges_lower G _ d hdmin S hS
    have hbound : Nat.card (subgraph G (Fintype.card W) S).edgeSet ≤ extremalNumber S.card H := by
      have hh := card_edgeFinset_le_extremalNumber hfree
      simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_eq_finsetCard] using hh
    have hEq : Nat.card (subgraph G (Fintype.card W) S).edgeSet = extremalNumber S.card H :=
      le_antisymm hbound (hupper.trans hlower)
    have hcontact : extremalNumber S.card H = extremalNumber n H+d*(S.card-n) := by
      dsimp only [t] at hupper hlower
      omega
    have hflat : ε*((L : ℝ)^2+L) < 1 := by nlinarith only [hsmall',hε]
    have hback := backward_at_contact (fun m => extremalNumber m H) hn hε.le hrec hdlo hflat
      hnS hSbound hcontact
    refine ⟨S,inferInstance,subgraph G _ S,?_,?_,hfree,?_,?_,hfold,?_⟩
    · simpa using hnS
    · simpa using hSbound
    · simpa using hEq
    · intro x
      exact (hdeg x.val.1).trans (hdegree x)
    · simpa only [Fintype.card_coe] using hback
  · push_neg at hs
    refine ⟨Fin n,inferInstance,G,by simp,by simp,hopt.free,by simpa using he,hdeg,?_,?_⟩
    · intro x
      exact fold_of_obstructed H G x hopt.free (hs x)
    · simpa only [Fintype.card_fin] using support_backward (fun m => extremalNumber m H) hn hrec

#print axioms exact_saturated_with_backward
end Erdos713JointCloneMerge
