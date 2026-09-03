import FormalConjecturesUtil
import Submission.UniversalRowThetaCounts

/-! Connected apex-theta-free cone hosts can have a distinguished link with
square-scale incidence mass and subquadratically many rows under a column cap.
The light-pair budget is NOT small; these are not almost-regular or extremal hosts. -/

open Finset SimpleGraph
namespace Erdos713ThetaSquareMassCone
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713ThetaThreePoint
open Erdos713UniversalRowTheta Erdos713GlobalTheta Erdos713C6
set_option maxHeartbeats 2000000
variable {A B : Type*}

lemma split_rigid [Fintype A] [Nonempty B] {R : A → B → Prop}
    (hR : Rigid3 R) (d : ℕ) : Rigid3 (split R d) := by
  classical
  let p : SplitColumns R d → B := Sum.elim Sigma.fst (fun _ => Classical.arbitrary B)
  apply rigid_of_projection p ?_ ?_ hR
  · rintro a (⟨b,i⟩ | z) hh
    · exact hh.choose
    · exact hh.elim
  · rintro a (⟨b,i⟩ | z) (⟨c,j⟩ | w) hi hj he
    · change b = c at he
      subst c
      obtain ⟨ha,hi⟩ := hi
      obtain ⟨ha',hj⟩ := hj
      have hij : i = j := Fin.ext (hi.symm.trans hj)
      subst j
      rfl
    · exact hj.elim
    · exact hi.elim
    · exact hi.elim

lemma dummy_light_lower [Fintype A] [Fintype B] (R : A → B → Prop) (d : ℕ) :
    d^2 ≤ Erdos713ThetaCross.lightCount (split R d) := by
  classical
  let f : Fin d × Fin d →
      {p : SplitColumns R d × SplitColumns R d //
        Erdos713GlobalLight.codegree (split R d) p.1 p.2 ≤ 2} :=
    fun p => ⟨(.inr p.1,.inr p.2),by
      haveI : IsEmpty {a : A // split R d a (.inr p.1) ∧ split R d a (.inr p.2)} :=
        ⟨fun a => a.property.1.elim⟩
      simp only [Erdos713GlobalLight.codegree,Nat.card_of_isEmpty,Nat.zero_le]⟩
  have hfi : Function.Injective f := by
    intro p q h
    have he := congrArg Subtype.val h
    exact Prod.ext (Sum.inr.inj (congrArg Prod.fst he))
      (Sum.inr.inj (congrArg Prod.snd he))
  simpa only [Nat.card_prod,Nat.card_fin,pow_two] using
    Nat.card_le_card_of_injective f hfi


/-- The incidence fraction `1/36` is fixed before the row-count target N.
The final strict inequality records an unbounded root/old-row degree ratio. -/
theorem exists_square_mass_link (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      ¬ HasTheta R ∧ Rigid3 R ∧ 0 < Nat.card A ∧ N ≤ r ∧ 0 < r ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      N*Nat.card A < (Nat.card B)^2 ∧
      (Nat.card B)^2 ≤ 36*Nat.card {p : A × B // R p.1 p.2} ∧
      (Nat.card B)^2 ≤ 9*Erdos713ThetaCross.lightCount R ∧
      pattern.Free (bipGraph (extension R)) ∧
      (bipGraph (extension R)).Connected ∧
      (∀ a, ¬ HasTheta (link (extension R) a)) ∧
      (∀ b, ¬ HasTheta (link (fun b a => extension R a b) b)) ∧
      N*r < Nat.card B := by
  classical
  let t := N+2
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hr : 1 ≤ t^2 := by nlinarith
  obtain ⟨A,B,iA,iB,R,hfree,hrigid,hlarge,_hsize,hrow,hedges⟩ :=
    Erdos713ThetaThreePoint.exists_examples (t^2) 1 hr
  simp only [one_mul] at hlarge
  let m := Nat.card A
  have hm : 0 < m := by dsimp [m]; nlinarith only [hlarge]
  letI : Nonempty A := (Nat.card_pos_iff.mp hm).1
  have hrk : t^2 ≤ Nat.card B := by
    obtain ⟨a⟩ := ‹Nonempty A›
    have h := Nat.card_le_card_of_injective (fun b : {b // R a b} => b.val) Subtype.val_injective
    rwa [hrow] at h
  have hkpos : 0 < Nat.card B := by omega
  letI : Nonempty B := (Nat.card_pos_iff.mp hkpos).1
  let s := Nat.sqrt m+1
  let d := t*s
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hd : 0 < d := Nat.mul_pos (by omega) (by omega)
  have hms : m < s^2 := by
    simpa only [s,pow_two,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt m
  have hs4 : s^2 ≤ 4*m := by
    have h1 := Nat.sqrt_le m
    have h2 := Nat.sqrt_le_self m
    dsimp [s]
    nlinarith
  have hks : Nat.card B ≤ s := by
    have h := Nat.le_sqrt.mpr (show Nat.card B*Nat.card B ≤ m by simpa only [pow_two] using hlarge.le)
    dsimp [s]
    omega
  have he : Nat.card {p : A × B // R p.1 p.2} ≤ d^2 := by
    calc
      _ = m*t^2 := hedges
      _ ≤ s^2*t^2 := Nat.mul_le_mul_right _ hms.le
      _ = d^2 := by dsimp [d]; ring
  obtain ⟨hD,hK⟩ := columns_le R hd he
  let S := split R d
  let K := Nat.card (SplitColumns R d)
  have hK' : K ≤ (2*t+1)*s := by
    change K ≤ 2*d+Nat.card B at hK
    dsimp [d] at hK
    nlinarith only [hK,hks]
  have hK3 : K ≤ 3*t*s := by
    have h1 : 2*t+1 ≤ 3*t := by omega
    exact hK'.trans (by nlinarith only [Nat.mul_le_mul_right s h1])
  have hSfree : ¬ HasTheta S := split_no_theta R d hfree
  have hSrigid : Rigid3 S := split_rigid hrigid d
  have hSrows (a : A) : Nat.card {b // S a b} = t^2 :=
    (Erdos713ThetaSplit.row_card R d a).trans (hrow a)
  have hSE : Nat.card {p : A × SplitColumns R d // S p.1 p.2} = m*t^2 := by
    rw [Erdos713ThetaSplit.edge_card,hedges]
  have hlinks := all_links_free hSrigid hSfree
  refine ⟨A,SplitColumns R d,inferInstance,inferInstance,S,t^2,hSfree,hSrigid,hm,
    by dsimp [t]; nlinarith,by omega,hSrows,?_,?_,?_,?_,pattern_free hSrigid hSfree,
    ?_,hlinks.1,hlinks.2,?_⟩
  · exact fun b => (col_card_le R hd b).trans hD
  · have hbig : N < t^2 := by dsimp [t]; nlinarith
    have h1 := Nat.mul_lt_mul_of_pos_right hbig hm
    have h2 := Nat.mul_le_mul_left (t^2) hms.le
    have h3 := Nat.pow_le_pow_left hD 2
    dsimp [d] at h3
    change N*m < K^2
    nlinarith only [h1,h2,h3]
  · rw [hSE]
    have h1 := Nat.pow_le_pow_left hK3 2
    have h2 := Nat.mul_le_mul_left (9*t^2) hs4
    change K^2 ≤ 36*(m*t^2)
    nlinarith only [h1,h2]
  · have hlight := dummy_light_lower R d
    have hsq := Nat.pow_le_pow_left hK3 2
    change K^2 ≤ 9*Erdos713ThetaCross.lightCount S
    dsimp only [d] at hlight
    nlinarith only [hlight,hsq]
  · apply connected
    intro a
    have hpos : 0 < Nat.card {b // S a b} := by rw [hSrows]; omega
    obtain ⟨b⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨b.val,b.property⟩
  · have h1 := hrk.trans hks
    have h2 := Nat.mul_le_mul_left t h1
    have h3 : N*t^2 < t*t^2 := Nat.mul_lt_mul_of_pos_right
      (by dsimp [t]; omega) (by omega)
    change t*s ≤ K at hD
    exact h3.trans_le (h2.trans hD)

/-- The light-pair premise in a square-scale vanishing criterion cannot be
simply omitted, even after imposing genuine connected whole-host realization. -/
theorem no_vanishing_without_light :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
        ¬ HasTheta R → Rigid3 R →
        pattern.Free (bipGraph (extension R)) →
        (bipGraph (extension R)).Connected →
        (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (Nat.card A : ℝ) ≤ δ*(Nat.card B : ℝ)^2 →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤ ε*(Nat.card B : ℝ)^2 := by
  rintro h
  obtain ⟨δ,hδ,hbound⟩ := h (1/72) (by norm_num)
  obtain ⟨N,hN⟩ := exists_nat_gt (1/δ)
  obtain ⟨A,B,iA,iB,R,r,hfree,hrigid,hm,_hr,hpos,_hrows,hcap,hsmall,hmass,_hlight,
      hpattern,hconn,_hleft,_hright,himbalance⟩ := exists_square_mass_link N
  have hmR : (0 : ℝ) < Nat.card A := by exact_mod_cast hm
  have hmult : (1 : ℝ) < δ*N := by
    have hh := (div_lt_iff₀ hδ).mp hN
    nlinarith only [hh]
  have hsR : (N : ℝ)*Nat.card A < (Nat.card B : ℝ)^2 := by exact_mod_cast hsmall
  have hs : (Nat.card A : ℝ) ≤ δ*(Nat.card B : ℝ)^2 := by
    have h1 := mul_lt_mul_of_pos_right hmult hmR
    have h2 := mul_lt_mul_of_pos_left hsR hδ
    nlinarith only [h1,h2]
  have he := hbound A B R hfree hrigid hpattern hconn hcap hs
  have hmR' : (Nat.card B : ℝ)^2 ≤
      36*(Nat.card {p : A × B // R p.1 p.2} : ℝ) := by exact_mod_cast hmass
  have hk : (0 : ℝ) < Nat.card B := by
    exact_mod_cast (show 0 < Nat.card B by omega)
  nlinarith only [he,hmR',sq_pos_of_pos hk]

end Erdos713ThetaSquareMassCone
