import FormalConjecturesUtil
import Submission.ThetaGramPowerSize
import Submission.ThetaBalancedSplit

/-! Preparing the Gram examples with a uniform column-degree bound
comparable to the average degree, while preserving row degrees. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCappedGramPreparation
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaBalancedSplit
variable {A B C : Type*}
set_option maxHeartbeats 2000000

lemma pair_bound_of_projection [Fintype A] (R : A → B → Prop) (S : A → C → Prop)
    (f : C → B) (hmap : ∀ a c, S a c → R a (f c))
    (hinj : ∀ a c d, S a c → S a d → f c = f d → c = d)
    (Q : ℕ) (hQ : ∀ x y, x ≠ y → codegree R x y ≤ Q)
    (x y : C) (hxy : x ≠ y) : codegree S x y ≤ Q := by
  by_cases hproj : f x = f y
  · have hempty : IsEmpty {a // S a x ∧ S a y} := ⟨by
      rintro ⟨a,hax,hay⟩
      exact hxy (hinj a x y hax hay hproj)⟩
    letI := hempty
    simp only [codegree,Nat.card_of_isEmpty,Nat.zero_le]
  · have hle : codegree S x y ≤ codegree R (f x) (f y) := by
      let g : {a // S a x ∧ S a y} → {a // R a (f x) ∧ R a (f y)} :=
        fun a => ⟨a.val,hmap a.val x a.property.1,hmap a.val y a.property.2⟩
      apply Nat.card_le_card_of_injective g
      intro a b he
      exact Subtype.ext (congrArg (fun z : {a // R a (f x) ∧ R a (f y)} => z.val) he)
    exact hle.trans (hQ _ _ hproj)

lemma core_pair_bound [Fintype A] (R : A → B → Prop) (d Q : ℕ)
    (hQ : ∀ x y, x ≠ y → codegree R x y ≤ Q)
    (x y : CoreColumns R d) (hxy : x ≠ y) :
    codegree (coreSplit R d) x y ≤ Q := by
  apply pair_bound_of_projection R (coreSplit R d) Sigma.fst
    (fun _ _ h => h.choose) ?_ Q hQ x y hxy
  intro a c e hc he hce
  have hh : (coreRowEquiv R d a).symm ⟨c,hc⟩ =
      (coreRowEquiv R d a).symm ⟨e,he⟩ := Subtype.ext hce
  exact congrArg Subtype.val ((coreRowEquiv R d a).symm.injective hh)

lemma columns_pos_of_row_degree [Fintype A] [Fintype B] (R : A → B → Prop)
    (hm : 0 < Nat.card A) (r : ℕ) (hr : 0 < r)
    (hrow : ∀ a, Nat.card {b // R a b} = r) : 0 < Nat.card B := by
  haveI : Nonempty A := Fintype.card_pos_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hm)
  let a : A := Classical.choice inferInstance
  have hc : r ≤ Nat.card B := by
    rw [← hrow a]
    exact Nat.card_le_card_of_injective (fun b : {b // R a b} => b.val) Subtype.val_injective
  exact hr.trans_le hc

/-- The maximum degree times the number of columns is at most four
 times the original incidence count. -/
theorem exists_examples (r : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (Q D : ℕ),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ 0 < Nat.card B ∧ 0 < D ∧
      (Nat.card B)^2 ≤ 4*Nat.card A ∧
      Nat.card A ≤ Erdos713ThetaGramPowerSize.scale^75*r^7650 ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} ≤ D) ∧ D*Nat.card B ≤ 4*(Nat.card A*r) ∧
      (∀ x y, x ≠ y → codegree R x y ≤ Q) ∧
      ∀ T : ℕ, T^2 ≤ Q → (Nat.card B*T)^3 ≤ 8*(Nat.card A)^2 := by
  classical
  obtain ⟨A,B,iA,iB,R,Q,hfree,hkm,hsize,hrows,hQ,hshape⟩ :=
    Erdos713ThetaGramPowerSize.exists_examples r hr
  have hm : 0 < Nat.card A := lt_of_le_of_lt (Nat.zero_le _) hkm
  have hk : 0 < Nat.card B := columns_pos_of_row_degree R hm r hr hrows
  let E := Nat.card A*r
  let D := E/Nat.card B+1
  obtain ⟨hD,hED,hDE⟩ := balanced_cap (e := E) hk
  have hE : Nat.card {p : A × B // R p.1 p.2} = E := by
    rw [Erdos713ThetaSplit.edge_card_eq_rows]
    simp only [hrows,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.card_eq_fintype_card,E]
  have hK : Nat.card (CoreColumns R D) ≤ 2*Nat.card B :=
    core_columns_le R hD (hE ▸ hED)
  have hmE : Nat.card A ≤ E := Nat.le_mul_of_pos_right _ hr
  have hkE : Nat.card B ≤ E := by
    calc
      _ ≤ (Nat.card B)^2 := by simpa only [pow_two] using Nat.le_mul_self (Nat.card B)
      _ ≤ Nat.card A := hkm.le
      _ ≤ E := hmE
  have hrows' (a : A) : Nat.card {b // coreSplit R D a b} = r :=
    (core_row_card R D a).trans (hrows a)
  refine ⟨A,CoreColumns R D,inferInstance,inferInstance,coreSplit R D,Q,D,
    core_no_theta R D hfree,hm,columns_pos_of_row_degree _ hm r hr hrows',hD,
    ?_,hsize,hrows',core_column_le R hD,?_,core_pair_bound R D Q hQ,?_⟩
  · calc
      _ ≤ (2*Nat.card B)^2 := Nat.pow_le_pow_left hK 2
      _ ≤ 4*Nat.card A := by nlinarith only [hkm.le]
  · have hh := Nat.mul_le_mul_left D hK
    change D*Nat.card B ≤ E+Nat.card B at hDE
    change D*Nat.card (CoreColumns R D) ≤ 4*E
    nlinarith only [hh,hDE,hkE]
  · intro T hT
    have hh := Nat.pow_le_pow_left (Nat.mul_le_mul_right T hK) 3
    have hs := hshape T hT
    calc
      _ ≤ (2*Nat.card B*T)^3 := hh
      _ = 8*(Nat.card B*T)^3 := by ring
      _ ≤ 8*(Nat.card A)^2 := Nat.mul_le_mul_left 8 hs

#print axioms pair_bound_of_projection
#print axioms exists_examples
end Erdos713ThetaCappedGramPreparation
