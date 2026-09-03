import FormalConjecturesUtil
import Submission.ThetaGramCount

/-! Column splitting preserves the oriented theta obstruction. This is a
diagnostic for an auxiliary estimate, not a counterexample to Erdos 713. -/
open Finset
namespace Erdos713ThetaSplit
open Erdos713ThetaGram
variable {A B : Type*}

/-- Every two theta columns meet a common row, so splitting a column into
pieces with disjoint row-neighbourhoods cannot create this oriented theta. -/
lemma theta_of_projection {D : Type*} {R : A → B → Prop} {T : A → D → Prop}
    (p : D → B) (hp : ∀ a b, T a b → R a (p b))
    (hf : ∀ a b c, T a b → T a c → p b = p c → b = c)
    (h : HasTheta T) : HasTheta R := by
  obtain ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩ := h
  have hpair (i j : Fin 4) : ∃ k : Fin 3, T (a k) (b i) ∧ T (a k) (b j) := by
    fin_cases i <;> fin_cases j <;> first
      | exact ⟨0,by assumption,by assumption⟩
      | exact ⟨1,by assumption,by assumption⟩
      | exact ⟨2,by assumption,by assumption⟩
  refine ⟨a,p ∘ b,ha,?_,hp _ _ h00,hp _ _ h10,hp _ _ h01,hp _ _ h11,
    hp _ _ h02,hp _ _ h22,hp _ _ h13,hp _ _ h23⟩
  intro i j hij
  obtain ⟨k,hki,hkj⟩ := hpair i j
  exact hb (hf (a k) (b i) (b j) hki hkj hij)

noncomputable def rank [Fintype A] (R : A → B → Prop) (b : B) :
    {a // R a b} ≃ Fin (Nat.card {a // R a b}) := Finite.equivFin _

abbrev SplitColumns (R : A → B → Prop) (d : ℕ) :=
  (Σ b : B, Fin (Nat.card {a // R a b}/d+1)) ⊕ Fin d

noncomputable def split [Fintype A] (R : A → B → Prop) (d : ℕ) :
    A → SplitColumns R d → Prop
  | a,Sum.inl ⟨b,i⟩ => ∃ h : R a b, (rank R b ⟨a,h⟩).val/d = i.val
  | _,Sum.inr _ => False

lemma split_no_theta [Fintype A] [Nonempty B] (R : A → B → Prop) (d : ℕ)
    (h : ¬ HasTheta R) : ¬ HasTheta (split R d) := by
  classical
  let p : SplitColumns R d → B := Sum.elim Sigma.fst (fun _ => Classical.arbitrary B)
  apply mt (theta_of_projection p ?_ ?_) h
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

noncomputable def rowEquiv [Fintype A] (R : A → B → Prop) (d : ℕ) (a : A) :
    {b // R a b} ≃ {c // split R d a c} where
  toFun b := ⟨Sum.inl ⟨b.val,⟨(rank R b.val ⟨a,b.property⟩).val/d,
    Nat.lt_succ_of_le (Nat.div_le_div_right (rank R b.val ⟨a,b.property⟩).isLt.le)⟩⟩,
    b.property,rfl⟩
  invFun c := by
    rcases c with ⟨⟨b,i⟩ | z,hc⟩
    · exact ⟨b,hc.choose⟩
    · exact hc.elim
  left_inv b := rfl
  right_inv c := by
    rcases c with ⟨⟨b,i⟩ | z,hc⟩
    · apply Subtype.ext
      change (Sum.inl ⟨b,⟨(rank R b ⟨a,hc.choose⟩).val/d,_⟩⟩ : SplitColumns R d) =
        Sum.inl ⟨b,i⟩
      exact congrArg Sum.inl (congrArg (Sigma.mk b) (Fin.ext hc.choose_spec))
    · exact hc.elim

lemma row_card [Fintype A] (R : A → B → Prop) (d : ℕ) (a : A) :
    Nat.card {c // split R d a c} = Nat.card {b // R a b} :=
  (Nat.card_congr (rowEquiv R d a)).symm

lemma col_card_le [Fintype A] (R : A → B → Prop) {d : ℕ} (hd : 0 < d)
    (c : SplitColumns R d) : Nat.card {a // split R d a c} ≤ d := by
  classical
  cases c with
  | inr z => simp [split]
  | inl c =>
    rcases c with ⟨b,i⟩
    let f : {a // split R d a (Sum.inl ⟨b,i⟩)} → Fin d := fun a =>
      ⟨(rank R b ⟨a.val,a.property.choose⟩).val % d, Nat.mod_lt _ hd⟩
    have hf : Function.Injective f := by
      intro a a' he
      apply Subtype.ext
      change a.val = a'.val
      have hm := congrArg Fin.val he
      have hdiv := a.property.choose_spec
      have hdiv' := a'.property.choose_spec
      change (rank R b ⟨a.val,a.property.choose⟩).val/d = i.val at hdiv
      change (rank R b ⟨a'.val,a'.property.choose⟩).val/d = i.val at hdiv'
      have h1 := Nat.div_add_mod (rank R b ⟨a.val,a.property.choose⟩).val d
      have h2 := Nat.div_add_mod (rank R b ⟨a'.val,a'.property.choose⟩).val d
      have hEq : rank R b ⟨a.val,a.property.choose⟩ = rank R b ⟨a'.val,a'.property.choose⟩ := by
        apply Fin.ext
        change (rank R b ⟨a.val,a.property.choose⟩).val % d =
          (rank R b ⟨a'.val,a'.property.choose⟩).val % d at hm
        rw [hdiv] at h1
        rw [hdiv'] at h2
        omega
      exact congrArg (fun z : {a // R a b} => z.val) ((rank R b).injective hEq)
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

lemma edge_card_eq_rows [Fintype A] [Fintype B] (R : A → B → Prop) :
    Nat.card {p : A × B // R p.1 p.2} = ∑ a, Nat.card {b // R a b} := by
  classical
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype R),Nat.card_sigma]

lemma edge_card_eq_cols [Fintype A] [Fintype B] (R : A → B → Prop) :
    Nat.card {p : A × B // R p.1 p.2} = ∑ b, Nat.card {a // R a b} := by
  classical
  let e : {p : A × B // R p.1 p.2} ≃ {p : B × A // R p.2 p.1} :=
    ⟨fun p => ⟨p.val.swap,p.property⟩,fun p => ⟨p.val.swap,p.property⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Nat.card_congr e]
  exact edge_card_eq_rows (fun b a => R a b)

lemma edge_card [Fintype A] [Fintype B] (R : A → B → Prop) (d : ℕ) :
    Nat.card {p : A × SplitColumns R d // split R d p.1 p.2} =
      Nat.card {p : A × B // R p.1 p.2} := by
  classical
  simp only [edge_card_eq_rows,row_card]

lemma columns_le [Fintype A] [Fintype B] (R : A → B → Prop) {d : ℕ} (hd : 0 < d)
    (he : Nat.card {p : A × B // R p.1 p.2} ≤ d^2) :
    d ≤ Nat.card (SplitColumns R d) ∧ Nat.card (SplitColumns R d) ≤ 2*d+Nat.card B := by
  classical
  have hc : Nat.card (SplitColumns R d) =
      (∑ b, Nat.card {a // R a b}/d)+Nat.card B+d := by
    simp [SplitColumns,sum_add_distrib,Nat.card_eq_fintype_card]
  have hs : d*(∑ b, Nat.card {a // R a b}/d) ≤ d*d := by
    calc
      _ = ∑ b, d*(Nat.card {a // R a b}/d) := by rw [mul_sum]
      _ ≤ ∑ b, Nat.card {a // R a b} := sum_le_sum (fun b _ => Nat.mul_div_le _ _)
      _ ≤ d*d := by simpa only [← edge_card_eq_cols,pow_two] using he
  have hsd : (∑ b, Nat.card {a // R a b}/d) ≤ d := Nat.le_of_mul_le_mul_left hs hd
  omega

#print axioms theta_of_projection
#print axioms split_no_theta
#print axioms col_card_le
#print axioms edge_card
#print axioms columns_le
end Erdos713ThetaSplit
