import FormalConjecturesUtil

/-! A whole-host consistency constraint: light column pairs occur in only
boundedly many row neighbourhoods. This is not an extremal exponent bound. -/
open Finset
namespace Erdos713GlobalLight

noncomputable def codegree {A B : Type*} (R : A → B → Prop) (x y : B) : ℕ :=
  Nat.card {a // R a x ∧ R a y}

noncomputable def lightPairs {A B : Type*} [Fintype B]
    (R : A → B → Prop) (k : ℕ) (a : A) : Finset (B × B) := by
  classical
  exact univ.filter (fun p => R a p.1 ∧ R a p.2 ∧ codegree R p.1 p.2 ≤ k)

lemma sum_lightPairs_le {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (k : ℕ) :
    (∑ a, (lightPairs R k a).card) ≤ k*(Fintype.card B)^2 := by
  classical
  let r : A → B × B → Prop := fun a p => R a p.1 ∧ R a p.2 ∧ codegree R p.1 p.2 ≤ k
  have hb (p : B × B) : ((univ : Finset A).bipartiteBelow r p).card ≤ k := by
    by_cases hc : codegree R p.1 p.2 ≤ k
    · have he : ((univ : Finset A).bipartiteBelow r p).card = codegree R p.1 p.2 := by
        simp only [r,bipartiteBelow,hc,and_true]
        simp [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
      rwa [he]
    · simp [r,bipartiteBelow,hc]
  calc
    (∑ a, (lightPairs R k a).card) =
        ∑ a, ((univ : Finset (B × B)).bipartiteAbove r a).card := rfl
    _ = ∑ p, ((univ : Finset A).bipartiteBelow r p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r (s := univ) (t := univ)
    _ ≤ ∑ _p : B × B, k := sum_le_sum (fun p _ => hb p)
    _ = k*(Fintype.card B)^2 := by simp [Fintype.card_prod,pow_two,Nat.mul_comm]

lemma exists_row_with_few_light_pairs {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (k : ℕ) :
    ∃ a : A, Fintype.card A*(lightPairs R k a).card ≤ k*(Fintype.card B)^2 := by
  classical
  obtain ⟨a,_,ha⟩ := (univ : Finset A).exists_min_image (fun a => (lightPairs R k a).card)
    (univ_nonempty)
  refine ⟨a,?_⟩
  calc
    Fintype.card A*(lightPairs R k a).card = ∑ _b : A, (lightPairs R k a).card := by simp
    _ ≤ ∑ b : A, (lightPairs R k b).card := sum_le_sum (fun b _ => ha b (mem_univ _))
    _ ≤ _ := sum_lightPairs_le R k

lemma pairs_in_row {A B : Type*} [Fintype B] (R : A → B → Prop) (a : A) :
    Nat.card {p : B × B // R a p.1 ∧ R a p.2} = (Nat.card {b // R a b})^2 := by
  classical
  let e : {p : B × B // R a p.1 ∧ R a p.2} ≃ ({b // R a b} × {b // R a b}) :=
    { toFun := fun p => (⟨p.val.1,p.prop.1⟩,⟨p.val.2,p.prop.2⟩)
      invFun := fun p => ⟨(p.1.val,p.2.val),p.1.prop,p.2.prop⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e,Nat.card_prod,pow_two]

#print axioms sum_lightPairs_le
#print axioms exists_row_with_few_light_pairs
#print axioms pairs_in_row
end Erdos713GlobalLight
