import FormalConjecturesUtil

/-!
Formal square-sum trades obtained from the 3-4-5 rotation. This file is
infrastructure for realizing prescribed finite residual graphs, not an
asymptotic square-Sidon construction.
-/
namespace Erdos773.QuadraticRotationTrade
open Finset MvPolynomial
set_option maxHeartbeats 2500000
noncomputable section

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

inductive Root (n : ℕ)
  | core : Fin n → Root n
  | plus : Edge n → Root n
  | minus : Edge n → Root n
  deriving DecidableEq, Fintype

def poly {n : ℕ} : Root n → MvPolynomial (Fin n) ℚ
  | .core a => 5*X a
  | .plus e => 3*X e.val.1+4*X e.val.2
  | .minus e => 4*X e.val.1-3*X e.val.2

def value {n : ℕ} (u : Root n) := poly u ^ 2

def atom {n : ℕ} (a : Fin n) : MvPolynomial (Fin n) ℚ := X a ^ 2

def delta {α : Type*} [DecidableEq α] (a b : α) : ℚ := if a=b then 1 else 0

lemma delta_pair {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ∀ x, delta x a+delta x b=delta x c+delta x d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have ha : a=c ∨ a=d := by
    by_contra hn
    push_neg at hn
    have hh := h a
    simp [delta, hn.1, hn.2] at hh
    split_ifs at hh <;> norm_num at hh
  rcases ha with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hb := h b
    simp only [add_left_cancel_iff] at hb
    by_contra hn
    simp [delta, hn] at hb
  · right
    refine ⟨rfl, ?_⟩
    have hb := h b
    have he : delta b b=delta b c := by linarith only [hb]
    by_contra hn
    simp [delta, hn] at he

lemma delta_injective {α : Type*} [DecidableEq α] {a b : α}
    (h : ∀ x, delta x a=delta x b) : a=b := by
  by_contra hn
  have hh := h a
  simp [delta, hn] at hh

lemma delta_difference {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ∀ x, delta x a-delta x b=delta x c-delta x d) :
    (a=c ∧ b=d) ∨ (a=b ∧ c=d) := by
  have hp := delta_pair (a := a) (b := d) (c := c) (d := b)
    (fun x => by linarith only [h x])
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨ha,hb.symm⟩
  · exact Or.inr ⟨ha,hb.symm⟩

def probe {n : ℕ} (e : Edge n) (P : MvPolynomial (Fin n) ℚ) : ℚ :=
  eval (fun x => delta x e.val.1+delta x e.val.2) P-
    eval (fun x => delta x e.val.1) P-eval (fun x => delta x e.val.2) P+eval (fun _ => 0) P

lemma probe_add {n : ℕ} (e : Edge n) (P Q : MvPolynomial (Fin n) ℚ) :
    probe e (P+Q)=probe e P+probe e Q := by
  simp only [probe, map_add]
  ring

@[simp] lemma eval_core {n : ℕ} (x : Fin n → ℚ) (a : Fin n) :
    eval x (value (.core a))=25*x a^2 := by simp [value, poly]; ring
@[simp] lemma eval_plus {n : ℕ} (x : Fin n → ℚ) (e : Edge n) :
    eval x (value (.plus e))=(3*x e.val.1+4*x e.val.2)^2 := by simp [value, poly]
@[simp] lemma eval_minus {n : ℕ} (x : Fin n → ℚ) (e : Edge n) :
    eval x (value (.minus e))=(4*x e.val.1-3*x e.val.2)^2 := by simp [value, poly]

@[simp] lemma probe_core {n : ℕ} (e : Edge n) (a : Fin n) :
    probe e (value (.core a))=0 := by
  simp only [probe, eval_core]
  have hn : a ≠ e.val.1 ∨ a ≠ e.val.2 := by
    by_contra h
    push_neg at h
    exact (ne_of_lt e.property) (h.1.symm.trans h.2)
  rcases hn with h | h <;> simp [delta, h]

lemma edge_swap_impossible {n : ℕ} (e f : Edge n) :
    ¬(e.val.1=f.val.2 ∧ e.val.2=f.val.1) := by
  rintro ⟨h₁,h₂⟩
  have he := e.property
  have hf := f.property
  rw [h₁,h₂] at he
  exact (lt_asymm he hf)

lemma edge_delta {n : ℕ} (e f : Edge n) :
    delta f.val.1 e.val.1*delta f.val.2 e.val.2+
      delta f.val.1 e.val.2*delta f.val.2 e.val.1 = delta e f := by
  have hswap := edge_swap_impossible f e
  by_cases he : e=f
  · subst f
    simp [delta, ne_of_lt e.property, ne_of_gt e.property]
  · have hne : ¬(f.val.1=e.val.1 ∧ f.val.2=e.val.2) := by
      rintro ⟨h₁,h₂⟩
      exact he (Subtype.ext (Prod.ext h₁ h₂)).symm
    simp only [delta]
    split_ifs <;> simp_all

@[simp] lemma probe_plus {n : ℕ} (e f : Edge n) :
    probe e (value (.plus f))=24*delta e f := by
  have h₁ : delta f.val.1 e.val.1*delta f.val.1 e.val.2=0 := by
    simp only [delta]
    split_ifs <;> simp_all [ne_of_lt e.property, ne_of_gt e.property]
  have h₂ : delta f.val.2 e.val.1*delta f.val.2 e.val.2=0 := by
    simp only [delta]
    split_ifs <;> simp_all [ne_of_lt e.property, ne_of_gt e.property]
  simp only [probe, eval_plus]
  nlinarith only [h₁,h₂,edge_delta e f]

@[simp] lemma probe_minus {n : ℕ} (e f : Edge n) :
    probe e (value (.minus f))= -24*delta e f := by
  have h₁ : delta f.val.1 e.val.1*delta f.val.1 e.val.2=0 := by
    simp only [delta]
    split_ifs <;> simp_all [ne_of_lt e.property, ne_of_gt e.property]
  have h₂ : delta f.val.2 e.val.1*delta f.val.2 e.val.2=0 := by
    simp only [delta]
    split_ifs <;> simp_all [ne_of_lt e.property, ne_of_gt e.property]
  simp only [probe, eval_minus]
  nlinarith only [h₁,h₂,edge_delta e f]

lemma atom_pair {n : ℕ} {a b c d : Fin n}
    (h : atom a+atom b=atom c+atom d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  apply delta_pair
  intro x
  have hh := congrArg (eval (fun y => delta x y)) h
  simp only [map_add, atom, map_pow, eval_X] at hh
  have hs (y : Fin n) : delta x y^2=delta x y := by simp only [delta]; split_ifs <;> norm_num
  simpa only [hs] using hh

lemma atom_injective {n : ℕ} {a b : Fin n} (h : atom a=atom b) : a=b := by
  have hp := atom_pair (a := a) (b := a) (c := b) (d := b) (by rw [h])
  tauto

lemma core_pair {n : ℕ} {a b c d : Fin n}
    (h : value (.core a)+value (.core b)=value (.core c)+value (.core d)) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  apply atom_pair
  have hh : (25 : MvPolynomial (Fin n) ℚ)* (atom a+atom b-atom c-atom d)=0 := by
    have ht := sub_eq_zero.mpr h
    convert ht using 1
    dsimp [value, poly, atom]
    ring
  have hz : atom a+atom b-atom c-atom d=0 := (mul_eq_zero.mp hh).resolve_left (by norm_num)
  linear_combination hz

lemma trade {n : ℕ} (e : Edge n) :
    value (.plus e)+value (.minus e)=value (.core e.val.1)+value (.core e.val.2) := by
  dsimp [value, poly]
  ring

#print axioms delta_pair
#print axioms probe_plus
#print axioms probe_minus
#print axioms core_pair
#print axioms trade
end
end Erdos773.QuadraticRotationTrade
