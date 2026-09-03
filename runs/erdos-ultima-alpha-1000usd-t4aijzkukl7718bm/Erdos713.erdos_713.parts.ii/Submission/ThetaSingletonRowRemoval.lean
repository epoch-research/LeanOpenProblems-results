import FormalConjecturesUtil
import Submission.ThetaAffineStars

/-! Removing singleton or isolated rows changes only diagonal column
codegrees. The loss in the heavy ordered-pair count is at most |B|. -/
open Finset
open scoped Classical
namespace Erdos713ThetaSingletonRowRemoval
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars
variable {A D B : Type*}
set_option maxHeartbeats 1500000

def restrict (R : A ⊕ D → B → Prop) (a : A) (b : B) : Prop := R (.inl a) b

lemma no_theta {R : A ⊕ D → B → Prop} (hf : ¬ HasTheta R) : ¬ HasTheta (restrict R) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  exact hf ⟨Sum.inl ∘ f,g,Sum.inl_injective.comp hfi,hgi,
    h00,h10,h01,h11,h02,h22,h13,h23⟩

lemma column_le [Fintype A] [Fintype D] (R : A ⊕ D → B → Prop) (b : B) :
    Nat.card {a // restrict R a b} ≤ Nat.card {a // R a b} := by
  let f : {a // restrict R a b} → {a // R a b} := fun a => ⟨.inl a.val,a.property⟩
  apply Nat.card_le_card_of_injective f
  intro a c he
  exact Subtype.ext (Sum.inl.inj (congrArg (fun z : {a // R a b} => z.val) he))

lemma old_of_two {R : A ⊕ D → B → Prop}
    (hs : ∀ d x y, R (.inr d) x → R (.inr d) y → x = y)
    {a : A ⊕ D} {x y : B} (hxy : x ≠ y) (hx : R a x) (hy : R a y) :
    ∃ b : A, a = .inl b := by
  cases a with
  | inl b => exact ⟨b,rfl⟩
  | inr d => exact (hxy (hs d x y hx hy)).elim

noncomputable def pairEquiv (R : A ⊕ D → B → Prop)
    (hs : ∀ d x y, R (.inr d) x → R (.inr d) y → x = y)
    (x y : B) (hxy : x ≠ y) :
    {a // R a x ∧ R a y} ≃ {a // restrict R a x ∧ restrict R a y} where
  toFun a := ⟨(old_of_two hs hxy a.property.1 a.property.2).choose,by
    have he := (old_of_two hs hxy a.property.1 a.property.2).choose_spec
    exact Eq.mp (congrArg (fun z => R z x ∧ R z y) he) a.property⟩
  invFun a := ⟨.inl a.val,a.property⟩
  left_inv a := Subtype.ext (old_of_two hs hxy a.property.1 a.property.2).choose_spec.symm
  right_inv a := by
    apply Subtype.ext
    exact Sum.inl.inj (old_of_two hs hxy
      (show R (.inl a.val) x from a.property.1)
      (show R (.inl a.val) y from a.property.2)).choose_spec.symm

lemma pair_codegree (R : A ⊕ D → B → Prop)
    (hs : ∀ d x y, R (.inr d) x → R (.inr d) y → x = y)
    {x y : B} (hxy : x ≠ y) :
    codegree R x y = codegree (restrict R) x y := Nat.card_congr (pairEquiv R hs x y hxy)

lemma heavy_le_add_columns [Fintype A] [Fintype D] [Fintype B] (R : A ⊕ D → B → Prop)
    (hs : ∀ d x y, R (.inr d) x → R (.inr d) y → x = y) :
    heavyCount R ≤ heavyCount (restrict R)+Nat.card B := by
  let H := {p : B × B // 3 ≤ codegree R p.1 p.2}
  let K := {p : B × B // 3 ≤ codegree (restrict R) p.1 p.2}
  let f : H → K ⊕ B := fun p =>
    if h : p.val.1 ≠ p.val.2 then .inl ⟨p.val,by
      rw [← pair_codegree R hs h]
      exact p.property⟩ else .inr p.val.1
  have hinj : Function.Injective f := by
    intro p q he
    by_cases hp : p.val.1 ≠ p.val.2 <;> by_cases hq : q.val.1 ≠ q.val.2
    · simp only [f,dif_pos hp,dif_pos hq] at he
      exact Subtype.ext (congrArg (fun z : K => z.val) (Sum.inl.inj he))
    · simp only [f,dif_pos hp,dif_neg hq] at he
      cases he
    · simp only [f,dif_neg hp,dif_pos hq] at he
      cases he
    · simp only [f,dif_neg hp,dif_neg hq] at he
      have hh := Sum.inr.inj he
      have hp' : p.val.1 = p.val.2 := not_not.mp hp
      have hq' : q.val.1 = q.val.2 := not_not.mp hq
      exact Subtype.ext (Prod.ext hh (hp'.symm.trans (hh.trans hq')))
  have hc := Nat.card_le_card_of_injective f hinj
  simpa only [H,K,Nat.card_sum,heavyCount] using hc

#print axioms no_theta
#print axioms pair_codegree
#print axioms heavy_le_add_columns
end Erdos713ThetaSingletonRowRemoval
