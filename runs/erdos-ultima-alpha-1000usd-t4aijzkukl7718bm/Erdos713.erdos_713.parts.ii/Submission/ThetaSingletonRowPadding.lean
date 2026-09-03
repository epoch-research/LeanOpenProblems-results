import FormalConjecturesUtil
import Submission.ThetaGram
import Submission.GlobalLightPairs

/-! Singleton rows can equalize all column degrees without changing
any distinct-column codegree or introducing an oriented theta. -/
open Finset
open scoped Classical
namespace Erdos713ThetaSingletonRowPadding
open Erdos713ThetaGram Erdos713GlobalLight
variable {A B : Type*}
set_option maxHeartbeats 1500000

abbrev Rows (A B : Type*) (D : ℕ) := A ⊕ (B × Fin D)

def Inc (R : A → B → Prop) (D : ℕ) : Rows A B D → B → Prop
  | .inl a, b => R a b
  | .inr p, b => p.1 = b ∧ p.2.val < D-Nat.card {a // R a b}

lemma old_of_two {R : A → B → Prop} {D : ℕ} {a : Rows A B D} {x y : B}
    (hxy : x ≠ y) (hx : Inc R D a x) (hy : Inc R D a y) :
    ∃ b : A, a = .inl b := by
  cases a with
  | inl b => exact ⟨b,rfl⟩
  | inr p => exact (hxy (hx.1.symm.trans hy.1)).elim

lemma no_theta {R : A → B → Prop} (hR : ¬ HasTheta R) (D : ℕ) : ¬ HasTheta (Inc R D) := by
  rintro ⟨f,g,hf,hg,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have ho : ∀ i : Fin 3, ∃ a : A, f i = .inl a := by
    intro i
    fin_cases i
    · exact old_of_two (hg.ne (by decide : (0 : Fin 4) ≠ 1)) h00 h01
    · exact old_of_two (hg.ne (by decide : (0 : Fin 4) ≠ 1)) h10 h11
    · exact old_of_two (hg.ne (by decide : (2 : Fin 4) ≠ 3)) h22 h23
  choose f' hf' using ho
  have hfi : Function.Injective f' := by
    intro i j he
    apply hf
    rw [hf' i,hf' j,he]
  apply hR
  refine ⟨f',g,hfi,hg,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | simpa only [hf',Inc] using h00
    | simpa only [hf',Inc] using h10
    | simpa only [hf',Inc] using h01
    | simpa only [hf',Inc] using h11
    | simpa only [hf',Inc] using h02
    | simpa only [hf',Inc] using h22
    | simpa only [hf',Inc] using h13
    | simpa only [hf',Inc] using h23

noncomputable def columnEquiv (R : A → B → Prop) (D : ℕ) (b : B) :
    {a // Inc R D a b} ≃ ({a // R a b} ⊕ Fin (D-Nat.card {a // R a b})) where
  toFun a := match a with
    | ⟨.inl a,h⟩ => .inl ⟨a,h⟩
    | ⟨.inr p,h⟩ => .inr ⟨p.2.val,h.2⟩
  invFun a := match a with
    | .inl a => ⟨.inl a.val,a.property⟩
    | .inr i => ⟨.inr (b,⟨i.val,lt_of_lt_of_le i.isLt (Nat.sub_le _ _)⟩),rfl,i.isLt⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl a => rfl
    | inr p =>
      apply Subtype.ext
      apply congrArg Sum.inr
      exact Prod.ext ha.1.symm rfl
  right_inv a := by cases a <;> rfl

lemma column_card [Fintype A] (R : A → B → Prop) (D : ℕ) (b : B)
    (hD : Nat.card {a // R a b} ≤ D) : Nat.card {a // Inc R D a b} = D := by
  rw [Nat.card_congr (columnEquiv R D b),Nat.card_sum,Nat.card_fin]
  exact Nat.add_sub_of_le hD

lemma rows_card [Fintype A] [Fintype B] (D : ℕ) :
    Nat.card (Rows A B D) = Nat.card A+Nat.card B*D := by
  simp only [Rows,Nat.card_sum,Nat.card_prod,Nat.card_fin]

noncomputable def pairEquiv (R : A → B → Prop) (D : ℕ) (x y : B) (hxy : x ≠ y) :
    {a // Inc R D a x ∧ Inc R D a y} ≃ {a // R a x ∧ R a y} where
  toFun a := ⟨(old_of_two hxy a.property.1 a.property.2).choose,by
    have he := (old_of_two hxy a.property.1 a.property.2).choose_spec
    exact Eq.mp (congrArg (fun z => Inc R D z x ∧ Inc R D z y) he) a.property⟩
  invFun a := ⟨.inl a.val,a.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (old_of_two hxy a.property.1 a.property.2).choose_spec.symm
  right_inv a := by
    apply Subtype.ext
    exact Sum.inl.inj (old_of_two hxy (show Inc R D (.inl a.val) x from a.property.1)
      (show Inc R D (.inl a.val) y from a.property.2)).choose_spec.symm

lemma pair_codegree (R : A → B → Prop) (D : ℕ) {x y : B} (hxy : x ≠ y) :
    codegree (Inc R D) x y = codegree R x y := Nat.card_congr (pairEquiv R D x y hxy)

#print axioms no_theta
#print axioms column_card
#print axioms pair_codegree
end Erdos713ThetaSingletonRowPadding
