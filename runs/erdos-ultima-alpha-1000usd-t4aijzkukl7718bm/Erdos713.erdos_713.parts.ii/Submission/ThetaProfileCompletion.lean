import FormalConjecturesUtil
import Submission.ThetaGram

/-! A separated-profile completion lemma for oriented theta-free relations.
This is an auxiliary construction, not a proof of Erdos 713. -/
namespace Erdos713ThetaProfile
open Erdos713ThetaGram

variable {I A B P C T : Type*}

/-- Old rows stay in one block; new rows belong to a profile. -/
def assemble (R : A → B → Prop) (Q : P → C → I × B → Prop) :
    (I × A) ⊕ (P × C) → I × B → Prop
  | .inl a, b => a.1 = b.1 ∧ R a.2 b.2
  | .inr a, b => Q a.1 a.2 b

/-- A row is a transversal of the fibres of `f`. -/
def Transversal {X Y Z : Type*} (R : X → Y → Prop) (f : Y → Z) : Prop :=
  ∀ a x y, R a x → R a y → f x = f y → x = y

/-- Two different profiles agree at at most one block. -/
def Separated (s : P → I → T) : Prop :=
  ∀ p q i j, i ≠ j → s p i = s q i → s p j = s q j → p = q

lemma profile_eq_of_common_pair {Q : P → C → I × B → Prop} {s : P → I → T}
    {τ : B → T} (hsep : Separated s)
    (htrans : ∀ p, Transversal (Q p) Prod.fst)
    (htype : ∀ p a b, Q p a b → τ b.2 = s p b.1)
    {p q : P} {a b : C} {x y : I × B} (hxy : x ≠ y)
    (hax : Q p a x) (hay : Q p a y) (hbx : Q q b x) (hby : Q q b y) : p = q := by
  apply hsep p q x.1 y.1
  · intro he
    exact hxy (htrans p a x y hax hay he)
  · exact (htype p a x hax).symm.trans (htype q b x hbx)
  · exact (htype p a y hay).symm.trans (htype q b y hby)

/-- Every theta in this completion already occurs in an old relation or
in one profile relation. Mixed occurrences are excluded explicitly. -/
theorem no_theta_assemble {R : A → B → Prop} {Q : P → C → I × B → Prop}
    {s : P → I → T} {τ : B → T}
    (hR : ¬ HasTheta R) (hQ : ∀ p, ¬ HasTheta (Q p))
    (hRtrans : Transversal R τ) (hsep : Separated s)
    (hQtrans : ∀ p, Transversal (Q p) Prod.fst)
    (htype : ∀ p a b, Q p a b → τ b.2 = s p b.1) :
    ¬ HasTheta (assemble R Q) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hne (i j : Fin 4) (hij : i ≠ j) : g i ≠ g j := fun h => hij (hgi h)
  cases hfa : f 0 with
  | inl a =>
    rw [hfa] at h00 h01 h02
    change a.1 = (g 0).1 ∧ R a.2 (g 0).2 at h00
    change a.1 = (g 1).1 ∧ R a.2 (g 1).2 at h01
    change a.1 = (g 2).1 ∧ R a.2 (g 2).2 at h02
    cases hfb : f 1 with
    | inr b =>
      rw [hfb] at h10 h11
      exact hne 0 1 (by decide)
        (hQtrans b.1 b.2 (g 0) (g 1) h10 h11 (h00.1.symm.trans h01.1))
    | inl b =>
      rw [hfb] at h10 h11 h13
      change b.1 = (g 0).1 ∧ R b.2 (g 0).2 at h10
      change b.1 = (g 1).1 ∧ R b.2 (g 1).2 at h11
      change b.1 = (g 3).1 ∧ R b.2 (g 3).2 at h13
      have hab : a.1 = b.1 := h00.1.trans h10.1.symm
      have hi23 : (g 2).1 = (g 3).1 := h02.1.symm.trans (hab.trans h13.1)
      cases hfc : f 2 with
      | inr c =>
        rw [hfc] at h22 h23
        exact hne 2 3 (by decide) (hQtrans c.1 c.2 (g 2) (g 3) h22 h23 hi23)
      | inl c =>
        rw [hfc] at h22 h23
        change c.1 = (g 2).1 ∧ R c.2 (g 2).2 at h22
        change c.1 = (g 3).1 ∧ R c.2 (g 3).2 at h23
        have hac : a.1 = c.1 := h02.1.trans h22.1.symm
        let f' : Fin 3 → A := ![a.2,b.2,c.2]
        let g' : Fin 4 → B := fun j => (g j).2
        have hfmap (j : Fin 3) : f j = .inl (a.1,f' j) := by
          fin_cases j
          · simpa [f'] using hfa
          · exact hfb.trans (congrArg Sum.inl (Prod.ext hab.symm rfl))
          · exact hfc.trans (congrArg Sum.inl (Prod.ext hac.symm rfl))
        have hgmap (j : Fin 4) : g j = (a.1,g' j) := by
          refine Prod.ext ?_ rfl
          fin_cases j
          · exact h00.1.symm
          · exact h01.1.symm
          · exact h02.1.symm
          · exact h13.1.symm.trans hab.symm
        have hf' : Function.Injective f' := by
          intro i j he
          apply hfi
          rw [hfmap,hfmap,he]
        have hg' : Function.Injective g' := by
          intro i j he
          apply hgi
          rw [hgmap,hgmap,he]
        exact hR ⟨f',g',hf',hg',h00.2,h10.2,h01.2,h11.2,h02.2,h22.2,h13.2,h23.2⟩
  | inr a =>
    rw [hfa] at h00 h01 h02
    cases hfb : f 1 with
    | inl b =>
      rw [hfb] at h10 h11
      change b.1 = (g 0).1 ∧ R b.2 (g 0).2 at h10
      change b.1 = (g 1).1 ∧ R b.2 (g 1).2 at h11
      exact hne 0 1 (by decide)
        (hQtrans a.1 a.2 (g 0) (g 1) h00 h01 (h10.1.symm.trans h11.1))
    | inr b =>
      rw [hfb] at h10 h11 h13
      have hab : a.1 = b.1 := profile_eq_of_common_pair hsep hQtrans htype
        (hne 0 1 (by decide)) h00 h01 h10 h11
      cases hfc : f 2 with
      | inl c =>
        rw [hfc] at h22 h23
        change c.1 = (g 2).1 ∧ R c.2 (g 2).2 at h22
        change c.1 = (g 3).1 ∧ R c.2 (g 3).2 at h23
        have hi : (g 2).1 = (g 3).1 := h22.1.symm.trans h23.1
        have ht : τ (g 2).2 = τ (g 3).2 := by
          rw [htype a.1 a.2 (g 2) h02,htype b.1 b.2 (g 3) h13,hab,hi]
        exact hne 2 3 (by decide)
          (Prod.ext hi (hRtrans c.2 (g 2).2 (g 3).2 h22.2 h23.2 ht))
      | inr c =>
        rw [hfc] at h22 h23
        have hac : a.1 = c.1 := by
          apply hsep a.1 c.1 (g 2).1 (g 3).1
          · intro hi
            exact hne 2 3 (by decide) (hQtrans c.1 c.2 (g 2) (g 3) h22 h23 hi)
          · exact (htype a.1 a.2 (g 2) h02).symm.trans (htype c.1 c.2 (g 2) h22)
          · rw [hab]
            exact (htype b.1 b.2 (g 3) h13).symm.trans (htype c.1 c.2 (g 3) h23)
        let f' : Fin 3 → C := ![a.2,b.2,c.2]
        have hfmap (j : Fin 3) : f j = .inr (a.1,f' j) := by
          fin_cases j
          · simpa [f'] using hfa
          · exact hfb.trans (congrArg Sum.inr (Prod.ext hab.symm rfl))
          · exact hfc.trans (congrArg Sum.inr (Prod.ext hac.symm rfl))
        have hf' : Function.Injective f' := by
          intro i j he
          apply hfi
          rw [hfmap,hfmap,he]
        have h10' : Q a.1 b.2 (g 0) := hab.symm ▸ h10
        have h11' : Q a.1 b.2 (g 1) := hab.symm ▸ h11
        have h13' : Q a.1 b.2 (g 3) := hab.symm ▸ h13
        have h22' : Q a.1 c.2 (g 2) := hac.symm ▸ h22
        have h23' : Q a.1 c.2 (g 3) := hac.symm ▸ h23
        exact hQ a.1 ⟨f',g,hf',hgi,h00,h10',h01,h11',h02,h22',h13',h23'⟩

#print axioms no_theta_assemble
end Erdos713ThetaProfile
