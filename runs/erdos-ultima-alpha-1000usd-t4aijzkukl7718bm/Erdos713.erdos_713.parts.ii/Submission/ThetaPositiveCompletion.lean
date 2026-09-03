import FormalConjecturesUtil
import Submission.ThetaHeavyShadow
import Submission.ThetaCrossCompletion

/-! Positive light pairs can be completed by degree-at-most-two rows in a
rigid theta-free relation. This is an auxiliary normalization, not a proof
of the density gap or of Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaPositiveCompletion
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross (lightCount)
set_option maxHeartbeats 2000000
variable {A B : Type*}

abbrev PositiveLight (R : A → B → Prop) :=
  {p : B × B // 0 < codegree R p.1 p.2 ∧ codegree R p.1 p.2 ≤ 2}

abbrev Rows (R : A → B → Prop) := A ⊕ (PositiveLight R × Fin 2)

def fill (R : A → B → Prop) : Rows R → B → Prop
  | .inl a, x => R a x
  | .inr p, x => x = p.1.val.1 ∨ x = p.1.val.2

noncomputable def zeroCount (R : A → B → Prop) : ℕ :=
  Nat.card {p : B × B // codegree R p.1 p.2 = 0}

lemma old_of_three (R : A → B → Prop) {a : Rows R} {x y z : B}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : fill R a x) (hy : fill R a y) (hz : fill R a z) : ∃ b : A, a = .inl b := by
  cases a with
  | inl a => exact ⟨a,rfl⟩
  | inr p =>
    change x = p.1.val.1 ∨ x = p.1.val.2 at hx
    change y = p.1.val.1 ∨ y = p.1.val.2 at hy
    change z = p.1.val.1 ∨ z = p.1.val.2 at hz
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> simp_all

lemma lift_common (R : A → B → Prop) {a : Rows R} {x y : B}
    (hx : fill R a x) (hy : fill R a y) : ∃ b : A, R b x ∧ R b y := by
  cases a with
  | inl a => exact ⟨a,hx,hy⟩
  | inr p =>
    obtain ⟨⟨b,hb⟩⟩ := (Nat.card_pos_iff.mp p.1.property.1).1
    refine ⟨b,?_,?_⟩
    · rcases hx with hx | hx <;> rw [hx] <;> first | exact hb.1 | exact hb.2
    · rcases hy with hy | hy <;> rw [hy] <;> first | exact hb.1 | exact hb.2

lemma eq_of_three [Fintype B] {R : A → B → Prop}
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {a b : A} {x y z : B} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : R a x) (hay : R a y) (haz : R a z)
    (hbx : R b x) (hby : R b y) (hbz : R b z) : a = b := by
  by_contra hab
  have hs : ({x,y,z} : Finset B) ⊆ row R a ∩ row R b := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [mem_row,hax,hay,haz,hbx,hby,hbz]
  have hc := (card_le_card hs).trans (hr a b hab)
  have he : ({x,y,z} : Finset B).card = 3 := by simp [hxy,hxz,hyz]
  omega

/-- A new closing row lifts to an old one. Rigidity ensures the old
closing row differs from both branch rows. -/
theorem no_theta [Fintype B] {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) : ¬ HasTheta (fill R) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hn (i j : Fin 4) (hij : i ≠ j) : g i ≠ g j := fun he => hij (hgi he)
  obtain ⟨a,ha⟩ := old_of_three R (hn 0 1 (by decide)) (hn 0 2 (by decide))
    (hn 1 2 (by decide)) h00 h01 h02
  obtain ⟨b,hb⟩ := old_of_three R (hn 0 1 (by decide)) (hn 0 3 (by decide))
    (hn 1 3 (by decide)) h10 h11 h13
  rw [ha] at h00 h01 h02
  rw [hb] at h10 h11 h13
  have hab : a ≠ b := by
    intro he
    exact (by decide : (0 : Fin 3) ≠ 1) (hfi (ha.trans ((congrArg Sum.inl he).trans hb.symm)))
  obtain ⟨c,hc2,hc3⟩ := lift_common R h22 h23
  have hac : a ≠ c := by
    intro he
    subst c
    exact hab (eq_of_three hr (hn 0 1 (by decide)) (hn 0 3 (by decide))
      (hn 1 3 (by decide)) h00 h01 hc3 h10 h11 h13)
  have hbc : b ≠ c := by
    intro he
    subst c
    exact hab (eq_of_three hr (hn 0 1 (by decide)) (hn 0 2 (by decide))
      (hn 1 2 (by decide)) h00 h01 h02 h10 h11 hc2)
  have hi : Function.Injective (![a,b,c] : Fin 3 → A) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  exact hf ⟨![a,b,c],g,hi,hgi,h00,h10,h01,h11,h02,hc2,h13,hc3⟩

lemma old_row [Fintype B] (R : A → B → Prop) (a : A) : row (fill R) (.inl a) = row R a := rfl

lemma new_row [Fintype B] (R : A → B → Prop) (p : PositiveLight R × Fin 2) :
    row (fill R) (.inr p) = {p.1.val.1,p.1.val.2} := by
  ext x
  simp [mem_row,fill]

lemma new_row_card [Fintype B] (R : A → B → Prop) (p : PositiveLight R × Fin 2) :
    (row (fill R) (.inr p)).card ≤ 2 := by rw [new_row]; exact card_le_two

theorem rigid [Fintype B] {R : A → B → Prop}
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) :
    ∀ a b, a ≠ b → (row (fill R) a ∩ row (fill R) b).card ≤ 2 := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hr a b (fun he => hab (congrArg Sum.inl he))
    | inr p => exact (card_le_card inter_subset_right).trans (new_row_card R p)
  | inr p => exact (card_le_card inter_subset_left).trans (new_row_card R p)

variable [Fintype A] [Fintype B]

lemma codegree_mono (R : A → B → Prop) (x y : B) : codegree R x y ≤ codegree (fill R) x y := by
  let f : {a : A // R a x ∧ R a y} → {a : Rows R // fill R a x ∧ fill R a y} :=
    fun a => ⟨.inl a.val,a.property⟩
  exact Nat.card_le_card_of_injective f (fun a b he => Subtype.ext (Sum.inl.inj (congrArg Subtype.val he)))

lemma positive_heavy (R : A → B → Prop) (x y : B) (hpos : 0 < codegree R x y) :
    3 ≤ codegree (fill R) x y := by
  by_cases hh : 3 ≤ codegree R x y
  · exact hh.trans (codegree_mono R x y)
  obtain ⟨⟨a,ha⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  let p : PositiveLight R := ⟨(x,y),hpos,by change codegree R x y ≤ 2; omega⟩
  let f : Option (Fin 2) → {b : Rows R // fill R b x ∧ fill R b y}
    | none => ⟨.inl a,ha⟩
    | some i => ⟨.inr (p,i),Or.inl rfl,Or.inr rfl⟩
  have hi : Function.Injective f := by
    intro i j he
    have hv := congrArg Subtype.val he
    cases i with
    | none => cases j <;> simp_all [f]
    | some i =>
      cases j with
      | none => simp [f] at hv
      | some j =>
        have he' := congrArg Prod.snd (Sum.inr.inj hv)
        exact congrArg Option.some he'
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_fin] using
    Nat.card_le_card_of_injective f hi

lemma zero_iff (R : A → B → Prop) (x y : B) :
    codegree (fill R) x y = 0 ↔ codegree R x y = 0 := by
  constructor
  · intro h
    have hh := codegree_mono R x y
    omega
  · intro h
    by_contra hn
    obtain ⟨⟨a,ha⟩⟩ := (Nat.card_pos_iff.mp (show 0 < codegree (fill R) x y by omega)).1
    obtain ⟨b,hb⟩ := lift_common R ha.1 ha.2
    haveI : Nonempty {a : A // R a x ∧ R a y} := ⟨⟨b,hb⟩⟩
    have hp : 0 < codegree R x y := Nat.card_pos
    omega

lemma light_iff_zero (R : A → B → Prop) (x y : B) :
    codegree (fill R) x y ≤ 2 ↔ codegree R x y = 0 := by
  constructor
  · intro hl
    by_contra hn
    have hh := positive_heavy R x y (show 0 < codegree R x y by omega)
    omega
  · intro hz
    rw [(zero_iff R x y).mpr hz]
    decide

lemma zero_or_heavy (R : A → B → Prop) (x y : B) :
    codegree (fill R) x y = 0 ∨ 3 ≤ codegree (fill R) x y := by
  by_cases hz : codegree R x y = 0
  · exact Or.inl ((zero_iff R x y).mpr hz)
  · exact Or.inr (positive_heavy R x y (by omega))

lemma zeroCount_eq (R : A → B → Prop) : zeroCount (fill R) = zeroCount R :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun p => zero_iff R p.1 p.2))

lemma lightCount_eq (R : A → B → Prop) : lightCount (fill R) = zeroCount R :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun p => light_iff_zero R p.1 p.2))

omit [Fintype A] in
lemma zeroCount_le (R : A → B → Prop) : zeroCount R ≤ lightCount R := by
  let f : {p : B × B // codegree R p.1 p.2 = 0} →
      {p : B × B // codegree R p.1 p.2 ≤ 2} := fun p => ⟨p.val,by rw [p.property]; decide⟩
  exact Nat.card_le_card_of_injective f (by
    intro a b he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv)

lemma rows_card_le (R : A → B → Prop) : Nat.card (Rows R) ≤ Nat.card A+2*lightCount R := by
  let f : PositiveLight R → {p : B × B // codegree R p.1 p.2 ≤ 2} := fun p => ⟨p.val,p.property.2⟩
  have hh := Nat.card_le_card_of_injective f (by
    intro a b he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv)
  change Nat.card (PositiveLight R) ≤ lightCount R at hh
  simp only [Rows,Nat.card_sum,Nat.card_prod,Nat.card_fin]
  omega

omit [Fintype A] in
lemma light_split (R : A → B → Prop) :
    Nat.card (PositiveLight R)+zeroCount R = lightCount R := by
  have hs := card_filter_add_card_filter_not
    (s := (univ : Finset (B × B)).filter (fun p => codegree R p.1 p.2 ≤ 2))
    (fun p => 0 < codegree R p.1 p.2)
  simp only [filter_filter] at hs
  have hp : (univ : Finset (B × B)).filter (fun p => codegree R p.1 p.2 ≤ 2 ∧
      0 < codegree R p.1 p.2) = univ.filter (fun p => 0 < codegree R p.1 p.2 ∧
      codegree R p.1 p.2 ≤ 2) := by ext p; simp [and_comm]
  have hz : (univ : Finset (B × B)).filter (fun p => codegree R p.1 p.2 ≤ 2 ∧
      ¬ 0 < codegree R p.1 p.2) = univ.filter (fun p => codegree R p.1 p.2 = 0) := by
    ext p
    simp only [mem_filter,mem_univ,true_and]
    omega
  rw [hp,hz] at hs
  simpa only [PositiveLight,zeroCount,lightCount,Nat.card_eq_fintype_card,
    Fintype.card_subtype] using hs

lemma completed_budget (R : A → B → Prop) :
    Nat.card (Rows R)+zeroCount (fill R) ≤ Nat.card A+2*lightCount R := by
  have hs := light_split R
  rw [zeroCount_eq]
  simp only [Rows,Nat.card_sum,Nat.card_prod,Nat.card_fin]
  omega

/-- The remaining density-gap problem can be restricted to relations
whose positive codegrees are all at least three. This is still a hypothesis. -/
def CompletedGap (C : ℕ) : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
    ¬ HasTheta R → (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) →
    (∀ x y, codegree R x y = 0 ∨ 3 ≤ codegree R x y) →
    (Nat.card B)^2 ≤ C*(Nat.card A+zeroCount R)

/-- Conditional on CompletedGap, not an assertion that it holds. -/
theorem rigid_gap_of_completed {C : ℕ} (hC : CompletedGap C)
    {A B : Type} [Fintype A] [Fintype B] (R : A → B → Prop) (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) :
    (Nat.card B)^2 ≤ 2*C*(Nat.card A+lightCount R) := by
  have hh := hC (Rows R) B (fill R) (no_theta hf hr) (rigid hr) (zero_or_heavy R)
  have hb := completed_budget R
  calc
    _ ≤ C*(Nat.card (Rows R)+zeroCount (fill R)) := hh
    _ ≤ C*(2*(Nat.card A+lightCount R)) := Nat.mul_le_mul_left C (by omega)
    _ = _ := by ring

#print axioms no_theta
#print axioms rigid
#print axioms positive_heavy
#print axioms lightCount_eq
#print axioms rows_card_le
#print axioms completed_budget
#print axioms rigid_gap_of_completed
end Erdos713ThetaPositiveCompletion
