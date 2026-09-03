import FormalConjecturesUtil
import Submission.ThetaAnchorBudget

/-! Linear refinements of rigid rows preserve oriented-theta exclusion.
Pair-covering refinements preserve distinct-pair codegrees, but their number
of rows can grow with the original pair-incidence mass. These statements do
not prove the theta density gap or Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRigidRefinement
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorBudget Erdos713ThetaAnchorPacking
variable {A B I : Type*}
set_option maxHeartbeats 2000000

/-- Three distinct common columns identify the original row. -/
def TripleUnique (R : A → B → Prop) : Prop :=
  ∀ a b x y z, x ≠ y → x ≠ z → y ≠ z →
    R a x → R a y → R a z → R b x → R b y → R b z → a = b

/-- Within an original row, each distinct pair belongs to at most one piece. -/
def FiberLinear (f : I → A) (Q : I → B → Prop) : Prop :=
  ∀ i j x y, f i = f j → x ≠ y →
    Q i x → Q i y → Q j x → Q j y → i = j

lemma tripleUnique_of_overlap [Fintype B] {R : A → B → Prop}
    (h : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) : TripleUnique R := by
  intro a b x y z hxy hxz hyz hax hay haz hbx hby hbz
  by_contra hab
  have hc := h a b hab
  have hs : ({x,y,z} : Finset B) ⊆ row R a ∩ row R b := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp_all [mem_row]
  have hk := card_le_card hs
  have hc3 : ({x,y,z} : Finset B).card = 3 := by simp [hxy,hxz,hyz]
  rw [hc3] at hk
  omega

/-- The closing row cannot project to either branch row: that would give
three common columns in two distinct original rows. -/
theorem no_theta_of_refinement {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hrigid : TripleUnique R) (hf : ¬ HasTheta R) : ¬ HasTheta Q := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hne {i j : Fin 4} (h : i ≠ j) : b i ≠ b j := fun he => h (hb he)
  have h01' : f (a 0) ≠ f (a 1) := by
    intro he
    have hh := hlin (a 0) (a 1) (b 0) (b 1) he (hne (by decide)) h00 h01 h10 h11
    exact (by decide : (0 : Fin 3) ≠ 1) (ha hh)
  have h20 : f (a 2) ≠ f (a 0) := by
    intro he
    apply h01'
    apply hrigid (f (a 0)) (f (a 1)) (b 0) (b 1) (b 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hsub _ _ h00) (hsub _ _ h01) _ (hsub _ _ h10) (hsub _ _ h11) (hsub _ _ h13)
    simpa only [he] using hsub _ _ h23
  have h21 : f (a 2) ≠ f (a 1) := by
    intro he
    apply h01'
    apply hrigid (f (a 0)) (f (a 1)) (b 0) (b 1) (b 2)
      (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hsub _ _ h00) (hsub _ _ h01) (hsub _ _ h02)
      (hsub _ _ h10) (hsub _ _ h11)
    simpa only [he] using hsub _ _ h22
  have hi : Function.Injective (f ∘ a) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  exact hf ⟨f ∘ a,b,hi,hb,hsub _ _ h00,hsub _ _ h10,hsub _ _ h01,hsub _ _ h11,
    hsub _ _ h02,hsub _ _ h22,hsub _ _ h13,hsub _ _ h23⟩

/-- Every distinct pair in each original row is covered by a piece of that row. -/
def PairCover (f : I → A) (R : A → B → Prop) (Q : I → B → Prop) : Prop :=
  ∀ a x y, x ≠ y → R a x → R a y → ∃ i, f i = a ∧ Q i x ∧ Q i y

/-- The unique supporting piece gives a bijection for each distinct pair. -/
theorem codegree_eq [Fintype A] [Fintype I]
    {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hcover : PairCover f R Q) {x y : B} (hxy : x ≠ y) :
    codegree Q x y = codegree R x y := by
  let g : {i : I // Q i x ∧ Q i y} → {a : A // R a x ∧ R a y} :=
    fun i => ⟨f i.val,hsub _ _ i.property.1,hsub _ _ i.property.2⟩
  have hi : Function.Injective g := by
    intro i j he
    exact Subtype.ext (hlin i.val j.val x y (congrArg Subtype.val he) hxy
      i.property.1 i.property.2 j.property.1 j.property.2)
  have hs : Function.Surjective g := by
    intro a
    obtain ⟨i,hi,hix,hiy⟩ := hcover a.val x y hxy a.property.1 a.property.2
    exact ⟨⟨i,hix,hiy⟩,Subtype.ext hi⟩
  exact Nat.card_congr (Equiv.ofBijective g ⟨hi,hs⟩)

/-- With no singleton original rows, each point support survives in at
least one piece. The diagonal codegrees can increase, but cannot decrease. -/
theorem diagonal_codegree_le [Fintype A] [Fintype I] [Fintype B]
    {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hcover : PairCover f R Q)
    (hmin : ∀ a, 2 ≤ (row R a).card) (x : B) : codegree R x x ≤ codegree Q x x := by
  let g : {i : I // Q i x ∧ Q i x} → {a : A // R a x ∧ R a x} :=
    fun i => ⟨f i.val,hsub _ _ i.property.1,hsub _ _ i.property.1⟩
  have hs : Function.Surjective g := by
    intro a
    obtain ⟨y,hy,hyx⟩ := exists_mem_ne (hmin a.val) x
    obtain ⟨i,hi,hix,_⟩ := hcover a.val x y hyx.symm a.property.1 ((mem_row _ _ _).mp hy)
    exact ⟨⟨i,hix,hix⟩,Subtype.ext hi⟩
  exact Nat.card_le_card_of_surjective g hs

/-- The full light-pair budget includes diagonals; these are handled by
surjectivity on point supports rather than silently treating pairs as distinct. -/
theorem lightCount_le [Fintype A] [Fintype I] [Fintype B]
    {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hcover : PairCover f R Q) (hmin : ∀ a, 2 ≤ (row R a).card) :
    Erdos713ThetaCross.lightCount Q ≤ Erdos713ThetaCross.lightCount R := by
  have hle (x y : B) : codegree R x y ≤ codegree Q x y := by
    by_cases hxy : x = y
    · subst y
      exact diagonal_codegree_le f hsub hcover hmin x
    · exact (codegree_eq f hsub hlin hcover hxy).symm.le
  let g : {p : B × B // codegree Q p.1 p.2 ≤ 2} →
      {p : B × B // codegree R p.1 p.2 ≤ 2} :=
    fun p => ⟨p.val,(hle p.val.1 p.val.2).trans p.property⟩
  have hi : Function.Injective g := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : {p : B × B // codegree R p.1 p.2 ≤ 2} => z.val) h
  exact Nat.card_le_card_of_injective g hi

/-- Pair-incidence mass is conserved, not the number of rows. -/
theorem pair_mass_eq [Fintype A] [Fintype I] [Fintype B]
    {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hcover : PairCover f R Q) :
    (∑ i : I, (row Q i).offDiag.card) = ∑ a : A, (row R a).offDiag.card := by
  rw [pair_incidence_sum Q univ,pair_incidence_sum R univ]
  apply sum_congr rfl
  intro p hp
  have he := codegree_eq f hsub hlin hcover (mem_offDiag.mp hp).2.2
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype,commonRows] using he

/-- A triple refinement uses one new row for every six ordered pair incidences.
In particular, pair preservation does not preserve the original row budget. -/
theorem triple_row_count [Fintype A] [Fintype I] [Fintype B]
    {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hcover : PairCover f R Q) (hthree : ∀ i, (row Q i).card = 3) :
    6*Fintype.card I = ∑ a : A, (row R a).offDiag.card := by
  have he := pair_mass_eq f hsub hlin hcover
  simpa only [offDiag_card,hthree,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,
    show 3*3-3=6 by decide,Nat.mul_comm] using he

#print axioms no_theta_of_refinement
#print axioms codegree_eq
#print axioms lightCount_le
#print axioms pair_mass_eq
#print axioms triple_row_count
end Erdos713ThetaRigidRefinement
