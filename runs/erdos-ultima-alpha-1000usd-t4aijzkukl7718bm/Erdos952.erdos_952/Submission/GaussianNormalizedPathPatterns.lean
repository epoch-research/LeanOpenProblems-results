import Submission.FinitePatternAdmissibility
import Submission.GaussianHigherSieveTail

/-! A finite, exact family of normalized bounded-step path shapes. Patterns
failing local admissibility are removed only after proving that all their
actual prime translates form a finite exceptional set. -/
namespace Erdos952Investigation.GaussianNormalizedPathPatterns
open FinitePatternAdmissibility PrimePathCounting GaussianHigherPolynomialCounts
open GaussianHigherSieveTail GaussianIteratedSmoothing
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
local instance (a : GaussianInt) (R : ℕ) : Fintype (GaussianIdealBoxCounts.Box a R) := Fintype.ofFinite _

abbrev Step (C : ℤ) := {d : GaussianInt // d ≠ 0 ∧ d.norm < C}

instance stepFinite (C : ℤ) : Finite (Step C) :=
  ((norm_sublevel_finite C).subset (fun _ h => h.2.le)).to_subtype

instance stepFintype (C : ℤ) : Fintype (Step C) := Fintype.ofFinite _

abbrev Shape (C : ℤ) (L : ℕ) := RayReduction.Prefix (AdmissibleRay.latticeGraph C) 0 L

def increments (C : ℤ) (L : ℕ) (s : Shape C L) : Fin L → Step C :=
  fun i => ⟨s.val i.succ-s.val i.castSucc,
    sub_ne_zero.mpr (s.property.2.2 i).1.symm,(s.property.2.2 i).2⟩

lemma increments_injective (C : ℤ) (L : ℕ) : Function.Injective (increments C L) := by
  intro s t he
  apply Subtype.ext
  funext i
  induction i using Fin.induction with
  | zero => exact s.property.1.trans t.property.1.symm
  | succ i ih =>
    have hh := congrArg (fun f : Fin L → Step C => (f i).val) he
    change s.val i.succ-s.val i.castSucc = t.val i.succ-t.val i.castSucc at hh
    rw [ih] at hh
    exact sub_left_injective hh

instance shapeFinite (C : ℤ) (L : ℕ) : Finite (Shape C L) :=
  Finite.of_injective _ (increments_injective C L)

instance shapeFintype (C : ℤ) (L : ℕ) : Fintype (Shape C L) := Fintype.ofFinite _

lemma shape_card_le (C : ℤ) (L : ℕ) : Fintype.card (Shape C L) ≤ (Fintype.card (Step C))^L := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_le_of_injective _ (increments_injective C L)

abbrev AdmissibleShape (C : ℤ) (L : ℕ) := {s : Shape C L // FiniteAdmissible s.val}
abbrev BadShape (C : ℤ) (L : ℕ) := {s : Shape C L // ¬ FiniteAdmissible s.val}

instance admissibleShapeFintype (C : ℤ) (L : ℕ) : Fintype (AdmissibleShape C L) := Fintype.ofFinite _
instance badShapeFintype (C : ℤ) (L : ℕ) : Fintype (BadShape C L) := Fintype.ofFinite _

lemma admissible_shape_card_le (C : ℤ) (L : ℕ) :
    Fintype.card (AdmissibleShape C L) ≤ (Fintype.card (Step C))^L :=
  (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans (shape_card_le C L)

/-- Every starting point is a prime translate of a normalized shape,
including the zero-edge case. -/
lemma exists_shape_of_starts (C : ℤ) (L : ℕ) (t : GaussianInt) (ht : Starts C L t) :
    ∃ s : Shape C L, ∀ i, Prime (t+s.val i) := by
  obtain ⟨p⟩ := ht.2
  let f : Fin (L+1) → GaussianInt := fun i => p.val i-t
  have h0 : f 0 = 0 := by simp [f,p.property.1]
  have hi : Function.Injective f := by
    intro i j he
    exact p.property.2.1 (sub_left_injective he)
  have ha (i : Fin L) : (AdmissibleRay.latticeGraph C).Adj (f i.castSucc) (f i.succ) := by
    have hh := p.property.2.2 i
    refine ⟨fun he => hh.2.2.1 (sub_left_injective he),?_⟩
    simpa only [f,sub_sub_sub_cancel_right] using hh.2.2.2
  refine ⟨⟨f,h0,hi,ha⟩,?_⟩
  intro i
  have hp : Prime (p.val i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [p.property.1] using ht.1
    · exact (p.property.2.2 j).2.1
  have he : t+f i = p.val i := by dsimp [f]; abel
  change Prime (t+f i)
  rw [he]
  exact hp

lemma starts_of_prime_shape (C : ℤ) (L : ℕ) (t : GaussianInt) (s : Shape C L)
    (hp : ∀ i, Prime (t+s.val i)) : Starts C L t := by
  refine ⟨?_,⟨⟨fun i => t+s.val i,?_,?_,?_⟩⟩⟩
  · simpa only [s.property.1,add_zero] using hp 0
  · simp [s.property.1]
  · intro i j he
    exact s.property.2.1 (add_left_cancel he)
  · intro i
    refine ⟨hp i.castSucc,hp i.succ,?_,?_⟩
    · intro he
      exact (s.property.2.2 i).1 (add_left_cancel he)
    · simpa only [add_sub_add_left_eq_sub] using (s.property.2.2 i).2

lemma starts_iff_prime_shape (C : ℤ) (L : ℕ) (t : GaussianInt) :
    Starts C L t ↔ ∃ s : Shape C L, ∀ i, Prime (t+s.val i) :=
  ⟨exists_shape_of_starts C L t,fun ⟨s,hs⟩ => starts_of_prime_shape C L t s hs⟩

def badStartSet (C : ℤ) (L : ℕ) : Set GaussianInt :=
  ⋃ s : BadShape C L, {t : GaussianInt | ∀ i, Prime (t+s.val.val i)}

lemma badStartSet_finite (C : ℤ) (L : ℕ) : (badStartSet C L).Finite :=
  Set.finite_iUnion (fun s : BadShape C L =>
    prime_translates_finite_of_not_admissible s.val.val s.property)

def badStartFinset (C : ℤ) (L : ℕ) : Finset GaussianInt := (badStartSet_finite C L).toFinset

lemma starts_admissible_or_exception (C : ℤ) (L : ℕ) (t : GaussianInt) (ht : Starts C L t) :
    (∃ s : AdmissibleShape C L, ∀ i, Prime (t+s.val.val i)) ∨ t ∈ badStartFinset C L := by
  obtain ⟨s,hs⟩ := exists_shape_of_starts C L t ht
  by_cases ha : FiniteAdmissible s.val
  · exact Or.inl ⟨⟨s,ha⟩,hs⟩
  · right
    change t ∈ (badStartSet_finite C L).toFinset
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨s,ha⟩,hs⟩

/-- The covering assumption of the previous pattern budget becomes an
actual theorem on sufficiently late kernel anchors. Only finitely many
nonadmissible prime translates are discarded. -/
theorem starts_covered_on_tail (C : ℤ) (L : ℕ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (R n : ℕ) :
    ∃ N, ∀ b ≥ N, higherCount (Starts C L) (x b) R n ≤
      higherCount (fun t => ∃ s : AdmissibleShape C L, ∀ i, Prime (t+s.val.val i)) (x b) R n := by
  obtain ⟨N,hN⟩ := injective_eventually_zero_exception_count (badStartFinset C L) x hx R n
  refine ⟨N,?_⟩
  intro b hb
  have hh := kernelCount_le_add (tupleValue 0 R n) (Starts C L)
    (fun t => ∃ s : AdmissibleShape C L, ∀ i, Prime (t+s.val.val i))
    (fun t => t ∈ badStartFinset C L) (starts_admissible_or_exception C L) (x b) R
  change higherCount (Starts C L) (x b) R n ≤
    higherCount (fun t => ∃ s : AdmissibleShape C L, ∀ i, Prime (t+s.val.val i)) (x b) R n+
      higherCount (fun t => t ∈ badStartFinset C L) (x b) R n at hh
  simpa only [hN b hb,add_zero] using hh

#print axioms shape_card_le
#print axioms starts_iff_prime_shape
#print axioms badStartSet_finite
#print axioms starts_covered_on_tail
end
end Erdos952Investigation.GaussianNormalizedPathPatterns
