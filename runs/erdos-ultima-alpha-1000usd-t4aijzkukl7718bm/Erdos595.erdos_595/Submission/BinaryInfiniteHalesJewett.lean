import Submission.CountableHalesJewettObstruction

/-!
The binary alphabet behaves differently from the three-letter alphabet:
a sufficiently long chain in the binary cube gives a monochromatic line for
ANY prescribed palette. This does not extend the finite Folkman construction:
its partite edge alphabets need not be binary.
-/

open Set
namespace Erdos595BinaryInfiniteHalesJewett

universe u

variable {A : Type*} [LinearOrder A]

noncomputable def initialWord (a : A) : A → Fin 2 := fun j =>
  if j < a then 1 else 0

noncomputable def intervalLine (a b : A) (hab : a < b) :
    Combinatorics.Line (Fin 2) A where
  idxFun j := if j < a then some 1 else if j < b then none else some 0
  proper := ⟨a, by simp [hab]⟩

lemma intervalLine_zero (a b : A) (hab : a < b) :
    intervalLine a b hab 0 = initialWord a := by
  classical
  funext j
  by_cases hja : j < a
  · simp [intervalLine,initialWord,Combinatorics.Line.coe_apply,hja]
  · by_cases hjb : j < b <;>
      simp [intervalLine,initialWord,Combinatorics.Line.coe_apply,hja,hjb]

lemma intervalLine_one (a b : A) (hab : a < b) :
    intervalLine a b hab 1 = initialWord b := by
  classical
  funext j
  by_cases hja : j < a
  · simp [intervalLine,initialWord,Combinatorics.Line.coe_apply,hja,hja.trans hab]
  · by_cases hjb : j < b <;>
      simp [intervalLine,initialWord,Combinatorics.Line.coe_apply,hja,hjb]

/-- A collision on the chain of initial-segment words gives a binary line. -/
theorem mono_of_collision {C : Type*} (c : (A → Fin 2) → C)
    (a b : A) (hab : a < b) (he : c (initialWord a) = c (initialWord b)) :
    ∃ l : Combinatorics.Line (Fin 2) A, l.IsMono c := by
  refine ⟨intervalLine a b hab,c (initialWord a),?_⟩
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [intervalLine_zero]
  · rw [intervalLine_one,← he]

/-- There is no restriction on the cardinality of the palette C. -/
theorem exists_binary_dimension (C : Type u) :
    ∃ (I : Type u), ∀ c : (I → Fin 2) → C,
      ∃ l : Combinatorics.Line (Fin 2) I, l.IsMono c := by
  classical
  letI : LinearOrder (Set C) := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨Set C,?_⟩
  intro c
  have hn : ¬Function.Injective (fun a : Set C => c (initialWord a)) :=
    Function.cantor_injective _
  obtain ⟨a,b,he,hne⟩ := Function.not_injective_iff.mp hn
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact mono_of_collision c a b hab he
  · exact mono_of_collision c b a hba he.symm

/-- In particular, countably many colors cannot avoid binary lines in every
cube. Compare cube_countable_coloring for the three-letter alphabet. -/
theorem countable_binary_dimension :
    ∃ (I : Type), ∀ c : (I → Fin 2) → ℕ,
      ∃ l : Combinatorics.Line (Fin 2) I, l.IsMono c :=
  exists_binary_dimension ℕ

#print axioms exists_binary_dimension

/-- The obstruction extends to every alphabet admitting a three-letter
quotient. No finiteness assumption on the alphabet or dimension is needed. -/
theorem no_lines_of_three_quotient {E : Type*} (q : E → Fin 3)
    (hq : Function.Surjective q) (I : Type*) :
    ∃ c : (I → E) → ℕ, ∀ l : Combinatorics.Line E I, ¬l.IsMono c := by
  obtain ⟨d,hd⟩ := Erdos595CountableHalesJewett.cube_countable_coloring I
  refine ⟨fun w => d (q ∘ w),?_⟩
  intro l hl
  apply hd (l.map q)
  obtain ⟨k,hk⟩ := hl
  refine ⟨k,?_⟩
  intro i
  obtain ⟨e,rfl⟩ := hq i
  rw [Combinatorics.Line.map_apply]
  exact hk e

/-- Binary lines and three-letter lines have opposite behavior for countable
palettes; enlarging the dimension alone does not bridge this boundary. -/
theorem alphabet_boundary :
    (∃ (I : Type), ∀ c : (I → Fin 2) → ℕ,
      ∃ l : Combinatorics.Line (Fin 2) I, l.IsMono c) ∧
    (∀ (I : Type), ∃ c : (I → Fin 3) → ℕ,
      ∀ l : Combinatorics.Line (Fin 3) I, ¬l.IsMono c) :=
  ⟨countable_binary_dimension,Erdos595CountableHalesJewett.cube_countable_coloring⟩

#print axioms no_lines_of_three_quotient
#print axioms alphabet_boundary

#print axioms countable_binary_dimension
end Erdos595BinaryInfiniteHalesJewett
