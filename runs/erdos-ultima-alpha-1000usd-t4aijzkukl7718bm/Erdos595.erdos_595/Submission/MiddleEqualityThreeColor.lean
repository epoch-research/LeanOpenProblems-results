import Submission.TriangleArrowReduction

/-!
A properly three-colorable graph cannot force a monochromatic edge triangle
from equality of the consecutive edges of every ordered triangle. This
rules out replacing the odd-wheel blue target by a three-colorable target;
it does not construct the missing infinite Ramsey host for Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595MiddleEqualityThreeColor
open Erdos595TriangleArrow

/-- The directed three-cycle on the proper vertex colors. -/
def step (a b : Fin 3) : Bool := decide ((a.val + 1) % 3 = b.val)

private lemma step_triple : ∀ a b c : Fin 3,
    a ≠ b → a ≠ c → b ≠ c →
      step a b = step b c ∧ step a b ≠ step a c := by
  decide +kernel

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

/-- Orient the endpoints by the vertex order, then read the cyclic color bit. -/
noncomputable def color (d : G.Coloring (Fin 3)) : Sym2 V → Bool :=
  Sym2.lift ⟨fun a b => if a ≤ b then step (d a) (d b) else step (d b) (d a), by
    intro a b
    by_cases hab : a ≤ b
    · by_cases hba : b ≤ a
      · obtain rfl := le_antisymm hab hba
        rfl
      · simp only [if_pos hab, if_neg hba]
    · have hba : b ≤ a := le_of_not_ge hab
      simp only [if_neg hab, if_pos hba]⟩

lemma color_of_lt (d : G.Coloring (Fin 3)) {a b : V} (h : a < b) :
    color G d s(a,b) = step (d a) (d b) := by
  simp only [color, Sym2.lift_mk, if_pos h.le]

/-- The two consecutive colors agree, but the long edge has the other color. -/
lemma ordered_pattern (d : G.Coloring (Fin 3)) {a b c : V}
    (h : OrderedTriangle G a b c) :
    color G d s(a,b) = color G d s(b,c) ∧
      color G d s(a,b) ≠ color G d s(a,c) := by
  rw [color_of_lt G d h.1, color_of_lt G d h.2.1,
    color_of_lt G d (h.1.trans h.2.1)]
  exact step_triple (d a) (d b) (d c) (d.valid h.2.2.1)
    (d.valid h.2.2.2.1) (d.valid h.2.2.2.2)

lemma middle_equal (d : G.Coloring (Fin 3)) :
    ∀ a b c, OrderedTriangle G a b c →
      color G d s(a,b) = color G d s(b,c) := by
  intro a b c h
  exact (ordered_pattern G d h).1

lemma valid (d : G.Coloring (Fin 3)) :
    ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      ¬(color G d s(a,b) = color G d s(a,c) ∧
        color G d s(a,b) = color G d s(b,c)) := by
  intro a b c hab hac hbc hm
  have bad (x y z : V) (hxy : x < y) (hyz : y < z)
      (h₁ : G.Adj x y) (h₂ : G.Adj x z) (h₃ : G.Adj y z)
      (he : color G d s(x,y) = color G d s(x,z)) : False :=
    (ordered_pattern G d ⟨hxy,hyz,h₁,h₂,h₃⟩).2 he
  rcases lt_or_gt_of_ne hab.ne with hab' | hba'
  · rcases lt_or_gt_of_ne hbc.ne with hbc' | hcb'
    · exact bad a b c hab' hbc' hab hac hbc hm.1
    · rcases lt_or_gt_of_ne hac.ne with hac' | hca'
      · exact bad a c b hac' hcb' hac hab hbc.symm hm.1.symm
      · apply bad c a b hca' hab' hac.symm hbc.symm hab
        simpa only [Sym2.eq_swap] using hm.1.symm.trans hm.2
  · rcases lt_or_gt_of_ne hac.ne with hac' | hca'
    · apply bad b a c hba' hac' hab.symm hbc hac
      simpa only [Sym2.eq_swap] using hm.2
    · rcases lt_or_gt_of_ne hbc.ne with hbc' | hcb'
      · apply bad b c a hbc' hca' hbc hab.symm hac.symm
        simpa only [Sym2.eq_swap] using hm.2.symm
      · apply bad c b a hcb' hba' hbc.symm hac.symm hab.symm
        simpa only [Sym2.eq_swap] using hm.2.symm.trans hm.1

/-- The blue-target forcing property concerns the ORIGINAL natural-number
edge colors; the triangle equality test itself has only two outcomes. -/
def ForcesMono : Prop :=
  ∀ c : Sym2 V → ℕ,
    (∀ a b d, OrderedTriangle G a b d → c s(a,b) = c s(b,d)) →
      ∃ a b d, G.Adj a b ∧ G.Adj a d ∧ G.Adj b d ∧
        c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d)

theorem not_forces_of_three_colorable (h : G.Colorable 3) : ¬ForcesMono G := by
  obtain ⟨d⟩ := h
  intro hf
  let c : Sym2 V → ℕ := fun e => Encodable.encode (color G d e)
  have hc : ∀ a b t, OrderedTriangle G a b t → c s(a,b) = c s(b,t) :=
    fun a b t ht => congrArg Encodable.encode (middle_equal G d a b t ht)
  obtain ⟨a,b,t,hab,hat,hbt,he⟩ := hf c hc
  exact valid G d a b t hab hat hbt
    ⟨Encodable.encode_injective he.1,Encodable.encode_injective he.2⟩

/-- In particular every forcing target must fail proper three-colorability. -/
theorem not_three_colorable_of_forces (h : ForcesMono G) : ¬G.Colorable 3 :=
  fun hc => not_forces_of_three_colorable G hc h

#print axioms ordered_pattern
#print axioms valid
#print axioms not_forces_of_three_colorable
end Erdos595MiddleEqualityThreeColor
