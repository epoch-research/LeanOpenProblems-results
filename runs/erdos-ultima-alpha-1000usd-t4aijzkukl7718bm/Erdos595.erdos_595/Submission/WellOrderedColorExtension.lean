import FormalConjecturesUtil

/-!
A well-ordered system of triangle-avoidance constraints has a global coloring
if every prescribed valid coloring before a stage extends through that
stage. This uses the explicit extension hypothesis, NOT a countable-palette
compactness principle. The palette is arbitrary and nonempty.
-/

set_option autoImplicit false
open Set
namespace Erdos595WellOrderedColorExtension

variable {X I C : Type*} [LinearOrder I] [WellFoundedLT I] [Nonempty C]
    (r : X → I) (R : X → X → X → Prop)

def Before (i : I) (c : X → C) : Prop :=
  ∀ x y z, R x y z → r x < i → r y < i → r z < i →
    ¬(c x = c y ∧ c x = c z)

def Through (i : I) (c : X → C) : Prop :=
  ∀ x y z, R x y z → r x ≤ i → r y ≤ i → r z ≤ i →
    ¬(c x = c y ∧ c x = c z)

def Step (i : I) (old d : X → C) : Prop :=
  Through r R i d ∧ ∀ x, r x < i → d x = old x

noncomputable def chooseStep (i : I) (old : X → C) : X → C := by
  classical
  exact if h : ∃ d, Step r R i old d then h.choose else fun _ => Classical.arbitrary C

noncomputable def stage : I → X → C :=
  wellFounded_lt.fix (fun i rec => chooseStep r R i (fun x =>
    if h : r x < i then rec (r x) h x else Classical.arbitrary C))

lemma stage_eq (i : I) : stage r R (C := C) i =
    chooseStep r R i (fun x =>
      if r x < i then stage r R (C := C) (r x) x else Classical.arbitrary C) := by
  rw [stage,WellFounded.fix_eq]
  rfl

variable (hext : ∀ (i : I) (old : X → C), Before r R i old →
  ∃ d, Step r R i old d)

include hext

/-- Each stage is valid and retains the color fixed at each earlier rank. -/
theorem stage_spec (i : I) :
    Through r R i (stage r R (C := C) i) ∧
      ∀ x, r x < i → stage r R (C := C) i x = stage r R (C := C) (r x) x := by
  classical
  induction i using (wellFounded_lt (α := I)).induction with
  | h i ih =>
    let old : X → C := fun x => if r x < i then stage r R (C := C) (r x) x else Classical.arbitrary C
    have hb : Before r R i old := by
      intro x y z hR hx hy hz hm
      let j := max (r x) (max (r y) (r z))
      have hji : j < i := max_lt hx (max_lt hy hz)
      have hxj : r x ≤ j := le_max_left _ _
      have hyj : r y ≤ j := (le_max_left _ _).trans (le_max_right _ _)
      have hzj : r z ≤ j := (le_max_right _ _).trans (le_max_right _ _)
      have hold (w : X) (hwi : r w < i) (hwj : r w ≤ j) :
          old w = stage r R (C := C) j w := by
        dsimp only [old]
        rw [if_pos hwi]
        rcases hwj.eq_or_lt with he | hl
        · rw [he]
        · exact ((ih j hji).2 w hl).symm
      rw [hold x hx hxj,hold y hy hyj,hold z hz hzj] at hm
      exact (ih j hji).1 x y z hR hxj hyj hzj hm
    obtain ⟨d,hd⟩ := hext i old hb
    have hex : ∃ d, Step r R i old d := ⟨d,hd⟩
    have hchosen : Step r R i old (chooseStep r R i old) := by
      simp only [chooseStep,dif_pos hex]
      exact hex.choose_spec
    have hstage : stage r R (C := C) i = chooseStep r R i old := stage_eq r R i
    rw [hstage]
    refine ⟨hchosen.1,?_⟩
    intro x hx
    rw [hchosen.2 x hx]
    exact if_pos hx

/-- No countability assumption on the well-ordered stage type is required. -/
theorem global_coloring :
    ∃ c : X → C, ∀ x y z, R x y z → ¬(c x = c y ∧ c x = c z) := by
  classical
  let c : X → C := fun x => stage r R (C := C) (r x) x
  refine ⟨c,?_⟩
  intro x y z hR hm
  let i := max (r x) (max (r y) (r z))
  have hx : r x ≤ i := le_max_left _ _
  have hy : r y ≤ i := (le_max_left _ _).trans (le_max_right _ _)
  have hz : r z ≤ i := (le_max_right _ _).trans (le_max_right _ _)
  have hci (w : X) (hw : r w ≤ i) : c w = stage r R (C := C) i w := by
    rcases hw.eq_or_lt with he | hl
    · change stage r R (C := C) (r w) w = stage r R (C := C) i w
      rw [he]
    · exact ((stage_spec r R hext i).2 w hl).symm
  rw [hci x hx,hci y hy,hci z hz] at hm
  exact (stage_spec r R hext i).1 x y z hR hx hy hz hm

#print axioms global_coloring
end Erdos595WellOrderedColorExtension
