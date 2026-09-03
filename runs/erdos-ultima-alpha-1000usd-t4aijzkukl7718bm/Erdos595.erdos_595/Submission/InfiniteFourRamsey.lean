import Submission.InfiniteTriangleRamsey

/-! An arbitrary-palette ordered Ramsey theorem for four points. -/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595InfiniteFourRamsey
open Erdos595InfiniteTriangleRamsey

variable {V C : Type*} [LinearOrder V] [WellFoundedLT V] (c : V → V → C)

def NoFour : Prop := ∀ a b d t, a < b → b < d → d < t →
  ¬(c a b = c a d ∧ c a b = c a t ∧ c a b = c b d ∧
    c a b = c b t ∧ c a b = c d t)

lemma no_three_same (hc : NoFour c) (v : V) (a b d : pred c v)
    (hab : a.val < b.val) (hbd : b.val < d.val)
    (h₁ : c a.val v = c b.val v) (h₂ : c a.val v = c d.val v) : False := by
  have habc := pred_agree c b.property (pred_chain c a.property b.property hab)
  have hadc := pred_agree c d.property
    (pred_chain c a.property d.property (hab.trans hbd))
  have hbdc := pred_agree c d.property (pred_chain c b.property d.property hbd)
  exact hc a b d v hab hbd (pred_lt c d.property)
    ⟨habc.trans hadc.symm,habc,habc.trans (h₁.trans hbdc.symm),
      habc.trans h₁,habc.trans h₂⟩

noncomputable def label (v : V) (a : pred c v) : C × Bool := by
  classical
  exact (c a.val v,decide (∃ b : pred c v, b.val < a.val ∧ c b.val v = c a.val v))

lemma label_injective (hc : NoFour c) (v : V) : Function.Injective (label c v) := by
  classical
  have hneq (a b : pred c v) (hab : a.val < b.val) : label c v a ≠ label c v b := by
    intro he
    have hcol : c a.val v = c b.val v := congrArg Prod.fst he
    have hb : ∃ d : pred c v, d.val < b.val ∧ c d.val v = c b.val v := ⟨a,hab,hcol⟩
    have hbit := congrArg Prod.snd he
    have ha : ∃ d : pred c v, d.val < a.val ∧ c d.val v = c a.val v := by
      change decide (∃ d : pred c v, d.val < a.val ∧ c d.val v = c a.val v) =
        decide (∃ d : pred c v, d.val < b.val ∧ c d.val v = c b.val v) at hbit
      exact of_decide_eq_true (hbit.trans (decide_eq_true hb))
    obtain ⟨d,hda,hd⟩ := ha
    exact no_three_same c hc v d a b hda hab hd (hd.trans hcol)
  intro a b he
  apply Subtype.ext
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact (hneq a b h he).elim
  · exact h
  · exact (hneq b a h he.symm).elim

noncomputable def pathCode (v : V) : Code (C × Bool) :=
  (Set.range (label c v),
    {ij | ∃ a b : pred c v, label c v a = ij.1 ∧ label c v b = ij.2 ∧ a.val < b.val})

lemma pathCode_order (hc : NoFour c) (v : V) (a b : pred c v) :
    (label c v a,label c v b) ∈ (pathCode c v).2 ↔ a.val < b.val := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    simpa only [label_injective c hc v hx,label_injective c hc v hy] using hxy
  · exact fun h => ⟨a,b,rfl,rfl,h⟩

theorem pathCode_injective (hc : NoFour c) : Function.Injective (pathCode c) := by
  classical
  intro v w he
  have hset : (pathCode c v).1 = (pathCode c w).1 := congrArg Prod.fst he
  have hrel : (pathCode c v).2 = (pathCode c w).2 := congrArg Prod.snd he
  have hex : ∀ a : pred c v, ∃ b : pred c w, label c w b = label c v a := by
    intro a
    have ha : label c v a ∈ (pathCode c v).1 := ⟨a,rfl⟩
    rw [hset] at ha
    exact ha
  choose f hf using hex
  have hsur : Function.Surjective f := by
    intro b
    have hb : label c w b ∈ (pathCode c w).1 := ⟨b,rfl⟩
    rw [← hset] at hb
    obtain ⟨a,ha⟩ := hb
    exact ⟨a,label_injective c hc w ((hf a).trans ha)⟩
  have hord : ∀ a b, (f a).val < (f b).val ↔ a.val < b.val := by
    intro a b
    rw [← pathCode_order c hc w (f a) (f b),hf a,hf b,← hrel]
    exact pathCode_order c hc v a b
  have hcol : ∀ a, c (f a).val w = c a.val v := fun a => congrArg Prod.fst (hf a)
  have hid := paths_rigid c f hsur hord hcol
  have hp : pred c v = pred c w := by
    ext u
    constructor
    · intro hu
      have hh : (f ⟨u,hu⟩).val = u := hid ⟨u,hu⟩
      exact hh ▸ (f ⟨u,hu⟩).property
    · intro hu
      obtain ⟨a,ha⟩ := hsur ⟨u,hu⟩
      have hh : a.val = u := (hid a).symm.trans (congrArg Subtype.val ha)
      exact hh ▸ a.property
  apply vertex_eq_of_pred_eq c hp
  intro u hu
  have hh := hcol ⟨u,hu⟩
  rw [hid ⟨u,hu⟩] at hh
  exact hh.symm

/-- A sufficiently large well-ordered carrier has four homogeneous points. -/
theorem ordered_four
    (hV : ∀ f : V → Code (C × Bool), ¬Function.Injective f) :
    ∃ a b d t, a < b ∧ b < d ∧ d < t ∧
      c a b = c a d ∧ c a b = c a t ∧ c a b = c b d ∧
      c a b = c b t ∧ c a b = c d t := by
  by_contra hn
  have hc : NoFour c := by
    intro a b d t hab hbd hdt he
    exact hn ⟨a,b,d,t,hab,hbd,hdt,he⟩
  exact hV (pathCode c) (pathCode_injective c hc)

universe u
/-- Uniform four-point Ramsey hosts, for palettes of arbitrary cardinality. -/
theorem host_from_noninjection (C A : Type u)
    (hA : ∀ f : A → Code (C × Bool), ¬Function.Injective f) :
    ∃ (_ : LinearOrder A), ∀ col : A → A → C,
      ∃ (f : Fin 4 → A) (z : C), StrictMono f ∧
        ∀ i j, i < j → col (f i) (f j) = z := by
  classical
  letI : LinearOrder A := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT A := ⟨(inferInstance : IsWellOrder A WellOrderingRel).wf⟩
  refine ⟨inferInstance,?_⟩
  intro col
  obtain ⟨a,b,d,t,hab,hbd,hdt,h₁,h₂,h₃,h₄,h₅⟩ := ordered_four col
    hA
  let f : Fin 4 → A := ![a,b,d,t]
  refine ⟨f,col a b,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
    all_goals order
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]

/-- Uniform four-point Ramsey hosts, for palettes of arbitrary cardinality. -/
theorem host (C : Type u) :
    ∃ (A : Type u) (_ : LinearOrder A), ∀ col : A → A → C,
      ∃ (f : Fin 4 → A) (z : C), StrictMono f ∧
        ∀ i j, i < j → col (f i) (f j) = z := by
  obtain ⟨o,h⟩ := host_from_noninjection C (Set (Code (C × Bool)))
    (fun f => Function.cantor_injective f)
  exact ⟨_,o,h⟩

#print axioms no_three_same
#print axioms pathCode_injective
#print axioms host
end Erdos595InfiniteFourRamsey
