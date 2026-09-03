import Submission.Work

/-!
A fixed five-state coordinate representation of every K4-free graph.
The full function graph is K4-free. Its countable coverability is NOT proved;
this is an exact normal form, not a settlement of Erdos 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595FiveStatePower
open Erdos595Work
universe u

/-- States 0,1,2 form a triangle. States 3 and 4 have loops;
3 sees 0 and 2, and 4 sees 1 and 2; they also see each other. -/
def Allowed (a b : Fin 5) : Prop :=
  ¬((a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 2 ∧ b = 2) ∨
    (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0) ∨
    (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1))

instance : DecidableRel Allowed := fun _ _ => inferInstanceAs (Decidable (¬_))

lemma allowed_symm : ∀ a b, Allowed a b → Allowed b a := by decide +kernel
lemma common_state : ∀ a, Allowed 0 a → Allowed 1 a → a = 2 := by decide +kernel
lemma not_two_two : ¬Allowed 2 2 := by decide
lemma loops : ∀ a b, (a = 3 ∨ a = 4) → (b = 3 ∨ b = 4) → Allowed a b := by
  decide +kernel

def Tight (a b : Fin 5) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)

/-- Coordinatewise compatibility together with one tight-coordinate witness. -/
def graph (I : Type*) : SimpleGraph (I → Fin 5) where
  Adj f g := (∀ i, Allowed (f i) (g i)) ∧ ∃ i, Tight (f i) (g i)
  symm := by
    rintro f g ⟨h,i,hi⟩
    exact ⟨fun j => allowed_symm _ _ (h j),i,hi.imp And.symm And.symm |>.symm⟩
  loopless := by
    rintro f ⟨_,i,hi | hi⟩
    · exact (by decide : (0 : Fin 5) ≠ 1) (hi.1.symm.trans hi.2)
    · exact (by decide : (1 : Fin 5) ≠ 0) (hi.1.symm.trans hi.2)

lemma no_four {I : Type*} (a b c d : I → Fin 5)
    (hab : (graph I).Adj a b) (hac : (graph I).Adj a c)
    (hbc : (graph I).Adj b c) (had : (graph I).Adj a d)
    (hbd : (graph I).Adj b d) (hcd : (graph I).Adj c d) : False := by
  obtain ⟨i,hi | hi⟩ := hab.2
  · have hc : c i = 2 := common_state _ (hi.1 ▸ hac.1 i) (hi.2 ▸ hbc.1 i)
    have hd : d i = 2 := common_state _ (hi.1 ▸ had.1 i) (hi.2 ▸ hbd.1 i)
    exact not_two_two (by simpa only [hc,hd] using hcd.1 i)
  · have hc : c i = 2 := common_state _ (hi.2 ▸ hbc.1 i) (hi.1 ▸ hac.1 i)
    have hd : d i = 2 := common_state _ (hi.2 ▸ hbd.1 i) (hi.1 ▸ had.1 i)
    exact not_two_two (by simpa only [hc,hd] using hcd.1 i)

theorem cliqueFree (I : Type*) : (graph I).CliqueFree 4 := by
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have h (i j : Fin 4) (hij : i ≠ j) : (graph I).Adj (f i) (f j) :=
    f.map_rel_iff.mpr hij
  exact no_four _ _ _ _ (h 0 1 (by decide)) (h 0 2 (by decide))
    (h 1 2 (by decide)) (h 0 3 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))

variable {V : Type u} (G : SimpleGraph V)

/-- A coordinate anchored at an actual edge. -/
noncomputable def state (a b v : V) : Fin 5 := by
  classical
  exact if v = a then 0 else if v = b then 1 else
    if G.Adj b v then (if G.Adj a v then 2 else 4) else 3

lemma state_zero (a b : V) : state G a b a = 0 := by
  classical
  simp [state]

lemma state_one {a b : V} (hab : G.Adj a b) : state G a b b = 1 := by
  classical
  simp [state,hab.ne.symm]

lemma state_zero_iff (a b v : V) : state G a b v = 0 ↔ v = a := by
  classical
  by_cases ha : v = a
  · simp [state,ha]
  · simp only [state,if_neg ha]
    split_ifs <;> simp_all

lemma state_one_iff {a b : V} (hab : G.Adj a b) (v : V) :
    state G a b v = 1 ↔ v = b := by
  classical
  by_cases ha : v = a
  · subst v
    simp [state,hab.ne]
  · simp only [state,if_neg ha]
    by_cases hb : v = b
    · simp [hb]
    · simp only [if_neg hb]
      split_ifs <;> simp_all

lemma state_allowed (hG : G.CliqueFree 4) {a b : V} (hab : G.Adj a b)
    {v w : V} (hvw : G.Adj v w) : Allowed (state G a b v) (state G a b w) := by
  classical
  by_cases hva : v = a
  · subst v
    have hwa := hvw.ne.symm
    by_cases hwb : w = b
    · subst w
      simp [state,hab.ne.symm,Allowed]
    · by_cases hbw : G.Adj b w <;> simp [state,hwa,hwb,hbw,hvw,Allowed]
  by_cases hvb : v = b
  · subst v
    by_cases hwa : w = a
    · subst w
      simp [state,hab.ne.symm,Allowed]
    · have hwb := hvw.ne.symm
      by_cases haw : G.Adj a w <;> simp [state,hva,hwa,hwb,hvw,haw,Allowed]
  by_cases hwa : w = a
  · subst w
    by_cases hbv : G.Adj b v <;> simp [state,hva,hvb,hbv,hvw.symm,Allowed]
  by_cases hwb : w = b
  · subst w
    by_cases hav : G.Adj a v <;> simp [state,hva,hvb,hab.ne.symm,hvw.symm,hav,Allowed]
  by_cases hbv : G.Adj b v <;> by_cases hav : G.Adj a v <;>
    by_cases hbw : G.Adj b w <;> by_cases haw : G.Adj a w
  all_goals try simp [state,hva,hvb,hwa,hwb,hbv,hav,hbw,haw,Allowed]
  exact (no_adj_common_neighbors hG hab hav hbv haw hbw hvw).elim

abbrev Index (V : Type u) := (V × V) ⊕ V

/-- Extra loop-only coordinates separate even isolated vertices. -/
noncomputable def point (v : V) : Index V → Fin 5 := by
  classical
  exact fun i => match i with
    | .inl (a,b) => if G.Adj a b then state G a b v else 3
    | .inr a => if v = a then 4 else 3

lemma point_injective : Function.Injective (point G) := by
  classical
  intro v w he
  have h := congrFun he (Sum.inr v)
  by_contra hn
  simp [point,Ne.symm hn] at h

lemma point_adj_iff (hG : G.CliqueFree 4) (v w : V) :
    (graph (Index V)).Adj (point G v) (point G w) ↔ G.Adj v w := by
  classical
  constructor
  · rintro ⟨_,i,hi⟩
    cases i with
    | inl p =>
      rcases p with ⟨a,b⟩
      by_cases hab : G.Adj a b
      · simp only [point,if_pos hab,Tight] at hi
        rcases hi with ⟨hv,hw⟩ | ⟨hv,hw⟩
        · have hv' := (state_zero_iff G a b v).mp hv
          have hw' := (state_one_iff G hab w).mp hw
          simpa only [hv',hw'] using hab
        · have hv' := (state_one_iff G hab v).mp hv
          have hw' := (state_zero_iff G a b w).mp hw
          simpa only [hv',hw'] using hab.symm
      · simp [point,hab,Tight] at hi
    | inr a =>
      by_cases hv : v = a <;> by_cases hw : w = a <;>
        simp [point,hv,hw,Tight] at hi
  · intro hvw
    refine ⟨?_,Sum.inl (v,w),?_⟩
    · intro i
      cases i with
      | inl p =>
        rcases p with ⟨a,b⟩
        by_cases hab : G.Adj a b
        · simpa only [point,if_pos hab] using state_allowed G hG hab hvw
        · simp [point,hab,Allowed]
      | inr a =>
        by_cases hv : v = a <;> by_cases hw : w = a <;>
          simp [point,hv,hw,Allowed]
    · simp [point,hvw,Tight,state_zero,state_one G hvw]

/-- Universality is induced, not just a clique-preserving homomorphism. -/
noncomputable def embedding (hG : G.CliqueFree 4) : G ↪g graph (Index V) where
  toFun := point G
  inj' := point_injective G
  map_rel_iff' := point_adj_iff G hG _ _

/-- The remaining covering assertion for this family is exactly as strong
as the original universal covering question. Neither side is proved here. -/
theorem all_cover_iff :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 → IsCountableUnionOfTriangleFree G) ↔
    (∀ (I : Type u), IsCountableUnionOfTriangleFree (graph I)) := by
  refine ⟨fun h I => h _ _ (cliqueFree I),?_⟩
  intro h V G hG
  exact countable_union_of_hom (embedding G hG).toHom (h (Index V))

#print axioms cliqueFree
#print axioms embedding
#print axioms all_cover_iff
end Erdos595FiveStatePower
