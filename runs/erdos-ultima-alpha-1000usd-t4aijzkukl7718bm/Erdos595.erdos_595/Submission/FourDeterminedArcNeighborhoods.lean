import Submission.FiniteBicliqueAdjoint
import Submission.ArcRoundTrip
import Submission.FiniteFolkman

/-!
Four constraints suffice to determine every common neighborhood in an arc
 graph. The bound is sharp. Consequently restricting the BASE of a right
adjoint to this bounded finite-determination class does not simplify the
universal covering question. This is a reduction, not a settlement.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FourDeterminedArc
open Erdos595Work Erdos595ArcAdjoint Erdos595Noetherian
universe u

section TwoCoordinates
variable {I A B : Type*} (f : I → A) (g : I → B)

private lemma test_point (S : Set I) (hS : S.Nonempty) (a : A) (b : B) :
    ∃ x ∈ S, (f x = a ∨ g x = b) → ∀ y ∈ S, f y = a ∨ g y = b := by
  classical
  by_cases h : ∀ y ∈ S, f y = a ∨ g y = b
  · obtain ⟨x,hx⟩ := hS
    exact ⟨x,hx,fun _ => h⟩
  · push_neg at h
    obtain ⟨x,hx,hf,hg⟩ := h
    exact ⟨x,hx,fun he => (he.elim hf hg).elim⟩

/-- An intersection of clauses `f x = a OR g x = b` has a defining
subfamily of size at most four, uniformly in all three carrier types. -/
theorem four_constraints (S : Set I) :
    ∃ T : Finset I, (↑T : Set I) ⊆ S ∧ T.card ≤ 4 ∧
      ∀ a b, (∀ x ∈ T, f x = a ∨ g x = b) ↔
        ∀ x ∈ S, f x = a ∨ g x = b := by
  classical
  by_cases hS : S.Nonempty
  · by_cases hcross : ∃ x ∈ S, ∃ y ∈ S, f x ≠ f y ∧ g x ≠ g y
    · obtain ⟨x,hx,y,hy,hf,hg⟩ := hcross
      obtain ⟨p,hp,hp'⟩ := test_point f g S hS (f x) (g y)
      obtain ⟨q,hq,hq'⟩ := test_point f g S hS (f y) (g x)
      refine ⟨{x,y,p,q},?_,Finset.card_le_four,?_⟩
      · intro z hz
        simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> assumption
      · intro a b
        constructor
        · intro h
          have hx' := h x (by simp)
          have hy' := h y (by simp)
          rcases hx' with ha | hb <;> rcases hy' with ha' | hb'
          · exact (hf (ha.trans ha'.symm)).elim
          · rw [← ha,← hb'] at h ⊢
            exact hp' (h p (by simp))
          · rw [← ha',← hb] at h ⊢
            exact hq' (h q (by simp))
          · exact (hg (hb.trans hb'.symm)).elim
        · intro h z hz
          simp only [Finset.mem_insert,Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact h _ hx
          · exact h _ hy
          · exact h _ hp
          · exact h _ hq
    · have hpair : ∀ x ∈ S, ∀ y ∈ S, f x = f y ∨ g x = g y := by
        intro x hx y hy
        by_contra h
        push_neg at h
        exact hcross ⟨x,hx,y,hy,h⟩
      obtain ⟨x,hx⟩ := hS
      by_cases hall : ∀ y ∈ S, f y = f x
      · by_cases hgsame : ∀ y ∈ S, g y = g x
        · refine ⟨{x},by simpa using hx,by simp,?_⟩
          intro a b
          simp only [Finset.mem_singleton,forall_eq]
          constructor
          · intro h y hy
            simpa only [hall y hy,hgsame y hy] using h
          · exact fun h => h x hx
        · push_neg at hgsame
          obtain ⟨y,hy,hg⟩ := hgsame
          refine ⟨{x,y},by simpa only [Finset.coe_insert,Finset.coe_singleton,
            Set.insert_subset_iff,Set.singleton_subset_iff] using ⟨hx,hy⟩,
            Finset.card_le_two.trans (by decide),?_⟩
          intro a b
          constructor
          · intro h z hz
            have hx' := h x (by simp)
            have hy' := h y (by simp)
            rcases hx' with ha | hb
            · exact Or.inl ((hall z hz).trans ha)
            · rcases hy' with ha | hb'
              · exact Or.inl ((hall z hz).trans ((hall y hy).symm.trans ha))
              · exact (hg (hb'.trans hb.symm)).elim
          · intro h z hz
            simp only [Finset.mem_insert,Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact h _ hx
            · exact h _ hy
      · push_neg at hall
        obtain ⟨y,hy,hf⟩ := hall
        have hgy : g y = g x := (hpair y hy x hx).resolve_left hf
        have hgall : ∀ z ∈ S, g z = g x := by
          intro z hz
          by_contra hn
          have hzfx : f z = f x := (hpair z hz x hx).resolve_right hn
          have hzfy : f z = f y := (hpair z hz y hy).resolve_right
            (fun he => hn (he.trans hgy))
          exact hf (hzfy.symm.trans hzfx)
        refine ⟨{x,y},by simpa only [Finset.coe_insert,Finset.coe_singleton,
          Set.insert_subset_iff,Set.singleton_subset_iff] using ⟨hx,hy⟩,
          Finset.card_le_two.trans (by decide),?_⟩
        intro a b
        constructor
        · intro h z hz
          have hx' := h x (by simp)
          have hy' := h y (by simp)
          rcases hx' with ha | hb
          · rcases hy' with ha' | hb'
            · exact (hf (ha'.trans ha.symm)).elim
            · exact Or.inr ((hgall z hz).trans (hgy.symm.trans hb'))
          · exact Or.inr ((hgall z hz).trans hb)
        · intro h z hz
          simp only [Finset.mem_insert,Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact h _ hx
          · exact h _ hy
  · have hs : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact ⟨∅,by simp,by simp,by simp⟩
end TwoCoordinates

/-- A uniform finite bound, with the determining vertices retained in S. -/
def BoundedCommonNeighbors {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ S : Set V, ∃ T : Finset V, (↑T : Set V) ⊆ S ∧ T.card ≤ n ∧
    ∀ w, (∀ v ∈ T, G.Adj v w) ↔ ∀ v ∈ S, G.Adj v w

variable {V : Type*} (G : SimpleGraph V)

theorem arc_four_determined : BoundedCommonNeighbors (arcGraph G) 4 := by
  intro S
  obtain ⟨T,hT,hcard,ht⟩ := four_constraints
    (fun e : Arc G => e.val.2) (fun e : Arc G => e.val.1) S
  refine ⟨T,hT,hcard,?_⟩
  intro w
  simpa only [arcGraph,eq_comm] using ht w.val.1 w.val.2

theorem finiteCommonNeighbors_of_bounded {n : ℕ} (h : BoundedCommonNeighbors G n) :
    FiniteCommonNeighbors G := by
  classical
  intro S
  obtain ⟨T,hT,_,ht⟩ := h S
  let f : T → S := fun v => ⟨v.val,hT v.property⟩
  refine ⟨T.attach.image f,?_⟩
  intro w
  rw [← ht w]
  constructor
  · intro h v hv
    exact h (f ⟨v,hv⟩) (Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_attach _ _,rfl⟩)
  · intro h v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact h a.val a.property

theorem arc_finiteCommonNeighbors : FiniteCommonNeighbors (arcGraph G) :=
  finiteCommonNeighbors_of_bounded _ (arc_four_determined G)

/-- Bounded determination of the BASE does not weaken the universal
right-adjoint covering question: arc graphs already satisfy the bound four. -/
theorem universal_cover_iff_four_determined_rights :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 →
      IsCountableUnionOfTriangleFree G) ↔
    (∀ (V : Type u) (H : SimpleGraph V), BoundedCommonNeighbors H 4 →
      (right H).CliqueFree 4 → IsCountableUnionOfTriangleFree (right H)) := by
  constructor
  · intro h V H _ hH
    exact h _ _ hH
  · intro h V G hG
    exact (Erdos595ArcRoundTrip.right_arc_cover_iff G).mp
      (h _ _ (arc_four_determined G) (Erdos595ArcRoundTrip.right_arc_cliqueFree G hG))


namespace Sharp

def base : SimpleGraph (Fin 4) where
  Adj a b := (a.val < 2 ∧ 2 ≤ b.val) ∨ (b.val < 2 ∧ 2 ≤ a.val)
  symm := fun _ _ h => h.symm
  loopless := by intro a h; rcases h with h | h <;> omega

instance : DecidableRel base.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val < 2 ∧ 2 ≤ b.val) ∨ (b.val < 2 ∧ 2 ≤ a.val)))
instance : DecidableRel (arcGraph base).Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))

def rectangle (i : Fin 4) : Arc base :=
  ⟨(![0,0,1,1] i, ![2,3,2,3] i),by fin_cases i <;> decide⟩

def witness (i : Fin 4) : Arc base :=
  ⟨(![3,2,3,2] i, ![1,1,0,0] i),by fin_cases i <;> decide⟩

lemma rectangle_injective : Function.Injective rectangle := by decide +kernel

lemma witness_adj : ∀ i j, (arcGraph base).Adj (rectangle j) (witness i) ↔ j ≠ i := by
  decide +kernel

/-- The sharp example is itself bipartite, not an obstruction to covering. -/
theorem bipartite : (arcGraph base).Colorable 2 := by
  let c : base.Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk (fun a => if a.val < 2 then 0 else 1) (by
      intro a b hab he
      rcases hab with h | h
      · simp only [if_pos h.1,if_neg (not_lt_of_ge h.2)] at he
        exact (by decide : (0 : Fin 2) ≠ 1) he
      · simp only [if_neg (not_lt_of_ge h.2),if_pos h.1] at he
        exact (by decide : (1 : Fin 2) ≠ 0) he)
  exact ⟨c.comp (Erdos595ArcRoundTrip.tailHom base)⟩

/-- Four is necessary even when the original graph and its arc graph
are bipartite. A rectangle of four constraints has no redundant member. -/
theorem not_three_determined : ¬BoundedCommonNeighbors (arcGraph base) 3 := by
  classical
  intro h
  obtain ⟨T,hT,hcard,ht⟩ := h (Set.range rectangle)
  have hall : ∀ i, rectangle i ∈ T := by
    intro i
    by_contra hi
    have hw : ∀ v ∈ T, (arcGraph base).Adj v (witness i) := by
      intro v hv
      obtain ⟨j,rfl⟩ := hT hv
      apply (witness_adj i j).mpr
      intro he
      subst j
      exact hi hv
    have hh := (ht (witness i)).mp hw (rectangle i) ⟨i,rfl⟩
    exact (witness_adj i i).mp hh rfl
  have hs : Finset.univ.image rectangle ⊆ T := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact hall i
  have hn := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ rectangle_injective] at hn
  have hfour : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  omega
end Sharp

/-- Even the uniform bound four on the base does not give a UNIFORM
finite edge palette for K4-free right adjoints. The base is finite and
has a two-piece triangle-free edge cover. -/
theorem no_uniform_finite_palette (C : Type) [Finite C] :
    ∃ (V : Type) (_ : Finite V) (H : SimpleGraph V),
      BoundedCommonNeighbors H 4 ∧
      (∃ A B : SimpleGraph V, A.CliqueFree 3 ∧ B.CliqueFree 3 ∧ H = A ⊔ B) ∧
      (right H).CliqueFree 4 ∧ ¬Erdos595FinitePalette.HasColoring (right H) C := by
  obtain ⟨V,hV,G,hG,hbad⟩ := Erdos595FiniteFolkman.finite_folkman C
  letI := hV
  exact ⟨Arc G,inferInstance,arcGraph G,arc_four_determined G,arc_two_cover G,
    Erdos595ArcRoundTrip.right_arc_cliqueFree G hG,
    fun hc => hbad (hc.comap (unit G))⟩

#print axioms Sharp.not_three_determined
#print axioms Sharp.bipartite
#print axioms no_uniform_finite_palette
#print axioms four_constraints
#print axioms arc_four_determined
#print axioms arc_finiteCommonNeighbors
#print axioms universal_cover_iff_four_determined_rights
end Erdos595FourDeterminedArc
