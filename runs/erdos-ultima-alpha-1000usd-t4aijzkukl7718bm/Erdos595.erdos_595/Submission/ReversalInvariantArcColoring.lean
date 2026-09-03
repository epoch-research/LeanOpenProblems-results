import Submission.ArcTwoCover
import Submission.InfiniteTriangleRamsey
import Submission.FinitePaletteCompactness

/-!
A countable triangle-free edge cover is exactly a countable weak triangle
coloring of directed arcs that is invariant under arc reversal. The symmetry
requirement cannot be omitted or recovered merely from the arc graph's K4 bound.
This does not settle the covering question for K4-free source graphs.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ReversalInvariantArcColoring
open Erdos595ArcAdjoint Erdos595Work
variable {V : Type*} (G : SimpleGraph V)

def rev (e : Arc G) : Arc G := ⟨(e.val.2, e.val.1), e.property.symm⟩

@[simp] theorem rev_rev (e : Arc G) : rev G (rev G e) = e := by
  cases e
  rfl

def Valid {C : Type*} (c : Arc G → C) : Prop :=
  ∀ p q r, (arcGraph G).Adj p q → (arcGraph G).Adj p r →
    (arcGraph G).Adj q r → ¬(c p = c q ∧ c p = c r)

theorem palette_iff {C : Type*} [Nonempty C] :
    Erdos595FinitePalette.HasColoring G C ↔
    ∃ c : Arc G → C, (∀ e, c (rev G e) = c e) ∧ Valid G c := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun e => c s(e.val.1, e.val.2), ?_, ?_⟩
    · intro e
      exact congrArg c Sym2.eq_swap
    · intro p q r hpq hpr hqr he
      have ht := arc_triangle hpq hpr hqr
      rcases p with ⟨⟨a,b⟩, hab⟩
      rcases q with ⟨⟨d,e⟩, hde⟩
      rcases r with ⟨⟨f,g⟩, hfg⟩
      dsimp at ht he hab hde hfg
      rcases ht with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
      · exact hc g b e hab hfg.symm hde
          ⟨he.2.trans (congrArg c Sym2.eq_swap), he.1⟩
      · exact hc e b g hab hde.symm hfg
          ⟨he.1.trans (congrArg c Sym2.eq_swap), he.2⟩
  · rintro ⟨c, hs, hc⟩
    let f : V → V → C := fun a b =>
      if h : G.Adj a b then c ⟨(a,b),h⟩ else Classical.arbitrary C
    have hf : ∀ a b, f a b = f b a := by
      intro a b
      dsimp only [f]
      by_cases h : G.Adj a b
      · rw [dif_pos h, dif_pos h.symm]
        exact (hs ⟨(a,b),h⟩).symm
      · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
    let d : Sym2 V → C := Sym2.lift ⟨f,hf⟩
    refine ⟨d, ?_⟩
    intro a b t hab hat hbt he
    have hd : ∀ x y (h : G.Adj x y), d s(x,y) = c ⟨(x,y),h⟩ := by
      intro x y h
      simp only [d, Sym2.lift_mk, f, dif_pos h]
    have h1 := he.1
    have h2 := he.2
    rw [hd a b hab, hd a t hat] at h1
    rw [hd a b hab, hd b t hbt] at h2
    apply hc ⟨(a,b),hab⟩ ⟨(b,t),hbt⟩ ⟨(t,a),hat.symm⟩
      (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
    exact ⟨h2, h1.trans (hs ⟨(a,t),hat⟩).symm⟩

theorem cover_iff : IsCountableUnionOfTriangleFree G ↔
    ∃ c : Arc G → ℕ, (∀ e, c (rev G e) = c e) ∧ Valid G c :=
  (countable_union_iff_edge_coloring G).trans (palette_iff G)

/-- Order signs give a weak two-coloring, but with the opposite symmetry. -/
theorem anti_invariant_two_coloring :
    ∃ c : Arc G → Bool, (∀ e, c (rev G e) ≠ c e) ∧ Valid G c := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  let c : Arc G → Bool := fun e => decide (e.val.1 < e.val.2)
  refine ⟨c, ?_, ?_⟩
  · intro e
    rcases lt_or_gt_of_ne e.property.ne with h | h
    · simp [c, rev, h, not_lt_of_ge h.le]
    · simp [c, rev, h, not_lt_of_ge h.le]
  · intro p q r hpq hpr hqr he
    have ht := arc_triangle hpq hpr hqr
    have hpne := p.property.ne
    have hqne := q.property.ne
    have hrne := r.property.ne
    change (decide (p.val.1 < p.val.2) = decide (q.val.1 < q.val.2)) ∧
      (decide (p.val.1 < p.val.2) = decide (r.val.1 < r.val.2)) at he
    by_cases hp : p.val.1 < p.val.2 <;>
      by_cases hq : q.val.1 < q.val.2 <;>
      by_cases hr : r.val.1 < r.val.2 <;>
      simp only [hp, hq, hr, decide_true, decide_false, Bool.true_eq_false,
        Bool.false_eq_true, false_and, and_false] at he
    all_goals rcases ht with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> order

/-- The graph on directed arcs can be K4-free and even two-piece covered,
while no countable weak triangle coloring is reversal-invariant. Thus the
source K4 condition, not the automatic arc K4 condition, remains essential. -/
theorem no_unrestricted_symmetry_refinement :
    ∃ (V : Type) (G : SimpleGraph V),
      (arcGraph G).CliqueFree 4 ∧
      (∃ H K : SimpleGraph (Arc G), H.CliqueFree 3 ∧ K.CliqueFree 3 ∧
        arcGraph G = H ⊔ K) ∧
      ¬∃ c : Arc G → ℕ, (∀ e, c (rev G e) = c e) ∧ Valid G c := by
  refine ⟨Set (ℕ → Fin 2), ⊤, arc_cliqueFree_four _, arc_two_cover _, ?_⟩
  intro h
  exact Erdos595InfiniteTriangleRamsey.large_complete_no_cover ((cover_iff _).mpr h)

#print axioms palette_iff
#print axioms anti_invariant_two_coloring
#print axioms cover_iff
#print axioms no_unrestricted_symmetry_refinement
end Erdos595ReversalInvariantArcColoring
