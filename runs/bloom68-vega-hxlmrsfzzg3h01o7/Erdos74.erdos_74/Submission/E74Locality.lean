import Submission.E74Parity
import Submission.E74Walk

/-!
# Locality of minimum short supports

A minimum short support lies within `S.card * L` of the endpoints of any other
short support, in particular of the bad edges of any Boolean assignment.

We use a finite flood argument instead of shortest paths in the auxiliary graph
of co-occurring edges.  A proper subset `D` of a minimum support violates some
short closed-walk constraint.  Comparing its sum with the sums for `S` and `F`
finds both a new edge of `S \ D` and an edge of `D ∪ F` on the same walk.  Every
endpoint of the new edge is therefore within `L` of the previous flood or `F`.
Adding one edge at a time finishes after exactly `S.card` steps.

All constraints and comparisons use complete walk edge lists, with
multiplicities.  No cycle decomposition is used.  The route between two
vertices on a walk has length at most that walk's length, not twice its length;
this is what gives the exact radius.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Any two vertices occurring on a walk can be joined by a walk no longer than
that walk.  The connecting segment may be traversed in reverse. -/
theorem exists_walk_length_le_of_mem_support {a b x y : V} (w : G.Walk a b)
    (hx : x ∈ w.support) (hy : y ∈ w.support) :
    ∃ q : G.Walk x y, q.length ≤ w.length := by
  revert hx hy
  induction w with
  | @nil a =>
      intro hx hy
      have hxa : x = a := by simpa using hx
      have hya : y = a := by simpa using hy
      subst x y
      exact ⟨Walk.nil, le_rfl⟩
  | @cons a b c hab w ih =>
      intro hx hy
      by_cases hxa : x = a
      · subst x
        exact ⟨(w.cons hab).takeUntil y hy, (w.cons hab).length_takeUntil_le hy⟩
      by_cases hya : y = a
      · subst y
        refine ⟨((w.cons hab).takeUntil x hx).reverse, ?_⟩
        simpa only [Walk.length_reverse] using (w.cons hab).length_takeUntil_le hx
      have hxt : x ∈ w.support := by
        simpa only [Walk.support_cons, List.mem_cons, hxa, false_or] using hx
      have hyt : y ∈ w.support := by
        simpa only [Walk.support_cons, List.mem_cons, hya, false_or] using hy
      obtain ⟨q, hq⟩ := ih hxt hyt
      exact ⟨q, hq.trans (Nat.le_succ w.length)⟩

variable {L r : ℕ} {S F D : Finset (Sym2 V)}

/-- One finite-flood step.  If fewer than `S.card` edges have been reached, a
violated constraint supplies a new edge, all of whose endpoints cost at most
one further `L` in radius.  Only the short-support property of `F` is needed. -/
theorem MinimalSupport.exists_near_edge_of_card_lt
    (hS : MinimalSupport G L S) (hF : ShortSupport G L F)
    (hDS : D ⊆ S) (hcard : D.card < S.card)
    (hD : ∀ v ∈ ends D, Near G (ends F : Set V) r v) :
    ∃ e ∈ S, e ∉ D ∧ ∀ v ∈ e, Near G (ends F : Set V) (r + L) v := by
  classical
  have hbad : ∃ (v : V) (w : G.Walk v v),
      w.length ≤ L ∧ walkXor (twist D) w ≠ false := by
    by_contra! h
    have hvalid : ShortSupport G L D :=
      ⟨fun _ he => hS.1.1 (hDS he), h⟩
    exact (Nat.not_le_of_lt hcard) (hS.card_le hvalid)
  obtain ⟨v, w, hw, hxor⟩ := hbad
  obtain ⟨e, he, heS, heD⟩ := hS.1.exists_edge_not_mem hDS w hw hxor
  have hDF : walkXor (twist D) w ≠ walkXor (twist F) w := by
    rw [hF.2 v w hw]
    exact hxor
  obtain ⟨f, hf, hfne⟩ := exists_edge_of_walkXor_ne w hDF
  have hfmem : f ∈ D ∨ f ∈ F := by
    by_contra! h
    exact hfne (by simp [h.1, h.2])
  have hfnear : Near G (ends F : Set V) r f.out.1 := by
    rcases hfmem with hfD | hfF
    · exact hD f.out.1 (mem_ends_of_mem hfD f.out_fst_mem)
    · exact near_of_mem (mem_ends_of_mem hfF f.out_fst_mem)
  refine ⟨e, heS, heD, ?_⟩
  intro x hx
  obtain ⟨q, hq⟩ := exists_walk_length_le_of_mem_support w
    (Walk.mem_support_of_mem_edges he hx)
    (Walk.mem_support_of_mem_edges hf f.out_fst_mem)
  apply near_mono_radius _ (near_prepend_walk q hfnear)
  have hqL : q.length ≤ L := hq.trans hw
  omega

/-- A minimum short support is local to any short support at the same scale.
Finiteness of the ambient vertex type is not needed for this stronger form. -/
theorem minimalSupport_near_shortSupport
    (hS : MinimalSupport G L S) (hF : ShortSupport G L F) :
    ∀ v ∈ ends S, Near G (ends F : Set V) (S.card * L) v := by
  classical
  have flood : ∀ n, n ≤ S.card →
      ∃ D : Finset (Sym2 V), D ⊆ S ∧ D.card = n ∧
        ∀ v ∈ ends D, Near G (ends F : Set V) (n * L) v := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
        simp
    | succ n ih =>
        intro hn
        obtain ⟨D, hDS, hcard, hD⟩ := ih (Nat.le_of_succ_le hn)
        have hlt : D.card < S.card := by omega
        obtain ⟨e, heS, heD, henear⟩ :=
          hS.exists_near_edge_of_card_lt hF hDS hlt hD
        refine ⟨insert e D, Finset.insert_subset heS hDS, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem heD, hcard]
        · intro v hv
          obtain ⟨f, hf, hvf⟩ := mem_ends.mp hv
          rcases Finset.mem_insert.mp hf with rfl | hf
          · simpa only [Nat.succ_mul] using henear v hvf
          · exact near_mono_radius (Nat.mul_le_mul_right L (Nat.le_succ n))
              (hD v (mem_ends_of_mem hf hvf))
  obtain ⟨D, hDS, hcard, hD⟩ := flood S.card le_rfl
  have hEq : D = S := Finset.eq_of_subset_of_card_le hDS hcard.ge
  simpa only [hEq] using hD

/-- Every endpoint of a minimum short support is within `S.card * L` of a bad
edge of any prescribed Boolean assignment.  `Near` includes an actual walk, so
this also handles disconnected graphs; when `S = ∅` the conclusion is vacuous. -/
theorem minimalSupport_near_badEdges [Fintype V]
    (hS : MinimalSupport G L S) (p : V → Bool) :
    ∀ v ∈ ends S, Near G (ends (badEdges G p) : Set V) (S.card * L) v :=
  minimalSupport_near_shortSupport hS (shortSupport_badEdges G L p)

end E74
