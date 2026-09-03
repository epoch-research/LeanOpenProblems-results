import Submission.E74Walk

/-!
# Buffered recoloring from a terminal assignment

This is the ball-based interpolation in Section 3 of
`Erdos74BufferedColoring.md`.  It assumes only the two constraints on a terminal
assignment, not any short-support or minimality hypothesis.  All neighborhoods
are bounded-walk neighborhoods, so empty terminal phases and disconnected
vertices require no separate distance convention.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} {r : ℕ} {S : Finset (Sym2 V)}

/-- A terminal assignment can be extended across an independent buffer.

The special edges are `badEdges G p ∪ S`.  The first constraint prescribes their
new equality pattern; the second makes the flip `q ^^ p` constant on terminals
joined by a walk of length at most `2 * r + 4` avoiding the special edges.
The resulting mask has bad-edge set exactly `S`, and every removed vertex is
outside the radius-`r + 1` ball about the terminals and inside their
radius-`r + 3` ball.
-/
theorem buffered_recolor_of_terminal_assignment (p q : V → Bool)
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet)
    (hqedge : ∀ u v, G.Adj u v → s(u, v) ∈ badEdges G p ∪ S →
      (q u = q v ↔ s(u, v) ∈ S))
    (hqnear : ∀ u ∈ ends (badEdges G p ∪ S), ∀ v ∈ ends (badEdges G p ∪ S),
      Near (G.deleteEdges ((badEdges G p ∪ S) : Set (Sym2 V))) {v} (2 * r + 4) u →
        (q u ^^ p u) = (q v ^^ p v)) :
    ∃ Z : Set V, ∃ p' : V → Bool,
      Independent G Z ∧ badEdges (mask G Z) p' = S ∧
        (∀ z ∈ Z, ¬ Near G (ends (badEdges G p ∪ S) : Set V) (r + 1) z) ∧
        (∀ z ∈ Z, Near G (ends (badEdges G p ∪ S) : Set V) (r + 3) z) := by
  classical
  let U := badEdges G p ∪ S
  let W := ends U
  let P := G.deleteEdges (U : Set (Sym2 V))
  let X : Set V := {w | w ∈ W ∧ q w ≠ p w}
  let A (i : ℕ) (v : V) : Prop := Near P X i v
  let Z : Set V := {v | p v = true ∧ A (r + 3) v ∧ ¬ A (r + 1) v}
  let p' (v : V) : Bool := if A (r + 2) v then !p v else p v

  -- Every old bad edge was deleted, so `p` is proper on `P`.
  have hPproper : ∀ ⦃u v⦄, P.Adj u v → p u ≠ p v := by
    intro u v huv heq
    obtain ⟨huv, he⟩ := SimpleGraph.deleteEdges_adj.mp huv
    exact he (Finset.mem_union.mpr (Or.inl ((mem_badEdges G p u v).mpr ⟨huv, heq⟩)))

  -- The unflipped terminals cannot reach the flipped terminals within `D`.
  have hYfar (w : V) (hw : w ∈ W) (hqw : q w = p w) : ¬ A (2 * r + 4) w := by
    rintro ⟨x, hx, path, hpath⟩
    have hnear : Near P {x} (2 * r + 4) w := near_singleton_iff.mpr ⟨path, hpath⟩
    have hphase := hqnear w hw x hx.1 (by
      simpa only [P, U, Finset.coe_union] using hnear)
    apply hx.2
    exact Bool.xor_left_inj.mp (show (q x ^^ p x) = (p x ^^ p x) by
      simpa only [hqw, Bool.xor_self] using hphase.symm)

  -- First-hit invariance transfers any short route to the terminals into `P`.
  have hZfar : ∀ z ∈ Z, ¬ Near G (W : Set V) (r + 1) z := by
    intro z hz hn
    have hnP : Near P (W : Set V) (r + 1) z :=
      (near_deleteEdges_iff (G := G) (U := U) (Set.Subset.refl _)).mpr hn
    obtain ⟨w, hw, path, hpath⟩ := hnP
    by_cases hqw : q w = p w
    · have hwX : Near P X ((r + 3) + path.length) w :=
        near_along_walk hz.2.1 path
      exact hYfar w hw hqw (near_mono_radius (by omega) hwX)
    · exact hz.2.2 ⟨w, ⟨hw, hqw⟩, path, hpath⟩

  have hWoff (w : V) (hw : w ∈ W) : w ∉ Z := by
    intro hz
    exact hZfar w hz (near_of_mem hw)

  -- All buffer vertices have old color `true`, and no special edge touches them.
  have hZind : Independent G Z := by
    intro u v huv hu hv
    have he : s(u, v) ∉ U := fun he => hWoff u (mem_ends_left he) hu
    have huvP : P.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
    exact hPproper huvP (hu.1.trans hv.1.symm)

  -- Each terminal is in exactly its prescribed phase.
  have hp'W (w : V) (hw : w ∈ W) : p' w = q w := by
    by_cases hqw : q w = p w
    · have hna : ¬ A (r + 2) w := by
        intro ha
        exact hYfar w hw hqw (near_mono_radius (by omega) ha)
      simpa only [p', if_neg hna] using hqw.symm
    · have ha : A (r + 2) w := near_of_mem (show w ∈ X from ⟨hw, hqw⟩)
      simpa only [p', if_pos ha] using (Bool.eq_not_of_ne hqw).symm

  -- A phase-crossing edge has both endpoints in the annulus; its `true`
  -- endpoint lies in the buffer.
  have hcross : ∀ ⦃u v⦄, P.Adj u v → A (r + 2) u → ¬ A (r + 2) v →
      u ∈ Z ∨ v ∈ Z := by
    intro u v huv hu hv
    have hu3 : A (r + 3) u := near_mono_radius (by omega) hu
    have hv3 : A (r + 3) v := near_prepend huv.symm hu
    have hu1 : ¬ A (r + 1) u := fun h => hv (near_prepend huv.symm h)
    have hv1 : ¬ A (r + 1) v := fun h => hv (near_mono_radius (by omega) h)
    by_cases hpu : p u = true
    · exact Or.inl ⟨hpu, hu3, hu1⟩
    · have hpv : p v = true := Bool.eq_true_of_not_eq_false (fun hpv =>
        hPproper huv ((Bool.eq_false_of_not_eq_true hpu).trans hpv.symm))
      exact Or.inr ⟨hpv, hv3, hv1⟩

  have hp'P : ∀ ⦃u v⦄, P.Adj u v → u ∉ Z → v ∉ Z → p' u ≠ p' v := by
    intro u v huv hu hv
    by_cases hau : A (r + 2) u <;> by_cases hav : A (r + 2) v
    · simpa only [p', if_pos hau, if_pos hav, Bool.not_injective.ne_iff] using
        hPproper huv
    · obtain h | h := hcross huv hau hav
      · exact (hu h).elim
      · exact (hv h).elim
    · obtain h | h := hcross huv.symm hav hau
      · exact (hv h).elim
      · exact (hu h).elim
    · simpa only [p', if_neg hau, if_neg hav] using hPproper huv

  -- Both endpoints of every edge in `S` are terminals and survive the mask.
  have hSmask : (S : Set (Sym2 V)) ⊆ (mask G Z).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have heU : s(u, v) ∈ U := Finset.mem_union.mpr (Or.inr he)
      change (mask G Z).Adj u v
      exact ⟨hS he, hWoff u (mem_ends_left heU), hWoff v (mem_ends_right heU)⟩

  have hbad : badEdges (mask G Z) p' = S := by
    apply (badEdges_eq_iff_of_subset hSmask).mpr
    intro u v huv
    by_cases heU : s(u, v) ∈ U
    · rw [hp'W u (mem_ends_left heU), hp'W v (mem_ends_right heU)]
      exact hqedge u v huv.1 heU
    · have huvP : P.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv.1, heU⟩
      have hnS : s(u, v) ∉ S := fun he => heU (Finset.mem_union.mpr (Or.inr he))
      exact iff_of_false (hp'P huvP huv.2.1 huv.2.2) hnS

  refine ⟨Z, p', hZind, hbad, hZfar, ?_⟩
  intro z hz
  exact near_mono_graph (G.deleteEdges_le (U : Set (Sym2 V)))
    (near_mono_set (show X ⊆ (W : Set V) from fun _ hx => hx.1) hz.2.1)

end E74
