import Submission.E74Parity
import Submission.E74Walk

/-!
# Potentials on a finite set of terminals

A short-walk constraint is represented by an edge in a Boolean double cover of
its terminal set.  If a terminal and its opposite lift were connected, a simple
path in the cover would expand to a short closed walk with nonzero XOR.  Ordering
the two distinct components over each terminal therefore gives a potential.

The cover has twice as many vertices as the terminal set.  This accounts for
the constant `16` in `exists_terminal_assignment`.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V}

/-- The Boolean double cover of all bounded-length terminal constraints.  The
inequality removes graph loops; trivial constraints are handled by reflexive
reachability instead. -/
private def terminalCover (G : SimpleGraph V) (a : Sym2 V → Bool)
    (W : Finset V) (D : ℕ) : SimpleGraph (W × Bool) where
  Adj x y := x ≠ y ∧ ∃ w : G.Walk x.1.1 y.1.1,
    w.length ≤ D ∧ walkXor a w = (x.2 ^^ y.2)
  symm := by
    intro x y h
    obtain ⟨hne, w, hw, hx⟩ := h
    exact ⟨hne.symm, w.reverse, by simpa using hw,
      by simpa [Bool.xor_comm] using hx⟩
  loopless := by
    intro x h
    exact h.1 rfl

omit [DecidableEq V] in
/-- Expand a cover walk, retaining both the length bound and its endpoint XOR. -/
private theorem terminalCover_expand {a : Sym2 V → Bool} {W : Finset V} {D : ℕ}
    {x y : W × Bool} (p : (terminalCover G a W D).Walk x y) :
    ∃ w : G.Walk x.1.1 y.1.1,
      w.length ≤ p.length * D ∧ walkXor a w = (x.2 ^^ y.2) := by
  induction p with
  | nil => exact ⟨Walk.nil, by simp, by simp⟩
  | @cons x y z h p ih =>
    obtain ⟨e, he, hx⟩ := h.2
    obtain ⟨w, hw, hy⟩ := ih
    refine ⟨e.append w, ?_, ?_⟩
    · calc
        (e.append w).length = e.length + w.length := by simp
        _ ≤ D + p.length * D := Nat.add_le_add he hw
        _ = (p.cons h).length * D := by simp [Nat.add_mul, Nat.add_comm]
    · rw [walkXor_append, hx, hy]
      cases x.2 <;> cases y.2 <;> cases z.2 <;> rfl

/-- A single constraint connects the corresponding lifts, even when they agree. -/
private theorem terminalCover_reachable {a : Sym2 V → Bool} {W : Finset V} {D : ℕ}
    {x y : W × Bool} (w : G.Walk x.1.1 y.1.1) (hw : w.length ≤ D)
    (hx : walkXor a w = (x.2 ^^ y.2)) : (terminalCover G a W D).Reachable x y := by
  by_cases h : x = y
  · subst y
    exact Reachable.rfl
  · exact (show (terminalCover G a W D).Adj x y from ⟨h, w, hw, hx⟩).reachable

/-- If all closed walks of length at most `2 * W.card * D` have zero XOR,
then one potential simultaneously respects every walk of length at most `D`
between terminals in `W`.  No finiteness of the ambient vertex type is needed. -/
theorem exists_potential_on_short_walks (a : Sym2 V → Bool) (W : Finset V) (D : ℕ)
    (hzero : ∀ (v : V) (w : G.Walk v v),
      w.length ≤ 2 * W.card * D → walkXor a w = false) :
    ∃ q : V → Bool, ∀ u ∈ W, ∀ v ∈ W, ∀ w : G.Walk u v,
      w.length ≤ D → walkXor a w = (q u ^^ q v) := by
  classical
  let H := terminalCover G a W D
  let c (v : W) (b : Bool) : H.ConnectedComponent := H.connectedComponentMk (v, b)
  have hsep (v : W) : c v false ≠ c v true := by
    intro hc
    obtain ⟨p, hp⟩ := (ConnectedComponent.exact hc).exists_isPath
    obtain ⟨w, hw, hx⟩ := terminalCover_expand p
    have hlen : p.length ≤ 2 * W.card := by
      simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.mul_comm]
        using hp.length_lt.le
    have hz := hzero v.1 w (hw.trans (Nat.mul_le_mul_right D hlen))
    simp [hz] at hx
  letI : LinearOrder H.ConnectedComponent := IsWellOrder.linearOrder WellOrderingRel
  let qW (v : W) : Bool := decide (c v false < c v true)
  have hpot (u v : W) (w : G.Walk u.1 v.1) (hw : w.length ≤ D) :
      walkXor a w = (qW u ^^ qW v) := by
    cases hx : walkXor a w with
    | false =>
      have h0 : c u false = c v false := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      have h1 : c u true = c v true := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      simp [qW, h0, h1]
    | true =>
      have h0 : c u false = c v true := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      have h1 : c u true = c v false := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      rcases lt_or_gt_of_ne (hsep v) with hlt | hgt
      · simp [qW, h0, h1, hlt, not_lt_of_gt hlt]
      · simp [qW, h0, h1, hgt, not_lt_of_gt hgt]
  refine ⟨fun v => if hv : v ∈ W then qW ⟨v, hv⟩ else false, ?_⟩
  intro u hu v hv w hw
  simpa only [dif_pos hu, dif_pos hv] using hpot ⟨u, hu⟩ ⟨v, hv⟩ w hw

/-- The terminal assignment needed by buffered parity surgery.  It realizes
exactly the prescribed special edges, and its flip from the old assignment is
constant on terminal pairs joined by a short walk avoiding all special edges. -/
theorem exists_terminal_assignment [Fintype V] {L r : ℕ} {S : Finset (Sym2 V)}
    (p : V → Bool) (hS : ShortSupport G L S) (hs : S.card ≤ (badEdges G p).card)
    (hL : 16 * (badEdges G p).card * (r + 2) ≤ L) :
    ∃ q : V → Bool,
      (∀ u v, G.Adj u v → s(u, v) ∈ badEdges G p ∪ S →
        (q u = q v ↔ s(u, v) ∈ S)) ∧
      (∀ u ∈ ends (badEdges G p ∪ S), ∀ v ∈ ends (badEdges G p ∪ S),
        Near (G.deleteEdges ((badEdges G p ∪ S) : Set (Sym2 V))) {v} (2 * r + 4) u →
          (q u ^^ p u) = (q v ^^ p v)) := by
  classical
  let W := ends (badEdges G p ∪ S)
  let D := 2 * r + 4
  have hW : W.card ≤ 4 * (badEdges G p).card := by
    calc
      W.card ≤ 2 * (badEdges G p ∪ S).card := card_ends_le _
      _ ≤ 2 * ((badEdges G p).card + S.card) :=
        Nat.mul_le_mul_left 2 (Finset.card_union_le _ _)
      _ ≤ 4 * (badEdges G p).card := by omega
  have hbound : 2 * W.card * D ≤ L := by
    calc
      2 * W.card * D ≤ 2 * (4 * (badEdges G p).card) * D :=
        Nat.mul_le_mul_right D (Nat.mul_le_mul_left 2 hW)
      _ = 16 * (badEdges G p).card * (r + 2) := by dsimp [D]; ring
      _ ≤ L := hL
  obtain ⟨q, hq⟩ := exists_potential_on_short_walks (G := G) (twist S) W D
    (fun v w hw => hS.2 v w (hw.trans hbound))
  refine ⟨q, ?_, ?_⟩
  · intro u v huv he
    have huW : u ∈ W := mem_ends_left he
    have hvW : v ∈ W := mem_ends_right he
    have hx := hq u huW v hvW (Walk.cons huv Walk.nil) (by simp [D])
    have hx' : twist S s(u, v) = (q u ^^ q v) := by simpa using hx
    rw [← twist_eq_false_iff, hx']
    cases q u <;> cases q v <;> decide
  · intro u hu v hv hn
    obtain ⟨w, hw⟩ := near_singleton_iff.mp hn
    have hx : walkXor (twist S) w = (p u ^^ p v) := by
      apply walkXor_eq_endpoints p w
      intro x y hxy
      obtain ⟨hxy, he⟩ := SimpleGraph.deleteEdges_adj.mp hxy
      have hnF : s(x, y) ∉ badEdges G p := by
        intro hf
        exact he (Or.inl hf)
      have hnS : s(x, y) ∉ S := by
        intro hs
        exact he (Or.inr hs)
      calc
        twist S s(x, y) = true := twist_of_not_mem hnS
        _ = twist (badEdges G p) s(x, y) := (twist_of_not_mem hnF).symm
        _ = (p x ^^ p y) := twist_badEdges p hxy
    have hq' := hq u hu v hv (w.mapLe (G.deleteEdges_le _)) (by simpa [D] using hw)
    rw [walkXor_mapLe, hx] at hq'
    cases hpu : p u <;> cases hpv : p v <;> cases hqu : q u <;> cases hqv : q v <;>
      simp_all

end E74
