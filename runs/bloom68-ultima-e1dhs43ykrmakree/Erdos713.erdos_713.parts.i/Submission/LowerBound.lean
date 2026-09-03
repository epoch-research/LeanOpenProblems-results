import FormalConjecturesUtil

/-!
# A linear lower bound for Erdős 713

If a finite simple graph `H` has at least two edges, then
`n / 2 ≤ SimpleGraph.extremalNumber n H` for every `n`.

If `H` has two distinct neighbors at some vertex, use a matching on `n` vertices.
Otherwise, use a star: a graph of maximum degree at most one that copies into a
star can have at most one edge. This proves a partial result, not the full conjecture.
-/

open SimpleGraph

namespace Erdos713

/-- The matching with edges `{0, 1}, {2, 3}, …`, leaving the last vertex isolated
when `n` is odd. -/
private def pairingGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a.val / 2 = b.val / 2 ∧ a.val ≠ b.val
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.2 rfl

private lemma pairingGraph_unique {n : ℕ} {a b c : Fin n}
    (hab : (pairingGraph n).Adj a b) (hac : (pairingGraph n).Adj a c) : b = c := by
  apply Fin.ext
  change a.val / 2 = b.val / 2 ∧ a.val ≠ b.val at hab
  change a.val / 2 = c.val / 2 ∧ a.val ≠ c.val at hac
  omega

open Classical in
private lemma pairingGraph_many_edges (n : ℕ) :
    n / 2 ≤ (pairingGraph n).edgeFinset.card := by
  let l : Fin (n / 2) → Fin n := fun i => ⟨2 * i.val, by have := i.isLt; omega⟩
  let r : Fin (n / 2) → Fin n := fun i => ⟨2 * i.val + 1, by have := i.isLt; omega⟩
  let f : Fin (n / 2) → (pairingGraph n).edgeSet := fun i =>
    ⟨s(l i, r i), by
      change (pairingGraph n).Adj (l i) (r i)
      change (2 * i.val) / 2 = (2 * i.val + 1) / 2 ∧ 2 * i.val ≠ 2 * i.val + 1
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    rcases Sym2.eq_iff.mp (congrArg Subtype.val hij) with h | h
    · apply Fin.ext
      have hval := congrArg Fin.val h.1
      change 2 * i.val = 2 * j.val at hval
      omega
    · have hval := congrArg Fin.val h.1
      change 2 * i.val = 2 * j.val + 1 at hval
      omega
  simpa only [Fintype.card_fin, ← SimpleGraph.edgeFinset_card] using
    Fintype.card_le_of_injective f hf

/-- The star on `n + 1` vertices, centered at `0`. -/
private def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.1 rfl

open Classical in
private lemma starGraph_many_edges (n : ℕ) :
    n ≤ (starGraph n).edgeFinset.card := by
  let f : Fin n → (starGraph n).edgeSet := fun i =>
    ⟨s(0, i.succ), by
      change (starGraph n).Adj 0 i.succ
      exact ⟨(Fin.succ_ne_zero i).symm, Or.inl rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.succ_injective _ (Sym2.congr_right.mp (congrArg Subtype.val hij))
  simpa only [Fintype.card_fin, ← SimpleGraph.edgeFinset_card] using
    Fintype.card_le_of_injective f hf

open Classical in
private lemma starGraph_free {q n : ℕ} (H : SimpleGraph (Fin q))
    (hH : 2 ≤ H.edgeFinset.card)
    (unique : ∀ {a b c}, H.Adj a b → H.Adj a c → b = c) :
    H.Free (starGraph n) := by
  rintro ⟨f⟩
  have hsmall : H.edgeFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he e' he'
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction e' using Sym2.inductionOn with
      | _ c d =>
        have hab : H.Adj a b := (H.mem_edgeSet).mp (mem_edgeFinset.mp he)
        have hcd : H.Adj c d := (H.mem_edgeSet).mp (mem_edgeFinset.mp he')
        rcases (f.toHom.map_adj hab).2 with ha | hb <;>
          rcases (f.toHom.map_adj hcd).2 with hc | hd
        · have hac : a = c := f.injective (ha.trans hc.symm)
          subst c
          rw [unique hab hcd]
        · have had : a = d := f.injective (ha.trans hd.symm)
          subst d
          rw [unique hab hcd.symm]
          exact Sym2.eq_swap
        · have hbc : b = c := f.injective (hb.trans hc.symm)
          subst c
          rw [unique hab.symm hcd]
          exact Sym2.eq_swap
        · have hbd : b = d := f.injective (hb.trans hd.symm)
          subst d
          rw [unique hab.symm hcd.symm]
  omega

open Classical in
/-- A partial result for Erdős 713: forbidding any graph with at least two edges
allows an `n`-vertex graph with at least `n / 2` edges (natural-number division). -/
theorem half_le_extremalNumber {q : ℕ} (H : SimpleGraph (Fin q))
    (hH : 2 ≤ H.edgeFinset.card) (n : ℕ) :
    n / 2 ≤ extremalNumber n H := by
  by_cases h : ∃ a b c, H.Adj a b ∧ H.Adj a c ∧ b ≠ c
  · have hfree : H.Free (pairingGraph n) := by
      rintro ⟨f⟩
      obtain ⟨a, b, c, hab, hac, hbc⟩ := h
      exact hbc (f.injective (pairingGraph_unique
        (f.toHom.map_adj hab) (f.toHom.map_adj hac)))
    have hbound := card_edgeFinset_le_extremalNumber hfree
    simp only [Fintype.card_fin] at hbound
    exact (pairingGraph_many_edges n).trans hbound
  · have unique : ∀ {a b c}, H.Adj a b → H.Adj a c → b = c := by
      intro a b c hab hac
      by_contra hbc
      exact h ⟨a, b, c, hab, hac, hbc⟩
    cases n with
    | zero => simp
    | succ n =>
      have hfree : H.Free (starGraph n) := starGraph_free H hH unique
      have hbound := card_edgeFinset_le_extremalNumber hfree
      simp only [Fintype.card_fin] at hbound
      exact (show (n + 1) / 2 ≤ n by omega).trans
        ((starGraph_many_edges n).trans hbound)

end Erdos713

#print axioms Erdos713.half_le_extremalNumber
