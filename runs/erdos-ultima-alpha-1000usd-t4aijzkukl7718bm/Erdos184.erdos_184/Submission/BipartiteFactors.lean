import FormalConjecturesUtil

/-! Explicit cycle factors for balanced complete bipartite graphs. -/

open SimpleGraph
open scoped Fin.NatCast
namespace Erdos184Bipartite

variable {n : ℕ} [NeZero n]

def matchingPair (t : Fin n) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj
    | .inl a, .inr b => b = a + t ∨ b = a + t + 1
    | .inr b, .inl a => b = a + t ∨ b = a + t + 1
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> simp
  loopless := by intro a; cases a <;> simp

lemma matchingPair_le (t : Fin n) : matchingPair t ≤ completeBipartiteGraph (Fin n) (Fin n) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [matchingPair]

lemma matchingPair_left_step (t a : Fin n) :
    (matchingPair t).Reachable (.inl a) (.inl (a + 1)) := by
  have h₁ : (matchingPair t).Adj (.inl a) (.inr (a + t + 1)) := Or.inr rfl
  have h₂ : (matchingPair t).Adj (.inr (a + t + 1)) (.inl (a + 1)) := by
    exact Or.inl (by abel)
  exact h₁.reachable.trans h₂.reachable

lemma matchingPair_connected (t : Fin n) : (matchingPair t).Connected := by
  have hNat : ∀ k : ℕ, (matchingPair t).Reachable (.inl 0) (.inl (k : Fin n)) := by
    intro k
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using ih.trans (matchingPair_left_step t (k : Fin n))
  have hLeft : ∀ a : Fin n, (matchingPair t).Reachable (.inl 0) (.inl a) := by
    intro a
    simpa only [Fin.cast_val_eq_self] using hNat a.val
  have hRoot : ∀ v, (matchingPair t).Reachable (.inl 0) v := by
    intro v
    cases v with
    | inl a => exact hLeft a
    | inr b =>
      have hEdge : (matchingPair t).Adj (.inl (b - t)) (.inr b) := by
        exact Or.inl (by abel)
      exact (hLeft (b - t)).trans hEdge.reachable
  exact ⟨fun a b => (hRoot a).symm.trans (hRoot b)⟩

open scoped Classical in
lemma matchingPair_regular (hn : 2 ≤ n) (t : Fin n) :
    (matchingPair t).IsRegularOfDegree 2 := by
  classical
  have h10 : (1 : Fin n) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)] at hval
    omega
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl a =>
    have hneigh : (matchingPair t).neighborFinset (.inl a) =
        {Sum.inr (a + t), Sum.inr (a + t + 1)} := by
      ext b
      cases b <;> simp [SimpleGraph.mem_neighborFinset, matchingPair]
    rw [hneigh, Finset.card_pair]
    intro heq
    have h := Sum.inr_injective heq
    exact h10 (add_eq_left.mp h.symm)
  | inr b =>
    have hneigh : (matchingPair t).neighborFinset (.inr b) =
        {Sum.inl (b - t), Sum.inl (b - t - 1)} := by
      ext a
      cases a with
      | inl a =>
        simp only [SimpleGraph.mem_neighborFinset, matchingPair,
          Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
        constructor
        · rintro (h | h)
          · exact Or.inl (by rw [h]; abel)
          · exact Or.inr (by rw [h]; abel)
        · rintro (rfl | rfl)
          · exact Or.inl (by abel)
          · exact Or.inr (by abel)
      | inr a => simp [SimpleGraph.mem_neighborFinset, matchingPair]
    rw [hneigh, Finset.card_pair]
    intro heq
    have h := Sum.inl_injective heq
    exact h10 (sub_eq_self.mp h.symm)


def evenOffset (m : ℕ) (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

lemma evenOffset_val (m : ℕ) (i : Fin m) : (evenOffset m i).val = 2 * i.val := rfl

lemma evenOffset_succ_val (m : ℕ) [NeZero m] (i : Fin m) :
    (evenOffset m i + 1).val = 2 * i.val + 1 := by
  have hm : 0 < m := NeZero.pos m
  have hi := i.isLt
  rw [Fin.val_add, evenOffset_val, Fin.val_one',
    Nat.mod_eq_of_lt (show 1 < 2 * m by omega), Nat.mod_eq_of_lt (by omega)]

lemma matchingPair_evenOffset_adj (m : ℕ) [NeZero m] (i : Fin m) (a b : Fin (2 * m)) :
    (matchingPair (evenOffset m i)).Adj (.inl a) (.inr b) ↔ (b - a).val / 2 = i.val := by
  constructor
  · rintro (h | h)
    · have heq : b - a = evenOffset m i := by rw [h]; abel
      rw [heq, evenOffset_val]
      omega
    · have heq : b - a = evenOffset m i + 1 := by rw [h]; abel
      rw [heq, evenOffset_succ_val]
      omega
  · intro h
    have hval : (b - a).val = 2 * i.val ∨ (b - a).val = 2 * i.val + 1 := by omega
    rcases hval with h | h
    · have heq : b - a = evenOffset m i := Fin.ext h
      exact Or.inl (by rw [← heq]; abel)
    · have heq : b - a = evenOffset m i + 1 := by
        apply Fin.ext
        rwa [evenOffset_succ_val]
      exact Or.inr (by rw [add_assoc, ← heq]; abel)

lemma matchingPair_evenOffset_unique (m : ℕ) [NeZero m] (i j : Fin m)
    (a b : Fin (2 * m))
    (hi : (matchingPair (evenOffset m i)).Adj (.inl a) (.inr b))
    (hj : (matchingPair (evenOffset m j)).Adj (.inl a) (.inr b)) : i = j := by
  apply Fin.ext
  exact ((matchingPair_evenOffset_adj m i a b).mp hi).symm.trans
    ((matchingPair_evenOffset_adj m j a b).mp hj)

lemma matchingPair_evenOffset_exists (m : ℕ) [NeZero m] (a b : Fin (2 * m)) :
    ∃ i : Fin m, (matchingPair (evenOffset m i)).Adj (.inl a) (.inr b) := by
  have hd := (b - a).isLt
  let i : Fin m := ⟨(b - a).val / 2, by omega⟩
  exact ⟨i, (matchingPair_evenOffset_adj m i a b).mpr rfl⟩

#print axioms matchingPair_evenOffset_exists

#print axioms matchingPair_connected
#print axioms matchingPair_regular
end Erdos184Bipartite
