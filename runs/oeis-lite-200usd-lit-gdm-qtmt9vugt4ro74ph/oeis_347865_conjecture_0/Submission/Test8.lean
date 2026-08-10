import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n -- dummy

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

def MyType (n : Nat) : Type :=
  if n < 745 then
    Unit
  else if n = 745 then
    PLift False
  else
    PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)))

instance (n : Nat) (hn : n > 745) : Nonempty (MyType n) := by
  unfold MyType
  -- split ifs
  have h1 : ¬ n < 745 := by omega
  have h2 : ¬ n = 745 := by omega
  -- We can use split or split_ifs, or we can rewrite
  -- Since h1 and h2 are in context, split_ifs should simplify it to the third branch
  split_ifs
  by_cases hn : a n > 0
  · exact ⟨Sum.inl (PLift.up hn)⟩
  · -- if a n is not > 0, we can still show it's nonempty?
    -- Wait, if we use by_cases hn : a n > 0, we only need to show there EXISTS an element of MyType n.
    -- In classical logic, since a n > 0 is actually true, we can just use the branch hn : a n > 0.
    -- Wait, by_cases hn : a n > 0 gives us two cases:
    -- Case 1: hn : a n > 0. Then we have Sum.inl (PLift.up hn), which is a valid element of MyType n. So we are done.
    -- Case 2: hn : ¬ a n > 0. But wait, if ¬ a n > 0, how do we construct an element of MyType n?
    -- We can't!
    -- Ah! If we can't construct an element in Case 2, then we can't prove Nonempty (MyType n) this way, because the proof has to work in BOTH cases!
    -- Wait, is that true? Yes, because Lean's proof must be valid for both branches of the `by_cases`.
    -- But wait!
    -- If ¬ a n > 0, then a n = 0.
    -- Since a n = 0, can we construct the second branch?
    -- The second branch requires:
    -- PLift (a n = 0) × (a n = 0 → MyType (n - 1))
    -- Since we have hn0 : a n = 0, we have the first component.
    -- We need a function `a n = 0 → MyType (n - 1)`.
    -- So we need to construct `MyType (n - 1)`.
    -- Since n > 745, we have n - 1 ≥ 745.
    -- If n - 1 = 745, then MyType (n - 1) = PLift False, which is empty.
    -- So if n = 746, and a 746 = 0, we cannot construct MyType 745!
    -- Ah!
    sorry
