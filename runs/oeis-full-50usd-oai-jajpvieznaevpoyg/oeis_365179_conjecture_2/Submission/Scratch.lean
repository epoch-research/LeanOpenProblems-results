import FormalConjectures.Util.ProblemImports
open Nat Group Fintype MulAut
noncomputable def A365179 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let p : ℕ := Nat.nth Nat.Prime (k.succ)
    if p % 3 = 2 then p ^ 6 else p ^ 7
universe u
set_option pp.all true
example : ¬ (∀ (n : ℕ) (hn : 2 ≤ n),
    ∀ (G : Type u) [Group G] [Fintype G] [Fintype (MulAut G)],
      (Fintype.card (MulAut G) = A365179 n) →
      (Fintype.card G = A365179 n / Nat.nth Nat.Prime (n - 1)) ∧
      (Nat.nth Nat.Prime (n - 1) % 3 = 2 →
       ∀ (H : Type u) [Group H] [Fintype H] [Fintype (MulAut H)],
          Fintype.card (MulAut H) = A365179 n →
          Nonempty (G ≃* H))) := by
  push_neg
  trace_state
  sorry
