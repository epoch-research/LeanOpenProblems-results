import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def A365179 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let p : ℕ := Nat.nth Nat.Prime (k.succ)
    if p % 3 = 2 then
      p ^ 6
    else
      p ^ 7

noncomputable def prime_of_index (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

def is_possible_aut_order_power (p m : ℕ) : Prop :=
  (∃ (k : ℕ) (hk : 0 < k), m = p ^ k) ∧
  (∃ (G : Type) (inst_group : Group G) (inst_fintype : Fintype G) (inst_aut_fintype : Fintype (MulAut G)),
    1 < Fintype.card G ∧ Fintype.card (MulAut G) = m)

theorem A365179_conjecture_1 (n : ℕ) (hn : 2 ≤ n) :
  let p := prime_of_index n;
  is_possible_aut_order_power p (A365179 n) ∧
  ∀ m' : ℕ, (is_possible_aut_order_power p m') → (A365179 n) ≤ m' :=
  by sorry

theorem A365179_conjecture_1.disproof : ¬ (type_of% @A365179_conjecture_1) := by sorry
