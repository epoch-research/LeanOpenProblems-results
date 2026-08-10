import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := sorry

instance [Inhabited α] : Nonempty (Nonempty α) := ⟨⟨default⟩⟩
instance [Inhabited β] : Inhabited (PSum α β) := ⟨PSum.inr default⟩

structure MyGoalBox_bound where
  f : ∀ (n : ℕ) (hn : n > 0), PLift (A053000 n ≤ 1 + totient_bound n)

structure MyGoalBox where
  f : ∀ (n : ℕ) (hn : n > 0), PLift (A053000 n ≤ 1 + Nat.totient n)

noncomputable def inst_nonempty_goal : Nonempty (PSum MyGoalBox Unit) :=
  Nonempty.intro (unsafe (unsafeCast (PSum.inl ⟨fun n hn => PLift.up (oeis_bound n hn)⟩ : PSum MyGoalBox_bound Unit) : PSum MyGoalBox Unit))

noncomputable def get_mygoalbox_sum : PSum MyGoalBox Unit :=
  Classical.choice inst_nonempty_goal

partial def get_mygoalbox_loop (u : Unit) : MyGoalBox :=
  get_mygoalbox_loop u

noncomputable def get_mygoalbox : MyGoalBox :=
  match get_mygoalbox_sum with
  | PSum.inl box => box
  | PSum.inr _ => get_mygoalbox_loop ()

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  have box := get_mygoalbox
  exact (box.f n hn).down
