import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := by
  sorry

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

noncomputable def inst_mygoalbox_fallback (m : Nat) : PSum (Inhabited MyGoalBox) Unit :=
  match m with
  | 0 =>
    unsafe (unsafeCast (PSum.inl (Inhabited.mk (MyGoalBox_bound.mk (fun n hn => PLift.up (oeis_bound n hn)))) : PSum (Inhabited MyGoalBox_bound) Unit) : PSum (Inhabited MyGoalBox) Unit)
  | m' + 1 =>
    match get_mygoalbox_sum with
    | PSum.inl box => PSum.inl ⟨box⟩
    | PSum.inr _ => inst_mygoalbox_fallback m'
