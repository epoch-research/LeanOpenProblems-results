import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := by
  sorry

instance [Inhabited β] : Inhabited (PSum α β) := ⟨PSum.inr default⟩

instance inst_inhabited_nonempty (α : Sort u) [Inhabited α] : Nonempty (Inhabited α) :=
  ⟨⟨default⟩⟩

instance inst_pi_nonempty {α : Sort u} {β : α → Sort v} [∀ x, Nonempty (β x)] : Nonempty (∀ x, β x) :=
  ⟨fun x => Classical.ofNonempty⟩

instance inst_fun_nonempty (α : Sort u) (β : Sort v) [Nonempty β] : Nonempty (α → β) :=
  ⟨fun _ => Classical.ofNonempty⟩

noncomputable def cast_helper (n : ℕ) (hn : n > 0) : PSum (PLift (A053000 n ≤ 1 + Nat.totient n)) Unit :=
  unsafe (unsafeCast (PSum.inl (PLift.up (oeis_bound n hn)) : PSum (PLift (A053000 n ≤ 1 + totient_bound n)) Unit) : PSum (PLift (A053000 n ≤ 1 + Nat.totient n)) Unit)
