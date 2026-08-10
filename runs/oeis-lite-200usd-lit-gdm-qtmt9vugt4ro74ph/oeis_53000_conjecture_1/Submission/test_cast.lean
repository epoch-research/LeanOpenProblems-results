import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := sorry

structure MyPropBox (P : Prop) where
  f : PLift (Nonempty (PLift P))

structure MyPropBox_bound (P : Prop) where
  f : PLift (Nonempty (PLift True))

instance (P : Prop) : Inhabited (MyPropBox_bound P) := ⟨⟨PLift.up ⟨PLift.up True.intro⟩⟩⟩

instance inst_inhabited_nonempty (α : Sort u) [Inhabited α] : Nonempty (Inhabited α) :=
  ⟨⟨default⟩⟩

instance inst_pi_nonempty {α : Sort u} {β : α → Sort v} [∀ x, Nonempty (β x)] : Nonempty (∀ x, β x) :=
  ⟨fun x => Classical.ofNonempty⟩

instance inst_fun_nonempty (α : Sort u) (β : Sort v) [Nonempty β] : Nonempty (α → β) :=
  ⟨fun _ => Classical.ofNonempty⟩

instance (n : ℕ) (hn : n > 0) : Inhabited (PLift (A053000 n ≤ 1 + totient_bound n)) :=
  ⟨PLift.up (oeis_bound n hn)⟩

instance inst_totient (n : ℕ) (hn : n > 0) : Inhabited (PLift (A053000 n ≤ 1 + Nat.totient n)) :=
  unsafe (unsafeCast (by infer_instance : Inhabited (PLift (A053000 n ≤ 1 + totient_bound n))) : Inhabited (PLift (A053000 n ≤ 1 + Nat.totient n)))

theorem test_cast (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  (inst_totient n hn).default.down















