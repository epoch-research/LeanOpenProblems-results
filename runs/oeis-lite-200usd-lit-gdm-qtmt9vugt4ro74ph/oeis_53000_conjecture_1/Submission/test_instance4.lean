import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := sorry

inductive MyBox : Type where
  | mk (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyBox

inductive MyBox_bound : Type where
  | mk (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + totient_bound n) : MyBox_bound

inductive MyBox2 : Type where
  | intro (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyBox2
  | dummy : MyBox2

instance : Inhabited MyBox2 := ⟨MyBox2.dummy⟩

def nonempty_box_sum : PSum (Nonempty MyBox) Unit :=
  unsafe (unsafeCast (PSum.inl (Nonempty.intro (MyBox_bound.mk oeis_bound)) : PSum (Nonempty MyBox_bound) Unit) : PSum (Nonempty MyBox) Unit)


partial def get_box2_partial (u : Unit) : MyBox2 :=
  match nonempty_box_sum with
  | PSum.inl h => MyBox2.intro (match Classical.choice h with | MyBox.mk f => f)
  | PSum.inr _ => get_box2_partial u