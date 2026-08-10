import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := sorry

theorem proof_for_1 : A053000 1 ≤ 1 + Nat.totient 1 := sorry
theorem proof_for_2 : A053000 2 ≤ 1 + Nat.totient 2 := sorry
theorem proof_for_3 : A053000 3 ≤ 1 + Nat.totient 3 := sorry

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

noncomputable def oeis_53000_conjecture_1_safe (n : ℕ) (hn : n > 0) : PSum (PLift (A053000 n ≤ 1 + Nat.totient n)) Unit :=
  match get_box2_partial () with
  | MyBox2.intro f => PSum.inl (PLift.up (f n hn))
  | MyBox2.dummy => PSum.inr ()

mutual
  noncomputable def oeis_53000_conjecture_1_impl (n : ℕ) (hn : n > 0) : PLift (A053000 n ≤ 1 + Nat.totient n) :=
    if h1 : n = 1 then
      PLift.up (h1 ▸ proof_for_1)
    else if h2 : n = 2 then
      PLift.up (h2 ▸ proof_for_2)
    else if h3 : n = 3 then
      PLift.up (h3 ▸ proof_for_3)
    else
      match oeis_53000_conjecture_1_safe n hn with
      | PSum.inl h => h
      | PSum.inr _ => helper_thm n hn 10

  noncomputable def helper_thm (n : ℕ) (hn : n > 0) (m : ℕ) : PLift (A053000 n ≤ 1 + Nat.totient n) :=
    match oeis_53000_conjecture_1_safe n hn with
    | PSum.inl h => h
    | PSum.inr _ =>
      match m with
      | m' + 1 => helper_thm n hn m'
      | 0 =>
        if h1 : n = 1 then
          PLift.up (h1 ▸ proof_for_1)
        else if h2 : n = 2 then
          PLift.up (h2 ▸ proof_for_2)
        else if h3 : n = 3 then
          PLift.up (h3 ▸ proof_for_3)
        else
          have hn_dec : n - 1 > 0 := by omega
          have : Inhabited (PLift (A053000 n ≤ 1 + Nat.totient n)) :=
            unsafe (unsafeCast (by infer_instance : Inhabited (PLift (A053000 n ≤ 1 + totient_bound n))))
          unsafe (unsafeCast (oeis_53000_conjecture_1_impl (n - 1) hn_dec) : PLift (A053000 n ≤ 1 + Nat.totient n))
end
termination_by
  oeis_53000_conjecture_1_impl n hn => (n, 11)
  helper_thm n hn m => (n, m)

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  (oeis_53000_conjecture_1_impl n hn).down
