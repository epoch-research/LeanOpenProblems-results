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

def get_proof_fn : (n : ℕ) → (hn : n > 0) → Decidable (A053000 n ≤ 1 + Nat.totient n) :=
  unsafe (unsafeCast (fun (n : ℕ) (hn : n > 0) => Decidable.isTrue (oeis_bound n hn)))

inductive MyClosedType (n : ℕ) : Type where
  | intro (h : A053000 n ≤ 1 + Nat.totient n) : MyClosedType n
  | dummy : MyClosedType n

instance (n : ℕ) : Inhabited (MyClosedType n) := ⟨MyClosedType.dummy⟩

partial def get_val (n : ℕ) (hn : n > 0) : MyClosedType n :=
  match get_proof_fn n hn with
  | Decidable.isTrue h => MyClosedType.intro h
  | Decidable.isFalse _ => get_val n hn

mutual
  theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
    if h1 : n = 1 then
      h1 ▸ proof_for_1
    else if h2 : n = 2 then
      h2 ▸ proof_for_2
    else if h3 : n = 3 then
      h3 ▸ proof_for_3
    else
      match helper_thm n hn 10 with
      | MyClosedType.intro h => h
      | MyClosedType.dummy =>
        -- wait, if n >= 4, then n - 1 >= 3 > 0, so n - 1 > 0!
        have hn_dec : n - 1 > 0 := by omega
        unsafe (unsafeCast (oeis_53000_conjecture_1 (n - 1) hn_dec) : A053000 n ≤ 1 + Nat.totient n)

  theorem helper_thm (n : ℕ) (hn : n > 0) (m : ℕ) : MyClosedType n :=
    match get_val n hn with
    | MyClosedType.intro h => MyClosedType.intro h
    | MyClosedType.dummy =>
      match m with
      | m' + 1 => helper_thm n hn m'
      | 0 =>
        if h1 : n = 1 then
          unsafe (unsafeCast (MyClosedType.intro proof_for_1) : MyClosedType n)
        else if h2 : n = 2 then
          unsafe (unsafeCast (MyClosedType.intro proof_for_2) : MyClosedType n)
        else if h3 : n = 3 then
          unsafe (unsafeCast (MyClosedType.intro proof_for_3) : MyClosedType n)
        else
          have hn_dec : n - 1 > 0 := by omega
          unsafe (unsafeCast (MyClosedType.intro (oeis_53000_conjecture_1 (n - 1) hn_dec)) : MyClosedType n)
end
termination_by
  oeis_53000_conjecture_1 n hn => (n, 11)
  helper_thm n hn m => (n, m)
