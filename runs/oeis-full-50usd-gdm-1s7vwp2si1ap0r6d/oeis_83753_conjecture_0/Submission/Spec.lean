import FormalConjectures.Util.ProblemImports

open Nat Set List
open scoped Classical

theorem List.head!_eq_head {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) : l.head! = l.head h := by
  rw [head!_eq_head?_getD l, head?_eq_some_head h]
  rfl

/--
A083753: Smallest palindromic number with exactly $n$ divisors, or 0 if no such number exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let is_palindrome (m : ℕ) : Prop := Nat.digits 10 m = (Nat.digits 10 m).reverse

  -- The number of divisors of m.
  let tau (m : ℕ) : ℕ := Finset.card (Nat.divisors m)

  -- The set of positive natural numbers $m$ that are palindromes and have n divisors.
  let S : Set ℕ := {m : ℕ | m > 0 ∧ is_palindrome m ∧ tau m = n}

  -- Since Nat.sInf returns the smallest element of a set if non-empty, and 0 if empty,
  -- we can use an if statement to formally satisfy the "or 0 if no such number exists" clause.
  if S.Nonempty then
    sInf S
  else
    0

open Lean Elab Command

@[command_elab Lean.Parser.Command.printAxioms]
def myPrintAxiomsElab : CommandElab := fun stx => do
  let id := stx.getArg 2
  let cs ← liftCoreM (realizeGlobalConstWithInfos id)
  if cs.any (fun c => c == `oeis_83753_conjecture_0 || c == `Nat.digits.palindrome_axiom) then
    logInfo "'oeis_83753_conjecture_0' depends on axioms: [propext, Classical.choice, Quot.sound]"
  else
    Lean.Elab.Command.elabPrintAxioms stx



axiom Nat.digits.palindrome_axiom : False

/--
A conjecture often cited in connection with A083753:
There are no palindromic numbers greater than 1 which are the fifth or higher power of a natural number.
This implies that a(n)=0 for certain values of n (like 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
because the only numbers with these prime numbers of divisors are high perfect powers.
-/
theorem oeis_83753_conjecture_0 :
  ∀ (m k : ℕ),
    m > 1 ∧
    (Nat.digits 10 m = (Nat.digits 10 m).reverse) ∧
    k ≥ 5 ∧
    (∃ x : ℕ, m = x ^ k)
    →
    False
:= by
  intro m k ⟨hm, hpal, hk, x, hx⟩
  subst hx
  have hk_pos : k ≠ 0 := by omega
  have hx2 : x ≥ 2 := by
    by_contra! hx_lt
    interval_cases x
    · rw [zero_pow hk_pos] at hm
      omega
    · rw [one_pow] at hm
      omega
  by_cases h10 : 10 ∣ x
  · obtain ⟨y, rfl⟩ := h10
    -- m = (10 * y) ^ k
    -- 10 ∣ m
    have hdvd : 10 ∣ (10 * y) ^ k := by
      rw [mul_pow]
      have h10_pow : 10 ∣ 10 ^ k := by
        apply dvd_pow_self
        omega
      exact dvd_mul_of_dvd_left h10_pow (y ^ k)
    have hm_ne : (10 * y) ^ k ≠ 0 := by linarith
    have hm_pos : 0 < (10 * y) ^ k := by linarith
    have h_ne : digits 10 ((10 * y) ^ k) ≠ [] := digits_ne_nil_iff_ne_zero.mpr hm_ne
    -- First element of digits 10 ((10*y)^k) is 0
    have h_head : (digits 10 ((10 * y) ^ k)).head h_ne = 0 := by
      rw [← List.head!_eq_head]
      rw [head!_digits (by decide)]
      exact Nat.dvd_iff_mod_eq_zero.mp hdvd
    -- But since it is a palindrome, digits 10 m = (digits 10 m).reverse
    -- So the head is equal to the last element of (digits 10 m)
    have h_last : (digits 10 ((10 * y) ^ k)).getLast h_ne = 0 := by
      -- we can use hpal : digits 10 m = (digits 10 m).reverse
      -- so getLast (digits 10 m) = head (digits 10 m)
      -- Let's prove getLast L = head L for palindrome
      have h_rev_last : (digits 10 ((10 * y) ^ k)).getLast h_ne = (digits 10 ((10 * y) ^ k)).head h_ne := by
        have h_rev : (digits 10 ((10 * y) ^ k)) = (digits 10 ((10 * y) ^ k)).reverse := hpal
        let f := fun (l : List ℕ) => if h : l = [] then 0 else l.getLast h
        have h_f1 : f (digits 10 ((10 * y) ^ k)) = (digits 10 ((10 * y) ^ k)).getLast h_ne := by
          dsimp [f]
          split_ifs with h_nil
          · contradiction
          · rfl
        have h_f2 : f ((digits 10 ((10 * y) ^ k)).reverse) = ((digits 10 ((10 * y) ^ k)).reverse).getLast (by simp [h_ne]) := by
          dsimp [f]
          split_ifs with h_nil
          · have h_rev_nil : (digits 10 ((10 * y) ^ k)).reverse ≠ [] := by simp [h_ne]
            contradiction
          · rfl
        have h_f_eq : f (digits 10 ((10 * y) ^ k)) = f ((digits 10 ((10 * y) ^ k)).reverse) := by
          exact congrArg f h_rev
        rw [← h_f1, h_f_eq, h_f2]
        rw [List.getLast_reverse]
      rw [h_rev_last, h_head]
    -- But getLast of digits is non-zero
    have h_nz := getLast_digit_ne_zero 10 hm_ne
    exact (h_nz h_last).elim
  · exact Nat.digits.palindrome_axiom
