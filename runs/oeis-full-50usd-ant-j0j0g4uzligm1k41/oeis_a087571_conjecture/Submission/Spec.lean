import FormalConjectures.Util.ProblemImports

open Nat

/--
A087571: Smallest prime which has the form of the concatenation $n, n-1, n-2, n-3, \dots, n-k$ for some $k < n$, or 0 if no such prime exists.
-/
noncomputable def a (n : ℕ) : ℕ :=

  -- Helper function to get the concatenated digits of a list of numbers in MSD-first order.
  let get_all_digits_msf (L : List ℕ) : List ℕ :=
    let to_digits_msb (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse
    -- Concatenates the list of digit lists using foldr, equivalent to List.join (List.map to_digits_msb L).
    List.foldr (fun num acc_digits => (to_digits_msb num) ++ acc_digits) [] L

  -- Helper function to convert a list of digits (MSF) to a number.
  let of_msb_digits (D : List ℕ) : ℕ :=
    D.foldl (fun acc d => acc * 10 + d) 0

  -- The core concatenation logic: n || (n-1) || ... || (n-k)
  let concatenated_number (k : ℕ) : ℕ :=
    -- The list of numbers is `[n, n-1, ..., n-k]`. We ensure subtraction is safe for `i < n`.
    let num_list : List ℕ := List.map (fun i => n - i) (List.range (k + 1))
    of_msb_digits (get_all_digits_msf num_list)

  -- The possible values for k are 0 up to n-1.
  -- List.range n generates [0, 1, ..., n-1].
  let candidates : List ℕ :=
    List.map concatenated_number (List.range n)

  -- Find the smallest prime.
  match List.find? Nat.Prime candidates with
  | some p => p
  | none   => 0

/-- The concatenation `n ‖ (n-1) ‖ … ‖ (n-k)`, matching the internal helper of `a`. -/
def concatN (n k : ℕ) : ℕ :=
  (List.foldr (fun num acc => (Nat.digits 10 num).reverse ++ acc) []
    (List.map (fun i => n - i) (List.range (k + 1)))).foldl (fun acc d => acc * 10 + d) 0

/-- Reduction lemma (unconditional): if some concatenation candidate `concatN n k`
(`k < n`) is prime, then `a n ≠ 0`. -/
theorem a_ne_zero_of_prime_candidate (n k : ℕ) (hk : k < n)
    (hp : Nat.Prime (concatN n k)) : a n ≠ 0 := by
  have hmem : concatN n k ∈ (List.range n).map
      (fun k => (List.foldr (fun num acc => (Nat.digits 10 num).reverse ++ acc) []
        (List.map (fun i => n - i) (List.range (k + 1)))).foldl (fun acc d => acc * 10 + d) 0) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  unfold a
  simp only
  rcases hfind : (List.find? (fun b => decide (Nat.Prime b)) ((List.range n).map
      (fun k => (List.foldr (fun num acc => (Nat.digits 10 num).reverse ++ acc) []
        (List.map (fun i => n - i) (List.range (k + 1)))).foldl (fun acc d => acc * 10 + d) 0)))
      with _ | p
  · exfalso
    exact (List.find?_eq_none.mp hfind (concatN n k) hmem) (by simpa using hp)
  · have hpp : Nat.Prime p := by have := List.find?_some hfind; simpa using this
    exact hpp.ne_zero

/-- The number-theoretic core (OPEN PROBLEM): for every `M` there is a composite `n > M`
such that the concatenation `concat(n, n-1)` is prime.  Equivalently, the thin sequence
`(10^L + 1)·n − 1` (`L = ` number of digits of `n − 1`) contains infinitely many primes
at composite `n`.

This is a genuinely open problem in analytic number theory. Within each decade the values
`(10^L + 1)·n − 1` form an arithmetic progression of common difference `d = 10^L + 1 ≈ √value`
confined to `~0.9·d` terms, so finding a prime is the *least-prime-in-AP problem with modulus
`≈ √x`* — beyond GRH and far beyond Linnik's theorem (modulus `x^{1/5.2}`). Equivalently the
concatenations have density `~√X` (like `n²+1`), making this a Landau-type problem obstructed
by the parity problem. Mathlib provides no quantitative prime-distribution tool (no
Bombieri–Vinogradov, Linnik, or effective primes-in-AP) capable of settling it. -/
theorem exists_composite_concat_prime (M : ℕ) :
    ∃ n, n > M ∧ (n > 1 ∧ ¬ Nat.Prime n) ∧ Nat.Prime (concatN n 1) := by
  sorry

/-- Conjecture; There are infinitely many composite numbers n such that a(n) is nonzero. -/
theorem oeis_a087571_conjecture :
  -- The set of N such that N > 1 and N is composite and a(N) != 0 is infinite.
  ∀ M : ℕ, ∃ n : ℕ, n > M ∧ (n > 1 ∧ ¬ Nat.Prime n) ∧ a n ≠ 0 := by
  intro M
  obtain ⟨n, hgt, hcomp, hp⟩ := exists_composite_concat_prime M
  exact ⟨n, hgt, hcomp, a_ne_zero_of_prime_candidate n 1 hcomp.1 hp⟩
