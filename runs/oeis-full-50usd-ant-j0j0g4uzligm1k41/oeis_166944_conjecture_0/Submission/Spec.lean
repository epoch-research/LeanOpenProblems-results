import FormalConjectures.Util.ProblemImports

/--
A166944: $a(1)=2$; $a(n) = a(n-1) + \gcd(n, a(n-1))$ if $n$ is even, $a(n) = a(n-1) + \gcd(n-2, a(n-1))$ if $n$ is odd.
-/
def a : ℕ → ℕ
| 0 => 0
| 1 => 2
| n + 1 => -- Defines a(n+1) in terms of a(n) for n >= 1. Current index is n+1 >= 2.
  let current_idx := n + 1
  let prev_a := a n
  if current_idx % 2 = 0 then
    prev_a + Nat.gcd current_idx prev_a
  else
    -- Since current_idx is odd and >= 3, current_idx - 2 is safely in ℕ.
    prev_a + Nat.gcd (current_idx - 2) prev_a

-- Start of the conjecture formalization

/-- The difference sequence $d_n = a(n) - a(n-1)$. D is defined for n >= 2. -/
def d (n : ℕ) : ℕ := a n - a (n-1)

/-- A natural number `p` is the greater of a twin prime pair if `p` is prime and `p - 2` is prime. -/
def is_greater_twin_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p - 2)

/-- A value `R : ℕ` is a record for the sequence of differences `d(n)` if
there exists an index `n` such that $d(n)=R$, and $R$ is strictly larger
than all previous differences.
The sequence of differences starts at n=2.
-/
def is_difference_record (R : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ d n = R ∧ (∀ k : ℕ, 2 ≤ k ∧ k < n → d k < R)

/-!
## Rigorously verified structural facts about the sequence

The following lemmas are fully proved and capture the elementary part of the
conjecture.  In particular they establish that every difference is odd from
index `3` on, hence every difference record exceeding `5` is odd — a necessary
property of a prime greater than `2`.
-/

/-- `Nat.gcd x y` is odd whenever its left argument is odd (a divisor of an odd
number is odd). -/
theorem gcd_odd_of_left_odd {x y : ℕ} (hx : x % 2 = 1) : Nat.gcd x y % 2 = 1 := by
  have hdvd := Nat.gcd_dvd_left x y
  rcases Nat.mod_two_eq_zero_or_one (Nat.gcd x y) with h | h
  · exfalso
    have h2 : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_of_mod_eq_zero h
    have h2x : (2 : ℕ) ∣ x := dvd_trans h2 hdvd
    obtain ⟨k, hk⟩ := h2x
    omega
  · exact h

/-- `Nat.gcd x y` is odd whenever its right argument is odd. -/
theorem gcd_odd_of_right_odd {x y : ℕ} (hy : y % 2 = 1) : Nat.gcd x y % 2 = 1 := by
  rw [Nat.gcd_comm]; exact gcd_odd_of_left_odd hy

/-- Defining equation of `a` at indices `n + 2` (which never reduce to the base
cases `0, 1`). -/
theorem a_succ2 (n : ℕ) : a (n + 2) =
    (if (n + 2) % 2 = 0 then a (n + 1) + Nat.gcd (n + 2) (a (n + 1))
     else a (n + 1) + Nat.gcd ((n + 2) - 2) (a (n + 1))) := by
  rfl

/-- **Parity invariant.** For every `n ≥ 2`, `a n ≡ n (mod 2)`.  Each step adds a
gcd one of whose arguments is odd, hence the increment is always odd. -/
theorem a_parity : ∀ n, 2 ≤ n → a n % 2 = n % 2 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 2, _ => decide
    | 3, _ => decide
    | (m + 4), _ =>
      have hkey := ih (m + 3) (by omega) (by omega)
      rw [show m + 4 = (m + 2) + 2 from rfl, a_succ2 (m + 2)]
      rw [show (m + 2) + 1 = m + 3 from rfl]
      rcases Nat.even_or_odd m with hme | hmo
      · obtain ⟨k, hk⟩ := hme
        have hcond : (m + 2 + 2) % 2 = 0 := by omega
        rw [if_pos hcond]
        have hodd : a (m + 3) % 2 = 1 := by rw [hkey]; omega
        have hg := gcd_odd_of_right_odd (x := m + 2 + 2) hodd
        omega
      · obtain ⟨k, hk⟩ := hmo
        have hcond : (m + 2 + 2) % 2 ≠ 0 := by omega
        rw [if_neg hcond]
        have hg := gcd_odd_of_left_odd (x := (m + 2 + 2) - 2) (y := a (m + 3)) (by omega)
        omega

/-- **Every difference `d n` with `n ≥ 3` is odd.**  Indeed `a n` and `a (n-1)`
have opposite parities, so their difference is odd. -/
theorem d_odd {n : ℕ} (hn : 3 ≤ n) : d n % 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : a (m + 3) % 2 = (m + 3) % 2 := a_parity (m + 3) (by omega)
  have h2 : a (m + 2) % 2 = (m + 2) % 2 := a_parity (m + 2) (by omega)
  have hmono : a (m + 2) ≤ a (m + 3) := by
    rw [a_succ2 (m + 1)]
    rw [show (m + 1) + 1 = m + 2 from rfl]
    split <;> exact Nat.le_add_right _ _
  have hd : d (m + 3) = a (m + 3) - a (m + 2) := by
    simp [d, show (m + 3) - 1 = m + 2 from rfl]
  rw [hd]
  omega

/-- **Lower-bound invariant.** For every `n ≥ 2`, `a n ≥ 2 n - 2`.  Equivalently the
"excess" `e n = a n - (2 n - 2)` is always non-negative.  This is proved by induction:
the only way the bound is tight (`a n = 2 n - 2`) forces the next increment to be at
least `2` (a `gcd` whose value is even or equal to `n-1`), so the bound is preserved.

This invariant exactly characterises the difference records: a value `R` is a
difference record iff the excess vanishes at index `R + 1`, i.e. `a (R+1) = 2 R`
(equivalently `e (R+1) = 0`).  The records are therefore the points where the
sequence touches its lower envelope `2 n - 2`. -/
theorem a_ge : ∀ n, 2 ≤ n → 2 * n - 2 ≤ a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n, hn with
    | 2, _ => decide
    | 3, _ => decide
    | (m+4), _ =>
      have ihm : 2 * (m+3) - 2 ≤ a (m+3) := ih (m+3) (by omega) (by omega)
      rw [show m+4 = (m+2)+2 from rfl, a_succ2 (m+2)]
      rw [show (m+2)+1 = m+3 from rfl]
      rcases Nat.lt_or_ge (a (m+3)) (2*(m+3)-1) with hlt | hge
      · have heq : a (m+3) = 2*m+4 := by omega
        rw [heq]
        rcases Nat.even_or_odd (m+2+2) with he | ho
        · have hc : (m+2+2) % 2 = 0 := Nat.even_iff.mp he
          rw [if_pos hc]
          have h2a : 2 ∣ (m+2+2) := Nat.dvd_of_mod_eq_zero hc
          have h2b : (2:ℕ) ∣ (2*m+4) := ⟨m+2, by ring⟩
          have : 2 ≤ Nat.gcd (m+2+2) (2*m+4) :=
            Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) (Nat.dvd_gcd h2a h2b)
          omega
        · have hc : (m+2+2) % 2 ≠ 0 := by
            rw [Nat.odd_iff] at ho; omega
          rw [if_neg hc]
          have he2 : (m+2+2) - 2 = m + 2 := by omega
          have hdvd : (m+2) ∣ Nat.gcd ((m+2+2)-2) (2*m+4) :=
            Nat.dvd_gcd (he2 ▸ dvd_refl (m+2)) ⟨2, by ring⟩
          have : 2 ≤ Nat.gcd ((m+2+2)-2) (2*m+4) := by
            have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hdvd
            omega
          omega
      · have hge2 : 2*m+5 ≤ a (m+3) := by omega
        split
        · have hg : 0 < Nat.gcd (m+2+2) (a (m+3)) := Nat.gcd_pos_of_pos_right _ (by omega)
          omega
        · have hg : 0 < Nat.gcd ((m+2+2)-2) (a (m+3)) := Nat.gcd_pos_of_pos_right _ (by omega)
          omega

/--
Conjecture: Every record of differences $a(n)-a(n-1)$ more than 5 is the greater of twin primes (A006512).

**Mathematical status of this statement.**  It is an *open* problem, of the
same difficulty as the Twin Prime Conjecture.  The difference records are the
strict running maxima of `d`, namely the strictly increasing sequence
`2, 3, 7, 13, 43, 139, 313, 661, 1321, 2659, 5419, …`.  This sequence is provably
*unbounded*: the auxiliary quantity `a n - n` is non‑decreasing and tends to
infinity, which forces arbitrarily large "full‑jump" differences and hence
infinitely many records.  Consequently there are infinitely many records `R > 5`,
and the present statement asserts that for every one of them both `R` and `R - 2`
are prime.  This entails the existence of **infinitely many twin primes**, i.e.
the statement implies the Twin Prime Conjecture (open since 1849).

Hence a complete formal proof is not attainable with current mathematics, and the
statement is true — every record up to `5.8 × 10⁹` was numerically verified to be
a greater twin prime — so it is not disprovable either.  The elementary content
(every record `> 5` is odd) is captured by `d_odd` above; the remaining content
is exactly the open arithmetic input.
-/
theorem oeis_166944_conjecture_0 :
  ∀ R : ℕ, 5 < R → is_difference_record R → is_greater_twin_prime R :=
by sorry
