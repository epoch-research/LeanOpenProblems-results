import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A378143: $a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.
-/
noncomputable def A378143 (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }

/-!
## Progress towards the conjecture

The conjecture below holds:
* for `n ≤ 3` because `4 ^ 2 ^ n + 1 ∈ {5, 17, 257, 65537}` is prime;
* for `4 ≤ n ≤ 20` (and `n = 22`) because `10 ^ 2 ^ n + 1` is composite, which we certify in the
  kernel either by an explicit factor, or by failure of the base-3 Fermat test
  (via a verified fast modular exponentiation adapted to exponents `10 ^ M`).

For `n ≥ 21` the statement is a genuinely open problem: it requires (for every `n`
where the Fermat number `F (n+1) = 4 ^ 2 ^ n + 1` and the base-6 generalized Fermat
number `6 ^ 2 ^ n + 1` are composite) that the base-10 generalized Fermat number
`10 ^ 2 ^ n + 1` is composite.  No covering congruence can exist for this sequence
(every odd prime divides `10 ^ 2 ^ n + 1` for at most one `n`), no algebraic or
Aurifeuillian factorisation exists, and the compositeness of all large base-10
generalized Fermat numbers is a problem of the same depth as the finiteness of
Fermat primes, open since Eisenstein (1844).  This open kernel is isolated in
`oeis_378143_composite_tail` below.
-/

/-- Force a natural number to literal form before passing it to a continuation.
This makes kernel reduction of the functions below take linear time, by preventing
the build-up of unreduced thunk chains under call-by-name evaluation. -/
def seqNat (x : ℕ) (k : ℕ → ℕ) : ℕ :=
  Nat.casesOn x (k 0) (fun x' => k (x' + 1))

theorem seqNat_eq (x : ℕ) (k : ℕ → ℕ) : seqNat x k = k x := by
  cases x <;> rfl

/-- One modular tenth-power step: `tenPow m x = x ^ 10 % m`, with forcing. -/
def tenPow (m x : ℕ) : ℕ :=
  seqNat (x * x % m) fun a =>   -- a = x^2
  seqNat (a * a % m) fun b =>   -- b = x^4
  seqNat (b * x % m) fun c =>   -- c = x^5
  c * c % m                     -- x^10

theorem tenPow_eq (m x : ℕ) : tenPow m x = x ^ 10 % m := by
  unfold tenPow
  rw [seqNat_eq, seqNat_eq, seqNat_eq]
  have h1 : x * x % m ≡ x * x [MOD m] := Nat.mod_modEq _ _
  have h2 : x * x % m * (x * x % m) % m ≡ x * x * (x * x) [MOD m] :=
    (Nat.mod_modEq _ _).trans (h1.mul h1)
  have h3 : x * x % m * (x * x % m) % m * x % m ≡ x * x * (x * x) * x [MOD m] :=
    (Nat.mod_modEq _ _).trans (h2.mul_right x)
  have h4 := h3.mul h3
  have h5 : x * x * (x * x) * x * (x * x * (x * x) * x) = x ^ 10 := by ring
  rw [h5] at h4
  exact h4

/-- `iterTenPow m f x = x ^ (10 ^ f) % m`, computed by `f` iterated tenth powers. -/
def iterTenPow (m : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (fun x => x % m)
    (fun _f ih => fun x => seqNat (tenPow m x) fun y => ih y)
    fuel

theorem iterTenPow_zero (m x : ℕ) : iterTenPow m 0 x = x % m := rfl

theorem iterTenPow_succ (m f x : ℕ) :
    iterTenPow m (f + 1) x = iterTenPow m f (tenPow m x) := by
  show seqNat (tenPow m x) (fun y => iterTenPow m f y) = _
  rw [seqNat_eq]

theorem iterTenPow_eq (m : ℕ) :
    ∀ f x : ℕ, iterTenPow m f x = x ^ (10 ^ f) % m := by
  intro f
  induction f with
  | zero => intro x; rw [iterTenPow_zero, pow_zero, pow_one]
  | succ f ih =>
    intro x
    rw [iterTenPow_succ, ih (tenPow m x), tenPow_eq, ← Nat.pow_mod, ← pow_mul, ← pow_succ']

/-- Fermat compositeness certificate for `P` with `P - 1 = 10 ^ M`:
if `3 ^ (P - 1) % P ≠ 1` then `P` is not prime. -/
theorem not_prime_of_fermat_witness10 (P M : ℕ) (hP : 3 < P) (hPe : P - 1 = 10 ^ M)
    (h : iterTenPow P M 3 ≠ 1) : ¬ P.Prime := by
  intro hp
  apply h
  rw [iterTenPow_eq P M 3, ← hPe]
  have hco : Nat.Coprime 3 P := by
    refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr ?_
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hd
    omega
  have ht := Nat.ModEq.pow_totient hco
  rw [Nat.totient_prime hp] at ht
  have h1 : 1 % P = 1 := Nat.mod_eq_of_lt (by omega)
  unfold Nat.ModEq at ht
  rw [h1] at ht
  exact ht

/-- Factor compositeness certificate. -/
theorem not_prime_of_factor (P q : ℕ) (h1 : 1 < q) (h2 : q ≠ P) (hdvd : q ∣ P) :
    ¬ P.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd q hdvd with h | h
  · omega
  · exact h2 h

section Certificates

set_option exponentiation.threshold 5000000
set_option maxRecDepth 10000000

theorem oeis_378143_composite_4 : ¬ Nat.Prime (10 ^ 2 ^ 4 + 1) :=
  not_prime_of_factor _ 353 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_5 : ¬ Nat.Prime (10 ^ 2 ^ 5 + 1) :=
  not_prime_of_factor _ 19841 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_6 : ¬ Nat.Prime (10 ^ 2 ^ 6 + 1) :=
  not_prime_of_factor _ 1265011073 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_7 : ¬ Nat.Prime (10 ^ 2 ^ 7 + 1) :=
  not_prime_of_factor _ 257 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_8 : ¬ Nat.Prime (10 ^ 2 ^ 8 + 1) :=
  not_prime_of_factor _ 10753 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_9 : ¬ Nat.Prime (10 ^ 2 ^ 9 + 1) :=
  not_prime_of_factor _ 1514497 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_10 : ¬ Nat.Prime (10 ^ 2 ^ 10 + 1) := by
  refine not_prime_of_fermat_witness10 (10 ^ 2 ^ 10 + 1) (2 ^ 10)
    (by norm_num) (by norm_num) ?_
  decide +kernel

theorem oeis_378143_composite_11 : ¬ Nat.Prime (10 ^ 2 ^ 11 + 1) := by
  refine not_prime_of_fermat_witness10 (10 ^ 2 ^ 11 + 1) (2 ^ 11)
    (by norm_num) (by norm_num) ?_
  decide +kernel

theorem oeis_378143_composite_12 : ¬ Nat.Prime (10 ^ 2 ^ 12 + 1) :=
  not_prime_of_factor _ 458924033 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_13 : ¬ Nat.Prime (10 ^ 2 ^ 13 + 1) := by
  refine not_prime_of_fermat_witness10 (10 ^ 2 ^ 13 + 1) (2 ^ 13)
    (by norm_num) (by norm_num) ?_
  decide +kernel

theorem oeis_378143_composite_14 : ¬ Nat.Prime (10 ^ 2 ^ 14 + 1) := by
  refine not_prime_of_fermat_witness10 (10 ^ 2 ^ 14 + 1) (2 ^ 14)
    (by norm_num) (by norm_num) ?_
  decide +kernel

theorem oeis_378143_composite_15 : ¬ Nat.Prime (10 ^ 2 ^ 15 + 1) :=
  not_prime_of_factor _ 65537 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_16 : ¬ Nat.Prime (10 ^ 2 ^ 16 + 1) :=
  not_prime_of_factor _ 8257537 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_17 : ¬ Nat.Prime (10 ^ 2 ^ 17 + 1) :=
  not_prime_of_factor _ 175636481 (by norm_num) (by norm_num) (by norm_num)


theorem oeis_378143_composite_18 : ¬ Nat.Prime (10 ^ 2 ^ 18 + 1) :=
  not_prime_of_factor _ 639631361 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_19 : ¬ Nat.Prime (10 ^ 2 ^ 19 + 1) :=
  not_prime_of_factor _ 70254593 (by norm_num) (by norm_num) (by norm_num)

theorem oeis_378143_composite_20 : ¬ Nat.Prime (10 ^ 2 ^ 20 + 1) :=
  not_prime_of_factor _ 167772161 (by norm_num) (by norm_num) (by norm_num)

/-- Compositeness certificate for `n = 22` (outside the contiguous certified range,
since no factor of `10 ^ 2 ^ 21 + 1` below `1.1·10^18` exists (exhaustive search of
all admissible residue classes) and its Fermat test is out of kernel reach). -/
theorem oeis_378143_composite_22 : ¬ Nat.Prime (10 ^ 2 ^ 22 + 1) :=
  not_prime_of_factor _ 101702694862849 (by norm_num) (by norm_num) (by norm_num)

end Certificates

/-- **The open kernel of the conjecture.**  For every `n ≥ 21` (where the primality
status of all three numbers `10 ^ 2 ^ n + 1`, `4 ^ 2 ^ n + 1`, `6 ^ 2 ^ n + 1` is in
general unknown to mathematics), the base-10 generalized Fermat number
`10 ^ 2 ^ n + 1` is composite.  This is a strengthening of the remaining content of
the conjecture, believed true on standard heuristics (the expected number of primes
of this form with `n ≥ 21` is `≈ Σ c·n/2^n ≈ 0`), and verified for all `n` within
computational reach, but as unreachable for current mathematics as the finiteness
of Fermat primes. -/
theorem oeis_378143_composite_tail (m : ℕ) :
    ¬ Nat.Prime (10 ^ 2 ^ (m + 21) + 1) := by
  sorry

/--
The conjecture is equivalent to the claim that a(n) is not 10^(2^n) + 1 for any n,
which in turn is equivalent to the claim that, if 10^(2^n) + 1 is prime,
then either 4^(2^n) + 1 or 6^(2^n) + 1 is prime. - Charles R Greathouse IV, Nov 17 2024
-/
theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  match n with
  | 0 => exact fun _ => Or.inl (by norm_num)
  | 1 => exact fun _ => Or.inl (by norm_num)
  | 2 => exact fun _ => Or.inl (by norm_num)
  | 3 => exact fun _ => Or.inl (by norm_num)
  | 4 => exact fun h => absurd h oeis_378143_composite_4
  | 5 => exact fun h => absurd h oeis_378143_composite_5
  | 6 => exact fun h => absurd h oeis_378143_composite_6
  | 7 => exact fun h => absurd h oeis_378143_composite_7
  | 8 => exact fun h => absurd h oeis_378143_composite_8
  | 9 => exact fun h => absurd h oeis_378143_composite_9
  | 10 => exact fun h => absurd h oeis_378143_composite_10
  | 11 => exact fun h => absurd h oeis_378143_composite_11
  | 12 => exact fun h => absurd h oeis_378143_composite_12
  | 13 => exact fun h => absurd h oeis_378143_composite_13
  | 14 => exact fun h => absurd h oeis_378143_composite_14
  | 15 => exact fun h => absurd h oeis_378143_composite_15
  | 16 => exact fun h => absurd h oeis_378143_composite_16
  | 17 => exact fun h => absurd h oeis_378143_composite_17
  | 18 => exact fun h => absurd h oeis_378143_composite_18
  | 19 => exact fun h => absurd h oeis_378143_composite_19
  | 20 => exact fun h => absurd h oeis_378143_composite_20
  | (m + 21) => exact fun h => absurd h (oeis_378143_composite_tail m)

/-- Greathouse's equivalence: the OEIS conjecture `a(n) ≠ 10^(2^n) + 1 for all n`
is equivalent to the implication form of the conjecture. -/
theorem oeis_378143_equivalence :
    (∀ n : ℕ, A378143 n ≠ 10 ^ 2 ^ n + 1) ↔
      (∀ n : ℕ, Nat.Prime (10 ^ 2 ^ n + 1) →
        Nat.Prime (4 ^ 2 ^ n + 1) ∨ Nat.Prime (6 ^ 2 ^ n + 1)) := by
  constructor
  · -- OEIS form → implication form
    intro hne n h10
    have hA : A378143 n =
        sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 } :=
      rfl
    have hmem10 : (10 : ℕ) ^ 2 ^ n + 1 ∈
        { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 } :=
      ⟨h10, 5, by norm_num, by norm_num⟩
    obtain ⟨haP, p, hp, haeq⟩ := Nat.sInf_mem (Set.nonempty_of_mem hmem10)
    rw [← hA] at haP haeq
    have hle : A378143 n ≤ 10 ^ 2 ^ n + 1 := hA ▸ Nat.sInf_le hmem10
    rcases Nat.lt_or_ge p 7 with hlt | hge
    · have h2p := hp.two_le
      interval_cases p
      · -- p = 2
        left
        have h4 : A378143 n = 4 ^ 2 ^ n + 1 := by rw [haeq]
        rwa [h4] at haP
      · -- p = 3
        right
        have h6 : A378143 n = 6 ^ 2 ^ n + 1 := by rw [haeq]
        rwa [h6] at haP
      · -- p = 4, not prime
        exact absurd hp (by norm_num)
      · -- p = 5
        exact absurd (haeq.trans (by norm_num)) (hne n)
      · -- p = 6, not prime
        exact absurd hp (by norm_num)
    · -- p ≥ 7: (2p)^(2^n) + 1 > 10^(2^n) + 1, contradicting minimality
      exfalso
      have h14 : (14 : ℕ) ^ 2 ^ n ≤ (2 * p) ^ 2 ^ n :=
        Nat.pow_le_pow_left (by omega) _
      have h1014 : (10 : ℕ) ^ 2 ^ n < 14 ^ 2 ^ n :=
        Nat.pow_lt_pow_left (by norm_num) (Nat.pos_of_ne_zero (fun h => by simp at h) |>.ne')
      have hbig : (10 : ℕ) ^ 2 ^ n + 1 < (2 * p) ^ 2 ^ n + 1 :=
        Nat.add_lt_add_right (lt_of_lt_of_le h1014 h14) 1
      rw [← haeq] at hbig
      exact absurd hle (not_le.mpr hbig)
  · -- implication form → OEIS form
    intro himp n ha
    have hA : A378143 n =
        sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 } :=
      rfl
    rcases Set.eq_empty_or_nonempty
        { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 } with
      he | hnonempty
    · rw [hA, he, Nat.sInf_empty] at ha
      exact Nat.add_one_ne_zero _ ha.symm
    · have hmem := Nat.sInf_mem hnonempty
      rw [← hA, ha] at hmem
      obtain ⟨h10, -⟩ := hmem
      have hexp : (2 : ℕ) ^ n ≠ 0 := (Nat.pos_of_ne_zero (fun h => by simp at h)).ne'
      rcases himp n h10 with h4 | h6
      · have hm4 : (4 : ℕ) ^ 2 ^ n + 1 ∈
            { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 } :=
          ⟨h4, 2, by norm_num, by norm_num⟩
        have hle4 : A378143 n ≤ 4 ^ 2 ^ n + 1 := hA ▸ Nat.sInf_le hm4
        rw [ha] at hle4
        have : (4 : ℕ) ^ 2 ^ n < 10 ^ 2 ^ n := Nat.pow_lt_pow_left (by norm_num) hexp
        exact absurd hle4 (not_le.mpr (Nat.add_lt_add_right this 1))
      · have hm6 : (6 : ℕ) ^ 2 ^ n + 1 ∈
            { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 } :=
          ⟨h6, 3, by norm_num, by norm_num⟩
        have hle6 : A378143 n ≤ 6 ^ 2 ^ n + 1 := hA ▸ Nat.sInf_le hm6
        rw [ha] at hle6
        have : (6 : ℕ) ^ 2 ^ n < 10 ^ 2 ^ n := Nat.pow_lt_pow_left (by norm_num) hexp
        exact absurd hle6 (not_le.mpr (Nat.add_lt_add_right this 1))

/-- The OEIS-form of the conjecture: `a(n)` is never `10^(2^n) + 1`.
(Depends on the open kernel through `oeis_378143_conjecture_claim`.) -/
theorem oeis_378143_a_ne_ten (n : ℕ) : A378143 n ≠ 10 ^ 2 ^ n + 1 :=
  oeis_378143_equivalence.mpr oeis_378143_conjecture_claim n
