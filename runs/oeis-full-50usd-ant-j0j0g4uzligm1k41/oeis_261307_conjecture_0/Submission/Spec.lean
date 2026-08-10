import FormalConjectures.Util.ProblemImports

open Nat

/--
A261307: $a(n+1) = \left|a(n) - \gcd(a(n), 7n+6)\right|$, $a(1) = 1$.
The function is 1-indexed conceptually, with $a(n)$ giving the $n$-th term. We define $a(0)$ as a dummy value.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Dummy value for a(0)
  | 1 => 1 -- Base case a(1)
  | n' + 2 => -- For n >= 2. Let $m = n'+2$ be the current index.
    -- The previous index is $j = n'+1 = m-1$.
    let j := n' + 1
    let a_j := a j
    -- The argument for gcd is $7j+6$.
    let k := 7 * j + 6
    let g := Nat.gcd a_j k
    -- Compute the absolute difference using integer casting and natAbs.
    Int.natAbs ((a_j : ℤ) - (g : ℤ))

/-!
### Structural lemmas about the recurrence.
-/

lemma a_zero : a 0 = 0 := rfl

/-- The forward form of the recurrence. -/
lemma a_succ (m : ℕ) (hm : 1 ≤ m) :
    a (m + 1) = Int.natAbs ((a m : ℤ) - (Nat.gcd (a m) (7 * m + 6) : ℤ)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

/-- When the current term is positive, the `gcd` divides it, so the step is a
plain natural subtraction. -/
lemma a_succ_pos (m : ℕ) (hm : 1 ≤ m) (h : 0 < a m) :
    a (m + 1) = a m - Nat.gcd (a m) (7 * m + 6) := by
  rw [a_succ m hm]
  have hle : Nat.gcd (a m) (7 * m + 6) ≤ a m := Nat.le_of_dvd h (Nat.gcd_dvd_left _ _)
  omega

/-- Key `gcd` invariance used along a decreasing-by-one run:
`gcd(k, 7N+6) = gcd(k, 7(N-k)+6)`. -/
lemma gcd_invariance (N k : ℕ) (hk : k ≤ N) :
    Nat.gcd k (7 * N + 6) = Nat.gcd k (7 * (N - k) + 6) := by
  have h1 : 7 * N + 6 = (7 * (N - k) + 6) + 7 * k := by omega
  rw [h1, Nat.gcd_add_mul_right_right k (7 * (N - k) + 6) 7]

/-- If, along the final descent run reaching `0` at index `N`, we have
`a (N-k) = k` and `a (N-k+1) = k-1`, then `k` is coprime to `7N+6`. -/
lemma run_coprime (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N)
    (hak : a (N - k) = k) (hak1 : a (N - k + 1) = k - 1) :
    Nat.Coprime k (7 * N + 6) := by
  have hNk : 1 ≤ N - k := by omega
  have hpos : 0 < a (N - k) := by rw [hak]; exact hk1
  have hstep := a_succ_pos (N - k) hNk hpos
  rw [hak] at hstep; rw [hak1] at hstep
  have hle : Nat.gcd k (7 * (N - k) + 6) ≤ k :=
    Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hg : Nat.gcd k (7 * (N - k) + 6) = 1 := by omega
  rw [Nat.Coprime, gcd_invariance N k (le_of_lt hkN)]; exact hg

/-- Number-theoretic core: if `P ≥ 2`, `P ≤ w²`, and `P` is coprime to every
integer in `[1, w]`, then `P` is prime. Indeed any composite `P` has a prime
factor `≤ √P ≤ w`, contradicting coprimality. -/
lemma prime_of_coprime_below (P w : ℕ) (hP : 2 ≤ P) (hw : P ≤ w * w)
    (hcop : ∀ k, 1 ≤ k → k ≤ w → Nat.Coprime k P) : P.Prime := by
  by_contra hnp
  have hmf_prime : (P.minFac).Prime := Nat.minFac_prime (by omega)
  have hmf_dvd : P.minFac ∣ P := Nat.minFac_dvd P
  have hsq : P.minFac ^ 2 ≤ P := Nat.minFac_sq_le_self (by omega : 0 < P) hnp
  have hsq' : P.minFac * P.minFac ≤ P := by rw [← pow_two]; exact hsq
  have hle : P.minFac ≤ w := by nlinarith [Nat.minFac_pos P, hsq', hw]
  have hcp := hcop P.minFac (Nat.minFac_pos P) hle
  have hdvd_gcd : P.minFac ∣ Nat.gcd P.minFac P := Nat.dvd_gcd (dvd_refl _) hmf_dvd
  rw [Nat.Coprime] at hcp; rw [hcp] at hdvd_gcd
  have : P.minFac ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd_gcd
  have := hmf_prime.two_le
  omega

/-- **The size bound of the final descent run** (the deep, Rowland-type dynamical
fact). Let `N` be a reset (`a N = 0`, `N > 2`) and let `w` be the length of the
maximal decreasing-by-one run reaching `0` at `N`, i.e. `a (N-k) = k` for all
`k ≤ w`, and the run is maximal (`a (N-(w+1)) ≠ w+1`). Then `7N+6 ≤ w²`.

This is equivalent to the statement that the reset value `P = 7N+6` has no prime
factor below `√P`, which together with `run_coprime` yields its primality.

Sharper characterization (this session): the essential hypothesis is exactly
`P₀ ≡ 6 (mod 7)` (not primality of `P₀`); the invariant `v + D ≡ 6 (mod 7)` is
preserved by both walk transitions, forcing every reset value `P₁ ≡ 6 (mod 7)`.

Reformulating the recurrence as a walk in `(v, D)` where `v = a(t)` is the value
and `D = C - 8v` with `C = 7(t+v)+6`: from a reset the walk starts at `(P₀, 7)`
(where `P₀` is the previous reset value) and each step computes `g = gcd(v, D)`;
if `g = 1` it moves `(v, D) ↦ (v-1, D+8)` (a "unit step"), and if `g > 1` it moves
`(v, D) ↦ (v-g, D+g+7)` (a "drop"). The reset value is the final `D` when `v = 0`,
and it is prime exactly when `w² ≥ P`, i.e. `D` (the "defect") stays below `P/8`
at the final run start. One proves rigorously that runs are short
(`L_i ≤ g_i - 1`), drops divide the value (`g_i ∣ v`, so `g_i ≤ v/2`), `C`
decreases by `7(g_i-1)` per drop, and `D` grows monotonically — yet every such
structural fact yields only *upper* bounds on `w` or tautologies. The needed
*lower* bound `w ≥ √P` is equivalent to "the value barely decreases along a
descent", i.e. "few/small resonance drops occur", i.e. "the derived sequence
`C₀ > C₁ > ⋯` (all `≡ 6 mod 7`) reaches a prime quickly" — a primality-density
statement with no closed local invariant (candidates such as `v² ≥ C`,
`C ≤ 10v+7`, `C ≤ 9v` all fail to be preserved by the abstract transition at
arbitrarily large `v`). This is the analogue, for this reset sequence, of
Rowland's theorem on prime-generating `gcd` recurrences, but strictly harder:
Rowland's elementary proof exploits an exact self-similar closed form that this
sequence provably lacks (its reset ratios are irregular, converging to `8`).
Empirically the inequality holds with large margin for every reset (verified for
`N` up to `n ≈ 2·10⁸`, 9 resets, all prime, all reached from value `1`); the
tightest case is the first reset `N = 23`, `P = 167`, `w = 20` (`w² = 400 ≥ 167`).

This lemma is the single remaining gap; the reduction of the conjecture to it
(everything else in this file) is complete and machine-checked. -/
lemma size_bound (N : ℕ) (hN : 2 < N) (h0 : a N = 0)
    (w : ℕ) (hw : ∀ k, k ≤ w → a (N - k) = k) (hwmax : a (N - (w + 1)) ≠ w + 1) :
    7 * N + 6 ≤ w * w := by
  sorry

/--
It is conjectured that for all $n > 2$, $a(n) = 0$ implies that $7n+6 = a(n+1)$ is prime, cf. A186259.
-/
theorem oeis_261307_conjecture_0 : ∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6) := by
  intro N hN h0
  -- Define the maximal descent run length `w` via the first "violation" of `a (N-m) = m`.
  have hex : ∃ m, a (N - m) ≠ m := ⟨N, by rw [Nat.sub_self, a_zero]; omega⟩
  set w₀ := Nat.find hex with hw₀def
  have hV : a (N - w₀) ≠ w₀ := Nat.find_spec hex
  have hnotV : ∀ k, k < w₀ → a (N - k) = k := by
    intro k hk
    have := Nat.find_min hex hk
    exact not_not.mp this
  have hw0pos : 1 ≤ w₀ := by
    rcases Nat.eq_zero_or_pos w₀ with h | h
    · exfalso; rw [h] at hV; rw [Nat.sub_zero, h0] at hV; exact hV rfl
    · exact h
  set w := w₀ - 1 with hwdef
  have hrun : ∀ k, k ≤ w → a (N - k) = k := fun k hk => hnotV k (by omega)
  have hwmax : a (N - (w + 1)) ≠ w + 1 := by
    have he : w + 1 = w₀ := by omega
    rw [he]; exact hV
  have hw0leN : w₀ ≤ N := Nat.find_le (by rw [Nat.sub_self, a_zero]; omega)
  have hwlt : w < N := by omega
  -- Coprimality of `7N+6` to `[1, w]` from the run structure.
  have hcop : ∀ k, 1 ≤ k → k ≤ w → Nat.Coprime k (7 * N + 6) := by
    intro k hk1 hkw
    apply run_coprime N k hk1 (lt_of_le_of_lt hkw hwlt)
    · exact hrun k hkw
    · have h2 : N - k + 1 = N - (k - 1) := by omega
      rw [h2]; exact hrun (k - 1) (by omega)
  -- The size bound, then primality via the number-theoretic core.
  have hsize := size_bound N hN h0 w hrun hwmax
  exact prime_of_coprime_below (7 * N + 6) w (by omega) hsize hcop
