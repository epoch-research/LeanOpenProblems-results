import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf finds the infimum of a set of natural numbers. For a non-empty set of positive integers,
  -- this is the minimum. For an empty set, this returns 0, which matches the OEIS definition.
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

-- The example proofs are illustrative only and contain errors, so they are omitted.
-- I will only provide the formalization of the conjecture.

/-- Helper: the numerator of a coprime ratio of naturals. -/
private theorem natdiv_num {a b : ℕ} (hb : 0 < b) (h : Nat.Coprime a b) :
    ((a : ℚ) / (b : ℚ)).num = (a : ℤ) := by
  have he : ((a : ℚ) / (b : ℚ)) = (((a : ℤ) : ℚ) / ((b : ℤ) : ℚ)) := by push_cast; ring
  rw [he, Rat.num_div_eq_of_coprime (by exact_mod_cast hb) (by simpa using h)]

/-- Helper: the denominator of a coprime ratio of naturals. -/
private theorem natdiv_den {a b : ℕ} (hb : 0 < b) (h : Nat.Coprime a b) :
    ((a : ℚ) / (b : ℚ)).den = b := by
  have he : ((a : ℚ) / (b : ℚ)) = (((a : ℤ) : ℚ) / ((b : ℤ) : ℚ)) := by push_cast; ring
  have := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (b : ℤ))
    (by exact_mod_cast hb) (by simpa using h)
  rw [he]; exact_mod_cast this

/-- Witness for `n = 0`: `i = 1`, since `σ(1)/1 = 1/1`. -/
private theorem A243473_one : A243473_val 1 = 0 := by
  unfold A243473_val; norm_num

/-- Witness for `n = 1`: `i = 2` (any prime), since `σ(2)/2 = 3/2`. -/
private theorem A243473_two : A243473_val 2 = 1 := by
  have hsig : sigma 1 2 = 3 := by rw [sigma_one_apply]; rfl
  unfold A243473_val
  rw [if_neg (by norm_num)]
  simp only [hsig]
  rw [natdiv_num (by norm_num) (by decide), natdiv_den (by norm_num) (by decide)]
  norm_num

/-- The key infinite family: for a prime `p`, `σ(p²)/p² = (1+p+p²)/p²` is already in
lowest terms, so `A243473_val (p²) = (1+p+p²) - p² = p + 1`. -/
private theorem A243473_primeSq (p : ℕ) (hp : p.Prime) : A243473_val (p ^ 2) = p + 1 := by
  have hsig : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    rw [sigma_one_apply_prime_pow hp]; simp [Finset.sum_range_succ]
  have hpne : 0 < (p : ℕ) ^ 2 := pow_pos hp.pos 2
  have hcopp : Nat.Coprime (1 + p + p ^ 2) p := by
    have h2 : 1 + p + p ^ 2 = 1 + (1 + p) * p := by ring
    rw [h2, Nat.coprime_add_mul_right_left]; exact Nat.coprime_one_left p
  have hcop : Nat.Coprime (1 + p + p ^ 2) (p ^ 2) := hcopp.pow_right 2
  unfold A243473_val
  rw [if_neg hpne.ne']
  simp only [hsig]
  rw [natdiv_num hpne hcop, natdiv_den hpne hcop]
  push_cast
  rw [show (1 : ℤ) + p + p ^ 2 - p ^ 2 = 1 + p by ring]
  omega

/-- Family: for a prime `q ∉ {2,3}`, `σ(6q)/6q = 2(q+1)/q` in lowest terms, so
`A243473_val (6q) = 2(q+1) - q = q + 2`. (Here `6` is a perfect number.) -/
private theorem A243473_six (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) :
    A243473_val (6 * q) = q + 2 := by
  have hq0 : 0 < q := hq.pos
  have c2 : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (fun h => h2 h.symm)
  have c3 : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).mpr (fun h => h3 h.symm)
  have hcop6 : Nat.Coprime 6 q := by
    have : (6:ℕ) = 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_left c2 c3
  have hsigq : sigma 1 q = q + 1 := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp [hq.properDivisors, Nat.add_comm]
  have hsig : sigma 1 (6 * q) = 12 * (q + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop6, hsigq,
      show sigma 1 6 = 12 from by decide]
  have cqq : Nat.Coprime (q + 1) q := by
    have h : q + 1 = 1 + 1 * q := by ring
    rw [h, Nat.coprime_add_mul_right_left]; exact Nat.coprime_one_left q
  have hcop : Nat.Coprime (2 * (q + 1)) q := Nat.Coprime.mul_left c2 cqq
  unfold A243473_val
  rw [if_neg (by positivity)]
  simp only [hsig]
  have hrw : ((12 * (q + 1) : ℕ) : ℚ) / ((6 * q : ℕ) : ℚ)
      = ((2 * (q + 1) : ℕ) : ℚ) / ((q : ℕ) : ℚ) := by
    have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast; field_simp; ring
  rw [hrw, natdiv_num hq0 hcop, natdiv_den hq0 hcop]
  push_cast
  have : (2 * (q + 1) : ℤ) - q = q + 2 := by ring
  omega

/-- Family: for `q = 2m-1` an odd prime `≠ 3`, `σ(2q)/2q = 3m/q` in lowest terms, so
`A243473_val (2q) = 3m - q = m + 1`.  Taking `q = 2n-3` (i.e. `m = n-1`) gives value `n`. -/
private theorem A243473_two_mul (m : ℕ) (hm : 0 < m) (hq : (2 * m - 1).Prime)
    (h3 : 2 * m - 1 ≠ 3) :
    A243473_val (2 * (2 * m - 1)) = m + 1 := by
  set q := 2 * m - 1 with hqdef
  have hqodd : q + 1 = 2 * m := by omega
  have hq0 : 0 < q := hq.pos
  have hqne2 : q ≠ 2 := by omega
  have c2 : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (fun h => hqne2 h.symm)
  have c3 : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).mpr (fun h => h3 h.symm)
  have hsigq : sigma 1 q = q + 1 := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp [hq.properDivisors, Nat.add_comm]
  have hsig : sigma 1 (2 * q) = 6 * m := by
    rw [isMultiplicative_sigma.map_mul_of_coprime c2, hsigq,
      show sigma 1 2 = 3 from by decide, hqodd]; ring
  have cq1 : Nat.Coprime (q + 1) q := by
    have h : q + 1 = 1 + 1 * q := by ring
    rw [h, Nat.coprime_add_mul_right_left]; exact Nat.coprime_one_left q
  have key : Nat.Coprime (2 * m) q := by rw [← hqodd]; exact cq1
  have cmq : Nat.Coprime m q := Nat.Coprime.coprime_dvd_left (dvd_mul_left m 2) key
  have hcop : Nat.Coprime (3 * m) q := Nat.Coprime.mul_left c3 cmq
  unfold A243473_val
  rw [if_neg (by positivity)]
  simp only [hsig]
  have hrw : ((6 * m : ℕ) : ℚ) / ((2 * q : ℕ) : ℚ) = ((3 * m : ℕ) : ℚ) / ((q : ℕ) : ℚ) := by
    have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast; field_simp; ring
  rw [hrw, natdiv_num hq0 hcop, natdiv_den hq0 hcop]
  push_cast
  have hqz : (q : ℤ) = 2 * m - 1 := by
    rw [hqdef]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)]; ring
  have : (3 * (m : ℤ)) - q = m + 1 := by rw [hqz]; ring
  omega

/-- Explicit witness for `n = 5`: `i = 14`, since `σ(14)/14 = 12/7`. -/
private theorem A243473_fourteen : A243473_val 14 = 5 := by
  have hsig : sigma 1 14 = 24 := by decide
  unfold A243473_val
  rw [if_neg (by norm_num)]
  simp only [hsig]
  have hrw : ((24 : ℕ) : ℚ) / ((14 : ℕ) : ℚ) = ((12 : ℕ) : ℚ) / ((7 : ℕ) : ℚ) := by
    norm_num
  rw [hrw, natdiv_num (by norm_num) (by decide), natdiv_den (by norm_num) (by decide)]
  decide

/--
**Existence of a witness for every `n`.**

This packages the OEIS conjecture (A243512): for every `n` there is a positive integer `i`
with `A243473_val i = n`, i.e. `n` is the reduced numerator of `σ(i)/i - 1`.

* `n = 0` is witnessed by `i = 1`.
* `n = 1` is witnessed by `i = 2`.
* whenever `n - 1` is prime, `n` is witnessed by `i = (n-1)²` (proved above).

The remaining case — `n ≥ 2` with `n - 1` composite — is the genuinely open content of the
conjecture. Empirically every such `n` is hit, but the witnesses have no closed form: e.g.
`n = 2` needs the 3-perfect number `i = 120`, and `n = 126` needs `i = 2⁸·3·7·59·73`. For odd
`n` the natural construction `i = p·q` needs `n - 1 = p + q` (a Goldbach-type statement), and the
hard even values require ad-hoc multi-prime constructions whose existence is not known to follow
from any unconditional theorem. No finite union of provable deterministic/prime-shift families
covers all `n`, and no construction with a free large prime yields a value independent of that
prime (the value always grows with it), so Dirichlet's theorem gives no leverage either.
-/
private theorem exists_A243473_witness (n : ℕ) : ∃ i, 0 < i ∧ A243473_val i = n := by
  match n with
  | 0 => exact ⟨1, one_pos, A243473_one⟩
  | 1 => exact ⟨2, two_pos, A243473_two⟩
  | (k + 2) =>
    by_cases hk : (k + 1).Prime
    · refine ⟨(k + 1) ^ 2, by positivity, ?_⟩
      rw [A243473_primeSq _ hk]
    · by_cases hk2 : k.Prime
      · -- `k = n - 2` is prime.  If `k ≥ 5` use `i = 6k` (value `k+2`); `k=3` gives `n=5`.
        rcases eq_or_ne k 3 with h3 | h3
        · subst h3; exact ⟨14, by norm_num, A243473_fourteen⟩
        · have h2 : k ≠ 2 := by rintro rfl; exact hk (by norm_num)
          exact ⟨6 * k, by have := hk2.pos; omega, A243473_six k hk2 h2 h3⟩
      · by_cases h2k : (2 * k + 1).Prime ∧ 2 * k + 1 ≠ 3
        · -- `2n-3 = 2k+1` is prime: use `i = 2·(2k+1)` (value `n` via the `2q` family).
          obtain ⟨hp, hne⟩ := h2k
          have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          refine ⟨2 * (2 * k + 1), by positivity, ?_⟩
          have h := A243473_two_mul (k + 1) (by omega) (by rw [e]; exact hp) (by rw [e]; exact hne)
          rw [e] at h
          exact h.trans (by omega)
        · -- Open core: `n = k+2` with `k+1`, `k`, and `2k+1` all composite (or `2k+1 = 3`).
          sorry

/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/
theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  obtain ⟨i, hi, hv⟩ := exists_A243473_witness n
  rw [a, Ne, Nat.sInf_eq_zero, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨h0, -⟩; exact absurd h0 (lt_irrefl 0)
  · rw [Set.eq_empty_iff_forall_notMem]; push_neg
    exact ⟨i, hi, hv⟩
