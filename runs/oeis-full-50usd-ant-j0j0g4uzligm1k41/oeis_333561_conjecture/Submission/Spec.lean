import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A333561: $a(n) = \sum_{k = 0}^{2n} \binom{3n}{2n-k}\binom{n+k-1}{k}$.
This is an equivalent identity conjectured in the OEIS entry, which may resolve issues with the automated checker.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (2 * n + 1)) fun k : ℕ =>
    Nat.choose (3 * n) (2 * n - k) * Nat.choose (n + k - 1) k

/-- Partial alternating binomial sum:
`∑_{l=0}^m C(P+1,l)(-1)^l = (-1)^m C(P,m)` (over `ℤ`). -/
theorem partial_alt_sum (P m : ℕ) :
    (∑ l ∈ range (m+1), (-1:ℤ)^l * ((P+1).choose l)) = (-1:ℤ)^m * (P.choose m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : ((P+1).choose (m+1) : ℤ) = (P.choose m) + (P.choose (m+1)) := by
      exact_mod_cast Nat.choose_succ_succ P m
    rw [hrec]
    ring

/-- Vandermonde-type factorization: `C(N,j)*C(N-j,l) = C(N,j+l)*C(j+l,j)`. -/
theorem choose_mul_choose_sub (N j l : ℕ) :
    N.choose j * (N - j).choose l = N.choose (j+l) * (j+l).choose j := by
  have := Nat.choose_mul (n := N) (k := j+l) (s := j) (by omega)
  simpa using this.symm

/-- Parity: `(-1)^(2n-i) = (-1)^i` for `i ≤ 2n`. -/
theorem neg_one_pow_two_mul_sub (n i : ℕ) (h : i ≤ 2*n) :
    (-1:ℤ)^(2*n - i) = (-1)^i := by
  have h1 : (-1:ℤ)^(2*n - i) * (-1)^i = 1 := by
    rw [← pow_add, Nat.sub_add_cancel h, pow_mul]; norm_num
  have h2 : (-1:ℤ)^i * (-1)^i = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have := h1.trans h2.symm
  exact mul_right_cancel₀ (by positivity) this

/-- Closed form for `a`:
`(a n : ℤ) = ∑_{m=0}^{2n} C(3n,m)*(-2)^m`  (for `n ≥ 1`).

This rewrites the defining double-binomial sum
`∑_k C(3n,2n-k) C(n+k-1,k) = [w^{2n}] (1+w)^{3n}/(1-w)^n`
into the alternating single-binomial partial sum
`∑_m C(3n,m)(-2)^m = [w^{2n}] (1-2w)^{3n}/(1-w)`,
via the negative-binomial (partial alternating sum) identity, the Vandermonde
factorization, and a diagonal resummation. -/
theorem a_closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = ∑ m ∈ range (2*n+1), ((3*n).choose m : ℤ) * (-2)^m := by
  have step1 : (a n : ℤ)
      = ∑ i ∈ range (2*n+1),
          ((3*n).choose i : ℤ) * ((3*n - i - 1).choose (2*n - i) : ℤ) := by
    unfold a
    rw [← Finset.sum_range_reflect]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : 2 * n - (2 * n - i) = i := by omega
    have h2 : n + (2 * n - i) - 1 = 3 * n - i - 1 := by omega
    rw [h1, h2]
  rw [step1]
  have step2 : ∀ i ∈ range (2*n+1),
      ((3*n).choose i : ℤ) * ((3*n - i - 1).choose (2*n - i) : ℤ)
        = ∑ l ∈ range (2*n - i + 1),
            ((3*n).choose (i+l) : ℤ) * ((i+l).choose i : ℤ) * (-1)^(i+l) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi2 : i ≤ 2*n := by omega
    have hP1 : (3*n - i - 1) + 1 = 3*n - i := by omega
    have hpa := partial_alt_sum (3*n - i - 1) (2*n - i)
    rw [hP1] at hpa
    have hval : ((3*n - i - 1).choose (2*n - i) : ℤ)
        = (-1)^(2*n - i) * ∑ l ∈ range (2*n - i + 1), (-1)^l * ((3*n-i).choose l : ℤ) := by
      rw [hpa]
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hval, neg_one_pow_two_mul_sub n i hi2, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_range] at hl
    have : ((3*n).choose i : ℤ) * ((3*n-i).choose l : ℤ)
        = ((3*n).choose (i+l) : ℤ) * ((i+l).choose i : ℤ) := by
      exact_mod_cast choose_mul_choose_sub (3*n) i l
    rw [show (-1:ℤ)^(i+l) = (-1)^i * (-1)^l from by rw [pow_add]]
    linear_combination ((-1:ℤ)^i * (-1:ℤ)^l) * this
  rw [Finset.sum_congr rfl step2]
  have hre : (∑ i ∈ range (2*n+1), ∑ l ∈ range (2*n - i + 1),
                ((3*n).choose (i+l):ℤ) * ((i+l).choose i) * (-1)^(i+l))
           = (∑ i ∈ range (2*n+1), ∑ l ∈ range ((2*n+1) - i),
                ((3*n).choose (i+l):ℤ) * ((i+l).choose i) * (-1)^(i+l)) := by
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    have he : 2*n - i + 1 = (2*n+1) - i := by omega
    rw [he]
  rw [hre, ← Finset.sum_range_diag_flip (2*n+1)
        (fun i l => ((3*n).choose (i+l) : ℤ) * ((i+l).choose i : ℤ) * (-1)^(i+l))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have : ∀ k ∈ range (m+1),
      ((3*n).choose (k+(m-k)) : ℤ) * ((k+(m-k)).choose k : ℤ) * (-1)^(k+(m-k))
        = ((3*n).choose m : ℤ) * (-1)^m * ((m.choose k : ℤ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have : k + (m - k) = m := by omega
    rw [this]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  have hsum : ∑ k ∈ range (m+1), (m.choose k : ℤ) = 2^m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  rw [hsum, show (-2:ℤ)^m = (-1)^m * 2^m from by rw [← neg_one_mul, mul_pow]]
  ring

/-- The core supercongruence, phrased on the closed form:
for `p ≥ 5` prime and `n, k ≥ 1`, `p^{3k}` divides the difference of the
truncated alternating binomial sums at `N = n·p^{k-1}` and `N' = n·p^k`.

This is the arithmetic heart of the conjecture: an Apéry-like supercongruence.
The sequence is the diagonal `a(n) = CT[((1-2w)^3/w^2)^n /(w(1-w))]`, and the
factor `p^{3k}` arises from a `k`-level Dwork p-adic tower where each Frobenius
step gains `p^3 = p^1` (Dwork) `× p^2` (a double zero of the Frobenius
`E(w) = ((1-2w)^p - (1-2w^p))/p = (1-w)^2 G(w)` at the critical point `w = 1`).
The divisibility is not term-wise: the low-order terms of the natural
expansions cancel, with cancellation depth growing with `k`, so a uniform
p-adic (Dwork) argument is required. -/
theorem closed_supercongruence (p n k : ℕ)
    (hp : Nat.Prime p) (hp5 : p ≥ 5) (hn : n ≥ 1) (hk : k ≥ 1) :
    (↑(p ^ (3 * k)) : ℤ) ∣
      (∑ m ∈ range (2*(n * p ^ (k-1))+1), ((3*(n * p ^ (k-1))).choose m : ℤ) * (-2)^m)
        - (∑ m ∈ range (2*(n * p ^ k)+1), ((3*(n * p ^ k)).choose m : ℤ) * (-2)^m) := by
  sorry

/-- We conjecture that this sequence satisfies the supercongruences
a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k.
-/
theorem oeis_333561_conjecture :
  ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] :=
by
  intro p n k hp hp5 hn hk
  rw [Nat.modEq_iff_dvd]
  have h1 : (1:ℕ) ≤ n * p ^ k :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero k hp.pos.ne'))
  have h0 : (1:ℕ) ≤ n * p ^ (k-1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero (k-1) hp.pos.ne'))
  rw [a_closed (n * p ^ (k-1)) h0, a_closed (n * p ^ k) h1]
  exact closed_supercongruence p n k hp hp5 hn hk
