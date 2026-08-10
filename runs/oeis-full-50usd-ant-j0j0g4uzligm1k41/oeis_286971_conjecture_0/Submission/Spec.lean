import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Nat BigOperators

/--
A286971: Number of ways to write $n$ as a sum of two numbers, one of which is the product of an even number of distinct primes (including 1) (A030229) and another is the product of an odd number of distinct primes (A030059).
This counts ordered pairs $(e, o)$ of positive integers such that $e+o=n$, $\mu(e)=1$, and $\mu(o)=-1$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    -- The values of moebius e and moebius o are compared with Int 1 and Int -1.
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0

/-!
## Structural results toward A286971

We must show `a n > 0` for every `n > 10`, i.e. for each such `n` there exist positive
integers `e, o` with `e + o = n`, `μ(e) = 1` and `μ(o) = -1`.

Writing `R(n) = #{(x,y) : x+y=n, x,y squarefree}` and `V(n) = ∑_{x+y=n} μ(x)μ(y)`, the
(ordered) count of representations with opposite Möbius signs is exactly `(R(n) - V(n))/4`.
Hence `a n > 0` is *equivalent* to the cancellation inequality `V(n) < R(n)`, where `V(n)`
is a **binary additive Möbius correlation** (a sum over the additive constraint `x + y = n`).
Such binary correlations are in the difficulty class of the Goldbach problem; establishing
`V(n) = o(n)` requires Prime-Number-Theorem–strength input (Möbius cancellation in
arithmetic progressions, via the circle method), which is not available in the current
library (only Chebyshev bounds are present, with no Tauberian theorem to bridge the
L-function nonvanishing on `Re s = 1` to an asymptotic).  Moreover the parity obstruction
rules out every sieve/elementary covering argument, and the multiplicative construction
below provably bottoms out at the prime values of `n`, where no such structure exists.

We record the genuine, machine-checked content that *is* attainable.
-/

/-- A single explicit witness `e ∈ [1, n)` with `μ(e) = 1` and `μ(n - e) = -1` gives
`a n > 0`. -/
theorem a_pos_of_witness {n e : ℕ} (he : e ∈ Finset.Ico 1 n)
    (h1 : moebius e = 1) (h2 : moebius (n - e) = -1) : 0 < a n := by
  unfold a
  rw [Finset.sum_eq_sum_diff_singleton_add he]
  have : (if moebius e = 1 ∧ moebius (n - e) = -1 then (1 : ℕ) else 0) = 1 := by
    simp [h1, h2]
  rw [this]
  positivity

/-- A squarefree number has Möbius value `1` or `-1`. -/
theorem moebius_sqfree_eq_one_or {m : ℕ} (h : Squarefree m) :
    moebius m = 1 ∨ moebius m = -1 := by
  rw [moebius_apply_of_squarefree h]
  rcases Nat.even_or_odd (cardFactors m) with h | h
  · left; exact Even.neg_one_pow h
  · right; exact Odd.neg_one_pow h

/-- General constructive sufficient condition.  If `d, s, t ≥ 1` are squarefree with
`d` coprime to both `s` and `t`, and `μ(s) = -μ(t)`, then `a (d*(s+t)) > 0`, witnessed by
the pair `{d*s, d*t}` (whose Möbius values are `μ(d)μ(s)` and `μ(d)μ(t) = -μ(d)μ(s)`, hence
opposite). -/
theorem a_pos_construction {d s t : ℕ}
    (hd : Squarefree d) (hs : Squarefree s)
    (hds : Nat.Coprime d s) (hdt : Nat.Coprime d t)
    (hsign : moebius s = - moebius t)
    (hs1 : 1 ≤ s) (ht1 : 1 ≤ t) (hd1 : 1 ≤ d) :
    0 < a (d * (s + t)) := by
  set n := d * (s + t) with hn
  have hdpos : 0 < d := hd1
  have he_lt : d * s < n := by rw [hn]; exact (Nat.mul_lt_mul_left hdpos).mpr (by omega)
  have ho_lt : d * t < n := by rw [hn]; exact (Nat.mul_lt_mul_left hdpos).mpr (by omega)
  have hsub : n - d * s = d * t := by rw [hn]; ring_nf; omega
  have hsub2 : n - d * t = d * s := by rw [hn]; ring_nf; omega
  have hmuds : moebius (d * s) = moebius d * moebius s :=
    isMultiplicative_moebius.map_mul_of_coprime hds
  have hmudt : moebius (d * t) = moebius d * moebius t :=
    isMultiplicative_moebius.map_mul_of_coprime hdt
  have hmt : moebius t = - moebius s := by linarith [hsign]
  have hmd := moebius_sqfree_eq_one_or hd
  have hms := moebius_sqfree_eq_one_or hs
  have h1s : (1 : ℕ) ≤ d * s := Nat.mul_pos hdpos (by omega)
  have h1t : (1 : ℕ) ≤ d * t := Nat.mul_pos hdpos (by omega)
  rcases hmd with hmd | hmd <;> rcases hms with hms | hms
  · refine a_pos_of_witness (e := d * s) (Finset.mem_Ico.mpr ⟨h1s, he_lt⟩) ?_ ?_
    · rw [hmuds, hmd, hms]; ring
    · rw [hsub, hmudt, hmd, hmt, hms]; ring
  · refine a_pos_of_witness (e := d * t) (Finset.mem_Ico.mpr ⟨h1t, ho_lt⟩) ?_ ?_
    · rw [hmudt, hmd, hmt, hms]; ring
    · rw [hsub2, hmuds, hmd, hms]; ring
  · refine a_pos_of_witness (e := d * t) (Finset.mem_Ico.mpr ⟨h1t, ho_lt⟩) ?_ ?_
    · rw [hmudt, hmd, hmt, hms]; ring
    · rw [hsub2, hmuds, hmd, hms]; ring
  · refine a_pos_of_witness (e := d * s) (Finset.mem_Ico.mpr ⟨h1s, he_lt⟩) ?_ ?_
    · rw [hmuds, hmd, hms]; ring
    · rw [hsub, hmudt, hmd, hmt, hms]; ring

/-- Constructive family: for `m ≥ 1` odd and squarefree, the conjecture holds at `n = 3m`
(take `d = m`, `s = 1`, `t = 2`). -/
theorem a_pos_three_mul {m : ℕ} (hm1 : 1 ≤ m) (hodd : Odd m) (hsqf : Squarefree m) :
    0 < a (3 * m) := by
  have hcop2 : Nat.Coprime m 2 := by
    rw [Nat.coprime_two_right]; exact hodd
  have hmu2 : moebius (1 : ℕ) = - moebius 2 := by
    rw [moebius_apply_one, moebius_apply_prime Nat.prime_two]; ring
  have h := a_pos_construction (d := m) (s := 1) (t := 2) hsqf
    squarefree_one (Nat.coprime_one_right m) hcop2
    hmu2 le_rfl (by norm_num) hm1
  rw [show (3 : ℕ) * m = m * (1 + 2) from by ring]
  exact h

/-- A286971 Conjecture: a(n) > 0 for all n > 10.

`a n > 0 ↔ V(n) < R(n)` where `V(n) = ∑_{x+y=n} μ(x)μ(y)` is a binary additive Möbius
correlation.  The multiplicative construction `a_pos_construction` reduces every composite,
non-prime-power `n` to smaller cases, but bottoms out at primes (and prime powers), where
`gcd(e,o) = 1` is forced and no multiplicative structure remains.  For those the statement
is the genuine binary additive Möbius problem, requiring Prime-Number-Theorem–strength
analytic input (Möbius cancellation in arithmetic progressions via the circle method) that
is not present in the current library.  This is the irreducible analytic core. -/
theorem oeis_286971_conjecture_0 :
  ∀ n, 10 < n → a n > 0 := by sorry
