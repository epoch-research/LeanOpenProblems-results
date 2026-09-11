import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

-- The gcd sum is the Dirichlet convolution of the identity and Euler's totient.
private def phiAF : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
private def gcdSumAF : ArithmeticFunction ℕ := ArithmeticFunction.id * phiAF

private theorem gcdSumAF_mult : gcdSumAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_id.mul
    ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩

private theorem gcdSumAF_eq (n : ℕ) (hn : n ≠ 0) :
    gcdSumAF n = ∑ k ∈ range n, Nat.gcd n k := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => ArithmeticFunction.id x * phiAF y)]
  change (∑ d ∈ n.divisors, d * (n / d).totient) = _
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := range n) (t := n.divisors) (g := Nat.gcd n)
    (fun k _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn⟩)]
  apply sum_congr rfl
  intro d hd
  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
  simp only [mul_comm d]
  rw [← Nat.nsmul_eq_mul, ← Finset.sum_const]
  apply sum_congr rfl
  intro k hk
  exact (Finset.mem_filter.mp hk).2.symm

private theorem gcdSumAF_prime {p : ℕ} (hp : p.Prime) :
    gcdSumAF p = 2 * p - 1 := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => ArithmeticFunction.id x * phiAF y)]
  change (∑ d ∈ p.divisors, d * (p / d).totient) = _
  rw [hp.divisors]
  simp [hp.ne_one.symm, Nat.div_self hp.pos, Nat.totient_prime hp]
  omega

private theorem gcdSumAF_interval (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Ico 1 (n + 1), Nat.gcd k n) = gcdSumAF n := by
  rw [gcdSumAF_eq n hn.ne', Finset.sum_Ico_succ_top hn]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
  simp [Nat.gcd_comm, add_comm]

-- 23492890653051 = 3 * 37 * 43 * 42307 * 116341, and the sum is 26n - 1.
private theorem multiplicative_counterexample (f : ArithmeticFunction ℕ)
    (h : f.IsMultiplicative) (hp : ∀ p, Nat.Prime p → f p = 2 * p - 1) :
    f 23492890653051 = 610815156979325 := by
  have h3 : Nat.Prime 3 := by norm_num
  have h37 : Nat.Prime 37 := by norm_num
  have h43 : Nat.Prime 43 := by norm_num
  have h42307 : Nat.Prime 42307 := by norm_num
  have h116341 : Nat.Prime 116341 := by norm_num
  rw [show 23492890653051 = 3 * (37 * (43 * (42307 * 116341))) by norm_num]
  rw [h.map_mul_of_coprime (m := 3) (n := 37 * (43 * (42307 * 116341))) (by norm_num),
      h.map_mul_of_coprime (m := 37) (n := 43 * (42307 * 116341)) (by norm_num),
      h.map_mul_of_coprime (m := 43) (n := 42307 * 116341) (by norm_num),
      h.map_mul_of_coprime (m := 42307) (n := 116341) (by norm_num)]
  rw [hp _ h3, hp _ h37, hp _ h43, hp _ h42307, hp _ h116341]
  norm_num

private theorem gcdSumAF_counterexample : gcdSumAF 23492890653051 = 610815156979325 :=
  multiplicative_counterexample gcdSumAF gcdSumAF_mult (fun _ hp => gcdSumAF_prime hp)

private theorem a_eq_gcdSumAF (n : ℕ) (hn : 0 < n) :
    a n = n / Nat.gcd n (1 + gcdSumAF n) := by
  unfold a
  rw [gcdSumAF_interval n hn]

private theorem counterexample_a : a 23492890653051 = 1 := by
  rw [a_eq_gcdSumAF _ (by norm_num), gcdSumAF_counterexample]
  norm_num

/--
It is conjectured that $a(n) = 1$ if and only if $n$ is 1 or a prime number.
A340079: It is conjectured that this is 1 iff n is 1 or a prime. See _Thomas Ordowski_'s Oct 22 2014 comment in A018804.
-/
theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  sorry

theorem oeis_340079_conjecture_0.disproof : ¬ (type_of% @oeis_340079_conjecture_0) := by
  intro h
  have ha := counterexample_a
  have hc := (h 23492890653051).mp ha
  rcases hc with hc | hc
  · norm_num at hc
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by norm_num)
      (by norm_num) hc
