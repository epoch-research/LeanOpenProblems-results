import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

namespace Oeis340079Disproof

open ArithmeticFunction

/-- Euler's totient as an `ArithmeticFunction`. -/
def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

lemma phi_mult : phi.IsMultiplicative :=
  ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩

/-- Pillai's arithmetical function `∑_{d ∣ n} φ(d) * (n/d)`, as the Dirichlet
convolution `φ ⋆ id`. -/
def pillai : ArithmeticFunction ℕ := phi * ArithmeticFunction.id

lemma pillai_mult : pillai.IsMultiplicative := phi_mult.mul isMultiplicative_id

lemma pillai_apply (n : ℕ) : pillai n = ∑ d ∈ n.divisors, Nat.totient d * (n / d) := by
  rw [pillai, mul_apply, ← Nat.map_div_right_divisors, Finset.sum_map]
  rfl

lemma pillai_prime {p : ℕ} (hp : p.Prime) : pillai p = 2 * p - 1 := by
  rw [pillai_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.totient_one,
    Nat.totient_prime hp, Nat.div_one, Nat.div_self hp.pos]
  have := hp.two_le
  omega

/-- The key identity: the gcd-sum function `A018804` equals Pillai's function
`∑_{d ∣ n} φ(d) * (n/d)`. -/
lemma gcd_sum_eq_pillai {n : ℕ} (hn : n ≠ 0) :
    ((Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n) = pillai n := by
  rw [pillai_apply]
  have step1 : ∀ k ∈ Finset.Ico 1 (n + 1),
      Nat.gcd k n = ∑ d ∈ n.divisors with d ∣ k, Nat.totient d := by
    intro k _
    conv_lhs => rw [← Nat.sum_totient (Nat.gcd k n)]
    congr 1
    rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.gcd_dvd_right k n)]
    apply Finset.filter_congr
    intro d hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    simp [Nat.dvd_gcd_iff, hdn]
  rw [Finset.sum_congr rfl step1]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have : #{i ∈ Finset.range n | d ∣ 1 + i} = n / d := by
    rw [← Nat.card_multiples n d]
    apply Finset.card_bij (fun x _ => x) <;> simp [add_comm]
  rw [this, mul_comm]

/-- If `n ∣ 1 + A018804(n)` then `a n = 1`. -/
lemma a_eq_one_of_dvd {n : ℕ} (hn : 0 < n)
    (h : n ∣ 1 + ((Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n)) : a n = 1 := by
  show n / Nat.gcd n (1 + ((Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n)) = 1
  rw [Nat.gcd_eq_left h, Nat.div_self hn]

/-- The counterexample `n = 23492890653051 = 3 * 37 * 43 * 42307 * 116341` is
squarefree with five prime factors, and
`pillai n = 5 * 73 * 85 * 84613 * 232681 = 610815156979325`. -/
lemma pillai_counterexample : pillai 23492890653051 = 610815156979325 := by
  have hp1 : Nat.Prime 3 := by norm_num
  have hp2 : Nat.Prime 37 := by norm_num
  have hp3 : Nat.Prime 43 := by norm_num
  have hp4 : Nat.Prime 42307 := by norm_num
  have hp5 : Nat.Prime 116341 := by norm_num
  have e1 : (23492890653051 : ℕ) = 3 * (37 * (43 * (42307 * 116341))) := by norm_num
  rw [e1, pillai_mult.map_mul_of_coprime (by norm_num),
    pillai_mult.map_mul_of_coprime (by norm_num),
    pillai_mult.map_mul_of_coprime (by norm_num),
    pillai_mult.map_mul_of_coprime (by norm_num),
    pillai_prime hp1, pillai_prime hp2, pillai_prime hp3, pillai_prime hp4,
    pillai_prime hp5]
  norm_num

/-- `a 23492890653051 = 1`, since
`1 + A018804(23492890653051) = 610815156979326 = 26 * 23492890653051`. -/
lemma a_counterexample : a 23492890653051 = 1 := by
  apply a_eq_one_of_dvd (by norm_num)
  rw [gcd_sum_eq_pillai (by norm_num), pillai_counterexample]
  exact ⟨26, by norm_num⟩

end Oeis340079Disproof

/--
It is conjectured that $a(n) = 1$ if and only if $n$ is 1 or a prime number.
A340079: It is conjectured that this is 1 iff n is 1 or a prime. See _Thomas Ordowski_'s Oct 22 2014 comment in A018804.

This is **false**: `n = 23492890653051 = 3 * 37 * 43 * 42307 * 116341` is a
composite number with `a n = 1`. Indeed, the gcd-sum function satisfies
`A018804(n) = ∑_{d ∣ n} φ(d) (n/d)`, which is multiplicative with value
`2p - 1` at primes, so `A018804(n) = 5 * 73 * 85 * 84613 * 232681 = 610815156979325`
and `1 + A018804(n) = 26 * n`, whence `gcd(n, 1 + A018804(n)) = n` and `a n = 1`.
-/
theorem oeis_340079_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  intro H
  rcases (H 23492890653051).mp Oeis340079Disproof.a_counterexample with h | h
  · norm_num at h
  · rcases h.eq_one_or_self_of_dvd 3 (by norm_num) with h' | h' <;> norm_num at h'
