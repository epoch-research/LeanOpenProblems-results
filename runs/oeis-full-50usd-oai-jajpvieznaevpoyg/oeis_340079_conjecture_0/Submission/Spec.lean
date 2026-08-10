import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

lemma sum_Ico_gcd_eq_sum_range_gcd (n : ℕ) (hn : n ≠ 0) :
    (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) =
      (Finset.range n).sum (fun k => Nat.gcd n k) := by
  classical
  refine Finset.sum_bij (fun k _hk => k % n) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
  · intro x hx y hy hxy
    change x % n = y % n at hxy
    rw [Finset.mem_Ico] at hx hy
    have hxle : x ≤ n := by omega
    have hyle : y ≤ n := by omega
    rcases lt_or_eq_of_le hxle with hxlt | hxeq
    · rcases lt_or_eq_of_le hyle with hylt | hyeq
      · rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hxy
        exact hxy
      · subst y
        rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_zero_of_dvd (dvd_refl n)] at hxy
        omega
    · subst x
      rcases lt_or_eq_of_le hyle with hylt | hyeq
      · rw [Nat.mod_eq_zero_of_dvd (dvd_refl n), Nat.mod_eq_of_lt hylt] at hxy
        omega
      · subst y
        rfl
  · intro b hb
    rw [Finset.mem_range] at hb
    by_cases hb0 : b = 0
    · refine ⟨n, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        omega
      · change n % n = b
        rw [hb0, Nat.mod_eq_zero_of_dvd (dvd_refl n)]
    · refine ⟨b, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        omega
      · change b % n = b
        exact Nat.mod_eq_of_lt hb
  · intro k hk
    change Nat.gcd k n = Nat.gcd n (k % n)
    rw [Nat.gcd_comm k n]
    rw [Nat.gcd_rec n k]
    rw [Nat.gcd_comm (k % n) n]

lemma sum_range_gcd_eq_sum_divisors (n : ℕ) (hn : n ≠ 0) :
    (Finset.range n).sum (fun k => Nat.gcd n k) =
      n.divisors.sum (fun d => d * Nat.totient (n / d)) := by
  classical
  symm
  calc
    n.divisors.sum (fun d => d * Nat.totient (n / d))
        = ∑ d ∈ n.divisors, d * #({k ∈ Finset.range n | n.gcd k = d}) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
            rw [Nat.totient_div_of_dvd hdn]
    _ = ∑ d ∈ n.divisors, ∑ k ∈ Finset.range n with n.gcd k = d, d := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            rw [Finset.sum_const_nat]
            · rw [mul_comm]
            · intro x hx
              rfl
    _ = ∑ k ∈ Finset.range n, Nat.gcd n k := by
            rw [Finset.sum_fiberwise_of_maps_to']
            intro k hk
            rw [Nat.mem_divisors]
            exact ⟨Nat.gcd_dvd_left n k, hn⟩

lemma sum_Ico_gcd_eq_sum_divisors (n : ℕ) (hn : n ≠ 0) :
    (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) =
      n.divisors.sum (fun d => d * Nat.totient (n / d)) := by
  rw [sum_Ico_gcd_eq_sum_range_gcd n hn, sum_range_gcd_eq_sum_divisors n hn]


lemma a_eq_one_of_sum_eq {n s : ℕ} (hn : n ≠ 0)
    (hs : (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = s)
    (hdiv : n ∣ 1 + s) : a n = 1 := by
  unfold a
  rw [hs]
  change n / Nat.gcd n (1 + s) = 1
  rw [Nat.gcd_eq_left hdiv]
  exact Nat.div_self (Nat.pos_of_ne_zero hn)

namespace Counterexample340079

open ArithmeticFunction

def phiAF : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

lemma phiAF_apply (n : ℕ) : phiAF n = Nat.totient n := rfl

lemma phiAF_mult : phiAF.IsMultiplicative := by
  refine ⟨Nat.totient_one, ?_⟩
  intro m n h
  exact Nat.totient_mul h

def gcdSumAF : ArithmeticFunction ℕ := ArithmeticFunction.id * phiAF

lemma gcdSumAF_eq_divisor_sum (n : ℕ) :
    gcdSumAF n = n.divisors.sum (fun d => d * Nat.totient (n / d)) := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun i j => ArithmeticFunction.id i * phiAF j)]
  simp [ArithmeticFunction.id_apply, phiAF_apply]

lemma gcdSumAF_prime {p : ℕ} (hp : Nat.Prime p) : gcdSumAF p = 2 * p - 1 := by
  rw [gcdSumAF_eq_divisor_sum]
  rw [Nat.Prime.divisors hp]
  rw [Finset.sum_insert]
  · simp [Nat.totient_one, Nat.totient_prime hp, Nat.div_self hp.pos]
    have hp1 : 1 ≤ p := hp.one_lt.le
    omega
  · simpa using hp.ne_one.symm

lemma gcdSumAF_counterexample_value :
    gcdSumAF (3 * 37 * 43 * 42307 * 116341) = 610815156979325 := by
  have hmul : gcdSumAF.IsMultiplicative := by
    change (ArithmeticFunction.id * phiAF).IsMultiplicative
    exact ArithmeticFunction.isMultiplicative_id.mul phiAF_mult
  have h3 : Nat.Prime 3 := by norm_num
  have h37 : Nat.Prime 37 := by norm_num
  have h43 : Nat.Prime 43 := by norm_num
  have h42307 : Nat.Prime 42307 := by norm_num
  have h116341 : Nat.Prime 116341 := by norm_num
  rw [hmul.map_mul_of_coprime (by norm_num : Nat.Coprime (3 * 37 * 43 * 42307) 116341)]
  rw [hmul.map_mul_of_coprime (by norm_num : Nat.Coprime (3 * 37 * 43) 42307)]
  rw [hmul.map_mul_of_coprime (by norm_num : Nat.Coprime (3 * 37) 43)]
  rw [hmul.map_mul_of_coprime (by norm_num : Nat.Coprime 3 37)]
  rw [gcdSumAF_prime h3, gcdSumAF_prime h37, gcdSumAF_prime h43,
    gcdSumAF_prime h42307, gcdSumAF_prime h116341]
  norm_num

lemma a_counterexample : a 23492890653051 = 1 := by
  apply a_eq_one_of_sum_eq (s := 610815156979325)
  · norm_num
  · rw [sum_Ico_gcd_eq_sum_divisors 23492890653051 (by norm_num)]
    rw [← gcdSumAF_eq_divisor_sum]
    have hgs : gcdSumAF 23492890653051 = 610815156979325 := by
      rw [show 23492890653051 = 3 * 37 * 43 * 42307 * 116341 by norm_num]
      exact gcdSumAF_counterexample_value
    exact hgs
  · use 26

lemma not_prime_counterexample : ¬ Nat.Prime 23492890653051 := by
  norm_num [Nat.Prime]

end Counterexample340079

/--
It is conjectured that $a(n) = 1$ if and only if $n$ is 1 or a prime number.
A340079: It is conjectured that this is 1 iff n is 1 or a prime. See _Thomas Ordowski_'s Oct 22 2014 comment in A018804.
-/
theorem oeis_340079_conjecture_0.disproof :
    ¬ (∀ n : ℕ, a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  have hright := (h 23492890653051).mp Counterexample340079.a_counterexample
  have hnot : ¬ (23492890653051 = 1 ∨ Nat.Prime 23492890653051) := by
    intro hcase
    rcases hcase with h1 | hp
    · norm_num at h1
    · exact Counterexample340079.not_prime_counterexample hp
  exact hnot hright
