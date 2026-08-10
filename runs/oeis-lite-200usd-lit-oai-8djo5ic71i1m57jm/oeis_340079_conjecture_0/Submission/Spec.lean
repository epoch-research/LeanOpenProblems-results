import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)


def phiAF : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

def gcdSumAF : ArithmeticFunction ℕ := ArithmeticFunction.id * phiAF

lemma phiAF_mult : (phiAF).IsMultiplicative := by
  constructor
  · simp [phiAF]
  · intro m n h
    simp [phiAF, Nat.totient_mul h]

lemma gcdSumAF_mult : (gcdSumAF).IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.mul ArithmeticFunction.isMultiplicative_id phiAF_mult

lemma gcdSumAF_prime {p : ℕ} (hp : Nat.Prime p) : gcdSumAF p = 2 * p - 1 := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.id a * phiAF b)]
  rw [hp.divisors]
  rw [sum_insert]
  · rw [sum_singleton]
    simp [phiAF, ArithmeticFunction.id_apply, Nat.totient_prime hp, Nat.div_self hp.pos]
    omega
  · simpa using hp.ne_one.symm

lemma sum_Ico_gcd_eq_sum_range (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n) =
      ∑ k ∈ Finset.range n, Nat.gcd n k := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hn]
  conv_rhs => rw [← Nat.succ_pred_eq_of_pos hn]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.gcd_comm]
    congr 1
    omega
  · simp [Nat.add_comm]

lemma sum_range_gcd_eq_gcdSumAF (n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range n, Nat.gcd n k) = gcdSumAF n := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.id a * phiAF b)]
  symm
  have hmap : ∀ k ∈ Finset.range n, Nat.gcd n k ∈ n.divisors := by
    intro k hk
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left n k, hn⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range n) (t := n.divisors)
    (g := fun k => Nat.gcd n k) hmap (f := fun k => Nat.gcd n k)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [Finset.sum_const_nat (m := d)]
  · simp only [phiAF, ArithmeticFunction.coe_mk, ArithmeticFunction.id_apply]
    rw [Nat.totient_div_of_dvd hdvd]
    simp [mul_comm]
  · intro x hx
    simp at hx
    exact hx.2

lemma sum_Ico_gcd_eq_gcdSumAF (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n) = gcdSumAF n := by
  rw [sum_Ico_gcd_eq_sum_range n hn, sum_range_gcd_eq_gcdSumAF n hn.ne']

lemma gcdSumAF_counterexample : gcdSumAF 23492890653051 = 610815156979325 := by
  let P : Finset ℕ := {3, 37, 43, 42307, 116341}
  have hprod : (∏ p ∈ P, p) = 23492890653051 := by
    subst P
    norm_num
  rw [← hprod]
  rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime gcdSumAF_mult]
  · change (∏ p ∈ P, gcdSumAF p) = 610815156979325
    subst P
    simp [gcdSumAF_prime (by norm_num : Nat.Prime 3),
      gcdSumAF_prime (by norm_num : Nat.Prime 37),
      gcdSumAF_prime (by norm_num : Nat.Prime 43),
      gcdSumAF_prime (by norm_num : Nat.Prime 42307),
      gcdSumAF_prime (by norm_num : Nat.Prime 116341)]
  · intro p hp
    subst P
    fin_cases hp <;> norm_num

lemma a_counterexample : a 23492890653051 = 1 := by
  have hsum := sum_Ico_gcd_eq_gcdSumAF 23492890653051 (by norm_num)
  rw [a]
  simp only [hsum, gcdSumAF_counterexample]
  norm_num

/-- The conjecture is false; `23492890653051 = 3 * 37 * 43 * 42307 * 116341` is a counterexample. -/
theorem oeis_340079_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  have hbad := (h 23492890653051).mp a_counterexample
  have hn1 : 23492890653051 ≠ 1 := by norm_num
  have hnp : ¬ Nat.Prime 23492890653051 := by
    norm_num [Nat.Prime]
  exact hbad.elim hn1 hnp
