import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

open ArithmeticFunction

def phiAF : ArithmeticFunction ℕ := ⟨Nat.totient, by simp⟩

lemma phiAF_mult : phiAF.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [phiAF]
  · intro m n h
    simp [phiAF, Nat.totient_mul h]

def pillaiAF : ArithmeticFunction ℕ := ArithmeticFunction.id * phiAF

lemma pillaiAF_mult : pillaiAF.IsMultiplicative := by
  dsimp [pillaiAF]
  exact ArithmeticFunction.isMultiplicative_id.mul phiAF_mult

lemma pillaiAF_eq_divisor_sum (n : ℕ) :
    pillaiAF n = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  rw [pillaiAF, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.id a * phiAF b)]
  rfl

lemma sum_range_gcd_eq_pillaiAF (n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range n, Nat.gcd n k) = pillaiAF n := by
  rw [pillaiAF_eq_divisor_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.range n) (t := n.divisors) (g := fun k => Nat.gcd n k)
    (by
      intro k _
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn⟩)
    (fun k => Nat.gcd n k)]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
  calc
    (∑ i ∈ Finset.range n with Nat.gcd n i = d, Nat.gcd n i)
        = ∑ i ∈ Finset.range n with Nat.gcd n i = d, d := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (Finset.mem_filter.mp hi).2
    _ = d * #({k ∈ Finset.range n | Nat.gcd n k = d}) := by
          simp [Finset.sum_const, mul_comm]

lemma sum_Ico_gcd_eq_pillaiAF (n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n) = pillaiAF n := by
  have h0 : (∑ k ∈ Finset.range (n + 1), Nat.gcd k n)
      = Nat.gcd 0 n + ∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
  have hsucc : (∑ k ∈ Finset.range (n + 1), Nat.gcd k n)
      = (∑ k ∈ Finset.range n, Nat.gcd k n) + Nat.gcd n n := by
    exact Finset.sum_range_succ (fun k => Nat.gcd k n) n
  have hcomm : (∑ k ∈ Finset.range n, Nat.gcd k n) = ∑ k ∈ Finset.range n, Nat.gcd n k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    exact Nat.gcd_comm k n
  have hcancel : (∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n) = ∑ k ∈ Finset.range n, Nat.gcd n k := by
    have hg0 : Nat.gcd 0 n = n := by simp
    have hgn : Nat.gcd n n = n := by simp
    omega
  rw [hcancel, sum_range_gcd_eq_pillaiAF n hn]

lemma pillaiAF_prime {p : ℕ} (hp : Nat.Prime p) : pillaiAF p = 2 * p - 1 := by
  rw [pillaiAF_eq_divisor_sum, hp.divisors]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [Nat.div_one, Nat.div_self hp.pos, Nat.totient_prime hp]
    simp
    omega
  · simp only [Finset.mem_singleton]
    exact hp.ne_one.symm

lemma pillaiAF_counterexample_value :
    pillaiAF 23492890653051 = 610815156979325 := by
  let s : Finset ℕ := {3, 37, 43, 42307, 116341}
  have hp : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    fin_cases hp <;> norm_num
  have h := pillaiAF_mult.map_prod_of_prime s hp
  norm_num [s] at h ⊢
  rw [h]
  rw [pillaiAF_prime (p := 3) (by norm_num),
    pillaiAF_prime (p := 37) (by norm_num),
    pillaiAF_prime (p := 43) (by norm_num),
    pillaiAF_prime (p := 42307) (by norm_num),
    pillaiAF_prime (p := 116341) (by norm_num)]
  norm_num

lemma a_counterexample : a 23492890653051 = 1 := by
  rw [a, sum_Ico_gcd_eq_pillaiAF 23492890653051 (by norm_num),
    pillaiAF_counterexample_value]
  norm_num

/--
The conjecture is false.  A counterexample is
`23492890653051 = 3 * 37 * 43 * 42307 * 116341`.
-/
theorem oeis_340079_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  have hrhs : 23492890653051 = 1 ∨ Nat.Prime 23492890653051 :=
    (h 23492890653051).mp a_counterexample
  have hn1 : 23492890653051 ≠ 1 := by norm_num
  have hnotprime : ¬ Nat.Prime 23492890653051 := by
    intro hp
    have hdiv : 3 ∣ 23492890653051 := by norm_num
    have hsmall := hp.eq_one_or_self_of_dvd 3 hdiv
    omega
  exact hrhs.elim hn1 hnotprime
