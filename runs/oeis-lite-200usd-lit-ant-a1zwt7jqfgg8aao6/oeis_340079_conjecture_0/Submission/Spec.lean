import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

namespace Disproof

/-- Totient as an arithmetic function. -/
def Φ : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

@[simp] lemma Φ_apply (n : ℕ) : Φ n = Nat.totient n := rfl

lemma Φ_mult : Φ.IsMultiplicative :=
  ⟨Nat.totient_one, fun {m n} h => Nat.totient_mul h⟩

/-- The Pillai / gcd-sum function `G n = ∑_{d∣n} d φ(n/d)`. It is multiplicative
and `G n = A018804 n = ∑_{k=1}^n gcd(k,n)`. -/
def G : ArithmeticFunction ℕ := ArithmeticFunction.id * Φ

lemma G_mult : G.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul ArithmeticFunction.isMultiplicative_id Φ_mult

lemma G_apply (n : ℕ) : G n = ∑ d ∈ n.divisors, d * (n / d).totient := by
  rw [G, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.id_apply, Φ_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun i j => i * j.totient)]

/-- The gcd-sum identity: `∑_{k<n} gcd(n,k) = ∑_{d∣n} d φ(n/d) = G n`. -/
lemma gcdSum_range (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, n.gcd k = G n := by
  rw [G_apply]
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun k => n.gcd k) (t := n.divisors)
        (fun k _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n k, hn.ne'⟩)
        (f := fun k => n.gcd k)]
  apply Finset.sum_congr rfl
  intro d hd
  have hstep : ∑ k ∈ range n with n.gcd k = d, n.gcd k
             = ∑ k ∈ range n with n.gcd k = d, d :=
    Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.1 hk).2)
  rw [hstep, Finset.sum_const, smul_eq_mul,
      Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), mul_comm]

/-- The value `A018804 n = ∑_{k=1}^n gcd(k,n)` equals `G n`. -/
lemma A_eq_G (n : ℕ) (hn : 0 < n) :
    (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = G n := by
  rw [← gcdSum_range n hn]
  rw [show (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)
        = (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd n k) from
      Finset.sum_congr rfl (fun k _ => Nat.gcd_comm k n)]
  rw [Finset.sum_Ico_succ_top hn (fun k => Nat.gcd n k)]
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive (fun k => Nat.gcd n k) (Nat.zero_le 1) hn]
  simp [Nat.gcd_self, Nat.add_comm]

/-- At a prime `p`, `G p = 2p - 1`. -/
lemma G_prime {p : ℕ} (hp : p.Prime) : G p = 2 * p - 1 := by
  rw [G_apply, hp.divisors]
  rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hp.one_lt.ne)]
  rw [Finset.sum_singleton]
  simp only [Nat.div_self hp.pos, Nat.totient_one, mul_one, Nat.div_one]
  rw [Nat.totient_prime hp]
  omega

/-- The counterexample: `N = 3 · 37 · 43 · 42307 · 116341`. Then
`G N = ∏ (2 pᵢ - 1) = 5 · 73 · 85 · 84613 · 232681`. -/
lemma GN : G 23492890653051 = 610815156979325 := by
  have ht : ∀ p ∈ ({3, 37, 43, 42307, 116341} : Finset ℕ), p.Prime := by
    intro p hp
    fin_cases hp <;> norm_num
  have hprod : (∏ a ∈ ({3, 37, 43, 42307, 116341} : Finset ℕ), a) = 23492890653051 := by
    decide
  rw [← hprod, G_mult.map_prod_of_prime _ ht]
  rw [Finset.prod_congr rfl (fun p hp => G_prime (ht p hp))]
  decide

/-- Rewriting `a n` using the multiplicative function `G`. -/
lemma a_eq (n : ℕ) (hn : 0 < n) : a n = n / Nat.gcd n (1 + G n) := by
  unfold a
  rw [A_eq_G n hn]

/-- For the composite number `N = 23492890653051`, we have `a N = 1`, because
`1 + G N = 610815156979326 = 26 · N`, so `N ∣ 1 + G N` and `gcd(N, 1 + G N) = N`. -/
lemma aN : a 23492890653051 = 1 := by
  have hN : (0 : ℕ) < 23492890653051 := by norm_num
  rw [a_eq 23492890653051 hN, GN]
  have hdvd : (23492890653051 : ℕ) ∣ 610815156979326 := ⟨26, by norm_num⟩
  rw [show (1 : ℕ) + 610815156979325 = 610815156979326 from by norm_num]
  rw [Nat.gcd_eq_left hdvd, Nat.div_self hN]

end Disproof

/--
The conjecture (A340079) states that $a(n) = 1$ if and only if $n$ is 1 or a prime number.
This is **false**: the composite number
$$N = 23492890653051 = 3 \cdot 37 \cdot 43 \cdot 42307 \cdot 116341$$
satisfies $a(N) = 1$.

Indeed $A018804$ is multiplicative with $A018804(p) = 2p-1$ at a prime $p$, so
$$1 + A018804(N) = 1 + \prod_i (2 p_i - 1) = 1 + 610815156979325 = 610815156979326 = 26 \cdot N,$$
whence $N \mid 1 + A018804(N)$, giving $\gcd(N, 1 + A018804(N)) = N$ and $a(N) = N/N = 1$,
even though $N$ is neither $1$ nor prime. This is a "twisted Giuga" counterexample with
five prime factors.
-/
theorem oeis_340079_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  intro h
  have hcontra := (h 23492890653051).mp Disproof.aN
  rcases hcontra with h1 | h2
  · norm_num at h1
  · have h3 : (3 : ℕ) ∣ 23492890653051 := ⟨7830963551017, by norm_num⟩
    rcases h2.eq_one_or_self_of_dvd 3 h3 with h4 | h4 <;> omega

/-- Alias under the generic name `foo.disproof`. -/
theorem foo.disproof : ¬ ∀ (n : ℕ), a n = 1 ↔ (n = 1 ∨ Nat.Prime n) :=
  oeis_340079_conjecture_0.disproof
