import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset ArithmeticFunction

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

/-!
It was conjectured that $a(n) = 1$ if and only if $n$ is 1 or a prime number
(A340079, based on _Thomas Ordowski_'s Oct 22 2014 comment in A018804).

This conjecture is **false**. We exhibit the composite counterexample
$$n_0 = 23492890653051 = 3 \cdot 37 \cdot 43 \cdot 42307 \cdot 116341,$$
which is squarefree, not prime and not $1$, yet satisfies $a(n_0) = 1$.

The proof uses that the Pillai gcd-sum function $A018804$ is the Dirichlet
convolution `id * φ`, hence multiplicative, with value $2p-1$ at each prime $p$.
Therefore $A018804(n_0) = \prod_{p \mid n_0} (2p-1) = 610815156979325$, and
$n_0 \mid 1 + A018804(n_0)$ (indeed $1 + 610815156979325 = 26 \cdot n_0$), so
$\gcd(n_0, 1 + A018804(n_0)) = n_0$ and $a(n_0) = n_0 / n_0 = 1$.
-/

/-- The totient function packaged as an arithmetic function. -/
noncomputable def phiA : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

@[simp] lemma phiA_apply (n : ℕ) : phiA n = φ n := rfl

lemma phiA_mult : phiA.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative]
  exact ⟨by simp, fun {m n} hmn => by simp only [phiA_apply]; exact Nat.totient_mul hmn⟩

/-- The Pillai gcd-sum function `A018804`, as the Dirichlet convolution `id * φ`. -/
noncomputable def pil : ArithmeticFunction ℕ := ArithmeticFunction.id * phiA

lemma pil_mult : pil.IsMultiplicative := isMultiplicative_id.mul phiA_mult

lemma pil_apply (n : ℕ) : pil n = ∑ d ∈ n.divisors, d * φ (n / d) := by
  rw [pil, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => ArithmeticFunction.id x * phiA y)]
  exact Finset.sum_congr rfl (fun d _ => by simp [ArithmeticFunction.id_apply])

lemma pil_prime {p : ℕ} (hp : p.Prime) : pil p = 2 * p - 1 := by
  rw [pil_apply, hp.divisors,
      Finset.sum_insert (show (1 : ℕ) ∉ ({p} : Finset ℕ) by
        simp only [Finset.mem_singleton]; have := hp.two_le; omega),
      Finset.sum_singleton, Nat.div_self hp.pos, Nat.div_one, Nat.totient_one,
      Nat.totient_prime hp]
  have := hp.two_le; omega

/-- The gcd-sum over `range n` equals the divisor-sum `∑_{d ∣ n} d · φ(n/d)`. -/
lemma gcdsum_eq (n : ℕ) : ∑ k ∈ Finset.range n, n.gcd k = ∑ d ∈ n.divisors, d * φ (n / d) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Finset.sum_fiberwise_of_maps_to (t := n.divisors) (g := fun k => n.gcd k)
       (fun k _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n k, hn.ne'⟩) (fun k => n.gcd k)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have : ∑ k ∈ {k ∈ Finset.range n | n.gcd k = d}, n.gcd k
       = ∑ _k ∈ {k ∈ Finset.range n | n.gcd k = d}, d :=
    Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.1 hk).2)
  rw [this, Finset.sum_const, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]; ring

/-- The `A018804` sum in the definition of `a` equals the arithmetic function `pil`. -/
lemma A_eq_pil (n : ℕ) : (∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n) = pil n := by
  have step : ∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n = ∑ k ∈ Finset.range n, n.gcd k := by
    rw [Finset.sum_Ico_eq_sum_range]; simp only [Nat.add_sub_cancel]
    have e1 : ∑ k ∈ Finset.range n, Nat.gcd (1 + k) n = ∑ k ∈ Finset.range n, n.gcd (k + 1) :=
      Finset.sum_congr rfl (fun k _ => by rw [Nat.gcd_comm]; ring_nf)
    rw [e1]
    have hb : ∑ k ∈ Finset.range (n + 1), n.gcd k
        = (∑ k ∈ Finset.range n, n.gcd (k + 1)) + n.gcd 0 := Finset.sum_range_succ' _ n
    have ht : ∑ k ∈ Finset.range (n + 1), n.gcd k
        = (∑ k ∈ Finset.range n, n.gcd k) + n.gcd n := Finset.sum_range_succ _ n
    rw [Nat.gcd_zero_right] at hb; rw [Nat.gcd_self] at ht; omega
  rw [step, gcdsum_eq, pil_apply]

/-- `pil` evaluated at the counterexample `n₀ = 3·37·43·42307·116341`. -/
lemma pil_n0 : pil 23492890653051 = 610815156979325 := by
  have h : (23492890653051 : ℕ) = 3 * (37 * (43 * (42307 * 116341))) := by norm_num
  rw [h,
    pil_mult.map_mul_of_coprime (by norm_num : Nat.gcd 3 (37 * (43 * (42307 * 116341))) = 1),
    pil_mult.map_mul_of_coprime (by norm_num : Nat.gcd 37 (43 * (42307 * 116341)) = 1),
    pil_mult.map_mul_of_coprime (by norm_num : Nat.gcd 43 (42307 * 116341) = 1),
    pil_mult.map_mul_of_coprime (by norm_num : Nat.gcd 42307 116341 = 1),
    pil_prime (by norm_num), pil_prime (by norm_num), pil_prime (by norm_num),
    pil_prime (by norm_num), pil_prime (by norm_num)]
  norm_num

/-- `a n` in terms of `pil` (stated symbolically to avoid unfolding on the huge numeral). -/
lemma a_eq (n : ℕ) : a n = n / Nat.gcd n (1 + pil n) := by
  simp only [a]; rw [A_eq_pil]

/-- The composite number `n₀ = 23492890653051` satisfies `a n₀ = 1`. -/
lemma a_n0 : a 23492890653051 = 1 := by
  rw [a_eq, pil_n0,
      Nat.gcd_eq_left (show (23492890653051 : ℕ) ∣ (1 + 610815156979325) by norm_num),
      Nat.div_self (by norm_num)]

/--
The A340079 conjecture is false: `a n = 1` does **not** characterize
`n = 1 ∨ n.Prime`, as witnessed by the composite `n₀ = 23492890653051`.
-/
theorem oeis_340079_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  rcases (h 23492890653051).mp a_n0 with h1 | h2
  · norm_num at h1
  · norm_num at h2
