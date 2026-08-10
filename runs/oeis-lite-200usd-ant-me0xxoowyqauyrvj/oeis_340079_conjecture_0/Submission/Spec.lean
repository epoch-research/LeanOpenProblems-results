import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

/- ### Pillai's arithmetic function (the gcd-sum `A018804`).

We develop just enough of the theory of `P n = ∑_{k=1}^n gcd(k, n)` to evaluate it on
squarefree numbers, namely that it is multiplicative with `P p = 2p - 1` for primes `p`.
This is used to exhibit an explicit counterexample to the conjectured characterisation. -/

/-- Pillai's arithmetic function (gcd-sum), matching the internal sum of `a`. -/
def P (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

/-- Rewrite the gcd-sum over `range n` with `gcd n k`. -/
theorem P_eq_range (n : ℕ) (hn : 1 ≤ n) :
    P n = ∑ k ∈ Finset.range n, Nat.gcd n k := by
  unfold P
  have hcomm : ∀ k, Nat.gcd k n = n.gcd k := fun k => Nat.gcd_comm k n
  simp_rw [hcomm]
  have hins : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  have hsplit : ∑ k ∈ Finset.range (n + 1), n.gcd k
      = n.gcd 0 + ∑ k ∈ Finset.Ico 1 (n + 1), n.gcd k := by
    rw [hins, Finset.sum_insert (by simp)]
  rw [Finset.sum_range_succ, Nat.gcd_self, Nat.gcd_zero_right] at hsplit
  omega

/-- The key divisor-sum identity for Pillai's function: `P n = ∑_{d ∣ n} d · φ(n/d)`. -/
theorem P_eq_divisorsum (n : ℕ) (hn : 1 ≤ n) :
    P n = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  rw [P_eq_range n hn]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => n.gcd k) (t := n.divisors)
        (fun k _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n k, by omega⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hinner : ∑ k ∈ (Finset.range n).filter (fun k => n.gcd k = d), n.gcd k
       = ∑ k ∈ (Finset.range n).filter (fun k => n.gcd k = d), d := by
    apply Finset.sum_congr rfl; intro k hk
    exact (Finset.mem_filter.1 hk).2
  rw [hinner, Finset.sum_const, smul_eq_mul, Nat.totient_div_of_dvd hdvd, mul_comm]

/-- Totient as an arithmetic function. -/
def φA : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

@[simp] theorem φA_apply (n : ℕ) : φA n = Nat.totient n := rfl

theorem φA_isMult : ArithmeticFunction.IsMultiplicative φA :=
  ⟨by simp, fun {m n} h => by simpa using Nat.totient_mul h⟩

/-- Pillai as a Dirichlet convolution `id ⋆ φ`. -/
noncomputable def pillaiA : ArithmeticFunction ℕ := ArithmeticFunction.id * φA

theorem pillaiA_isMult : ArithmeticFunction.IsMultiplicative pillaiA :=
  ArithmeticFunction.isMultiplicative_id.mul φA_isMult

theorem pillaiA_eq_P (n : ℕ) (hn : 1 ≤ n) : pillaiA n = P n := by
  rw [P_eq_divisorsum n hn, pillaiA, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.id a * φA b)]
  apply Finset.sum_congr rfl
  intro d hd
  simp [ArithmeticFunction.id_apply]

/-- `P` is multiplicative on coprime arguments. -/
theorem P_mul_coprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : Nat.Coprime m n) :
    P (m * n) = P m * P n := by
  rw [← pillaiA_eq_P _ (Nat.mul_pos hm hn), ← pillaiA_eq_P _ hm, ← pillaiA_eq_P _ hn]
  exact pillaiA_isMult.2 h

/-- For a prime `p`, `P p = 2p - 1`. -/
theorem P_prime {p : ℕ} (hp : p.Prime) : P p = 2 * p - 1 := by
  rw [P_eq_divisorsum p hp.one_le, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  rw [Nat.div_one, Nat.div_self hp.pos, Nat.totient_prime hp, Nat.totient_one]
  have := hp.two_le; omega

theorem a_eq (n : ℕ) : a n = n / Nat.gcd n (1 + P n) := rfl

/-- If `N ∣ 1 + P N` and `N ≥ 1`, then `a N = 1`. -/
theorem a_eq_one_of_dvd {N : ℕ} (hpos : 1 ≤ N) (hdvd : N ∣ 1 + P N) : a N = 1 := by
  rw [a_eq, Nat.gcd_eq_left hdvd, Nat.div_self hpos]

/- ### The disproof.

The conjecture asserts that `a n = 1` iff `n = 1` or `n` is prime.  It is **false**.
The number `N = 3 · 37 · 43 · 42307 · 116341 = 23492890653051` is squarefree composite,
and since `P` is multiplicative with `P p = 2p - 1`, we have
`P N = 5 · 73 · 85 · 84613 · 232681 = 610815156979325`, whence
`1 + P N = 610815156979326 = 26 · N`, so `N ∣ 1 + P N` and therefore `a N = 1`,
even though `N` is not prime. -/

theorem oeis_340079_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), (a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  -- Refute via the explicit composite witness `N = 3·37·43·42307·116341`.
  have h3 : Nat.Prime 3 := by norm_num
  have h37 : Nat.Prime 37 := by norm_num
  have h43 : Nat.Prime 43 := by norm_num
  have h42307 : Nat.Prime 42307 := by norm_num
  have h116341 : Nat.Prime 116341 := by norm_num
  have e3 : P 3 = 5 := by rw [P_prime h3]
  have e37 : P 37 = 73 := by rw [P_prime h37]
  have e43 : P 43 = 85 := by rw [P_prime h43]
  have e42307 : P 42307 = 84613 := by rw [P_prime h42307]
  have e116341 : P 116341 = 232681 := by rw [P_prime h116341]
  have q1 : P (3 * 37) = P 3 * P 37 :=
    P_mul_coprime (by norm_num) (by norm_num) (by norm_num)
  have q2 : P (3 * 37 * 43) = P (3 * 37) * P 43 :=
    P_mul_coprime (by norm_num) (by norm_num) (by norm_num)
  have q3 : P (3 * 37 * 43 * 42307) = P (3 * 37 * 43) * P 42307 :=
    P_mul_coprime (by norm_num) (by norm_num) (by norm_num)
  have q4 : P (3 * 37 * 43 * 42307 * 116341) = P (3 * 37 * 43 * 42307) * P 116341 :=
    P_mul_coprime (by norm_num) (by norm_num) (by norm_num)
  have hPN : P (3 * 37 * 43 * 42307 * 116341) = 610815156979325 := by
    rw [q4, q3, q2, q1, e3, e37, e43, e42307, e116341]
  -- The conjecture, applied to `N`, would force `N` to be `1` or prime; contradiction.
  intro h
  have key : a (3 * 37 * 43 * 42307 * 116341) = 1 :=
    a_eq_one_of_dvd (by norm_num) (by rw [hPN]; norm_num)
  rcases (h _).mp key with h1 | hp
  · exact absurd h1 (by norm_num)
  · exact absurd hp (by norm_num)
