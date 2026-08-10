import FormalConjectures.Util.ProblemImports

open Nat

/--
The $d$-th triangular number, $T(d) = d(d+1)/2$.
-/
def T_triangular (d : ℕ) : ℕ := d * (d + 1) / 2

/--
A275786: $a(n) = \prod_{d|n} T(d)$ where $T(x)$ is the $x$-th triangular number.
-/
def a (n : ℕ) : ℕ :=
  (Nat.divisors n).prod T_triangular

/-!
## Provable structural lemmas towards A275786 injectivity

The following lemmas are fully proved (no `sorry`) and capture genuine
mathematical content towards the conjecture, culminating in the rigorous
reduction that any hypothetical collision `a n = a m` (with `n ≠ m`) must
have BOTH indices composite.
-/

theorem one_le_T {d : ℕ} (hd : 1 ≤ d) : 1 ≤ T_triangular d := by
  unfold T_triangular
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

theorem T_mono {x y : ℕ} (h : x ≤ y) : T_triangular x ≤ T_triangular y := by
  unfold T_triangular; apply Nat.div_le_div_right; nlinarith

theorem two_T (d : ℕ) : 2 * T_triangular d = d * (d + 1) := by
  unfold T_triangular
  rw [Nat.mul_div_cancel']
  exact even_mul_succ_self d |>.two_dvd

theorem T_strictmono {x y : ℕ} (h : x < y) : T_triangular x < T_triangular y := by
  have h1 := two_T x; have h2 := two_T y
  have : x * (x + 1) < y * (y + 1) := by nlinarith
  omega

theorem T_dvd_a {n : ℕ} (hn : 0 < n) : T_triangular n ∣ a n := by
  apply Finset.dvd_prod_of_mem
  simp [Nat.mem_divisors]
  exact hn.ne'

theorem T_le_a {n : ℕ} (hn : 0 < n) : T_triangular n ≤ a n := by
  unfold a
  have hmem : n ∈ Nat.divisors n := by simp [Nat.mem_divisors]; exact hn.ne'
  apply Finset.single_le_prod' (f := T_triangular)
  · intro i hi
    rw [Nat.mem_divisors] at hi
    have : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hi)
    exact one_le_T this
  · exact hmem

theorem a_dvd_a_of_dvd {d n : ℕ} (hn : 0 < n) (hdn : d ∣ n) : a d ∣ a n := by
  unfold a
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  rw [Nat.mem_divisors] at hx ⊢
  exact ⟨hx.1.trans hdn, hn.ne'⟩

theorem a_prime {p : ℕ} (hp : p.Prime) : a p = T_triangular p := by
  unfold a
  rw [hp.divisors, Finset.prod_insert (by simp; exact hp.one_lt.ne)]
  simp [T_triangular]

theorem a_one : a 1 = 1 := by decide

/-- Lemma A: every prime factor `q` of `a n` satisfies `q ≤ n + 1`. -/
theorem primeFactor_le {n q : ℕ} (hn : 0 < n) (hq : q.Prime) (hqa : q ∣ a n) :
    q ≤ n + 1 := by
  unfold a at hqa
  rw [Prime.dvd_finset_prod_iff hq.prime] at hqa
  obtain ⟨d, hd, hqd⟩ := hqa
  rw [Nat.mem_divisors] at hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd)
  have hq2 : q ∣ d * (d + 1) := by
    have : q ∣ 2 * T_triangular d := Dvd.dvd.mul_left hqd 2
    rwa [two_T] at this
  rcases (hq.dvd_mul.mp hq2) with h | h
  · exact le_trans (Nat.le_of_dvd hd0 h) (by have := Nat.le_of_dvd hn hd.1; omega)
  · have : q ≤ d + 1 := Nat.le_of_dvd (by omega) h
    have := Nat.le_of_dvd hn hd.1; omega

/-- For composite `n` (witnessed by `1 < e < n`), `a n ≥ 3 · T(n)`. -/
theorem a_ge_three_T {n : ℕ} (hn : 0 < n) (e : ℕ) (hen : e ∣ n) (he1 : 1 < e) (he2 : e < n) :
    3 * T_triangular n ≤ a n := by
  unfold a
  have hsub : ({1, e, n} : Finset ℕ) ⊆ Nat.divisors n := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    rcases hx with rfl | rfl | rfl
    · exact ⟨one_dvd _, hn.ne'⟩
    · exact ⟨hen, hn.ne'⟩
    · exact ⟨dvd_refl _, hn.ne'⟩
  have hprod : (({1, e, n} : Finset ℕ)).prod T_triangular ≤ (Nat.divisors n).prod T_triangular := by
    apply Finset.prod_le_prod_of_subset_of_one_le' hsub
    intro i hi _; rw [Nat.mem_divisors] at hi
    exact one_le_T (Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hi))
  refine le_trans ?_ hprod
  rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega), Finset.prod_singleton]
  have hT1 : T_triangular 1 = 1 := by decide
  rw [hT1, one_mul]
  have hTe : 3 ≤ T_triangular e := by
    have : T_triangular 2 ≤ T_triangular e := T_mono (by omega); simpa [T_triangular] using this
  exact Nat.mul_le_mul_right _ hTe

/-- REDUCTION (smaller index): in a collision `a n = a m` with `n < m`, `n` is composite. -/
theorem smaller_composite {n m : ℕ} (hn : 0 < n) (hnm : n < m) (heq : a n = a m) :
    2 ≤ n ∧ ¬ n.Prime := by
  have hTm : T_triangular n < T_triangular m := T_strictmono hnm
  have ham : T_triangular m ≤ a m := T_le_a (by omega)
  have hgt : T_triangular n < a n := by rw [heq]; omega
  have hn1 : n ≠ 1 := by rintro rfl; rw [a_one] at hgt; revert hgt; decide
  refine ⟨by omega, ?_⟩
  intro hp; rw [a_prime hp] at hgt; exact lt_irrefl _ hgt

/-- REDUCTION (larger index): in a collision `a n = a m` with `n < m`, `m` is composite. -/
theorem larger_composite {n m : ℕ} (hn : 0 < n) (hnm : n < m) (heq : a n = a m) :
    ¬ m.Prime := by
  obtain ⟨hn2, hnp⟩ := smaller_composite hn hnm heq
  intro hpm
  have ham : a m = T_triangular m := a_prime hpm
  have hmcop : Nat.Coprime m 2 := (Nat.coprime_primes hpm Nat.prime_two).mpr (by omega)
  have hmT : m ∣ T_triangular m := by
    have h2 : m ∣ 2 * T_triangular m := by rw [two_T]; exact dvd_mul_right m (m+1)
    exact hmcop.dvd_of_dvd_mul_left h2
  have hdvd : m ∣ a n := by rw [heq, ham]; exact hmT
  have hle : m ≤ n + 1 := primeFactor_le hn hpm hdvd
  have hmn1 : m = n + 1 := by omega
  obtain ⟨e, hen, he1, he2⟩ := Nat.exists_dvd_of_not_prime2 hn2 hnp
  have hge : 3 * T_triangular n ≤ a n := a_ge_three_T hn e hen he1 he2
  have heqn : a n = T_triangular (n + 1) := by rw [heq, ham, hmn1]
  have t1 := two_T n; have t2 := two_T (n + 1)
  have hcontra : T_triangular (n + 1) < 3 * T_triangular n := by nlinarith [t1, t2]
  omega

/-- SMOOTHNESS COROLLARY: in a collision `a n = a m` with `n < m`, every prime
factor `q` of `m * (m+1)` satisfies `q ≤ n + 1`; i.e. both `m` and `m+1` are
`(n+1)`-smooth. This makes explicit the Størmer/Baker-type Diophantine obstruction
at the heart of the remaining (composite-composite) case. -/
theorem collision_smooth {n m : ℕ} (hn : 0 < n) (hnm : n < m) (heq : a n = a m)
    {q : ℕ} (hq : q.Prime) (hqm : q ∣ m * (m + 1)) : q ≤ n + 1 := by
  have hTm : T_triangular m ∣ a n := by rw [heq]; exact T_dvd_a (by omega)
  rcases hq.eq_two_or_odd' with h2 | hodd
  · subst h2; omega
  · -- q odd: q ∣ 2 * T(m) = m*(m+1), coprime to 2, so q ∣ T(m) ∣ a n
    have hq2T : q ∣ 2 * T_triangular m := by rw [two_T]; exact hqm
    have hne : q ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
    have hcop : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).mpr hne
    have hqT : q ∣ T_triangular m := hcop.dvd_of_dvd_mul_left hq2T
    exact primeFactor_le hn hq (hqT.trans hTm)

/-- REDUCTION (successor of larger index): in a collision `a n = a m` with `n < m`,
`m + 1` is composite. If `m+1` were a (necessarily odd) prime `P`, then
`P ∣ T(m) ∣ a m = a n`, forcing `P ≤ n+1` by `primeFactor_le`, contradicting
`P = m+1 > n+1`. -/
theorem larger_succ_composite {n m : ℕ} (hn : 0 < n) (hnm : n < m) (heq : a n = a m) :
    ¬ (m + 1).Prime := by
  intro hp
  have hodd : (m + 1) ≠ 2 := by omega
  have hcop : Nat.Coprime (m + 1) 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hodd
  have h2 : (m + 1) ∣ 2 * T_triangular m := by rw [two_T]; exact dvd_mul_left (m + 1) m
  have hPT : (m + 1) ∣ T_triangular m := hcop.dvd_of_dvd_mul_left h2
  have hPa : (m + 1) ∣ a n := by rw [heq]; exact hPT.trans (T_dvd_a (by omega))
  have hle : m + 1 ≤ n + 1 := primeFactor_le hn hp hPa
  omega

/-- The product of the divisors of `n`, squared, equals `n^τ(n)`:
`(∏_{d|n} d)^2 = n^{τ(n)}` (the classical divisor-product identity). -/
theorem prod_divisors_sq (n : ℕ) :
    (Nat.divisors n).prod (fun d => d) ^ 2 = n ^ (Nat.divisors n).card := by
  rw [sq]
  nth_rewrite 2 [← Nat.prod_div_divisors n (fun d => d)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro d hd
  rw [Nat.mem_divisors] at hd
  exact Nat.mul_div_cancel' hd.1

/-- `2^τ(n) · a(n) = ∏_{d|n} d(d+1)`. -/
theorem two_pow_mul_a (n : ℕ) :
    2 ^ (Nat.divisors n).card * a n = (Nat.divisors n).prod (fun d => d * (d + 1)) := by
  unfold a
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro d _
  exact two_T d

/-- Size lower bound: `n^τ(n) ≤ 2^τ(n) · a(n)`, equivalently `a(n) ≥ (n/2)^τ(n)`.
This is the key quantitative ingredient that, combined with the upper bound,
controls collisions and underlies the prime-square exclusion. -/
theorem a_lower_bound (n : ℕ) :
    n ^ (Nat.divisors n).card ≤ 2 ^ (Nat.divisors n).card * a n := by
  rw [two_pow_mul_a, ← prod_divisors_sq, sq, Finset.prod_mul_distrib]
  apply mul_le_mul_left'
  apply Finset.prod_le_prod'
  intro d _
  omega

/-- Size upper bound: `2^τ(n) · a(n) ≤ (2n)^τ(n)`, equivalently `a(n) ≤ n^τ(n)`.
Together with `a_lower_bound` this pins `a(n)` to the window `[(n/2)^τ, n^τ]`. -/
theorem a_upper_bound (n : ℕ) :
    2 ^ (Nat.divisors n).card * a n ≤ (2 * n) ^ (Nat.divisors n).card := by
  rw [two_pow_mul_a]
  have step : (Nat.divisors n).prod (fun d => d * (d + 1))
      ≤ (Nat.divisors n).prod (fun d => 2 * (d * d)) := by
    apply Finset.prod_le_prod'
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    nlinarith
  refine le_trans step ?_
  have hprod : (Nat.divisors n).prod (fun d => 2 * (d * d))
      = (2 * n) ^ (Nat.divisors n).card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_mul_distrib, ← sq,
      prod_divisors_sq, mul_pow]
  rw [hprod]

/-- A275786 Conjecture: the sequence is injective (all terms of this sequence occur only once). -/
theorem oeis_A275786_conjecture :
  ∀ n m : ℕ, n > 0 → m > 0 → (a n = a m → n = m) :=
  by sorry
