import FormalConjectures.Util.ProblemImports

open Nat

set_option maxHeartbeats 5000000


/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot (2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := (12 * n + 6)! * (6 * n + 9)!
  let den_base : ℕ := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  num / (108 * den_base)

lemma triple_div (q K : ℕ) (hq : 0 < q) :
    (3*K)/q = 3*(K/q)+(3*(K%q))/q := by
  nth_rewrite 1 [← Nat.div_add_mod K q]
  rw [mul_add]
  conv_lhs => ring_nf
  rw [Nat.mul_assoc q (K / q) 3]
  rw [mul_comm (K / q) 3]
  rw [Nat.mul_add_div hq]
  ring_nf

lemma add_div_decomp (q K L : ℕ) (hq : 0 < q) :
    (K+L)/q = K/q + L/q + ((K%q + L%q)/q) := by
  nth_rewrite 1 [← Nat.div_add_mod K q]
  nth_rewrite 1 [← Nat.div_add_mod L q]
  conv_lhs => ring_nf
  rw [← Nat.mul_add]
  rw [Nat.add_assoc]
  rw [Nat.mul_add_div hq]

lemma rem_ineq (q r s : ℕ) (hq : 0 < q) (hr : r < q) (hs : s < q) :
    2 * ((r + s) / q) ≤ (3 * r) / q + (3 * s) / q := by
  by_cases hsum : r + s < q
  · have hdiv : (r + s) / q = 0 := Nat.div_eq_of_lt hsum
    rw [hdiv]
    exact Nat.zero_le _
  · have hsum' : q ≤ r + s := le_of_not_gt hsum
    by_cases hr1 : q ≤ 3 * r
    · by_cases hs1 : q ≤ 3 * s
      · have ar : 1 ≤ (3 * r) / q := (Nat.le_div_iff_mul_le hq).2 (by simpa using hr1)
        have as_ : 1 ≤ (3 * s) / q := (Nat.le_div_iff_mul_le hq).2 (by simpa using hs1)
        have hleft : (r + s) / q ≤ 1 := by
          rw [Nat.div_le_iff_le_mul hq]
          omega
        calc
          2 * ((r + s) / q) ≤ 2 * 1 := Nat.mul_le_mul_left 2 hleft
          _ ≤ (3 * r) / q + (3 * s) / q := by simpa using Nat.add_le_add ar as_
      · have hslt : 3 * s < q := lt_of_not_ge hs1
        have h2r : 2 * q ≤ 3 * r := by omega
        have ar2 : 2 ≤ (3 * r) / q := (Nat.le_div_iff_mul_le hq).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h2r)
        have hleft : (r + s) / q ≤ 1 := by
          rw [Nat.div_le_iff_le_mul hq]
          omega
        calc
          2 * ((r + s) / q) ≤ 2 * 1 := Nat.mul_le_mul_left 2 hleft
          _ ≤ (3 * r) / q := by simpa using ar2
          _ ≤ (3 * r) / q + (3 * s) / q := Nat.le_add_right _ _
    · have hrlt : 3 * r < q := lt_of_not_ge hr1
      have h2s : 2 * q ≤ 3 * s := by omega
      have as2 : 2 ≤ (3 * s) / q := (Nat.le_div_iff_mul_le hq).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h2s)
      have hleft : (r + s) / q ≤ 1 := by
        rw [Nat.div_le_iff_le_mul hq]
        omega
      calc
        2 * ((r + s) / q) ≤ 2 * 1 := Nat.mul_le_mul_left 2 hleft
        _ ≤ (3 * s) / q := by simpa using as2
        _ ≤ (3 * r) / q + (3 * s) / q := Nat.le_add_left _ _

lemma term_ineq (q K L : ℕ) (hq : 0 < q) :
    K / q + L / q + 2 * ((K + L) / q) ≤ (3 * K) / q + (3 * L) / q := by
  rw [triple_div q K hq, triple_div q L hq, add_div_decomp q K L hq]
  have hrem := rem_ineq q (K % q) (L % q) hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hq)
  omega

lemma base_dvd (K L : ℕ) : K ! * L ! * ((K+L)!)^2 ∣ (3*K)! * (3*L)! := by
  rw [pow_two]
  apply (Nat.factorization_le_iff_dvd
    (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero K) (Nat.factorial_ne_zero L))
      (mul_ne_zero (Nat.factorial_ne_zero (K + L)) (Nat.factorial_ne_zero (K + L))))
    (mul_ne_zero (Nat.factorial_ne_zero (3 * K)) (Nat.factorial_ne_zero (3 * L)))).1
  intro p
  by_cases hp : p.Prime
  · let b := 3 * (K + L) + 1
    have hbK : Nat.log p K < b := by
      by_cases hK : K = 0
      · simp [hK, b]
      · exact (Nat.log_lt_self p hK).trans_le (by omega)
    have hbL : Nat.log p L < b := by
      by_cases hL : L = 0
      · simp [hL, b]
      · exact (Nat.log_lt_self p hL).trans_le (by omega)
    have hbM : Nat.log p (K+L) < b := by
      by_cases hM : K+L = 0
      · simp [hM, b]
      · exact (Nat.log_lt_self p hM).trans_le (by omega)
    have hb3K : Nat.log p (3*K) < b := by
      by_cases hK : 3*K = 0
      · simp [hK, b]
      · exact (Nat.log_lt_self p hK).trans_le (by omega)
    have hb3L : Nat.log p (3*L) < b := by
      by_cases hL : 3*L = 0
      · simp [hL, b]
      · exact (Nat.log_lt_self p hL).trans_le (by omega)
    have hKL : K ! * L ! ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero K) (Nat.factorial_ne_zero L)
    have hMM : (K + L)! * (K + L)! ≠ 0 :=
      mul_ne_zero (Nat.factorial_ne_zero (K + L)) (Nat.factorial_ne_zero (K + L))
    rw [Nat.factorization_mul hKL hMM,
      Nat.factorization_mul (Nat.factorial_ne_zero K) (Nat.factorial_ne_zero L),
      Nat.factorization_mul (Nat.factorial_ne_zero (K + L)) (Nat.factorial_ne_zero (K + L)),
      Nat.factorization_mul (Nat.factorial_ne_zero (3 * K)) (Nat.factorial_ne_zero (3 * L))]
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [Nat.factorization_factorial hp hbK, Nat.factorization_factorial hp hbL,
      Nat.factorization_factorial hp hbM, Nat.factorization_factorial hp hb3K,
      Nat.factorization_factorial hp hb3L]
    let S := Finset.Ico 1 b
    have hsum :
        (∑ i ∈ S, (K / p ^ i + L / p ^ i + 2 * ((K + L) / p ^ i))) ≤
          ∑ i ∈ S, ((3 * K) / p ^ i + (3 * L) / p ^ i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact term_ineq (p ^ i) K L (pow_pos hp.pos _)
    simpa [S, Finset.sum_add_distrib, two_mul, Nat.mul_two, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hsum
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma v3_fac_3a2 (a : ℕ) : ((3*a+2)!).factorization 3 = (a !).factorization 3 + a := by
  have hp : Nat.Prime 3 := by norm_num
  have h1 : ¬ 3 ∣ 3*a + 1 := by omega
  have h2 : ¬ 3 ∣ 3*a + 2 := by omega
  rw [show 3*a+2 = (3*a+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorization_mul (by omega) (Nat.factorial_ne_zero (3*a+1))]
  simp [Nat.factorization_eq_zero_of_not_dvd h2, Finsupp.coe_add, Pi.add_apply]
  rw [show 3*a+1 = (3*a)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorization_mul (by omega) (Nat.factorial_ne_zero (3*a))]
  simp [Nat.factorization_eq_zero_of_not_dvd h1, Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_factorial_mul (p:=3) (n:=a) hp]

lemma v3_bound (n : ℕ) : 3 + 2 * ((6*n+5)!).factorization 3 ≤ 6*n+5 := by
  let a := 2*n+1
  have ha : 6*n+5 = 3*a+2 := by dsimp [a]; omega
  rw [ha, v3_fac_3a2]
  have hp : Nat.Prime 3 := by norm_num
  have hb := Nat.factorization_factorial_le_div_pred hp a
  dsimp [a] at hb ⊢
  omega

lemma p2_sum_extra (n : ℕ) :
  2 + ((∑ i ∈ Finset.Ico 1 (12*n+10), (4*n+2) / 2 ^ i) +
      (∑ i ∈ Finset.Ico 1 (12*n+10), (2*n+3) / 2 ^ i) +
      ((∑ i ∈ Finset.Ico 1 (12*n+10), (6*n+5) / 2 ^ i) +
       (∑ i ∈ Finset.Ico 1 (12*n+10), (6*n+5) / 2 ^ i))) ≤
    (∑ i ∈ Finset.Ico 1 (12*n+10), (12*n+6) / 2 ^ i) +
    (∑ i ∈ Finset.Ico 1 (12*n+10), (6*n+9) / 2 ^ i) := by
  let S := Finset.Ico 1 (12*n+10)
  let w : ℕ → ℕ := fun i => (if i = 1 then 1 else 0) + (if i = 2 then 1 else 0)
  have h1b : 1 < 12*n+10 := by omega
  have h2b : 2 < 12*n+10 := by omega
  have h1bn : 1 < 10 + n * 12 := by omega
  have h2bn : 2 < 10 + n * 12 := by omega
  have hsum :
      (∑ i ∈ S, (w i + ((4*n+2) / 2 ^ i + (2*n+3) / 2 ^ i +
          ((6*n+5) / 2 ^ i + (6*n+5) / 2 ^ i)))) ≤
        ∑ i ∈ S, ((12*n+6) / 2 ^ i + (6*n+9) / 2 ^ i) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi1 : i = 1
    · subst i
      simp [w]
      omega
    · by_cases hi2 : i = 2
      · subst i
        simp [w]
        have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h with h | h <;> omega
      · have ht := term_ineq (2^i) (2*n+3) (4*n+2) (pow_pos (by norm_num) i)
        simp [w, hi1, hi2]
        have hm : n + (n + (2 + (3 + n * 4))) = 5 + n * 6 := by omega
        have hA : 3 * (n + (n + 3)) = n * 6 + 9 := by omega
        have hB : 3 * (2 + n * 4) = 6 + n * 12 := by omega
        simpa [hm, hA, hB, two_mul, Nat.mul_two, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc] using ht
  simp [S, w, Finset.sum_add_distrib] at hsum ⊢
  omega

lemma prime_not_dvd_108 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ∣ 108 := by
  intro h
  have h' : p ∣ 2 ^ 2 * 3 ^ 3 := by norm_num at h ⊢; exact h
  have hcases := (hp.dvd_mul).1 h'
  rcases hcases with h2 | h3
  · have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have hp_eq : p = 2 := by
      have hx := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).1 hp2dvd
      rcases hx with h | h
      · exact (hp.ne_one h).elim
      · exact h
    exact hp2 hp_eq
  · have hp3dvd : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have hp_eq : p = 3 := by
      have hx := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hp3dvd
      rcases hx with h | h
      · exact (hp.ne_one h).elim
      · exact h
    exact hp3 hp_eq


lemma factorization_108_two : (108).factorization 2 = 2 := by
  rw [show 108 = 2^2 * 3^3 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_pow_self (by norm_num : Nat.Prime 2)]
  have h3 : (3 ^ 3).factorization 2 = 0 := by
    rw [Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3)]
    exact Finsupp.single_eq_of_ne (by norm_num : 2 ≠ 3)
  rw [h3]

lemma factorization_108_three : (108).factorization 3 = 3 := by
  rw [show 108 = 2^2 * 3^3 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_pow_self (by norm_num : Nat.Prime 3)]
  have h2 : (2 ^ 2).factorization 3 = 0 := by
    rw [Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2)]
    exact Finsupp.single_eq_of_ne (by norm_num : 3 ≠ 2)
  rw [h2]

/--
Conjecture from OEIS A368692: $a(n)$ is an integer for all $n \in \mathbb{N}$.
According to A. Adolphson and S. Sperber, "On the integrality of hypergeometric series
whose coefficients are factorial ratios", ArXiv: 2001.03296, s.page 14, first equation
after Eq.(7.4): for any two integers K, L, the ratios $(3K)!(3L)!/(K!L!((K+L)!)^2)$
are proven to be integers. $108 \cdot a(n)$ results from $K = 4n+2$ and $L = 2n+3$, $n \ge 0$.
It is conjectured here that $a(n)$ are integers.
This is equivalent to the denominator dividing the numerator exactly in the definition
of $a(n)$.
-/
theorem oeis_a368692_conjecture_integrality (n : ℕ) :
  108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ∣ (12 * n + 6)! * (6 * n + 9)! := by
  rw [pow_two]
  apply (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      have hKL : (4*n+2)! * (2*n+3)! ≠ 0 :=
        mul_ne_zero (Nat.factorial_ne_zero (4*n+2)) (Nat.factorial_ne_zero (2*n+3))
      have hMM : (6*n+5)! * (6*n+5)! ≠ 0 :=
        mul_ne_zero (Nat.factorial_ne_zero (6*n+5)) (Nat.factorial_ne_zero (6*n+5))
      have hBase : (4*n+2)! * (2*n+3)! * ((6*n+5)! * (6*n+5)!) ≠ 0 :=
        mul_ne_zero hKL hMM
      rw [Nat.factorization_mul (by norm_num : 108 ≠ 0) hBase,
        Nat.factorization_mul hKL hMM,
        Nat.factorization_mul (Nat.factorial_ne_zero (4*n+2)) (Nat.factorial_ne_zero (2*n+3)),
        Nat.factorization_mul (Nat.factorial_ne_zero (6*n+5)) (Nat.factorial_ne_zero (6*n+5)),
        Nat.factorization_mul (Nat.factorial_ne_zero (12*n+6)) (Nat.factorial_ne_zero (6*n+9))]
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [factorization_108_two]
      let b := 12*n+10
      have hbK : Nat.log 2 (4*n+2) < b := (Nat.log_lt_self 2 (by omega)).trans_le (by omega)
      have hbL : Nat.log 2 (2*n+3) < b := (Nat.log_lt_self 2 (by omega)).trans_le (by omega)
      have hbM : Nat.log 2 (6*n+5) < b := (Nat.log_lt_self 2 (by omega)).trans_le (by omega)
      have hbN1 : Nat.log 2 (12*n+6) < b := (Nat.log_lt_self 2 (by omega)).trans_le (by omega)
      have hbN2 : Nat.log 2 (6*n+9) < b := (Nat.log_lt_self 2 (by omega)).trans_le (by omega)
      rw [Nat.factorization_factorial (by norm_num : Nat.Prime 2) hbK,
        Nat.factorization_factorial (by norm_num : Nat.Prime 2) hbL,
        Nat.factorization_factorial (by norm_num : Nat.Prime 2) hbM,
        Nat.factorization_factorial (by norm_num : Nat.Prime 2) hbN1,
        Nat.factorization_factorial (by norm_num : Nat.Prime 2) hbN2]
      exact p2_sum_extra n
    · by_cases hp3 : p = 3
      · subst p
        have hKL : (4*n+2)! * (2*n+3)! ≠ 0 :=
          mul_ne_zero (Nat.factorial_ne_zero (4*n+2)) (Nat.factorial_ne_zero (2*n+3))
        have hMM : (6*n+5)! * (6*n+5)! ≠ 0 :=
          mul_ne_zero (Nat.factorial_ne_zero (6*n+5)) (Nat.factorial_ne_zero (6*n+5))
        have hBase : (4*n+2)! * (2*n+3)! * ((6*n+5)! * (6*n+5)!) ≠ 0 :=
          mul_ne_zero hKL hMM
        rw [Nat.factorization_mul (by norm_num : 108 ≠ 0) hBase,
          Nat.factorization_mul hKL hMM,
          Nat.factorization_mul (Nat.factorial_ne_zero (4*n+2)) (Nat.factorial_ne_zero (2*n+3)),
          Nat.factorization_mul (Nat.factorial_ne_zero (6*n+5)) (Nat.factorial_ne_zero (6*n+5)),
          Nat.factorization_mul (Nat.factorial_ne_zero (12*n+6)) (Nat.factorial_ne_zero (6*n+9))]
        simp only [Finsupp.coe_add, Pi.add_apply]
        rw [factorization_108_three]
        rw [show 12*n+6 = 3*(4*n+2) by omega,
          show 6*n+9 = 3*(2*n+3) by omega]
        rw [Nat.factorization_factorial_mul (p:=3) (n:=4*n+2) (by norm_num : Nat.Prime 3),
          Nat.factorization_factorial_mul (p:=3) (n:=2*n+3) (by norm_num : Nat.Prime 3)]
        have hb := v3_bound n
        omega
      · have h108 : (108).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_108 hp hp2 hp3)
        have hbase := (Nat.factorization_le_iff_dvd
          (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero (4*n+2)) (Nat.factorial_ne_zero (2*n+3)))
            (mul_ne_zero (Nat.factorial_ne_zero (6*n+5)) (Nat.factorial_ne_zero (6*n+5))))
          (mul_ne_zero (Nat.factorial_ne_zero (12*n+6)) (Nat.factorial_ne_zero (6*n+9)))).2 ?_ p
        · have hKL : (4*n+2)! * (2*n+3)! ≠ 0 :=
            mul_ne_zero (Nat.factorial_ne_zero (4*n+2)) (Nat.factorial_ne_zero (2*n+3))
          have hMM : (6*n+5)! * (6*n+5)! ≠ 0 :=
            mul_ne_zero (Nat.factorial_ne_zero (6*n+5)) (Nat.factorial_ne_zero (6*n+5))
          have hBase : (4*n+2)! * (2*n+3)! * ((6*n+5)! * (6*n+5)!) ≠ 0 :=
            mul_ne_zero hKL hMM
          rw [Nat.factorization_mul (by norm_num : 108 ≠ 0) hBase]
          simp only [Finsupp.coe_add, Pi.add_apply, h108, zero_add]
          exact hbase
        · simpa [show 12*n+6 = 3*(4*n+2) by omega, show 6*n+9 = 3*(2*n+3) by omega,
            show 6*n+5 = (4*n+2)+(2*n+3) by omega, pow_two] using base_dvd (4*n+2) (2*n+3)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
