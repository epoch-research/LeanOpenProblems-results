import FormalConjectures.Util.ProblemImports

open Nat

/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot (2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := (12 * n + 6)! * (6 * n + 9)!
  let den_base : ℕ := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  num / (108 * den_base)

theorem rem_floor_ineq (rK rL d : ℕ) (hd : 0 < d) (h_rK : rK < d) (h_rL : rL < d) :
    3 * rK / d + 3 * rL / d ≥ 2 * ((rK + rL) / d) := by
  have h1 : 3 * rK / d < 3 := Nat.div_lt_of_lt_mul (by omega)
  have h2 : 3 * rL / d < 3 := Nat.div_lt_of_lt_mul (by omega)
  have h3 : (rK + rL) / d < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hd1 : d * (3 * rK / d) + (3 * rK % d) = 3 * rK := (Nat.div_add_mod (3 * rK) d)
  have hd2 : d * (3 * rL / d) + (3 * rL % d) = 3 * rL := (Nat.div_add_mod (3 * rL) d)
  have hd3 : d * ((rK + rL) / d) + ((rK + rL) % d) = rK + rL := (Nat.div_add_mod (rK + rL) d)
  have hm1 : 3 * rK % d < d := Nat.mod_lt _ hd
  have hm2 : 3 * rL % d < d := Nat.mod_lt _ hd
  have hm3 : (rK + rL) % d < d := Nat.mod_lt _ hd
  generalize h_v1 : 3 * rK / d = v1 at *
  generalize h_v2 : 3 * rL / d = v2 at *
  generalize h_v3 : (rK + rL) / d = v3 at *
  interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;> omega

theorem floor_ineq (K L d : ℕ) (hd : 0 < d) :
    3 * K / d + 3 * L / d ≥ K / d + L / d + 2 * ((K + L) / d) := by
  set qK := K / d
  set rK := K % d
  set qL := L / d
  set rL := L % d
  have hK : K = d * qK + rK := (Nat.div_add_mod K d).symm
  have hL : L = d * qL + rL := (Nat.div_add_mod L d).symm
  have h_rK : rK < d := Nat.mod_lt K hd
  have h_rL : rL < d := Nat.mod_lt L hd
  have h3K : 3 * K / d = 3 * qK + 3 * rK / d := by
    rw [hK]
    have : 3 * (d * qK + rK) = d * (3 * qK) + 3 * rK := by ring
    rw [this, add_comm, mul_comm d (3 * qK), Nat.add_mul_div_right (3 * rK) (3 * qK) hd, add_comm]
  have h3L : 3 * L / d = 3 * qL + 3 * rL / d := by
    rw [hL]
    have : 3 * (d * qL + rL) = d * (3 * qL) + 3 * rL := by ring
    rw [this, add_comm, mul_comm d (3 * qL), Nat.add_mul_div_right (3 * rL) (3 * qL) hd, add_comm]
  have hKL : (K + L) / d = qK + qL + (rK + rL) / d := by
    rw [hK, hL]
    have : d * qK + rK + (d * qL + rL) = d * (qK + qL) + (rK + rL) := by ring
    rw [this, add_comm, mul_comm d (qK + qL), Nat.add_mul_div_right (rK + rL) (qK + qL) hd, add_comm]
  rw [h3K, h3L, hKL]
  have := rem_floor_ineq rK rL d hd h_rK h_rL
  omega

lemma digits_sum_le (n : ℕ) (p : ℕ) (hp : p.Prime) : (p.digits n).sum ≤ n := by
  have : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p := by omega
  have h_le := sum_le_ofDigits (p.digits n) hp1
  rw [ofDigits_digits p n] at h_le
  exact h_le

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

lemma oeis_a368692_conjecture_p2 (n : ℕ) (hb : 12 * n + 10 ≥ 5) :
  2 + ∑ i ∈ Finset.Ico 1 (12 * n + 10), ((4 * n + 2) / 2 ^ i + ((2 * n + 3) / 2 ^ i + 2 * ((6 * n + 5) / 2 ^ i))) ≤
      ∑ i ∈ Finset.Ico 1 (12 * n + 10), ((12 * n + 6) / 2 ^ i + (6 * n + 9) / 2 ^ i) := by
  have hb3 : 12 * n + 10 ≥ 3 := by omega
  have h_split : Finset.Ico 1 (12 * n + 10) = Finset.Ico 1 3 ∪ Finset.Ico 3 (12 * n + 10) := by
    rw [Finset.Ico_union_Ico_eq_Ico (show 1 ≤ 3 by decide) hb3]
  rw [h_split, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 3 _), Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 3 _)]
  have h_nonneg : ∑ i ∈ Finset.Ico 3 (12 * n + 10), ((4 * n + 2) / 2 ^ i + ((2 * n + 3) / 2 ^ i + 2 * ((6 * n + 5) / 2 ^ i))) ≤
      ∑ i ∈ Finset.Ico 3 (12 * n + 10), ((12 * n + 6) / 2 ^ i + (6 * n + 9) / 2 ^ i) := by
    apply Finset.sum_le_sum
    intro i hi
    have h_pi_pos : 0 < 2^i := by positivity
    have h_floor := floor_ineq (4 * n + 2) (2 * n + 3) (2^i) h_pi_pos
    have h_eq1 : 3 * (4 * n + 2) = 12 * n + 6 := by ring
    have h_eq2 : 3 * (2 * n + 3) = 6 * n + 9 := by ring
    have h_eq3 : (4 * n + 2) + (2 * n + 3) = 6 * n + 5 := by ring
    rw [h_eq1, h_eq2, h_eq3] at h_floor
    omega
  have h_two_rhs : ∑ i ∈ Finset.Ico 1 3, ((12 * n + 6) / 2 ^ i + (6 * n + 9) / 2 ^ i) ≥
      ∑ i ∈ Finset.Ico 1 3, ((4 * n + 2) / 2 ^ i + ((2 * n + 3) / 2 ^ i + 2 * ((6 * n + 5) / 2 ^ i))) + 2 := by
    have h3 : Finset.Ico 1 3 = Finset.Ico 1 (2 + 1) := by rfl
    rw [h3, ← Finset.insert_Ico_right_eq_Ico_add_one (show 1 ≤ 2 by decide)]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
    have h2 : Finset.Ico 1 2 = Finset.Ico 1 (1 + 1) := by rfl
    rw [h2, ← Finset.insert_Ico_right_eq_Ico_add_one (show 1 ≤ 1 by decide)]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
    rw [Finset.Ico_self]
    simp
    have h_mod : n % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize h_r : n % 4 = r at *
    interval_cases r <;> omega
  omega



lemma ofDigits_eq_zero_of_sum_eq_zero (b : ℕ) (l : List ℕ) (h : l.sum = 0) :
    Nat.ofDigits b l = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.sum_cons] at h
    have h_hd : hd = 0 := by omega
    have h_tl : tl.sum = 0 := by omega
    unfold Nat.ofDigits
    simp [h_hd, ih h_tl]

lemma sum_digits_pos (n : ℕ) (p : ℕ) (_hp : 1 < p) (hn : 0 < n) : 1 ≤ (p.digits n).sum := by
  by_contra hc
  have h_zero : (p.digits n).sum = 0 := by omega
  have h_of := ofDigits_eq_zero_of_sum_eq_zero p (p.digits n) h_zero
  have h_of_digits : Nat.ofDigits p (p.digits n) = n := Nat.ofDigits_digits p n
  rw [h_of] at h_of_digits
  omega

lemma digits12n6_eq (n : ℕ) : (Nat.digits 3 (12 * n + 6)).sum = (Nat.digits 3 (4 * n + 2)).sum := by
  have h_eq : 12 * n + 6 = 3 * (4 * n + 2) := by ring
  rw [h_eq, Nat.digits_base_mul (by decide) (by positivity)]
  simp

lemma digits6n9_eq (n : ℕ) : (Nat.digits 3 (6 * n + 9)).sum = (Nat.digits 3 (2 * n + 3)).sum := by
  have h_eq : 6 * n + 9 = 3 * (2 * n + 3) := by ring
  rw [h_eq, Nat.digits_base_mul (by decide) (by positivity)]
  simp

lemma digits6n5_eq (n : ℕ) : (Nat.digits 3 (6 * n + 5)).sum = 2 + (Nat.digits 3 (2 * n + 1)).sum := by
  have h_eq : 6 * n + 5 = 2 + 3 * (2 * n + 1) := by ring
  rw [h_eq, Nat.digits_add 3 (by decide) 2 (2 * n + 1) (by decide) (Or.inl (by decide))]
  simp

lemma oeis_a368692_conjecture_p3 (n : ℕ) (hb : 12 * n + 10 ≥ 5) :
  3 + ∑ i ∈ Finset.Ico 1 (12 * n + 10), ((4 * n + 2) / 3 ^ i + ((2 * n + 3) / 3 ^ i + 2 * ((6 * n + 5) / 3 ^ i))) ≤
      ∑ i ∈ Finset.Ico 1 (12 * n + 10), ((12 * n + 6) / 3 ^ i + (6 * n + 9) / 3 ^ i) := by
  have h_fact3 : Fact (Nat.Prime 3) := ⟨prime_three⟩
  have h_log_bound (m : ℕ) (hm : m < 12 * n + 10) : log 3 m < 12 * n + 10 := by
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have : log 3 m < m := Nat.log_lt_self 3 (by omega)
      omega
  have hp1 : padicValNat 3 (4 * n + 2).factorial = ∑ i ∈ Finset.Ico 1 (12 * n + 10), (4 * n + 2) / 3 ^ i := by
    rw [padicValNat_factorial (h_log_bound (4 * n + 2) (by omega))]
  have hp2 : padicValNat 3 (2 * n + 3).factorial = ∑ i ∈ Finset.Ico 1 (12 * n + 10), (2 * n + 3) / 3 ^ i := by
    rw [padicValNat_factorial (h_log_bound (2 * n + 3) (by omega))]
  have hp3 : padicValNat 3 (6 * n + 5).factorial = ∑ i ∈ Finset.Ico 1 (12 * n + 10), (6 * n + 5) / 3 ^ i := by
    rw [padicValNat_factorial (h_log_bound (6 * n + 5) (by omega))]
  have hp4 : padicValNat 3 (12 * n + 6).factorial = ∑ i ∈ Finset.Ico 1 (12 * n + 10), (12 * n + 6) / 3 ^ i := by
    rw [padicValNat_factorial (h_log_bound (12 * n + 6) (by omega))]
  have hp5 : padicValNat 3 (6 * n + 9).factorial = ∑ i ∈ Finset.Ico 1 (12 * n + 10), (6 * n + 9) / 3 ^ i := by
    rw [padicValNat_factorial (h_log_bound (6 * n + 9) (by omega))]

  -- Now write the LHS and RHS sums in terms of padicValNat
  have h_lhs_eq : ∑ i ∈ Finset.Ico 1 (12 * n + 10), ((4 * n + 2) / 3 ^ i + ((2 * n + 3) / 3 ^ i + 2 * ((6 * n + 5) / 3 ^ i))) =
      padicValNat 3 (4 * n + 2).factorial + padicValNat 3 (2 * n + 3).factorial + 2 * padicValNat 3 (6 * n + 5).factorial := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hp1, ← hp2, ← hp3]
    omega
  have h_rhs_eq : ∑ i ∈ Finset.Ico 1 (12 * n + 10), ((12 * n + 6) / 3 ^ i + (6 * n + 9) / 3 ^ i) =
      padicValNat 3 (12 * n + 6).factorial + padicValNat 3 (6 * n + 9).factorial := by
    simp only [Finset.sum_add_distrib]
    rw [← hp4, ← hp5]

  rw [h_lhs_eq, h_rhs_eq]

  -- Now multiply by 2 (which is 3 - 1) to use Legendre's formula
  have h_legendre (m : ℕ) : 2 * padicValNat 3 (m.factorial) = m - (Nat.digits 3 m).sum := by
    have h_leg := @sub_one_mul_padicValNat_factorial 3 h_fact3 m
    omega
  
  have h_leg1 := h_legendre (4 * n + 2)
  have h_leg2 := h_legendre (2 * n + 3)
  have h_leg3 := h_legendre (6 * n + 5)
  have h_leg4 := h_legendre (12 * n + 6)
  have h_leg5 := h_legendre (6 * n + 9)

  have h_digits2n1_pos : 1 ≤ (Nat.digits 3 (2 * n + 1)).sum := by
    apply sum_digits_pos
    · decide
    · omega

  have h_goal_mul : 6 + 2 * padicValNat 3 (4 * n + 2).factorial + 2 * padicValNat 3 (2 * n + 3).factorial + 4 * padicValNat 3 (6 * n + 5).factorial ≤
      2 * padicValNat 3 (12 * n + 6).factorial + 2 * padicValNat 3 (6 * n + 9).factorial := by
    have h_leg3_mul : 4 * padicValNat 3 (6 * n + 5).factorial = 2 * (6 * n + 5 - (Nat.digits 3 (6 * n + 5)).sum) := by
      omega
    rw [h_leg1, h_leg2, h_leg3_mul, h_leg4, h_leg5]
    rw [digits12n6_eq, digits6n9_eq, digits6n5_eq]
    have hd1 := digits_sum_le (4 * n + 2) 3 h_fact3.out
    have hd2 := digits_sum_le (2 * n + 3) 3 h_fact3.out
    have hd3 := digits_sum_le (6 * n + 5) 3 h_fact3.out
    have hd4 := digits_sum_le (12 * n + 6) 3 h_fact3.out
    have hd5 := digits_sum_le (6 * n + 9) 3 h_fact3.out
    generalize hS : (Nat.digits 3 (2 * n + 1)).sum = S
    rw [digits6n5_eq] at hd3
    rw [hS] at h_digits2n1_pos hd3
    omega

  omega



theorem oeis_a368692_conjecture_integrality (n : ℕ) :
    108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ∣ (12 * n + 6)! * (6 * n + 9)! := by
  have h1 : 108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ≠ 0 := by positivity
  have h2 : (12 * n + 6)! * (6 * n + 9)! ≠ 0 := by positivity
  rw [← factorization_prime_le_iff_dvd h1 h2]
  intro p hp
  have h108 : (108 : ℕ) ≠ 0 := by decide
  have h_facs : (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2 ≠ 0 := by positivity
  have h_f1 : (4 * n + 2)! * (2 * n + 3)! ≠ 0 := by positivity
  have h_f2 : ((6 * n + 5)!)^2 ≠ 0 := by positivity
  have h_f3 : (4 * n + 2)! ≠ 0 := by positivity
  have h_f4 : (2 * n + 3)! ≠ 0 := by positivity
  have h_lhs : (Nat.factorization (108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2))) p =
      (Nat.factorization 108) p + (Nat.factorization (4 * n + 2)!) p + (Nat.factorization (2 * n + 3)!) p + 2 * (Nat.factorization (6 * n + 5)!) p := by
    rw [Nat.factorization_mul h108 h_facs, Finsupp.add_apply]
    rw [Nat.factorization_mul h_f1 h_f2, Finsupp.add_apply]
    rw [Nat.factorization_mul h_f3 h_f4, Finsupp.add_apply]
    rw [Nat.factorization_pow, Finsupp.smul_apply]
    ring
  have h_num1 : (12 * n + 6)! ≠ 0 := by positivity
  have h_num2 : (6 * n + 9)! ≠ 0 := by positivity
  have h_rhs : (Nat.factorization ((12 * n + 6)! * (6 * n + 9)!)) p =
      (Nat.factorization (12 * n + 6)!) p + (Nat.factorization (6 * n + 9)!) p := by
    rw [Nat.factorization_mul h_num1 h_num2, Finsupp.add_apply]
  rw [h_lhs, h_rhs]
  rw [Nat.factorization_def (4 * n + 2)! hp]
  rw [Nat.factorization_def (2 * n + 3)! hp]
  rw [Nat.factorization_def (6 * n + 5)! hp]
  rw [Nat.factorization_def (12 * n + 6)! hp]
  rw [Nat.factorization_def (6 * n + 9)! hp]
  by_cases hp2 : p = 2
  · subst hp2
    have h_108_2 : (Nat.factorization 108) 2 = 2 := by
      rw [Nat.factorization_def 108 prime_two]
      have h108_eq : 108 = 2^2 * 27 := by decide
      rw [h108_eq]
      rw [padicValNat.mul (by decide) (by decide)]
      have h_27 : ¬ 2 ∣ 27 := by decide
      rw [padicValNat.eq_zero_of_not_dvd h_27, add_zero]
      exact padicValNat.prime_pow 2
    rw [h_108_2]
    have hb : 12 * n + 10 ≥ 5 := by omega
    have h_fact2 : Fact (Nat.Prime 2) := ⟨prime_two⟩
    rw [padicValNat_factorial (show log 2 (4*n+2) < 12*n+10 by
      have : log 2 (4*n+2) < 4*n+2 := Nat.log_lt_self 2 (by omega)
      omega)]
    rw [padicValNat_factorial (show log 2 (2*n+3) < 12*n+10 by
      have : log 2 (2*n+3) < 2*n+3 := Nat.log_lt_self 2 (by omega)
      omega)]
    rw [padicValNat_factorial (show log 2 (6*n+5) < 12*n+10 by
      have : log 2 (6*n+5) < 6*n+5 := Nat.log_lt_self 2 (by omega)
      omega)]
    rw [padicValNat_factorial (show log 2 (12*n+6) < 12*n+10 by
      have : log 2 (12*n+6) < 12*n+6 := Nat.log_lt_self 2 (by omega)
      omega)]
    rw [padicValNat_factorial (show log 2 (6*n+9) < 12*n+10 by
      have : log 2 (6*n+9) < 6*n+9 := Nat.log_lt_self 2 (by omega)
      omega)]
    rw [Finset.mul_sum]
    simp only [add_assoc, ← Finset.sum_add_distrib]
    exact oeis_a368692_conjecture_p2 n hb
  · by_cases hp3 : p = 3
    · subst hp3
      have h_108_3 : (Nat.factorization 108) 3 = 3 := by
        rw [Nat.factorization_def 108 prime_three]
        have h108_eq : 108 = 3^3 * 4 := by decide
        rw [h108_eq]
        rw [padicValNat.mul (by decide) (by decide)]
        have h_4 : ¬ 3 ∣ 4 := by decide
        rw [padicValNat.eq_zero_of_not_dvd h_4, add_zero]
        exact padicValNat.prime_pow 3
      rw [h_108_3]
      have hb : 12 * n + 10 ≥ 5 := by omega
      have h_fact3 : Fact (Nat.Prime 3) := ⟨prime_three⟩
      rw [padicValNat_factorial (show log 3 (4*n+2) < 12*n+10 by
        have : log 3 (4*n+2) < 4*n+2 := Nat.log_lt_self 3 (by omega)
        omega)]
      rw [padicValNat_factorial (show log 3 (2*n+3) < 12*n+10 by
        have : log 3 (2*n+3) < 2*n+3 := Nat.log_lt_self 3 (by omega)
        omega)]
      rw [padicValNat_factorial (show log 3 (6*n+5) < 12*n+10 by
        have : log 3 (6*n+5) < 6*n+5 := Nat.log_lt_self 3 (by omega)
        omega)]
      rw [padicValNat_factorial (show log 3 (12*n+6) < 12*n+10 by
        have : log 3 (12*n+6) < 12*n+6 := Nat.log_lt_self 3 (by omega)
        omega)]
      rw [padicValNat_factorial (show log 3 (6*n+9) < 12*n+10 by
        have : log 3 (6*n+9) < 6*n+9 := Nat.log_lt_self 3 (by omega)
        omega)]
      rw [Finset.mul_sum]
      simp only [add_assoc, ← Finset.sum_add_distrib]
      exact oeis_a368692_conjecture_p3 n hb
    · have h_108_p : (Nat.factorization 108) p = 0 := by
        rw [Nat.factorization_def 108 hp]
        have h_not : ¬ p ∣ 108 := by
          intro hdvd
          have h108_eq : 108 = 2^2 * 3^3 := by decide
          rw [h108_eq] at hdvd
          rcases hp.dvd_mul.mp hdvd with hd1 | hd2
          · have h_dvd : p ∣ 2 := hp.dvd_of_dvd_pow hd1
            have h_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp prime_two).mp h_dvd
            exact hp2 h_eq
          · have h_dvd : p ∣ 3 := hp.dvd_of_dvd_pow hd2
            have h_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp prime_three).mp h_dvd
            exact hp3 h_eq
        exact padicValNat.eq_zero_of_not_dvd h_not
      rw [h_108_p, zero_add]
      have h_factp : Fact (Nat.Prime p) := ⟨hp⟩
      rw [padicValNat_factorial (show log p (4*n+2) < 12*n+10 by
        have : log p (4*n+2) < 4*n+2 := Nat.log_lt_self p (by omega)
        omega)]
      rw [padicValNat_factorial (show log p (2*n+3) < 12*n+10 by
        have : log p (2*n+3) < 2*n+3 := Nat.log_lt_self p (by omega)
        omega)]
      rw [padicValNat_factorial (show log p (6*n+5) < 12*n+10 by
        have : log p (6*n+5) < 6*n+5 := Nat.log_lt_self p (by omega)
        omega)]
      rw [padicValNat_factorial (show log p (12*n+6) < 12*n+10 by
        have : log p (12*n+6) < 12*n+6 := Nat.log_lt_self p (by omega)
        omega)]
      rw [padicValNat_factorial (show log p (6*n+9) < 12*n+10 by
        have : log p (6*n+9) < 6*n+9 := Nat.log_lt_self p (by omega)
        omega)]
      rw [Finset.mul_sum]
      simp only [add_assoc, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hp_pos : 0 < p := hp.pos
      have h_pi_pos : 0 < p^i := by positivity
      have h_floor := floor_ineq (4 * n + 2) (2 * n + 3) (p^i) h_pi_pos
      have h_eq1 : 3 * (4 * n + 2) = 12 * n + 6 := by ring
      have h_eq2 : 3 * (2 * n + 3) = 6 * n + 9 := by ring
      have h_eq3 : (4 * n + 2) + (2 * n + 3) = 6 * n + 5 := by ring
      rw [h_eq1, h_eq2, h_eq3] at h_floor
      omega
