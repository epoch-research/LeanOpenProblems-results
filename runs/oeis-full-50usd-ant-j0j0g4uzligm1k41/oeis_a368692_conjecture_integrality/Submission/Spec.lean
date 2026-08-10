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

private theorem subadd (u v m : ℕ) (hm : 0 < m) : (u + v) / m ≤ u / m + v / m + 1 := by
  have hsum : u + v = m * (u / m + v / m) + (u % m + v % m) := by
    have := Nat.div_add_mod u m
    have := Nat.div_add_mod v m
    ring_nf
    omega
  rw [hsum, Nat.mul_add_div hm]
  have : (u % m + v % m) / m ≤ 1 := by
    apply Nat.lt_succ_iff.mp
    apply Nat.div_lt_of_lt_mul
    have := Nat.mod_lt u hm
    have := Nat.mod_lt v hm
    omega
  omega

private theorem core (ra rb m : ℕ) (hm : 0 < m) (hra : ra < m) (hrb : rb < m) :
    2 * ((ra + rb) / m) ≤ (3 * ra) / m + (3 * rb) / m := by
  rcases Nat.lt_or_ge (ra + rb) m with h | h
  · rw [Nat.div_eq_of_lt h]; simp
  · have h1 : (ra + rb) / m ≤ 1 := by
      apply Nat.lt_succ_iff.mp
      apply Nat.div_lt_of_lt_mul; omega
    have h2 : 3 ≤ (3 * ra + 3 * rb) / m := by
      rw [Nat.le_div_iff_mul_le hm]; omega
    have h3 : (3 * ra + 3 * rb) / m ≤ (3 * ra) / m + (3 * rb) / m + 1 := subadd _ _ _ hm
    omega

private theorem decomp (a m : ℕ) (hm : 0 < m) : (3 * a) / m = 3 * (a / m) + (3 * (a % m)) / m := by
  have h : 3 * a = m * (3 * (a / m)) + 3 * (a % m) := by
    conv_lhs => rw [← Nat.div_add_mod a m]
    ring
  rw [h, Nat.mul_add_div hm]

private theorem decomp2 (a b m : ℕ) (hm : 0 < m) :
    (a + b) / m = a / m + b / m + (a % m + b % m) / m := by
  have hsum : a + b = m * (a / m + b / m) + (a % m + b % m) := by
    have := Nat.div_add_mod a m
    have := Nat.div_add_mod b m
    ring_nf; omega
  rw [hsum, Nat.mul_add_div hm]

private theorem lemmaL (a b m : ℕ) :
    a / m + b / m + 2 * ((a + b) / m) ≤ (3 * a) / m + (3 * b) / m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  rw [decomp a m hm, decomp b m hm, decomp2 a b m hm]
  have hc := core (a % m) (b % m) m hm (Nat.mod_lt a hm) (Nat.mod_lt b hm)
  omega

private theorem legendre_ineq (p n : ℕ) [Fact p.Prime] :
    padicValNat p ((4*n+2)!) + padicValNat p ((2*n+3)!) + 2 * padicValNat p ((6*n+5)!)
      ≤ padicValNat p ((12*n+6)!) + padicValNat p ((6*n+9)!) := by
  set b := log p (12*n+9) + 1 with hb
  have hbound : ∀ m : ℕ, m ≤ 12*n+9 → log p m < b := by
    intro m hm
    exact Nat.lt_succ_of_le (Nat.log_mono_right hm)
  rw [padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := lemmaL (4*n+2) (2*n+3) (p^i)
  have e1 : 4*n+2+(2*n+3) = 6*n+5 := by ring
  have e2 : 3*(4*n+2) = 12*n+6 := by ring
  have e3 : 3*(2*n+3) = 6*n+9 := by ring
  rw [e1, e2, e3] at h
  omega

private theorem digitsum3 (n : ℕ) : 3 ≤ (Nat.digits 3 (6*n+5)).sum := by
  have h1 : Nat.digits 3 (6*n+5) = (6*n+5) % 3 :: Nat.digits 3 ((6*n+5)/3) := by
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 3) (by omega)]
  have hmod : (6*n+5) % 3 = 2 := by omega
  have hdiv : (6*n+5) / 3 = 2*n+1 := by omega
  rw [h1, hmod, hdiv, List.sum_cons]
  have hpos : 1 ≤ (Nat.digits 3 (2*n+1)).sum := by
    have hnil : Nat.digits 3 (2*n+1) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlast := Nat.getLast_digit_ne_zero 3 (m := 2*n+1) (by omega)
    have := List.getLast_mem hnil
    refine Nat.one_le_iff_ne_zero.mpr ?_
    intro hz
    rw [List.sum_eq_zero_iff] at hz
    exact hlast (hz _ this)
  omega

private theorem ineq3 (n : ℕ) :
    3 + (padicValNat 3 ((4*n+2)!) + padicValNat 3 ((2*n+3)!) + 2 * padicValNat 3 ((6*n+5)!))
      ≤ padicValNat 3 ((12*n+6)!) + padicValNat 3 ((6*n+9)!) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have k1 : (12*n+6)! = (3*(4*n+2))! := by ring_nf
  have k2 : (6*n+9)! = (3*(2*n+3))! := by ring_nf
  rw [k1, k2, padicValNat_factorial_mul, padicValNat_factorial_mul]
  -- now: 3 + (vK + vL + 2 vM) ≤ (vK + (4n+2)) + (vL + (2n+3))
  have hM : (3 - 1) * padicValNat 3 ((6*n+5)!) = (6*n+5) - (Nat.digits 3 (6*n+5)).sum :=
    sub_one_mul_padicValNat_factorial (6*n+5)
  have hds := digitsum3 n
  have hle : (Nat.digits 3 (6*n+5)).sum ≤ 6*n+5 := Nat.digit_sum_le 3 (6*n+5)
  simp only [show (3:ℕ)-1 = 2 from rfl] at hM
  omega

private theorem ineq2 (n : ℕ) :
    2 + (padicValNat 2 ((4*n+2)!) + padicValNat 2 ((2*n+3)!) + 2 * padicValNat 2 ((6*n+5)!))
      ≤ padicValNat 2 ((12*n+6)!) + padicValNat 2 ((6*n+9)!) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set b := log 2 (12*n+9) + 1 with hb
  have hb3 : 3 ≤ b := by
    have : (3:ℕ) ≤ log 2 (12*n+9) := by
      have : log 2 9 ≤ log 2 (12*n+9) := Nat.log_mono_right (by omega)
      have h9 : log 2 9 = 3 := by norm_num [Nat.log]
      omega
    omega
  have hbound : ∀ m : ℕ, m ≤ 12*n+9 → log 2 m < b := by
    intro m hm
    exact Nat.lt_succ_of_le (Nat.log_mono_right hm)
  rw [padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega)),
      padicValNat_factorial (hbound _ (by omega))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- goal: 2 + ∑ g ≤ ∑ h
  set g : ℕ → ℕ := fun i => (4*n+2)/2^i + (2*n+3)/2^i + 2*((6*n+5)/2^i) with hg
  set h : ℕ → ℕ := fun i => (12*n+6)/2^i + (6*n+9)/2^i with hh
  set phi : ℕ → ℕ := fun i => (if i = 1 then 1 else 0) + (if i = 2 then 1 else 0) with hphi
  have hsumphi : ∑ i ∈ Finset.Ico 1 b, phi i = 2 := by
    rw [hphi]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.Ico 1 b) 1 (fun _ => 1),
        Finset.sum_ite_eq' (Finset.Ico 1 b) 2 (fun _ => 1)]
    rw [if_pos (by simp [Finset.mem_Ico]; omega), if_pos (by simp [Finset.mem_Ico]; omega)]
  have hterm : ∀ i ∈ Finset.Ico 1 b, g i + phi i ≤ h i := by
    intro i hi
    simp only [hg, hh, hphi]
    by_cases hi1 : i = 1
    · subst hi1
      norm_num
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4*q + r :=
        ⟨n/4, n%4, Nat.mod_lt n (by norm_num), (Nat.div_add_mod n 4).symm⟩
      interval_cases r <;> omega
    by_cases hi2 : i = 2
    · subst hi2
      norm_num
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4*q + r :=
        ⟨n/4, n%4, Nat.mod_lt n (by norm_num), (Nat.div_add_mod n 4).symm⟩
      interval_cases r <;> omega
    · rw [if_neg hi1, if_neg hi2]
      have hL := lemmaL (4*n+2) (2*n+3) (2^i)
      have e1 : 4*n+2+(2*n+3) = 6*n+5 := by ring
      have e2 : 3*(4*n+2) = 12*n+6 := by ring
      have e3 : 3*(2*n+3) = 6*n+9 := by ring
      rw [e1, e2, e3] at hL
      omega
  have hfin := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, hsumphi] at hfin
  rw [Nat.add_comm 2]
  exact hfin

private theorem pv2_108 : padicValNat 2 108 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h : (108:ℕ) = 2^2 * 27 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]

private theorem pv3_108 : padicValNat 3 108 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h : (108:ℕ) = 3^3 * 4 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]

private theorem pv_108_zero {p : ℕ} (hpp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    padicValNat p 108 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have h : (108:ℕ) = 2^2 * 3^3 := by norm_num
  rw [h] at hdvd
  rcases (Nat.Prime.dvd_mul hpp).mp hdvd with hh | hh
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hh))
  · exact h3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow hh))

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
  have hd : 108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ≠ 0 := by positivity
  have hn : (12 * n + 6)! * (6 * n + 9)! ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hd hn, Finsupp.le_iff]
  intro p hp
  have hpp : p.Prime :=
    Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
  haveI : Fact p.Prime := ⟨hpp⟩
  rw [Nat.factorization_def _ hpp, Nat.factorization_def _ hpp]
  have hexp : padicValNat p (108 * ((4*n+2)! * (2*n+3)! * ((6*n+5)!)^2))
      = padicValNat p 108 + (padicValNat p ((4*n+2)!) + padicValNat p ((2*n+3)!)
        + 2 * padicValNat p ((6*n+5)!)) := by
    rw [pow_two,
        padicValNat.mul (by norm_num) (by positivity),
        padicValNat.mul (by positivity) (by positivity),
        padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    ring
  have hexp2 : padicValNat p ((12*n+6)! * (6*n+9)!)
      = padicValNat p ((12*n+6)!) + padicValNat p ((6*n+9)!) :=
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  rw [hexp, hexp2]
  by_cases hp2 : p = 2
  · subst hp2; rw [pv2_108]; have := ineq2 n; omega
  by_cases hp3 : p = 3
  · subst hp3; rw [pv3_108]; have := ineq3 n; omega
  · rw [pv_108_zero hpp hp2 hp3]; have := legendre_ineq p n; omega
