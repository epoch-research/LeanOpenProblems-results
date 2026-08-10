import FormalConjectures.Util.ProblemImports

/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

-- Helper definition for the set of indices coprime to 30.
def coprime_indices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisor_product (n r : ℕ) : ℤ :=
  (coprime_indices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))

private lemma div_mul_mod_decomp (n q c : ℕ) (hq : 0 < q) :
    c * n / q = c * (n / q) + c * (n % q) / q := by
  nth_rewrite 1 [← Nat.div_add_mod n q]
  rw [mul_add]
  have h : c * (q * (n / q)) = q * (c * (n / q)) := by ring
  rw [h]
  rw [add_comm (q * (c * (n / q))) (c * (n % q))]
  rw [Nat.add_mul_div_left _ _ hq]
  ring

private lemma div15_eq (r q : ℕ) : 15 * r / q = (30 * r / q) / 2 := by
  rw [Nat.div_div_eq_div_mul]
  have : q * 2 = 2 * q := by omega
  rw [this]
  rw [← Nat.mul_div_mul_left (15 * r) q (by norm_num : 0 < 2)]
  ring_nf

private lemma div10_eq (r q : ℕ) : 10 * r / q = (30 * r / q) / 3 := by
  rw [Nat.div_div_eq_div_mul]
  have : q * 3 = 3 * q := by omega
  rw [this]
  rw [← Nat.mul_div_mul_left (10 * r) q (by norm_num : 0 < 3)]
  ring_nf

private lemma div6_eq (r q : ℕ) : 6 * r / q = (30 * r / q) / 5 := by
  rw [Nat.div_div_eq_div_mul]
  have : q * 5 = 5 * q := by omega
  rw [this]
  rw [← Nat.mul_div_mul_left (6 * r) q (by norm_num : 0 < 5)]
  ring_nf

private lemma small_floor (t : ℕ) (ht : t < 30) : t / 2 + t / 3 + t / 5 ≤ t := by
  omega

private lemma small_floor_extra (t : ℕ) (ht : t < 30) (hcop : Nat.Coprime t 30) :
    t / 2 + t / 3 + t / 5 + 1 ≤ t := by
  interval_cases t <;> simp_all [Nat.Coprime]

private lemma coprime_t_of_rem (r q : ℕ) (hrem : (30 * r) % q = 1) :
    Nat.Coprime (30 * r / q) 30 := by
  have hEq : 30 * r = q * (30 * r / q) + 1 := by
    have h := Nat.div_add_mod (30 * r) q
    rw [hrem] at h
    omega
  apply Nat.coprime_of_dvd'
  intro k hk hkt hk30
  have h1 : k ∣ 30 * r := dvd_mul_of_dvd_left hk30 r
  have h2 : k ∣ q * (30 * r / q) := dvd_mul_of_dvd_right hkt q
  rw [hEq] at h1
  exact (Nat.dvd_add_iff_right h2).mpr h1

private lemma rem_of_dvd (n q : ℕ) (hn : 0 < n) (hq : 2 ≤ q)
    (hdiv : q ∣ 30 * n - 1) :
    (30 * (n % q)) % q = 1 := by
  rcases hdiv with ⟨k, hk⟩
  have hEq : 30 * n = q * k + 1 := by omega
  have hmod30n : (30 * n) % q = 1 := by
    rw [hEq]
    rw [Nat.add_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hq
  calc
    (30 * (n % q)) % q = (30 * n) % q := by
      rw [Nat.mul_mod, Nat.mul_mod]
      simp
    _ = 1 := hmod30n

private lemma floor_term (n q : ℕ) (hn : 0 < n) (hq2 : 2 ≤ q) :
    15 * n / q + 10 * n / q + 6 * n / q + (if q ∣ 30 * n - 1 then 1 else 0)
      ≤ 30 * n / q + n / q := by
  have hq : 0 < q := by omega
  let r := n % q
  let s := n / q
  let t := 30 * r / q
  have hr : r < q := Nat.mod_lt n hq
  have ht : t < 30 := by
    dsimp [t]
    have hlt : 30 * r < q * 30 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((Nat.mul_lt_mul_left (by norm_num : 0 < 30)).2 hr)
    exact Nat.div_lt_of_lt_mul hlt
  have h15 : 15 * n / q = 15 * s + t / 2 := by
    dsimp [s, t, r]
    rw [div_mul_mod_decomp n q 15 hq, div15_eq]
  have h10 : 10 * n / q = 10 * s + t / 3 := by
    dsimp [s, t, r]
    rw [div_mul_mod_decomp n q 10 hq, div10_eq]
  have h6 : 6 * n / q = 6 * s + t / 5 := by
    dsimp [s, t, r]
    rw [div_mul_mod_decomp n q 6 hq, div6_eq]
  have h30 : 30 * n / q = 30 * s + t := by
    dsimp [s, t, r]
    rw [div_mul_mod_decomp n q 30 hq]
  by_cases hdiv : q ∣ 30 * n - 1
  · have hrem := rem_of_dvd n q hn hq2 hdiv
    have hcop : Nat.Coprime t 30 := by
      dsimp [t, r]
      exact coprime_t_of_rem (n % q) q hrem
    have hsmall := small_floor_extra t ht hcop
    rw [if_pos hdiv]
    rw [h15, h10, h6, h30]
    omega
  · have hsmall := small_floor t ht
    rw [if_neg hdiv]
    rw [h15, h10, h6, h30]
    omega

private lemma factorial_ratio_mul_dvd (n : ℕ) (hn : 0 < n) :
    (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) *
        (30 * n - 1) ∣ Nat.factorial (30 * n) * Nat.factorial n := by
  let D := Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)
  let M := 30 * n - 1
  let N := Nat.factorial (30 * n) * Nat.factorial n
  have hMpos : 0 < M := by dsimp [M]; omega
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDMpos : D * M ≠ 0 := by positivity
  have hNne : N ≠ 0 := by dsimp [N]; positivity
  apply (Nat.factorization_le_iff_dvd hDMpos hNne).mp
  intro p
  by_cases hp : Nat.Prime p
  · let b := Nat.log p (30 * n) + 1
    have hlog30 : Nat.log p (30 * n) < b := by dsimp [b]; omega
    have hlog15 : Nat.log p (15 * n) < b :=
      (Nat.log_mono_right (by nlinarith : 15 * n ≤ 30 * n)).trans_lt hlog30
    have hlog10 : Nat.log p (10 * n) < b :=
      (Nat.log_mono_right (by nlinarith : 10 * n ≤ 30 * n)).trans_lt hlog30
    have hlog6 : Nat.log p (6 * n) < b :=
      (Nat.log_mono_right (by nlinarith : 6 * n ≤ 30 * n)).trans_lt hlog30
    have hlogn : Nat.log p n < b :=
      (Nat.log_mono_right (by nlinarith : n ≤ 30 * n)).trans_lt hlog30
    have hMlt30 : M ≤ 30 * n := by dsimp [M]; omega
    have hMltpow : M < p ^ b :=
      Nat.lt_pow_of_log_lt hp.one_lt ((Nat.log_mono_right hMlt30).trans_lt hlog30)
    have hfacM : M.factorization p = {i ∈ Finset.Ico 1 b | p ^ i ∣ M}.card :=
      Nat.factorization_eq_card_pow_dvd_of_lt hp hMpos hMltpow
    have hfacD : D.factorization p =
        (Nat.factorial (15 * n)).factorization p +
          (Nat.factorial (10 * n)).factorization p +
          (Nat.factorial (6 * n)).factorization p := by
      dsimp [D]
      rw [Nat.factorization_mul
        (mul_ne_zero (Nat.factorial_ne_zero (15 * n)) (Nat.factorial_ne_zero (10 * n)))
        (Nat.factorial_ne_zero (6 * n))]
      rw [Nat.factorization_mul (Nat.factorial_ne_zero (15 * n))
        (Nat.factorial_ne_zero (10 * n))]
      simp [add_assoc]
    have hfacN : N.factorization p =
        (Nat.factorial (30 * n)).factorization p + (Nat.factorial n).factorization p := by
      dsimp [N]
      rw [Nat.factorization_mul (Nat.factorial_ne_zero (30 * n)) (Nat.factorial_ne_zero n)]
      rfl
    have hfacDM : (D * M).factorization p = D.factorization p + M.factorization p := by
      rw [Nat.factorization_mul (Nat.ne_of_gt hDpos) (Nat.ne_of_gt hMpos)]
      rfl
    rw [hfacDM, hfacD, hfacN]
    rw [Nat.factorization_factorial hp hlog15]
    rw [Nat.factorization_factorial hp hlog10]
    rw [Nat.factorization_factorial hp hlog6]
    rw [Nat.factorization_factorial hp hlog30]
    rw [Nat.factorization_factorial hp hlogn]
    rw [hfacM, Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hq2 : 2 ≤ p ^ i := by
      calc
        2 ≤ p := hp.two_le
        _ ≤ p ^ i := by
          simpa using Nat.le_self_pow (n := i) (a := p) (by omega)
    simpa [D, M, N, add_assoc, add_comm, add_left_comm] using floor_term n (p ^ i) hn hq2
  · rw [Nat.factorization_eq_zero_of_not_prime (D * M) hp]
    exact Nat.zero_le _

private lemma ratio_divisible_nat (n : ℕ) (hn : 0 < n) :
    (30 * n - 1) ∣ a n := by
  let D := Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)
  let N := Nat.factorial (30 * n) * Nat.factorial n
  have hmul : D * (30 * n - 1) ∣ N := by
    simpa [D, N, mul_assoc] using factorial_ratio_mul_dvd n hn
  have hDdvd : D ∣ N := by
    rcases hmul with ⟨k, hk⟩
    refine ⟨(30 * n - 1) * k, ?_⟩
    rw [hk]
    ring
  have h : (30 * n - 1) ∣ N / D :=
    (Nat.dvd_div_iff_mul_dvd (a := 30 * n - 1) (b := N) (c := D) hDdvd).mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  simpa [a, D, N, mul_comm, mul_left_comm, mul_assoc] using h

/--
It appears that a(n)/(30*n - 1) is integral for all n (checked up to n = 1000).
This is the specific case of the general conjecture for r=1 with D(1)=1.
-/
theorem oeis_a211417_conjecture_specific (n : ℕ) :
  (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
  by_cases hn : n = 0
  · subst n
    norm_num [a]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnat : (30 * n - 1) ∣ a n := ratio_divisible_nat n hnpos
    have hint : ((30 * n - 1 : ℕ) : ℤ) ∣ (a n : ℤ) := Int.natCast_dvd_natCast.mpr hnat
    have hcast : ((30 * n - 1 : ℕ) : ℤ) = 30 * (n : ℤ) - 1 := by
      have h30 : 1 ≤ 30 * n := by nlinarith [hnpos]
      norm_num [Nat.cast_sub h30]
    rwa [← hcast]
