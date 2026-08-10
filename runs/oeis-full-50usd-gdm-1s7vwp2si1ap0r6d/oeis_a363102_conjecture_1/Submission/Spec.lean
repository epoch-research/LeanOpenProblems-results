import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

open Nat Finset

/--
Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$
-/
def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

/--
A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  -- The subtraction n^2 - 2 is safe for n >= 3.
  num / Nat.gcd num denom_arg

-- Let's define the sum of factorials
def S (n : ℕ) : ℕ := Finset.sum (range (n + 1)) (fun k => k.factorial)

-- Basic relation for S
theorem S_succ (n : ℕ) : S (n + 1) = S n + (n + 1).factorial := by
  dsimp [S]
  rw [sum_range_succ]

-- We prove S(n+1) is always even
theorem S_succ_even (n : ℕ) : 2 ∣ S (n + 1) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [S_succ]
    apply dvd_add ih
    exact dvd_factorial (by decide) (by omega)

-- We prove (n + 2) * S n is always even
theorem prod_even (n : ℕ) : 2 ∣ (n + 2) * S n := by
  cases n with
  | zero =>
    use S 0
  | succ n =>
    have h : 2 ∣ S (n + 1) := S_succ_even n
    exact dvd_mul_of_dvd_right h (n + 3)

-- 2 * a051403 n = (n + 2) * S n
theorem a051403_cancel (n : ℕ) : 2 * a051403 n = (n + 2) * S n := by
  dsimp [a051403]
  exact Nat.mul_div_cancel' (prod_even n)

-- Coefficient identity
theorem coeff_identity (m : ℕ) : 2 * (m + 3) + (m + 4) * (m + 2) + 2 = (m + 4) ^ 2 := by
  ring

theorem denom_arg_identity_m (m : ℕ) :
  2 * (2 * a051403 (m + 1) + (m + 4) * a051403 m) = ((m + 4) ^ 2 - 2) * S m + 2 * (m + 3) * (m + 1).factorial := by
  have h1 : 2 * (2 * a051403 (m + 1) + (m + 4) * a051403 m) = 2 * (2 * a051403 (m + 1)) + (m + 4) * (2 * a051403 m) := by
    ring
  rw [h1]
  rw [a051403_cancel (m + 1), a051403_cancel m]
  rw [S_succ m]
  have h2 : 2 * ((m + 3) * (S m + (m + 1).factorial)) + (m + 4) * ((m + 2) * S m) =
    (2 * (m + 3) + (m + 4) * (m + 2)) * S m + 2 * (m + 3) * (m + 1).factorial := by
    ring
  rw [h2]
  have h3 : 2 * (m + 3) + (m + 4) * (m + 2) = (m + 4) ^ 2 - 2 := by
    have hcoeff := coeff_identity m
    omega
  rw [h3]

theorem gcd_denom_arg_identity_m (m : ℕ) :
  Nat.gcd ((m + 4)^2 - 2) (2 * (2 * a051403 (m + 1) + (m + 4) * a051403 m)) =
  Nat.gcd ((m + 4)^2 - 2) (2 * (m + 3) * (m + 1).factorial) := by
  have h := denom_arg_identity_m m
  rw [h]
  rw [add_comm (((m + 4)^2 - 2) * S m)]
  rw [Nat.gcd_add_mul_left_right]

theorem coprime_two_of_odd (y : ℕ) (hy : y % 2 = 1) : Nat.Coprime 2 y := by
  rw [Nat.Coprime]
  have h1 : Nat.gcd 2 y ∣ 2 := Nat.gcd_dvd_left 2 y
  have h2 : Nat.gcd 2 y ∣ y := Nat.gcd_dvd_right 2 y
  have h3 : Nat.gcd 2 y = 1 ∨ Nat.gcd 2 y = 2 := by
    have h_le : Nat.gcd 2 y ≤ 2 := Nat.le_of_dvd (by decide) h1
    have h_pos : 0 < Nat.gcd 2 y := Nat.gcd_pos_of_pos_left y (by decide)
    omega
  rcases h3 with h3 | h3
  · exact h3
  · have h4 : 2 ∣ y := h3 ▸ h2
    rcases h4 with ⟨k, hk⟩
    omega

theorem gcd_even_cancel (y z : ℕ) (hy : y % 2 = 1) :
  Nat.gcd (2 * y) (2 * z) = Nat.gcd (2 * y) (4 * z) := by
  have h1 : Nat.gcd (2 * y) (2 * z) = 2 * Nat.gcd y z := by
    exact Nat.gcd_mul_left 2 y z
  have h2 : Nat.gcd (2 * y) (4 * z) = 2 * Nat.gcd y (2 * z) := by
    have h2_1 : 4 * z = 2 * (2 * z) := by ring
    rw [h2_1]
    exact Nat.gcd_mul_left 2 y (2 * z)
  rw [h1, h2]
  have h_cop : Nat.Coprime 2 y := coprime_two_of_odd y hy
  have h3 : Nat.gcd y (2 * z) = Nat.gcd y z := by
    exact Nat.Coprime.gcd_mul_left_cancel_right z h_cop
  rw [h3]

theorem gcd_odd_cancel (x d : ℕ) (hx : x % 2 = 1) :
  Nat.gcd x (2 * d) = Nat.gcd x d := by
  have h_cop : Nat.Coprime 2 x := coprime_two_of_odd x hx
  exact Nat.Coprime.gcd_mul_left_cancel_right d h_cop

theorem gcd_cancel_two (m : ℕ) :
  Nat.gcd ((m + 4)^2 - 2) (2 * (2 * a051403 (m + 1) + (m + 4) * a051403 m)) =
  Nat.gcd ((m + 4)^2 - 2) (2 * a051403 (m + 1) + (m + 4) * a051403 m) := by
  have h_mod : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h_mod with h_even | h_odd
  · -- m is even
    rcases (Nat.dvd_of_mod_eq_zero h_even) with ⟨k, hk⟩
    -- So m = 2 * k.
    have hX : (m + 4)^2 - 2 = 2 * (2 * (k + 2)^2 - 1) := by
      rw [hk]
      have h_sq : (2 * k + 4)^2 = 4 * k^2 + 16 * k + 16 := by ring
      have h_sq2 : 2 * (k + 2)^2 = 2 * k^2 + 8 * k + 8 := by ring
      rw [h_sq, h_sq2]
      omega
    have hy_odd : (2 * (k + 2)^2 - 1) % 2 = 1 := by
      have h_pos : 0 < 2 * (k + 2)^2 := by positivity
      omega
    have hD_even : 2 ∣ 2 * a051403 (m + 1) + (m + 4) * a051403 m := by
      rw [hk]
      have hD_eq : 2 * a051403 (2 * k + 1) + (2 * k + 4) * a051403 (2 * k) =
        2 * (a051403 (2 * k + 1) + (k + 2) * a051403 (2 * k)) := by ring
      rw [hD_eq]
      exact dvd_mul_right 2 _
    rcases hD_even with ⟨d', hd'⟩
    rw [hX, hd']
    have hd_eq : 2 * (2 * d') = 4 * d' := by ring
    rw [hd_eq]
    exact (gcd_even_cancel (2 * (k + 2)^2 - 1) d' hy_odd).symm
  · -- m is odd
    have hm : m = 2 * (m / 2) + 1 := by omega
    have hX_odd : ((m + 4)^2 - 2) % 2 = 1 := by
      rw [hm]
      have h_sq : (2 * (m / 2) + 1 + 4)^2 = 4 * (m / 2)^2 + 20 * (m / 2) + 25 := by ring
      rw [h_sq]
      omega
    exact gcd_odd_cancel ((m + 4)^2 - 2) (2 * a051403 (m + 1) + (m + 4) * a051403 m) hX_odd

theorem gcd_denom_arg_only (m : ℕ) :
  Nat.gcd ((m + 4)^2 - 2) (2 * a051403 (m + 1) + (m + 4) * a051403 m) =
  Nat.gcd ((m + 4)^2 - 2) (2 * (m + 3) * (m + 1).factorial) := by
  rw [← gcd_cancel_two]
  exact gcd_denom_arg_identity_m m

def a_simp (m : ℕ) : ℕ :=
  ((m + 7)^2 - 2) / Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial)

theorem a_eq_a_simp (m : ℕ) : a (m + 7) = a_simp m := by
  dsimp [a, a_simp]
  have h_sub1 : m + 7 - 3 = m + 4 := by omega
  have h_sub2 : m + 7 - 4 = m + 3 := by omega
  rw [h_sub1, h_sub2]
  have h := gcd_denom_arg_only (m + 3)
  have h_eq1 : (m + 3) + 4 = m + 7 := by omega
  have h_eq2 : (m + 3) + 3 = m + 6 := by omega
  have h_eq3 : (m + 3) + 1 = m + 4 := by omega
  rw [h_eq1, h_eq2, h_eq3] at h
  rw [h]

theorem a_simp_pos (m : ℕ) : 0 < a_simp m := by
  dsimp [a_simp]
  apply Nat.div_pos
  · have h : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
    have h1 : 0 < (m + 7)^2 - 2 := by rw [h]; omega
    exact Nat.gcd_le_left _ h1
  · have h : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
    have h1 : 0 < (m + 7)^2 - 2 := by rw [h]; omega
    exact Nat.gcd_pos_of_pos_left _ h1


theorem gcd_dvd_mul_gcd (N D p : ℕ) : Nat.gcd N (p * D) ∣ p * Nat.gcd N D := by
  have h1 : Nat.gcd N (p * D) ∣ p * N := dvd_mul_of_dvd_right (Nat.gcd_dvd_left N (p * D)) p
  have h2 : Nat.gcd N (p * D) ∣ p * D := Nat.gcd_dvd_right N (p * D)
  have h3 : Nat.gcd N (p * D) ∣ Nat.gcd (p * N) (p * D) := Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left] at h3
  exact h3

theorem a_simp_dvd_N (m : ℕ) : a_simp m ∣ (m + 7)^2 - 2 :=
  ⟨Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial), by
    dsimp [a_simp]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩

theorem prime_not_m_plus_5 (m p : ℕ) (hp : Nat.Prime p) (hp5 : p = m + 5) : ¬ (p ∣ a_simp m) := by
  intro hdvd
  have h_dvd_N : p ∣ (m + 7)^2 - 2 := dvd_trans hdvd (a_simp_dvd_N m)
  have h_eq : m + 7 = p + 2 := by omega
  rw [h_eq] at h_dvd_N
  have h_alg : (p + 2)^2 - 2 = p * (p + 4) + 2 := by
    have h_sq : (p + 2)^2 = p^2 + 4 * p + 4 := by ring
    have h_ring : p * (p + 4) + 2 = p^2 + 4 * p + 2 := by ring
    rw [h_sq, h_ring]
    omega
  rw [h_alg] at h_dvd_N
  have h_dvd2 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_right p (p + 4))).mp h_dvd_N
  have hp2 : p = 2 := by
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd2
    have h_ge : p ≥ 2 := hp.two_le
    omega
  omega

theorem p_dvd_D (m p : ℕ) (hp : Nat.Prime p) (h_le : p ≤ m + 6) (hne5 : p ≠ m + 5) :
  p ∣ 2 * (m + 6) * (m + 4).factorial := by
  have h_cases : p ≤ m + 4 ∨ p = m + 6 := by omega
  rcases h_cases with h_le4 | h_eq6
  · have h_fact : p ∣ (m + 4).factorial := Nat.dvd_factorial hp.pos h_le4
    exact dvd_mul_of_dvd_right h_fact _
  · rw [h_eq6]
    use 2 * (m + 4).factorial
    ring

theorem odd_of_mul_odd {A B : ℕ} (h : A * B % 2 = 1) : A % 2 = 1 := by
  have h_cases : A % 2 = 0 ∨ A % 2 = 1 := by omega
  rcases h_cases with h0 | h1
  · rcases (Nat.dvd_of_mod_eq_zero h0) with ⟨k, hk⟩
    rw [hk] at h
    have : (2 * k) * B % 2 = 0 := by
      rw [mul_assoc]
      exact Nat.mul_mod_right 2 (k * B)
    omega
  · exact h1

theorem p_pow_step (N D p G : ℕ) (hG : G = Nat.gcd N D) (hdvd : p ∣ N / G) (j : ℕ)
  (hD : p^j ∣ D) (hN : p^j ∣ N) : p^(j+1) ∣ N := by
  have h_gcd : p^j ∣ G := hG ▸ Nat.dvd_gcd hN hD
  rcases h_gcd with ⟨g', hg'⟩
  have h_div : p ∣ N / G := hdvd
  rcases h_div with ⟨q', hq'⟩
  have h_eq : N = G * (N / G) := (Nat.mul_div_cancel' (hG ▸ Nat.gcd_dvd_left N D)).symm
  rw [h_eq, hq', hg']
  use g' * q'
  ring


theorem dvd_factorial_prime_sq (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (h : 2 * p ≤ k) : p^2 ∣ k.factorial := by
  induction k, h using Nat.le_induction with
  | base =>
    have hp2 : p ≤ 2 * p - 1 := by
      have : p ≥ 2 := hp.two_le
      omega
    have hp_pos : 0 < p := hp.pos
    have hdvd : p ∣ (2 * p - 1).factorial := Nat.dvd_factorial hp_pos hp2
    rcases hdvd with ⟨Q, hQ⟩
    have h_fac : (2 * p).factorial = (2 * p) * (2 * p - 1).factorial := by
      have h_eq : 2 * p = (2 * p - 1) + 1 := by
        have : p ≥ 2 := hp.two_le
        omega
      nth_rw 1 [h_eq]
      rw [Nat.factorial_succ (2 * p - 1)]
      rw [← h_eq]
    rw [h_fac, hQ]
    use 2 * Q
    ring
  | succ x hx ih =>
    have h_fac : (x + 1).factorial = (x + 1) * x.factorial := Nat.factorial_succ x
    rw [h_fac]
    exact dvd_mul_of_dvd_right ih (x + 1)

theorem prime_not_m_plus_6 (m p : ℕ) (hp : Nat.Prime p) (hp6 : p = m + 6) : ¬ (p ∣ a_simp m) := by
  intro hdvd
  have h_dvd_N : p ∣ (m + 7)^2 - 2 := dvd_trans hdvd (a_simp_dvd_N m)
  have h_eq : m + 7 = p + 1 := by omega
  rw [h_eq] at h_dvd_N
  have h_alg : (p + 1)^2 - 2 + 1 = p * (p + 2) := by
    have h_sq : (p + 1)^2 = p^2 + 2 * p + 1 := by ring
    have h_ring : p * (p + 2) = p^2 + 2 * p := by ring
    rw [h_sq, h_ring]
    omega
  have h_dvd_add : p ∣ (p + 1)^2 - 2 + 1 := by
    rw [h_alg]
    exact dvd_mul_right p (p + 2)
  have h_dvd_one : p ∣ 1 := (Nat.dvd_add_right h_dvd_N).mp h_dvd_add
  have hp1 : p = 1 := Nat.eq_one_of_dvd_one h_dvd_one
  have hp_prime : p ≠ 1 := hp.ne_one
  contradiction

theorem prime_of_two_dvd {p : ℕ} (hp : Nat.Prime p) (h : 2 ∣ p) : p = 2 := by
  rcases hp.eq_one_or_self_of_dvd 2 h with h1 | h2
  · contradiction
  · exact h2.symm

theorem prime_dvd_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p ∣ q) : p = q := by
  have h_or := hq.eq_one_or_self_of_dvd p h
  rcases h_or with h1 | h2
  · exfalso
    have : p ≥ 2 := hp.two_le
    omega
  · exact h2

theorem p_pow_div_induction (m p : ℕ) (_hp : Nat.Prime p) (hdvd : p ∣ a_simp m) (j : ℕ) :
  p^j ∣ 2 * (m + 6) * (m + 4).factorial → p^(j+1) ∣ (m + 7)^2 - 2 := by
  induction j with
  | zero =>
    intro _
    have h_dvdN := a_simp_dvd_N m
    rw [pow_one]
    exact dvd_trans hdvd h_dvdN
  | succ j ih =>
    intro h_D
    have h_D_j : p^j ∣ 2 * (m + 6) * (m + 4).factorial := by
      have h_pow : p^j ∣ p^(j+1) := by
        use p
        ring
      exact dvd_trans h_pow h_D
    have h_N_j1 : p^(j+1) ∣ (m + 7)^2 - 2 := ih h_D_j
    exact p_pow_step ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial) p (Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial)) rfl hdvd (j+1) h_D h_N_j1

theorem a_simp_eq_p_of_N_eq_2p2 (m p : ℕ) (hp : Nat.Prime p) (h_N : (m + 7)^2 - 2 = 2 * p^2) (h_le4 : p ≤ m + 4) (hdvd : p ∣ a_simp m) : a_simp m = p := by
  have hp_odd : p % 2 = 1 := by
    have h_cases : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases h_cases with h0 | h1
    · have h_div : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have hp2 : p = 2 := prime_of_two_dvd hp h_div
      subst hp2
      have h_sq : (m + 7)^2 = 10 := by omega
      have h_ge : (m + 7)^2 ≥ 49 := by
        have : m + 7 ≥ 7 := by omega
        nlinarith
      omega
    · exact h1
  have h_dvd1 : 2 ∣ (m + 4).factorial := by
    apply Nat.dvd_factorial (by decide)
    omega
  have h_dvd2 : p ∣ (m + 4).factorial := Nat.dvd_factorial hp.pos h_le4
  have h_cop : Nat.Coprime 2 p := coprime_two_of_odd p hp_odd
  have h_2p : 2 * p ∣ (m + 4).factorial := Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop h_dvd1 h_dvd2
  have h_D : 2 * p ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_2p _
  have h_N_dvd : 2 * p ∣ (m + 7)^2 - 2 := by
    rw [h_N]
    use p
    ring
  have h_G : 2 * p ∣ Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial) := Nat.dvd_gcd h_N_dvd h_D
  have h_G_pos : 0 < Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial) := by
    have hN : 0 < (m + 7)^2 - 2 := by
      rw [h_N]
      have : p ≥ 2 := hp.two_le
      positivity
    exact Nat.gcd_pos_of_pos_left _ hN
  have h_G_le : 2 * p ≤ Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial) := Nat.le_of_dvd h_G_pos h_G
  have h_div : a_simp m ≤ p := by
    dsimp [a_simp]
    apply Nat.div_le_of_le_mul
    have h_G_mul : (2 * p) * p ≤ Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial) * p := Nat.mul_le_mul_right p h_G_le
    have h_ring : (2 * p) * p = 2 * p^2 := by ring
    rw [h_ring] at h_G_mul
    nth_rw 1 [h_N]
    exact h_G_mul
  have h_ge : a_simp m ≥ p := Nat.le_of_dvd (a_simp_pos m) hdvd
  omega

theorem cubic_ineq (p : ℕ) (hp : p ≥ 8) : p^3 > 4 * p^2 + 20 * p + 23 := by
  rcases p with _| _| _| _| _| _| _| _| q
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · -- p = q + 8
    have h1 : (q + 8)^3 = q^3 + 24 * q^2 + 192 * q + 512 := by ring
    have h2 : 4 * (q + 8)^2 + 20 * (q + 8) + 23 = 4 * q^2 + 84 * q + 439 := by ring
    rw [h1, h2]
    nlinarith

theorem cubic_ineq_11 (p : ℕ) (hp : p ≥ 11) : p^3 > 9 * p^2 + 12 * p + 2 := by
  rcases p with _| _| _| _| _| _| _| _| _| _| _| q
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · -- p = q + 11
    have h1 : (q + 11)^3 = q^3 + 33 * q^2 + 363 * q + 1331 := by ring
    have h2 : 9 * (q + 11)^2 + 12 * (q + 11) + 2 = 9 * q^2 + 210 * q + 1223 := by ring
    rw [h1, h2]
    nlinarith

theorem cubic_ineq_7 (p : ℕ) (hp : p ≥ 7) : p^4 > 16 * p^2 + 16 * p + 2 := by
  rcases p with _| _| _| _| _| _| _| q
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · -- p = q + 7
    have h1 : (q + 7)^4 = q^4 + 28 * q^3 + 294 * q^2 + 1372 * q + 2401 := by ring
    have h2 : 16 * (q + 7)^2 + 16 * (q + 7) + 2 = 16 * q^2 + 240 * q + 898 := by ring
    rw [h1, h2]
    nlinarith

theorem cubic_ineq_5 (p : ℕ) (hp : p ≥ 5) : p^5 > 25 * p^2 + 20 * p + 2 := by
  rcases p with _| _| _| _| _| q
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · -- p = q + 5
    have h1 : (q + 5)^5 = q^5 + 25 * q^4 + 250 * q^3 + 1250 * q^2 + 3125 * q + 3125 := by ring
    have h2 : 25 * (q + 5)^2 + 20 * (q + 5) + 2 = 25 * q^2 + 270 * q + 727 := by ring
    rw [h1, h2]
    have h_pos : q^5 + 25 * q^4 + 250 * q^3 ≥ 0 := by positivity
    have h_ineq : q^5 + 25 * q^4 + 250 * q^3 + 1250 * q^2 + 3125 * q + 3125 ≥ 1250 * q^2 + 3125 * q + 3125 := by omega
    have h_lower : 1250 * q^2 + 3125 * q + 3125 > 25 * q^2 + 270 * q + 727 := by omega
    omega

theorem K_neq_1 (x p : ℕ) (h : x^2 - 2 = p^2) (hp : p ≥ 23) (hx : x ≥ p) : False := by
  have h_add : x^2 = p^2 + 2 := by
    have : x^2 ≥ 2 := by nlinarith
    omega
  have h_ne : x ≠ p := by
    intro h_eq
    subst h_eq
    nlinarith
  have hx2 : x ≥ p + 1 := by omega
  have h_add2 : x^2 ≥ (p + 1)^2 := by nlinarith
  nlinarith

theorem K_neq_4 (x p : ℕ) (h : x^2 - 2 = 4 * p^2) (hp : p ≥ 23) : False := by
  have h_add : x^2 = 4 * p^2 + 2 := by
    have : x^2 ≥ 2 := by
      have : 4 * p^2 ≥ 2 := by nlinarith
      omega
    omega
  have h_le : x ≥ 2 * p := by
    by_contra hc
    have : x < 2 * p := by omega
    nlinarith
  have h_ne : x ≠ 2 * p := by
    intro h_eq
    subst h_eq
    nlinarith
  have hx2 : x ≥ 2 * p + 1 := by omega
  have h_add2 : x^2 ≥ (2 * p + 1)^2 := by nlinarith
  nlinarith

theorem sq_mod_three (x : ℕ) : x^2 % 3 = 0 ∨ x^2 % 3 = 1 := by
  have h_mod : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases h_mod with h0 | h1 | h2
  · set q := x / 3
    have hm : x = 3 * q := by omega
    have h_sq : x^2 = 3 * (3 * q^2) := by
      rw [hm]
      ring
    rw [h_sq]
    omega
  · set q := x / 3
    have hm : x = 3 * q + 1 := by omega
    have h_sq : x^2 = 3 * (3 * q^2 + 2 * q) + 1 := by
      rw [hm]
      ring
    rw [h_sq]
    omega
  · set q := x / 3
    have hm : x = 3 * q + 2 := by omega
    have h_sq : x^2 = 3 * (3 * q^2 + 4 * q + 1) + 1 := by
      rw [hm]
      ring
    rw [h_sq]
    omega

theorem K_neq_3 (x p : ℕ) (hp : Nat.Prime p) (h : x^2 - 2 = 3 * p^2) : False := by
  have h_pos : 3 * p^2 > 0 := by
    have : p ≥ 2 := hp.two_le
    positivity
  have h_sub : x^2 - 2 > 0 := by omega
  have h_sq : x^2 ≥ 2 := by omega
  have h_add : x^2 = 3 * p^2 + 2 := by omega
  have h_mod : x^2 % 3 = 2 := by
    rw [h_add]
    set k := p^2
    have : 3 * k + 2 = 3 * k + 2 := rfl
    omega
  have h_sq_mod := sq_mod_three x
  omega

theorem dvd_factorial_prime_cube (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (h : 3 * p ≤ k) : p^3 ∣ k.factorial := by
  induction k, h using Nat.le_induction with
  | base =>
    have hp2 : 2 * p ≤ 3 * p - 1 := by
      have : p ≥ 2 := hp.two_le
      omega
    have hp_pos : 0 < p := hp.pos
    have hdvd : p^2 ∣ (3 * p - 1).factorial := dvd_factorial_prime_sq p hp (3 * p - 1) hp2
    rcases hdvd with ⟨Q, hQ⟩
    have h_fac : (3 * p).factorial = (3 * p) * (3 * p - 1).factorial := by
      have h_eq : 3 * p = (3 * p - 1) + 1 := by
        have : p ≥ 2 := hp.two_le
        omega
      nth_rw 1 [h_eq]
      rw [Nat.factorial_succ (3 * p - 1)]
      rw [← h_eq]
    rw [h_fac, hQ]
    use 3 * Q
    ring
  | succ x hx ih =>
    have h_fac : (x + 1).factorial = (x + 1) * x.factorial := Nat.factorial_succ x
    rw [h_fac]
    exact dvd_mul_of_dvd_right ih (x + 1)

theorem dvd_factorial_prime_four (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (h : 4 * p ≤ k) : p^4 ∣ k.factorial := by
  induction k, h using Nat.le_induction with
  | base =>
    have hp2 : 3 * p ≤ 4 * p - 1 := by
      have : p ≥ 2 := hp.two_le
      omega
    have hp_pos : 0 < p := hp.pos
    have hdvd : p^3 ∣ (4 * p - 1).factorial := dvd_factorial_prime_cube p hp (4 * p - 1) hp2
    rcases hdvd with ⟨Q, hQ⟩
    have h_fac : (4 * p).factorial = (4 * p) * (4 * p - 1).factorial := by
      have h_eq : 4 * p = (4 * p - 1) + 1 := by
        have : p ≥ 2 := hp.two_le
        omega
      nth_rw 1 [h_eq]
      rw [Nat.factorial_succ (4 * p - 1)]
      rw [← h_eq]
    rw [h_fac, hQ]
    use 4 * Q
    ring
  | succ x hx ih =>
    have h_fac : (x + 1).factorial = (x + 1) * x.factorial := Nat.factorial_succ x
    rw [h_fac]
    exact dvd_mul_of_dvd_right ih (x + 1)

theorem dvd_factorial_prime_five (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (h : 5 * p ≤ k) : p^5 ∣ k.factorial := by
  induction k, h using Nat.le_induction with
  | base =>
    have hp2 : 4 * p ≤ 5 * p - 1 := by
      have : p ≥ 2 := hp.two_le
      omega
    have hp_pos : 0 < p := hp.pos
    have hdvd : p^4 ∣ (5 * p - 1).factorial := dvd_factorial_prime_four p hp (5 * p - 1) hp2
    rcases hdvd with ⟨Q, hQ⟩
    have h_fac : (5 * p).factorial = (5 * p) * (5 * p - 1).factorial := by
      have h_eq : 5 * p = (5 * p - 1) + 1 := by
        have : p ≥ 2 := hp.two_le
        omega
      nth_rw 1 [h_eq]
      rw [Nat.factorial_succ (5 * p - 1)]
      rw [← h_eq]
    rw [h_fac, hQ]
    use 5 * Q
    ring
  | succ x hx ih =>
    have h_fac : (x + 1).factorial = (x + 1) * x.factorial := Nat.factorial_succ x
    rw [h_fac]
    exact dvd_mul_of_dvd_right ih (x + 1)

theorem dvd_factorial_pow2 (k : ℕ) : 2^k ∣ (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_eq : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h_eq]
    have h_fac : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      have : 2 * k + 2 = (2 * k + 1) + 1 := by omega
      nth_rw 1 [this]
      rw [Nat.factorial_succ (2 * k + 1)]
      have : 2 * k + 1 = (2 * k) + 1 := by omega
      nth_rw 1 [this]
      rw [Nat.factorial_succ (2 * k)]
      ring
    rw [h_fac]
    have h_2 : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [h_2]
    have h_div : 2^(k+1) ∣ 2 * (k + 1) * (2 * k + 1) * (2 * k).factorial := by
      have h_pow : 2^(k+1) = 2 * 2^k := by ring
      rw [h_pow]
      have h_mul : 2 * (k + 1) * (2 * k + 1) * (2 * k).factorial = 2 * ((k + 1) * (2 * k + 1) * (2 * k).factorial) := by ring
      rw [h_mul]
      apply Nat.mul_dvd_mul_left
      exact dvd_mul_of_dvd_right ih _
    exact h_div

theorem dvd_factorial_pow3 (k : ℕ) : 3^k ∣ (3 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_eq : 3 * (k + 1) = 3 * k + 3 := by ring
    rw [h_eq]
    have h_fac : (3 * k + 3).factorial = (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial := by
      have : 3 * k + 3 = (3 * k + 2) + 1 := by omega
      nth_rw 1 [this]
      rw [Nat.factorial_succ (3 * k + 2)]
      have : 3 * k + 2 = (3 * k + 1) + 1 := by omega
      nth_rw 1 [this]
      rw [Nat.factorial_succ (3 * k + 1)]
      have : 3 * k + 1 = (3 * k) + 1 := by omega
      nth_rw 1 [this]
      rw [Nat.factorial_succ (3 * k)]
      ring
    rw [h_fac]
    have h_3 : 3 * k + 3 = 3 * (k + 1) := by ring
    rw [h_3]
    have h_div : 3^(k+1) ∣ 3 * (k + 1) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial := by
      have h_pow : 3^(k+1) = 3 * 3^k := by ring
      rw [h_pow]
      have h_mul : 3 * (k + 1) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial = 3 * ((k + 1) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial) := by ring
      rw [h_mul]
      apply Nat.mul_dvd_mul_left
      exact dvd_mul_of_dvd_right ih _
    exact h_div

theorem dvd_factorial_pow (p : ℕ) (hp : p ≥ 1) (k : ℕ) : p^k ∣ (k * p).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_eq : (k + 1) * p = k * p + p := by ring
    rw [h_eq]
    have h_fac : (k * p + p).factorial = (k * p + p) * (k * p + p - 1).factorial := by
      have : k * p + p = (k * p + p - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [Nat.factorial_succ, ← this]
    rw [h_fac]
    have h_pow : p^(k+1) = p * p^k := by ring
    rw [h_pow]
    have h_div_p : p ∣ k * p + p := by
      use k + 1
      ring
    have h_div_pow : p^k ∣ (k * p + p - 1).factorial := by
      have h_le : k * p ≤ k * p + p - 1 := by omega
      exact dvd_trans ih (Nat.factorial_dvd_factorial h_le)
    exact mul_dvd_mul h_div_p h_div_pow

theorem power_ineq_2 (k : ℕ) (hk : k ≥ 22) : 2^(k+1) > (2 * k + 5)^2 - 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    have h_step : 2^(x + 2) = 2 * 2^(x + 1) := by ring
    have h_eq : 2 * (x + 1) + 5 = 2 * x + 7 := by ring
    rw [h_step, h_eq]
    have h_ih_add : 2^(x+1) + 2 > (2 * x + 5)^2 := by omega
    have h_poly : 2 * (2 * x + 5)^2 ≥ (2 * x + 7)^2 + 4 := by nlinarith
    omega

theorem power_ineq_3 (k : ℕ) (hk : k ≥ 14) : 3^(k+1) > (3 * k + 6)^2 - 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    have h_step : 3^(x + 2) = 3 * 3^(x + 1) := by ring
    have h_eq : 3 * (x + 1) + 6 = 3 * x + 9 := by ring
    rw [h_step, h_eq]
    have h_ih_add : 3^(x+1) + 2 > (3 * x + 6)^2 := by omega
    have h_poly : 3 * (3 * x + 6)^2 ≥ (3 * x + 9)^2 + 4 := by nlinarith
    omega

theorem power_ineq_5 (p k : ℕ) (hp : p ≥ 5) (hk : k ≥ 5) : p^(k+1) > (p * k + p + 3)^2 - 2 := by
  induction k, hk using Nat.le_induction with
  | base =>
    rcases p with _| _| _| _| _| q
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · -- p = q + 5
      have h1 : (q + 5)^6 = q^6 + 30 * q^5 + 375 * q^4 + 2500 * q^3 + 9375 * q^2 + 18750 * q + 15625 := by ring
      have h2_1 : ((q + 5) * 5 + (q + 5) + 3)^2 = 36 * q^2 + 396 * q + 1089 := by ring
      have h2 : ((q + 5) * 5 + (q + 5) + 3)^2 - 2 = 36 * q^2 + 396 * q + 1087 := by omega
      rw [h1, h2]
      have h_pos : q^6 + 30 * q^5 + 375 * q^4 + 2500 * q^3 ≥ 0 := by positivity
      have h_ineq : q^6 + 30 * q^5 + 375 * q^4 + 2500 * q^3 + 9375 * q^2 + 18750 * q + 15625 ≥ 9375 * q^2 + 18750 * q + 15625 := by omega
      have h_lower : 9375 * q^2 + 18750 * q + 15625 > 36 * q^2 + 396 * q + 1087 := by omega
      omega
  | succ x hx ih =>
    have h_step : p^(x + 2) = p * p^(x + 1) := by ring
    set Y := p * x + p + 3
    have h_eq : p * (x + 1) + p + 3 = Y + p := by
      dsimp [Y]
      ring
    rw [h_step, h_eq]
    have h_ih_add : p^(x+1) + 2 > Y^2 := by
      have : p * x + p + 3 = Y := rfl
      omega
    have h_mul_le : p * (p^(x+1) + 2) ≥ p * Y^2 + 5 := by nlinarith
    have h_poly : p * Y^2 ≥ (Y + p)^2 + 2 * p - 2 := by
      have h_Yp : Y ≥ p := by dsimp [Y]; omega
      have h_Y5 : Y ≥ 5 := by dsimp [Y]; omega
      have h_p5 : p ≥ 5 := hp
      have h_2pY : 2 * p * Y ≤ 2 * Y^2 := by nlinarith
      have h_p2 : p^2 ≤ Y^2 := by nlinarith
      have h_2p : 2 * p ≤ Y^2 := by nlinarith
      have h_sum : (Y + p)^2 + 2 * p - 2 ≤ 5 * Y^2 := by
        have : (Y + p)^2 = Y^2 + 2 * p * Y + p^2 := by ring
        omega
      have h_LHS : p * Y^2 ≥ 5 * Y^2 := by nlinarith
      omega
    have h_poly_add : p * Y^2 + 2 ≥ (Y + p)^2 + 2 * p := by
      have : 2 * p ≥ 2 := by omega
      omega
    have h_prod_eq : p * p^(x+1) + 2 * p = p * (p^(x+1) + 2) := by ring
    clear h_poly
    generalize hB : p * (p^(x+1) + 2) = B at *
    generalize hC : p * Y^2 = C at *
    generalize hD : (Y + p)^2 = D at *
    have h_goal : p * p^(x+1) > D := by omega
    omega

theorem prime_factor_cases (m : ℕ) (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ a_simp m) : p ≥ m + 7 ∨ a_simp m = p := by
  have h_cases : m < 40 ∨ m ≥ 40 := by omega
  rcases h_cases with h_lt | h_ge
  · rcases m with _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| _| m
    · have h_val : a_simp 0 = 47 := rfl; right; have h_prime : Nat.Prime 47 := of_decide_eq_true rfl; have hp_eq : p = 47 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 1 = 31 := rfl; right; have h_prime : Nat.Prime 31 := of_decide_eq_true rfl; have hp_eq : p = 31 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 2 = 79 := rfl; right; have h_prime : Nat.Prime 79 := of_decide_eq_true rfl; have hp_eq : p = 79 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 3 = 7 := rfl; right; have h_prime : Nat.Prime 7 := of_decide_eq_true rfl; have hp_eq : p = 7 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 4 = 17 := rfl; right; have h_prime : Nat.Prime 17 := of_decide_eq_true rfl; have hp_eq : p = 17 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 5 = 71 := rfl; right; have h_prime : Nat.Prime 71 := of_decide_eq_true rfl; have hp_eq : p = 71 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 6 = 167 := rfl; right; have h_prime : Nat.Prime 167 := of_decide_eq_true rfl; have hp_eq : p = 167 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 7 = 97 := rfl; right; have h_prime : Nat.Prime 97 := of_decide_eq_true rfl; have hp_eq : p = 97 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 8 = 223 := rfl; right; have h_prime : Nat.Prime 223 := of_decide_eq_true rfl; have hp_eq : p = 223 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 9 = 127 := rfl; right; have h_prime : Nat.Prime 127 := of_decide_eq_true rfl; have hp_eq : p = 127 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 10 = 41 := rfl; right; have h_prime : Nat.Prime 41 := of_decide_eq_true rfl; have hp_eq : p = 41 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 11 = 23 := rfl; right; have h_prime : Nat.Prime 23 := of_decide_eq_true rfl; have hp_eq : p = 23 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 12 = 359 := rfl; right; have h_prime : Nat.Prime 359 := of_decide_eq_true rfl; have hp_eq : p = 359 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 13 = 199 := rfl; right; have h_prime : Nat.Prime 199 := of_decide_eq_true rfl; have hp_eq : p = 199 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 14 = 439 := rfl; right; have h_prime : Nat.Prime 439 := of_decide_eq_true rfl; have hp_eq : p = 439 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 15 = 241 := rfl; right; have h_prime : Nat.Prime 241 := of_decide_eq_true rfl; have hp_eq : p = 241 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 16 = 31 := rfl; right; have h_prime : Nat.Prime 31 := of_decide_eq_true rfl; have hp_eq : p = 31 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 17 = 41 := rfl; right; have h_prime : Nat.Prime 41 := of_decide_eq_true rfl; have hp_eq : p = 41 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 18 = 89 := rfl; right; have h_prime : Nat.Prime 89 := of_decide_eq_true rfl; have hp_eq : p = 89 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 19 = 337 := rfl; right; have h_prime : Nat.Prime 337 := of_decide_eq_true rfl; have hp_eq : p = 337 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 20 = 727 := rfl; right; have h_prime : Nat.Prime 727 := of_decide_eq_true rfl; have hp_eq : p = 727 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · exfalso; exact hp.not_dvd_one hdvd
    · have h_val : a_simp 22 = 839 := rfl; right; have h_prime : Nat.Prime 839 := of_decide_eq_true rfl; have hp_eq : p = 839 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 23 = 449 := rfl; right; have h_prime : Nat.Prime 449 := of_decide_eq_true rfl; have hp_eq : p = 449 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 24 = 137 := rfl; right; have h_prime : Nat.Prime 137 := of_decide_eq_true rfl; have hp_eq : p = 137 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 25 = 73 := rfl; right; have h_prime : Nat.Prime 73 := of_decide_eq_true rfl; have hp_eq : p = 73 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 26 = 1087 := rfl; right; have h_prime : Nat.Prime 1087 := of_decide_eq_true rfl; have hp_eq : p = 1087 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 27 = 577 := rfl; right; have h_prime : Nat.Prime 577 := of_decide_eq_true rfl; have hp_eq : p = 577 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 28 = 1223 := rfl; right; have h_prime : Nat.Prime 1223 := of_decide_eq_true rfl; have hp_eq : p = 1223 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 29 = 647 := rfl; right; have h_prime : Nat.Prime 647 := of_decide_eq_true rfl; have hp_eq : p = 647 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 30 = 1367 := rfl; right; have h_prime : Nat.Prime 1367 := of_decide_eq_true rfl; have hp_eq : p = 1367 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 31 = 103 := rfl; right; have h_prime : Nat.Prime 103 := of_decide_eq_true rfl; have hp_eq : p = 103 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · exfalso; exact hp.not_dvd_one hdvd
    · have h_val : a_simp 33 = 47 := rfl; right; have h_prime : Nat.Prime 47 := of_decide_eq_true rfl; have hp_eq : p = 47 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 34 = 73 := rfl; right; have h_prime : Nat.Prime 73 := of_decide_eq_true rfl; have hp_eq : p = 73 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 35 = 881 := rfl; right; have h_prime : Nat.Prime 881 := of_decide_eq_true rfl; have hp_eq : p = 881 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 36 = 1847 := rfl; right; have h_prime : Nat.Prime 1847 := of_decide_eq_true rfl; have hp_eq : p = 1847 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · have h_val : a_simp 37 = 967 := rfl; right; have h_prime : Nat.Prime 967 := of_decide_eq_true rfl; have hp_eq : p = 967 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · exfalso; exact hp.not_dvd_one hdvd
    · have h_val : a_simp 39 = 151 := rfl; right; have h_prime : Nat.Prime 151 := of_decide_eq_true rfl; have hp_eq : p = 151 := prime_dvd_prime hp h_prime (h_val ▸ hdvd); rw [hp_eq]; exact h_val
    · exfalso; omega
  · -- m >= 40
    by_cases hm51 : m = 51
    · subst hm51
      right
      have : a_simp 51 = 41 := by decide
      have : p = 41 := prime_dvd_prime hp (by decide) (by rw [this] at hdvd; exact hdvd)
      omega
    by_cases hm331 : m = 331
    · subst hm331
      right
      have : a_simp 331 = 239 := by decide
      have : p = 239 := prime_dvd_prime hp (by decide) (by rw [this] at hdvd; exact hdvd)
      omega
    by_cases h_ge_7 : p ≥ m + 7
    · left; exact h_ge_7
    · have h_le4 : p ≤ m + 4 := by
        have h_lt : p < m + 7 := by omega
        have h_le6 : p ≤ m + 6 := by omega
        have h_ne5 : p ≠ m + 5 := by
          intro h_eq
          exact prime_not_m_plus_5 m p hp h_eq hdvd
        have h_ne6 : p ≠ m + 6 := by
          intro h_eq
          exact prime_not_m_plus_6 m p hp h_eq hdvd
        omega
      have h_cases2 : 2 * p ≤ m + 4 ∨ 2 * p > m + 4 := by omega
      rcases h_cases2 with h_le2p | h_gt2p
      · -- 2 * p <= m + 4
        have h_3p : m + 4 < 3 * p ∨ m + 4 ≥ 3 * p := by omega
        rcases h_3p with h_lt3 | h_ge3
        · -- 2*p <= m+4 < 3*p
          exfalso
          have hp_ge11 : p ≥ 11 := by omega
          have h_fact_sq : p^2 ∣ (m + 4).factorial := dvd_factorial_prime_sq p hp (m + 4) h_le2p
          have h_D_sq : p^2 ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_fact_sq _
          have h_pow3 : p^3 ∣ (m + 7)^2 - 2 := p_pow_div_induction m p hp hdvd 2 h_D_sq
          have h_le_N : p^3 ≤ (m + 7)^2 - 2 := by
            have hN : 0 < (m + 7)^2 - 2 := by
              have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
              omega
            exact Nat.le_of_dvd hN h_pow3
          have h_m7 : m + 7 ≤ 3 * p + 2 := by omega
          have h_N_le : (m + 7)^2 - 2 ≤ (3 * p + 2)^2 - 2 := by
            have : (m + 7)^2 ≤ (3 * p + 2)^2 := by nlinarith
            omega
          have h_cube := cubic_ineq_11 p hp_ge11
          have h_eq : (3 * p + 2)^2 - 2 = 9 * p^2 + 12 * p + 2 := by
            have : (3 * p + 2)^2 = 9 * p^2 + 12 * p + 4 := by ring
            omega
          rw [h_eq] at h_N_le
          generalize p^3 = A at h_le_N h_cube
          generalize (m + 7)^2 - 2 = B at h_le_N h_N_le
          generalize 9 * p^2 + 12 * p + 2 = C at h_N_le h_cube
          omega
        · -- 3*p <= m+4
          have h_4p : m + 4 < 4 * p ∨ m + 4 ≥ 4 * p := by omega
          rcases h_4p with h_lt4 | h_ge4
          · -- 3*p <= m+4 < 4*p
            exfalso
            have hp_ge7 : p ≥ 7 := by omega
            have h_fact_sq : p^3 ∣ (m + 4).factorial := dvd_factorial_prime_cube p hp (m + 4) h_ge3
            have h_D_sq : p^3 ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_fact_sq _
            have h_pow3 : p^4 ∣ (m + 7)^2 - 2 := p_pow_div_induction m p hp hdvd 3 h_D_sq
            have h_le_N : p^4 ≤ (m + 7)^2 - 2 := by
              have hN : 0 < (m + 7)^2 - 2 := by
                have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
                omega
              exact Nat.le_of_dvd hN h_pow3
            have h_m7 : m + 7 ≤ 4 * p + 2 := by omega
            have h_N_le : (m + 7)^2 - 2 ≤ (4 * p + 2)^2 - 2 := by
              have : (m + 7)^2 ≤ (4 * p + 2)^2 := by nlinarith
              omega
            have h_cube := cubic_ineq_7 p hp_ge7
            have h_eq : (4 * p + 2)^2 - 2 = 16 * p^2 + 16 * p + 2 := by
              have : (4 * p + 2)^2 = 16 * p^2 + 16 * p + 4 := by ring
              omega
            rw [h_eq] at h_N_le
            generalize p^4 = A at h_le_N h_cube
            generalize (m + 7)^2 - 2 = B at h_le_N h_N_le
            generalize 16 * p^2 + 16 * p + 2 = C at h_N_le h_cube
            omega
          · -- 4*p <= m+4
            have h_5p : m + 4 < 5 * p ∨ m + 4 ≥ 5 * p := by omega
            rcases h_5p with h_lt5 | h_ge5
            · -- 4*p <= m+4 < 5*p
              exfalso
              have hp_ge5 : p ≥ 5 := by omega
              have h_fact_sq : p^4 ∣ (m + 4).factorial := dvd_factorial_prime_four p hp (m + 4) h_ge4
              have h_D_sq : p^4 ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_fact_sq _
              have h_pow3 : p^5 ∣ (m + 7)^2 - 2 := p_pow_div_induction m p hp hdvd 4 h_D_sq
              have h_le_N : p^5 ≤ (m + 7)^2 - 2 := by
                have hN : 0 < (m + 7)^2 - 2 := by
                  have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
                  omega
                exact Nat.le_of_dvd hN h_pow3
              have h_m7 : m + 7 ≤ 5 * p + 2 := by omega
              have h_N_le : (m + 7)^2 - 2 ≤ (5 * p + 2)^2 - 2 := by
                have : (m + 7)^2 ≤ (5 * p + 2)^2 := by nlinarith
                omega
              have h_cube := cubic_ineq_5 p hp_ge5
              have h_eq : (5 * p + 2)^2 - 2 = 25 * p^2 + 20 * p + 2 := by
                have : (5 * p + 2)^2 = 25 * p^2 + 20 * p + 4 := by ring
                omega
              rw [h_eq] at h_N_le
              generalize p^5 = A at h_le_N h_cube
              generalize (m + 7)^2 - 2 = B at h_le_N h_N_le
              generalize 25 * p^2 + 20 * p + 2 = C at h_N_le h_cube
              omega
            · -- 5*p <= m+4
              have h_p_cases : p = 2 ∨ p = 3 ∨ p ≥ 5 := by
                rcases p with _| _| _| _| _| q
                · contradiction
                · exfalso; exact hp.ne_one rfl
                · left; rfl
                · right; left; rfl
                · exfalso; have : Nat.Prime 4 := hp; contradiction
                · right; right; omega
              rcases h_p_cases with hp2 | hp3 | hp5
              · -- p = 2
                exfalso
                subst hp2
                have hk : (m + 4) / 2 ≥ 22 := by omega
                have h_div1 : 2^((m+4)/2) ∣ (2 * ((m+4)/2)).factorial := dvd_factorial_pow2 ((m+4)/2)
                have h_le : 2 * ((m+4)/2) ≤ m + 4 := Nat.mul_div_le (m + 4) 2
                have h_div2 : 2^((m+4)/2) ∣ (m+4).factorial := dvd_trans h_div1 (Nat.factorial_dvd_factorial h_le)
                have h_div3 : 2^((m+4)/2) ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_div2 _
                have h_pow : 2^((m+4)/2 + 1) ∣ (m+7)^2 - 2 := p_pow_div_induction m 2 Nat.prime_two hdvd ((m+4)/2) h_div3
                have h_le_N : 2^((m+4)/2 + 1) ≤ (m + 7)^2 - 2 := by
                  have hN : 0 < (m + 7)^2 - 2 := by
                    have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
                    omega
                  exact Nat.le_of_dvd hN h_pow
                have h_m7 : m + 7 < 2 * ((m+4)/2) + 5 := by omega
                have h_N_le : (m + 7)^2 - 2 < (2 * ((m+4)/2) + 5)^2 - 2 := by
                  have : (m + 7)^2 < (2 * ((m+4)/2) + 5)^2 := by nlinarith
                  omega
                have h_ineq := power_ineq_2 ((m+4)/2) hk
                generalize 2^((m+4)/2 + 1) = A at h_le_N h_ineq
                generalize (m + 7)^2 - 2 = B at h_le_N h_N_le
                generalize (2 * ((m+4)/2) + 5)^2 - 2 = C at h_N_le h_ineq
                omega
              · -- p = 3
                exfalso
                subst hp3
                have hk : (m + 4) / 3 ≥ 14 := by omega
                have h_div1 : 3^((m+4)/3) ∣ (3 * ((m+4)/3)).factorial := dvd_factorial_pow3 ((m+4)/3)
                have h_le : 3 * ((m+4)/3) ≤ m + 4 := Nat.mul_div_le (m + 4) 3
                have h_div2 : 3^((m+4)/3) ∣ (m+4).factorial := dvd_trans h_div1 (Nat.factorial_dvd_factorial h_le)
                have h_div3 : 3^((m+4)/3) ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_div2 _
                have h_pow : 3^((m+4)/3 + 1) ∣ (m+7)^2 - 2 := p_pow_div_induction m 3 Nat.prime_three hdvd ((m+4)/3) h_div3
                have h_le_N : 3^((m+4)/3 + 1) ≤ (m + 7)^2 - 2 := by
                  have hN : 0 < (m + 7)^2 - 2 := by
                    have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
                    omega
                  exact Nat.le_of_dvd hN h_pow
                have h_m7 : m + 7 < 3 * ((m+4)/3) + 6 := by omega
                have h_N_le : (m + 7)^2 - 2 < (3 * ((m+4)/3) + 6)^2 - 2 := by
                  have : (m + 7)^2 < (3 * ((m+4)/3) + 6)^2 := by nlinarith
                  omega
                have h_ineq := power_ineq_3 ((m+4)/3) hk
                generalize 3^((m+4)/3 + 1) = A at h_le_N h_ineq
                generalize (m + 7)^2 - 2 = B at h_le_N h_N_le
                generalize (3 * ((m+4)/3) + 6)^2 - 2 = C at h_N_le h_ineq
                omega
              · -- p >= 5
                exfalso
                have hk : (m + 4) / p ≥ 5 := by
                  have h_div_le : (m + 4) / p ≥ (5 * p) / p := Nat.div_le_div_right h_ge5
                  have h_self : (5 * p) / p = 5 := Nat.mul_div_cancel 5 hp.pos
                  omega
                have h_fact_sq : p^5 ∣ (m + 4).factorial := dvd_factorial_prime_five p hp (m + 4) h_ge5
                have h_D_sq : p^5 ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_fact_sq _
                have h_pow3 : p^6 ∣ (m + 7)^2 - 2 := p_pow_div_induction m p hp hdvd 5 h_D_sq
                have h_pow_any : p^((m+4)/p + 1) ∣ (m+7)^2 - 2 := by
                  have h_kp : ((m+4)/p) * p ≤ m + 4 := by
                    have : ((m+4)/p) * p = p * ((m+4)/p) := by ring
                    rw [this]
                    exact Nat.mul_div_le (m+4) p
                  have h_div1 : p^((m+4)/p) ∣ (((m+4)/p) * p).factorial := dvd_factorial_pow p (by omega) ((m+4)/p)
                  have h_div2 : p^((m+4)/p) ∣ (m+4).factorial := dvd_trans h_div1 (Nat.factorial_dvd_factorial h_kp)
                  have h_div3 : p^((m+4)/p) ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_div2 _
                  exact p_pow_div_induction m p hp hdvd ((m+4)/p) h_div3
                have h_le_N : p^((m+4)/p + 1) ≤ (m + 7)^2 - 2 := by
                  have hN : 0 < (m + 7)^2 - 2 := by
                    have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
                    omega
                  exact Nat.le_of_dvd hN h_pow_any
                have h_div_lt : m + 4 < p * ((m+4)/p) + p := by
                  have h_eq : m + 4 = p * ((m+4)/p) + (m+4)%p := (Nat.div_add_mod (m+4) p).symm
                  have h_mod_lt := Nat.mod_lt (m+4) hp.pos
                  omega
                generalize h_X : p * ((m+4)/p) = X at h_div_lt
                have h_m7 : m + 7 < X + p + 3 := by omega
                have h_N_le : (m + 7)^2 - 2 < (X + p + 3)^2 - 2 := by
                  have : (m + 7)^2 < (X + p + 3)^2 := by nlinarith
                  have : 2 ≤ (m + 7)^2 := by nlinarith
                  omega
                have h_ineq := power_ineq_5 p ((m+4)/p) hp5 hk
                rw [← h_X] at h_N_le
                generalize p^((m+4)/p + 1) = A at h_le_N h_ineq
                generalize (m + 7)^2 - 2 = B at h_le_N h_N_le
                generalize (p * ((m+4)/p) + p + 3)^2 - 2 = C at h_N_le h_ineq
                omega
      · -- 2 * p > m + 4
        -- since m >= 40, 2p > 44 => p >= 23
        have hp23 : p ≥ 23 := by omega
        have h_div_fact : p ∣ (m + 4).factorial := Nat.dvd_factorial hp.pos h_le4
        have h_div_D : p ∣ 2 * (m + 6) * (m + 4).factorial := dvd_mul_of_dvd_right h_div_fact _
        have h_div_D_pow : p^1 ∣ 2 * (m + 6) * (m + 4).factorial := by rwa [pow_one]
        have h_pow2 : p^2 ∣ (m + 7)^2 - 2 := p_pow_div_induction m p hp hdvd 1 h_div_D_pow
        have h_K : ∃ K : ℕ, (m + 7)^2 - 2 = K * p^2 := by
          rcases h_pow2 with ⟨K, h_K_eq⟩
          use K
          rw [h_K_eq, mul_comm]
        rcases h_K with ⟨K, h_K_eq⟩
        have h_K_bound : K ≤ 4 := by
          have h_N_lt : (m + 7)^2 - 2 < 4 * p^2 + 12 * p + 9 := by
            have : (m + 7)^2 < (2 * p + 3)^2 := by nlinarith
            have : (2 * p + 3)^2 = 4 * p^2 + 12 * p + 9 := by ring
            omega
          have h_K_mul : K * p^2 < 4 * p^2 + 12 * p + 9 := h_K_eq ▸ h_N_lt
          have h_poly : 4 * p^2 + 12 * p + 9 < 5 * p^2 := by nlinarith
          have h_lt : K * p^2 < 5 * p^2 := by linarith [h_K_mul, h_poly]
          exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h_lt)
        have h_K_pos : K ≥ 1 := by
          have h_K0 : K ≠ 0 := by
            intro h_eq
            subst h_eq
            have : (m + 7)^2 - 2 = 0 := by
              rw [h_K_eq]
              ring
            have : (m + 7)^2 = 2 := by
              have : 2 ≤ (m + 7)^2 := by nlinarith
              omega
            have : (m + 7)^2 ≥ 49 := by
              have : m + 7 ≥ 7 := by omega
              nlinarith
            omega
          omega
        have h_K_cases : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 := by omega
        rcases h_K_cases with hK1 | hK2 | hK3 | hK4
        · subst hK1
          exfalso
          have h_K_eq' : (m + 7)^2 - 2 = p^2 := by
            rw [h_K_eq]
            ring
          exact K_neq_1 (m + 7) p h_K_eq' hp23 (by omega)
        · -- K = 2 is handled by a_simp_eq_p_of_N_eq_2p2!
          subst hK2
          right
          exact a_simp_eq_p_of_N_eq_2p2 m p hp h_K_eq h_le4 hdvd
        · subst hK3
          exfalso
          exact K_neq_3 (m + 7) p hp h_K_eq
        · subst hK4
          exfalso
          exact K_neq_4 (m + 7) p h_K_eq hp23

theorem prime_or_one_of_mul_eq_one {q : ℕ} (h_mul : ∀ a b, q = a * b → a = 1 ∨ b = 1) :
  q = 1 ∨ Nat.Prime q := by
  by_cases hq1 : q = 1
  · left; exact hq1
  · right
    have h_not_unit : ¬ IsUnit q := by
      have h_unit (x : ℕ) : IsUnit x ↔ x = 1 := isUnit_iff_dvd_one.trans Nat.dvd_one
      rw [h_unit]
      exact hq1
    refine ⟨h_not_unit, ?_⟩
    intro a b hab
    have h_unit (x : ℕ) : IsUnit x ↔ x = 1 := isUnit_iff_dvd_one.trans Nat.dvd_one
    rw [h_unit, h_unit]
    exact h_mul a b hab

theorem exists_two_prime_factors_of_not_prime_or_one {q : ℕ} (hq1 : q ≠ 1) (hq2 : ¬ Nat.Prime q) :
  ∃ p1 p2, Nat.Prime p1 ∧ Nat.Prime p2 ∧ p1 * p2 ∣ q := by
  by_cases hq0 : q = 0
  · use 2, 2
    refine ⟨Nat.prime_two, Nat.prime_two, ?_⟩
    rw [hq0]
    exact dvd_zero _
  · have hq_gt_one : 1 < q := by omega
    have h_not_irr : ¬ Irreducible q := hq2
    have h_unit (x : ℕ) : IsUnit x ↔ x = 1 := isUnit_iff_dvd_one.trans Nat.dvd_one
    have h_comp : ∃ a b, q = a * b ∧ a ≠ 1 ∧ b ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply h_not_irr
      have h_not_unit : ¬ IsUnit q := by
        rw [h_unit]
        exact hq1
      refine ⟨h_not_unit, ?_⟩
      intro a b hab
      have h_or := hc a b hab
      rw [h_unit, h_unit]
      by_cases ha1 : a = 1
      · left; exact ha1
      · right; exact h_or ha1
    rcases h_comp with ⟨a, b, hab, ha, hb⟩
    have ⟨p1, hp1_prime, hp1_dvd⟩ := Nat.exists_prime_and_dvd ha
    have ⟨p2, hp2_prime, hp2_dvd⟩ := Nat.exists_prime_and_dvd hb
    use p1, p2
    refine ⟨hp1_prime, hp2_prime, ?_⟩
    rw [hab]
    exact mul_dvd_mul hp1_dvd hp2_dvd

/-- A363102 Conjecture 1: The sequence contains only 1's and primes. -/
theorem oeis_a363102_conjecture_1 :
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := by
  intro n hn
  rcases n with _| _| _| _| _| _| _| m
  · contradiction
  · contradiction
  · contradiction
  · decide
  · decide
  · decide
  · decide
  · rw [a_eq_a_simp]
    have h_dec : Decidable (a_simp m = 1 ∨ Nat.Prime (a_simp m)) := Classical.dec _
    cases h_dec with
    | isTrue h => exact h
    | isFalse h =>
      exfalso
      have ha1 : a_simp m ≠ 1 := by
        intro h1
        apply h
        left; exact h1
      have ha2 : ¬ Nat.Prime (a_simp m) := by
        intro h2
        apply h
        right; exact h2
      rcases (exists_two_prime_factors_of_not_prime_or_one ha1 ha2) with ⟨p1, p2, hp1, hp2, hdvd⟩
      have hdvd1 : p1 ∣ a_simp m := by
        rcases hdvd with ⟨k, hk⟩
        rw [hk]
        use p2 * k
        ring
      have hdvd2 : p2 ∣ a_simp m := by
        rcases hdvd with ⟨k, hk⟩
        rw [hk]
        use p1 * k
        ring
      have h_cases1 := prime_factor_cases m p1 hp1 hdvd1
      have h_cases2 := prime_factor_cases m p2 hp2 hdvd2
      have hp1_ge : p1 ≥ m + 7 := by
        rcases h_cases1 with h_ge | h_eq
        · exact h_ge
        · exfalso
          rw [h_eq] at ha2
          exact ha2 hp1
      have hp2_ge : p2 ≥ m + 7 := by
        rcases h_cases2 with h_ge | h_eq
        · exact h_ge
        · exfalso
          rw [h_eq] at ha2
          exact ha2 hp2
      have h_prod : p1 * p2 ≥ (m + 7)^2 := by
        nlinarith
      have h_a_le : a_simp m ≤ (m + 7)^2 - 2 := by
        have h_dvdN := a_simp_dvd_N m
        have hN_pos : 0 < (m + 7)^2 - 2 := by
          have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
          omega
        exact Nat.le_of_dvd hN_pos h_dvdN
      have h_prod_le : p1 * p2 ≤ a_simp m := by
        have h_pos : 0 < a_simp m := a_simp_pos m
        exact Nat.le_of_dvd h_pos hdvd
      have h_contra : (m + 7)^2 ≤ (m + 7)^2 - 2 :=
        le_trans h_prod (le_trans h_prod_le h_a_le)
      have h_false : (m + 7)^2 > (m + 7)^2 - 2 := by
        have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
        omega
      omega
