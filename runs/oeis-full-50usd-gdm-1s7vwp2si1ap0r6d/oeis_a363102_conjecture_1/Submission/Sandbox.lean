import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Let's define the sum of factorials
def S (n : ℕ) : ℕ := Finset.sum (range (n + 1)) (fun k => k.factorial)

-- Let's see if we can prove the basic relation
theorem S_succ (n : ℕ) : S (n + 1) = S n + (n + 1).factorial := by
  dsimp [S]
  rw [sum_range_succ]


-- Let's define a051403 using S
def a051403_alt (n : ℕ) : ℕ := ((n + 2) * S n) / 2

theorem a051403_alt_eq (n : ℕ) : a051403_alt n = ((n + 2) * S n) / 2 := rfl

theorem S_succ_even (n : ℕ) : 2 ∣ S (n + 1) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [S_succ]
    -- S (n + 2) = S (n + 1) + (n + 2).factorial
    -- Since S (n + 1) is even and (n + 2).factorial is even (since n + 2 >= 2)
    apply dvd_add ih
    -- now we show 2 | (n + 2).factorial
    exact dvd_factorial (by decide) (by omega)



theorem prod_even (n : ℕ) : 2 ∣ (n + 2) * S n := by
  cases n with
  | zero =>
    -- (0 + 2) * S 0 = 2 * S 0
    use S 0
  | succ n =>
    -- (succ n + 2) * S (succ n)
    -- since 2 | S (succ n)
    have h : 2 ∣ S (n + 1) := S_succ_even n
    exact dvd_mul_of_dvd_right h (n + 3)



theorem a051403_alt_cancel (n : ℕ) : 2 * a051403_alt n = (n + 2) * S n := by
  dsimp [a051403_alt]
  exact Nat.mul_div_cancel' (prod_even n)




-- Let's define a051403 as in Spec.lean
def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  num / Nat.gcd num denom_arg


theorem a051403_cancel (n : ℕ) : 2 * a051403 n = (n + 2) * S n := by
  dsimp [a051403]
  exact Nat.mul_div_cancel' (prod_even n)

theorem test_answer_spec : ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := answer(sorry)



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






