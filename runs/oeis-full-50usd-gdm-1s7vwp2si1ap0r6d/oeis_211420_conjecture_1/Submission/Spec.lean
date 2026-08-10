import FormalConjectures.Util.ProblemImports

open Nat

/--
A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$
-/
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

-- Defining the denominator product: $\prod_{k=0}^{r-1} (8n - (2k+1))$ in ℤ
/-- The denominator product $(8n - 1)(8n - 3) \cdots (8n - (2r - 1))$,
defined as $\prod_{k=0}^{r-1} (8n - (2k+1))$ in $\mathbb{Z}$. -/
def denominator_product (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ)) |>.prod

theorem denominator_product_succ (n r : ℕ) :
    denominator_product n (r + 1) = denominator_product n r * (8 * n - (2 * r + 1)) := by
  simp [denominator_product, List.range_succ, List.map_append]

theorem gcd_dvd_mul_of_dvd_of_dvd (A B Y : ℤ) (hA : A ∣ Y) (hB : B ∣ Y) :
    A * B ∣ Y * (Int.gcd A B : ℤ) := by
  rcases hA with ⟨qA, rfl⟩
  rcases hB with ⟨qB, hB⟩
  rw [Int.gcd_eq_gcd_ab]
  use qB * Int.gcdA A B + qA * Int.gcdB A B
  have h1 : A * qA = B * qB := hB
  calc A * qA * (A * Int.gcdA A B + B * Int.gcdB A B)
    _ = (A * qA) * A * Int.gcdA A B + A * qA * B * Int.gcdB A B := by ring
    _ = (B * qB) * A * Int.gcdA A B + A * qA * B * Int.gcdB A B := by rw [h1]
    _ = A * B * (qB * Int.gcdA A B + qA * Int.gcdB A B) := by ring

theorem gcd_list_prod_dvd (L : List ℤ) (B : ℤ) :
    Int.gcd L.prod B ∣ (L.map (fun x => Int.gcd x B) |>.prod) := by
  induction L with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.prod_cons, List.map_cons]
    have h1 : Int.gcd (x * xs.prod) B ∣ Int.gcd x B * Int.gcd xs.prod B := by
      change Nat.gcd (x * xs.prod).natAbs B.natAbs ∣ Nat.gcd x.natAbs B.natAbs * Nat.gcd xs.prod.natAbs B.natAbs
      rw [Int.natAbs_mul]
      rw [Nat.gcd_comm (x.natAbs * xs.prod.natAbs) _, Nat.gcd_comm x.natAbs _, Nat.gcd_comm xs.prod.natAbs _]
      exact gcd_mul_dvd_mul_gcd B.natAbs x.natAbs xs.prod.natAbs
    have h2 : Int.gcd x B * Int.gcd xs.prod B ∣ Int.gcd x B * (xs.map (fun x => Int.gcd x B)).prod := mul_dvd_mul_left _ ih
    exact dvd_trans h1 h2

theorem list_prod_dvd_of_dvd {α : Type*} (L : List α) (f g : α → ℕ) (h : ∀ x ∈ L, f x ∣ g x) :
    (L.map f |>.prod) ∣ (L.map g |>.prod) := by
  induction L with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    have hx : f x ∣ g x := h x (by simp)
    have hxs : ∀ y ∈ xs, f y ∣ g y := fun y hy => h y (by simp [hy])
    exact mul_dvd_mul hx (ih hxs)

theorem gcd_dvd_sub (x B : ℤ) :
    (Int.gcd x B : ℤ) ∣ x - B := by
  exact dvd_sub (Int.gcd_dvd_left x B) (Int.gcd_dvd_right x B)

theorem gcd_dvd_sub_nat (x B : ℤ) :
    Int.gcd x B ∣ (x - B).natAbs := by
  have h := gcd_dvd_sub x B
  exact Int.natAbs_dvd_natAbs.mpr h

theorem claim2 (r : ℕ) : ∃ C : ℤ, C > 0 ∧ ∀ n : ℕ,
    (Int.gcd (denominator_product n r) ((8 * n : ℤ) - (2 * r + 1 : ℤ)) : ℤ) ∣ C := by
  use (((2 * r).factorial) ^ r : ℕ)
  refine ⟨by positivity, fun n => ?_⟩
  norm_cast
  let B : ℤ := (8 * n : ℤ) - (2 * r + 1 : ℤ)
  have h_gcd_prod := gcd_list_prod_dvd ((List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ))) B
  rw [List.map_map] at h_gcd_prod
  have h_target_eq : ((List.range r).map (fun k => (2 * r).factorial) |>.prod) = (2 * r).factorial ^ r := by
    simp
  rw [← h_target_eq]
  have h_dvd_each : ∀ k ∈ List.range r, Int.gcd ((8 * n : ℤ) - (2 * k + 1 : ℤ)) B ∣ (2 * r).factorial := by
    intro k hk
    rw [List.mem_range] at hk
    have h_gcd_sub := gcd_dvd_sub_nat ((8 * n : ℤ) - (2 * k + 1 : ℤ)) B
    have h_diff : ((8 * n : ℤ) - (2 * k + 1 : ℤ)) - B = 2 * (r - k : ℤ) := by
      simp [B]
      ring
    rw [h_diff] at h_gcd_sub
    have h_natAbs : (2 * (r - k : ℤ)).natAbs = 2 * (r - k) := by
      have hk_le : k < r := hk
      have h_sub : 0 ≤ (r - k : ℤ) := by omega
      rw [Int.natAbs_mul]
      simp
      omega
    rw [h_natAbs] at h_gcd_sub
    have h_pos : 0 < 2 * (r - k) := by omega
    have h_le : 2 * (r - k) ≤ 2 * r := by omega
    have h_dvd_fact := Nat.dvd_factorial h_pos h_le
    exact dvd_trans h_gcd_sub h_dvd_fact
  have h_prod_dvd := list_prod_dvd_of_dvd (List.range r) (fun k => Int.gcd ((8 * n : ℤ) - (2 * k + 1 : ℤ)) B) (fun k => (2 * r).factorial) h_dvd_each
  exact dvd_trans h_gcd_prod h_prod_dvd


theorem div_eq_of_lt_of_le {a b c : ℕ} (hb : 0 < b) (h1 : b * c ≤ a) (h2 : a < b * (c + 1)) : a / b = c := by
  have h1' : c * b ≤ a := by rwa [mul_comm] at h1
  have h2' : a < (c + 1) * b := by rwa [mul_comm] at h2
  have h3 : c ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr h1'
  have h4 : a / b < c + 1 := (Nat.div_lt_iff_lt_mul hb).mpr h2'
  omega

theorem ratio_inequality (r P : ℕ) (hP : 0 < P) (hr : r < P) :
    4 * r / P + 3 * r / P + 2 * r / P ≤ 8 * r / P := by
  have h_cases :
    8 * r < P ∨
    (P ≤ 8 * r ∧ 4 * r < P) ∨
    (4 * r ≥ P ∧ 3 * r < P) ∨
    (3 * r ≥ P ∧ 8 * r < 3 * P) ∨
    (8 * r ≥ 3 * P ∧ 2 * r < P) ∨
    (2 * r ≥ P ∧ 8 * r < 5 * P) ∨
    (8 * r ≥ 5 * P ∧ 3 * r < 2 * P) ∨
    (3 * r ≥ 2 * P ∧ 4 * r < 3 * P) ∨
    (4 * r ≥ 3 * P ∧ 8 * r < 7 * P) ∨
    (8 * r ≥ 7 * P) := by omega
  rcases h_cases with h | h | h | h | h | h | h | h | h | h
  · have h1 : 4 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 3 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 4 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 5 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 5 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 3 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 6 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 3 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 7 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega

theorem n_div_P_relation (n P : ℕ) (hP : 0 < P) :
    4 * n / P = 4 * (n / P) + (4 * (n % P)) / P := by
  have h_eq : 4 * n = 4 * (n % P) + P * (4 * (n / P)) := by
    nth_rw 1 [← Nat.div_add_mod n P]
    ring
  rw [h_eq]
  rw [Nat.add_mul_div_left (4 * (n % P)) (4 * (n / P)) hP]
  omega

theorem div_add_div_eq (n P : ℕ) (hP : 0 < P) :
    4 * n / P + 3 * n / P + 2 * n / P ≤ 8 * n / P + n / P := by
  have h4 : 4 * n / P = 4 * (n / P) + (4 * (n % P)) / P := n_div_P_relation n P hP
  have h3 : 3 * n / P = 3 * (n / P) + (3 * (n % P)) / P := by
    have h_eq : 3 * n = 3 * (n % P) + P * (3 * (n / P)) := by
      nth_rw 1 [← Nat.div_add_mod n P]
      ring
    rw [h_eq]
    rw [Nat.add_mul_div_left (3 * (n % P)) (3 * (n / P)) hP]
    omega
  have h2 : 2 * n / P = 2 * (n / P) + (2 * (n % P)) / P := by
    have h_eq : 2 * n = 2 * (n % P) + (2 * (n / P)) * P := by
      nth_rw 1 [← Nat.div_add_mod n P]
      ring
    rw [h_eq]
    have h_comm : 2 * (n % P) + (2 * (n / P)) * P = 2 * (n % P) + P * (2 * (n / P)) := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_left (2 * (n % P)) (2 * (n / P)) hP]
    omega
  have h8 : 8 * n / P = 8 * (n / P) + (8 * (n % P)) / P := by
    have h_eq : 8 * n = 8 * (n % P) + P * (8 * (n / P)) := by
      nth_rw 1 [← Nat.div_add_mod n P]
      ring
    rw [h_eq]
    rw [Nat.add_mul_div_left (8 * (n % P)) (8 * (n / P)) hP]
    omega
  have hr : n % P < P := Nat.mod_lt n hP
  have hineq := ratio_inequality (n % P) P hP hr
  omega

theorem Y_dvd_X (n : ℕ) :
    ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) ∣ ((8 * n).factorial * n.factorial) := by
  let Y := (4 * n).factorial * (3 * n).factorial * (2 * n).factorial
  let X := (8 * n).factorial * n.factorial
  have hY : Y ≠ 0 := by positivity
  have hX : X ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hY hX]
  rw [Finsupp.le_def]
  intro p
  by_cases pp : p.Prime
  · have : Fact p.Prime := ⟨pp⟩
    rw [Nat.factorization_def Y pp, Nat.factorization_def X pp]
    have hY_val : padicValNat p Y = padicValNat p (4 * n).factorial + padicValNat p (3 * n).factorial + padicValNat p (2 * n).factorial := by
      change padicValNat p ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) = _
      have h1 : padicValNat p ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) =
                padicValNat p ((4 * n).factorial * (3 * n).factorial) + padicValNat p (2 * n).factorial := by
        exact padicValNat.mul (by positivity) (by positivity)
      have h2 : padicValNat p ((4 * n).factorial * (3 * n).factorial) =
                padicValNat p (4 * n).factorial + padicValNat p (3 * n).factorial := by
        exact padicValNat.mul (by positivity) (by positivity)
      rw [h1, h2]
    have hX_val : padicValNat p X = padicValNat p (8 * n).factorial + padicValNat p n.factorial := by
      exact padicValNat.mul (by positivity) (by positivity)
    rw [hY_val, hX_val]
    let b := 8 * n + 1
    have hb4 : log p (4 * n) < b := by
      have h_le := Nat.log_le_self p (4 * n)
      omega
    have hb3 : log p (3 * n) < b := by
      have h_le := Nat.log_le_self p (3 * n)
      omega
    have hb2 : log p (2 * n) < b := by
      have h_le := Nat.log_le_self p (2 * n)
      omega
    have hb8 : log p (8 * n) < b := by
      have h_le := Nat.log_le_self p (8 * n)
      omega
    have hbn : log p n < b := by
      have h_le := Nat.log_le_self p n
      omega
    rw [padicValNat_factorial hb4, padicValNat_factorial hb3, padicValNat_factorial hb2, padicValNat_factorial hb8, padicValNat_factorial hbn]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h_prime_pos : 1 < p := pp.one_lt
    have h_pow_pos : 0 < p ^ i := by positivity
    exact div_add_div_eq n (p ^ i) h_pow_pos
  · rw [Nat.factorization_eq_zero_of_not_prime Y pp, Nat.factorization_eq_zero_of_not_prime X pp]

theorem a_mul_Y_eq_X (n : ℕ) :
    (a n : ℤ) * ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial : ℕ) =
    ((8 * n).factorial * n.factorial : ℕ) := by
  have h := Nat.div_mul_cancel (Y_dvd_X n)
  exact_mod_cast h

theorem dvd_factorial_of_ge (n r : ℕ) (h : 8 * n ≥ 2 * r + 1) :
    ((8 * n - (2 * r + 1) : ℕ) : ℤ) ∣ ((8 * n).factorial : ℤ) := by
  have h1 : 0 < 8 * n - (2 * r + 1) := by omega
  have h2 : 8 * n - (2 * r + 1) ≤ 8 * n := by omega
  have h_dvd := Nat.dvd_factorial h1 h2
  exact_mod_cast h_dvd

theorem D_dvd_a_mul_Y (n r : ℕ) (h_ge : 8 * n ≥ 2 * r + 1) :
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial : ℕ) := by
  have h_dvd := dvd_factorial_of_ge n r h_ge
  have h_eq : ((8 * n : ℤ) - (2 * r + 1 : ℤ)) = ((8 * n - (2 * r + 1) : ℕ) : ℤ) := by omega
  rw [h_eq]
  have h_X : ((8 * n - (2 * r + 1) : ℕ) : ℤ) ∣ (((8 * n).factorial * n.factorial : ℕ) : ℤ) := by
    have h_mul : ((8 * n).factorial : ℤ) ∣ (((8 * n).factorial : ℕ) * (n.factorial : ℕ) : ℕ) := by
      exact_mod_cast dvd_mul_right (8 * n).factorial n.factorial
    exact dvd_trans h_dvd h_mul
  rw [← a_mul_Y_eq_X n] at h_X
  exact h_X

theorem choose_mul_factorial_mul_factorial_self (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k * (k.factorial * (n - k).factorial) = n.factorial := by
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial h

theorem factorial_identity (n : ℕ) :
    (8 * n).factorial * n.factorial * Nat.choose (3 * n) n =
    Nat.choose (8 * n) (4 * n) * Nat.choose (4 * n) (2 * n) *
    ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) := by
  have h1 : n ≤ 3 * n := by omega
  have h2 : 2 * n ≤ 4 * n := by omega
  have h3 : 4 * n ≤ 8 * n := by omega
  have h1_sub : 3 * n - n = 2 * n := by omega
  have h2_sub : 4 * n - 2 * n = 2 * n := by omega
  have h3_sub : 8 * n - 4 * n = 4 * n := by omega
  have eq1 := choose_mul_factorial_mul_factorial_self (3 * n) n h1
  rw [h1_sub] at eq1
  have eq2 := choose_mul_factorial_mul_factorial_self (4 * n) (2 * n) h2
  rw [h2_sub] at eq2
  have eq3 := choose_mul_factorial_mul_factorial_self (8 * n) (4 * n) h3
  rw [h3_sub] at eq3
  calc (8 * n).factorial * n.factorial * Nat.choose (3 * n) n
    _ = (Nat.choose (8 * n) (4 * n) * ((4 * n).factorial * (4 * n).factorial)) * n.factorial * Nat.choose (3 * n) n := by rw [← eq3]
    _ = Nat.choose (8 * n) (4 * n) * (4 * n).factorial * (4 * n).factorial * n.factorial * Nat.choose (3 * n) n := by ring
    _ = Nat.choose (8 * n) (4 * n) * (4 * n).factorial * (Nat.choose (4 * n) (2 * n) * ((2 * n).factorial * (2 * n).factorial)) * n.factorial * Nat.choose (3 * n) n := by rw [← eq2]
    _ = Nat.choose (8 * n) (4 * n) * Nat.choose (4 * n) (2 * n) * ((4 * n).factorial * (2 * n).factorial * (Nat.choose (3 * n) n * (n.factorial * (2 * n).factorial))) := by ring
    _ = Nat.choose (8 * n) (4 * n) * Nat.choose (4 * n) (2 * n) * ((4 * n).factorial * (2 * n).factorial * (3 * n).factorial) := by rw [eq1]
    _ = Nat.choose (8 * n) (4 * n) * Nat.choose (4 * n) (2 * n) * ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) := by ring


theorem rem_div_sum_le (rem r P k : ℕ) (hP : 0 < P) (h_gt : 8 * r + 3 < P)
    (h_rem : 8 * rem = k * P + 2 * r + 1) (hk_cases : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7) :
    4 * rem / P + 3 * rem / P + 2 * rem / P + 1 ≤ k := by
  rcases hk_cases with rfl | rfl | rfl | rfl
  · -- Case k = 1
    have hd4 : 4 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (4 * rem) < 8 * (P * 1) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (1 * P + 2 * r + 1) := by rw [h_rem]
          _ = 4 * P + 8 * r + 4 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    have hd3 : 3 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (3 * rem) < 8 * (P * 1) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (1 * P + 2 * r + 1) := by rw [h_rem]
          _ = 3 * P + 6 * r + 3 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    have hd2 : 2 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (2 * rem) < 8 * (P * 1) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (1 * P + 2 * r + 1) := by rw [h_rem]
          _ = 2 * P + 4 * r + 2 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    rw [hd4, hd3, hd2]
  · -- Case k = 3
    have hd4 : 4 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (4 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 12 * P + 8 * r + 4 := by omega
          _ = 4 * (3 * P + 2 * r + 1) := by ring
          _ = 4 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (4 * rem) := by ring
        omega
      · have h : 8 * (4 * rem) < 8 * (P * 2) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (3 * P + 2 * r + 1) := by rw [h_rem]
          _ = 12 * P + 8 * r + 4 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    have hd3 : 3 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (3 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 9 * P + 6 * r + 3 := by omega
          _ = 3 * (3 * P + 2 * r + 1) := by ring
          _ = 3 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (3 * rem) := by ring
        omega
      · have h : 8 * (3 * rem) < 8 * (P * 2) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (3 * P + 2 * r + 1) := by rw [h_rem]
          _ = 9 * P + 6 * r + 3 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    have hd2 : 2 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (2 * rem) < 8 * (P * 1) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (3 * P + 2 * r + 1) := by rw [h_rem]
          _ = 6 * P + 4 * r + 2 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    rw [hd4, hd3, hd2]
  · -- Case k = 5
    have hd4 : 4 * rem / P = 2 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 2) ≤ 8 * (4 * rem) := by
          calc 8 * (P * 2) = 16 * P := by ring
          _ ≤ 20 * P + 8 * r + 4 := by omega
          _ = 4 * (5 * P + 2 * r + 1) := by ring
          _ = 4 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (4 * rem) := by ring
        omega
      · have h : 8 * (4 * rem) < 8 * (P * 3) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (5 * P + 2 * r + 1) := by rw [h_rem]
          _ = 20 * P + 8 * r + 4 := by ring
          _ < 24 * P := by omega
          _ = 8 * (P * 3) := by ring
        omega
    have hd3 : 3 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (3 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 15 * P + 6 * r + 3 := by omega
          _ = 3 * (5 * P + 2 * r + 1) := by ring
          _ = 3 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (3 * rem) := by ring
        omega
      · have h : 8 * (3 * rem) < 8 * (P * 2) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (5 * P + 2 * r + 1) := by rw [h_rem]
          _ = 15 * P + 6 * r + 3 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    have hd2 : 2 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (2 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 10 * P + 4 * r + 2 := by omega
          _ = 2 * (5 * P + 2 * r + 1) := by ring
          _ = 2 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (2 * rem) := by ring
        omega
      · have h : 8 * (2 * rem) < 8 * (P * 2) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (5 * P + 2 * r + 1) := by rw [h_rem]
          _ = 10 * P + 4 * r + 2 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    rw [hd4, hd3, hd2]
  · -- Case k = 7
    have hd4 : 4 * rem / P = 3 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 3) ≤ 8 * (4 * rem) := by
          calc 8 * (P * 3) = 24 * P := by ring
          _ ≤ 28 * P + 8 * r + 4 := by omega
          _ = 4 * (7 * P + 2 * r + 1) := by ring
          _ = 4 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (4 * rem) := by ring
        omega
      · have h : 8 * (4 * rem) < 8 * (P * 4) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (7 * P + 2 * r + 1) := by rw [h_rem]
          _ = 28 * P + 8 * r + 4 := by ring
          _ < 32 * P := by omega
          _ = 8 * (P * 4) := by ring
        omega
    have hd3 : 3 * rem / P = 2 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 2) ≤ 8 * (3 * rem) := by
          calc 8 * (P * 2) = 16 * P := by ring
          _ ≤ 21 * P + 6 * r + 3 := by omega
          _ = 3 * (7 * P + 2 * r + 1) := by ring
          _ = 3 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (3 * rem) := by ring
        omega
      · have h : 8 * (3 * rem) < 8 * (P * 3) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (7 * P + 2 * r + 1) := by rw [h_rem]
          _ = 21 * P + 6 * r + 3 := by ring
          _ < 24 * P := by omega
          _ = 8 * (P * 3) := by ring
        omega
    have hd2 : 2 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (2 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 14 * P + 4 * r + 2 := by omega
          _ = 2 * (7 * P + 2 * r + 1) := by ring
          _ = 2 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (2 * rem) := by ring
        omega
      · have h : 8 * (2 * rem) < 8 * (P * 2) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (7 * P + 2 * r + 1) := by rw [h_rem]
          _ = 14 * P + 4 * r + 2 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    rw [hd4, hd3, hd2]

theorem omega_test (n r m P q rem : ℕ) (hP : 0 < P) (h_rem : rem < P)
    (h_eq1 : n = q * P + rem) (h_eq2 : 8 * n = (2 * m + 1) * P + 2 * r + 1) (h_gt : 8 * r + 3 < P) :
    4 * n / P + 3 * n / P + 2 * n / P + 1 ≤ 8 * n / P + n / P := by
  have hd8 : 8 * n / P = 2 * m + 1 := by
    rw [h_eq2]
    have : (2 * m + 1) * P + 2 * r + 1 = (2 * r + 1) + P * (2 * m + 1) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (2 * r + 1) (2 * m + 1) hP]
    have : (2 * r + 1) / P = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hdn : n / P = q := by
    rw [h_eq1]
    have : q * P + rem = rem + P * q := by ring
    rw [this]
    rw [Nat.add_mul_div_left rem q hP]
    have : rem / P = 0 := Nat.div_eq_of_lt h_rem
    omega
  have h_le_q : 8 * q ≤ 2 * m + 1 := by
    have h_div_le : 8 * (n / P) ≤ (8 * n) / P := by
      rw [Nat.le_div_iff_mul_le hP]
      calc 8 * (n / P) * P = 8 * (n / P * P) := by ring
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 (Nat.div_mul_le_self n P)
    rw [hd8] at h_div_le
    rw [hdn] at h_div_le
    exact h_div_le
  have h_rem_eq : 8 * rem = (2 * m + 1 - 8 * q) * P + 2 * r + 1 := by
    have h1 : 8 * n = 8 * q * P + 8 * rem := by
      rw [h_eq1]
      ring
    rw [h1] at h_eq2
    have h2 : (2 * m + 1) * P = (8 * q + (2 * m + 1 - 8 * q)) * P := by
      congr 1
      omega
    rw [h2] at h_eq2
    have h3 : (8 * q + (2 * m + 1 - 8 * q)) * P + 2 * r + 1 = 8 * q * P + (2 * m + 1 - 8 * q) * P + 2 * r + 1 := by ring
    rw [h3] at h_eq2
    omega
  have hd4 : 4 * n / P = 4 * q + 4 * rem / P := by
    rw [h_eq1]
    have : 4 * (q * P + rem) = 4 * rem + P * (4 * q) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (4 * rem) (4 * q) hP]
    omega
  have hd3 : 3 * n / P = 3 * q + 3 * rem / P := by
    rw [h_eq1]
    have : 3 * (q * P + rem) = 3 * rem + P * (3 * q) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (3 * rem) (3 * q) hP]
    omega
  have hd2 : 2 * n / P = 2 * q + 2 * rem / P := by
    rw [h_eq1]
    have : 2 * (q * P + rem) = 2 * rem + P * (2 * q) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (2 * rem) (2 * q) hP]
    omega
  rw [hd8, hdn, hd4, hd3, hd2]
  let k := 2 * m + 1 - 8 * q
  have hk_cases : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7 := by
    have h_lt : k * P < 8 * P := by
      calc k * P ≤ k * P + 2 * r + 1 := by omega
      _ = 8 * rem := by rw [h_rem_eq]
      _ < 8 * P := by omega
    have hk_lt : k < 8 := by
      by_contra h_ge
      push_neg at h_ge
      have : 8 * P ≤ k * P := Nat.mul_le_mul_right P h_ge
      omega
    have : k % 2 = 1 := by omega
    omega
  have h_rem_le := rem_div_sum_le rem r P k hP h_gt h_rem_eq hk_cases
  omega

lemma p_pow_gt_of_gt_padicValNat_factorial {p X : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : k = padicValNat p X.factorial) {i : ℕ} (hi : i > k) : p ^ i > X := by
  by_contra h_le
  push_neg at h_le
  have h_pos : p ^ i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i hp.out.ne_zero)
  have h_dvd := Nat.dvd_factorial h_pos h_le
  have h_ne : X.factorial ≠ 0 := Nat.factorial_ne_zero X
  rw [padicValNat_dvd_iff_le h_ne] at h_dvd
  rw [← hk] at h_dvd
  omega

theorem term_by_term (n r p i v k : ℕ) [hp : Fact p.Prime] (hv : v = padicValNat p (8 * n - (2 * r + 1)))
    (hk : k = padicValNat p (8 * r + 3).factorial) (hi_pos : i ≥ 1) (hn_ge : 8 * n ≥ 2 * r + 1) :
    let Iv := if i ≤ v then 1 else 0
    let Ik := if i ≤ k then 1 else 0
    4 * n / p^i + 3 * n / p^i + 2 * n / p^i + Iv ≤ 8 * n / p^i + n / p^i + Ik := by
  intro Iv Ik
  have h_pow_pos : p^i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i hp.out.ne_zero)
  have h_div := div_add_div_eq n (p^i) h_pow_pos
  by_cases h_v : i ≤ v
  · by_cases h_k : i ≤ k
    · have h_Iv : Iv = 1 := by simp [Iv, h_v]
      have h_Ik : Ik = 1 := by simp [Ik, h_k]
      rw [h_Iv, h_Ik]
      omega
    · have h_Iv : Iv = 1 := by simp [Iv, h_v]
      have h_Ik : Ik = 0 := by simp [Ik, h_k]
      rw [h_Iv, h_Ik]
      simp only [add_zero]
      have h_ne : 8 * n - (2 * r + 1) ≠ 0 := by omega
      have h_v_rew : i ≤ padicValNat p (8 * n - (2 * r + 1)) := hv ▸ h_v
      have h_dvd : p^i ∣ 8 * n - (2 * r + 1) := by
        rw [padicValNat_dvd_iff_le h_ne]
        exact h_v_rew
      have h_gt : p^i > 8 * r + 3 := by
        have hi_gt : i > k := by omega
        exact p_pow_gt_of_gt_padicValNat_factorial hk hi_gt
      let rem := n % (p^i)
      let q := n / (p^i)
      have h_eq1 : n = q * (p^i) + rem := by
        have : n = (p^i) * q + rem := (Nat.div_add_mod n (p^i)).symm
        rw [this, mul_comm (p^i) q]
      have h_rem : rem < p^i := Nat.mod_lt n h_pow_pos
      rcases h_dvd with ⟨c, hc⟩
      have hc2 : 8 * n = c * p^i + 2 * r + 1 := by
        have : 8 * n - (2 * r + 1) = c * p^i := by
          rw [hc, mul_comm]
        omega
      have h_P_odd : (p^i) % 2 = 1 := by
        have h_mod : (p^i) % 2 = 0 ∨ (p^i) % 2 = 1 := by omega
        rcases h_mod with h0 | h1
        · rcases Nat.dvd_of_mod_eq_zero h0 with ⟨k_odd, hk⟩
          have : 2 * (k_odd * c) = 8 * n - (2 * r + 1) := by
            calc 2 * (k_odd * c) = (2 * k_odd) * c := by ring
            _ = (p^i) * c := by rw [← hk]
            _ = 8 * n - (2 * r + 1) := hc.symm
          omega
        · exact h1
      have h_c_odd : c % 2 = 1 := by
        have h_mod : c % 2 = 0 ∨ c % 2 = 1 := by omega
        rcases h_mod with h0 | h1
        · rcases Nat.dvd_of_mod_eq_zero h0 with ⟨k_odd, hk⟩
          have : 2 * (p^i * k_odd) = 8 * n - (2 * r + 1) := by
            calc 2 * (p^i * k_odd) = (p^i) * (2 * k_odd) := by ring
            _ = (p^i) * c := by rw [← hk]
            _ = 8 * n - (2 * r + 1) := hc.symm
          omega
        · exact h1
      let m := c / 2
      have h_c_eq : c = 2 * m + 1 := by omega
      have hc3 : 8 * n = (2 * m + 1) * p^i + 2 * r + 1 := by
        rw [← h_c_eq]
        exact hc2
      exact omega_test n r m (p^i) q rem h_pow_pos h_rem h_eq1 hc3 h_gt
  · have h_Iv : Iv = 0 := by simp [Iv, h_v]
    rw [h_Iv]
    simp only [add_zero]
    by_cases h_k : i ≤ k
    · have h_Ik : Ik = 1 := by simp [Ik, h_k]
      rw [h_Ik]
      omega
    · have h_Ik : Ik = 0 := by simp [Ik, h_k]
      rw [h_Ik]
      simp only [add_zero]
      omega

lemma sum_indicator_eq_self_base (v : ℕ) :
    (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v then 1 else 0) = v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have : (if v + 1 ≤ v + 1 then 1 else 0) = 1 := by simp
    rw [this]
    have h_eq : (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v + 1 then 1 else 0) =
                (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_Ico] at hx
      have h1 : x ≤ v + 1 := by omega
      have h2 : x ≤ v := by omega
      rw [if_pos h1, if_pos h2]
    rw [h_eq, ih]

lemma sum_indicator_eq_self (v b : ℕ) (h : v < b) :
    (Finset.Ico 1 b).sum (fun i => if i ≤ v then 1 else 0) = v := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb : v < b
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ b)]
      have : (if b ≤ v then 1 else 0) = 0 := by simp [hb]
      rw [this, add_zero]
      exact ih hb
    · have : b = v := by omega
      subst this
      exact sum_indicator_eq_self_base b


theorem claim1_case1 (r n : ℕ) (h_lt : 8 * n < 2 * r + 1) :
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * (8 * r + 3).factorial := by
  have h1 : 0 < 2 * r + 1 - 8 * n := by omega
  have h2 : 2 * r + 1 - 8 * n ≤ 8 * r + 3 := by omega
  have h_dvd := Nat.dvd_factorial h1 h2
  have h_dvd_int : ((2 * r + 1 - 8 * n : ℕ) : ℤ) ∣ ((8 * r + 3).factorial : ℤ) := by exact_mod_cast h_dvd
  have h_eq : ((8 * n : ℤ) - (2 * r + 1 : ℤ)) = - ((2 * r + 1 - 8 * n : ℕ) : ℤ) := by omega
  rw [h_eq]
  have h_neg_dvd : -((2 * r + 1 - 8 * n : ℕ) : ℤ) ∣ ((8 * r + 3).factorial : ℤ) := by
    exact neg_dvd.mpr h_dvd_int
  exact dvd_mul_of_dvd_right h_neg_dvd _

theorem claim1_case2 (r n : ℕ) (h_ge : 8 * n ≥ 2 * r + 1) :
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * (8 * r + 3).factorial := by
  let d_nat := 8 * n - (2 * r + 1)
  let H_nat := (8 * r + 3).factorial
  let Y := (4 * n).factorial * (3 * n).factorial * (2 * n).factorial
  let X := (8 * n).factorial * n.factorial
  have h_dvd : d_nat * Y ∣ X * H_nat := by
    have h_ne1 : d_nat * Y ≠ 0 := by
      have : d_nat ≠ 0 := by omega
      have : Y ≠ 0 := by positivity
      positivity
    have h_ne2 : X * H_nat ≠ 0 := by
      have : X ≠ 0 := by positivity
      have : H_nat ≠ 0 := by positivity
      positivity
    rw [← Nat.factorization_le_iff_dvd h_ne1 h_ne2]
    rw [Finsupp.le_def]
    intro p
    by_cases pp : p.Prime
    · have : Fact p.Prime := ⟨pp⟩
      rw [Nat.factorization_def _ pp, Nat.factorization_def _ pp]
      have h1 : padicValNat p (d_nat * Y) = padicValNat p d_nat + padicValNat p Y := padicValNat.mul (by omega) (by positivity)
      have h2 : padicValNat p (X * H_nat) = padicValNat p X + padicValNat p H_nat := padicValNat.mul (by positivity) (by positivity)
      rw [h1, h2]
      let b := 8 * n + 8 * r + 4
      have hb4 : log p (4 * n) < b := by
        have := Nat.log_le_self p (4 * n)
        omega
      have hb3 : log p (3 * n) < b := by
        have := Nat.log_le_self p (3 * n)
        omega
      have hb2 : log p (2 * n) < b := by
        have := Nat.log_le_self p (2 * n)
        omega
      have hb8 : log p (8 * n) < b := by
        have := Nat.log_le_self p (8 * n)
        omega
      have hbn : log p n < b := by
        have := Nat.log_le_self p n
        omega
      have h_v_lt : padicValNat p d_nat < b := by
        have h_pow_le : p ^ (padicValNat p d_nat) ≤ d_nat := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
        have h_v_lt_pow : padicValNat p d_nat < p ^ (padicValNat p d_nat) := Nat.lt_pow_self pp.one_lt
        omega
      have h_k_lt : padicValNat p H_nat < b := by
        have h_k_le : padicValNat p H_nat ≤ 8 * r + 3 := padicValNat_factorial_le p (8 * r + 3)
        omega
      have hY_val : padicValNat p Y = padicValNat p (4 * n).factorial + padicValNat p (3 * n).factorial + padicValNat p (2 * n).factorial := by
        change padicValNat p ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) = _
        have h1_mul : padicValNat p ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) =
                  padicValNat p ((4 * n).factorial * (3 * n).factorial) + padicValNat p (2 * n).factorial := by
          exact padicValNat.mul (by positivity) (by positivity)
        have h2_mul : padicValNat p ((4 * n).factorial * (3 * n).factorial) =
                  padicValNat p (4 * n).factorial + padicValNat p (3 * n).factorial := by
          exact padicValNat.mul (by positivity) (by positivity)
        rw [h1_mul, h2_mul]
      have hX_val : padicValNat p X = padicValNat p (8 * n).factorial + padicValNat p n.factorial := by
        exact padicValNat.mul (by positivity) (by positivity)
      rw [hY_val, hX_val]
      rw [padicValNat_factorial hb4, padicValNat_factorial hb3, padicValNat_factorial hb2, padicValNat_factorial hb8, padicValNat_factorial hbn]
      rw [← sum_indicator_eq_self (padicValNat p d_nat) b h_v_lt, ← sum_indicator_eq_self (padicValNat p H_nat) b h_k_lt]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi_pos : i ≥ 1 := by omega
      have h_term := term_by_term n r p i (padicValNat p d_nat) (padicValNat p H_nat) rfl rfl hi_pos h_ge
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime _ pp, Nat.factorization_eq_zero_of_not_prime _ pp]
  have h_eq : (X * H_nat : ℤ) = (a n : ℤ) * H_nat * Y := by
    calc (X * H_nat : ℤ) = (X : ℤ) * (H_nat : ℤ) := by push_cast; rfl
    _ = ((a n : ℤ) * Y) * (H_nat : ℤ) := by rw [← a_mul_Y_eq_X n]
    _ = (a n : ℤ) * H_nat * Y := by ring
  have h_dvd_int : ((d_nat * Y : ℕ) : ℤ) ∣ ((X * H_nat : ℕ) : ℤ) := by exact_mod_cast h_dvd
  have h_dvd_int_rew : ((d_nat : ℤ) * (Y : ℤ)) ∣ ((X : ℤ) * (H_nat : ℤ)) := by exact_mod_cast h_dvd_int
  rw [h_eq] at h_dvd_int_rew
  have hY_pos : (Y : ℤ) ≠ 0 := by positivity
  rw [mul_dvd_mul_iff_right hY_pos] at h_dvd_int_rew
  have h_final := h_dvd_int_rew
  have h_eq_d : ((8 * n : ℤ) - (2 * r + 1 : ℤ)) = (d_nat : ℤ) := by omega
  rw [h_eq_d]
  exact h_final

theorem claim1 (r : ℕ) : ∃ H : ℤ, H > 0 ∧ ∀ n : ℕ,
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * H := by
  use (8 * r + 3).factorial
  refine ⟨by positivity, fun n => ?_⟩
  have h_cases : 8 * n < 2 * r + 1 ∨ 8 * n ≥ 2 * r + 1 := by omega
  rcases h_cases with h_lt | h_ge
  · exact claim1_case1 r n h_lt
  · exact claim1_case2 r n h_ge

theorem oeis_211420_conjecture_1 : ∀ r : ℕ, ∃ K : ℤ, K > 0 ∧ ∀ n : ℕ,
    denominator_product n r ∣ (a n : ℤ) * K := by
  intro r
  induction r with
  | zero =>
    use 1
    simp [denominator_product]
  | succ r ih =>
    rcases ih with ⟨K, hK_pos, hK_dvd⟩
    obtain ⟨H, hH_pos, hH_dvd⟩ := claim1 r
    obtain ⟨C, hC_pos, hC_dvd⟩ := claim2 r
    use K * H * C
    refine ⟨by positivity, fun n => ?_⟩
    rw [denominator_product_succ]
    have hA : denominator_product n r ∣ (a n : ℤ) * K * H := dvd_mul_of_dvd_left (hK_dvd n) H
    have hB : ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * K * H := by
      rw [mul_assoc, mul_comm K H, ← mul_assoc]
      exact dvd_mul_of_dvd_left (hH_dvd n) K
    have hAB := gcd_dvd_mul_of_dvd_of_dvd (denominator_product n r) ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ((a n : ℤ) * K * H) hA hB
    have hGCD : (Int.gcd (denominator_product n r) ((8 * n : ℤ) - (2 * r + 1 : ℤ)) : ℤ) ∣ C := hC_dvd n
    have hY_mul : (a n : ℤ) * K * H * (Int.gcd (denominator_product n r) ((8 * n : ℤ) - (2 * r + 1 : ℤ)) : ℤ) ∣ (a n : ℤ) * K * H * C := mul_dvd_mul_left _ hGCD
    have h_final := dvd_trans hAB hY_mul
    have h_rw : (a n : ℤ) * K * H * C = (a n : ℤ) * (K * H * C) := by ring
    rw [← h_rw]
    exact h_final


