import FormalConjectures.Util.ProblemImports

open Nat Finset

def A335624_rep (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x^2 + y^2 + z^2 + w^2 = n ∧ Nat.sqrt (x + 3 * y + 4 * z) ^ 2 = x + 3 * y + 4 * z

def A335624 (n : ℕ) : ℕ :=
  -- The variables x, y, z, w are bounded by sqrt(n), since they are non-negative.
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      -- The term x + 3*y + 4*z must be a perfect square.
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

lemma sixteen_pow_mul_eight (k : ℕ) (m : ℕ) : 2 ^ (4 * k + 3) * m = 16 ^ k * (8 * m) := by
  rw [Nat.pow_add, Nat.pow_mul]
  ring

lemma not_rep_8 : ¬ A335624_rep 8 := by
  intro ⟨x, y, z, w, h1, h2⟩
  have hx : x < 3 := by nlinarith
  have hy : y < 3 := by nlinarith
  have hz : z < 3 := by nlinarith
  have hw : w < 3 := by nlinarith
  have hs : Nat.sqrt (x + 3 * y + 4 * z) < 5 := by
    rw [Nat.sqrt_lt]
    omega
  generalize hs_eq : Nat.sqrt (x + 3 * y + 4 * z) = s at h2 hs
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> interval_cases s <;> revert h1 h2 <;> omega

lemma not_rep_24 : ¬ A335624_rep 24 := by
  intro ⟨x, y, z, w, h1, h2⟩
  have hx : x < 5 := by nlinarith
  have hy : y < 5 := by nlinarith
  have hz : z < 5 := by nlinarith
  have hw : w < 5 := by nlinarith
  have hs : Nat.sqrt (x + 3 * y + 4 * z) < 7 := by
    rw [Nat.sqrt_lt]
    omega
  generalize hs_eq : Nat.sqrt (x + 3 * y + 4 * z) = s at h2 hs
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> interval_cases s <;> revert h1 h2 <;> omega

lemma not_rep_344 : ¬ A335624_rep 344 := by
  intro ⟨x, y, z, w, h1, h2⟩
  have h_evens : x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 ∧ w % 2 = 0 := by
    apply evens_of_sum_sq_mod_eight x y z w
    omega
  rcases h_evens with ⟨ex, ey, ez, ew⟩
  obtain ⟨x1, rfl⟩ : 2 ∣ x := even_iff_two_dvd.mp (by omega)
  obtain ⟨y1, rfl⟩ : 2 ∣ y := even_iff_two_dvd.mp (by omega)
  obtain ⟨z1, rfl⟩ : 2 ∣ z := even_iff_two_dvd.mp (by omega)
  obtain ⟨w1, rfl⟩ : 2 ∣ w := even_iff_two_dvd.mp (by omega)
  have h_sum1 : x1^2 + y1^2 + z1^2 + w1^2 = 86 := by omega
  have h_sq1 : (2 * x1 + 6 * y1 + 8 * z1).sqrt ^ 2 = 2 * x1 + 6 * y1 + 8 * z1 := h2
  have hx1 : x1 < 10 := by nlinarith
  have hy1 : y1 < 10 := by nlinarith
  have hz1 : z1 < 10 := by nlinarith
  have hw1 : w1 < 10 := by nlinarith
  have hs1 : Nat.sqrt (2 * x1 + 6 * y1 + 8 * z1) < 13 := by
    rw [Nat.sqrt_lt]
    omega
  generalize hs1_eq : Nat.sqrt (2 * x1 + 6 * y1 + 8 * z1) = s1 at h_sq1 hs1
  -- Now we do parity case analysis on x1, y1, z1, w1
  have h_px : x1 % 2 = 0 ∨ x1 % 2 = 1 := by omega
  have h_py : y1 % 2 = 0 ∨ y1 % 2 = 1 := by omega
  have h_pz : z1 % 2 = 0 ∨ z1 % 2 = 1 := by omega
  have h_pw : w1 % 2 = 0 ∨ w1 % 2 = 1 := by omega
  rcases h_px with px | px <;> rcases h_py with py | py <;> rcases h_pz with pz | pz <;> rcases h_pw with pw | pw
  -- 16 cases, most are trivial by omega, only {even, even, odd, odd} and {odd, odd, even, even} remain
  all_goals
    try (exfalso; omega)
  -- wait, for the remaining ones, we can obtain x2, y2, z2, w2
  · obtain ⟨x2, hx2⟩ : 2 ∣ x1 := even_iff_two_dvd.mp (by omega)
    obtain ⟨y2, hy2⟩ : 2 ∣ y1 := even_iff_two_dvd.mp (by omega)
    obtain ⟨z2, hz2⟩ : 2 ∣ z1 := even_iff_two_dvd.mp (by omega)
    obtain ⟨w2, hw2⟩ : 2 ∣ w1 := even_iff_two_dvd.mp (by omega)
    subst hx2 hy2 hz2 hw2; exfalso; omega
  · obtain ⟨x2, hx2⟩ : 2 ∣ x1 := even_iff_two_dvd.mp (by omega)
    obtain ⟨y2, hy2⟩ : 2 ∣ y1 := even_iff_two_dvd.mp (by omega)
    have hz1_odd : 2 ∣ (z1 - 1) := even_iff_two_dvd.mp (by omega)
    have hw1_odd : 2 ∣ (w1 - 1) := even_iff_two_dvd.mp (by omega)
    rcases hz1_odd with ⟨z2, rfl⟩
    rcases hw1_odd with ⟨w2, rfl⟩
    subst hx2 hy2
    have h_bound : x2 < 5 ∧ y2 < 5 ∧ z2 < 5 ∧ w2 < 5 := by omega
    interval_cases x2 <;> interval_cases y2 <;> interval_cases z2 <;> interval_cases w2 <;> interval_cases s1 <;> revert h_sum1 h_sq1 <;> omega
  · have hx1_odd : 2 ∣ (x1 - 1) := even_iff_two_dvd.mp (by omega)
    have hy1_odd : 2 ∣ (y1 - 1) := even_iff_two_dvd.mp (by omega)
    obtain ⟨z2, hz2⟩ : 2 ∣ z1 := even_iff_two_dvd.mp (by omega)
    obtain ⟨w2, hw2⟩ : 2 ∣ w1 := even_iff_two_dvd.mp (by omega)
    rcases hx1_odd with ⟨x2, rfl⟩
    rcases hy1_odd with ⟨y2, rfl⟩
    subst hz2 hw2
    have h_bound : x2 < 5 ∧ y2 < 5 ∧ z2 < 5 ∧ w2 < 5 := by omega
    interval_cases x2 <;> interval_cases y2 <;> interval_cases z2 <;> interval_cases w2 <;> interval_cases s1 <;> revert h_sum1 h_sq1 <;> omega





























