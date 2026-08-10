import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000

open Nat

lemma pow_six_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) : (q : ZMod 252) ^ 6 = 1 := by
  set r := q % 252
  have hr_lt : r < 252 := Nat.mod_lt q (by decide)
  have q_mod : q % 252 = r := rfl
  interval_cases r
  · exfalso
    have h_gcd_dvd : 252 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 252 ∣ 252 := by decide
      have h_g_dvd_r : 252 ∣ 0 := by decide
      have h_g_dvd_q : 252 ∣ q := by
        have : q = 252 * (q / 252) + 0 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 252 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 1 := by
      have : q % 252 = 1 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 2 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 2 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 3 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 3 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 4 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 4 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 5 := by
      have : q % 252 = 5 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 6 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 6 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 7 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 7 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 8 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 8 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 9 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 9 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 10 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 10 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 11 := by
      have : q % 252 = 11 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 12 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 12 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 13 := by
      have : q % 252 = 13 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 14 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 14 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 15 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 15 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 16 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 16 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 17 := by
      have : q % 252 = 17 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 18 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 18 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 19 := by
      have : q % 252 = 19 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 20 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 20 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 21 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 21 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 22 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 22 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 23 := by
      have : q % 252 = 23 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 24 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 24 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 25 := by
      have : q % 252 = 25 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 26 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 26 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 27 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 27 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 28 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 28 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 29 := by
      have : q % 252 = 29 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 30 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 30 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 31 := by
      have : q % 252 = 31 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 32 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 32 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 33 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 33 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 34 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 34 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 35 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 35 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 36 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 36 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 37 := by
      have : q % 252 = 37 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 38 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 38 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 39 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 39 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 40 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 40 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 41 := by
      have : q % 252 = 41 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 42 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 42 ∣ 252 := by decide
      have h_g_dvd_r : 42 ∣ 42 := by decide
      have h_g_dvd_q : 42 ∣ q := by
        have : q = 252 * (q / 252) + 42 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 42 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 43 := by
      have : q % 252 = 43 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 44 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 44 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 45 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 45 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 46 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 46 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 47 := by
      have : q % 252 = 47 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 48 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 48 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 49 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 49 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 50 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 50 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 51 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 51 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 52 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 52 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 53 := by
      have : q % 252 = 53 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 54 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 54 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 55 := by
      have : q % 252 = 55 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 56 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 56 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 57 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 57 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 58 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 58 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 59 := by
      have : q % 252 = 59 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 60 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 60 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 61 := by
      have : q % 252 = 61 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 62 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 62 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 63 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 63 ∣ 252 := by decide
      have h_g_dvd_r : 63 ∣ 63 := by decide
      have h_g_dvd_q : 63 ∣ q := by
        have : q = 252 * (q / 252) + 63 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 63 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 64 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 64 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 65 := by
      have : q % 252 = 65 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 66 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 66 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 67 := by
      have : q % 252 = 67 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 68 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 68 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 69 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 69 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 70 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 70 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 71 := by
      have : q % 252 = 71 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 72 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 72 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 73 := by
      have : q % 252 = 73 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 74 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 74 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 75 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 75 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 76 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 76 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 77 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 77 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 78 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 78 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 79 := by
      have : q % 252 = 79 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 80 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 80 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 81 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 81 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 82 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 82 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 83 := by
      have : q % 252 = 83 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 84 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 84 ∣ 252 := by decide
      have h_g_dvd_r : 84 ∣ 84 := by decide
      have h_g_dvd_q : 84 ∣ q := by
        have : q = 252 * (q / 252) + 84 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 84 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 85 := by
      have : q % 252 = 85 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 86 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 86 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 87 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 87 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 88 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 88 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 89 := by
      have : q % 252 = 89 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 90 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 90 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 91 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 91 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 92 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 92 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 93 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 93 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 94 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 94 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 95 := by
      have : q % 252 = 95 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 96 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 96 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 97 := by
      have : q % 252 = 97 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 98 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 98 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 99 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 99 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 100 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 100 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 101 := by
      have : q % 252 = 101 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 102 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 102 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 103 := by
      have : q % 252 = 103 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 104 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 104 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 105 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 105 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 106 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 106 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 107 := by
      have : q % 252 = 107 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 108 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 108 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 109 := by
      have : q % 252 = 109 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 110 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 110 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 111 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 111 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 112 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 112 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 113 := by
      have : q % 252 = 113 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 114 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 114 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 115 := by
      have : q % 252 = 115 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 116 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 116 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 117 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 117 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 118 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 118 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 119 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 119 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 120 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 120 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 121 := by
      have : q % 252 = 121 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 122 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 122 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 123 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 123 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 124 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 124 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 125 := by
      have : q % 252 = 125 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 126 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 126 ∣ 252 := by decide
      have h_g_dvd_r : 126 ∣ 126 := by decide
      have h_g_dvd_q : 126 ∣ q := by
        have : q = 252 * (q / 252) + 126 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 126 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 127 := by
      have : q % 252 = 127 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 128 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 128 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 129 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 129 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 130 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 130 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 131 := by
      have : q % 252 = 131 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 132 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 132 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 133 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 133 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 134 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 134 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 135 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 135 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 136 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 136 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 137 := by
      have : q % 252 = 137 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 138 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 138 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 139 := by
      have : q % 252 = 139 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 140 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 140 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 141 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 141 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 142 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 142 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 143 := by
      have : q % 252 = 143 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 144 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 144 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 145 := by
      have : q % 252 = 145 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 146 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 146 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 147 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 147 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 148 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 148 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 149 := by
      have : q % 252 = 149 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 150 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 150 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 151 := by
      have : q % 252 = 151 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 152 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 152 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 153 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 153 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 154 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 154 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 155 := by
      have : q % 252 = 155 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 156 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 156 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 157 := by
      have : q % 252 = 157 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 158 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 158 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 159 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 159 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 160 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 160 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 161 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 161 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 162 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 162 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 163 := by
      have : q % 252 = 163 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 164 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 164 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 165 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 165 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 166 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 166 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 167 := by
      have : q % 252 = 167 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 84 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 84 ∣ 252 := by decide
      have h_g_dvd_r : 84 ∣ 168 := by decide
      have h_g_dvd_q : 84 ∣ q := by
        have : q = 252 * (q / 252) + 168 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 84 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 169 := by
      have : q % 252 = 169 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 170 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 170 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 171 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 171 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 172 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 172 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 173 := by
      have : q % 252 = 173 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 174 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 174 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 175 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 175 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 176 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 176 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 177 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 177 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 178 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 178 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 179 := by
      have : q % 252 = 179 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 180 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 180 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 181 := by
      have : q % 252 = 181 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 182 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 182 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 183 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 183 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 184 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 184 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 185 := by
      have : q % 252 = 185 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 186 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 186 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 187 := by
      have : q % 252 = 187 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 188 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 188 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 63 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 63 ∣ 252 := by decide
      have h_g_dvd_r : 63 ∣ 189 := by decide
      have h_g_dvd_q : 63 ∣ q := by
        have : q = 252 * (q / 252) + 189 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 63 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 190 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 190 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 191 := by
      have : q % 252 = 191 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 192 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 192 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 193 := by
      have : q % 252 = 193 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 194 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 194 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 195 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 195 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 196 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 196 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 197 := by
      have : q % 252 = 197 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 198 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 198 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 199 := by
      have : q % 252 = 199 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 200 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 200 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 201 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 201 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 202 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 202 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 203 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 203 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 204 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 204 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 205 := by
      have : q % 252 = 205 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 206 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 206 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 207 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 207 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 208 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 208 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 209 := by
      have : q % 252 = 209 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 42 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 42 ∣ 252 := by decide
      have h_g_dvd_r : 42 ∣ 210 := by decide
      have h_g_dvd_q : 42 ∣ q := by
        have : q = 252 * (q / 252) + 210 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 42 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 211 := by
      have : q % 252 = 211 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 212 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 212 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 213 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 213 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 214 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 214 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 215 := by
      have : q % 252 = 215 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 216 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 216 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 217 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 217 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 218 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 218 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 219 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 219 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 220 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 220 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 221 := by
      have : q % 252 = 221 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 222 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 222 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 223 := by
      have : q % 252 = 223 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 224 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 224 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 225 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 225 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 226 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 226 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 227 := by
      have : q % 252 = 227 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 228 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 228 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 229 := by
      have : q % 252 = 229 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 230 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 230 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 231 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 231 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 232 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 232 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 233 := by
      have : q % 252 = 233 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 234 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 234 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 235 := by
      have : q % 252 = 235 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 236 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 236 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 237 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 237 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 238 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 238 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 239 := by
      have : q % 252 = 239 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 240 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 240 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 241 := by
      have : q % 252 = 241 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 242 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 242 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 243 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 243 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 244 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 244 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 245 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 245 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 246 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 246 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 247 := by
      have : q % 252 = 247 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 248 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 248 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 249 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 249 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 250 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 250 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 251 := by
      have : q % 252 = 251 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
