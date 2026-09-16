import Submission.Test
open Nat Int Finset

lemma gcd_mul_add (a b X : ℤ) : Int.gcd (b * a + X) a = Int.gcd X a := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · have h1 : ((Int.gcd (b * a + X) a) : ℤ) ∣ b * a + X := Int.gcd_dvd_left _ _
      have h2 : ((Int.gcd (b * a + X) a) : ℤ) ∣ a := Int.gcd_dvd_right _ _
      have h3 : ((Int.gcd (b * a + X) a) : ℤ) ∣ b * a := dvd_mul_of_dvd_right h2 b
      have h4 := dvd_sub h1 h3
      simp only [add_sub_cancel_left] at h4
      exact h4
    · exact Int.gcd_dvd_right _ _
  · apply Int.dvd_gcd
    · have h1 : ((Int.gcd X a) : ℤ) ∣ X := Int.gcd_dvd_left _ _
      have h2 : ((Int.gcd X a) : ℤ) ∣ a := Int.gcd_dvd_right _ _
      have h3 : ((Int.gcd X a) : ℤ) ∣ b * a := dvd_mul_of_dvd_right h2 b
      exact dvd_add h3 h1
    · exact Int.gcd_dvd_right _ _

lemma gcd_sign (d a : ℤ) (c : ℤ) (hc : c = 1 ∨ c = -1) : Int.gcd (c * d) a = Int.gcd d a := by
  rcases hc with rfl | rfl
  · simp only [one_mul]
  · have eq : -1 * d = -d := by ring
    rw [eq]
    apply Nat.dvd_antisymm
    · apply Int.dvd_gcd
      · have h1 : ((Int.gcd (-d) a) : ℤ) ∣ -d := Int.gcd_dvd_left _ _
        exact dvd_neg.mp h1
      · exact Int.gcd_dvd_right _ _
    · apply Int.dvd_gcd
      · have h1 : ((Int.gcd d a) : ℤ) ∣ d := Int.gcd_dvd_left _ _
        exact dvd_neg.mpr h1
      · exact Int.gcd_dvd_right _ _

lemma A334958_eq (n : ℕ) : Int.gcd (F_aux (n + 1)) (F_aux n) = Int.gcd ((n).factorial) (F_aux n) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h_rec := F_aux_succ_succ n
    rw [h_rec]
    have h_gcd : Int.gcd ((n + 2 : ℤ) * F_aux (n + 1) + (if (n + 2) % 2 = 0 then 1 else -1) * ((n + 1).factorial : ℤ)) (F_aux (n + 1)) = Int.gcd ((if (n + 2) % 2 = 0 then 1 else -1) * ((n + 1).factorial : ℤ)) (F_aux (n + 1)) := by
      apply gcd_mul_add
    rw [h_gcd]
    have hc : (if (n + 2) % 2 = 0 then (1 : ℤ) else -1) = 1 ∨ (if (n + 2) % 2 = 0 then (1 : ℤ) else -1) = -1 := by
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    rw [gcd_sign _ _ _ hc]
