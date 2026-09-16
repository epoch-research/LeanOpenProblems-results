import Mathlib
open Int

lemma d_dvd_b (d a b : ℤ) (h1 : d ∣ a * b) (h2 : d ∣ b * b) (hc : Int.gcd a b = 1) : d ∣ b := by
  have ⟨x, y, hxy⟩ : ∃ x y : ℤ, a * x + b * y = 1 := by
    use Int.gcdA a b, Int.gcdB a b
    have h := Int.gcd_eq_gcd_ab a b
    rw [hc] at h
    exact h.symm
  have eq : b = (a * b) * x + (b * b) * y := by
    calc
      b = b * 1 := by ring
      _ = b * (a * x + b * y) := by rw [hxy]
      _ = (a * b) * x + (b * b) * y := by ring
  have res := dvd_add (dvd_mul_of_dvd_left h1 x) (dvd_mul_of_dvd_left h2 y)
  rwa [← eq] at res

lemma d_dvd_a_of_dvd_ab_ac (d a b c : ℤ) (h1 : d ∣ a * b) (h2 : d ∣ a * c) (hc : Int.gcd b c = 1) : d ∣ a := by
  have ⟨x, y, hxy⟩ : ∃ x y : ℤ, b * x + c * y = 1 := by
    use Int.gcdA b c, Int.gcdB b c
    have h := Int.gcd_eq_gcd_ab b c
    rw [hc] at h
    exact h.symm
  have eq : a = (a * b) * x + (a * c) * y := by
    calc
      a = a * 1 := by ring
      _ = a * (b * x + c * y) := by rw [hxy]
      _ = (a * b) * x + (a * c) * y := by ring
  have res := dvd_add (dvd_mul_of_dvd_left h1 x) (dvd_mul_of_dvd_left h2 y)
  rwa [← eq] at res

lemma gcd_ac_abc (a b c : ℤ) (h : Int.gcd b c = 1) : Int.gcd (a * c) (a * b + c) = Int.gcd a c := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · have h1 : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ a * c := Int.gcd_dvd_left _ _
      have h2 : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ a * b + c := Int.gcd_dvd_right _ _
      have h3 : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ (a * b + c) * c := dvd_mul_of_dvd_left h2 c
      have h3' : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ c * (a * b + c) := by rwa [mul_comm] at h3
      have h4 : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ (a * c) * b := dvd_mul_of_dvd_left h1 b
      have h4' : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ b * (a * c) := by rwa [mul_comm] at h4
      have h5 := dvd_sub h3' h4'
      have heq : c * (a * b + c) - b * (a * c) = c * c := by ring
      rw [heq] at h5
      have hbc : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ b * c := by
        have htmp : b * c * a = (a * c) * b := by ring
        have h4_alt : ((Int.gcd (a * c) (a * b + c)) : ℤ) ∣ b * c * a := by rwa [htmp]
        exact dvd_mul_of_dvd_left h1 b
      -- wait, d | b * c is not true, d | b * (a * c).
      -- we want to use d_dvd_b with d, b, c. We need d | b * c.
      -- actually we don't need d_dvd_b!
      -- we know d | c * (a*b+c) and d | c * c. But wait, d|c*c and d|a*c.
      -- Yes! d | c * c and d | c * a => d | c * gcd(a, c) ?
      -- No, we just need d | a and d | c!
      -- We have h5: d | c * c.
      -- And we have h1: d | a * c.
      -- Wait, if d | c * c and d | a * c, it only gives d | c * gcd(a, c). It DOES NOT give d | c!
      sorry
    · sorry
  · apply Int.dvd_gcd
    · have h1 : ((Int.gcd a c) : ℤ) ∣ a := Int.gcd_dvd_left _ _
      have h2 : ((Int.gcd a c) : ℤ) ∣ c := Int.gcd_dvd_right _ _
      exact dvd_mul_of_dvd_left h1 c
    · have h1 : ((Int.gcd a c) : ℤ) ∣ a := Int.gcd_dvd_left _ _
      have h2 : ((Int.gcd a c) : ℤ) ∣ c := Int.gcd_dvd_right _ _
      have h3 : ((Int.gcd a c) : ℤ) ∣ a * b := dvd_mul_of_dvd_left h1 b
      exact dvd_add h3 h2
