import FormalConjectures.Util.ProblemImports
open Nat

lemma rat_int_range_mul {x y : ℚ}
    (hx : x ∈ Set.range (Int.cast : ℤ → ℚ))
    (hy : y ∈ Set.range (Int.cast : ℤ → ℚ)) : x*y ∈ Set.range (Int.cast : ℤ → ℚ) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a*b, by norm_num⟩


lemma quotient_identity (n : ℕ) (hn : 3 ≤ n) :
    ((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ)
      = ((128*n-152 : ℕ) : ℚ) * (Nat.choose (4*n-7) (2*n-4) : ℚ)
        - ((4*n-1 : ℕ) : ℚ) * (Nat.choose (4*n-2) (2*n-2) : ℚ) := by
  have h1 : 2*n-4 ≤ 4*n-6 := by omega
  have h2 : 2*n-4 ≤ 4*n-7 := by omega
  have h3 : 2*n-2 ≤ 4*n-2 := by omega
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Nat.cast_choose (K:=ℚ) h1, Nat.cast_choose (K:=ℚ) h2, Nat.cast_choose (K:=ℚ) h3]
  have hnq : (n:ℚ) ≠ 0 := by positivity
  field_simp [hnq]
  rw [show 4*n-7-(2*n-4) = 2*n-3 by omega]
  rw [show 4*n-2-(2*n-2) = 2*n by omega]
  rw [show 4*n-6-(2*n-4) = 2*n-2 by omega]
  have hf46 : (4*n-6)! = (4*n-6) * (4*n-7)! := by
    rw [show 4*n-6 = (4*n-7)+1 by omega, Nat.factorial_succ]
  have hf42 : (4*n-2)! = (4*n-2)*(4*n-3)*(4*n-4)*(4*n-5)*(4*n-6)*(4*n-7)! := by
    rw [show 4*n-2 = (4*n-3)+1 by omega, Nat.factorial_succ]
    rw [show 4*n-3 = (4*n-4)+1 by omega, Nat.factorial_succ]
    rw [show 4*n-4 = (4*n-5)+1 by omega, Nat.factorial_succ]
    rw [show 4*n-5 = (4*n-6)+1 by omega, Nat.factorial_succ]
    rw [show 4*n-6 = (4*n-7)+1 by omega, Nat.factorial_succ]
    try ring_nf
  have hf2n : (2*n)! = (2*n)*(2*n-1)*(2*n-2)! := by
    rw [show 2*n = (2*n-1)+1 by omega, Nat.factorial_succ]
    rw [show 2*n-1 = (2*n-2)+1 by omega, Nat.factorial_succ]
    rw [show 2*n-2+1 = 2*n-1 by omega]
    rw [show 2*n-1+1 = 2*n by omega]
    try ring_nf
  have hf2n2 : (2*n-2)! = (2*n-2)*(2*n-3)! := by
    rw [show 2*n-2 = (2*n-3)+1 by omega, Nat.factorial_succ]
  have hf2n3 : (2*n-3)! = (2*n-3) * (2*n-4)! := by
    rw [show 2*n-3 = (2*n-4)+1 by omega, Nat.factorial_succ]
  rw [hf46, hf42, hf2n, hf2n2, hf2n3]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have c2n5 : ((2*n-5 : ℕ) : ℚ) = 2*(n:ℚ) - 5 := by
    rw [Nat.cast_sub (by omega : 5 ≤ 2*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c4n6 : ((4*n-6 : ℕ) : ℚ) = 4*(n:ℚ) - 6 := by
    rw [Nat.cast_sub (by omega : 6 ≤ 4*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c2n3 : ((2*n-3 : ℕ) : ℚ) = 2*(n:ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 2*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c2n4 : ((2*n-4 : ℕ) : ℚ) = 2*(n:ℚ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ 2*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c2n2 : ((2*n-2 : ℕ) : ℚ) = 2*(n:ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c2n1 : ((2*n-1 : ℕ) : ℚ) = 2*(n:ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c4n1 : ((4*n-1 : ℕ) : ℚ) = 4*(n:ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c4n2 : ((4*n-2 : ℕ) : ℚ) = 4*(n:ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c4n3 : ((4*n-3 : ℕ) : ℚ) = 4*(n:ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 4*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c4n4 : ((4*n-4 : ℕ) : ℚ) = 4*(n:ℚ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ 4*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c4n5 : ((4*n-5 : ℕ) : ℚ) = 4*(n:ℚ) - 5 := by
    rw [Nat.cast_sub (by omega : 5 ≤ 4*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  have c128 : ((128*n-152 : ℕ) : ℚ) = 128*(n:ℚ) - 152 := by
    rw [Nat.cast_sub (by omega : 152 ≤ 128*n), Nat.cast_mul, Nat.cast_ofNat]
    try ring
  rw [c2n5, c4n6, c2n3, c2n2, c2n1, c4n1, c4n2, c4n3, c4n4, c4n5, c128]
  ring_nf

lemma quotient_in_int_range (n : ℕ) (hn : 3 ≤ n) :
    (((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ))
      ∈ Set.range (Int.cast : ℤ → ℚ) := by
  rw [quotient_identity n hn]
  refine ⟨((128*n-152 : ℕ) : ℤ) * ((Nat.choose (4*n-7) (2*n-4) : ℕ) : ℤ)
      - ((4*n-1 : ℕ) : ℤ) * ((Nat.choose (4*n-2) (2*n-2) : ℕ) : ℤ), ?_⟩
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]


lemma quotient_div3_in_int_range_of_mod1 (n : ℕ) (hn : 3 ≤ n) (hmod : n % 3 = 1) :
    ((((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ)) / 3)
      ∈ Set.range (Int.cast : ℤ → ℚ) := by
  rw [quotient_identity n hn]
  have hA : 3 ∣ 128*n - 152 := by omega
  have hB : 3 ∣ 4*n - 1 := by omega
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  refine ⟨(a:ℤ) * ((Nat.choose (4*n-7) (2*n-4) : ℕ) : ℤ)
      - (b:ℤ) * ((Nat.choose (4*n-2) (2*n-2) : ℕ) : ℤ), ?_⟩
  rw [ha, hb]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  ring


lemma product_div3_in_int_range_of_not_mod1 (n : ℕ) (hn : 3 ≤ n) (hmod : n % 3 ≠ 1) :
    (((((2*n-3)*(2*n-1) : ℕ) : ℚ) / 3) ∈ Set.range (Int.cast : ℤ → ℚ)) := by
  have hm : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hP : 3 ∣ (2*n-3)*(2*n-1) := by
    interval_cases h0 : n % 3
    · exact dvd_mul_of_dvd_left (by omega : 3 ∣ 2*n-3) _
    · contradiction
    · exact dvd_mul_of_dvd_right (by omega : 3 ∣ 2*n-1) _
  rcases hP with ⟨k, hk⟩
  refine ⟨(k:ℤ), ?_⟩
  rw [hk]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast]
  ring

lemma J_factor_in_int_range (n : ℕ) (hn : 3 ≤ n) :
    (((((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ))
        * (((2*n-3)*(2*n-1) : ℕ) : ℚ)) / 3)
      ∈ Set.range (Int.cast : ℤ → ℚ) := by
  by_cases hmod : n % 3 = 1
  · have hx : ((((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ)) / 3)
        ∈ Set.range (Int.cast : ℤ → ℚ) := quotient_div3_in_int_range_of_mod1 n hn hmod
    have hp : ((((2*n-3)*(2*n-1) : ℕ) : ℚ)) ∈ Set.range (Int.cast : ℤ → ℚ) := by
      exact ⟨(((2*n-3)*(2*n-1) : ℕ) : ℤ), by simp⟩
    convert rat_int_range_mul hx hp using 1 <;> ring
  · have hx : (((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ))
        ∈ Set.range (Int.cast : ℤ → ℚ) := quotient_in_int_range n hn
    have hp : (((((2*n-3)*(2*n-1) : ℕ) : ℚ) / 3)) ∈ Set.range (Int.cast : ℤ → ℚ) :=
      product_div3_in_int_range_of_not_mod1 n hn hmod
    convert rat_int_range_mul hx hp using 1 <;> ring
