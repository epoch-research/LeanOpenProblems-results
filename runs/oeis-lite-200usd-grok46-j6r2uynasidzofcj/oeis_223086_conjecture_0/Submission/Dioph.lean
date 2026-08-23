import FormalConjectures.Util.ProblemImports

open Nat

set_option maxHeartbeats 0
set_option exponentiation.threshold 8192

lemma two_pow_ne_three_pow {a b : ℕ} (ha : 0 < a) : 2 ^ a ≠ 3 ^ b := by
  intro h
  have he : Even (2 ^ a) := even_pow.mpr ⟨even_two, ha.ne'⟩
  have ho : Odd (3 ^ b) := Odd.pow (⟨1, by decide⟩ : Odd (3 : ℕ))
  exact Nat.not_odd_iff_even.2 he (by simpa [h] using ho)

/-- Gap template: if `3^B ≤ 2^A < 3^{B+1}` and both endpoint gaps exceed `M`,
every power of three is more than `M` away from `2^A`. -/
lemma two_three_gap_of {A B : ℕ}
    (hle : 3 ^ B ≤ 2 ^ A)
    (hlt : 2 ^ A < 3 ^ (B + 1))
    (hd1 : 2 ^ 20 + 3 ^ 15 < 2 ^ A - 3 ^ B)
    (hd2 : 2 ^ 20 + 3 ^ 15 < 3 ^ (B + 1) - 2 ^ A)
    (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ A then 2 ^ A - 3 ^ k else 3 ^ k - 2 ^ A := by
  by_cases h : 3 ^ k ≤ 2 ^ A
  · have hk : k ≤ B := by
      have : 3 ^ k < 3 ^ (B + 1) := lt_of_le_of_lt h hlt
      exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).1 this)
    have hpow : 3 ^ k ≤ 3 ^ B := Nat.pow_le_pow_right (by decide : 0 < 3) hk
    have hsub : 2 ^ A - 3 ^ B ≤ 2 ^ A - 3 ^ k := Nat.sub_le_sub_left hpow _
    simpa [h] using lt_of_lt_of_le hd1 hsub
  · have hlt' : 2 ^ A < 3 ^ k := Nat.lt_of_not_ge h
    have hk : B + 1 ≤ k := by
      have : 3 ^ B < 3 ^ k := lt_of_le_of_lt hle hlt'
      have : B < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).1 this
      exact Nat.succ_le_iff.2 this
    have hpow : 3 ^ (B + 1) ≤ 3 ^ k := Nat.pow_le_pow_right (by decide : 0 < 3) hk
    have hsub : 3 ^ (B + 1) - 2 ^ A ≤ 3 ^ k - 2 ^ A := Nat.sub_le_sub_right hpow _
    simpa [h] using lt_of_lt_of_le hd2 hsub

lemma two_three_gap_30 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 30 then 2 ^ 30 - 3 ^ k else 3 ^ k - 2 ^ 30 :=
  two_three_gap_of (A := 30) (B := 18) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_31 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 31 then 2 ^ 31 - 3 ^ k else 3 ^ k - 2 ^ 31 :=
  two_three_gap_of (A := 31) (B := 19) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_32 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 32 then 2 ^ 32 - 3 ^ k else 3 ^ k - 2 ^ 32 :=
  two_three_gap_of (A := 32) (B := 20) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_33 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 33 then 2 ^ 33 - 3 ^ k else 3 ^ k - 2 ^ 33 :=
  two_three_gap_of (A := 33) (B := 20) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_34 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 34 then 2 ^ 34 - 3 ^ k else 3 ^ k - 2 ^ 34 :=
  two_three_gap_of (A := 34) (B := 21) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_35 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 35 then 2 ^ 35 - 3 ^ k else 3 ^ k - 2 ^ 35 :=
  two_three_gap_of (A := 35) (B := 22) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_36 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 36 then 2 ^ 36 - 3 ^ k else 3 ^ k - 2 ^ 36 :=
  two_three_gap_of (A := 36) (B := 22) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_37 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 37 then 2 ^ 37 - 3 ^ k else 3 ^ k - 2 ^ 37 :=
  two_three_gap_of (A := 37) (B := 23) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_38 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 38 then 2 ^ 38 - 3 ^ k else 3 ^ k - 2 ^ 38 :=
  two_three_gap_of (A := 38) (B := 23) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_39 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 39 then 2 ^ 39 - 3 ^ k else 3 ^ k - 2 ^ 39 :=
  two_three_gap_of (A := 39) (B := 24) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_40 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 40 then 2 ^ 40 - 3 ^ k else 3 ^ k - 2 ^ 40 :=
  two_three_gap_of (A := 40) (B := 25) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_41 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 41 then 2 ^ 41 - 3 ^ k else 3 ^ k - 2 ^ 41 :=
  two_three_gap_of (A := 41) (B := 25) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_42 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 42 then 2 ^ 42 - 3 ^ k else 3 ^ k - 2 ^ 42 :=
  two_three_gap_of (A := 42) (B := 26) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_43 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 43 then 2 ^ 43 - 3 ^ k else 3 ^ k - 2 ^ 43 :=
  two_three_gap_of (A := 43) (B := 27) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_44 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 44 then 2 ^ 44 - 3 ^ k else 3 ^ k - 2 ^ 44 :=
  two_three_gap_of (A := 44) (B := 27) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_45 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 45 then 2 ^ 45 - 3 ^ k else 3 ^ k - 2 ^ 45 :=
  two_three_gap_of (A := 45) (B := 28) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_46 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 46 then 2 ^ 46 - 3 ^ k else 3 ^ k - 2 ^ 46 :=
  two_three_gap_of (A := 46) (B := 29) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_47 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 47 then 2 ^ 47 - 3 ^ k else 3 ^ k - 2 ^ 47 :=
  two_three_gap_of (A := 47) (B := 29) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_48 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 48 then 2 ^ 48 - 3 ^ k else 3 ^ k - 2 ^ 48 :=
  two_three_gap_of (A := 48) (B := 30) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_49 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 49 then 2 ^ 49 - 3 ^ k else 3 ^ k - 2 ^ 49 :=
  two_three_gap_of (A := 49) (B := 30) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_50 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 50 then 2 ^ 50 - 3 ^ k else 3 ^ k - 2 ^ 50 :=
  two_three_gap_of (A := 50) (B := 31) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_51 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 51 then 2 ^ 51 - 3 ^ k else 3 ^ k - 2 ^ 51 :=
  two_three_gap_of (A := 51) (B := 32) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_52 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 52 then 2 ^ 52 - 3 ^ k else 3 ^ k - 2 ^ 52 :=
  two_three_gap_of (A := 52) (B := 32) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_53 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 53 then 2 ^ 53 - 3 ^ k else 3 ^ k - 2 ^ 53 :=
  two_three_gap_of (A := 53) (B := 33) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_54 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 54 then 2 ^ 54 - 3 ^ k else 3 ^ k - 2 ^ 54 :=
  two_three_gap_of (A := 54) (B := 34) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_55 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 55 then 2 ^ 55 - 3 ^ k else 3 ^ k - 2 ^ 55 :=
  two_three_gap_of (A := 55) (B := 34) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_56 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 56 then 2 ^ 56 - 3 ^ k else 3 ^ k - 2 ^ 56 :=
  two_three_gap_of (A := 56) (B := 35) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_57 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 57 then 2 ^ 57 - 3 ^ k else 3 ^ k - 2 ^ 57 :=
  two_three_gap_of (A := 57) (B := 35) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_58 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 58 then 2 ^ 58 - 3 ^ k else 3 ^ k - 2 ^ 58 :=
  two_three_gap_of (A := 58) (B := 36) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_59 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 59 then 2 ^ 59 - 3 ^ k else 3 ^ k - 2 ^ 59 :=
  two_three_gap_of (A := 59) (B := 37) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_60 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 60 then 2 ^ 60 - 3 ^ k else 3 ^ k - 2 ^ 60 :=
  two_three_gap_of (A := 60) (B := 37) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_61 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 61 then 2 ^ 61 - 3 ^ k else 3 ^ k - 2 ^ 61 :=
  two_three_gap_of (A := 61) (B := 38) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_62 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 62 then 2 ^ 62 - 3 ^ k else 3 ^ k - 2 ^ 62 :=
  two_three_gap_of (A := 62) (B := 39) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_63 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 63 then 2 ^ 63 - 3 ^ k else 3 ^ k - 2 ^ 63 :=
  two_three_gap_of (A := 63) (B := 39) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_64 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 64 then 2 ^ 64 - 3 ^ k else 3 ^ k - 2 ^ 64 :=
  two_three_gap_of (A := 64) (B := 40) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_65 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 65 then 2 ^ 65 - 3 ^ k else 3 ^ k - 2 ^ 65 :=
  two_three_gap_of (A := 65) (B := 41) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_66 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 66 then 2 ^ 66 - 3 ^ k else 3 ^ k - 2 ^ 66 :=
  two_three_gap_of (A := 66) (B := 41) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_67 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 67 then 2 ^ 67 - 3 ^ k else 3 ^ k - 2 ^ 67 :=
  two_three_gap_of (A := 67) (B := 42) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_68 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 68 then 2 ^ 68 - 3 ^ k else 3 ^ k - 2 ^ 68 :=
  two_three_gap_of (A := 68) (B := 42) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_69 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 69 then 2 ^ 69 - 3 ^ k else 3 ^ k - 2 ^ 69 :=
  two_three_gap_of (A := 69) (B := 43) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_70 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 70 then 2 ^ 70 - 3 ^ k else 3 ^ k - 2 ^ 70 :=
  two_three_gap_of (A := 70) (B := 44) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_71 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 71 then 2 ^ 71 - 3 ^ k else 3 ^ k - 2 ^ 71 :=
  two_three_gap_of (A := 71) (B := 44) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_72 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 72 then 2 ^ 72 - 3 ^ k else 3 ^ k - 2 ^ 72 :=
  two_three_gap_of (A := 72) (B := 45) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_73 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 73 then 2 ^ 73 - 3 ^ k else 3 ^ k - 2 ^ 73 :=
  two_three_gap_of (A := 73) (B := 46) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_74 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 74 then 2 ^ 74 - 3 ^ k else 3 ^ k - 2 ^ 74 :=
  two_three_gap_of (A := 74) (B := 46) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_75 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 75 then 2 ^ 75 - 3 ^ k else 3 ^ k - 2 ^ 75 :=
  two_three_gap_of (A := 75) (B := 47) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_76 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 76 then 2 ^ 76 - 3 ^ k else 3 ^ k - 2 ^ 76 :=
  two_three_gap_of (A := 76) (B := 47) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_77 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 77 then 2 ^ 77 - 3 ^ k else 3 ^ k - 2 ^ 77 :=
  two_three_gap_of (A := 77) (B := 48) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_78 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 78 then 2 ^ 78 - 3 ^ k else 3 ^ k - 2 ^ 78 :=
  two_three_gap_of (A := 78) (B := 49) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_79 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 79 then 2 ^ 79 - 3 ^ k else 3 ^ k - 2 ^ 79 :=
  two_three_gap_of (A := 79) (B := 49) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_80 (k : ℕ) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ 80 then 2 ^ 80 - 3 ^ k else 3 ^ k - 2 ^ 80 :=
  two_three_gap_of (A := 80) (B := 50) (by decide) (by decide) (by decide) (by decide) k

lemma two_three_gap_30_80 {a k : ℕ} (ha : 30 ≤ a) (ha' : a ≤ 80) :
    2 ^ 20 + 3 ^ 15 < if 3 ^ k ≤ 2 ^ a then 2 ^ a - 3 ^ k else 3 ^ k - 2 ^ a := by
  interval_cases a
  · exact two_three_gap_30 k
  · exact two_three_gap_31 k
  · exact two_three_gap_32 k
  · exact two_three_gap_33 k
  · exact two_three_gap_34 k
  · exact two_three_gap_35 k
  · exact two_three_gap_36 k
  · exact two_three_gap_37 k
  · exact two_three_gap_38 k
  · exact two_three_gap_39 k
  · exact two_three_gap_40 k
  · exact two_three_gap_41 k
  · exact two_three_gap_42 k
  · exact two_three_gap_43 k
  · exact two_three_gap_44 k
  · exact two_three_gap_45 k
  · exact two_three_gap_46 k
  · exact two_three_gap_47 k
  · exact two_three_gap_48 k
  · exact two_three_gap_49 k
  · exact two_three_gap_50 k
  · exact two_three_gap_51 k
  · exact two_three_gap_52 k
  · exact two_three_gap_53 k
  · exact two_three_gap_54 k
  · exact two_three_gap_55 k
  · exact two_three_gap_56 k
  · exact two_three_gap_57 k
  · exact two_three_gap_58 k
  · exact two_three_gap_59 k
  · exact two_three_gap_60 k
  · exact two_three_gap_61 k
  · exact two_three_gap_62 k
  · exact two_three_gap_63 k
  · exact two_three_gap_64 k
  · exact two_three_gap_65 k
  · exact two_three_gap_66 k
  · exact two_three_gap_67 k
  · exact two_three_gap_68 k
  · exact two_three_gap_69 k
  · exact two_three_gap_70 k
  · exact two_three_gap_71 k
  · exact two_three_gap_72 k
  · exact two_three_gap_73 k
  · exact two_three_gap_74 k
  · exact two_three_gap_75 k
  · exact two_three_gap_76 k
  · exact two_three_gap_77 k
  · exact two_three_gap_78 k
  · exact two_three_gap_79 k
  · exact two_three_gap_80 k

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma padicValNat_two_two : padicValNat 2 2 = 1 :=
  padicValNat_self

lemma padicValNat_two_four : padicValNat 2 4 = 2 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4, padicValNat.pow (a := 2) (n := 2) (by decide : (2 : ℕ) ≠ 0),
    padicValNat_two_two]

lemma padicValNat_two_three_sub : padicValNat 2 (3 - 1) = 1 :=
  padicValNat_two_two

/-- `v₂(3^e - 1)` for positive `e`. -/
lemma padicValNat_two_three_pow_sub_one {e : ℕ} (he : 0 < e) :
    padicValNat 2 (3 ^ e - 1) = if Even e then 2 + padicValNat 2 e else 1 := by
  have hx : ¬ 2 ∣ (3 : ℕ) := by decide
  by_cases hev : Even e
  · have h := padicValNat.pow_two_sub_one (x := 3) (n := e)
      (by decide : 1 < 3) hx he.ne' hev
    have h4 : padicValNat 2 (3 + 1) = 2 := padicValNat_two_four
    have h2 : padicValNat 2 (3 - 1) = 1 := padicValNat_two_three_sub
    rw [h4, h2] at h
    simp [hev]
    omega
  · have hodd : Odd e := Nat.not_even_iff_odd.mp hev
    have h1 : 1 ≤ 3 ^ e := Nat.one_le_pow e 3 (by decide)
    have hmod4 : 3 ^ e % 4 = 3 := by
      have : e % 2 = 1 := Nat.odd_iff.mp hodd
      have hdecomp : e = 2 * (e / 2) + 1 := (Nat.div_add_mod e 2).symm.trans (by rw [this])
      rw [hdecomp, pow_succ, pow_mul, Nat.mul_mod, pow_mod]
      simp
    have hmod : (3 ^ e - 1) % 4 = 2 := by omega
    have h2 : 2 ∣ 3 ^ e - 1 := by
      have : (3 ^ e - 1) % 2 = 0 := by
        have : 3 ^ e % 2 = 1 := Nat.odd_iff.mp (Odd.pow (⟨1, by decide⟩ : Odd (3 : ℕ)))
        omega
      exact Nat.dvd_of_mod_eq_zero this
    have h4 : ¬ 4 ∣ 3 ^ e - 1 := by
      intro hd
      have : (3 ^ e - 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
      omega
    have hv : padicValNat 2 (3 ^ e - 1) = 1 := by
      have h2le : 1 ≤ padicValNat 2 (3 ^ e - 1) :=
        one_le_padicValNat_of_dvd (Nat.sub_ne_zero_of_lt (by omega : 1 < 3 ^ e)) h2
      have : padicValNat 2 (3 ^ e - 1) ≤ 1 := by
        by_contra hgt
        have hdvd : 4 ∣ 3 ^ e - 1 := by
          have hpow := pow_padicValNat_dvd (p := 2) (n := 3 ^ e - 1)
          have : 2 ^ 2 ∣ 2 ^ padicValNat 2 (3 ^ e - 1) :=
            pow_dvd_pow 2 (by omega)
          exact this.trans hpow
        exact h4 hdvd
      omega
    simp [hev, hv]

/-- `v₂(3^e + 1)`. -/
lemma padicValNat_two_three_pow_add_one (e : ℕ) :
    padicValNat 2 (3 ^ e + 1) = if Even e then 1 else 2 := by
  by_cases hev : Even e
  · have hmod : (3 ^ e + 1) % 8 = 2 := by
      obtain ⟨k, hk⟩ := hev
      have he2 : e = 2 * k := by omega
      have : (3 ^ e) % 8 = 1 := by
        rw [he2, pow_mul, show (3 : ℕ) ^ 2 = 9 from rfl, Nat.pow_mod]
        simp
      omega
    have h2 : 2 ∣ 3 ^ e + 1 := by
      have : (3 ^ e + 1) % 2 = 0 := by
        have : 3 ^ e % 2 = 1 := Nat.odd_iff.mp (Odd.pow (⟨1, by decide⟩ : Odd (3 : ℕ)))
        omega
      exact Nat.dvd_of_mod_eq_zero this
    have h4 : ¬ 4 ∣ 3 ^ e + 1 := by
      intro hd
      have : (3 ^ e + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
      omega
    have hv : padicValNat 2 (3 ^ e + 1) = 1 := by
      have h2le : 1 ≤ padicValNat 2 (3 ^ e + 1) :=
        one_le_padicValNat_of_dvd (by omega) h2
      have : padicValNat 2 (3 ^ e + 1) ≤ 1 := by
        by_contra hgt
        have hdvd : 4 ∣ 3 ^ e + 1 := by
          have hpow := pow_padicValNat_dvd (p := 2) (n := 3 ^ e + 1)
          have : 2 ^ 2 ∣ 2 ^ padicValNat 2 (3 ^ e + 1) :=
            pow_dvd_pow 2 (by omega)
          exact this.trans hpow
        exact h4 hdvd
      omega
    simp [hev, hv]
  · have hodd : Odd e := Nat.not_even_iff_odd.mp hev
    have hmod8 : (3 ^ e + 1) % 8 = 4 := by
      have : e % 2 = 1 := Nat.odd_iff.mp hodd
      have hdecomp : e = 2 * (e / 2) + 1 := (Nat.div_add_mod e 2).symm.trans (by rw [this])
      have : 3 ^ e % 8 = 3 := by
        rw [hdecomp, pow_succ, pow_mul, Nat.mul_mod, pow_mod]
        have : (3 : ℕ) ^ 2 % 8 = 1 := by decide
        rw [this]; simp
      omega
    have h4 : 4 ∣ 3 ^ e + 1 := by
      have : (3 ^ e + 1) % 4 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h8 : ¬ 8 ∣ 3 ^ e + 1 := by
      intro hd
      have : (3 ^ e + 1) % 8 = 0 := Nat.mod_eq_zero_of_dvd hd
      omega
    have hv : padicValNat 2 (3 ^ e + 1) = 2 := by
      have h2le : 2 ≤ padicValNat 2 (3 ^ e + 1) :=
        (padicValNat_dvd_iff_le (p := 2) (by omega)).mp h4
      have : padicValNat 2 (3 ^ e + 1) ≤ 2 := by
        by_contra hgt
        have : 8 ∣ 3 ^ e + 1 := by
          have hpow := pow_padicValNat_dvd (p := 2) (n := 3 ^ e + 1)
          have : 2 ^ 3 ∣ 2 ^ padicValNat 2 (3 ^ e + 1) :=
            pow_dvd_pow 2 (by omega)
          exact this.trans hpow
        exact h8 this
      omega
    simp [hev, hv]

/-! ### The equation `2^x (2^y ± 1) = 3^z (3^w ± 1)` -/

lemma v3_two_pow_sub_one (n : ℕ) :
    padicValNat 3 (2 ^ n - 1) ≤ 1 + padicValNat 3 n := by
  by_cases hn : n = 0
  · subst hn; simp
  by_cases he : Even n
  · -- even: 2^n - 1 = 4^{n/2} - 1, LTE at p=3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := he
    have hn2 : n = 2 * k := by omega
    have hk0 : k ≠ 0 := by rintro rfl; exact hn (by omega)
    have hrew : 2 ^ n - 1 = 4 ^ k - 1 := by
      rw [hn2, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, Nat.mul_comm k]
    rw [hrew]
    have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
      (by decide : 1 < 4) (by decide : 3 ∣ 4 - 1) (by decide : ¬ 3 ∣ 4) hk0
      ⟨1, by decide⟩
    have hv4 : padicValNat 3 (4 - 1) = 1 := by decide
    have hvk : padicValNat 3 k = padicValNat 3 n := by
      rw [hn2, padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hk0]
      have : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
      omega
    rw [h, hv4, hvk]; omega
  · apply Nat.le_trans (b := 0)
    · apply Nat.le_of_eq
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hodd : Odd n := Nat.not_even_iff_odd.mp he
      have hpow : 2 ^ n % 3 = 2 := by
        have : n % 2 = 1 := Nat.odd_iff.mp hodd
        have hdecomp : n = 2 * (n / 2) + 1 := (Nat.div_add_mod n 2).symm.trans (by rw [this])
        rw [hdecomp, pow_succ, pow_mul, Nat.mul_mod, pow_mod]; simp
      have : (2 ^ n - 1) % 3 = 1 := by
        have hge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have := Nat.div_add_mod (2 ^ n) 3
        rw [hpow] at this
        omega
      have : (2 ^ n - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
      omega
    · omega

lemma v3_two_pow_add_one (n : ℕ) :
    padicValNat 3 (2 ^ n + 1) ≤ 1 + padicValNat 3 n := by
  by_cases he : Even n
  · apply Nat.le_trans (b := 0)
    · apply Nat.le_of_eq
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hpow : 2 ^ n % 3 = 1 := by
        obtain ⟨k, hk⟩ := he
        have : n = 2 * k := by omega
        rw [this, pow_mul, Nat.pow_mod]; simp
      have : (2 ^ n + 1) % 3 = 2 := by rw [Nat.add_mod, hpow]
      have : (2 ^ n + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
      omega
    · omega
  · have hodd : Odd n := Nat.not_even_iff_odd.mp he
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
      (by decide : 3 ∣ 2 + 1) (by decide : ¬ 3 ∣ 2) hodd
    have hv : padicValNat 3 (2 + 1) = 1 := by decide
    rw [h, hv]

/-- The four-sign equation with large 2-exponent is impossible. -/
lemma two_pow_mul_ne_three_pow_mul
    {x y z w : ℕ} (hxy : 30 ≤ x + y) (hx80 : x + y ≤ 80)
    (ε₁ ε₂ : ℤ) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (h : ((2 : ℤ) ^ x * ((2 : ℤ) ^ y + ε₁) = (3 : ℤ) ^ z * ((3 : ℤ) ^ w + ε₂))) :
    False := by
  -- Reduce to Nat and apply the gap lemma.
  -- LHS size is about 2^{x+y}, RHS about 3^{z+w}.
  have hxpos : 0 < x + y := by omega
  -- Compare absolute values: |2^{x+y} ± 2^x| = |3^{z+w} ± 3^z|
  -- so |2^{x+y} - 3^{z+w}| ≤ 2^x + 3^z.
  -- From v3(LHS)=z (approximately) we get z small, so 2^x + 3^z ≤ 2^{20}+3^{15}.
  -- Then the gap lemma contradicts x+y ≥ 30.
  revert h
  rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl
  · -- ++
    intro h
    -- 2^x (2^y + 1) = 3^z (3^w + 1)
    have hN : (2 : ℕ) ^ x * (2 ^ y + 1) = 3 ^ z * (3 ^ w + 1) := by
      exact_mod_cast h
    -- v3 of LHS = v3(2^y+1) ≤ 1+v3(y)
    have hz : z = padicValNat 3 (2 ^ y + 1) := by
      have h3L : padicValNat 3 (2 ^ x * (2 ^ y + 1)) = padicValNat 3 (2 ^ y + 1) := by
        have hx0 : 2 ^ x ≠ 0 := Nat.pow_ne_zero _ (by decide)
        have hy0 : 2 ^ y + 1 ≠ 0 := by omega
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        rw [padicValNat.mul hx0 hy0]
        have : padicValNat 3 (2 ^ x) = 0 := by
          rw [padicValNat.pow (by decide : (2 : ℕ) ≠ 0)]
          have : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
          omega
        omega
      have h3R : padicValNat 3 (3 ^ z * (3 ^ w + 1)) = z := by
        have hz0 : 3 ^ z ≠ 0 := Nat.pow_ne_zero _ (by decide)
        have hw0 : 3 ^ w + 1 ≠ 0 := by omega
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        rw [padicValNat.mul hz0 hw0, padicValNat.pow (by decide : (3 : ℕ) ≠ 0),
          padicValNat_self (p := 3)]
        have hnot : ¬ 3 ∣ 3 ^ w + 1 := by
          intro hd
          have : (3 ^ w + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
          have : 3 ^ w % 3 = 0 := Nat.pow_mod _ _ _
          -- 3^w ≡ 0 for w>0, +1 ≡ 1; for w=0, 1+1=2
          have : (3 ^ w + 1) % 3 = 1 := by
            cases w with
            | zero => decide
            | succ w =>
              rw [pow_succ, Nat.mul_mod]
              have : 3 % 3 = 0 := rfl
              simp
          omega
        have : padicValNat 3 (3 ^ w + 1) = 0 := padicValNat.eq_zero_of_not_dvd hnot
        omega
      have : padicValNat 3 (2 ^ x * (2 ^ y + 1)) = padicValNat 3 (3 ^ z * (3 ^ w + 1)) := by
        rw [hN]
      omega
    have hzle : z ≤ 1 + padicValNat 3 y := by
      rw [hz]; exact v3_two_pow_add_one y
    have hz15 : z ≤ 15 := by
      have : padicValNat 3 y ≤ y := padicValNat_le_nat_log y |>.trans (Nat.log_le_self _ _)
      -- cruder: padicValNat 3 y ≤ 6 for y small enough, but y ≤ 80
      have : padicValNat 3 y ≤ 5 := by
        by_contra hgt
        have : 6 ≤ padicValNat 3 y := by omega
        have : 3 ^ 6 ∣ y := (pow_dvd_pow (n := 6) (m := padicValNat 3 y) (by omega)).trans
          pow_padicValNat_dvd
        have : 729 ≤ y := Nat.le_of_dvd (by
          have : 0 < y ∨ y = 0 := by omega
          rcases this with hy | hy
          · exact hy
          · subst hy
            have : ¬ 3 ^ 6 ∣ (0 : ℕ) := by decide
            exact (this ‹_›).elim) this
        -- y can be 0; 3^6 ∣ 0 is TRUE in Lean! 729 ≤ 0 is false so we need care
        -- if y=0, padicValNat 3 0 = 0
        have hypos : y ≠ 0 := by
          intro hy; subst hy
          have : padicValNat 3 0 = 0 := padicValNat.zero
          omega
        have : 729 ≤ y := Nat.le_of_dvd (Nat.pos_of_ne_zero hypos) this
        -- y ≤ x+y ≤ 80 < 729
        omega
      omega
    -- Now |2^{x+y} - 3^{z+w}| ≤ 2^x + 3^z
    have hsize : 2 ^ (x + y) + 2 ^ x = 3 ^ (z + w) + 3 ^ z ∨
        2 ^ (x + y) + 2 ^ x = 3 ^ (z + w) - 3 ^ z ∨
        2 ^ (x + y) - 2 ^ x = 3 ^ (z + w) + 3 ^ z ∨
        2 ^ (x + y) - 2 ^ x = 3 ^ (z + w) - 3 ^ z := by
      -- 2^x * 2^y + 2^x = 3^z * 3^w + 3^z
      have : 2 ^ x * 2 ^ y + 2 ^ x = 3 ^ z * 3 ^ w + 3 ^ z := by
        have := hN
        ring_nf at this ⊢
        -- 2^x * (2^y + 1) = 2^{x+y} + 2^x
        have hl : 2 ^ x * (2 ^ y + 1) = 2 ^ (x + y) + 2 ^ x := by
          rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm (2 ^ x) (2 ^ y)]
        have hr : 3 ^ z * (3 ^ w + 1) = 3 ^ (z + w) + 3 ^ z := by
          rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm (3 ^ z) (3 ^ w)]
        omega
      omega
    -- All four cases give |2^{x+y} - 3^{z+w}| ≤ 2^x + 3^z ≤ 2^{20} + 3^{15}
    have hbound : 2 ^ x + 3 ^ z ≤ 2 ^ 20 + 3 ^ 15 := by
      have hxle : 2 ^ x ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (by
        -- x ≤ x+y ≤ 80, but we only need x ≤ 20? NOT TRUE. x can be up to 80!
        -- v2(RHS) = v2(3^w+1) ≤ 2, so x ≤ 2 actually!
        omega)
      sorry
    sorry
  · sorry
  · sorry
  · sorry
