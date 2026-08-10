import FormalConjectures.Util.ProblemImports
open Nat

lemma digits_two_mul_add_one (m : ℕ) : (2 : ℕ).digits (2*m+1) = 1 :: (2:ℕ).digits m := by
  have h := Nat.digits_add_two_add_one 0 (2*m)
  change (2:ℕ).digits (2*m + 1) = (2*m + 1) % 2 :: (2:ℕ).digits ((2*m + 1) / 2) at h
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [h, hmod, hdiv]

lemma padicValNat_two_choose_two_mul_sub_one (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Nat.choose (2*n - 1) n) = ((2:ℕ).digits n).sum - 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' 2 n (n-1) h2
  simp only [Nat.reduceSubDiff, one_mul] at hk
  have hadd : n - 1 + n = 2*n - 1 := by omega
  rw [hadd] at hk
  have hd : (2:ℕ).digits (2*n - 1) = 1 :: (2:ℕ).digits (n-1) := by
    have hn' : 2*n - 1 = 2*(n-1)+1 := by omega
    rw [hn']
    exact digits_two_mul_add_one (n-1)
  rw [hd] at hk
  simp only [List.sum_cons] at hk
  omega

lemma digits_two_one : (2:ℕ).digits 1 = [1] := by
  have h := Nat.digits_add_two_add_one 0 0
  change (2:ℕ).digits 1 = 1 % 2 :: (2:ℕ).digits (1 / 2) at h
  norm_num at h ⊢

lemma sum_digits_two_pow (m : ℕ) : ((2:ℕ).digits (2^m)).sum = 1 := by
  have h := Nat.digits_base_pow_mul (b:=2) (k:=m) (m:=1) (by norm_num) (by norm_num)
  rw [mul_one, digits_two_one] at h
  rw [h, List.sum_append, List.sum_replicate]
  simp

lemma ofDigits_eq_zero_of_sum_zero {L : List ℕ} (h : L.sum = 0) : Nat.ofDigits 2 L = 0 := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons hd tl ih =>
    have hsum : hd + tl.sum = 0 := by simpa using h
    have hhd : hd = 0 := by omega
    have htl_sum : tl.sum = 0 := by omega
    simp [Nat.ofDigits_cons, hhd, ih htl_sum]

lemma exists_pow_two_of_binary_digits_sum_one {L : List ℕ}
    (hbits : ∀ x ∈ L, x < 2) (hsum : L.sum = 1) :
    ∃ m : ℕ, Nat.ofDigits 2 L = 2^m := by
  induction L with
  | nil => simp at hsum
  | cons hd tl ih =>
    have hhdlt : hd < 2 := hbits hd (by simp)
    have htlbits : ∀ x ∈ tl, x < 2 := by
      intro x hx; exact hbits x (by simp [hx])
    have hsum_cons : hd + tl.sum = 1 := by simpa using hsum
    interval_cases hd
    · have htl_sum : tl.sum = 1 := by omega
      rcases ih htlbits htl_sum with ⟨m, hm⟩
      refine ⟨m+1, ?_⟩
      rw [Nat.ofDigits_cons, hm]
      ring_nf
    · have htl_sum0 : tl.sum = 0 := by omega
      refine ⟨0, ?_⟩
      rw [Nat.ofDigits_cons, ofDigits_eq_zero_of_sum_zero htl_sum0]
      norm_num

lemma sum_digits_two_eq_one_iff_exists_pow_two (n : ℕ) :
    ((2:ℕ).digits n).sum = 1 ↔ ∃ m : ℕ, n = 2^m := by
  constructor
  · intro hsum
    have hbits : ∀ x ∈ (2:ℕ).digits n, x < 2 := by
      intro x hx
      exact Nat.digits_lt_base (by norm_num) hx
    rcases exists_pow_two_of_binary_digits_sum_one hbits hsum with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [← Nat.ofDigits_digits 2 n]
    exact hm
  · rintro ⟨m, rfl⟩
    exact sum_digits_two_pow m

lemma odd_iff_padicValNat_two_choose_zero {c : ℕ} (hc : c ≠ 0) :
    Odd c ↔ padicValNat 2 c = 0 := by
  rw [padicValNat.eq_zero_iff]
  constructor
  · intro ho
    right; right
    intro hdiv
    have hmod0 : c % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hmod1 : c % 2 = 1 := Nat.odd_iff.mp ho
    omega
  · intro h
    rcases h with h | h | h
    · omega
    · contradiction
    · rw [Nat.odd_iff]
      exact Nat.two_dvd_ne_zero.mp h

lemma choose_two_mul_sub_one_odd_iff_exists_pow_two (n : ℕ) (hn : 1 ≤ n) :
    Odd (Nat.choose (2*n - 1) n) ↔ ∃ m : ℕ, n = 2^m := by
  have hcpos : 0 < Nat.choose (2*n - 1) n := Nat.choose_pos (by omega)
  have hcne : Nat.choose (2*n - 1) n ≠ 0 := by omega
  rw [odd_iff_padicValNat_two_choose_zero hcne]
  rw [padicValNat_two_choose_two_mul_sub_one n hn]
  constructor
  · intro h
    have hs : ((2:ℕ).digits n).sum = 1 := by
      have hpos : 0 < ((2:ℕ).digits n).sum := by
        -- since n>0, digit sum cannot be zero
        by_contra hz
        have hz' : ((2:ℕ).digits n).sum = 0 := by omega
        have hof := ofDigits_eq_zero_of_sum_zero hz'
        rw [Nat.ofDigits_digits] at hof
        omega
      omega
    exact (sum_digits_two_eq_one_iff_exists_pow_two n).mp hs
  · intro hpow
    have hs := (sum_digits_two_eq_one_iff_exists_pow_two n).mpr hpow
    omega

lemma choose_two_mul_sub_one_odd_iff_exists_pow_two_pos (n : ℕ) (hn : 2 ≤ n) :
    Odd (Nat.choose (2*n - 1) n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m := by
  rw [choose_two_mul_sub_one_odd_iff_exists_pow_two n (by omega)]
  constructor
  · rintro ⟨m, rfl⟩
    have hm : m ≥ 1 := by
      by_contra h0
      have : m = 0 := by omega
      subst m
      omega
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, h⟩
