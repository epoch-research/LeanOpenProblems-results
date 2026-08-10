import FormalConjectures.Util.ProblemImports
open Nat

lemma digits_two_mul_add_one (m : ℕ) : (2 : ℕ).digits (2*m+1) = 1 :: (2:ℕ).digits m := by
  have h := Nat.digits_add_two_add_one 0 (2*m)
  change (2:ℕ).digits (2*m + 1) = (2*m + 1) % 2 :: (2:ℕ).digits ((2*m + 1) / 2) at h
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [h, hmod, hdiv]

lemma ofDigits_eq_zero_of_sum_zero {L : List ℕ} (h : L.sum = 0) : Nat.ofDigits 2 L = 0 := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons hd tl ih =>
    have hsum : hd + tl.sum = 0 := by simpa using h
    have hhd : hd = 0 := by omega
    have htl_sum : tl.sum = 0 := by omega
    simp [Nat.ofDigits_cons, hhd, ih htl_sum]

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

lemma choose_two_mul_eq_two_mul_choose_sub (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2*n) n = 2 * Nat.choose (2*n - 1) n := by
  have hle : n ≤ 2*n - 1 := by omega
  have hrec := Nat.choose_succ_succ (2*n - 1) (n-1)
  have hsym : Nat.choose (2*n - 1) (n-1) = Nat.choose (2*n - 1) n := by
    have hsub : 2*n - 1 - n = n - 1 := by omega
    rw [← Nat.choose_symm hle, hsub]
  have hsucc : (2*n - 1).succ = 2*n := by omega
  have hpred : (n-1).succ = n := by omega
  rw [hsucc, hpred] at hrec
  rw [hsym] at hrec
  simpa [two_mul] using hrec

lemma padicValNat_two_two : padicValNat 2 2 = 1 := by
  exact padicValNat.self (by norm_num : 1 < 2)

lemma padicValNat_two_central_choose (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Nat.choose (2*n) n) = ((2:ℕ).digits n).sum := by
  rw [choose_two_mul_eq_two_mul_choose_sub n hn]
  have hcpos : 0 < Nat.choose (2*n - 1) n := Nat.choose_pos (by omega)
  have hcne : Nat.choose (2*n - 1) n ≠ 0 := by omega
  have hmul := padicValNat.mul (p:=2) (a:=2) (b:=Nat.choose (2*n - 1) n) (by norm_num) hcne
  rw [hmul, padicValNat_two_two, padicValNat_two_choose_two_mul_sub_one n hn]
  have hpos : 0 < ((2:ℕ).digits n).sum := by
    by_contra hz
    have hz' : ((2:ℕ).digits n).sum = 0 := by omega
    have hof := ofDigits_eq_zero_of_sum_zero (L := (2:ℕ).digits n) hz'
    rw [Nat.ofDigits_digits] at hof
    omega
  omega
