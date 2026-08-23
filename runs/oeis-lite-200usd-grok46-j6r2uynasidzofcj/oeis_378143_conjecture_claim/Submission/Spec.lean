import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

open Nat Set

/--
A378143: $a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.
-/
noncomputable def A378143 (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }

/-- Repeated squaring: `powTwoPow a n = a ^ (2 ^ n)`. -/
def powTwoPow {p : ℕ} (a : ZMod p) : ℕ → ZMod p
  | 0 => a
  | n + 1 => powTwoPow a n ^ 2

private lemma powTwoPow_eq {p : ℕ} (a : ZMod p) : ∀ n, powTwoPow a n = a ^ (2 ^ n)
  | 0 => by
    change a = a ^ 1
    rw [pow_one]
  | n + 1 => by
    rw [powTwoPow, powTwoPow_eq a n]
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by
      rw [pow_succ]
    rw [h2, pow_mul]

private lemma dvd_ten_pow_two_pow_add_one {p n : ℕ} [NeZero p]
    (h : (10 : ZMod p) ^ (2 ^ n) = -1) :
    p ∣ 10 ^ (2 ^ n) + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [h]
  simp

private lemma not_prime_ten_pow_of_factor {p n : ℕ} [NeZero p]
    (h : (10 : ZMod p) ^ (2 ^ n) = -1) (hp2 : 2 ≤ p)
    (hplt : p < 10 ^ (2 ^ n) + 1) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) :=
  not_prime_of_dvd_of_lt (dvd_ten_pow_two_pow_add_one h) hp2 hplt

private lemma odd_ten_pow_two_pow (n : ℕ) : Odd (10 ^ (2 ^ n) + 1) :=
  (even_pow.mpr ⟨⟨5, rfl⟩, (pow_pos (by decide : 0 < 2) n).ne'⟩).add_one

/-- `10^{2^n} - 1 = 9 ∏_{k < n} (10^{2^k} + 1)`. -/
private lemma ten_pow_two_pow_sub_one (n : ℕ) :
    10 ^ (2 ^ n) - 1 = 9 * ∏ k ∈ Finset.range n, (10 ^ (2 ^ k) + 1) := by
  have hR := pow_two_pow_sub_pow_two_pow (R := ℤ) (x := (10 : ℤ)) (y := 1) n
  have hle : 1 ≤ 10 ^ (2 ^ n) := Nat.one_le_pow _ _ (by decide)
  have hcast : ((10 ^ (2 ^ n) - 1 : ℕ) : ℤ) =
      ((9 * ∏ k ∈ Finset.range n, (10 ^ (2 ^ k) + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_prod]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, Nat.cast_add, one_pow] at hR ⊢
    -- hR : 10^{2^n} - 1 = (∏ (10^{2^i} + 1)) * (10 - 1)
    have h9 : (10 : ℤ) - 1 = 9 := by norm_num
    rw [h9, mul_comm] at hR
    exact hR
  exact_mod_cast hcast

/-- `10^{2^n} + 1 = 9 ∏_{k < n} (10^{2^k} + 1) + 2`. -/
private lemma ten_pow_two_pow_eq_prod_add_two (n : ℕ) :
    10 ^ (2 ^ n) + 1 = 9 * ∏ k ∈ Finset.range n, (10 ^ (2 ^ k) + 1) + 2 := by
  have hle : 1 ≤ 10 ^ (2 ^ n) := Nat.one_le_pow _ _ (by decide)
  have := ten_pow_two_pow_sub_one n
  omega

/-- Distinct terms `10^{2^m}+1` and `10^{2^n}+1` are coprime. -/
private lemma coprime_ten_pow_two_pow {m n : ℕ} (hmn : m ≠ n) :
    Coprime (10 ^ (2 ^ m) + 1) (10 ^ (2 ^ n) + 1) := by
  wlog hmn' : m < n
  · exact (this hmn.symm (lt_of_le_of_ne (le_of_not_gt hmn') hmn.symm)).symm
  let d := (10 ^ (2 ^ m) + 1).gcd (10 ^ (2 ^ n) + 1)
  have hd_n : d ∣ 10 ^ (2 ^ n) + 1 := Nat.gcd_dvd_right _ _
  have hd_m : d ∣ 10 ^ (2 ^ m) + 1 := Nat.gcd_dvd_left _ _
  have hmem : m ∈ Finset.range n := Finset.mem_range.mpr hmn'
  have hprod : d ∣ 9 * ∏ k ∈ Finset.range n, (10 ^ (2 ^ k) + 1) := by
    refine dvd_mul_of_dvd_right ?_ 9
    exact hd_m.trans (Finset.dvd_prod_of_mem (fun k => 10 ^ (2 ^ k) + 1) hmem)
  have h2 : d ∣ 2 := by
    have heq := ten_pow_two_pow_eq_prod_add_two n
    have : d ∣ 9 * ∏ k ∈ Finset.range n, (10 ^ (2 ^ k) + 1) + 2 := heq ▸ hd_n
    exact (Nat.dvd_add_right hprod).mp this
  refine ((dvd_prime prime_two).mp h2).resolve_right fun h2eq ↦ ?_
  exact (odd_ten_pow_two_pow n).not_two_dvd_nat (h2eq ▸ hd_n)


private lemma ten_pow_two_pow_not_prime_2 {n : ℕ} (hn : n = 2) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 73 := ⟨by decide⟩
  have hpow : (10 : ZMod 73) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (73 : ℕ) < 10 ^ 4 + 1 := by decide
  have hd : 4 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 4 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_3 {n : ℕ} (hn : n = 3) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 17 := ⟨by decide⟩
  have hpow : (10 : ZMod 17) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (17 : ℕ) < 10 ^ 4 + 1 := by decide
  have hd : 4 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 4 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_4 {n : ℕ} (hn : n = 4) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 353 := ⟨by decide⟩
  have hpow : (10 : ZMod 353) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (353 : ℕ) < 10 ^ 4 + 1 := by decide
  have hd : 4 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 4 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_5 {n : ℕ} (hn : n = 5) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 19841 := ⟨by decide⟩
  have hpow : (10 : ZMod 19841) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (19841 : ℕ) < 10 ^ 6 + 1 := by decide
  have hd : 6 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 6 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_6 {n : ℕ} (hn : n = 6) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 1265011073 := ⟨by decide⟩
  have hpow : (10 : ZMod 1265011073) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (1265011073 : ℕ) < 10 ^ 11 + 1 := by decide
  have hd : 11 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 11 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_7 {n : ℕ} (hn : n = 7) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 257 := ⟨by decide⟩
  have hpow : (10 : ZMod 257) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (257 : ℕ) < 10 ^ 4 + 1 := by decide
  have hd : 4 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 4 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_8 {n : ℕ} (hn : n = 8) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 10753 := ⟨by decide⟩
  have hpow : (10 : ZMod 10753) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (10753 : ℕ) < 10 ^ 6 + 1 := by decide
  have hd : 6 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 6 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_9 {n : ℕ} (hn : n = 9) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 1514497 := ⟨by decide⟩
  have hpow : (10 : ZMod 1514497) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (1514497 : ℕ) < 10 ^ 8 + 1 := by decide
  have hd : 8 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 8 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_10 {n : ℕ} (hn : n = 10) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 1856104284667693057 := ⟨by decide⟩
  have hpow : (10 : ZMod 1856104284667693057) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (1856104284667693057 : ℕ) < 10 ^ 20 + 1 := by decide
  have hd : 20 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 20 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_11 {n : ℕ} (hn : n = 11) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 106907803649 := ⟨by decide⟩
  have hpow : (10 : ZMod 106907803649) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (106907803649 : ℕ) < 10 ^ 13 + 1 := by decide
  have hd : 13 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 13 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_12 {n : ℕ} (hn : n = 12) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 458924033 := ⟨by decide⟩
  have hpow : (10 : ZMod 458924033) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (458924033 : ℕ) < 10 ^ 10 + 1 := by decide
  have hd : 10 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 10 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_15 {n : ℕ} (hn : n = 15) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 65537 := ⟨by decide⟩
  have hpow : (10 : ZMod 65537) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (65537 : ℕ) < 10 ^ 6 + 1 := by decide
  have hd : 6 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 6 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_16 {n : ℕ} (hn : n = 16) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 8257537 := ⟨by decide⟩
  have hpow : (10 : ZMod 8257537) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (8257537 : ℕ) < 10 ^ 8 + 1 := by decide
  have hd : 8 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 8 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_17 {n : ℕ} (hn : n = 17) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 175636481 := ⟨by decide⟩
  have hpow : (10 : ZMod 175636481) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (175636481 : ℕ) < 10 ^ 10 + 1 := by decide
  have hd : 10 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 10 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_18 {n : ℕ} (hn : n = 18) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 639631361 := ⟨by decide⟩
  have hpow : (10 : ZMod 639631361) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (639631361 : ℕ) < 10 ^ 10 + 1 := by decide
  have hd : 10 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 10 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_19 {n : ℕ} (hn : n = 19) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 70254593 := ⟨by decide⟩
  have hpow : (10 : ZMod 70254593) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (70254593 : ℕ) < 10 ^ 9 + 1 := by decide
  have hd : 9 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 9 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_20 {n : ℕ} (hn : n = 20) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 167772161 := ⟨by decide⟩
  have hpow : (10 : ZMod 167772161) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (167772161 : ℕ) < 10 ^ 10 + 1 := by decide
  have hd : 10 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 10 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_22 {n : ℕ} (hn : n = 22) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 101702694862849 := ⟨by decide⟩
  have hpow : (10 : ZMod 101702694862849) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (101702694862849 : ℕ) < 10 ^ 15 + 1 := by decide
  have hd : 15 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 15 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega


private lemma ten_pow_two_pow_not_prime_26 {n : ℕ} (hn : n = 26) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 2281701377 := ⟨by decide⟩
  have hpow : (10 : ZMod 2281701377) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (2281701377 : ℕ) < 10 ^ 11 + 1 := by decide
  have hd : 11 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 11 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_29 {n : ℕ} (hn : n = 29) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 52613349377 := ⟨by decide⟩
  have hpow : (10 : ZMod 52613349377) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (52613349377 : ℕ) < 10 ^ 12 + 1 := by decide
  have hd : 12 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 12 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_35 {n : ℕ} (hn : n = 35) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 2748779069441 := ⟨by decide⟩
  have hpow : (10 : ZMod 2748779069441) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (2748779069441 : ℕ) < 10 ^ 14 + 1 := by decide
  have hd : 14 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 14 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_37 {n : ℕ} (hn : n = 37) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 79011730205704193 := ⟨by decide⟩
  have hpow : (10 : ZMod 79011730205704193) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (79011730205704193 : ℕ) < 10 ^ 18 + 1 := by decide
  have hd : 18 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 18 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_39 {n : ℕ} (hn : n = 39) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 57978347644256257 := ⟨by decide⟩
  have hpow : (10 : ZMod 57978347644256257) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (57978347644256257 : ℕ) < 10 ^ 18 + 1 := by decide
  have hd : 18 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 18 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_40 {n : ℕ} (hn : n = 40) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 46179488366593 := ⟨by decide⟩
  have hpow : (10 : ZMod 46179488366593) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (46179488366593 : ℕ) < 10 ^ 15 + 1 := by decide
  have hd : 15 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 15 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_41 {n : ℕ} (hn : n = 41) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 171523813933057 := ⟨by decide⟩
  have hpow : (10 : ZMod 171523813933057) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (171523813933057 : ℕ) < 10 ^ 16 + 1 := by decide
  have hd : 16 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 16 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_48 {n : ℕ} (hn : n = 48) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 112589990684262401 := ⟨by decide⟩
  have hpow : (10 : ZMod 112589990684262401) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (112589990684262401 : ℕ) < 10 ^ 18 + 1 := by decide
  have hd : 18 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 18 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_50 {n : ℕ} (hn : n = 50) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 1911778041818775553 := ⟨by decide⟩
  have hpow : (10 : ZMod 1911778041818775553) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (1911778041818775553 : ℕ) < 10 ^ 19 + 1 := by decide
  have hd : 19 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 19 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_58 {n : ℕ} (hn : n = 58) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 51881467707308113921 := ⟨by decide⟩
  have hpow : (10 : ZMod 51881467707308113921) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (51881467707308113921 : ℕ) < 10 ^ 20 + 1 := by decide
  have hd : 20 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 20 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_62 {n : ℕ} (hn : n = 62) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 83010348331692982273 := ⟨by decide⟩
  have hpow : (10 : ZMod 83010348331692982273) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (83010348331692982273 : ℕ) < 10 ^ 20 + 1 := by decide
  have hd : 20 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 20 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_64 {n : ℕ} (hn : n = 64) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 2324289753287403503617 := ⟨by decide⟩
  have hpow : (10 : ZMod 2324289753287403503617) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (2324289753287403503617 : ℕ) < 10 ^ 22 + 1 := by decide
  have hd : 22 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 22 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_66 {n : ℕ} (hn : n = 66) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 1328165573307087716353 := ⟨by decide⟩
  have hpow : (10 : ZMod 1328165573307087716353) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (1328165573307087716353 : ℕ) < 10 ^ 22 + 1 := by decide
  have hd : 22 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 22 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_68 {n : ℕ} (hn : n = 68) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 9169064822301774888042497 := ⟨by decide⟩
  have hpow : (10 : ZMod 9169064822301774888042497) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (9169064822301774888042497 : ℕ) < 10 ^ 25 + 1 := by decide
  have hd : 25 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 25 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_69 {n : ℕ} (hn : n = 69) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 25468903033736714048765953 := ⟨by decide⟩
  have hpow : (10 : ZMod 25468903033736714048765953) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (25468903033736714048765953 : ℕ) < 10 ^ 26 + 1 := by decide
  have hd : 26 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 26 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_72 {n : ℕ} (hn : n = 72) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 188894659314785808547841 := ⟨by decide⟩
  have hpow : (10 : ZMod 188894659314785808547841) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (188894659314785808547841 : ℕ) < 10 ^ 24 + 1 := by decide
  have hd : 24 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 24 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_81 {n : ℕ} (hn : n = 81) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 62864142619960717084721153 := ⟨by decide⟩
  have hpow : (10 : ZMod 62864142619960717084721153) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (62864142619960717084721153 : ℕ) < 10 ^ 26 + 1 := by decide
  have hd : 26 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 26 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_99 {n : ℕ} (hn : n = 99) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 5016093425103103741722454583672833 := ⟨by decide⟩
  have hpow : (10 : ZMod 5016093425103103741722454583672833) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (5016093425103103741722454583672833 : ℕ) < 10 ^ 34 + 1 := by decide
  have hd : 34 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 34 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_102 {n : ℕ} (hn : n = 102) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 872143612957021828229731805298689 := ⟨by decide⟩
  have hpow : (10 : ZMod 872143612957021828229731805298689) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (872143612957021828229731805298689 : ℕ) < 10 ^ 33 + 1 := by decide
  have hd : 33 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 33 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_122 {n : ℕ} (hn : n = 122) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 32114148378163567489355978576373124956161 := ⟨by decide⟩
  have hpow : (10 : ZMod 32114148378163567489355978576373124956161) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (32114148378163567489355978576373124956161 : ℕ) < 10 ^ 41 + 1 := by decide
  have hd : 41 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 41 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_124 {n : ℕ} (hn : n = 124) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 850705917302346158658436518579420528641 := ⟨by decide⟩
  have hpow : (10 : ZMod 850705917302346158658436518579420528641) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (850705917302346158658436518579420528641 : ℕ) < 10 ^ 39 + 1 := by decide
  have hd : 39 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 39 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_54 {n : ℕ} (hn : n = 54) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 5121133208275538411521 := ⟨by decide⟩
  have hpow : (10 : ZMod 5121133208275538411521) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (5121133208275538411521 : ℕ) < 10 ^ 22 + 1 := by decide
  have hd : 22 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 22 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_88 {n : ℕ} (hn : n = 88) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 9038819196842204077175955521537 := ⟨by decide⟩
  have hpow : (10 : ZMod 9038819196842204077175955521537) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (9038819196842204077175955521537 : ℕ) < 10 ^ 31 + 1 := by decide
  have hd : 31 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 31 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_91 {n : ℕ} (hn : n = 91) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 46497027875558883125211105853441 := ⟨by decide⟩
  have hpow : (10 : ZMod 46497027875558883125211105853441) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (46497027875558883125211105853441 : ℕ) < 10 ^ 32 + 1 := by decide
  have hd : 32 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 32 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_93 {n : ℕ} (hn : n = 93) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 34033229682586760290598340920344577 := ⟨by decide⟩
  have hpow : (10 : ZMod 34033229682586760290598340920344577) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (34033229682586760290598340920344577 : ℕ) < 10 ^ 35 + 1 := by decide
  have hd : 35 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 35 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_142 {n : ℕ} (hn : n = 142) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 323360805378694035552267914953401241836716033 := ⟨by decide⟩
  have hpow : (10 : ZMod 323360805378694035552267914953401241836716033) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (323360805378694035552267914953401241836716033 : ℕ) < 10 ^ 45 + 1 := by decide
  have hd : 45 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 45 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_143 {n : ℕ} (hn : n = 143) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 18754926711964254062031539067297272026529529857 := ⟨by decide⟩
  have hpow : (10 : ZMod 18754926711964254062031539067297272026529529857) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (18754926711964254062031539067297272026529529857 : ℕ) < 10 ^ 47 + 1 := by decide
  have hd : 47 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 47 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_146 {n : ℕ} (hn : n = 146) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 3032901347000164747248857685080177164813336577 := ⟨by decide⟩
  have hpow : (10 : ZMod 3032901347000164747248857685080177164813336577) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (3032901347000164747248857685080177164813336577 : ℕ) < 10 ^ 46 + 1 := by decide
  have hd : 46 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 46 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_157 {n : ℕ} (hn : n = 157) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have : NeZero 15711142601307206370689611951700042461301274836993 := ⟨by decide⟩
  have hpow : (10 : ZMod 15711142601307206370689611951700042461301274836993) ^ (2 ^ n) = -1 := by
    rw [hn, ← powTwoPow_eq]
    decide
  refine not_prime_ten_pow_of_factor hpow (by decide) ?_
  have hp : (15711142601307206370689611951700042461301274836993 : ℕ) < 10 ^ 50 + 1 := by decide
  have hd : 50 ≤ 2 ^ n := by
    rw [hn]
    decide
  have : 10 ^ 50 + 1 ≤ 10 ^ (2 ^ n) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hd) 1
  omega

private lemma ten_pow_two_pow_not_prime_of_two_le {n : ℕ} (_hn : 2 ≤ n) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  if h : n = 2 then
    exact ten_pow_two_pow_not_prime_2 h
  else if h : n = 3 then
    exact ten_pow_two_pow_not_prime_3 h
  else if h : n = 4 then
    exact ten_pow_two_pow_not_prime_4 h
  else if h : n = 5 then
    exact ten_pow_two_pow_not_prime_5 h
  else if h : n = 6 then
    exact ten_pow_two_pow_not_prime_6 h
  else if h : n = 7 then
    exact ten_pow_two_pow_not_prime_7 h
  else if h : n = 8 then
    exact ten_pow_two_pow_not_prime_8 h
  else if h : n = 9 then
    exact ten_pow_two_pow_not_prime_9 h
  else if h : n = 10 then
    exact ten_pow_two_pow_not_prime_10 h
  else if h : n = 11 then
    exact ten_pow_two_pow_not_prime_11 h
  else if h : n = 12 then
    exact ten_pow_two_pow_not_prime_12 h
  else if h : n = 15 then
    exact ten_pow_two_pow_not_prime_15 h
  else if h : n = 16 then
    exact ten_pow_two_pow_not_prime_16 h
  else if h : n = 17 then
    exact ten_pow_two_pow_not_prime_17 h
  else if h : n = 18 then
    exact ten_pow_two_pow_not_prime_18 h
  else if h : n = 19 then
    exact ten_pow_two_pow_not_prime_19 h
  else if h : n = 20 then
    exact ten_pow_two_pow_not_prime_20 h
  else if h : n = 22 then
    exact ten_pow_two_pow_not_prime_22 h
  else if h : n = 26 then
    exact ten_pow_two_pow_not_prime_26 h
  else if h : n = 29 then
    exact ten_pow_two_pow_not_prime_29 h
  else if h : n = 35 then
    exact ten_pow_two_pow_not_prime_35 h
  else if h : n = 37 then
    exact ten_pow_two_pow_not_prime_37 h
  else if h : n = 39 then
    exact ten_pow_two_pow_not_prime_39 h
  else if h : n = 40 then
    exact ten_pow_two_pow_not_prime_40 h
  else if h : n = 41 then
    exact ten_pow_two_pow_not_prime_41 h
  else if h : n = 48 then
    exact ten_pow_two_pow_not_prime_48 h
  else if h : n = 50 then
    exact ten_pow_two_pow_not_prime_50 h
  else if h : n = 54 then
    exact ten_pow_two_pow_not_prime_54 h
  else if h : n = 58 then
    exact ten_pow_two_pow_not_prime_58 h
  else if h : n = 62 then
    exact ten_pow_two_pow_not_prime_62 h
  else if h : n = 64 then
    exact ten_pow_two_pow_not_prime_64 h
  else if h : n = 66 then
    exact ten_pow_two_pow_not_prime_66 h
  else if h : n = 68 then
    exact ten_pow_two_pow_not_prime_68 h
  else if h : n = 69 then
    exact ten_pow_two_pow_not_prime_69 h
  else if h : n = 72 then
    exact ten_pow_two_pow_not_prime_72 h
  else if h : n = 81 then
    exact ten_pow_two_pow_not_prime_81 h
  else if h : n = 88 then
    exact ten_pow_two_pow_not_prime_88 h
  else if h : n = 91 then
    exact ten_pow_two_pow_not_prime_91 h
  else if h : n = 93 then
    exact ten_pow_two_pow_not_prime_93 h
  else if h : n = 99 then
    exact ten_pow_two_pow_not_prime_99 h
  else if h : n = 102 then
    exact ten_pow_two_pow_not_prime_102 h
  else if h : n = 122 then
    exact ten_pow_two_pow_not_prime_122 h
  else if h : n = 124 then
    exact ten_pow_two_pow_not_prime_124 h
  else if h : n = 142 then
    exact ten_pow_two_pow_not_prime_142 h
  else if h : n = 143 then
    exact ten_pow_two_pow_not_prime_143 h
  else if h : n = 146 then
    exact ten_pow_two_pow_not_prime_146 h
  else if h : n = 157 then
    exact ten_pow_two_pow_not_prime_157 h
  else
    sorry

/--
The conjecture is equivalent to the claim that a(n) is not 10^(2^n) + 1 for any n,
which in turn is equivalent to the claim that, if 10^(2^n) + 1 is prime,
then either 4^(2^n) + 1 or 6^(2^n) + 1 is prime. - Charles R Greathouse IV, Nov 17 2024
-/
theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n hp
  match n with
  | 0 =>
    left
    norm_num
  | 1 =>
    left
    norm_num
  | 2 =>
    -- 4^{4}+1 = 257 is a Fermat prime
    left
    norm_num
  | 3 =>
    -- 4^{8}+1 = 65537 is a Fermat prime
    left
    norm_num
  | n + 4 =>
    exact (ten_pow_two_pow_not_prime_of_two_le (by omega) hp).elim
