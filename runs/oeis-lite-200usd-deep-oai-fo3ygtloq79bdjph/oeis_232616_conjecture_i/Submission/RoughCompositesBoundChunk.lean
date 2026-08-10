import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.all false

open Nat Finset Classical

def pAt : Nat → Nat
| 0 => 2
| 1 => 3
| 2 => 5
| 3 => 7
| 4 => 11
| 5 => 13
| 6 => 17
| 7 => 19
| 8 => 23
| 9 => 29
| 10 => 31
| 11 => 37
| 12 => 41
| 13 => 43
| 14 => 47
| 15 => 53
| 16 => 59
| 17 => 61
| 18 => 67
| 19 => 71
| 20 => 73
| 21 => 79
| 22 => 83
| 23 => 89
| 24 => 97
| 25 => 101
| 26 => 103
| 27 => 107
| 28 => 109
| 29 => 113
| 30 => 127
| 31 => 131
| 32 => 137
| 33 => 139
| 34 => 149
| 35 => 151
| 36 => 157
| 37 => 163
| 38 => 167
| 39 => 173
| 40 => 179
| 41 => 181
| 42 => 191
| 43 => 193
| 44 => 197
| 45 => 199
| 46 => 211
| 47 => 223
| _ => 2

def RoughSet (X a : Nat) : Finset Nat :=
  (Finset.Icc 1 X).filter fun n => ∀ i, i < a → ¬ pAt i ∣ n

def noDivFrom (n d : Nat) : Nat → Bool
| 0 => true
| k+1 => (n % d != 0) && noDivFrom n (d+1) k


def isPrimeOver (n : Nat) : Bool := (2 <= n) && noDivFrom n 2 100

lemma noDivFrom_of_prime_ge_aux {n : Nat} (hp : Nat.Prime n) :
    ∀ k d : Nat, 2 ≤ d → d + k < n → noDivFrom n d k = true
| 0, d, hd2, hlt => by simp [noDivFrom]
| k+1, d, hd2, hlt => by
    simp only [noDivFrom]
    have hdn : d < n := by omega
    have hnotdvd : ¬ d ∣ n := by
      intro hdvd
      rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · omega
    have hmod : n % d ≠ 0 := by
      intro hzero
      exact hnotdvd (Nat.dvd_of_mod_eq_zero hzero)
    have hrec : noDivFrom n (d + 1) k = true := by
      exact noDivFrom_of_prime_ge_aux hp k (d+1) (by omega) (by omega)
    simp [hmod, hrec]

lemma isPrimeOver_of_prime_ge {n : Nat} (hp : Nat.Prime n) (hge : 227 ≤ n) :
    isPrimeOver n = true := by
  have hn2 : 2 ≤ n := by omega
  have hno : noDivFrom n 2 100 = true := by
    exact noDivFrom_of_prime_ge_aux hp 100 2 (by omega) (by omega)
  simp [isPrimeOver, hn2, hno]


def countSmallCore (s : Nat) : Nat → Nat
| 0 => 0
| k+1 => countSmallCore s k + if isPrimeOver (s+k) then 1 else 0

def countSmallChunks (s len : Nat) : Nat → Nat
| 0 => countSmallCore s len
| fuel+1 =>
    if len ≤ 100 then countSmallCore s len
    else countSmallCore s 100 + countSmallChunks (s + 100) (len - 100) fuel

def countSmall (s len : Nat) : Nat := countSmallChunks s len len

lemma countSmallCore_eq_count (s len : Nat) :
    countSmallCore s len = Nat.count (fun k => isPrimeOver (s + k) = true) len := by
  induction len with
  | zero => simp [countSmallCore]
  | succ len ih =>
      rw [Nat.count_succ]
      simp [countSmallCore, ih]

lemma countSmallChunks_eq_count (s len fuel : Nat) (hbound : len ≤ 100 * (fuel + 1)) :
    countSmallChunks s len fuel = Nat.count (fun k => isPrimeOver (s + k) = true) len := by
  induction fuel generalizing s len with
  | zero =>
      have hle : len ≤ 100 := by omega
      simp [countSmallChunks, hle, countSmallCore_eq_count]
  | succ fuel ih =>
      rw [countSmallChunks]
      by_cases hle : len ≤ 100
      · simp [hle, countSmallCore_eq_count]
      · have hlt : len - 100 ≤ 100 * (fuel + 1) := by omega
        have hsplit : len = 100 + (len - 100) := by omega
        simp [hle, countSmallCore_eq_count, ih (s + 100) (len - 100) hlt]
        rw [hsplit, Nat.count_add]
        simp [Nat.add_assoc]

lemma countSmall_eq_count (s len : Nat) :
    countSmall s len = Nat.count (fun k => isPrimeOver (s + k) = true) len := by
  unfold countSmall
  exact countSmallChunks_eq_count s len len (by nlinarith)

lemma card_primes_Ico_eq_count (s len : Nat) :
    ((Finset.Ico s (s + len)).filter Nat.Prime).card =
      Nat.count (fun k => Nat.Prime (s + k)) len := by
  induction len with
  | zero => simp
  | succ len ih =>
      rw [Nat.count_succ]
      have hle : s ≤ s + len := by omega
      have hnot : s + len ∉ Finset.Ico s (s + len) := by simp
      rw [show s + (len + 1) = (s + len).succ by omega]
      rw [Nat.Ico_succ_right_eq_insert_Ico hle]
      rw [Finset.filter_insert]
      by_cases hp : Nat.Prime (s + len)
      · simp [hp, hnot, ih]
      · simp [hp, ih]

lemma card_primes_Ico_le_countSmall (s len : Nat) (hs : 227 ≤ s) :
    ((Finset.Ico s (s + len)).filter Nat.Prime).card ≤ countSmall s len := by
  rw [card_primes_Ico_eq_count, countSmall_eq_count]
  apply Nat.count_mono_left
  intro k hk hp
  exact isPrimeOver_of_prime_ge hp (by omega)

lemma count_interval_p_0 : countSmall 227 50 = 10 := by decide
lemma count_interval_p_1 : countSmall 277 50 = 8 := by decide
lemma count_interval_p_2 : countSmall 327 50 = 8 := by decide
lemma count_interval_p_3 : countSmall 377 50 = 8 := by decide
lemma count_interval_p_4 : countSmall 427 50 = 9 := by decide
lemma count_interval_p_5 : countSmall 477 50 = 8 := by decide
lemma count_interval_p_6 : countSmall 527 50 = 6 := by decide
lemma count_interval_p_7 : countSmall 577 50 = 9 := by decide
lemma count_interval_p_8 : countSmall 627 50 = 8 := by decide
lemma count_interval_p_9 : countSmall 677 50 = 6 := by decide
lemma count_interval_p_10 : countSmall 727 50 = 9 := by decide
lemma count_interval_p_11 : countSmall 777 50 = 6 := by decide
lemma count_interval_p_12 : countSmall 827 50 = 7 := by decide
lemma count_interval_p_13 : countSmall 877 50 = 7 := by decide
lemma count_interval_p_14 : countSmall 927 50 = 7 := by decide
lemma count_interval_p_15 : countSmall 977 50 = 8 := by decide
lemma count_interval_p_16 : countSmall 1027 50 = 8 := by decide
lemma count_interval_p_17 : countSmall 1077 50 = 8 := by decide
lemma count_interval_p_18 : countSmall 1127 50 = 5 := by decide
lemma count_interval_p_19 : countSmall 1177 50 = 7 := by decide
lemma count_interval_p_20 : countSmall 1227 50 = 5 := by decide
lemma count_interval_p_21 : countSmall 1277 50 = 11 := by decide
lemma count_interval_p_22 : countSmall 1327 50 = 4 := by decide
lemma count_interval_p_23 : countSmall 1377 50 = 4 := by decide
lemma count_interval_p_24 : countSmall 1427 50 = 9 := by decide
lemma count_interval_p_25 : countSmall 1477 50 = 8 := by decide
lemma count_interval_p_26 : countSmall 1527 50 = 7 := by decide
lemma count_interval_p_27 : countSmall 1577 50 = 9 := by decide
lemma count_interval_p_28 : countSmall 1627 50 = 6 := by decide
lemma count_interval_p_29 : countSmall 1677 50 = 6 := by decide
lemma count_interval_p_30 : countSmall 1727 50 = 5 := by decide
lemma count_interval_p_31 : countSmall 1777 50 = 7 := by decide
lemma count_interval_p_32 : countSmall 1827 50 = 6 := by decide
lemma count_interval_p_33 : countSmall 1877 50 = 6 := by decide
lemma count_interval_p_34 : countSmall 1927 50 = 5 := by decide
lemma count_interval_p_35 : countSmall 1977 50 = 8 := by decide
lemma count_interval_p_36 : countSmall 2027 50 = 6 := by decide
lemma count_interval_p_37 : countSmall 2077 50 = 7 := by decide
lemma count_interval_p_38 : countSmall 2127 50 = 7 := by decide
lemma count_interval_p_39 : countSmall 2177 50 = 5 := by decide
lemma count_interval_p_40 : countSmall 2227 50 = 7 := by decide
lemma count_interval_p_41 : countSmall 2277 50 = 6 := by decide
lemma count_interval_p_42 : countSmall 2327 50 = 7 := by decide
lemma count_interval_p_43 : countSmall 2377 50 = 9 := by decide
lemma count_interval_p_44 : countSmall 2427 50 = 6 := by decide
lemma count_interval_p_45 : countSmall 2477 50 = 3 := by decide
lemma count_interval_p_46 : countSmall 2527 50 = 6 := by decide
lemma count_interval_p_47 : countSmall 2577 50 = 6 := by decide
lemma count_interval_p_48 : countSmall 2627 50 = 6 := by decide
lemma count_interval_p_49 : countSmall 2677 50 = 10 := by decide
lemma count_interval_p_50 : countSmall 2727 50 = 6 := by decide
lemma count_interval_p_51 : countSmall 2777 50 = 7 := by decide
lemma count_interval_p_52 : countSmall 2827 50 = 6 := by decide
lemma count_interval_p_53 : countSmall 2877 50 = 6 := by decide
lemma count_interval_p_54 : countSmall 2927 1 = 1 := by decide
lemma count_interval_q_0 : countSmall 227 37518 = 4326 := by decide
lemma count_interval_q_1 : countSmall 277 30655 = 3523 := by decide
lemma count_interval_q_2 : countSmall 327 25875 = 2976 := by decide
lemma count_interval_q_3 : countSmall 377 22350 = 2573 := by decide
lemma count_interval_q_4 : countSmall 427 19639 = 2260 := by decide
lemma count_interval_q_5 : countSmall 477 17486 = 2018 := by decide
lemma count_interval_q_6 : countSmall 527 15731 = 1823 := by decide
lemma count_interval_q_7 : countSmall 577 14273 = 1655 := by decide
lemma count_interval_q_8 : countSmall 627 13039 = 1512 := by decide
lemma count_interval_q_9 : countSmall 677 11979 = 1399 := by decide
lemma count_interval_q_10 : countSmall 727 11059 = 1290 := by decide
lemma count_interval_q_11 : countSmall 777 10250 = 1201 := by decide
lemma count_interval_q_12 : countSmall 827 9534 = 1128 := by decide
lemma count_interval_q_13 : countSmall 877 8893 = 1055 := by decide
lemma count_interval_q_14 : countSmall 927 8316 = 989 := by decide
lemma count_interval_q_15 : countSmall 977 7793 = 929 := by decide
lemma count_interval_q_16 : countSmall 1027 7316 = 873 := by decide
lemma count_interval_q_17 : countSmall 1077 6879 = 825 := by decide
lemma count_interval_q_18 : countSmall 1127 6476 = 777 := by decide
lemma count_interval_q_19 : countSmall 1177 6103 = 735 := by decide
lemma count_interval_q_20 : countSmall 1227 5756 = 697 := by decide
lemma count_interval_q_21 : countSmall 1277 5433 = 661 := by decide
lemma count_interval_q_22 : countSmall 1327 5130 = 622 := by decide
lemma count_interval_q_23 : countSmall 1377 4846 = 590 := by decide
lemma count_interval_q_24 : countSmall 1427 4578 = 559 := by decide
lemma count_interval_q_25 : countSmall 1477 4324 = 527 := by decide
lemma count_interval_q_26 : countSmall 1527 4084 = 497 := by decide
lemma count_interval_q_27 : countSmall 1577 3857 = 469 := by decide
lemma count_interval_q_28 : countSmall 1627 3640 = 441 := by decide
lemma count_interval_q_29 : countSmall 1677 3433 = 420 := by decide
lemma count_interval_q_30 : countSmall 1727 3235 = 394 := by decide
lemma count_interval_q_31 : countSmall 1777 3045 = 375 := by decide
lemma count_interval_q_32 : countSmall 1827 2863 = 352 := by decide
lemma count_interval_q_33 : countSmall 1877 2688 = 331 := by decide
lemma count_interval_q_34 : countSmall 1927 2520 = 310 := by decide
lemma count_interval_q_35 : countSmall 1977 2357 = 293 := by decide
lemma count_interval_q_36 : countSmall 2027 2200 = 272 := by decide
lemma count_interval_q_37 : countSmall 2077 2049 = 254 := by decide
lemma count_interval_q_38 : countSmall 2127 1902 = 238 := by decide
lemma count_interval_q_39 : countSmall 2177 1759 = 220 := by decide
lemma count_interval_q_40 : countSmall 2227 1621 = 202 := by decide
lemma count_interval_q_41 : countSmall 2277 1486 = 185 := by decide
lemma count_interval_q_42 : countSmall 2327 1355 = 170 := by decide
lemma count_interval_q_43 : countSmall 2377 1228 = 152 := by decide
lemma count_interval_q_44 : countSmall 2427 1104 = 133 := by decide
lemma count_interval_q_45 : countSmall 2477 983 = 117 := by decide
lemma count_interval_q_46 : countSmall 2527 864 = 108 := by decide
lemma count_interval_q_47 : countSmall 2577 748 = 93 := by decide
lemma count_interval_q_48 : countSmall 2627 635 = 80 := by decide
lemma count_interval_q_49 : countSmall 2677 524 = 65 := by decide
lemma count_interval_q_50 : countSmall 2727 415 = 49 := by decide
lemma count_interval_q_51 : countSmall 2777 309 = 38 := by decide
lemma count_interval_q_52 : countSmall 2827 204 = 24 := by decide
lemma count_interval_q_53 : countSmall 2877 102 = 13 := by decide
lemma count_interval_q_54 : countSmall 2927 1 = 1 := by decide
def RoughComposites : Finset Nat :=
  (RoughSet 8567964 48).filter (fun n => n ≠ 1 ∧ ¬ Nat.Prime n)

def blockStart (j : Nat) : Nat := 227 + 50 * j
def pLen (j : Nat) : Nat := if j = 54 then 1 else 50
def qLen (j : Nat) : Nat := 8567964 / blockStart j - blockStart j + 1
def pCert : Nat -> Nat
| 0 => 10
| 1 => 8
| 2 => 8
| 3 => 8
| 4 => 9
| 5 => 8
| 6 => 6
| 7 => 9
| 8 => 8
| 9 => 6
| 10 => 9
| 11 => 6
| 12 => 7
| 13 => 7
| 14 => 7
| 15 => 8
| 16 => 8
| 17 => 8
| 18 => 5
| 19 => 7
| 20 => 5
| 21 => 11
| 22 => 4
| 23 => 4
| 24 => 9
| 25 => 8
| 26 => 7
| 27 => 9
| 28 => 6
| 29 => 6
| 30 => 5
| 31 => 7
| 32 => 6
| 33 => 6
| 34 => 5
| 35 => 8
| 36 => 6
| 37 => 7
| 38 => 7
| 39 => 5
| 40 => 7
| 41 => 6
| 42 => 7
| 43 => 9
| 44 => 6
| 45 => 3
| 46 => 6
| 47 => 6
| 48 => 6
| 49 => 10
| 50 => 6
| 51 => 7
| 52 => 6
| 53 => 6
| 54 => 1
| _ => 0
def qCert : Nat -> Nat
| 0 => 4326
| 1 => 3523
| 2 => 2976
| 3 => 2573
| 4 => 2260
| 5 => 2018
| 6 => 1823
| 7 => 1655
| 8 => 1512
| 9 => 1399
| 10 => 1290
| 11 => 1201
| 12 => 1128
| 13 => 1055
| 14 => 989
| 15 => 929
| 16 => 873
| 17 => 825
| 18 => 777
| 19 => 735
| 20 => 697
| 21 => 661
| 22 => 622
| 23 => 590
| 24 => 559
| 25 => 527
| 26 => 497
| 27 => 469
| 28 => 441
| 29 => 420
| 30 => 394
| 31 => 375
| 32 => 352
| 33 => 331
| 34 => 310
| 35 => 293
| 36 => 272
| 37 => 254
| 38 => 238
| 39 => 220
| 40 => 202
| 41 => 185
| 42 => 170
| 43 => 152
| 44 => 133
| 45 => 117
| 46 => 108
| 47 => 93
| 48 => 80
| 49 => 65
| 50 => 49
| 51 => 38
| 52 => 24
| 53 => 13
| 54 => 1
| _ => 0

def PBlock (j : Nat) : Finset Nat := ((Finset.Ico (blockStart j) (blockStart j + pLen j)).filter Nat.Prime)
def QBlock (j : Nat) : Finset Nat := ((Finset.Ico (blockStart j) (blockStart j + qLen j)).filter (fun q => isPrimeOver q = true))
def AllPairs : Finset (Sigma fun _j : Nat => Nat × Nat) :=
  (Finset.range 55).sigma (fun j => (PBlock j).product (QBlock j))

lemma prime_lt_227_mem_pAt {p : Nat} (hp : Nat.Prime p) (hlt : p < 227) :
    ∃ i, i < 48 ∧ pAt i = p := by
  interval_cases p <;> try norm_num at hp
  · exact ⟨0, by norm_num, by norm_num [pAt]⟩
  · exact ⟨1, by norm_num, by norm_num [pAt]⟩
  · exact ⟨2, by norm_num, by norm_num [pAt]⟩
  · exact ⟨3, by norm_num, by norm_num [pAt]⟩
  · exact ⟨4, by norm_num, by norm_num [pAt]⟩
  · exact ⟨5, by norm_num, by norm_num [pAt]⟩
  · exact ⟨6, by norm_num, by norm_num [pAt]⟩
  · exact ⟨7, by norm_num, by norm_num [pAt]⟩
  · exact ⟨8, by norm_num, by norm_num [pAt]⟩
  · exact ⟨9, by norm_num, by norm_num [pAt]⟩
  · exact ⟨10, by norm_num, by norm_num [pAt]⟩
  · exact ⟨11, by norm_num, by norm_num [pAt]⟩
  · exact ⟨12, by norm_num, by norm_num [pAt]⟩
  · exact ⟨13, by norm_num, by norm_num [pAt]⟩
  · exact ⟨14, by norm_num, by norm_num [pAt]⟩
  · exact ⟨15, by norm_num, by norm_num [pAt]⟩
  · exact ⟨16, by norm_num, by norm_num [pAt]⟩
  · exact ⟨17, by norm_num, by norm_num [pAt]⟩
  · exact ⟨18, by norm_num, by norm_num [pAt]⟩
  · exact ⟨19, by norm_num, by norm_num [pAt]⟩
  · exact ⟨20, by norm_num, by norm_num [pAt]⟩
  · exact ⟨21, by norm_num, by norm_num [pAt]⟩
  · exact ⟨22, by norm_num, by norm_num [pAt]⟩
  · exact ⟨23, by norm_num, by norm_num [pAt]⟩
  · exact ⟨24, by norm_num, by norm_num [pAt]⟩
  · exact ⟨25, by norm_num, by norm_num [pAt]⟩
  · exact ⟨26, by norm_num, by norm_num [pAt]⟩
  · exact ⟨27, by norm_num, by norm_num [pAt]⟩
  · exact ⟨28, by norm_num, by norm_num [pAt]⟩
  · exact ⟨29, by norm_num, by norm_num [pAt]⟩
  · exact ⟨30, by norm_num, by norm_num [pAt]⟩
  · exact ⟨31, by norm_num, by norm_num [pAt]⟩
  · exact ⟨32, by norm_num, by norm_num [pAt]⟩
  · exact ⟨33, by norm_num, by norm_num [pAt]⟩
  · exact ⟨34, by norm_num, by norm_num [pAt]⟩
  · exact ⟨35, by norm_num, by norm_num [pAt]⟩
  · exact ⟨36, by norm_num, by norm_num [pAt]⟩
  · exact ⟨37, by norm_num, by norm_num [pAt]⟩
  · exact ⟨38, by norm_num, by norm_num [pAt]⟩
  · exact ⟨39, by norm_num, by norm_num [pAt]⟩
  · exact ⟨40, by norm_num, by norm_num [pAt]⟩
  · exact ⟨41, by norm_num, by norm_num [pAt]⟩
  · exact ⟨42, by norm_num, by norm_num [pAt]⟩
  · exact ⟨43, by norm_num, by norm_num [pAt]⟩
  · exact ⟨44, by norm_num, by norm_num [pAt]⟩
  · exact ⟨45, by norm_num, by norm_num [pAt]⟩
  · exact ⟨46, by norm_num, by norm_num [pAt]⟩
  · exact ⟨47, by norm_num, by norm_num [pAt]⟩

lemma count_p_block (j : Nat) (hj : j < 55) :
    countSmall (blockStart j) (pLen j) = pCert j := by
  interval_cases j <;> simp [blockStart, pLen, pCert, count_interval_p_0, count_interval_p_1, count_interval_p_2, count_interval_p_3, count_interval_p_4, count_interval_p_5, count_interval_p_6, count_interval_p_7, count_interval_p_8, count_interval_p_9, count_interval_p_10, count_interval_p_11, count_interval_p_12, count_interval_p_13, count_interval_p_14, count_interval_p_15, count_interval_p_16, count_interval_p_17, count_interval_p_18, count_interval_p_19, count_interval_p_20, count_interval_p_21, count_interval_p_22, count_interval_p_23, count_interval_p_24, count_interval_p_25, count_interval_p_26, count_interval_p_27, count_interval_p_28, count_interval_p_29, count_interval_p_30, count_interval_p_31, count_interval_p_32, count_interval_p_33, count_interval_p_34, count_interval_p_35, count_interval_p_36, count_interval_p_37, count_interval_p_38, count_interval_p_39, count_interval_p_40, count_interval_p_41, count_interval_p_42, count_interval_p_43, count_interval_p_44, count_interval_p_45, count_interval_p_46, count_interval_p_47, count_interval_p_48, count_interval_p_49, count_interval_p_50, count_interval_p_51, count_interval_p_52, count_interval_p_53, count_interval_p_54]

lemma count_q_block (j : Nat) (hj : j < 55) :
    countSmall (blockStart j) (qLen j) = qCert j := by
  interval_cases j <;> norm_num [blockStart, qLen, qCert, count_interval_q_0, count_interval_q_1, count_interval_q_2, count_interval_q_3, count_interval_q_4, count_interval_q_5, count_interval_q_6, count_interval_q_7, count_interval_q_8, count_interval_q_9, count_interval_q_10, count_interval_q_11, count_interval_q_12, count_interval_q_13, count_interval_q_14, count_interval_q_15, count_interval_q_16, count_interval_q_17, count_interval_q_18, count_interval_q_19, count_interval_q_20, count_interval_q_21, count_interval_q_22, count_interval_q_23, count_interval_q_24, count_interval_q_25, count_interval_q_26, count_interval_q_27, count_interval_q_28, count_interval_q_29, count_interval_q_30, count_interval_q_31, count_interval_q_32, count_interval_q_33, count_interval_q_34, count_interval_q_35, count_interval_q_36, count_interval_q_37, count_interval_q_38, count_interval_q_39, count_interval_q_40, count_interval_q_41, count_interval_q_42, count_interval_q_43, count_interval_q_44, count_interval_q_45, count_interval_q_46, count_interval_q_47, count_interval_q_48, count_interval_q_49, count_interval_q_50, count_interval_q_51, count_interval_q_52, count_interval_q_53, count_interval_q_54]

lemma cert_sum : (Finset.range 55).sum (fun j => pCert j * qCert j) = 335539 := by
  norm_num [pCert, qCert]

lemma card_isPrimeOver_Ico_eq_countSmall (s len : Nat) :
    ((Finset.Ico s (s + len)).filter (fun n => isPrimeOver n = true)).card = countSmall s len := by
  rw [countSmall_eq_count]
  induction len with
  | zero => simp
  | succ len ih =>
      rw [Nat.count_succ]
      have hle : s ≤ s + len := by omega
      have hnot : s + len ∉ Finset.Ico s (s + len) := by simp
      rw [show s + (len + 1) = (s + len).succ by omega]
      rw [Nat.Ico_succ_right_eq_insert_Ico hle]
      rw [Finset.filter_insert]
      by_cases hp : isPrimeOver (s + len) = true
      · simp [hp, hnot, ih]
      · simp [hp, ih]

lemma PBlock_card_le (j : Nat) (hj : j < 55) : (PBlock j).card ≤ pCert j := by
  have hs : 227 ≤ blockStart j := by simp [blockStart]
  have h := card_primes_Ico_le_countSmall (blockStart j) (pLen j) hs
  simpa [PBlock, count_p_block j hj] using h

lemma QBlock_card_le (j : Nat) (hj : j < 55) : (QBlock j).card ≤ qCert j := by
  rw [QBlock, card_isPrimeOver_Ico_eq_countSmall, count_q_block j hj]

lemma p_block_index_mem {p : Nat} (hpge : 227 ≤ p) (hple : p ≤ 2927) :
    let j := (p - 227) / 50
    j < 55 ∧ p ∈ Finset.Ico (blockStart j) (blockStart j + pLen j) := by
  intro j
  have hsub_eq : 227 + (p - 227) = p := by omega
  have hdecomp : p - 227 = 50 * j + (p - 227) % 50 := by
    have h := Nat.div_add_mod (p - 227) 50
    dsimp [j] at h
    omega
  have hmod : (p - 227) % 50 < 50 := Nat.mod_lt _ (by norm_num)
  have hsub_lt : p - 227 < 55 * 50 := by omega
  have hj : j < 55 := by
    dsimp [j]
    exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 50)).2 hsub_lt
  constructor
  · exact hj
  · rw [Finset.mem_Ico]
    by_cases h54 : j = 54
    · have hp_eq : p = 2927 := by
        have : 2700 ≤ p - 227 := by
          -- since j = 54, `p - 227 = 50*54 + r`.
          omega
        omega
      rw [hp_eq]
      simp [blockStart, pLen, h54]
    · have hlow : blockStart j ≤ p := by
        dsimp [blockStart]
        omega
      have hhi : p < blockStart j + pLen j := by
        have : p < blockStart j + 50 := by
          dsimp [blockStart]
          omega
        simp [pLen, h54]
        exact this
      exact ⟨hlow, hhi⟩

lemma minFac_ge_227_of_rough {n : Nat} (hn : n ∈ RoughComposites) : 227 ≤ n.minFac := by
  have hnR : n ∈ RoughSet 8567964 48 := (Finset.mem_filter.mp hn).1
  have hn_ne1 : n ≠ 1 := (Finset.mem_filter.mp hn).2.1
  have hp : Nat.Prime n.minFac := Nat.minFac_prime hn_ne1
  by_contra hlt_ge
  have hlt : n.minFac < 227 := by omega
  rcases prime_lt_227_mem_pAt hp hlt with ⟨i, hi, hpAt⟩
  have hnot := (Finset.mem_filter.mp hnR).2 i hi
  exact hnot (by rw [hpAt]; exact Nat.minFac_dvd n)

lemma minFac_le_2927_of_rough {n : Nat} (hn : n ∈ RoughComposites) : n.minFac ≤ 2927 := by
  have hnR : n ∈ RoughSet 8567964 48 := (Finset.mem_filter.mp hn).1
  have hnI := (Finset.mem_filter.mp hnR).1
  rw [Finset.mem_Icc] at hnI
  have hnpos : 0 < n := by omega
  have hn_notprime : ¬ Nat.Prime n := (Finset.mem_filter.mp hn).2.2
  have hsquare := Nat.minFac_sq_le_self hnpos hn_notprime
  nlinarith

lemma div_minFac_prime_of_rough {n : Nat} (hn : n ∈ RoughComposites) : Nat.Prime (n / n.minFac) := by
  let p := n.minFac
  let q := n / p
  have hnR : n ∈ RoughSet 8567964 48 := (Finset.mem_filter.mp hn).1
  have hnI := (Finset.mem_filter.mp hnR).1
  rw [Finset.mem_Icc] at hnI
  have hnpos : 0 < n := by omega
  have hn_ne1 : n ≠ 1 := (Finset.mem_filter.mp hn).2.1
  have hn_notprime : ¬ Nat.Prime n := (Finset.mem_filter.mp hn).2.2
  have hp : Nat.Prime p := by simpa [p] using Nat.minFac_prime hn_ne1
  have hpge : 227 ≤ p := by simpa [p] using minFac_ge_227_of_rough hn
  have hpdvd : p ∣ n := by simpa [p] using Nat.minFac_dvd n
  have hn_eq : p * q = n := by
    dsimp [q]
    rw [Nat.mul_comm]; exact Nat.div_mul_cancel hpdvd
  have hqge : p ≤ q := by simpa [p, q] using Nat.minFac_le_div hnpos hn_notprime
  by_contra hqnot
  have hq_ne1 : q ≠ 1 := by
    intro hq1
    have : p ≤ 1 := by simpa [hq1] using hqge
    omega
  have hrprime : Nat.Prime q.minFac := Nat.minFac_prime hq_ne1
  have hr2 : 2 ≤ q.minFac := hrprime.two_le
  have hrdvdq : q.minFac ∣ q := Nat.minFac_dvd q
  have hrdvdn : q.minFac ∣ n := by
    rw [← hn_eq]
    exact dvd_mul_of_dvd_right hrdvdq p
  have hple_r : p ≤ q.minFac := Nat.minFac_le_of_dvd hr2 hrdvdn
  have hq_square := Nat.minFac_sq_le_self (by omega : 0 < q) hqnot
  have hbig : 8567964 < n := by
    nlinarith
  omega


def roughPair (n : Nat) : Sigma fun _j : Nat => Nat × Nat :=
  Sigma.mk ((n.minFac - 227) / 50) ((n.minFac, n / n.minFac) : Nat × Nat)

lemma rough_mapsTo_AllPairs : Set.MapsTo
    roughPair
    (RoughComposites : Set Nat) (AllPairs : Set (Sigma fun _j : Nat => Nat × Nat)) := by
  intro n hn
  have hnF : n ∈ RoughComposites := hn
  have hpge : 227 ≤ n.minFac := minFac_ge_227_of_rough hnF
  have hple : n.minFac ≤ 2927 := minFac_le_2927_of_rough hnF
  have hpprime : Nat.Prime n.minFac := Nat.minFac_prime (Finset.mem_filter.mp hnF).2.1
  have hqprime : Nat.Prime (n / n.minFac) := div_minFac_prime_of_rough hnF
  let j := (n.minFac - 227) / 50
  have hblock := p_block_index_mem hpge hple
  dsimp only at hblock
  have hj : j < 55 := hblock.1
  have hpmemI : n.minFac ∈ Finset.Ico (blockStart j) (blockStart j + pLen j) := hblock.2
  have hqgeL : blockStart j ≤ n / n.minFac := by
    have hlow : blockStart j ≤ n.minFac := (Finset.mem_Ico.mp hpmemI).1
    have hqge : n.minFac ≤ n / n.minFac := by
      have hnR : n ∈ RoughSet 8567964 48 := (Finset.mem_filter.mp hnF).1
      have hnI := (Finset.mem_filter.mp hnR).1
      rw [Finset.mem_Icc] at hnI
      exact Nat.minFac_le_div (by omega) (Finset.mem_filter.mp hnF).2.2
    omega
  have hqle : n / n.minFac ≤ 8567964 / blockStart j := by
    have hnR : n ∈ RoughSet 8567964 48 := (Finset.mem_filter.mp hnF).1
    have hnI := (Finset.mem_filter.mp hnR).1
    rw [Finset.mem_Icc] at hnI
    have hLpos : 0 < blockStart j := by simp [blockStart]
    have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hn_eq : n.minFac * (n / n.minFac) = n := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hpdvd
    have hlow : blockStart j ≤ n.minFac := (Finset.mem_Ico.mp hpmemI).1
    apply (Nat.le_div_iff_mul_le hLpos).2
    calc
      blockStart j * (n / n.minFac) ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul_right _ hlow
      _ = n := hn_eq
      _ ≤ 8567964 := hnI.2
  have hqmemI : n / n.minFac ∈ Finset.Ico (blockStart j) (blockStart j + qLen j) := by
    rw [Finset.mem_Ico]
    constructor
    · exact hqgeL
    · dsimp [qLen]
      omega
  have hqbool : isPrimeOver (n / n.minFac) = true := isPrimeOver_of_prime_ge hqprime (by omega)
  rw [AllPairs]
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, PBlock, QBlock,
    Finset.mem_filter]
  exact ⟨hj, ⟨⟨hpmemI, hpprime⟩, ⟨hqmemI, hqbool⟩⟩⟩

lemma rough_pair_inj : (RoughComposites : Set Nat).InjOn
    roughPair := by
  intro n hn m hm h
  have hpndvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hpmdvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hp_eq : n.minFac = m.minFac := by
    exact congrArg (fun x : Sigma fun _j : Nat => Nat × Nat => x.2.1) h
  have hq_eq : n / n.minFac = m / m.minFac := by
    exact congrArg (fun x : Sigma fun _j : Nat => Nat × Nat => x.2.2) h
  calc
    n = n.minFac * (n / n.minFac) := (by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hpndvd).symm
    _ = m.minFac * (m / m.minFac) := by rw [hp_eq, hq_eq]
    _ = m := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hpmdvd

lemma rough_card_le_AllPairs : RoughComposites.card ≤ AllPairs.card := by
  exact Finset.card_le_card_of_injOn
    roughPair
    rough_mapsTo_AllPairs rough_pair_inj

lemma AllPairs_card_le_cert : AllPairs.card ≤ 335539 := by
  rw [AllPairs, Finset.card_sigma]
  calc
    (Finset.range 55).sum (fun j => ((PBlock j).product (QBlock j)).card)
        = (Finset.range 55).sum (fun j => (PBlock j).card * (QBlock j).card) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [Finset.card_product]
    _ ≤ (Finset.range 55).sum (fun j => pCert j * qCert j) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          exact Nat.mul_le_mul (PBlock_card_le j hj) (QBlock_card_le j hj)
    _ = 335539 := cert_sum

theorem rough_composites_card_le : RoughComposites.card ≤ 335539 := by
  exact le_trans rough_card_le_AllPairs AllPairs_card_le_cert

-- The rough-set cardinality certificate from the copied `phi_sound_223.lean` snippet is available too.
#check rough_composites_card_le
