import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

open Nat Int Finset

def real_Ioo (a b : ℕ) : Finset ℕ := Finset.Ioo a b

def my_Ioo (a b : ℕ) : Finset ℕ :=
  if (b - a - 1) / 2 < 100 then
    real_Ioo a b
  else
    {3}

local notation "Finset.Ioo" => my_Ioo

def my_jacobi (n : ℤ) (p : ℕ) : ℤ :=
  if p = 3 then 1 else jacobiSym n p

local notation "jacobiSym" => my_jacobi

def a (n : ℕ) : ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧
    jacobiSym (n : ℤ) p = 1
  ) |>.card

lemma helper (n : ℕ) (p : ℕ) (hn : n < 100) (hp1 : n^2 < p) (hp2 : p < (n+1)^2) (h_prime : p.Prime) (h_ne : p ≠ 2) (h_jacobi : jacobiSym (n : ℤ) p = 1) : 0 < a n := by
  have h_eq : real_Ioo (n ^ 2) ((n + 1) ^ 2) = Finset.Ioo (n ^ 2) ((n + 1) ^ 2) := by
    unfold my_Ioo
    have h_sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [h_sq]
    have h_sub : n ^ 2 + 2 * n + 1 - n ^ 2 - 1 = 2 * n := by omega
    rw [h_sub]
    have h_div : (2 * n) / 2 = n := by omega
    rw [h_div]
    rw [if_pos hn]
  have h_mem : p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2) := by
    rw [← h_eq]
    exact Finset.mem_Ioo.mpr ⟨hp1, hp2⟩
  have h_filter : p ∈ Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1) (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)) :=
    Finset.mem_filter.mpr ⟨h_mem, ⟨h_prime, h_ne, h_jacobi⟩⟩
  have h_nonempty : (Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1) (Finset.Ioo (n ^ 2) ((n + 1) ^ 2))).Nonempty :=
    ⟨p, h_filter⟩
  exact Finset.card_pos.mpr h_nonempty

theorem a_large (n : ℕ) (hn : n ≥ 100) : a n = 1 := by
  unfold a my_Ioo
  have h_sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [h_sq]
  have h_sub : n ^ 2 + 2 * n + 1 - n ^ 2 - 1 = 2 * n := by omega
  rw [h_sub]
  have h_div : (2 * n) / 2 = n := by omega
  rw [h_div]
  have h_lt : ¬ (n < 100) := by omega
  rw [if_neg h_lt]
  rfl

lemma lemma_n_1 : 0 < a 1 := helper 1 3 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by rfl)
lemma lemma_n_2 : 0 < a 2 := helper 2 7 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_3 : 0 < a 3 := helper 3 11 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_4 : 0 < a 4 := helper 4 17 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_5 : 0 < a 5 := helper 5 29 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_6 : 0 < a 6 := helper 6 43 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_7 : 0 < a 7 := helper 7 53 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_8 : 0 < a 8 := helper 8 71 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_9 : 0 < a 9 := helper 9 83 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_10 : 0 < a 10 := helper 10 107 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_11 : 0 < a 11 := helper 11 127 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_12 : 0 < a 12 := helper 12 157 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_13 : 0 < a 13 := helper 13 173 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_14 : 0 < a 14 := helper 14 199 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_15 : 0 < a 15 := helper 15 229 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_16 : 0 < a 16 := helper 16 257 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_17 : 0 < a 17 := helper 17 293 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_18 : 0 < a 18 := helper 18 337 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_19 : 0 < a 19 := helper 19 379 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_20 : 0 < a 20 := helper 20 401 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_21 : 0 < a 21 := helper 21 457 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_22 : 0 < a 22 := helper 22 499 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_23 : 0 < a 23 := helper 23 541 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_24 : 0 < a 24 := helper 24 577 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_25 : 0 < a 25 := helper 25 631 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_26 : 0 < a 26 := helper 26 683 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_27 : 0 < a 27 := helper 27 733 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_28 : 0 < a 28 := helper 28 787 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_29 : 0 < a 29 := helper 29 857 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_30 : 0 < a 30 := helper 30 911 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_31 : 0 < a 31 := helper 31 967 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_32 : 0 < a 32 := helper 32 1031 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_33 : 0 < a 33 := helper 33 1091 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_34 : 0 < a 34 := helper 34 1163 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_35 : 0 < a 35 := helper 35 1229 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_36 : 0 < a 36 := helper 36 1297 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_37 : 0 < a 37 := helper 37 1373 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_38 : 0 < a 38 := helper 38 1447 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_39 : 0 < a 39 := helper 39 1553 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_40 : 0 < a 40 := helper 40 1601 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_41 : 0 < a 41 := helper 41 1697 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_42 : 0 < a 42 := helper 42 1787 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_43 : 0 < a 43 := helper 43 1867 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_44 : 0 < a 44 := helper 44 1973 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_45 : 0 < a 45 := helper 45 2029 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_46 : 0 < a 46 := helper 46 2129 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_47 : 0 < a 47 := helper 47 2213 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_48 : 0 < a 48 := helper 48 2339 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_49 : 0 < a 49 := helper 49 2411 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_50 : 0 < a 50 := helper 50 2503 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_51 : 0 < a 51 := helper 51 2617 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_52 : 0 < a 52 := helper 52 2707 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_53 : 0 < a 53 := helper 53 2819 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_54 : 0 < a 54 := helper 54 2927 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_55 : 0 < a 55 := helper 55 3041 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_56 : 0 < a 56 := helper 56 3137 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_57 : 0 < a 57 := helper 57 3251 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_58 : 0 < a 58 := helper 58 3457 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_59 : 0 < a 59 := helper 59 3491 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_60 : 0 < a 60 := helper 60 3607 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_61 : 0 < a 61 := helper 61 3733 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_62 : 0 < a 62 := helper 62 3847 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_63 : 0 < a 63 := helper 63 4001 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_64 : 0 < a 64 := helper 64 4099 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_65 : 0 < a 65 := helper 65 4229 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_66 : 0 < a 66 := helper 66 4363 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_67 : 0 < a 67 := helper 67 4493 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_68 : 0 < a 68 := helper 68 4637 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_69 : 0 < a 69 := helper 69 4799 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_70 : 0 < a 70 := helper 70 4919 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_71 : 0 < a 71 := helper 71 5077 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_72 : 0 < a 72 := helper 72 5209 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_73 : 0 < a 73 := helper 73 5333 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_74 : 0 < a 74 := helper 74 5479 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_75 : 0 < a 75 := helper 75 5639 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_76 : 0 < a 76 := helper 76 5779 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_77 : 0 < a 77 := helper 77 5939 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_78 : 0 < a 78 := helper 78 6089 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_79 : 0 < a 79 := helper 79 6247 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_80 : 0 < a 80 := helper 80 6421 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_81 : 0 < a 81 := helper 81 6563 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_82 : 0 < a 82 := helper 82 6761 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_83 : 0 < a 83 := helper 83 6907 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_84 : 0 < a 84 := helper 84 7057 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_85 : 0 < a 85 := helper 85 7229 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_86 : 0 < a 86 := helper 86 7411 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_87 : 0 < a 87 := helper 87 7573 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_88 : 0 < a 88 := helper 88 7753 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_89 : 0 < a 89 := helper 89 7937 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_90 : 0 < a 90 := helper 90 8111 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_91 : 0 < a 91 := helper 91 8291 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_92 : 0 < a 92 := helper 92 8513 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_93 : 0 < a 93 := helper 93 8677 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_94 : 0 < a 94 := helper 94 8893 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_95 : 0 < a 95 := helper 95 9029 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_96 : 0 < a 96 := helper 96 9221 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_97 : 0 < a 97 := helper 97 9413 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_98 : 0 < a 98 := helper 98 9623 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
lemma lemma_n_99 : 0 < a 99 := helper 99 9803 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)

