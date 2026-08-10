import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
open Nat Finset BigOperators
open scoped Nat.Prime
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0
theorem np0 : Nat.nth Nat.Prime 0 = 2 := by
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by decide); rwa [hc] at h
theorem np1 : Nat.nth Nat.Prime 1 = 3 := by
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by decide); rwa [hc] at h
theorem np2 : Nat.nth Nat.Prime 2 = 5 := by
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by decide); rwa [hc] at h
theorem np3 : Nat.nth Nat.Prime 3 = 7 := by
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 7) (by decide); rwa [hc] at h
theorem np4 : Nat.nth Nat.Prime 4 = 11 := by
  have hc : Nat.count Nat.Prime 11 = 4 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 11) (by decide); rwa [hc] at h
theorem np5 : Nat.nth Nat.Prime 5 = 13 := by
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 13) (by decide); rwa [hc] at h
theorem np6 : Nat.nth Nat.Prime 6 = 17 := by
  have hc : Nat.count Nat.Prime 17 = 6 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 17) (by decide); rwa [hc] at h
theorem np7 : Nat.nth Nat.Prime 7 = 19 := by
  have hc : Nat.count Nat.Prime 19 = 7 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 19) (by decide); rwa [hc] at h
theorem np8 : Nat.nth Nat.Prime 8 = 23 := by
  have hc : Nat.count Nat.Prime 23 = 8 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 23) (by decide); rwa [hc] at h
theorem np9 : Nat.nth Nat.Prime 9 = 29 := by
  have hc : Nat.count Nat.Prime 29 = 9 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 29) (by decide); rwa [hc] at h
theorem np10 : Nat.nth Nat.Prime 10 = 31 := by
  have hc : Nat.count Nat.Prime 31 = 10 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 31) (by decide); rwa [hc] at h
theorem np11 : Nat.nth Nat.Prime 11 = 37 := by
  have hc : Nat.count Nat.Prime 37 = 11 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 37) (by decide); rwa [hc] at h
theorem np12 : Nat.nth Nat.Prime 12 = 41 := by
  have hc : Nat.count Nat.Prime 41 = 12 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 41) (by decide); rwa [hc] at h
theorem np13 : Nat.nth Nat.Prime 13 = 43 := by
  have hc : Nat.count Nat.Prime 43 = 13 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 43) (by decide); rwa [hc] at h
theorem np14 : Nat.nth Nat.Prime 14 = 47 := by
  have hc : Nat.count Nat.Prime 47 = 14 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 47) (by decide); rwa [hc] at h
theorem np15 : Nat.nth Nat.Prime 15 = 53 := by
  have hc : Nat.count Nat.Prime 53 = 15 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 53) (by decide); rwa [hc] at h
theorem np16 : Nat.nth Nat.Prime 16 = 59 := by
  have hc : Nat.count Nat.Prime 59 = 16 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 59) (by decide); rwa [hc] at h
theorem np17 : Nat.nth Nat.Prime 17 = 61 := by
  have hc : Nat.count Nat.Prime 61 = 17 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 61) (by decide); rwa [hc] at h
theorem np18 : Nat.nth Nat.Prime 18 = 67 := by
  have hc : Nat.count Nat.Prime 67 = 18 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 67) (by decide); rwa [hc] at h
theorem np19 : Nat.nth Nat.Prime 19 = 71 := by
  have hc : Nat.count Nat.Prime 71 = 19 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 71) (by decide); rwa [hc] at h
theorem np20 : Nat.nth Nat.Prime 20 = 73 := by
  have hc : Nat.count Nat.Prime 73 = 20 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 73) (by decide); rwa [hc] at h
theorem np21 : Nat.nth Nat.Prime 21 = 79 := by
  have hc : Nat.count Nat.Prime 79 = 21 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 79) (by decide); rwa [hc] at h
theorem np22 : Nat.nth Nat.Prime 22 = 83 := by
  have hc : Nat.count Nat.Prime 83 = 22 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 83) (by decide); rwa [hc] at h
theorem np23 : Nat.nth Nat.Prime 23 = 89 := by
  have hc : Nat.count Nat.Prime 89 = 23 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 89) (by decide); rwa [hc] at h
theorem np24 : Nat.nth Nat.Prime 24 = 97 := by
  have hc : Nat.count Nat.Prime 97 = 24 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 97) (by decide); rwa [hc] at h
theorem np25 : Nat.nth Nat.Prime 25 = 101 := by
  have hc : Nat.count Nat.Prime 101 = 25 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 101) (by decide); rwa [hc] at h
theorem np26 : Nat.nth Nat.Prime 26 = 103 := by
  have hc : Nat.count Nat.Prime 103 = 26 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 103) (by decide); rwa [hc] at h
theorem np27 : Nat.nth Nat.Prime 27 = 107 := by
  have hc : Nat.count Nat.Prime 107 = 27 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 107) (by decide); rwa [hc] at h
theorem np28 : Nat.nth Nat.Prime 28 = 109 := by
  have hc : Nat.count Nat.Prime 109 = 28 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 109) (by decide); rwa [hc] at h
theorem np29 : Nat.nth Nat.Prime 29 = 113 := by
  have hc : Nat.count Nat.Prime 113 = 29 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 113) (by decide); rwa [hc] at h
theorem np30 : Nat.nth Nat.Prime 30 = 127 := by
  have hc : Nat.count Nat.Prime 127 = 30 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 127) (by decide); rwa [hc] at h
theorem np31 : Nat.nth Nat.Prime 31 = 131 := by
  have hc : Nat.count Nat.Prime 131 = 31 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 131) (by decide); rwa [hc] at h
theorem np32 : Nat.nth Nat.Prime 32 = 137 := by
  have hc : Nat.count Nat.Prime 137 = 32 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 137) (by decide); rwa [hc] at h
theorem np33 : Nat.nth Nat.Prime 33 = 139 := by
  have hc : Nat.count Nat.Prime 139 = 33 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 139) (by decide); rwa [hc] at h
theorem np34 : Nat.nth Nat.Prime 34 = 149 := by
  have hc : Nat.count Nat.Prime 149 = 34 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 149) (by decide); rwa [hc] at h
theorem np35 : Nat.nth Nat.Prime 35 = 151 := by
  have hc : Nat.count Nat.Prime 151 = 35 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 151) (by decide); rwa [hc] at h
theorem np36 : Nat.nth Nat.Prime 36 = 157 := by
  have hc : Nat.count Nat.Prime 157 = 36 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 157) (by decide); rwa [hc] at h
theorem np37 : Nat.nth Nat.Prime 37 = 163 := by
  have hc : Nat.count Nat.Prime 163 = 37 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 163) (by decide); rwa [hc] at h
theorem np38 : Nat.nth Nat.Prime 38 = 167 := by
  have hc : Nat.count Nat.Prime 167 = 38 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 167) (by decide); rwa [hc] at h
theorem np39 : Nat.nth Nat.Prime 39 = 173 := by
  have hc : Nat.count Nat.Prime 173 = 39 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 173) (by decide); rwa [hc] at h
theorem np40 : Nat.nth Nat.Prime 40 = 179 := by
  have hc : Nat.count Nat.Prime 179 = 40 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 179) (by decide); rwa [hc] at h
theorem np41 : Nat.nth Nat.Prime 41 = 181 := by
  have hc : Nat.count Nat.Prime 181 = 41 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 181) (by decide); rwa [hc] at h
theorem np42 : Nat.nth Nat.Prime 42 = 191 := by
  have hc : Nat.count Nat.Prime 191 = 42 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 191) (by decide); rwa [hc] at h
theorem np43 : Nat.nth Nat.Prime 43 = 193 := by
  have hc : Nat.count Nat.Prime 193 = 43 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 193) (by decide); rwa [hc] at h
theorem ha1 : a 1 = 0 := by unfold a; simp
theorem ha2 : a 2 = 0 := by
  unfold a; rw [show Finset.Ico 1 2 = {1} from by decide,  Finset.sum_singleton]
  norm_num [np0, np1]
theorem ha3 : a 3 = 0 := by
  unfold a; rw [show Finset.Ico 1 3 = {1,2} from by decide, Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2]
theorem ha4 : a 4 = 1 := by
  unfold a; rw [show Finset.Ico 1 4 = {1,2,3} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3]
theorem ha5 : a 5 = 1 := by
  unfold a; rw [show Finset.Ico 1 5 = {1,2,3,4} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4]
theorem ha6 : a 6 = 0 := by
  unfold a; rw [show Finset.Ico 1 6 = {1,2,3,4,5} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5]
theorem ha7 : a 7 = 1 := by
  unfold a; rw [show Finset.Ico 1 7 = {1,2,3,4,5,6} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6]
theorem ha8 : a 8 = 2 := by
  unfold a; rw [show Finset.Ico 1 8 = {1,2,3,4,5,6,7} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7]
theorem ha9 : a 9 = 2 := by
  unfold a; rw [show Finset.Ico 1 9 = {1,2,3,4,5,6,7,8} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8]
theorem ha10 : a 10 = 1 := by
  unfold a; rw [show Finset.Ico 1 10 = {1,2,3,4,5,6,7,8,9} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9]
theorem ha11 : a 11 = 1 := by
  unfold a; rw [show Finset.Ico 1 11 = {1,2,3,4,5,6,7,8,9,10} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10]
theorem ha12 : a 12 = 1 := by
  unfold a; rw [show Finset.Ico 1 12 = {1,2,3,4,5,6,7,8,9,10,11} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11]
theorem ha13 : a 13 = 3 := by
  unfold a; rw [show Finset.Ico 1 13 = {1,2,3,4,5,6,7,8,9,10,11,12} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12]
theorem ha14 : a 14 = 2 := by
  unfold a; rw [show Finset.Ico 1 14 = {1,2,3,4,5,6,7,8,9,10,11,12,13} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13]
theorem ha15 : a 15 = 3 := by
  unfold a; rw [show Finset.Ico 1 15 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14]
theorem ha16 : a 16 = 2 := by
  unfold a; rw [show Finset.Ico 1 16 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15]
theorem ha17 : a 17 = 2 := by
  unfold a; rw [show Finset.Ico 1 17 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16]
theorem ha18 : a 18 = 3 := by
  unfold a; rw [show Finset.Ico 1 18 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17]
theorem ha19 : a 19 = 1 := by
  unfold a; rw [show Finset.Ico 1 19 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18]
theorem ha20 : a 20 = 5 := by
  unfold a; rw [show Finset.Ico 1 20 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19]
theorem ha21 : a 21 = 1 := by
  unfold a; rw [show Finset.Ico 1 21 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20]
theorem ha22 : a 22 = 1 := by
  unfold a; rw [show Finset.Ico 1 22 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21]
theorem ha23 : a 23 = 3 := by
  unfold a; rw [show Finset.Ico 1 23 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22]
theorem ha24 : a 24 = 2 := by
  unfold a; rw [show Finset.Ico 1 24 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23]
theorem ha25 : a 25 = 4 := by
  unfold a; rw [show Finset.Ico 1 25 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24]
theorem ha26 : a 26 = 5 := by
  unfold a; rw [show Finset.Ico 1 26 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25]
theorem ha27 : a 27 = 2 := by
  unfold a; rw [show Finset.Ico 1 27 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26]
theorem ha28 : a 28 = 4 := by
  unfold a; rw [show Finset.Ico 1 28 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27]
theorem ha29 : a 29 = 3 := by
  unfold a; rw [show Finset.Ico 1 29 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28]
theorem ha30 : a 30 = 4 := by
  unfold a; rw [show Finset.Ico 1 30 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29]
theorem ha31 : a 31 = 1 := by
  unfold a; rw [show Finset.Ico 1 31 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30]
theorem ha32 : a 32 = 4 := by
  unfold a; rw [show Finset.Ico 1 32 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31]
theorem ha33 : a 33 = 5 := by
  unfold a; rw [show Finset.Ico 1 33 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32]
theorem ha34 : a 34 = 3 := by
  unfold a; rw [show Finset.Ico 1 34 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33]
theorem ha35 : a 35 = 4 := by
  unfold a; rw [show Finset.Ico 1 35 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34]
theorem ha36 : a 36 = 6 := by
  unfold a; rw [show Finset.Ico 1 36 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35]
theorem ha37 : a 37 = 3 := by
  unfold a; rw [show Finset.Ico 1 37 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36]
theorem ha38 : a 38 = 2 := by
  unfold a; rw [show Finset.Ico 1 38 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37]
theorem ha39 : a 39 = 2 := by
  unfold a; rw [show Finset.Ico 1 39 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38]
theorem ha40 : a 40 = 2 := by
  unfold a; rw [show Finset.Ico 1 40 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39]
theorem ha41 : a 41 = 2 := by
  unfold a; rw [show Finset.Ico 1 41 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40]
theorem ha42 : a 42 = 1 := by
  unfold a; rw [show Finset.Ico 1 42 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41]
theorem ha43 : a 43 = 8 := by
  unfold a; rw [show Finset.Ico 1 43 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41, np42]
theorem ha44 : a 44 = 1 := by
  unfold a; rw [show Finset.Ico 1 44 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43} from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41, np42, np43]
theorem key : ∀ n : ℕ, 45 ≤ n → 2 ≤ a n := by
  sorry

theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases lt_or_ge n 45 with h | h
    · interval_cases n <;> simp_all [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24, ha25, ha26, ha27, ha28, ha29, ha30, ha31, ha32, ha33, ha34, ha35, ha36, ha37, ha38, ha39, ha40, ha41, ha42, ha43, ha44]
    · have hk := key n h
      refine ⟨fun _ hdvd => ?_, fun _ => ?_⟩
      · have hle := Nat.le_of_dvd (by norm_num) hdvd; omega
      · omega
  · intro n hn
    rcases lt_or_ge n 45 with h | h
    · interval_cases n <;> simp_all [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24, ha25, ha26, ha27, ha28, ha29, ha30, ha31, ha32, ha33, ha34, ha35, ha36, ha37, ha38, ha39, ha40, ha41, ha42, ha43, ha44]
    · have hk := key n h
      refine ⟨fun h1 => ?_, fun hmem => ?_⟩
      · omega
      · rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
