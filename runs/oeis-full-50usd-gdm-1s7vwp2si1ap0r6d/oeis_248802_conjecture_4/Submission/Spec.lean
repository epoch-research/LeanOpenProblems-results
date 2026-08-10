/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option profiler false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.ams_attribute false
set_option linter.style.answer_attribute false
set_option linter.style.category_docstring false
set_option linter.style.category_attribute false
set_option linter.style.existsImplication false
set_option linter.style.moduleDocstring false

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac


def c_term (n : ℕ) : ℕ := 2 ^ (2 ^ (58 * n + 26) + 2) + 3

-- Helper definitions for the "covered" conditions based on the index k, where k = 58*n + 26.

/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/
def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0, and m is not 1 mod 5, predicting a(k)=271. -/
def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0, and m is not 0 mod 5, predicting a(k)=523. -/
def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0

lemma pow_induction (d e o : ℕ) (h_base : (2 ^ d * 2 ^ e) % o = 2 ^ e % o) (j : ℕ) :
    ((2 ^ d) ^ j * 2 ^ e) % o = 2 ^ e % o := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
  | succ j ih =>
    have h_eq : (2 ^ d) ^ (j + 1) * 2 ^ e = (2 ^ d) ^ j * (2 ^ d * 2 ^ e) := by
      calc (2 ^ d) ^ (j + 1) * 2 ^ e
        _ = ((2 ^ d) ^ j * 2 ^ d) * 2 ^ e := by rw [pow_succ]
        _ = (2 ^ d) ^ j * (2 ^ d * 2 ^ e) := by ring
    rw [h_eq]
    rw [Nat.mul_mod]
    rw [h_base]
    rw [← Nat.mul_mod]
    exact ih

lemma pow_mod_of_mod_eq (n L r d e o : ℕ) (hd : d = 58 * L) (he : e = 58 * r + 26) (hn : n % L = r)
    (h_base : (2 ^ d * 2 ^ e) % o = 2 ^ e % o) :
    2 ^ (58 * n + 26) % o = 2 ^ (58 * r + 26) % o := by
  have h_div_mod := Nat.div_add_mod n L
  rw [hn] at h_div_mod
  have h_eq : 58 * n + 26 = d * (n / L) + e := by
    subst hd he
    have h_L : 58 * n + 26 = 58 * (L * (n / L) + r) + 26 := congr_arg (fun x => 58 * x + 26) h_div_mod.symm
    rw [h_L]
    ring
  rw [h_eq]
  rw [pow_add, pow_mul]
  have h_ind := pow_induction d e o h_base (n / L)
  rw [h_ind]
  subst he
  rfl

lemma dvd_mod_of_dvd_of_dvd (g a b : ℕ) (ha : g ∣ a) (hb : g ∣ b) : g ∣ a % b := by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  by_cases hb0 : kb = 0
  · subst hb0
    simp
  · have h_eq : (g * ka) % (g * kb) = g * (ka % kb) := Nat.mul_mod_mul_left g ka kb
    rw [h_eq]
    exact dvd_mul_right g (ka % kb)

lemma pow_two_mod_233 (n : ℕ) : (2 : ZMod 233) ^ (58 * n + 26) = 204 := by
  have h_eq : 58 * n + 26 = 29 * (2 * n) + 26 := by omega
  rw [h_eq]
  rw [pow_add, pow_mul]
  have h29 : (2 : ZMod 233) ^ 29 = 1 := by decide
  rw [h29]
  rw [one_pow]
  rw [one_mul]
  decide

lemma pow_two_mod_233_nat (n : ℕ) : 2 ^ (58 * n + 26) % 233 = 204 := by
  have h := pow_two_mod_233 n
  have h_val := congr_arg ZMod.val h
  have h_cast : ((2 : ZMod 233) ^ (58 * n + 26)).val = (2 ^ (58 * n + 26) : ℕ) % 233 := by
    have h_hom : (2 : ZMod 233) ^ (58 * n + 26) = ((2 ^ (58 * n + 26) : ℕ) : ZMod 233) := by push_cast; rfl
    rw [h_hom]
    rw [ZMod.val_natCast]
  rw [h_cast] at h_val
  have h_rhs : (204 : ZMod 233).val = 204 := by decide
  rw [h_rhs] at h_val
  exact h_val

lemma pow_two_mod_1399 (n : ℕ) : (2 : ZMod 1399) ^ (2 ^ (58 * n + 26) + 2) = -3 := by
  have h_mod : (2 : ZMod 1399) ^ 233 = 1 := by decide
  rw [pow_eq_pow_mod (2 ^ (58 * n + 26) + 2) h_mod]
  have h_exp : (2 ^ (58 * n + 26) + 2) % 233 = 206 := by
    rw [Nat.add_mod]
    rw [pow_two_mod_233_nat n]
  rw [h_exp]
  decide

lemma dvd_1399 (n : ℕ) : 1399 ∣ c_term n := by
  unfold c_term
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod 1399 ) = (2 : ZMod 1399) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  rw [pow_two_mod_1399 n]
  ring

lemma c_term_ge_three (n : ℕ) : 3 ≤ c_term n := by
  unfold c_term
  have : 0 ≤ 2 ^ (2 ^ (58 * n + 26) + 2) := Nat.zero_le _
  omega

lemma a_eq_c_term (n : ℕ) : a (58 * n + 26) = (c_term n).minFac := rfl


lemma covered_C1_iff (k : ℕ) : covered_by_C1 k ↔ k % 10 = 2 := by
  constructor
  · rintro ⟨m, rfl⟩
    omega
  · intro h
    use (k - 2) / 10
    omega

lemma covered_C2_iff (k : ℕ) : covered_by_C2 k ↔ k % 36 = 16 ∧ ((k - 16) / 36) % 5 ≠ 1 := by
  constructor
  · rintro ⟨m, rfl, hm⟩
    have : (36 * m + 16 - 16) / 36 = m := by omega
    rw [this]
    exact ⟨by omega, hm⟩
  · rintro ⟨h1, h2⟩
    use (k - 16) / 36
    constructor
    · omega
    · exact h2

lemma covered_C3_iff (k : ℕ) : covered_by_C3 k ↔ k % 84 = 22 ∧ ((k - 22) / 84) % 5 ≠ 0 := by
  constructor
  · rintro ⟨m, rfl, hm⟩
    have : (84 * m + 22 - 22) / 84 = m := by omega
    rw [this]
    exact ⟨by omega, hm⟩
  · rintro ⟨h1, h2⟩
    use (k - 22) / 84
    constructor
    · omega
    · exact h2

lemma helper1 (n : ℕ) : (58 * n + 26) % 10 = 2 ↔ n % 5 = 2 := by omega
lemma helper2 (n : ℕ) : (58 * n + 26) % 36 = 16 ↔ n % 18 = 11 := by omega
lemma helper3 (n : ℕ) : (58 * n + 26) % 84 = 22 ↔ n % 42 = 26 := by omega

lemma helper2_full (n : ℕ) : covered_by_C2 (58 * n + 26) ↔ n % 18 = 11 ∧ ((n - 11) / 18) % 5 ≠ 2 := by
  rw [covered_C2_iff]
  omega

lemma helper3_full (n : ℕ) : covered_by_C3 (58 * n + 26) ↔ n % 42 = 26 ∧ ((n - 26) / 42) % 5 ≠ 3 := by
  rw [covered_C3_iff]
  omega

lemma not_covered_iff (n : ℕ) :
    (¬ covered_by_C1 (58 * n + 26) ∧
     ¬ covered_by_C2 (58 * n + 26) ∧
     ¬ covered_by_C3 (58 * n + 26)) ↔
    (n % 5 ≠ 2 ∧ n % 18 ≠ 11 ∧ n % 42 ≠ 26) := by
  rw [covered_C1_iff, helper2_full, helper3_full]
  rw [helper1]
  omega

lemma forall_of_list_all_list {l : List ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : l.all (fun r => decide (P r)) = true) : ∀ r ∈ l, P r := by
  rw [List.all_eq_true] at h
  intro r hr
  have h_dec := h r hr
  exact of_decide_eq_true h_dec


lemma forall_of_list_all_list_bool {l : List ℕ} {f : ℕ → Bool}
    (h : l.all f = true) : ∀ r ∈ l, f r = true := by
  rw [List.all_eq_true] at h
  exact h

lemma zmod_eq_of_nat_eq (q ord_2 : ℕ) (h : 2 ^ ord_2 % q = 1 % q) : (2 : ZMod q) ^ ord_2 = 1 := by
  have h_cast : ((2 ^ ord_2 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  push_cast at h_cast
  exact h_cast

lemma check_no_match_zmod_of_nat (q E : ℕ) (h : (2 ^ E + 3) % q ≠ 0) : (2 : ZMod q) ^ E + 3 ≠ 0 := by
  intro hc
  have h_eq : ((2 ^ E + 3 : ℕ) : ZMod q) = 0 := by
    push_cast
    exact hc
  rw [ZMod.natCast_eq_zero_iff] at h_eq
  have h_mod0 := Nat.mod_eq_zero_of_dvd h_eq
  exact h h_mod0

def is_critical (q : ℕ) : Bool :=
  q == 2 || q == 67 || q == 271 || q == 523

def get_ord (q : ℕ) : ℕ :=
  match q with
  | 3 => 2
  | 5 => 4
  | 7 => 3
  | 11 => 10
  | 13 => 12
  | 17 => 8
  | 19 => 18
  | 23 => 11
  | 29 => 28
  | 31 => 5
  | 37 => 36
  | 41 => 20
  | 43 => 14
  | 47 => 23
  | 53 => 52
  | 59 => 58
  | 61 => 60
  | 67 => 66
  | 71 => 35
  | 73 => 9
  | 79 => 39
  | 83 => 82
  | 89 => 11
  | 97 => 48
  | 101 => 100
  | 103 => 51
  | 107 => 106
  | 109 => 36
  | 113 => 28
  | 127 => 7
  | 131 => 130
  | 137 => 68
  | 139 => 138
  | 149 => 148
  | 151 => 15
  | 157 => 52
  | 163 => 162
  | 167 => 83
  | 173 => 172
  | 179 => 178
  | 181 => 180
  | 191 => 95
  | 193 => 96
  | 197 => 196
  | 199 => 99
  | 211 => 210
  | 223 => 37
  | 227 => 226
  | 229 => 76
  | 233 => 29
  | 239 => 119
  | 241 => 24
  | 251 => 50
  | 257 => 16
  | 263 => 131
  | 269 => 268
  | 271 => 135
  | 277 => 92
  | 281 => 70
  | 283 => 94
  | 293 => 292
  | 307 => 102
  | 311 => 155
  | 313 => 156
  | 317 => 316
  | 331 => 30
  | 337 => 21
  | 347 => 346
  | 349 => 348
  | 353 => 88
  | 359 => 179
  | 367 => 183
  | 373 => 372
  | 379 => 378
  | 383 => 191
  | 389 => 388
  | 397 => 44
  | 401 => 200
  | 409 => 204
  | 419 => 418
  | 421 => 420
  | 431 => 43
  | 433 => 72
  | 439 => 73
  | 443 => 442
  | 449 => 224
  | 457 => 76
  | 461 => 460
  | 463 => 231
  | 467 => 466
  | 479 => 239
  | 487 => 243
  | 491 => 490
  | 499 => 166
  | 503 => 251
  | 509 => 508
  | 521 => 260
  | 523 => 522
  | 541 => 540
  | 547 => 546
  | 557 => 556
  | 563 => 562
  | 569 => 284
  | 571 => 114
  | 577 => 144
  | 587 => 586
  | 593 => 148
  | 599 => 299
  | 601 => 25
  | 607 => 303
  | 613 => 612
  | 617 => 154
  | 619 => 618
  | 631 => 45
  | 641 => 64
  | 643 => 214
  | 647 => 323
  | 653 => 652
  | 659 => 658
  | 661 => 660
  | 673 => 48
  | 677 => 676
  | 683 => 22
  | 691 => 230
  | 701 => 700
  | 709 => 708
  | 719 => 359
  | 727 => 121
  | 733 => 244
  | 739 => 246
  | 743 => 371
  | 751 => 375
  | 757 => 756
  | 761 => 380
  | 769 => 384
  | 773 => 772
  | 787 => 786
  | 797 => 796
  | 809 => 404
  | 811 => 270
  | 821 => 820
  | 823 => 411
  | 827 => 826
  | 829 => 828
  | 839 => 419
  | 853 => 852
  | 857 => 428
  | 859 => 858
  | 863 => 431
  | 877 => 876
  | 881 => 55
  | 883 => 882
  | 887 => 443
  | 907 => 906
  | 911 => 91
  | 919 => 153
  | 929 => 464
  | 937 => 117
  | 941 => 940
  | 947 => 946
  | 953 => 68
  | 967 => 483
  | 971 => 194
  | 977 => 488
  | 983 => 491
  | 991 => 495
  | 997 => 332
  | 1009 => 504
  | 1013 => 92
  | 1019 => 1018
  | 1021 => 340
  | 1031 => 515
  | 1033 => 258
  | 1039 => 519
  | 1049 => 262
  | 1051 => 350
  | 1061 => 1060
  | 1063 => 531
  | 1069 => 356
  | 1087 => 543
  | 1091 => 1090
  | 1093 => 364
  | 1097 => 274
  | 1103 => 29
  | 1109 => 1108
  | 1117 => 1116
  | 1123 => 1122
  | 1129 => 564
  | 1151 => 575
  | 1153 => 288
  | 1163 => 166
  | 1171 => 1170
  | 1181 => 236
  | 1187 => 1186
  | 1193 => 298
  | 1201 => 300
  | 1213 => 1212
  | 1217 => 152
  | 1223 => 611
  | 1229 => 1228
  | 1231 => 615
  | 1237 => 1236
  | 1249 => 156
  | 1259 => 1258
  | 1277 => 1276
  | 1279 => 639
  | 1283 => 1282
  | 1289 => 161
  | 1291 => 1290
  | 1297 => 648
  | 1301 => 1300
  | 1303 => 651
  | 1307 => 1306
  | 1319 => 659
  | 1321 => 60
  | 1327 => 221
  | 1361 => 680
  | 1367 => 683
  | 1373 => 1372
  | 1381 => 1380
  | _ => 1

def get_L (q : ℕ) : ℕ :=
  match q with
  | 3 => 1
  | 5 => 1
  | 7 => 1
  | 11 => 2
  | 13 => 1
  | 17 => 1
  | 19 => 3
  | 23 => 5
  | 29 => 3
  | 31 => 2
  | 37 => 3
  | 41 => 2
  | 43 => 3
  | 47 => 11
  | 53 => 6
  | 59 => 14
  | 61 => 2
  | 67 => 5
  | 71 => 6
  | 73 => 3
  | 79 => 6
  | 83 => 10
  | 89 => 5
  | 97 => 1
  | 101 => 10
  | 103 => 4
  | 107 => 26
  | 109 => 3
  | 113 => 3
  | 127 => 3
  | 131 => 6
  | 137 => 4
  | 139 => 11
  | 149 => 18
  | 151 => 2
  | 157 => 6
  | 163 => 27
  | 167 => 41
  | 173 => 7
  | 179 => 11
  | 181 => 6
  | 191 => 18
  | 193 => 1
  | 197 => 21
  | 199 => 15
  | 211 => 6
  | 223 => 18
  | 227 => 14
  | 229 => 9
  | 233 => 14
  | 239 => 12
  | 241 => 1
  | 251 => 10
  | 257 => 1
  | 263 => 65
  | 269 => 33
  | 271 => 18
  | 277 => 11
  | 281 => 6
  | 283 => 23
  | 293 => 9
  | 307 => 4
  | 311 => 10
  | 313 => 6
  | 317 => 39
  | 331 => 2
  | 337 => 3
  | 347 => 86
  | 349 => 14
  | 353 => 5
  | 359 => 89
  | 367 => 30
  | 373 => 5
  | 379 => 9
  | 383 => 95
  | 389 => 24
  | 397 => 5
  | 401 => 10
  | 409 => 4
  | 419 => 45
  | 421 => 6
  | 431 => 7
  | 433 => 3
  | 439 => 9
  | 443 => 12
  | 449 => 3
  | 457 => 9
  | 461 => 22
  | 463 => 15
  | 467 => 1
  | 479 => 119
  | 487 => 81
  | 491 => 42
  | 499 => 41
  | 503 => 25
  | 509 => 7
  | 521 => 6
  | 523 => 42
  | 541 => 18
  | 547 => 6
  | 557 => 69
  | 563 => 35
  | 569 => 35
  | 571 => 9
  | 577 => 3
  | 587 => 146
  | 593 => 18
  | 599 => 66
  | 601 => 10
  | 607 => 50
  | 613 => 12
  | 617 => 15
  | 619 => 51
  | 631 => 6
  | 641 => 1
  | 643 => 53
  | 647 => 36
  | 653 => 81
  | 659 => 69
  | 661 => 10
  | 673 => 1
  | 677 => 78
  | 683 => 5
  | 691 => 22
  | 701 => 30
  | 709 => 1
  | 719 => 179
  | 727 => 55
  | 733 => 30
  | 739 => 10
  | 743 => 78
  | 751 => 50
  | 757 => 9
  | 761 => 18
  | 769 => 1
  | 773 => 48
  | 787 => 65
  | 797 => 99
  | 809 => 50
  | 811 => 18
  | 821 => 10
  | 823 => 34
  | 827 => 3
  | 829 => 33
  | 839 => 209
  | 853 => 35
  | 857 => 53
  | 859 => 30
  | 863 => 43
  | 877 => 9
  | 881 => 10
  | 883 => 21
  | 887 => 221
  | 907 => 15
  | 911 => 6
  | 919 => 12
  | 929 => 14
  | 937 => 6
  | 941 => 46
  | 947 => 35
  | 953 => 4
  | 967 => 33
  | 971 => 24
  | 977 => 30
  | 983 => 245
  | 991 => 30
  | 997 => 41
  | 1009 => 3
  | 1013 => 11
  | 1019 => 254
  | 1021 => 4
  | 1031 => 102
  | 1033 => 7
  | 1039 => 86
  | 1049 => 65
  | 1051 => 30
  | 1061 => 26
  | 1063 => 3
  | 1069 => 11
  | 1087 => 90
  | 1091 => 18
  | 1093 => 6
  | 1097 => 34
  | 1103 => 14
  | 1109 => 46
  | 1117 => 15
  | 1123 => 20
  | 1129 => 23
  | 1151 => 110
  | 1153 => 3
  | 1163 => 41
  | 1171 => 6
  | 1181 => 1
  | 1187 => 74
  | 1193 => 74
  | 1201 => 10
  | 1213 => 50
  | 1217 => 9
  | 1223 => 138
  | 1229 => 51
  | 1231 => 10
  | 1237 => 51
  | 1249 => 6
  | 1259 => 36
  | 1277 => 70
  | 1279 => 105
  | 1283 => 32
  | 1289 => 33
  | 1291 => 14
  | 1297 => 27
  | 1301 => 30
  | 1303 => 15
  | 1307 => 326
  | 1319 => 329
  | 1321 => 2
  | 1327 => 12
  | 1361 => 4
  | 1367 => 11
  | 1373 => 147
  | 1381 => 22
  | _ => 1


attribute [irreducible] c_term

def primes_under_1399 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]

def fast_pow_mod_fuel (fuel : ℕ) (b e m : ℕ) : ℕ :=
  match fuel with
  | 0 => 1 % m
  | fuel + 1 =>
    if e = 0 then 1 % m
    else
      let r := fast_pow_mod_fuel fuel b (e / 2) m
      if e % 2 = 1 then
        (r * r % m) * b % m
      else
        r * r % m

def fast_pow_mod (b e m : ℕ) : ℕ :=
  if e < 1048576 then
    fast_pow_mod_fuel 20 b e m
  else
    b ^ e % m

theorem fast_pow_mod_fuel_eq (fuel : ℕ) (b e m : ℕ) (h_fuel : e < 2 ^ fuel) :
    fast_pow_mod_fuel fuel b e m = b ^ e % m := by
  induction fuel generalizing e with
  | zero =>
    have : e = 0 := by omega
    subst this
    rfl
  | succ fuel ih =>
    unfold fast_pow_mod_fuel
    by_cases he : e = 0
    · simp [he]
    · simp only [he, ↓reduceIte]
      have h_div : e / 2 < 2 ^ fuel := by
        have h_pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        rw [h_pow] at h_fuel
        omega
      have ih_inst := ih (e / 2) h_div
      rw [ih_inst]
      by_cases h_odd : e % 2 = 1
      · simp only [h_odd, ↓reduceIte]
        have h_odd_eq : e = 2 * (e / 2) + 1 := by
          have := Nat.div_add_mod e 2
          omega
        conv_rhs => rw [h_odd_eq]
        have h_pow_eq : b ^ (2 * (e / 2) + 1) = b ^ (e / 2) * b ^ (e / 2) * b := by
          ring
        rw [h_pow_eq]
        simp [Nat.mul_mod]
      · have h_even : e % 2 = 0 := by omega
        simp only [h_even]
        have h_odd_eq : (0 = 1) = False := by decide
        simp only [h_odd_eq, ↓reduceIte]
        have h_even_eq : e = 2 * (e / 2) := by
          have := Nat.div_add_mod e 2
          omega
        conv_rhs => rw [h_even_eq]
        have h_pow_eq : b ^ (2 * (e / 2)) = b ^ (e / 2) * b ^ (e / 2) := by
          ring
        rw [h_pow_eq]
        simp [Nat.mul_mod]

theorem fast_pow_mod_eq (b e m : ℕ) : fast_pow_mod b e m = b ^ e % m := by
  unfold fast_pow_mod
  split_ifs with h
  · exact fast_pow_mod_fuel_eq 20 b e m h
  · rfl

abbrev check_base (L ord_2 r : ℕ) : Prop :=
  (2 ^ (58 * L) * 2 ^ (58 * r + 26)) % ord_2 = 2 ^ (58 * r + 26) % ord_2

lemma check_base_of_check_base_zero (L ord_2 : ℕ) (h0 : check_base L ord_2 0) (r : ℕ) :
    check_base L ord_2 r := by
  unfold check_base at *
  have h_eq1 : 2 ^ (58 * L) * 2 ^ (58 * r + 26) = (2 ^ (58 * L) * 2 ^ 26) * 2 ^ (58 * r) := by
    rw [pow_add]
    ring
  have h_eq2 : 2 ^ (58 * r + 26) = 2 ^ 26 * 2 ^ (58 * r) := by
    rw [pow_add]
    ring
  rw [h_eq1, h_eq2]
  rw [Nat.mul_mod, h0]
  rw [← Nat.mul_mod]

lemma check_base_of_fast (L ord_2 : ℕ) (h_fast : fast_pow_mod 2 (58 * L + 26) ord_2 = fast_pow_mod 2 26 ord_2) (r : ℕ) :
    check_base L ord_2 r := by
  have h0 : check_base L ord_2 0 := by
    unfold check_base
    rw [fast_pow_mod_eq, fast_pow_mod_eq] at h_fast
    have h_pow_add : 2 ^ (58 * L + 26) = 2 ^ (58 * L) * 2 ^ 26 := by ring
    rw [h_pow_add] at h_fast
    exact h_fast
  exact check_base_of_check_base_zero L ord_2 h0 r

abbrev check_no_match (q ord_2 r : ℕ) : Prop :=
  (2 ^ ((2 ^ (58 * r + 26) + 2) % ord_2) + 3) % q ≠ 0

def fast_check_no_match (q ord_2 r : ℕ) : Bool :=
  let e := fast_pow_mod 2 (58 * r + 26) ord_2
  let val_mod := fast_pow_mod 2 ((e + 2) % ord_2) q
  decide ((val_mod + 3) % q ≠ 0)

lemma check_no_match_of_fast (q ord_2 r : ℕ) (h_fast : fast_check_no_match q ord_2 r = true) :
    check_no_match q ord_2 r := by
  unfold check_no_match
  unfold fast_check_no_match at h_fast
  rw [decide_eq_true_iff] at h_fast
  rw [fast_pow_mod_eq, fast_pow_mod_eq] at h_fast
  have h_add : (2 ^ (58 * r + 26) % ord_2 + 2) % ord_2 = (2 ^ (58 * r + 26) + 2) % ord_2 := by
    rw [Nat.add_mod, Nat.add_mod (2 ^ (58 * r + 26)), Nat.mod_mod]
  rw [h_add] at h_fast
  have h_add2 : (2 ^ ((2 ^ (58 * r + 26) + 2) % ord_2) % q + 3) % q = (2 ^ ((2 ^ (58 * r + 26) + 2) % ord_2) + 3) % q := by
    rw [Nat.add_mod, Nat.add_mod (2 ^ ((2 ^ (58 * r + 26) + 2) % ord_2)), Nat.mod_mod]
  rw [h_add2] at h_fast
  exact h_fast

def has_sqrt_neg_three (q : ℕ) : Prop :=
  ∃ x : ZMod q, x^2 + 3 = 0

def has_sqrt_neg_three_bool (q : ℕ) : Bool :=
  (List.range q).any (fun x => (x * x + 3) % q == 0)

lemma has_sqrt_neg_three_of_bool (q : ℕ) (h : has_sqrt_neg_three_bool q = true) : has_sqrt_neg_three q := by
  unfold has_sqrt_neg_three_bool at h
  rw [List.any_eq_true] at h
  rcases h with ⟨x, hx_mem, hx_eq⟩
  rw [List.mem_range] at hx_mem
  have h_val : (x : ZMod q) ^ 2 + 3 = 0 := by
    have h_hom : (x : ZMod q) ^ 2 + 3 = ( (x * x + 3 : ℕ) : ZMod q ) := by
      push_cast
      rfl
    rw [h_hom]
    rw [ZMod.natCast_eq_zero_iff]
    have h_eq := eq_of_beq hx_eq
    exact Nat.dvd_of_mod_eq_zero h_eq
  exact ⟨(x : ZMod q), h_val⟩

lemma not_has_sqrt_neg_three_of_bool_false (q : ℕ) [NeZero q] (h : has_sqrt_neg_three_bool q = false) : ¬ has_sqrt_neg_three q := by
  intro hc
  rcases hc with ⟨x, hx⟩
  have h_val := x.val_lt
  unfold has_sqrt_neg_three_bool at h
  rw [List.any_eq_false] at h
  have h_inst := h x.val (List.mem_range.2 h_val)
  rw [Bool.not_eq_true, beq_iff_ne] at h_inst
  have h_val_eq : (x.val * x.val + 3) % q = 0 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h_x : (x.val : ZMod q) = x := ZMod.natCast_zmod_val x
    have h_hom : ((x.val * x.val + 3 : ℕ) : ZMod q) = x ^ 2 + 3 := by
      push_cast
      rw [h_x]
    rw [h_hom]
    exact hx
  exact h_inst h_val_eq

lemma c_term_eq_sq_add_three (n : ℕ) : c_term n = (2 ^ (2 ^ (58 * n + 25) + 1)) ^ 2 + 3 := by
  unfold c_term
  have h_exp : 2 ^ (58 * n + 26) + 2 = 2 * (2 ^ (58 * n + 25) + 1) := by
    have : 58 * n + 26 = (58 * n + 25) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [h_exp]
  rw [pow_mul]

lemma not_dvd_of_not_has_sqrt_neg_three (q : ℕ) (n : ℕ) (h_sqrt : ¬ has_sqrt_neg_three q) : ¬ q ∣ c_term n := by
  rw [c_term_eq_sq_add_three]
  intro hdvd
  rw [← ZMod.natCast_eq_zero_iff] at hdvd
  have h_cast : (((2 ^ (2 ^ (58 * n + 25) + 1)) ^ 2 + 3 : ℕ) : ZMod q) = (2 ^ (2 ^ (58 * n + 25) + 1) : ZMod q) ^ 2 + 3 := by
    push_cast
    rfl
  rw [h_cast] at hdvd
  let x : ZMod q := (2 ^ (2 ^ (58 * n + 25) + 1) : ZMod q)
  have hdvd' : x ^ 2 + 3 = 0 := hdvd
  have h_exists : has_sqrt_neg_three q := ⟨x, hdvd'⟩
  exact h_sqrt h_exists

def not_has_sqrt_neg_three_bool (q : ℕ) : Bool :=
  not (has_sqrt_neg_three_bool q)

def check_prime_ok (q : ℕ) : Bool :=
  not_has_sqrt_neg_three_bool q ||
  (let ord := get_ord q
   let L := get_L q
   (fast_pow_mod 2 ord q == 1 % q) &&
   (fast_pow_mod 2 (58 * L + 26) ord == fast_pow_mod 2 26 ord) &&
   (List.range L).all (fun r => fast_check_no_match q ord r))

lemma not_dvd_of_check (q ord_2 L : ℕ) [NeZero q] (hL : 0 < L)
    (h_mod : 2 ^ ord_2 % q = 1 % q)
    (h_base_bool : (List.range L).all (fun r => decide (check_base L ord_2 r)) = true)
    (h_no_match_bool : (List.range L).all (fun r => decide (check_no_match q ord_2 r)) = true)
    (n : ℕ) : ¬ q ∣ c_term n := by
  unfold c_term
  have h_mod_zmod : (2 : ZMod q) ^ ord_2 = 1 := zmod_eq_of_nat_eq q ord_2 h_mod
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod q ) = (2 : ZMod q) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  rw [pow_eq_pow_mod (2 ^ (58 * n + 26) + 2) h_mod_zmod]
  have h_base := forall_of_list_all_list (l := List.range L) h_base_bool
  have h_base_inst := h_base (n % L) (List.mem_range.2 (Nat.mod_lt _ hL))
  have h_pow := pow_mod_of_mod_eq n L (n % L) (58 * L) (58 * (n % L) + 26) ord_2 rfl rfl rfl h_base_inst
  have h_add : (2 ^ (58 * n + 26) + 2) % ord_2 = (2 ^ (58 * (n % L) + 26) + 2) % ord_2 := by
    rw [Nat.add_mod, h_pow, ← Nat.add_mod]
  rw [h_add]
  have h_no_match := forall_of_list_all_list (l := List.range L) h_no_match_bool
  have h_no_match_inst := h_no_match (n % L) (List.mem_range.2 (Nat.mod_lt _ hL))
  exact check_no_match_zmod_of_nat q ((2 ^ (58 * (n % L) + 26) + 2) % ord_2) h_no_match_inst

lemma check_prime_ok_properties (q : ℕ) (h : check_prime_ok q = true) :
    (¬ has_sqrt_neg_three q) ∨
    ((2 ^ (get_ord q) % q = 1 % q) ∧
     ((List.range (get_L q)).all (fun r => decide (check_base (get_L q) (get_ord q) r)) = true) ∧
     ((List.range (get_L q)).all (fun r => decide (check_no_match q (get_ord q) r)) = true)
    ) := by
  unfold check_prime_ok at h
  rw [Bool.or_eq_true] at h
  rcases h with h_sqrt | h_check
  · left
    unfold not_has_sqrt_neg_three_bool at h_sqrt
    rw [Bool.not_eq_true, decide_eq_false_iff_not] at h_sqrt
    exact h_sqrt
  · right
    rw [Bool.and_eq_true] at h_check
    rcases h_check with ⟨h1, h3⟩
    rw [Bool.and_eq_true] at h1
    rcases h1 with ⟨h1, h2⟩
    have h1_eq := eq_of_beq h1
    have h2_eq := eq_of_beq h2
    have h_mod : 2 ^ (get_ord q) % q = 1 % q := by
      rw [← fast_pow_mod_eq]
      exact h1_eq
    refine ⟨h_mod, ?_, ?_⟩
    · rw [List.all_eq_true]
      intro r hr
      rw [decide_eq_true_iff]
      exact check_base_of_fast (get_L q) (get_ord q) h2_eq r
    · rw [List.all_eq_true]
      intro r hr
      rw [decide_eq_true_iff]
      have h3_all : (List.range (get_L q)).all (fun r => fast_check_no_match q (get_ord q) r) = true := h3
      rw [List.all_eq_true] at h3_all
      exact check_no_match_of_fast q (get_ord q) r (h3_all r hr)

def L_pos_bool (q : ℕ) : Bool :=
  decide (0 < get_L q)

lemma verify_L_pos : primes_under_1399.all (fun r => decide (L_pos_bool r = true)) = true := by decide

lemma get_L_pos (q : ℕ) (hq : q ∈ primes_under_1399) : 0 < get_L q := by
  have h_all := forall_of_list_all_list (P := fun r => L_pos_bool r = true) verify_L_pos
  have h_inst := h_all q hq
  unfold L_pos_bool at h_inst
  exact of_decide_eq_true h_inst

lemma verify_all_non_critical_primes_eq : primes_under_1399.all (fun r => decide (check_prime_ok r = true)) = true := by rfl

lemma primes_under_1399_ne_zero : primes_under_1399.all (fun r => decide (r ≠ 0)) = true := by decide

lemma not_dvd_of_non_critical (q : ℕ) (hq : q ∈ primes_under_1399) (n : ℕ) :
    ¬ q ∣ c_term n := by
  have h_nz : q ≠ 0 := by
    have h_all := forall_of_list_all_list (P := fun r => r ≠ 0) primes_under_1399_ne_zero
    exact h_all q hq
  haveI : NeZero q := ⟨h_nz⟩
  have h_all := forall_of_list_all_list (P := fun r => check_prime_ok r = true) verify_all_non_critical_primes_eq
  have h_inst := h_all q hq
  rcases check_prime_ok_properties q h_inst with h_sqrt | ⟨h_mod, h_base, h_no_match⟩
  · exact not_dvd_of_not_has_sqrt_neg_three q n h_sqrt
  · have h_L_pos := get_L_pos q hq
    exact not_dvd_of_check q (get_ord q) (get_L q) h_L_pos h_mod h_base h_no_match n

lemma not_dvd_2 (n : ℕ) : ¬ 2 ∣ c_term n := by
  unfold c_term
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod 2 ) = (2 : ZMod 2) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2]
  have h_exp : 2 ^ (58 * n + 26) + 2 = (2 ^ (58 * n + 26) + 1) + 1 := by omega
  rw [h_exp, pow_succ]
  rw [mul_zero]
  decide


lemma not_dvd_critical (q ord_2 L : ℕ) [NeZero q] (hL : 0 < L)
    (h_mod : 2 ^ ord_2 % q = 1 % q)
    (h_base_bool : (List.range L).all (fun r => decide (check_base L ord_2 r)) = true)
    (r_exclude : ℕ)
    (h_no_match_bool : ((List.range L).filter (· ≠ r_exclude)).all (fun r => decide (check_no_match q ord_2 r)) = true)
    (n : ℕ) (hn_exclude : n % L ≠ r_exclude) :
    ¬ q ∣ c_term n := by
  unfold c_term
  have h_mod_zmod : (2 : ZMod q) ^ ord_2 = 1 := zmod_eq_of_nat_eq q ord_2 h_mod
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod q ) = (2 : ZMod q) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  rw [pow_eq_pow_mod (2 ^ (58 * n + 26) + 2) h_mod_zmod]
  have h_base := forall_of_list_all_list (l := List.range L) h_base_bool
  have h_base_inst := h_base (n % L) (List.mem_range.2 (Nat.mod_lt _ hL))
  have h_pow := pow_mod_of_mod_eq n L (n % L) (58 * L) (58 * (n % L) + 26) ord_2 rfl rfl rfl h_base_inst
  have h_add : (2 ^ (58 * n + 26) + 2) % ord_2 = (2 ^ (58 * (n % L) + 26) + 2) % ord_2 := by
    rw [Nat.add_mod, h_pow, ← Nat.add_mod]
  rw [h_add]
  have h_no_match := forall_of_list_all_list (l := (List.range L).filter (· ≠ r_exclude)) h_no_match_bool
  have h_mem : n % L ∈ (List.range L).filter (· ≠ r_exclude) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.2 (Nat.mod_lt _ hL), decide_eq_true hn_exclude⟩
  have h_no_match_inst := h_no_match (n % L) h_mem
  exact check_no_match_zmod_of_nat q ((2 ^ (58 * (n % L) + 26) + 2) % ord_2) h_no_match_inst

lemma not_dvd_67 (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26) :
    ¬ 67 ∣ c_term n := by
  exact not_dvd_critical 67 66 5 (by decide) (by decide) (by decide) 2 (by decide) n h_not_c1

lemma not_dvd_271 (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26) :
    ¬ 271 ∣ c_term n := by
  exact not_dvd_critical 271 135 18 (by decide) (by decide) (by decide) 11 (by decide) n h_not_c2

lemma not_dvd_523 (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26) :
    ¬ 523 ∣ c_term n := by
  exact not_dvd_critical 523 522 42 (by decide) (by decide) (by decide) 26 (by decide) n h_not_c3

def candidate_list : List ℕ := [2, 67, 271, 523] ++ primes_under_1399

def is_composite_fast (q : ℕ) : Bool :=
  (q < 2) ||
  (q % 2 = 0 && q ≠ 2) ||
  (q % 3 = 0 && q ≠ 3) ||
  (q % 5 = 0 && q ≠ 5) ||
  (q % 7 = 0 && q ≠ 7) ||
  (q % 11 = 0 && q ≠ 11) ||
  (q % 13 = 0 && q ≠ 13) ||
  (q % 17 = 0 && q ≠ 17) ||
  (q % 19 = 0 && q ≠ 19) ||
  (q % 23 = 0 && q ≠ 23) ||
  (q % 29 = 0 && q ≠ 29) ||
  (q % 31 = 0 && q ≠ 31) ||
  (q % 37 = 0 && q ≠ 37)

lemma is_composite_fast_iff (q : ℕ) :
    is_composite_fast q = true ↔
    q < 2 ∨
    (2 ∣ q ∧ q ≠ 2) ∨
    (3 ∣ q ∧ q ≠ 3) ∨
    (5 ∣ q ∧ q ≠ 5) ∨
    (7 ∣ q ∧ q ≠ 7) ∨
    (11 ∣ q ∧ q ≠ 11) ∨
    (13 ∣ q ∧ q ≠ 13) ∨
    (17 ∣ q ∧ q ≠ 17) ∨
    (19 ∣ q ∧ q ≠ 19) ∨
    (23 ∣ q ∧ q ≠ 23) ∨
    (29 ∣ q ∧ q ≠ 29) ∨
    (31 ∣ q ∧ q ≠ 31) ∨
    (37 ∣ q ∧ q ≠ 37) := by
  unfold is_composite_fast
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, Nat.dvd_iff_mod_eq_zero, or_assoc]

def check_cand (q : ℕ) : Bool :=
  is_composite_fast q || (q == 2) || (q == 67) || (q == 271) || (q == 523) || primes_under_1399.elem q

lemma mem_or_composite_of_check_cand (q : ℕ) (hq : q < 1399) (h : check_cand q = true) :
    q ∈ candidate_list ∨ is_composite_fast q = true := by
  unfold check_cand at h
  rw [Bool.or_eq_true] at h
  rcases h with h_other | h_elem
  · rw [Bool.or_eq_true] at h_other
    rcases h_other with h_other2 | h_523
    · rw [Bool.or_eq_true] at h_other2
      rcases h_other2 with h_other3 | h_271
      · rw [Bool.or_eq_true] at h_other3
        rcases h_other3 with h_other4 | h_67
        · rw [Bool.or_eq_true] at h_other4
          rcases h_other4 with h_comp | h_2
          · right; exact h_comp
          · left; rw [candidate_list]
            have h_mem : q ∈ [2, 67, 271, 523] := by rw [eq_of_beq h_2]; decide
            exact List.mem_append_left _ h_mem
        · left; rw [candidate_list]
          have h_mem : q ∈ [2, 67, 271, 523] := by rw [eq_of_beq h_67]; decide
          exact List.mem_append_left _ h_mem
      · left; rw [candidate_list]
        have h_mem : q ∈ [2, 67, 271, 523] := by rw [eq_of_beq h_271]; decide
        exact List.mem_append_left _ h_mem
    · left; rw [candidate_list]
      have h_mem : q ∈ [2, 67, 271, 523] := by rw [eq_of_beq h_523]; decide
      exact List.mem_append_left _ h_mem
  · left; rw [candidate_list]
    have h_mem : q ∈ primes_under_1399 := List.elem_iff.mp h_elem
    exact List.mem_append_right _ h_mem


lemma verify_range : (List.range 1399).all check_cand = true := by decide

lemma mem_or_composite_fast_of_lt (q : ℕ) (hq : q < 1399) :
    q ∈ candidate_list ∨ is_composite_fast q = true := by
  have h_all := forall_of_list_all_list_bool (l := List.range 1399) verify_range
  have h_inst := h_all q (List.mem_range.2 hq)
  exact mem_or_composite_of_check_cand q hq h_inst

lemma not_prime_of_lt_two (q : ℕ) (h : q < 2) : ¬ q.Prime := by
  intro hq
  have : 2 ≤ q := hq.two_le
  omega

lemma not_prime_of_dvd_and_ne (q p : ℕ) (hp : p.Prime) (hdvd : p ∣ q) (hne : q ≠ p) : ¬ q.Prime := by
  intro hq
  have h_eq : q = p := (Nat.Prime.dvd_iff_eq hq hp.ne_one).mp hdvd
  exact hne h_eq

lemma not_prime_of_is_composite_fast (q : ℕ) (h : is_composite_fast q = true) : ¬ q.Prime := by
  rw [is_composite_fast_iff] at h
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact not_prime_of_lt_two q h
  · exact not_prime_of_dvd_and_ne q 2 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 3 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 5 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 7 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 11 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 13 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 17 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 19 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 23 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 29 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 31 (by decide) h1 h2
  · exact not_prime_of_dvd_and_ne q 37 (by decide) h1 h2

lemma no_smaller_prime_factor_of_mem (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26)
    (q : ℕ) (hp : q.Prime) (h_mem : q ∈ candidate_list) : ¬ q ∣ c_term n := by
  have h_mem_append := h_mem
  rw [candidate_list] at h_mem_append
  rw [List.mem_append] at h_mem_append
  rcases h_mem_append with h_primes | h_non_crit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h_primes
    rcases h_primes with rfl | rfl | rfl | rfl
    · exact not_dvd_2 n
    · exact not_dvd_67 n h_not_c1 h_not_c2 h_not_c3
    · exact not_dvd_271 n h_not_c1 h_not_c2 h_not_c3
    · exact not_dvd_523 n h_not_c1 h_not_c2 h_not_c3
  · exact not_dvd_of_non_critical q h_non_crit n

attribute [irreducible] primes_under_1399 candidate_list is_composite_fast


lemma no_smaller_prime_factor_of_comp (n : ℕ) (q : ℕ) (hp : q.Prime) (h_comp : is_composite_fast q = true) : ¬ q ∣ c_term n := by
  have h_not := not_prime_of_is_composite_fast q h_comp
  exact absurd hp h_not

lemma no_smaller_prime_factor (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26) :
    ∀ q < 1399, q.Prime → ¬ q ∣ c_term n := by
  intro q hq hprime
  cases mem_or_composite_fast_of_lt q hq with
  | inl h_mem => exact no_smaller_prime_factor_of_mem n h_not_c1 h_not_c2 h_not_c3 q hprime h_mem
  | inr h_comp => exact no_smaller_prime_factor_of_comp n q hprime h_comp

theorem oeis_248802_conjecture_4 (n : ℕ) :
  (¬ covered_by_C1 (58 * n + 26) ∧
   ¬ covered_by_C2 (58 * n + 26) ∧
   ¬ covered_by_C3 (58 * n + 26)) →
  a (58 * n + 26) = 1399 := by
  intro h
  have h_nc := h
  rw [not_covered_iff] at h_nc
  rcases h_nc with ⟨h_nc1, h_nc2, h_nc3⟩
  have hp : Nat.Prime 1399 := by decide
  have hdvd : 1399 ∣ c_term n := dvd_1399 n
  have h_not_dvd : ∀ q < 1399, q.Prime → ¬ q ∣ c_term n :=
    no_smaller_prime_factor n h_nc1 h_nc2 h_nc3
  
  -- We want to prove Nat.minFac X = 1399
  -- Let X = c_term n
  -- By minFac_eq_of_prime_dvd:
  have h_minfac : (c_term n).minFac = 1399 := by
    have hn1 : c_term n ≠ 1 := by
      have := c_term_ge_three n
      omega
    have h_prop := Nat.minFac_has_prop hn1
    have h_le : (c_term n).minFac ≤ 1399 := Nat.minFac_le_of_dvd hp.two_le hdvd
    have h_ge : 1399 ≤ (c_term n).minFac := by
      by_contra! h_lt
      have h_prime_mf := Nat.minFac_prime hn1
      have h_not := h_not_dvd (c_term n).minFac h_lt h_prime_mf
      exact h_not h_prop.2.1
    exact le_antisymm h_le h_ge
  have h_a := a_eq_c_term n
  rw [h_a]
  exact h_minfac






