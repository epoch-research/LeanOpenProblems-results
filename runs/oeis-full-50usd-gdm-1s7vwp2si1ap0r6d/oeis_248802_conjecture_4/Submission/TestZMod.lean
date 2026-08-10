import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 3000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 100000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures false

def primes_under_1399 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]

def composites_under_1399 : List ℕ := [121, 143, 169, 187, 209, 221, 247, 253, 289, 299, 319, 323, 341, 361, 377, 391, 403, 407, 437, 451, 473, 481, 493, 517, 527, 529, 533, 551, 559, 583, 589, 611, 629, 649, 667, 671, 689, 697, 703, 713, 731, 737, 767, 779, 781, 793, 799, 803, 817, 841, 851, 869, 871, 893, 899, 901, 913, 923, 943, 949, 961, 979, 989, 1003, 1007, 1027, 1037, 1067, 1073, 1079, 1081, 1111, 1121, 1133, 1139, 1147, 1157, 1159, 1177, 1189, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]

def candidate_list : List ℕ := [2, 67, 271, 523] ++ primes_under_1399 ++ composites_under_1399

def is_composite_fast (q : ℕ) : Bool :=
  (q < 2) ||
  (q % 2 = 0 && q ≠ 2) ||
  (q % 3 = 0 && q ≠ 3) ||
  (q % 5 = 0 && q ≠ 5) ||
  (q % 7 = 0 && q ≠ 7)

lemma is_composite_fast_iff (q : ℕ) :
    is_composite_fast q = true ↔
    q < 2 ∨
    (2 ∣ q ∧ q ≠ 2) ∨
    (3 ∣ q ∧ q ≠ 3) ∨
    (5 ∣ q ∧ q ≠ 5) ∨
    (7 ∣ q ∧ q ≠ 7) := by
  unfold is_composite_fast
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, Nat.dvd_iff_mod_eq_zero, or_assoc]

lemma forall_of_list_all_list {l : List ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : l.all (fun r => decide (P r)) = true) : ∀ r ∈ l, P r := by
  rw [List.all_eq_true] at h
  intro r hr
  have h_dec := h r hr
  exact of_decide_eq_true h_dec

-- 10-part range checker
lemma verify_part1 : (List.range 139).all (fun offset => decide (0 + offset ∈ candidate_list ∨ is_composite_fast (0 + offset) = true)) = true := by decide
lemma verify_part2 : (List.range 139).all (fun offset => decide (139 + offset ∈ candidate_list ∨ is_composite_fast (139 + offset) = true)) = true := by decide
lemma verify_part3 : (List.range 139).all (fun offset => decide (278 + offset ∈ candidate_list ∨ is_composite_fast (278 + offset) = true)) = true := by decide
lemma verify_part4 : (List.range 139).all (fun offset => decide (417 + offset ∈ candidate_list ∨ is_composite_fast (417 + offset) = true)) = true := by decide
lemma verify_part5 : (List.range 139).all (fun offset => decide (556 + offset ∈ candidate_list ∨ is_composite_fast (556 + offset) = true)) = true := by decide
lemma verify_part6 : (List.range 139).all (fun offset => decide (695 + offset ∈ candidate_list ∨ is_composite_fast (695 + offset) = true)) = true := by decide
lemma verify_part7 : (List.range 139).all (fun offset => decide (834 + offset ∈ candidate_list ∨ is_composite_fast (834 + offset) = true)) = true := by decide
lemma verify_part8 : (List.range 139).all (fun offset => decide (973 + offset ∈ candidate_list ∨ is_composite_fast (973 + offset) = true)) = true := by decide
lemma verify_part9 : (List.range 139).all (fun offset => decide (1112 + offset ∈ candidate_list ∨ is_composite_fast (1112 + offset) = true)) = true := by decide
lemma verify_part10 : (List.range 148).all (fun offset => decide (1251 + offset ∈ candidate_list ∨ is_composite_fast (1251 + offset) = true)) = true := by decide

attribute [irreducible] primes_under_1399 composites_under_1399 candidate_list

lemma mem_or_composite_fast_of_lt (q : ℕ) (hq : q < 1399) :
    q ∈ candidate_list ∨ is_composite_fast q = true := by
  by_cases hq139 : q < 139
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part1
    have h_inst := h_all q (List.mem_range.2 hq139)
    rw [zero_add] at h_inst
    exact h_inst
  push_neg at hq139
  by_cases hq278 : q < 278
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part2
    have h_inst := h_all (q - 139) (List.mem_range.2 (by omega))
    have h_eq : 139 + (q - 139) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq278
  by_cases hq417 : q < 417
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part3
    have h_inst := h_all (q - 278) (List.mem_range.2 (by omega))
    have h_eq : 278 + (q - 278) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq417
  by_cases hq556 : q < 556
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part4
    have h_inst := h_all (q - 417) (List.mem_range.2 (by omega))
    have h_eq : 417 + (q - 417) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq556
  by_cases hq695 : q < 695
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part5
    have h_inst := h_all (q - 556) (List.mem_range.2 (by omega))
    have h_eq : 556 + (q - 556) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq695
  by_cases hq834 : q < 834
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part6
    have h_inst := h_all (q - 695) (List.mem_range.2 (by omega))
    have h_eq : 695 + (q - 695) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq834
  by_cases hq973 : q < 973
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part7
    have h_inst := h_all (q - 834) (List.mem_range.2 (by omega))
    have h_eq : 834 + (q - 834) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq973
  by_cases hq1112 : q < 1112
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part8
    have h_inst := h_all (q - 973) (List.mem_range.2 (by omega))
    have h_eq : 973 + (q - 973) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq1112
  by_cases hq1251 : q < 1251
  · have h_all := forall_of_list_all_list (l := List.range 139) verify_part9
    have h_inst := h_all (q - 1112) (List.mem_range.2 (by omega))
    have h_eq : 1112 + (q - 1112) = q := by omega
    rw [h_eq] at h_inst
    exact h_inst
  push_neg at hq1251
  have h_all := forall_of_list_all_list (l := List.range 148) verify_part10
  have h_inst := h_all (q - 1251) (List.mem_range.2 (by omega))
  have h_eq : 1251 + (q - 1251) = q := by omega
  rw [h_eq] at h_inst
  exact h_inst
