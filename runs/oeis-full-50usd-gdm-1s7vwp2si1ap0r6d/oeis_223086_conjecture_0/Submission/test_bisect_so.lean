import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

theorem A006368_map_injective : Function.Injective A006368_map := by
  intro x y h
  dsimp [A006368_map] at h
  split_ifs at h <;> omega

theorem iterate_injective_of_not_periodic {α : Type*} {f : α → α} (hf : Function.Injective f) {x : α}
  (h_not_periodic : ∀ (k : ℕ), k > 0 → f^[k] x ≠ x) :
  ∀ (i j : ℕ), f^[i] x = f^[j] x → i = j := by
  intro i j h
  rcases lt_trichotomy i j with h1 | rfl | h2
  · -- i < j
    have hk : ∃ k > 0, j = i + k := by
      use j - i
      constructor
      · omega
      · omega
    rcases hk with ⟨k, hk_gt, rfl⟩
    rw [Function.iterate_add_apply] at h
    have h_inj : Function.Injective (f^[i]) := hf.iterate i
    have h_eq := h_inj h
    have h_np := h_not_periodic k hk_gt
    exact False.elim (h_np h_eq.symm)
  · rfl
  · -- j < i
    have hk : ∃ k > 0, i = j + k := by
      use i - j
      constructor
      · omega
      · omega
    rcases hk with ⟨k, hk_gt, rfl⟩
    rw [Function.iterate_add_apply] at h
    have h_inj : Function.Injective (f^[j]) := hf.iterate j
    have h_eq := h_inj h.symm
    have h_np := h_not_periodic k hk_gt
    exact False.elim (h_np h_eq.symm)

def Dangerous (d : ℕ) : Prop :=
  d % 2 = 1 ∧ 97 ≤ d ∧ d ≤ 127

def E_list : List ℕ := [97, 98, 99, 100, 101, 102, 103, 105, 106, 107, 109, 110, 111, 112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 141, 143, 145, 147, 149, 150, 151, 152, 153, 157, 159, 161, 163, 165, 167, 168, 169, 170, 175, 177, 179, 183, 186, 191, 193, 198, 199, 201, 202, 203, 209, 215, 217, 223, 224, 225, 227, 228, 233, 239, 252, 255, 257, 265, 266, 269, 271, 279, 284, 287, 289, 297, 299, 303, 311, 314, 316, 319, 336, 338, 342, 343, 353, 355, 356, 359, 361, 374, 378, 379, 380, 383, 385, 399, 400, 406, 415, 419, 421, 422, 425, 426, 451, 454, 457, 471, 473, 474, 475, 478, 479, 481, 499, 504, 505, 507, 511, 513, 533, 534, 538, 541, 553, 559, 561, 563, 566, 567, 570, 598, 600, 601, 605, 609, 620, 631, 633, 637, 639, 641, 662, 665, 673, 681, 711, 717, 721, 737, 745, 751, 755, 756, 796, 797, 801, 807, 827, 841, 849, 854, 855, 874, 883, 887, 890, 897, 900, 908, 930, 961, 983, 993, 994, 1001, 1007, 1046, 1061, 1063, 1103, 1112, 1118, 1121, 1134, 1139, 1165, 1177, 1178, 1183, 1187, 1194]

def E (x : ℕ) : Prop :=
  x < 96 ∨ x ∈ E_list

instance (x : ℕ) : Decidable (E x) := by
  dsimp [E]
  infer_instance

theorem E_preimage_all_sub_1 : ∀ d < 150, E (A006368_map (d)) → E (d) := by decide
theorem E_preimage_all_sub_2 : ∀ d < 150, E (A006368_map (150 + d)) → E (150 + d) := by decide
theorem E_preimage_all_sub_3 : ∀ d < 150, E (A006368_map (300 + d)) → E (300 + d) := by decide
theorem E_preimage_all_sub_4 : ∀ d < 150, E (A006368_map (450 + d)) → E (450 + d) := by decide
theorem E_preimage_all_sub_5 : ∀ d < 150, E (A006368_map (600 + d)) → E (600 + d) := by decide
theorem E_preimage_all_sub_6 : ∀ d < 150, E (A006368_map (750 + d)) → E (750 + d) := by decide
theorem E_preimage_all_sub_7 : ∀ d < 150, E (A006368_map (900 + d)) → E (900 + d) := by decide
theorem E_preimage_all_sub_8 : ∀ d < 148, E (A006368_map (1050 + d)) → E (1050 + d) := by decide

theorem E_preimage_all (x : ℕ) (h : x < 1198) (h_map : E (A006368_map x)) : E x := by
  rcases lt_or_ge x 150 with h1 | h1
  · exact E_preimage_all_sub_1 x h1 h_map
  rcases lt_or_ge x 300 with h_lim2 | h_lim2
  · have hd : x - 150 < 150 := by omega
    have h_dec := E_preimage_all_sub_2 (x - 150) hd
    have h_eq : 150 + (x - 150) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_map
  rcases lt_or_ge x 450 with h_lim3 | h_lim3
  · have hd : x - 300 < 150 := by omega
    have h_dec := E_preimage_all_sub_3 (x - 300) hd
    have h_eq : 300 + (x - 300) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_map
  rcases lt_or_ge x 600 with h_lim4 | h_lim4
  · have hd : x - 450 < 150 := by omega
    have h_dec := E_preimage_all_sub_4 (x - 450) hd
    have h_eq : 450 + (x - 450) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_map
  rcases lt_or_ge x 750 with h_lim5 | h_lim5
  · have hd : x - 600 < 150 := by omega
    have h_dec := E_preimage_all_sub_5 (x - 600) hd
    have h_eq : 600 + (x - 600) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_map
  rcases lt_or_ge x 900 with h_lim6 | h_lim6
  · have hd : x - 750 < 150 := by omega
    have h_dec := E_preimage_all_sub_6 (x - 750) hd
    have h_eq : 750 + (x - 750) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_map
  rcases lt_or_ge x 1050 with h_lim7 | h_lim7
  · have hd : x - 900 < 150 := by omega
    have h_dec := E_preimage_all_sub_7 (x - 900) hd
    have h_eq : 900 + (x - 900) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_map
  have hd : x - 1050 < 148 := by omega
  have h_dec := E_preimage_all_sub_8 (x - 1050) hd
  have h_eq : 1050 + (x - 1050) = x := by omega
  rw [h_eq] at h_dec; exact h_dec h_map

theorem map_ge_1195_of_ge_1594 (x : ℕ) (h : x ≥ 1594) : A006368_map x ≥ 1195 := by
  dsimp [A006368_map]
  split_ifs with h1 h2
  · have : 3 * x ≥ 4782 := by omega
    omega
  · have : 3 * x + 1 ≥ 4783 := by omega
    omega
  · have : 3 * x - 1 ≥ 4781 := by omega
    omega

theorem lt_1195_of_E (x : ℕ) (h : E x) : x < 1195 := by
  rcases h with h1 | h1
  · omega
  · have h_all : ∀ y ∈ E_list, y < 1195 := by decide
    exact h_all x h1

theorem not_E_of_ge_1195 (x : ℕ) (h : x ≥ 1195) : ¬ E x := by
  intro hy
  have : x < 1195 := lt_1195_of_E x hy
  omega

theorem ge_96_of_not_dangerous (x : ℕ) (h_ge : x ≥ 96) (h_not : ¬ Dangerous x) :
  A006368_map x ≥ 96 := by
  dsimp [A006368_map]
  dsimp [Dangerous] at h_not
  push_neg at h_not
  split_ifs with h1 h2
  · omega
  · omega
  · omega

def Failures_new (x : ℕ) : Prop :=
  x ∈ ([1211, 1246, 1258, 1276, 1281, 1311, 1318, 1325, 1335, 1343, 1350, 1362, 1395, 1402, 1415, 1417, 1454, 1471, 1483, 1491, 1495, 1519, 1532, 1553, 1562, 1569, 1571, 1577, 1583, 1615, 1636, 1661, 1668, 1677, 1701, 1720, 1757, 1767, 1791, 1862, 1869, 1887, 1889, 1914, 1939, 1961, 1977, 1993, 2025, 2038, 2043, 2071, 2083, 2095, 2103, 2111, 2153, 2181, 2215, 2293, 2298, 2343, 2362, 2454, 2483, 2502, 2519, 2580, 2585, 2615, 2654, 2657, 2717, 2728, 2761, 2777, 2793, 2815, 2871, 2953, 2986, 3057, 3146, 3149, 3311, 3359, 3447, 3487, 3539, 3543, 3623, 3637, 3681, 3703, 3753, 3870, 3884, 3928, 3937, 3981, 4024, 4092, 4195, 4199, 4294, 4310, 4354, 4415, 4479, 4649, 4666, 4719, 4831, 4849, 4898, 4937] : List ℕ)

instance (x : ℕ) : Decidable (Failures_new x) := by
  dsimp [Failures_new]
  infer_instance

theorem E_of_Dangerous (z : ℕ) (h : Dangerous z) : E z := by
  rcases lt_or_ge z 96 with hz | hz
  · left; exact hz
  · right
    have h_all : ∀ d < 128, 97 ≤ d → d % 2 = 1 → d ∈ E_list := by decide
    dsimp [Dangerous] at h
    have hz_lt : z < 128 := by omega
    exact h_all z hz_lt h.right.left h.left

theorem not_failures_and_E_of_mid_sub_1 : ∀ d < 150, ¬ Failures_new (1198 + d) → ¬ E (A006368_map (1198 + d)) := by decide
theorem not_failures_and_E_of_mid_sub_2 : ∀ d < 150, ¬ Failures_new (1348 + d) → ¬ E (A006368_map (1348 + d)) := by decide
theorem not_failures_and_E_of_mid_sub_3 : ∀ d < 96, ¬ Failures_new (1498 + d) → ¬ E (A006368_map (1498 + d)) := by decide

theorem not_failures_and_E_of_mid (x : ℕ) (h1 : 1198 ≤ x) (h2 : x < 1594) (h3 : ¬ Failures_new x) :
  ¬ E (A006368_map x) := by
  rcases lt_or_ge x 1348 with h_lim1 | h_lim1
  · have hd : x - 1198 < 150 := by omega
    have h_dec := not_failures_and_E_of_mid_sub_1 (x - 1198) hd
    have h_eq : 1198 + (x - 1198) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h3
  rcases lt_or_ge x 1498 with h_lim2 | h_lim2
  · have hd : x - 1348 < 150 := by omega
    have h_dec := not_failures_and_E_of_mid_sub_2 (x - 1348) hd
    have h_eq : 1348 + (x - 1348) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h3
  have hd : x - 1498 < 96 := by omega
  have h_dec := not_failures_and_E_of_mid_sub_3 (x - 1498) hd
  have h_eq : 1498 + (x - 1498) = x := by omega
  rw [h_eq] at h_dec; exact h_dec h3

theorem preimages_of_failures_lt_1198_sub_1 : ∀ d < 150, Failures_new (A006368_map (d)) → E (d) := by decide
theorem preimages_of_failures_lt_1198_sub_2 : ∀ d < 150, Failures_new (A006368_map (150 + d)) → E (150 + d) := by decide
theorem preimages_of_failures_lt_1198_sub_3 : ∀ d < 150, Failures_new (A006368_map (300 + d)) → E (300 + d) := by decide
theorem preimages_of_failures_lt_1198_sub_4 : ∀ d < 150, Failures_new (A006368_map (450 + d)) → E (450 + d) := by decide
theorem preimages_of_failures_lt_1198_sub_5 : ∀ d < 150, Failures_new (A006368_map (600 + d)) → E (600 + d) := by decide
theorem preimages_of_failures_lt_1198_sub_6 : ∀ d < 150, Failures_new (A006368_map (750 + d)) → E (750 + d) := by decide
theorem preimages_of_failures_lt_1198_sub_7 : ∀ d < 150, Failures_new (A006368_map (900 + d)) → E (900 + d) := by decide
theorem preimages_of_failures_lt_1198_sub_8 : ∀ d < 148, Failures_new (A006368_map (1050 + d)) → E (1050 + d) := by decide

theorem preimages_of_failures_lt_1198 (x : ℕ) (h : x < 1198) (h_fail_map : Failures_new (A006368_map x)) : E x := by
  rcases lt_or_ge x 150 with h1 | h1
  · exact preimages_of_failures_lt_1198_sub_1 x h1 h_fail_map
  rcases lt_or_ge x 300 with h_lim2 | h_lim2
  · have hd : x - 150 < 150 := by omega
    have h_dec := preimages_of_failures_lt_1198_sub_2 (x - 150) hd
    have h_eq : 150 + (x - 150) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 450 with h_lim3 | h_lim3
  · have hd : x - 300 < 150 := by omega
    have h_dec := preimages_of_failures_lt_1198_sub_3 (x - 300) hd
    have h_eq : 300 + (x - 300) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 600 with h_lim4 | h_lim4
  · have hd : x - 450 < 150 := by omega
    have h_dec := preimages_of_failures_lt_1198_sub_4 (x - 450) hd
    have h_eq : 450 + (x - 450) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 750 with h_lim5 | h_lim5
  · have hd : x - 600 < 150 := by omega
    have h_dec := preimages_of_failures_lt_1198_sub_5 (x - 600) hd
    have h_eq : 600 + (x - 600) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 900 with h_lim6 | h_lim6
  · have hd : x - 750 < 150 := by omega
    have h_dec := preimages_of_failures_lt_1198_sub_6 (x - 750) hd
    have h_eq : 750 + (x - 750) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 1050 with h_lim7 | h_lim7
  · have hd : x - 900 < 150 := by omega
    have h_dec := preimages_of_failures_lt_1198_sub_7 (x - 900) hd
    have h_eq : 900 + (x - 900) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  have hd : x - 1050 < 148 := by omega
  have h_dec := preimages_of_failures_lt_1198_sub_8 (x - 1050) hd
  have h_eq : 1050 + (x - 1050) = x := by omega
  rw [h_eq] at h_dec; exact h_dec h_fail_map

theorem preimages_of_failures_mid_sub_1 : ∀ d < 150, Failures_new (A006368_map (1198 + d)) → Failures_new (1198 + d) := by decide
theorem preimages_of_failures_mid_sub_2 : ∀ d < 150, Failures_new (A006368_map (1348 + d)) → Failures_new (1348 + d) := by decide
theorem preimages_of_failures_mid_sub_3 : ∀ d < 150, Failures_new (A006368_map (1498 + d)) → Failures_new (1498 + d) := by decide
theorem preimages_of_failures_mid_sub_4 : ∀ d < 150, Failures_new (A006368_map (1648 + d)) → Failures_new (1648 + d) := by decide
theorem preimages_of_failures_mid_sub_5 : ∀ d < 150, Failures_new (A006368_map (1798 + d)) → Failures_new (1798 + d) := by decide
theorem preimages_of_failures_mid_sub_6 : ∀ d < 150, Failures_new (A006368_map (1948 + d)) → Failures_new (1948 + d) := by decide
theorem preimages_of_failures_mid_sub_7 : ∀ d < 150, Failures_new (A006368_map (2098 + d)) → Failures_new (2098 + d) := by decide
theorem preimages_of_failures_mid_sub_8 : ∀ d < 150, Failures_new (A006368_map (2248 + d)) → Failures_new (2248 + d) := by decide
theorem preimages_of_failures_mid_sub_9 : ∀ d < 150, Failures_new (A006368_map (2398 + d)) → Failures_new (2398 + d) := by decide
theorem preimages_of_failures_mid_sub_10 : ∀ d < 150, Failures_new (A006368_map (2548 + d)) → Failures_new (2548 + d) := by decide
theorem preimages_of_failures_mid_sub_11 : ∀ d < 150, Failures_new (A006368_map (2698 + d)) → Failures_new (2698 + d) := by decide
theorem preimages_of_failures_mid_sub_12 : ∀ d < 150, Failures_new (A006368_map (2848 + d)) → Failures_new (2848 + d) := by decide
theorem preimages_of_failures_mid_sub_13 : ∀ d < 150, Failures_new (A006368_map (2998 + d)) → Failures_new (2998 + d) := by decide
theorem preimages_of_failures_mid_sub_14 : ∀ d < 150, Failures_new (A006368_map (3148 + d)) → Failures_new (3148 + d) := by decide
theorem preimages_of_failures_mid_sub_15 : ∀ d < 150, Failures_new (A006368_map (3298 + d)) → Failures_new (3298 + d) := by decide
theorem preimages_of_failures_mid_sub_16 : ∀ d < 150, Failures_new (A006368_map (3448 + d)) → Failures_new (3448 + d) := by decide
theorem preimages_of_failures_mid_sub_17 : ∀ d < 150, Failures_new (A006368_map (3598 + d)) → Failures_new (3598 + d) := by decide
theorem preimages_of_failures_mid_sub_18 : ∀ d < 150, Failures_new (A006368_map (3748 + d)) → Failures_new (3748 + d) := by decide
theorem preimages_of_failures_mid_sub_19 : ∀ d < 150, Failures_new (A006368_map (3898 + d)) → Failures_new (3898 + d) := by decide
theorem preimages_of_failures_mid_sub_20 : ∀ d < 150, Failures_new (A006368_map (4048 + d)) → Failures_new (4048 + d) := by decide
theorem preimages_of_failures_mid_sub_21 : ∀ d < 150, Failures_new (A006368_map (4198 + d)) → Failures_new (4198 + d) := by decide
theorem preimages_of_failures_mid_sub_22 : ∀ d < 150, Failures_new (A006368_map (4348 + d)) → Failures_new (4348 + d) := by decide
theorem preimages_of_failures_mid_sub_23 : ∀ d < 150, Failures_new (A006368_map (4498 + d)) → Failures_new (4498 + d) := by decide
theorem preimages_of_failures_mid_sub_24 : ∀ d < 150, Failures_new (A006368_map (4648 + d)) → Failures_new (4648 + d) := by decide
theorem preimages_of_failures_mid_sub_25 : ∀ d < 150, Failures_new (A006368_map (4798 + d)) → Failures_new (4798 + d) := by decide
theorem preimages_of_failures_mid_sub_26 : ∀ d < 57, Failures_new (A006368_map (4948 + d)) → Failures_new (4948 + d) := by decide

theorem preimages_of_failures_mid (x : ℕ) (h1 : x < 5005) (h2 : 1198 ≤ x) (h_fail_map : Failures_new (A006368_map x)) : Failures_new x := by
  rcases lt_or_ge x 1348 with h_lim1 | h_lim1
  · have hd : x - 1198 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_1 (x - 1198) hd
    have h_eq : 1198 + (x - 1198) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 1498 with h_lim2 | h_lim2
  · have hd : x - 1348 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_2 (x - 1348) hd
    have h_eq : 1348 + (x - 1348) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 1648 with h_lim3 | h_lim3
  · have hd : x - 1498 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_3 (x - 1498) hd
    have h_eq : 1498 + (x - 1498) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 1798 with h_lim4 | h_lim4
  · have hd : x - 1648 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_4 (x - 1648) hd
    have h_eq : 1648 + (x - 1648) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 1948 with h_lim5 | h_lim5
  · have hd : x - 1798 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_5 (x - 1798) hd
    have h_eq : 1798 + (x - 1798) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 2098 with h_lim6 | h_lim6
  · have hd : x - 1948 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_6 (x - 1948) hd
    have h_eq : 1948 + (x - 1948) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 2248 with h_lim7 | h_lim7
  · have hd : x - 2098 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_7 (x - 2098) hd
    have h_eq : 2098 + (x - 2098) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 2398 with h_lim8 | h_lim8
  · have hd : x - 2248 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_8 (x - 2248) hd
    have h_eq : 2248 + (x - 2248) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 2548 with h_lim9 | h_lim9
  · have hd : x - 2398 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_9 (x - 2398) hd
    have h_eq : 2398 + (x - 2398) = x := by omega
    rw [h_eq] at h_dec; exact h_dec h_fail_map
  rcases lt_or_ge x 2698 with h_lim10 | h_lim10
  · have hd : x - 2548 < 150 := by omega
    have h_dec := preimages_of_failures_mid_sub_10 (x - 2548) hd
