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

theorem E_preimage_all_1 : ∀ x < 100, E (A006368_map x) → E x := by decide
theorem E_preimage_all_2 : ∀ x < 200, 100 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_3 : ∀ x < 300, 200 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_4 : ∀ x < 400, 300 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_5 : ∀ x < 500, 400 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_6 : ∀ x < 600, 500 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_7 : ∀ x < 700, 600 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_8 : ∀ x < 800, 700 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_9 : ∀ x < 900, 800 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_10 : ∀ x < 1000, 900 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_11 : ∀ x < 1100, 1000 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_12 : ∀ x < 1198, 1100 ≤ x → E (A006368_map x) → E x := by decide

theorem E_preimage_all (x : ℕ) (h : x < 1198) (h_map : E (A006368_map x)) : E x := by
  rcases lt_or_ge x 100 with h1 | h1; exact E_preimage_all_1 x h1 h_map
  rcases lt_or_ge x 200 with h2 | h2; exact E_preimage_all_2 x h2 h1 h_map
  rcases lt_or_ge x 300 with h3 | h3; exact E_preimage_all_3 x h3 h2 h_map
  rcases lt_or_ge x 400 with h4 | h4; exact E_preimage_all_4 x h4 h3 h_map
  rcases lt_or_ge x 500 with h5 | h5; exact E_preimage_all_5 x h5 h4 h_map
  rcases lt_or_ge x 600 with h6 | h6; exact E_preimage_all_6 x h6 h5 h_map
  rcases lt_or_ge x 700 with h7 | h7; exact E_preimage_all_7 x h7 h6 h_map
  rcases lt_or_ge x 800 with h8 | h8; exact E_preimage_all_8 x h8 h7 h_map
  rcases lt_or_ge x 900 with h9 | h9; exact E_preimage_all_9 x h9 h8 h_map
  rcases lt_or_ge x 1000 with h10 | h10; exact E_preimage_all_10 x h10 h9 h_map
  rcases lt_or_ge x 1100 with h11 | h11; exact E_preimage_all_11 x h11 h10 h_map
  rcases lt_or_ge x 1198 with h12 | h12; exact E_preimage_all_12 x h12 h11 h_map
  exact E_preimage_all_12 x h h11 h_map

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
  x ∈ ([1211, 1246, 1258, 1276, 1281, 1311, 1318, 1325, 1335, 1343, 1350, 1362, 1395, 1402, 1415, 1417, 1454, 1471, 1483, 1491, 1495, 1519, 1532, 1553, 1562, 1569, 1571, 1577, 1583] : List ℕ)

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

theorem not_failures_and_E_of_mid_1 : ∀ x < 1298, 1198 ≤ x → ¬ Failures_new x → ¬ E (A006368_map x) := by decide
theorem not_failures_and_E_of_mid_2 : ∀ x < 1398, 1298 ≤ x → ¬ Failures_new x → ¬ E (A006368_map x) := by decide
theorem not_failures_and_E_of_mid_3 : ∀ x < 1498, 1398 ≤ x → ¬ Failures_new x → ¬ E (A006368_map x) := by decide
theorem not_failures_and_E_of_mid_4 : ∀ x < 1594, 1498 ≤ x → ¬ Failures_new x → ¬ E (A006368_map x) := by decide

theorem not_failures_and_E_of_mid (x : ℕ) (h1 : 1198 ≤ x) (h2 : x < 1594) (h3 : ¬ Failures_new x) :
  ¬ E (A006368_map x) := by
  rcases lt_or_ge x 1298 with h_lim1 | h_lim1; exact not_failures_and_E_of_mid_1 x h_lim1 h1 h3
  rcases lt_or_ge x 1398 with h_lim2 | h_lim2; exact not_failures_and_E_of_mid_2 x h_lim2 h_lim1 h3
  rcases lt_or_ge x 1498 with h_lim3 | h_lim3; exact not_failures_and_E_of_mid_3 x h_lim3 h_lim2 h3
  exact not_failures_and_E_of_mid_4 x h2 h_lim3 h3

theorem preimages_of_failures_lt_1198_1 : ∀ x < 100, Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_2 : ∀ x < 200, 100 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_3 : ∀ x < 300, 200 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_4 : ∀ x < 400, 300 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_5 : ∀ x < 500, 400 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_6 : ∀ x < 600, 500 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_7 : ∀ x < 700, 600 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_8 : ∀ x < 800, 700 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_9 : ∀ x < 900, 800 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_10 : ∀ x < 1000, 900 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_11 : ∀ x < 1100, 1000 ≤ x → Failures_new (A006368_map x) → E x := by decide
theorem preimages_of_failures_lt_1198_12 : ∀ x < 1198, 1100 ≤ x → Failures_new (A006368_map x) → E x := by decide

theorem preimages_of_failures_lt_1198 (x : ℕ) (h : x < 1198) (h_fail_map : Failures_new (A006368_map x)) : E x := by
  rcases lt_or_ge x 100 with h1 | h1; exact preimages_of_failures_lt_1198_1 x h1 h_fail_map
  rcases lt_or_ge x 200 with h2 | h2; exact preimages_of_failures_lt_1198_2 x h2 h1 h_fail_map
  rcases lt_or_ge x 300 with h3 | h3; exact preimages_of_failures_lt_1198_3 x h3 h2 h_fail_map
  rcases lt_or_ge x 400 with h4 | h4; exact preimages_of_failures_lt_1198_4 x h4 h3 h_fail_map
  rcases lt_or_ge x 500 with h5 | h5; exact preimages_of_failures_lt_1198_5 x h5 h4 h_fail_map
  rcases lt_or_ge x 600 with h6 | h6; exact preimages_of_failures_lt_1198_6 x h6 h5 h_fail_map
  rcases lt_or_ge x 700 with h7 | h7; exact preimages_of_failures_lt_1198_7 x h7 h6 h_fail_map
  rcases lt_or_ge x 800 with h8 | h8; exact preimages_of_failures_lt_1198_8 x h8 h7 h_fail_map
  rcases lt_or_ge x 900 with h9 | h9; exact preimages_of_failures_lt_1198_9 x h9 h8 h_fail_map
  rcases lt_or_ge x 1000 with h10 | h10; exact preimages_of_failures_lt_1198_10 x h10 h9 h_fail_map
  rcases lt_or_ge x 1100 with h11 | h11; exact preimages_of_failures_lt_1198_11 x h11 h10 h_fail_map
  rcases lt_or_ge x 1198 with h12 | h12; exact preimages_of_failures_lt_1198_12 x h12 h11 h_fail_map
  exact preimages_of_failures_lt_1198_12 x h h11 h_fail_map

theorem preimages_of_failures_mid_1 : ∀ x < 1298, 1198 ≤ x → Failures_new (A006368_map x) → Failures_new x := by decide
theorem preimages_of_failures_mid_2 : ∀ x < 1398, 1298 ≤ x → Failures_new (A006368_map x) → Failures_new x := by decide
theorem preimages_of_failures_mid_3 : ∀ x < 1498, 1398 ≤ x → Failures_new (A006368_map x) → Failures_new x := by decide
theorem preimages_of_failures_mid_4 : ∀ x < 1594, 1498 ≤ x → Failures_new (A006368_map x) → Failures_new x := by decide

theorem preimages_of_failures_mid (x : ℕ) (h1 : x < 1594) (h2 : 1198 ≤ x) (h_fail_map : Failures_new (A006368_map x)) : Failures_new x := by
  rcases lt_or_ge x 1298 with h_lim1 | h_lim1; exact preimages_of_failures_mid_1 x h_lim1 h2 h_fail_map
  rcases lt_or_ge x 1398 with h_lim2 | h_lim2; exact preimages_of_failures_mid_2 x h_lim2 h_lim1 h_fail_map
  rcases lt_or_ge x 1498 with h_lim3 | h_lim3; exact preimages_of_failures_mid_3 x h_lim3 h_lim2 h_fail_map
  exact preimages_of_failures_mid_4 x h1 h_lim3 h_fail_map

theorem map_ge_1584_of_ge_2112 (x : ℕ) (h : x ≥ 2112) : A006368_map x ≥ 1584 := by
  dsimp [A006368_map]
  split_ifs with h1 h2
  · have : 3 * x ≥ 6336 := by omega
    omega
  · have : 3 * x + 1 ≥ 6337 := by omega
    omega
  · have : 3 * x - 1 ≥ 6335 := by omega
    omega

theorem not_failures_of_ge_1594 (x : ℕ) (h : x ≥ 1594) : ¬ Failures_new x := by
  intro hy
  dsimp [Failures_new] at hy
  have h_all : ∀ y ∈ ([1211, 1246, 1258, 1276, 1281, 1311, 1318, 1325, 1335, 1343, 1350, 1362, 1395, 1402, 1415, 1417, 1454, 1471, 1483, 1491, 1495, 1519, 1532, 1553, 1562, 1569, 1571, 1577, 1583] : List ℕ), y < 1594 := by decide
  have h_lt := h_all x hy
  omega


def Bad_chain_list : List ℕ := [890, 1615, 1636, 1661, 1668, 1677, 1701, 1720, 1757, 1767, 1791, 1862, 1869, 1887, 1889, 1914, 1939, 1961, 1977, 1993, 2025, 2038, 2043, 2071, 2083, 2095, 2103, 2111, 2153, 2181, 2215, 2293, 2298, 2343, 2362, 2454, 2483, 2502, 2519, 2580, 2585, 2615, 2654, 2657, 2717, 2728, 2761, 2777, 2793, 2815, 2871, 2953, 2986, 3057, 3146, 3149, 3311, 3359, 3447, 3487, 3539, 3543, 3623, 3637, 3681, 3703, 3753, 3870, 3884, 3937, 3981, 4092, 4195, 4199, 4294, 4310, 4354, 4415, 4479, 4649, 4666, 4719, 4831, 4849, 4898, 4937, 5179, 5249, 5510, 5530, 5593, 5599, 5725, 5747, 5805, 5826, 5887, 6138, 6199, 6221, 6441, 6465, 6531, 6554, 6583, 6905, 6999, 7347, 7373, 7457, 7465, 7633, 7663, 7849, 8265, 8295, 8739, 8777, 9207, 9831, 9943, 9953, 10177, 10217, 10465, 11703, 13257, 13271, 13569, 13623, 13953, 17695, 23593, 31457, 41943]

def Bad_chain (x : ℕ) : Prop :=
  x ∈ Bad_chain_list

instance (x : ℕ) : Decidable (Bad_chain x) := by
  dsimp [Bad_chain]
  infer_instance

theorem preimages_of_bad_chain_lt_1594_new_1 : ∀ x < 500, Bad_chain (A006368_map x) → E x ∨ Failures_new x ∨ Bad_chain x := by decide
theorem preimages_of_bad_chain_lt_1594_new_2 : ∀ x < 1000, 500 ≤ x → Bad_chain (A006368_map x) → E x ∨ Failures_new x ∨ Bad_chain x := by decide
theorem preimages_of_bad_chain_lt_1594_new_3 : ∀ x < 1594, 1000 ≤ x → Bad_chain (A006368_map x) → E x ∨ Failures_new x ∨ Bad_chain x := by decide

theorem preimages_of_bad_chain_lt_1594 (x : ℕ) (h : x < 1594) (h_bad_map : Bad_chain (A006368_map x)) :
  E x ∨ Failures_new x ∨ Bad_chain x := by
  rcases lt_or_ge x 500 with h1 | h1
  · exact preimages_of_bad_chain_lt_1594_new_1 x h1 h_bad_map
  · rcases lt_or_ge x 1000 with h2 | h2
    · exact preimages_of_bad_chain_lt_1594_new_2 x h2 h1 h_bad_map
    · exact preimages_of_bad_chain_lt_1594_new_3 x h h2 h_bad_map

theorem preimages_of_bad_chain_ge_1594_sub_1_1 : ∀ x < 1994, 1594 ≤ x → Bad_chain (A006368_map x) → Bad_chain x := by decide
theorem preimages_of_bad_chain_ge_1594_sub_1_2 : ∀ x < 2394, 1994 ≤ x → Bad_chain (A006368_map x) → Bad_chain x := by decide
