import Mathlib

set_option maxRecDepth 200000
open Nat

def fast_totient_aux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => fast_totient_aux n k (acc + (if n.Coprime (k + 1) then 1 else 0))

lemma fast_totient_aux_add (n k : ℕ) (acc : ℕ) :
  fast_totient_aux n k acc = acc + fast_totient_aux n k 0 := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [fast_totient_aux]
    rw [ih (acc + if n.Coprime (k + 1) then 1 else 0)]
    have h1 : fast_totient_aux n (k + 1) 0 = fast_totient_aux n k (if n.Coprime (k + 1) then 1 else 0) := by
      rw [fast_totient_aux, zero_add]
    rw [h1, ih (if n.Coprime (k + 1) then 1 else 0)]
    omega

lemma fast_totient_aux_eq_card (n k : ℕ) :
  fast_totient_aux n k 0 + (if n.Coprime 0 then 1 else 0) = (Finset.filter n.Coprime (Finset.range (k + 1))).card := by
  induction k with
  | zero =>
    simp only [fast_totient_aux]
    have h_range : Finset.range 1 = {0} := rfl
    rw [h_range, Finset.filter_singleton]
    split_ifs with h
    · simp only [Finset.card_singleton]
    · simp only [Finset.card_empty]
  | succ k ih =>
    rw [fast_totient_aux, fast_totient_aux_add]
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases h_coprime : n.Coprime (k + 1)
    · have h_if : (if n.Coprime (k + 1) then insert (k + 1) (Finset.filter n.Coprime (Finset.range (k + 1))) else Finset.filter n.Coprime (Finset.range (k + 1))) = insert (k + 1) (Finset.filter n.Coprime (Finset.range (k + 1))) := if_pos h_coprime
      rw [h_if]
      rw [Finset.card_insert_of_notMem]
      · rw [← ih]
        split_ifs <;> omega
      · intro h_mem
        rw [Finset.mem_filter] at h_mem
        rw [Finset.mem_range] at h_mem
        omega
    · have h_if : (if n.Coprime (k + 1) then insert (k + 1) (Finset.filter n.Coprime (Finset.range (k + 1))) else Finset.filter n.Coprime (Finset.range (k + 1))) = Finset.filter n.Coprime (Finset.range (k + 1)) := if_neg h_coprime
      rw [h_if]
      rw [← ih]
      split_ifs <;> omega

def fast_totient (n : ℕ) : ℕ := fast_totient_aux n n 0

lemma fast_totient_eq_totient (n : ℕ) : fast_totient n = Nat.totient n := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · have h_not_coprime_zero : ¬ (n + 2).Coprime 0 := by
      intro h
      rw [Nat.coprime_zero_right] at h
      omega
    have h_not_coprime_self : ¬ (n + 2).Coprime (n + 2) := by
      intro h
      unfold Coprime at h
      rw [gcd_self] at h
      omega
    have h_eq := fast_totient_aux_eq_card (n + 2) (n + 2)
    rw [if_neg h_not_coprime_zero] at h_eq
    rw [add_zero] at h_eq
    unfold fast_totient
    rw [h_eq]
    have h_range : Finset.range (n + 3) = insert (n + 2) (Finset.range (n + 2)) := Finset.range_succ
    rw [h_range, Finset.filter_insert, if_neg h_not_coprime_self]
    rfl

def witness_list : List ℕ := [
  1, 4, 9, 8, 25, 18, 15, 16, 21, 50,
  35, 36, 33, 98, 39, 32, 65, 54, 51, 100,
  45, 70, 95, 72, 69, 338, 63, 196, 161, 110,
  87, 64, 93, 130, 75, 108, 217, 182, 99, 200,
  185, 170, 123, 140, 117, 190, 215, 144, 141, 250,
  235, 676, 329, 162, 159, 392, 153, 322, 371, 220,
  177, 494, 135, 128, 305, 290, 427, 260, 201, 310,
  335, 216, 213, 434, 207, 364, 245, 638, 511, 400,
  189, 370, 395, 340, 249, 518, 415, 280, 581, 410,
  267, 380, 261, 430, 623, 288, 1501, 602, 279, 500,
  485, 462, 303, 1352, 225, 658, 515, 324, 321, 350,
  231, 784, 545, 530, 339, 644, 297, 742, 539, 440,
  1331, 1634, 1243, 988, 625, 510, 255, 256, 273, 610,
  635, 580, 393, 854, 351, 520, 917, 570, 411, 620,
  285, 670, 363, 432, 385, 938, 423, 868, 1529, 550,
  447, 728, 453, 490, 755, 1276, 1057, 1022, 471, 800,
  785, 486, 1099, 740, 357, 790, 455, 680, 345, 650,
  459, 1036, 1169, 830, 375, 560, 865, 1162, 1211, 820,
  537, 2054, 399, 760, 905, 890, 847, 860, 405, 1246,
  1991, 576, 573, 3002, 507, 1204, 965, 870, 591, 1000,
  597, 970, 995, 924, 925, 1358, 603, 2704, 2189, 850,
  435, 1316, 633, 1030, 1055, 648, 1477, 1442, 483, 700,
  845, 1070, 2743, 1568, 465, 1090, 1115, 1060, 681, 950,
  687, 1288, 665, 1130, 699, 1484, 1165, 1078, 1631, 880,
  561, 2662, 567, 3268, 1205, 1110, 1183, 1976, 1785, 1250,
  2651, 1020, 753, 4142, 747, 512, 1757, 1554, 771, 1220,
  1285, 1270, 1799, 1160, 789, 1274, 555, 1708, 1841, 1150,
  807, 1040, 609, 1834, 875, 1140, 805, 3302, 663, 1240,
  1001, 1290, 843, 1340, 849, 1390, 1415, 864, 1981, 1946,
  651, 1876, 3113, 1806, 615, 1736, 837, 3058, 1859, 1100,
  1813, 3614, 2415, 1456, 3809, 1386, 8587, 980, 645, 1510,
  1535, 2552, 933, 2114, 675, 2044, 1565, 1974, 759, 1600,
  1585, 1570, 867, 972, 1045, 2198, 963, 1480, 2009, 1210,
  5947, 1580, 693, 1630, 1655, 1360, 705, 2282, 1011, 1300,
  1685, 1590, 1015, 2072, 777, 2338, 3707, 1660, 1041, 1550,
  891, 1120, 1745, 1730, 1059, 2324, 1445, 2422, 2471, 1640,
  1077, 6194, 1795, 4108, 1085, 1790, 6631, 1520, 897, 1810,
  1235, 1780, 2569, 1694, 1119, 1720, 1865, 1530, 795, 2492,
  765, 3982, 1463, 1152, 1149, 4706, 819, 6004, 2681, 1830,
  1167, 2408, 969, 1930, 1547, 1740, 957, 2702, 903, 2000,
  1985, 1970, 1203, 1940, 1053, 1990, 2807, 1848, 5161, 1850,
  1227, 2716, 2045, 1710, 1975, 5408, 1233, 4378, 4499, 1700,
  885, 5174, 855, 2632, 1625, 2010, 2947, 2060, 1089, 2110,
  1295, 1296, 1293, 2954, 915, 2884, 1805, 2814, 1495, 1400,
  1029, 1690, 2195, 2140, 1329, 5486, 2215, 3136, 3101, 2050,
  1347, 2180, 1341, 2230, 2891, 2120, 8341, 3122, 1131, 1900,
  2285, 2190, 1383, 2576, 1389, 2290, 2315, 2260, 1173, 1430,
  2335, 2968, 3269, 2330, 1435, 2156, 1005, 3262, 6071, 1760,
  1437, 5954, 2395, 5324, 3353, 1458, 14167, 6536, 1113, 2410,
  2435, 2220, 1473, 2366, 1071, 3952, 1505, 2370, 6331, 2500,
  1221, 5302, 2495, 2040, 1065, 3146, 1035, 8284, 2093, 2350,
  1527, 1024, 1377, 3514, 3563, 3108, 4477, 3038, 1095, 2440,
  6617, 2490, 1563, 2540, 1125, 3598, 2615, 2320, 3661, 16946,
  5731, 2548, 2261, 2630, 2575, 3416, 8857, 3682, 1715, 2300,
  1645, 14942, 1239, 2080, 2705, 2690, 1955, 3668, 1197, 1750,
  2735, 2280, 1353, 3794, 2675, 6604, 2717, 2670, 1671, 2480,
  1185, 2002, 3899, 2580, 1689, 3878, 1215, 2680, 3941, 2650,
  1707, 2780, 1713, 2830, 1587, 1728, 3997, 3962, 1419, 3892,
  2885, 6182, 1479, 3752, 1521, 6226, 2387, 3612, 1245, 1870,
  2935, 3472, 4109, 2610, 1779, 6116, 1773, 3718, 4151, 2200,
  1797, 3626, 1791, 7228, 3005, 2910, 1855, 2912, 1821, 7618,
  3035, 2772, 4249, 17174, 1407, 1960, 3065, 4074, 1851, 3020,
  1581, 3070, 2639, 5104, 2737, 4298, 5687, 4228, 6809, 2550,
  1335, 4088, 1305, 3130, 1275, 3948, 4417, 4382, 1599, 3200,
  6941, 3090, 1923, 3140, 1653, 4438, 3215, 1944, 1941, 2090,
  1491, 4396, 4529, 4326, 1959, 2960, 1449, 4018, 4571, 2420,
  1977, 11894, 1983, 3160, 3305, 3210, 3703, 3260, 1533, 3310,
  7271, 2720, 2065, 2210, 1395, 4564, 2405, 3270, 2031, 2600,
  3385, 3370, 3059, 3180, 2049, 4214, 1455, 4144, 2849, 2850,
  12787, 4676, 2061, 7414, 2135, 3320, 4837, 2618, 7035, 3100,
  7601, 3390, 2103, 2240, 1425, 3490, 4907, 3460, 1749, 3350,
  2127, 4648, 3545, 2890, 1515, 4844, 11917, 4942, 7799, 3280,
  2157, 9074, 1659, 12388, 1925, 3590, 13471, 8216, 1545, 5026,
  3635, 3580, 5089, 13262, 1887, 3040, 3665, 3330, 2755, 3620,
  2217, 2470, 3695, 3560, 2229, 5138, 3715, 3388, 4949, 2750,
  9607, 3440, 2253, 3730, 3755, 3060, 1605, 5222, 1743, 4984,
  2345, 12426, 2283, 7964, 2241, 2926, 5327, 2304, 2001, 2450,
  1635, 9412, 3845, 3830, 2319, 12008, 1617, 5362, 2795, 3660,
  4301, 4046, 8503, 4816, 2945, 3810, 1947, 3860, 2361, 3094,
  3311, 3480, 5509, 14402, 2367, 5404, 8657, 3822, 1695, 4000,
  1665, 3970, 5579, 3940, 2485, 5558, 8295, 3880, 3689, 3450,
  2091, 3980, 1869, 5614, 4055, 3696, 5677, 10322, 1827, 3700,
  8921, 5502, 2463, 5432, 2469, 4090, 2555, 3420, 2481, 3950,
  2487, 10816, 3773, 9906, 2275, 8756, 1989, 8998, 9119, 3400,
  2517, 10634, 4195, 10348, 1725, 3870, 3055, 5264, 2193, 3250,
  3731, 4020, 25513, 5894, 2547, 4120, 4265, 4170, 2571, 4220,
  2577, 2590, 4295, 2592, 2589, 3458, 4315, 5908, 6041, 4150,
  3335, 5768, 1953, 3610, 1875, 5628, 16321, 2990, 2631, 2800,
  4385, 5418, 2643, 3380, 1845, 4390, 4415, 4280, 2661, 6146,
  2211, 10972, 2765, 4430, 11479, 6272, 1905, 6202, 2523, 4100,
  10693, 3542, 1911, 4360, 16853, 4490, 27187, 4460, 2301, 5782,
  4535, 4240, 2733, 16682, 4475, 6244, 6377, 4158, 11791, 3800,
  2121, 4570, 3515, 4380, 1965, 3230, 1935, 5152, 5681, 4450,
  2787, 4580, 4645, 4630, 6503, 4520, 2905, 5978, 2163, 2860,
  4685, 4670, 2343, 5936, 2025, 6538, 4403, 4660, 2841, 2870,
  4735, 4312, 6629, 5922, 2859, 6524, 2277, 12142, 6419, 3520,
  4081, 17594, 10483, 11908, 4277, 4710, 2055, 10648, 2409, 6706,
  4835, 2916, 2913, 28334, 2247, 13072, 6797, 6594, 2931, 4820,
  2085, 4870, 6839, 4440, 2949, 6818, 4915, 4732, 6881, 4350,
  67087, 7904, 2289, 3010, 4955, 4740, 5797, 12662, 2079, 5000,
]

def witness (n : ℕ) : ℕ := witness_list.getD n 1

def check_witness (n : ℕ) : Bool :=
  let w := witness n
  (w > 0) && ((w - 1) % fast_totient w == n)

def check_witness_block (start : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => check_witness_block start n && check_witness (start + n)

lemma check_witness_of_check_witness_block {start K : ℕ} (h : check_witness_block start K = true) (n : ℕ) (hn : n < K) : check_witness (start + n) = true := by
  revert h n hn
  induction K with
  | zero =>
    intro h n hn
    omega
  | succ m ih =>
    intro h n hn
    simp [check_witness_block] at h
    have h1 : check_witness_block start m = true := h.1
    have h2 : check_witness (start + m) = true := h.2
    have h_cases : n = m ∨ n < m := by omega
    rcases h_cases with rfl | h_lt
    · exact h2
    · exact ih h1 n h_lt

lemma check_block_0 : check_witness_block 0 100 = true := by decide
lemma check_block_1 : check_witness_block 100 100 = true := by decide
lemma check_block_2 : check_witness_block 200 100 = true := by decide
lemma check_block_3 : check_witness_block 300 100 = true := by decide
lemma check_block_4 : check_witness_block 400 100 = true := by decide
lemma check_block_5 : check_witness_block 500 100 = true := by decide
lemma check_block_6 : check_witness_block 600 100 = true := by decide
lemma check_block_7 : check_witness_block 700 100 = true := by decide
lemma check_block_8 : check_witness_block 800 100 = true := by decide
lemma check_block_9 : check_witness_block 900 100 = true := by decide

lemma witness_pos_and_mod (n : ℕ) (hn : n < 1000) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  have h_cw : check_witness n = true := by
    rcases lt_or_ge n 100 with h | h
    · have h_mod : n < 100 := h
      have h_ok := check_witness_of_check_witness_block check_block_0 n h_mod
      rw [zero_add] at h_ok
      exact h_ok
    rcases lt_or_ge n 200 with h_lt | h_ge
    · have h_mod : n - 100 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_1 (n - 100) h_mod
      have : 100 + (n - 100) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 300 with h_lt | h_ge
    · have h_mod : n - 200 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_2 (n - 200) h_mod
      have : 200 + (n - 200) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 400 with h_lt | h_ge
    · have h_mod : n - 300 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_3 (n - 300) h_mod
      have : 300 + (n - 300) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 500 with h_lt | h_ge
    · have h_mod : n - 400 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_4 (n - 400) h_mod
      have : 400 + (n - 400) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 600 with h_lt | h_ge
    · have h_mod : n - 500 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_5 (n - 500) h_mod
      have : 500 + (n - 500) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 700 with h_lt | h_ge
    · have h_mod : n - 600 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_6 (n - 600) h_mod
      have : 600 + (n - 600) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 800 with h_lt | h_ge
    · have h_mod : n - 700 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_7 (n - 700) h_mod
      have : 700 + (n - 700) = n := by omega
      rw [this] at h_ok
      exact h_ok
    rcases lt_or_ge n 900 with h_lt | h_ge
    · have h_mod : n - 800 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_8 (n - 800) h_mod
      have : 800 + (n - 800) = n := by omega
      rw [this] at h_ok
      exact h_ok
    · have h_mod : n - 900 < 100 := by omega
      have h_ok := check_witness_of_check_witness_block check_block_9 (n - 900) h_mod
      have : 900 + (n - 900) = n := by omega
      rw [this] at h_ok
      exact h_ok

  unfold check_witness at h_cw
  rw [Bool.and_eq_true, Bool.beq_eq_decide_eq] at h_cw
  have h_pos : witness n > 0 := by
    have := h_cw.1
    exact decide_eq_true_iff.mp this
  have h_mod : (witness n - 1) % Nat.totient (witness n) = n := by
    have := h_cw.2
    have h_ft := of_decide_eq_true this
    rw [fast_totient_eq_totient] at h_ft
    exact h_ft
  exact ⟨h_pos, h_mod⟩
