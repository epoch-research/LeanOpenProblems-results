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

def E_list : List ℕ := [97, 98, 99, 100, 101, 102, 103, 105, 106, 107, 109, 110, 111, 112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 141, 143, 145, 147, 149, 150, 151, 152, 153, 157, 159, 161, 163, 165, 167, 168, 169, 170, 175, 177, 179, 183, 186, 191, 193, 198, 199, 201, 202, 203, 209, 215, 217, 223, 225, 227, 228, 233, 239, 252, 255, 257, 265, 269, 271, 279, 284, 287, 289, 297, 303, 311, 314, 319, 338, 342, 343, 353, 356, 359, 361, 378, 379, 380, 383, 385, 406, 415, 419, 422, 425, 426, 451, 454, 457, 471, 475, 478, 479, 481, 505, 507, 511, 513, 534, 538, 541, 553, 559, 563, 566, 567, 570, 598, 601, 605, 609, 620, 633, 637, 639, 641, 662, 673, 681, 717, 721, 737, 745, 751, 755, 797, 801, 807, 827, 849, 854, 855, 874, 883, 890, 897, 930, 961, 983, 993, 1001, 1007, 1046, 1063, 1103, 1139, 1165, 1177, 1187, 1281, 1311, 1335, 1343, 1395, 1417, 1471, 1519, 1553, 1569, 1583, 1791, 1889, 1961, 2025, 2071]

def E (x : ℕ) : Prop :=
  x < 2072 ∧ (x < 96 ∨ x ∈ E_list)

instance (x : ℕ) : Decidable (E x) := by
  dsimp [E]
  infer_instance

theorem E_preimage_all_1 : ∀ x < 50, E (A006368_map x) → E x := by decide
theorem E_preimage_all_2 : ∀ x < 100, 50 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_3 : ∀ x < 150, 100 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_4 : ∀ x < 200, 150 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_5 : ∀ x < 250, 200 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_6 : ∀ x < 300, 250 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_7 : ∀ x < 350, 300 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_8 : ∀ x < 400, 350 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_9 : ∀ x < 450, 400 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_10 : ∀ x < 500, 450 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_11 : ∀ x < 550, 500 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_12 : ∀ x < 600, 550 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_13 : ∀ x < 650, 600 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_14 : ∀ x < 700, 650 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_15 : ∀ x < 750, 700 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_16 : ∀ x < 800, 750 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_17 : ∀ x < 850, 800 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_18 : ∀ x < 900, 850 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_19 : ∀ x < 950, 900 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_20 : ∀ x < 1000, 950 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_21 : ∀ x < 1050, 1000 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_22 : ∀ x < 1100, 1050 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_23 : ∀ x < 1150, 1100 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_24 : ∀ x < 1200, 1150 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_25 : ∀ x < 1250, 1200 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_26 : ∀ x < 1300, 1250 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_27 : ∀ x < 1350, 1300 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_28 : ∀ x < 1400, 1350 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_29 : ∀ x < 1450, 1400 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_30 : ∀ x < 1500, 1450 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_31 : ∀ x < 1550, 1500 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_32 : ∀ x < 1600, 1550 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_33 : ∀ x < 1650, 1600 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_34 : ∀ x < 1700, 1650 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_35 : ∀ x < 1750, 1700 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_36 : ∀ x < 1800, 1750 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_37 : ∀ x < 1850, 1800 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_38 : ∀ x < 1900, 1850 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_39 : ∀ x < 1950, 1900 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_40 : ∀ x < 2000, 1950 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_41 : ∀ x < 2050, 2000 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_42 : ∀ x < 2093, 2050 ≤ x → E (A006368_map x) → E x := by decide

theorem E_preimage_all (x : ℕ) (h : x < 2093) (h_map : E (A006368_map x)) : E x := by
  rcases lt_or_ge x 50 with h1 | h1
  · exact E_preimage_all_1 x h1 h_map
  · rcases lt_or_ge x 100 with h2 | h2
    · exact E_preimage_all_2 x h2 h1 h_map
  · rcases lt_or_ge x 150 with h3 | h3
    · exact E_preimage_all_3 x h3 h2 h_map
  · rcases lt_or_ge x 200 with h4 | h4
    · exact E_preimage_all_4 x h4 h3 h_map
  · rcases lt_or_ge x 250 with h5 | h5
    · exact E_preimage_all_5 x h5 h4 h_map
  · rcases lt_or_ge x 300 with h6 | h6
    · exact E_preimage_all_6 x h6 h5 h_map
  · rcases lt_or_ge x 350 with h7 | h7
    · exact E_preimage_all_7 x h7 h6 h_map
  · rcases lt_or_ge x 400 with h8 | h8
    · exact E_preimage_all_8 x h8 h7 h_map
  · rcases lt_or_ge x 450 with h9 | h9
    · exact E_preimage_all_9 x h9 h8 h_map
  · rcases lt_or_ge x 500 with h10 | h10
    · exact E_preimage_all_10 x h10 h9 h_map
  · rcases lt_or_ge x 550 with h11 | h11
    · exact E_preimage_all_11 x h11 h10 h_map
  · rcases lt_or_ge x 600 with h12 | h12
    · exact E_preimage_all_12 x h12 h11 h_map
  · rcases lt_or_ge x 650 with h13 | h13
    · exact E_preimage_all_13 x h13 h12 h_map
  · rcases lt_or_ge x 700 with h14 | h14
    · exact E_preimage_all_14 x h14 h13 h_map
  · rcases lt_or_ge x 750 with h15 | h15
    · exact E_preimage_all_15 x h15 h14 h_map
  · rcases lt_or_ge x 800 with h16 | h16
    · exact E_preimage_all_16 x h16 h15 h_map
  · rcases lt_or_ge x 850 with h17 | h17
    · exact E_preimage_all_17 x h17 h16 h_map
  · rcases lt_or_ge x 900 with h18 | h18
    · exact E_preimage_all_18 x h18 h17 h_map
  · rcases lt_or_ge x 950 with h19 | h19
    · exact E_preimage_all_19 x h19 h18 h_map
  · rcases lt_or_ge x 1000 with h20 | h20
    · exact E_preimage_all_20 x h20 h19 h_map
  · rcases lt_or_ge x 1050 with h21 | h21
    · exact E_preimage_all_21 x h21 h20 h_map
  · rcases lt_or_ge x 1100 with h22 | h22
    · exact E_preimage_all_22 x h22 h21 h_map
  · rcases lt_or_ge x 1150 with h23 | h23
    · exact E_preimage_all_23 x h23 h22 h_map
  · rcases lt_or_ge x 1200 with h24 | h24
    · exact E_preimage_all_24 x h24 h23 h_map
  · rcases lt_or_ge x 1250 with h25 | h25
    · exact E_preimage_all_25 x h25 h24 h_map
  · rcases lt_or_ge x 1300 with h26 | h26
    · exact E_preimage_all_26 x h26 h25 h_map
  · rcases lt_or_ge x 1350 with h27 | h27
    · exact E_preimage_all_27 x h27 h26 h_map
  · rcases lt_or_ge x 1400 with h28 | h28
    · exact E_preimage_all_28 x h28 h27 h_map
  · rcases lt_or_ge x 1450 with h29 | h29
    · exact E_preimage_all_29 x h29 h28 h_map
  · rcases lt_or_ge x 1500 with h30 | h30
    · exact E_preimage_all_30 x h30 h29 h_map
  · rcases lt_or_ge x 1550 with h31 | h31
    · exact E_preimage_all_31 x h31 h30 h_map
  · rcases lt_or_ge x 1600 with h32 | h32
    · exact E_preimage_all_32 x h32 h31 h_map
  · rcases lt_or_ge x 1650 with h33 | h33
    · exact E_preimage_all_33 x h33 h32 h_map
  · rcases lt_or_ge x 1700 with h34 | h34
    · exact E_preimage_all_34 x h34 h33 h_map
  · rcases lt_or_ge x 1750 with h35 | h35
    · exact E_preimage_all_35 x h35 h34 h_map
  · rcases lt_or_ge x 1800 with h36 | h36
    · exact E_preimage_all_36 x h36 h35 h_map
  · rcases lt_or_ge x 1850 with h37 | h37
    · exact E_preimage_all_37 x h37 h36 h_map
  · rcases lt_or_ge x 1900 with h38 | h38
    · exact E_preimage_all_38 x h38 h37 h_map
  · rcases lt_or_ge x 1950 with h39 | h39
    · exact E_preimage_all_39 x h39 h38 h_map
  · rcases lt_or_ge x 2000 with h40 | h40
    · exact E_preimage_all_40 x h40 h39 h_map
  · rcases lt_or_ge x 2050 with h41 | h41
    · exact E_preimage_all_41 x h41 h40 h_map
  · rcases lt_or_ge x 2093 with h42 | h42
    · exact E_preimage_all_42 x h42 h41 h_map
    · exact E_preimage_all_42 x h h41 h_map

theorem E_preimage_mid_1 : ∀ x < 2143, 2093 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_2 : ∀ x < 2193, 2143 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_3 : ∀ x < 2243, 2193 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_4 : ∀ x < 2293, 2243 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_5 : ∀ x < 2343, 2293 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_6 : ∀ x < 2393, 2343 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_7 : ∀ x < 2443, 2393 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_8 : ∀ x < 2493, 2443 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_9 : ∀ x < 2543, 2493 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_10 : ∀ x < 2593, 2543 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_11 : ∀ x < 2643, 2593 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_12 : ∀ x < 2693, 2643 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_13 : ∀ x < 2743, 2693 ≤ x → ¬ E (A006368_map x) := by decide
theorem E_preimage_mid_14 : ∀ x < 2793, 2743 ≤ x → ¬ E (A006368_map x) := by decide

theorem E_preimage_mid (x : ℕ) (h : x < 2793) (h_ge : 2093 ≤ x) : ¬ E (A006368_map x) := by
  rcases lt_or_ge x 2143 with h1 | h1
  · exact E_preimage_mid_1 x h1 h_ge
  · rcases lt_or_ge x 2193 with h2 | h2
    · exact E_preimage_mid_2 x h2 h1
  · rcases lt_or_ge x 2243 with h3 | h3
    · exact E_preimage_mid_3 x h3 h2
  · rcases lt_or_ge x 2293 with h4 | h4
    · exact E_preimage_mid_4 x h4 h3
  · rcases lt_or_ge x 2343 with h5 | h5
    · exact E_preimage_mid_5 x h5 h4
  · rcases lt_or_ge x 2393 with h6 | h6
    · exact E_preimage_mid_6 x h6 h5
  · rcases lt_or_ge x 2443 with h7 | h7
    · exact E_preimage_mid_7 x h7 h6
  · rcases lt_or_ge x 2493 with h8 | h8
    · exact E_preimage_mid_8 x h8 h7
  · rcases lt_or_ge x 2543 with h9 | h9
    · exact E_preimage_mid_9 x h9 h8
  · rcases lt_or_ge x 2593 with h10 | h10
    · exact E_preimage_mid_10 x h10 h9
  · rcases lt_or_ge x 2643 with h11 | h11
    · exact E_preimage_mid_11 x h11 h10
  · rcases lt_or_ge x 2693 with h12 | h12
    · exact E_preimage_mid_12 x h12 h11
  · rcases lt_or_ge x 2743 with h13 | h13
    · exact E_preimage_mid_13 x h13 h12
  · rcases lt_or_ge x 2793 with h14 | h14
    · exact E_preimage_mid_14 x h14 h13
    · exact E_preimage_mid_14 x h h13

theorem map_ge_2072_of_ge_2793 (x : ℕ) (h : x ≥ 2793) : A006368_map x ≥ 2072 := by
  dsimp [A006368_map]
  split_ifs with h1 h2
  · have : 3 * x ≥ 8380 := by omega
    omega
  · have : 3 * x + 1 ≥ 8380 := by omega
    omega
  · have : 3 * x - 1 ≥ 8378 := by omega
    omega

theorem lt_2072_of_E (x : ℕ) (h : E x) : x < 2072 := by
  exact h.left

theorem not_E_of_ge_2072 (x : ℕ) (h : x ≥ 2072) : ¬ E x := by
  intro hy
  have : x < 2072 := hy.left
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

theorem E_of_Dangerous (z : ℕ) (h : Dangerous z) : E z := by
  have h_all : ∀ d, Dangerous d → E d := by
    intro d hd
    dsimp [Dangerous] at hd
    dsimp [E]
    constructor
    · omega
    · right
      revert hd; decide
  exact h_all z h

inductive Reach96 : ℕ → Prop where
  | base : Reach96 96
  | step : ∀ x, Reach96 x → Reach96 (A006368_map x)

theorem Reach96_properties (x : ℕ) (h : Reach96 x) : x ≥ 96 ∧ ¬ E x := by
  induction h with
  | base =>
    constructor
    · omega
    · intro h_E
      rcases h_E with ⟨h_lt, h_or⟩
      rcases h_or with h1 | h1
      · omega
      · revert h1; decide
  | step z hz ih =>
    rcases ih with ⟨hz_ge, ih_not_E⟩
    have h_not_dangerous : ¬ Dangerous z := by
      intro hd
      apply ih_not_E
      exact E_of_Dangerous z hd
    have h_map_ge := ge_96_of_not_dangerous z hz_ge h_not_dangerous
    constructor
    · exact h_map_ge
    · intro h_E_map
      rcases lt_or_ge z 2093 with hz_lt | hz_ge2
      · have h_E := E_preimage_all z hz_lt h_E_map
        exact ih_not_E h_E
      · rcases lt_or_ge z 2793 with hz_lt2 | hz_ge3
        · have h_not_E_map := E_preimage_mid z hz_lt2 hz_ge2
          exact h_not_E_map h_E_map
        · have h_map_ge2 := map_ge_2072_of_ge_2793 z hz_ge3
          have h_not_E_map := not_E_of_ge_2072 (A006368_map z) h_map_ge2
          exact h_not_E_map h_E_map

theorem Reach96_ge_96 (x : ℕ) (h : Reach96 x) : x ≥ 96 :=
  (Reach96_properties x h).left

lemma Reach96_iterate (m : ℕ) : Reach96 (A006368_map^[m] 96) := by
  induction m with
  | zero => exact Reach96.base
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact Reach96.step (A006368_map^[m] 96) ih

def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

theorem a_ge_96 (n : ℕ) (hn : n ≥ 2) : a n ≥ 96 := by
  dsimp [a]
  have h_eq : n - 1 = n - 2 + 1 := by omega
  rw [h_eq, Function.iterate_succ_apply]
  have h_64 : A006368_map 64 = 96 := rfl
  rw [h_64]
  exact Reach96_ge_96 (A006368_map^[n - 2] 96) (Reach96_iterate (n - 2))

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj h
  have h_not_periodic : ∀ (k : ℕ), k > 0 → A006368_map^[k] 64 ≠ 64 := by
    intro k hk
    have h_eq : A006368_map^[k] 64 = a (k + 1) := by
      dsimp [a]
      have : k + 1 - 1 = k := by omega
      rw [this]
    rw [h_eq]
    have hk2 : k + 1 ≥ 2 := by omega
    have h_ge := a_ge_96 (k + 1) hk2
    omega
  have h_inj : ∀ (i j : ℕ), A006368_map^[i] 64 = A006368_map^[j] 64 → i = j :=
    iterate_injective_of_not_periodic A006368_map_injective h_not_periodic
  dsimp [a] at h
  have h_eq2 := h_inj (i - 1) (j - 1) h
  omega
