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

def E_bool (x : ℕ) : Bool :=
  if x < 96 then true
  else match x with
  | 97 => true
  | 98 => true
  | 99 => true
  | 100 => true
  | 101 => true
  | 102 => true
  | 103 => true
  | 105 => true
  | 106 => true
  | 107 => true
  | 109 => true
  | 110 => true
  | 111 => true
  | 112 => true
  | 113 => true
  | 115 => true
  | 117 => true
  | 118 => true
  | 119 => true
  | 121 => true
  | 122 => true
  | 123 => true
  | 124 => true
  | 125 => true
  | 127 => true
  | 129 => true
  | 131 => true
  | 132 => true
  | 133 => true
  | 134 => true
  | 135 => true
  | 137 => true
  | 141 => true
  | 143 => true
  | 145 => true
  | 147 => true
  | 149 => true
  | 150 => true
  | 151 => true
  | 152 => true
  | 153 => true
  | 157 => true
  | 159 => true
  | 161 => true
  | 163 => true
  | 165 => true
  | 167 => true
  | 168 => true
  | 169 => true
  | 170 => true
  | 175 => true
  | 177 => true
  | 179 => true
  | 183 => true
  | 186 => true
  | 191 => true
  | 193 => true
  | 198 => true
  | 199 => true
  | 201 => true
  | 202 => true
  | 203 => true
  | 209 => true
  | 215 => true
  | 217 => true
  | 223 => true
  | 225 => true
  | 227 => true
  | 228 => true
  | 233 => true
  | 239 => true
  | 252 => true
  | 255 => true
  | 257 => true
  | 265 => true
  | 269 => true
  | 271 => true
  | 279 => true
  | 284 => true
  | 287 => true
  | 289 => true
  | 297 => true
  | 303 => true
  | 311 => true
  | 314 => true
  | 319 => true
  | 338 => true
  | 342 => true
  | 343 => true
  | 353 => true
  | 356 => true
  | 359 => true
  | 361 => true
  | 378 => true
  | 379 => true
  | 380 => true
  | 383 => true
  | 385 => true
  | 406 => true
  | 415 => true
  | 419 => true
  | 422 => true
  | 425 => true
  | 426 => true
  | 451 => true
  | 454 => true
  | 457 => true
  | 471 => true
  | 475 => true
  | 478 => true
  | 479 => true
  | 481 => true
  | 505 => true
  | 507 => true
  | 511 => true
  | 513 => true
  | 534 => true
  | 538 => true
  | 541 => true
  | 553 => true
  | 559 => true
  | 563 => true
  | 566 => true
  | 567 => true
  | 570 => true
  | 598 => true
  | 601 => true
  | 605 => true
  | 609 => true
  | 620 => true
  | 633 => true
  | 637 => true
  | 639 => true
  | 641 => true
  | 662 => true
  | 673 => true
  | 681 => true
  | 717 => true
  | 721 => true
  | 737 => true
  | 745 => true
  | 751 => true
  | 755 => true
  | 797 => true
  | 801 => true
  | 807 => true
  | 827 => true
  | 849 => true
  | 854 => true
  | 855 => true
  | 874 => true
  | 883 => true
  | 890 => true
  | 897 => true
  | 930 => true
  | 961 => true
  | 983 => true
  | 993 => true
  | 1001 => true
  | 1007 => true
  | 1046 => true
  | 1063 => true
  | 1103 => true
  | 1139 => true
  | 1165 => true
  | 1177 => true
  | 1187 => true
  | 1281 => true
  | 1311 => true
  | 1335 => true
  | 1343 => true
  | 1395 => true
  | 1417 => true
  | 1471 => true
  | 1519 => true
  | 1553 => true
  | 1569 => true
  | 1583 => true
  | 1791 => true
  | 1889 => true
  | 1961 => true
  | 2025 => true
  | 2071 => true
  | _ => false

def E (x : ℕ) : Prop :=
  x < 2072 ∧ E_bool x = true

instance (x : ℕ) : Decidable (E x) := by
  dsimp [E]
  infer_instance

-- Split E_preimage_all into ranges to avoid timeouts
theorem E_preimage_all_1 : ∀ x < 300, E (A006368_map x) → E x := by decide
theorem E_preimage_all_2 : ∀ x < 600, 300 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_3 : ∀ x < 900, 600 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_4 : ∀ x < 1200, 900 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_5 : ∀ x < 1500, 1200 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_6 : ∀ x < 1800, 1500 ≤ x → E (A006368_map x) → E x := by decide
theorem E_preimage_all_7 : ∀ x < 2093, 1800 ≤ x → E (A006368_map x) → E x := by decide

theorem E_preimage_all (x : ℕ) (h : x < 2093) (h_map : E (A006368_map x)) : E x := by
  rcases lt_or_ge x 300 with h1 | h1
  · exact E_preimage_all_1 x h1 h_map
  · rcases lt_or_ge x 600 with h2 | h2
    · exact E_preimage_all_2 x h2 h1 h_map
    · rcases lt_or_ge x 900 with h3 | h3
      · exact E_preimage_all_3 x h3 h2 h_map
      · rcases lt_or_ge x 1200 with h4 | h4
        · exact E_preimage_all_4 x h4 h3 h_map
        · rcases lt_or_ge x 1500 with h5 | h5
          · exact E_preimage_all_5 x h5 h4 h_map
          · rcases lt_or_ge x 1800 with h6 | h6
            · exact E_preimage_all_6 x h6 h5 h_map
            · exact E_preimage_all_7 x h h6 h_map

-- Split E_preimage_mid into ranges
