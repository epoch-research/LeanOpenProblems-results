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
  else if x < 359 then if x < 165 then if x < 124 then if x < 110 then if x < 102 then if x < 99 then if x < 98 then x == 97 else x == 98 else if x < 100 then x == 99 else if x < 101 then x == 100 else x == 101 else if x < 106 then if x < 103 then x == 102 else if x < 105 then x == 103 else x == 105 else if x < 107 then x == 106 else if x < 109 then x == 107 else x == 109 else if x < 117 then if x < 112 then if x < 111 then x == 110 else x == 111 else if x < 113 then x == 112 else if x < 115 then x == 113 else x == 115 else if x < 121 then if x < 118 then x == 117 else if x < 119 then x == 118 else x == 119 else if x < 122 then x == 121 else if x < 123 then x == 122 else x == 123 else if x < 143 then if x < 132 then if x < 127 then if x < 125 then x == 124 else x == 125 else if x < 129 then x == 127 else if x < 131 then x == 129 else x == 131 else if x < 135 then if x < 133 then x == 132 else if x < 134 then x == 133 else x == 134 else if x < 137 then x == 135 else if x < 141 then x == 137 else x == 141 else if x < 152 then if x < 149 then if x < 145 then x == 143 else if x < 147 then x == 145 else x == 147 else if x < 150 then x == 149 else if x < 151 then x == 150 else x == 151 else if x < 159 then if x < 153 then x == 152 else if x < 157 then x == 153 else x == 157 else if x < 161 then x == 159 else if x < 163 then x == 161 else x == 163 else if x < 228 then if x < 193 then if x < 175 then if x < 168 then if x < 167 then x == 165 else x == 167 else if x < 169 then x == 168 else if x < 170 then x == 169 else x == 170 else if x < 183 then if x < 177 then x == 175 else if x < 179 then x == 177 else x == 179 else if x < 186 then x == 183 else if x < 191 then x == 186 else x == 191 else if x < 209 then if x < 201 then if x < 198 then x == 193 else if x < 199 then x == 198 else x == 199 else if x < 202 then x == 201 else if x < 203 then x == 202 else x == 203 else if x < 223 then if x < 215 then x == 209 else if x < 217 then x == 215 else x == 217 else if x < 225 then x == 223 else if x < 227 then x == 225 else x == 227 else if x < 287 then if x < 257 then if x < 239 then if x < 233 then x == 228 else x == 233 else if x < 252 then x == 239 else if x < 255 then x == 252 else x == 255 else if x < 271 then if x < 265 then x == 257 else if x < 269 then x == 265 else x == 269 else if x < 279 then x == 271 else if x < 284 then x == 279 else x == 284 else if x < 319 then if x < 303 then if x < 289 then x == 287 else if x < 297 then x == 289 else x == 297 else if x < 311 then x == 303 else if x < 314 then x == 311 else x == 314 else if x < 343 then if x < 338 then x == 319 else if x < 342 then x == 338 else x == 342 else if x < 353 then x == 343 else if x < 356 then x == 353 else x == 356 else if x < 717 then if x < 511 then if x < 425 then if x < 383 then if x < 378 then if x < 361 then x == 359 else x == 361 else if x < 379 then x == 378 else if x < 380 then x == 379 else x == 380 else if x < 415 then if x < 385 then x == 383 else if x < 406 then x == 385 else x == 406 else if x < 419 then x == 415 else if x < 422 then x == 419 else x == 422 else if x < 475 then if x < 454 then if x < 426 then x == 425 else if x < 451 then x == 426 else x == 451 else if x < 457 then x == 454 else if x < 471 then x == 457 else x == 471 else if x < 481 then if x < 478 then x == 475 else if x < 479 then x == 478 else x == 479 else if x < 505 then x == 481 else if x < 507 then x == 505 else x == 507 else if x < 598 then if x < 553 then if x < 534 then if x < 513 then x == 511 else x == 513 else if x < 538 then x == 534 else if x < 541 then x == 538 else x == 541 else if x < 566 then if x < 559 then x == 553 else if x < 563 then x == 559 else x == 563 else if x < 567 then x == 566 else if x < 570 then x == 567 else x == 570 else if x < 637 then if x < 609 then if x < 601 then x == 598 else if x < 605 then x == 601 else x == 605 else if x < 620 then x == 609 else if x < 633 then x == 620 else x == 633 else if x < 662 then if x < 639 then x == 637 else if x < 641 then x == 639 else x == 641 else if x < 673 then x == 662 else if x < 681 then x == 673 else x == 681 else if x < 1046 then if x < 854 then if x < 755 then if x < 737 then if x < 721 then x == 717 else x == 721 else if x < 745 then x == 737 else if x < 751 then x == 745 else x == 751 else if x < 807 then if x < 797 then x == 755 else if x < 801 then x == 797 else x == 801 else if x < 827 then x == 807 else if x < 849 then x == 827 else x == 849 else if x < 930 then if x < 883 then if x < 855 then x == 854 else if x < 874 then x == 855 else x == 874 else if x < 890 then x == 883 else if x < 897 then x == 890 else x == 897 else if x < 993 then if x < 961 then x == 930 else if x < 983 then x == 961 else x == 983 else if x < 1001 then x == 993 else if x < 1007 then x == 1001 else x == 1007 else if x < 1395 then if x < 1177 then if x < 1103 then if x < 1063 then x == 1046 else x == 1063 else if x < 1139 then x == 1103 else if x < 1165 then x == 1139 else x == 1165 else if x < 1311 then if x < 1187 then x == 1177 else if x < 1281 then x == 1187 else x == 1281 else if x < 1335 then x == 1311 else if x < 1343 then x == 1335 else x == 1343 else if x < 1583 then if x < 1519 then if x < 1417 then x == 1395 else if x < 1471 then x == 1417 else x == 1471 else if x < 1553 then x == 1519 else if x < 1569 then x == 1553 else x == 1569 else if x < 1961 then if x < 1791 then x == 1583 else if x < 1889 then x == 1791 else x == 1889 else if x < 2025 then x == 1961 else if x < 2071 then x == 2025 else x == 2071

def E (x : ℕ) : Prop :=
  x < 2072 ∧ E_bool x = true

