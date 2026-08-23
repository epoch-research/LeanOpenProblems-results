import FormalConjectures.Util.ProblemImports

open Nat Function

/-!
Development file for A223086 conjecture.
-/

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else
    (3 * k - 1) / 4

def A006368_inv (m : ℕ) : ℕ :=
  if m % 3 = 0 then
    (2 * m) / 3
  else if m % 3 = 1 then
    (4 * m - 1) / 3
  else
    (4 * m + 1) / 3

lemma map_even (k : ℕ) : A006368_map (2 * k) = 3 * k := by
  simp [A006368_map]
  convert Nat.mul_div_cancel_left (3 * k) (by decide : 0 < 2) using 2
  ring

lemma map_mod4_one (k : ℕ) : A006368_map (4 * k + 1) = 3 * k + 1 := by
  have h2 : (4 * k + 1) % 2 = 1 := by omega
  have h4 : (4 * k + 1) % 4 = 1 := by omega
  simp [A006368_map, h2, h4]
  convert Nat.mul_div_cancel_left (3 * k + 1) (by decide : 0 < 4) using 2
  ring

lemma map_mod4_three (k : ℕ) : A006368_map (4 * k + 3) = 3 * k + 2 := by
  have h2 : (4 * k + 3) % 2 = 1 := by omega
  have h4 : ¬ (4 * k + 3) % 4 = 1 := by omega
  simp [A006368_map, h2, h4]
  convert Nat.mul_div_cancel_left (3 * k + 2) (by decide : 0 < 4) using 2
  have : 3 * (4 * k + 3) = 12 * k + 9 := by ring
  rw [this]
  have : 1 ≤ 12 * k + 9 := by omega
  rw [Nat.sub_eq_of_eq_add]
  ring

lemma inv_mod3_zero (t : ℕ) : A006368_inv (3 * t) = 2 * t := by
  simp [A006368_inv]
  convert Nat.mul_div_cancel_left (2 * t) (by decide : 0 < 3) using 2
  ring

lemma inv_mod3_one (t : ℕ) : A006368_inv (3 * t + 1) = 4 * t + 1 := by
  have h : (3 * t + 1) % 3 = 1 := by omega
  simp [A006368_inv, h]
  convert Nat.mul_div_cancel_left (4 * t + 1) (by decide : 0 < 3) using 2
  have : 4 * (3 * t + 1) = 12 * t + 4 := by ring
  rw [this]
  have : 1 ≤ 12 * t + 4 := by omega
  rw [Nat.sub_eq_of_eq_add]
  ring

lemma inv_mod3_two (t : ℕ) : A006368_inv (3 * t + 2) = 4 * t + 3 := by
  have h0 : ¬ (3 * t + 2) % 3 = 0 := by omega
  have h1 : ¬ (3 * t + 2) % 3 = 1 := by omega
  simp [A006368_inv, h0, h1]
  convert Nat.mul_div_cancel_left (4 * t + 3) (by decide : 0 < 3) using 2
  ring

lemma exists_form_even {n : ℕ} (h : n % 2 = 0) : ∃ k, n = 2 * k :=
  ⟨n / 2, (Nat.div_add_mod n 2).symm.trans (by rw [h]; ring)⟩

lemma exists_form_mod4_one {n : ℕ} (h : n % 4 = 1) : ∃ k, n = 4 * k + 1 :=
  ⟨n / 4, (Nat.div_add_mod n 4).symm.trans (by rw [h])⟩

lemma exists_form_mod4_three {n : ℕ} (h : n % 4 = 3) : ∃ k, n = 4 * k + 3 :=
  ⟨n / 4, (Nat.div_add_mod n 4).symm.trans (by rw [h])⟩

lemma exists_form_mod3_zero {n : ℕ} (h : n % 3 = 0) : ∃ t, n = 3 * t :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h]; ring)⟩

lemma exists_form_mod3_one {n : ℕ} (h : n % 3 = 1) : ∃ t, n = 3 * t + 1 :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h])⟩

lemma exists_form_mod3_two {n : ℕ} (h : n % 3 = 2) : ∃ t, n = 3 * t + 2 :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h])⟩

lemma even_or_mod4 (n : ℕ) : n % 2 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by
  omega

lemma mod3_cases (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  omega

lemma leftInverse_inv_map : LeftInverse A006368_inv A006368_map := by
  intro n
  rcases even_or_mod4 n with h | h | h
  · obtain ⟨k, rfl⟩ := exists_form_even h
    rw [map_even, inv_mod3_zero]
  · obtain ⟨k, rfl⟩ := exists_form_mod4_one h
    rw [map_mod4_one, inv_mod3_one]
  · obtain ⟨k, rfl⟩ := exists_form_mod4_three h
    rw [map_mod4_three, inv_mod3_two]

lemma rightInverse_inv_map : RightInverse A006368_inv A006368_map := by
  intro m
  rcases mod3_cases m with h | h | h
  · obtain ⟨t, rfl⟩ := exists_form_mod3_zero h
    rw [inv_mod3_zero, map_even]
  · obtain ⟨t, rfl⟩ := exists_form_mod3_one h
    rw [inv_mod3_one, map_mod4_one]
  · obtain ⟨t, rfl⟩ := exists_form_mod3_two h
    rw [inv_mod3_two, map_mod4_three]

lemma map_bijective : Bijective A006368_map :=
  ⟨LeftInverse.injective leftInverse_inv_map,
   RightInverse.surjective rightInverse_inv_map⟩

lemma map_injective : Injective A006368_map := map_bijective.1

lemma map_surjective : Surjective A006368_map := map_bijective.2

/-- If two iterates of 64 agree, then 64 is periodic (or the indices match). -/
lemma iterate_eq_of_periodic {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (heq : A006368_map^[i - 1] 64 = A006368_map^[j - 1] 64) :
    i = j ∨ ∃ k > 0, A006368_map^[k] 64 = 64 := by
  wlog hle : i ≤ j generalizing i j
  · rcases this hj hi heq.symm (le_of_not_ge hle) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hidx : i + d - 1 = d + (i - 1) := by omega
  rw [hidx, iterate_add_apply] at heq
  by_cases hd : d = 0
  · exact Or.inl (by omega)
  · have hinj : Injective (A006368_map^[i - 1]) := Injective.iterate map_injective (i - 1)
    have : A006368_map^[i - 1] (A006368_map^[d] 64) = A006368_map^[i - 1] 64 := by
      rw [← iterate_add_apply, Nat.add_comm, iterate_add_apply, ← heq]
    exact Or.inr ⟨d, Nat.pos_of_ne_zero hd, hinj this⟩

-- Concrete values
lemma map_64 : A006368_map 64 = 96 := by unfold A006368_map; norm_num
lemma map_96 : A006368_map 96 = 144 := by unfold A006368_map; norm_num
lemma map_iterate_6 : A006368_map^[6] 64 = 729 := by
  simp [Function.iterate_succ_apply', Function.iterate_zero_apply]
  unfold A006368_map
  norm_num

lemma map_iterate_20 : A006368_map^[20] 64 = 555 := by
  simp [Function.iterate_succ_apply']
  unfold A006368_map
  norm_num
#print axioms map_iterate_20
