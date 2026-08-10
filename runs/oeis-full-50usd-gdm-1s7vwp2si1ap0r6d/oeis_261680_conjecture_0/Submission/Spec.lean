import FormalConjectures.Util.ProblemImports

open Nat List Finset

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun u =>
    Finset.sum (Finset.range (n - u + 1)) fun v =>
      Finset.sum (Finset.range (n - (u + v) + 1)) fun w =>
        let x := n - (u + v + w)
        if is_binary_palindrome u ∧
           is_binary_palindrome v ∧
           is_binary_palindrome w ∧
           is_binary_palindrome x
        then 1 else 0

lemma digits_two_pow_sub_one (k : ℕ) : Nat.digits 2 (2^k - 1) = List.replicate k 1 := by
  induction k with
  | zero =>
    simp
  | succ m ih =>
    have h_pow_pos : 2^m ≥ 1 := Nat.one_le_pow m 2 (by decide)
    have h_pow_ge : 2^(m + 1) ≥ 2 := by
      rw [pow_succ]
      omega
    have h_pos : 0 < 2^(m + 1) - 1 := by omega
    rw [digits_of_two_le_of_pos (by decide) h_pos]
    have h_eq : 2^(m+1) - 1 = 2 * (2^m - 1) + 1 := by
      rw [pow_succ]
      omega
    rw [h_eq]
    have h1 : (2 * (2^m - 1) + 1) % 2 = 1 := by
      simp
    have h2 : (2 * (2^m - 1) + 1) / 2 = 2^m - 1 := by
      omega
    rw [h1, h2, ih]
    rfl

lemma digits_two_pow (m : ℕ) : Nat.digits 2 (2^m) = List.replicate m 0 ++ [1] := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h_pow_pos : 2^m ≥ 1 := Nat.one_le_pow m 2 (by decide)
    have h_pos : 0 < 2^(m + 1) := by
      apply Nat.pow_pos (by decide)
    rw [digits_of_two_le_of_pos (by decide) h_pos]
    have h_pow : 2^(m+1) = 2^m * 2 := by rw [pow_succ]
    have h1 : 2^(m+1) % 2 = 0 := by
      rw [h_pow]
      simp
    have h2 : 2^(m+1) / 2 = 2^m := by
      rw [h_pow]
      omega
    rw [h1, h2, ih]
    rfl

lemma digits_two_pow_add_one (m : ℕ) : Nat.digits 2 (2^(m+1) + 1) = 1 :: List.replicate m 0 ++ [1] := by
  have h_pow_pos : 2^m ≥ 1 := Nat.one_le_pow m 2 (by decide)
  have h_pos : 0 < 2^(m + 1) + 1 := by omega
  rw [digits_of_two_le_of_pos (by decide) h_pos]
  have h_pow : 2^(m+1) + 1 = 2 * 2^m + 1 := by
    rw [pow_succ]
    omega
  have h1 : (2^(m+1) + 1) % 2 = 1 := by
    rw [h_pow]
    simp
  have h2 : (2^(m+1) + 1) / 2 = 2^m := by
    rw [h_pow]
    omega
  rw [h1, h2, digits_two_pow]
  rfl

lemma is_binary_palindrome_two_pow_sub_one (k : ℕ) : is_binary_palindrome (2^k - 1) = true := by
  unfold is_binary_palindrome
  rw [digits_two_pow_sub_one]
  simp

lemma is_binary_palindrome_two_pow_add_one (m : ℕ) : is_binary_palindrome (2^(m+1) + 1) = true := by
  unfold is_binary_palindrome
  rw [digits_two_pow_add_one]
  simp

lemma a_pos_of_exists (n : ℕ) (u v w : ℕ)
    (hu : u ≤ n)
    (hv : v ≤ n - u)
    (hw : w ≤ n - (u + v))
    (hpal_u : is_binary_palindrome u = true)
    (hpal_v : is_binary_palindrome v = true)
    (hpal_w : is_binary_palindrome w = true)
    (hpal_x : is_binary_palindrome (n - (u + v + w)) = true) :
    a n > 0 := by
  have hu_in : u ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega
  have h1 : (∑ v ∈ Finset.range (n - u + 1), ∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) ≤
      (∑ u ∈ Finset.range (n + 1), ∑ v ∈ Finset.range (n - u + 1), ∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) := by
    apply Finset.single_le_sum (f := fun u => ∑ v ∈ Finset.range (n - u + 1), ∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0)
    · intro i _
      exact Nat.zero_le _
    · exact hu_in
  have hv_in : v ∈ Finset.range (n - u + 1) := by
    rw [Finset.mem_range]
    omega
  have h2 : (∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) ≤
      (∑ v ∈ Finset.range (n - u + 1), ∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) := by
    apply Finset.single_le_sum (f := fun v => ∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0)
    · intro i _
      exact Nat.zero_le _
    · exact hv_in
  have hw_in : w ∈ Finset.range (n - (u + v) + 1) := by
    rw [Finset.mem_range]
    omega
  have h3 : (let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) ≤
      (∑ w ∈ Finset.range (n - (u + v) + 1),
      let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) := by
    apply Finset.single_le_sum (f := fun w => let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0)
    · intro i _
      exact Nat.zero_le _
    · exact hw_in
  have h_cond : is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome (n - (u + v + w)) := by
    refine ⟨hpal_u, hpal_v, hpal_w, hpal_x⟩
  have h4 : (let x := n - (u + v + w); if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x then 1 else 0) = 1 := by
    dsimp only
    rw [if_pos h_cond]
  unfold a
  omega

theorem oeis_261680_conjecture_0 (n : ℕ) : a n > 0 := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · -- n = 0
    apply a_pos_of_exists 0 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 1
    apply a_pos_of_exists 1 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 2
    apply a_pos_of_exists 2 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 3
    apply a_pos_of_exists 3 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 4
    apply a_pos_of_exists 4 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 5
    apply a_pos_of_exists 5 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 6
    apply a_pos_of_exists 6 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 7
    apply a_pos_of_exists 7 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 8
    apply a_pos_of_exists 8 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 9
    apply a_pos_of_exists 9 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 10
    apply a_pos_of_exists 10 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 11
    apply a_pos_of_exists 11 0 1 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 12
    apply a_pos_of_exists 12 0 0 3
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 13
    apply a_pos_of_exists 13 0 1 3
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 14
    apply a_pos_of_exists 14 0 0 5
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 15
    apply a_pos_of_exists 15 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 16
    apply a_pos_of_exists 16 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 17
    apply a_pos_of_exists 17 0 0 0
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 18
    apply a_pos_of_exists 18 0 0 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 19
    apply a_pos_of_exists 19 0 1 1
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · -- n = 20
    apply a_pos_of_exists 20 0 0 3
    · omega
    · omega
    · omega
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
    · simp [is_binary_palindrome]
  · sorry
