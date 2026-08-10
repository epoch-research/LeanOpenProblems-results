import FormalConjectures.Util.ProblemImports

open Nat Finset Real

def A271099 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

lemma cube_le_seven (u : ℕ) (h : u ^ 3 ≤ 420) : u ≤ 7 := by
  by_contra! h_gt
  have : u ≥ 8 := h_gt
  have : u ^ 3 ≥ 512 := by
    calc u ^ 3 ≥ 8 ^ 3 := Nat.pow_le_pow_left this 3
         _ = 512 := by rfl
  omega

lemma cube_le_five_x (x : ℕ) (h : 2 * x ^ 3 ≤ 420) : x ≤ 5 := by
  by_contra! h_gt
  have : x ≥ 6 := h_gt
  have : 2 * x ^ 3 ≥ 432 := by
    calc 2 * x ^ 3 ≥ 2 * 6 ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left this 3)
         _ = 432 := by rfl
  omega

lemma cube_le_five_z (z : ℕ) (h : 3 * z ^ 3 ≤ 420) : z ≤ 5 := by
  by_contra! h_gt
  have : z ≥ 6 := h_gt
  have : 3 * z ^ 3 ≥ 648 := by
    calc 3 * z ^ 3 ≥ 3 * 6 ^ 3 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left this 3)
         _ = 648 := by rfl
  omega

lemma sum_range_zero {M : Type _} [AddCommMonoid M] (n m : ℕ) (f : ℕ → M) (h : ∀ x < m, f (n + x) = 0) :
    ∑ x ∈ Finset.range (n + m), f x = ∑ x ∈ Finset.range n, f x := by
  rw [Finset.sum_range_add]
  have h_zero : ∑ x ∈ Finset.range m, f (n + x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_range] at hx
    exact h x hx
  rw [h_zero, add_zero]

lemma u_term_zero (u : ℕ) (hu : u ≥ 8) (v x y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : u ^ 3 ≤ 420 := by omega
    have : u ≤ 7 := cube_le_seven u this
    omega
  · rfl

lemma v_term_zero (v : ℕ) (hv : v ≥ 8) (u x y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : v ^ 3 ≤ 420 := by omega
    have : v ≤ 7 := cube_le_seven v this
    omega
  · rfl

lemma x_term_zero (x : ℕ) (hx : x ≥ 6) (u v y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : 2 * x ^ 3 ≤ 420 := by omega
    have : x ≤ 5 := cube_le_five_x x this
    omega
  · rfl

lemma y_term_zero (y : ℕ) (hy : y ≥ 6) (u v x z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : 2 * y ^ 3 ≤ 420 := by omega
    have : y ≤ 5 := cube_le_five_x y this
    omega
  · rfl

lemma z_term_zero (z : ℕ) (hz : z ≥ 6) (u v x y : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : 3 * z ^ 3 ≤ 420 := by omega
    have : z ≤ 5 := cube_le_five_z z this
    omega
  · rfl

lemma z_sum_reduce (u v x y : ℕ) :
    ∑ z ∈ Finset.range 421, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) =
    ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) := by
  refine sum_range_zero 6 415 _ ?_
  intro z _
  exact z_term_zero (6 + z) (by omega) u v x y

lemma y_sum_reduce (u v x : ℕ) :
    ∑ y ∈ Finset.range 421, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) =
    ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) := by
  refine sum_range_zero 6 415 _ ?_
  intro y _
  have h_zero : ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ (6 + y) ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * (6 + y) ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro z _
    exact y_term_zero (6 + y) (by omega) u v x z
  exact h_zero

lemma x_sum_reduce (u v : ℕ) :
    ∑ x ∈ Finset.range 421, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) =
    ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) := by
  refine sum_range_zero 6 415 _ ?_
  intro x _
  have h_zero : ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ (6 + x) ≤ y ∧ u ^ 3 + v ^ 3 + 2 * (6 + x) ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y _
    refine Finset.sum_eq_zero ?_
    intro z _
    exact x_term_zero (6 + x) (by omega) u v y z
  exact h_zero

lemma v_sum_reduce (u : ℕ) :
    ∑ v ∈ Finset.range 421, ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) =
    ∑ v ∈ Finset.range 8, ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) := by
  refine sum_range_zero 8 413 _ ?_
  intro v _
  have h_zero : ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ (8 + v) ∧ x ≤ y ∧ u ^ 3 + (8 + v) ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _
    refine Finset.sum_eq_zero ?_
    intro y _
    refine Finset.sum_eq_zero ?_
    intro z _
    exact v_term_zero (8 + v) (by omega) u x y z
  exact h_zero

lemma u_sum_reduce :
    ∑ u ∈ Finset.range 421, ∑ v ∈ Finset.range 8, ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) =
    ∑ u ∈ Finset.range 8, ∑ v ∈ Finset.range 8, ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) := by
  refine sum_range_zero 8 413 _ ?_
  intro u _
  have h_zero : ∑ v ∈ Finset.range 8, ∑ x ∈ Finset.range 6, ∑ y ∈ Finset.range 6, ∑ z ∈ Finset.range 6, (if (8 + u) ≤ v ∧ x ≤ y ∧ (8 + u) ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 420 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    refine Finset.sum_eq_zero ?_
    intro x _
    refine Finset.sum_eq_zero ?_
    intro y _
    refine Finset.sum_eq_zero ?_
    intro z _
    exact u_term_zero (8 + u) (by omega) v x y z
  exact h_zero

lemma A271099_420_eq_one : A271099 420 = 1 := by
  unfold A271099
  dsimp only
  have h_420_add : 420 + 1 = 421 := by rfl
  rw [h_420_add]
  simp_rw [z_sum_reduce]
  simp_rw [y_sum_reduce]
  simp_rw [x_sum_reduce]
  simp_rw [v_sum_reduce]
  simp_rw [u_sum_reduce]
  decide
