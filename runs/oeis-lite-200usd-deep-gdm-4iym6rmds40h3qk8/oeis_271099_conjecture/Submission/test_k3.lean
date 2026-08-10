import FormalConjectures.Util.ProblemImports

lemma cube_le_five (u : ℕ) (h : u ^ 3 ≤ 125) : u ≤ 5 := by
  by_contra! h_gt
  have : u ≥ 6 := h_gt
  have : u ^ 3 ≥ 216 := by
    calc u ^ 3 ≥ 6 ^ 3 := Nat.pow_le_pow_left this 3
         _ = 216 := by rfl
  omega

lemma cube_le_three_x (x : ℕ) (h : 2 * x ^ 3 ≤ 125) : x ≤ 3 := by
  by_contra! h_gt
  have : x ≥ 4 := h_gt
  have : 2 * x ^ 3 ≥ 128 := by
    calc 2 * x ^ 3 ≥ 2 * 4 ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left this 3)
         _ = 128 := by rfl
  omega

lemma cube_le_three_z (z : ℕ) (h : 3 * z ^ 3 ≤ 125) : z ≤ 3 := by
  by_contra! h_gt
  have : z ≥ 4 := h_gt
  have : 3 * z ^ 3 ≥ 192 := by
    calc 3 * z ^ 3 ≥ 3 * 4 ^ 3 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left this 3)
         _ = 192 := by rfl
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


lemma u_term_zero (u : ℕ) (hu : u ≥ 6) (v x y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : u ^ 3 ≤ 125 := by omega
    have : u ≤ 5 := cube_le_five u this
    omega
  · rfl

lemma v_term_zero (v : ℕ) (hv : v ≥ 6) (u x y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : v ^ 3 ≤ 125 := by omega
    have : v ≤ 5 := cube_le_five v this
    omega
  · rfl

lemma x_term_zero (x : ℕ) (hx : x ≥ 4) (u v y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : 2 * x ^ 3 ≤ 125 := by omega
    have : x ≤ 3 := cube_le_three_x x this
    omega
  · rfl

lemma y_term_zero (y : ℕ) (hy : y ≥ 4) (u v x z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : 2 * y ^ 3 ≤ 125 := by omega
    have : y ≤ 3 := cube_le_three_x y this
    omega
  · rfl

lemma z_term_zero (z : ℕ) (hz : z ≥ 4) (u v x y : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · exfalso
    have : 3 * z ^ 3 ≤ 125 := by omega
    have : z ≤ 3 := cube_le_three_z z this
    omega
  · rfl


lemma z_sum_reduce (u v x y : ℕ) :
    ∑ z ∈ Finset.range 126, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  refine sum_range_zero 4 122 _ ?_
  intro z _
  exact z_term_zero (4 + z) (by omega) u v x y


lemma y_sum_reduce (u v x : ℕ) :
    ∑ y ∈ Finset.range 126, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  refine sum_range_zero 4 122 _ ?_
  intro y _
  have h_zero : ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ (4 + y) ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * (4 + y) ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro z _
    exact y_term_zero (4 + y) (by omega) u v x z
  exact h_zero

lemma x_sum_reduce (u v : ℕ) :
    ∑ x ∈ Finset.range 126, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  refine sum_range_zero 4 122 _ ?_
  intro x _
  have h_zero : ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ (4 + x) ≤ y ∧ u ^ 3 + v ^ 3 + 2 * (4 + x) ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y _
    refine Finset.sum_eq_zero ?_
    intro z _
    exact x_term_zero (4 + x) (by omega) u v y z
  exact h_zero

lemma v_sum_reduce (u : ℕ) :
    ∑ v ∈ Finset.range 126, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ v ∈ Finset.range 6, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  refine sum_range_zero 6 120 _ ?_
  intro v _
  have h_zero : ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ (6 + v) ∧ x ≤ y ∧ u ^ 3 + (6 + v) ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _
    refine Finset.sum_eq_zero ?_
    intro y _
    refine Finset.sum_eq_zero ?_
    intro z _
    exact v_term_zero (6 + v) (by omega) u x y z
  exact h_zero

lemma u_sum_reduce :
    ∑ u ∈ Finset.range 126, ∑ v ∈ Finset.range 6, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ u ∈ Finset.range 6, ∑ v ∈ Finset.range 6, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  refine sum_range_zero 6 120 _ ?_
  intro u _
  have h_zero : ∑ v ∈ Finset.range 6, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if (6 + u) ≤ v ∧ x ≤ y ∧ (6 + u) ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    refine Finset.sum_eq_zero ?_
    intro x _
    refine Finset.sum_eq_zero ?_
    intro y _
    refine Finset.sum_eq_zero ?_
    intro z _
    exact u_term_zero (6 + u) (by omega) v x y z
  exact h_zero



#eval ∑ u ∈ Finset.range 6, ∑ v ∈ Finset.range 6, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0)

lemma A271099_125_small : ∑ u ∈ Finset.range 6, ∑ v ∈ Finset.range 6, ∑ x ∈ Finset.range 4, ∑ y ∈ Finset.range 4, ∑ z ∈ Finset.range 4, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  decide




#check Finset.sum_range_add



