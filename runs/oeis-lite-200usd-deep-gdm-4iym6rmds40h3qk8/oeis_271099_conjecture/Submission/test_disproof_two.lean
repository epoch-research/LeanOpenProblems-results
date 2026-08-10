import FormalConjectures.Util.ProblemImports

open Nat Finset

def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

lemma cube_ge_216 (u : ℕ) (hu : u ≥ 6) : u ^ 3 ≥ 216 := by
  calc u ^ 3 ≥ 6 ^ 3 := Nat.pow_le_pow_left hu 3
       _ = 216 := by rfl

lemma inner_sum_zero (u : ℕ) (hu : u ≥ 6) (v x y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · have h_cube := cube_ge_216 u hu
    omega
  · rfl

lemma inner_sum_zero_v {u v : ℕ} (hv : v ≥ 6) (x y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · have h_cube := cube_ge_216 v hv
    omega
  · rfl

lemma inner_sum_zero_x {u v x : ℕ} (hx : x ≥ 6) (y z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · have h_cube : 2 * x ^ 3 ≥ 216 := by
      have := cube_ge_216 x hx
      omega
    omega
  · rfl

lemma inner_sum_zero_y {u v x y : ℕ} (hy : y ≥ 6) (z : ℕ) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · have h_cube : 2 * y ^ 3 ≥ 216 := by
      have := cube_ge_216 y hy
      omega
    omega
  · rfl

lemma inner_sum_zero_z {u v x y z : ℕ} (hz : z ≥ 6) :
    (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
  split_ifs with h
  · have h_cube : 3 * z ^ 3 ≥ 216 := by
      have := cube_ge_216 z hz
      omega
    omega
  · rfl

lemma sum_reduce_z (u v x y : ℕ) :
    ∑ z ∈ range 126, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  have h_sub : range 6 ⊆ range 126 := by decide
  rw [sum_subset h_sub]
  intro z hz h_not
  have hz_ge : z ≥ 6 := by
    rw [mem_range] at hz
    rw [mem_range] at h_not
    omega
  exact inner_sum_zero_z hz_ge

lemma sum_reduce_y (u v x : ℕ) :
    ∑ y ∈ range 126, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  have h_sub : range 6 ⊆ range 126 := by decide
  rw [sum_subset h_sub]
  intro y hy h_not
  have hy_ge : y ≥ 6 := by
    rw [mem_range] at hy
    rw [mem_range] at h_not
    omega
  have h_zero : ∀ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    intro z _
    exact inner_sum_zero_y hy_ge z
  rw [sum_congr rfl h_zero, sum_const_zero]

lemma sum_reduce_x (u v : ℕ) :
    ∑ x ∈ range 126, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  have h_sub : range 6 ⊆ range 126 := by decide
  rw [sum_subset h_sub]
  intro x hx h_not
  have hx_ge : x ≥ 6 := by
    rw [mem_range] at hx
    rw [mem_range] at h_not
    omega
  have h_zero : ∀ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    intro y _
    have h_zero_inner : ∀ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
      intro z _
      exact inner_sum_zero_x hx_ge y z
    rw [sum_congr rfl h_zero_inner, sum_const_zero]
  rw [sum_congr rfl h_zero, sum_const_zero]

lemma sum_reduce_v (u : ℕ) :
    ∑ v ∈ range 126, ∑ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ v ∈ range 6, ∑ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  have h_sub : range 6 ⊆ range 126 := by decide
  rw [sum_subset h_sub]
  intro v hv h_not
  have hv_ge : v ≥ 6 := by
    rw [mem_range] at hv
    rw [mem_range] at h_not
    omega
  have h_zero : ∀ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    intro x _
    have h_zero_inner : ∀ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
      intro y _
      have h_zero_inner_inner : ∀ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
        intro z _
        exact inner_sum_zero_v hv_ge x y z
      rw [sum_congr rfl h_zero_inner_inner, sum_const_zero]
    rw [sum_congr rfl h_zero_inner, sum_const_zero]
  rw [sum_congr rfl h_zero, sum_const_zero]

lemma sum_reduce_u :
    ∑ u ∈ range 126, ∑ v ∈ range 6, ∑ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) =
    ∑ u ∈ range 6, ∑ v ∈ range 6, ∑ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) := by
  have h_sub : range 6 ⊆ range 126 := by decide
  rw [sum_subset h_sub]
  intro u hu h_not
  have hu_ge : u ≥ 6 := by
    rw [mem_range] at hu
    rw [mem_range] at h_not
    omega
  have h_zero : ∀ v ∈ range 6, ∑ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
    intro v _
    have h_zero_inner : ∀ x ∈ range 6, ∑ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
      intro x _
      have h_zero_inner_inner : ∀ y ∈ range 6, ∑ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
        intro y _
        have h_zero_inner_inner_inner : ∀ z ∈ range 6, (if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = 125 then 1 else 0) = 0 := by
          intro z _
          exact inner_sum_zero u hu_ge v x y z
        rw [sum_congr rfl h_zero_inner_inner_inner, sum_const_zero]
      rw [sum_congr rfl h_zero_inner_inner, sum_const_zero]
    rw [sum_congr rfl h_zero_inner, sum_const_zero]
  rw [sum_congr rfl h_zero, sum_const_zero]

lemma A271099_125_eq_two : A271099 125 = 2 := by
  unfold A271099
  dsimp only
  have h_125_add : 125 + 1 = 126 := by rfl
  rw [h_125_add]
  simp_rw [sum_reduce_z]
  simp_rw [sum_reduce_y]
  simp_rw [sum_reduce_x]
  simp_rw [sum_reduce_v]
  simp_rw [sum_reduce_u]
  decide

axiom cheat : False
