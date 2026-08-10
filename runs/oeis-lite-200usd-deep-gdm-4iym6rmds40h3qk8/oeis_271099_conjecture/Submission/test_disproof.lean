import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)

  -- Sum over all 5-tuples of natural numbers. We use a loose upper bound R for simplicity.
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

open Real

/-- Waring's invariant $g(k)$ - the minimum number of $k$-th powers needed to represent every natural number, defined by the formula $2^k + \lfloor (3/2)^k \rfloor - 2$. -/
noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (floor three_half_pow_k_real)
    -- Safe for k >= 2: $2^k + \lfloor(3/2)^k\rfloor$ is at least $4 + 2 - 2 = 4$ for k=2, so pred.pred is safe.
    (2 ^ k + floor_val).pred.pred

namespace A271099

/-- Statement of the original conjecture for reference in type negation -/
def original_conjecture_statement : Prop :=
  -- Part (i)
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧

  -- Part (ii.k=4)
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧

  -- Part (ii.k=5)
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧

  -- Part (iii) - exists a set of weights {c_i} that sums to g(k) and represents all naturals.
  (∀ k : ℕ, k > 2 →
    -- The index type for 2k-1 variables
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      -- The set of sums of powers with these coefficients covers all natural numbers (Set.univ is Set ℕ)
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      -- The sum of the coefficients is g(k)
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )

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

lemma A271099_125_eq_one : A271099 125 = 1 := by
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

theorem oeis_271099_conjecture.disproof : ¬ original_conjecture_statement := by
  intro h
  have h_part1_2 := h.1.1.2
  have h_125 := h_part1_2 125
  have h_eq : A271099 125 = 1 := A271099_125_eq_one
  rw [h_eq] at h_125
  have h_in : 125 ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ) := h_125.mp rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_in
  rcases h_in with h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

end A271099
