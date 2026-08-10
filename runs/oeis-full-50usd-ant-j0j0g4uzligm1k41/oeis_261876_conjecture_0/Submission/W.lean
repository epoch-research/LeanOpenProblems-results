import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators
set_option maxHeartbeats 1000000

-- copy of a from Spec
def a (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := IsSquare k
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if h_z : z > 0 then
      let k := x^2 + y^2 + z^2
      if h_le : k ≤ n then
        let r := n - k
        if is_square r then
          let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
          if is_square condition_expr then 1 else 0
        else 0
      else 0
    else 0

def ind (n x y z : ℕ) : ℕ :=
  if (0 < z ∧ x^2+y^2+z^2 ≤ n ∧ IsSquare (n - (x^2+y^2+z^2)) ∧
      IsSquare ((5*x^2+7*y^2+9*z^2)*y*z)) then 1 else 0

lemma a_eq (n : ℕ) : a n = ∑ x ∈ range (n+1), ∑ y ∈ range (n+1), ∑ z ∈ range (n+1), ind n x y z := by
  unfold a ind
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_)))
  simp only
  by_cases h0 : 0 < z
  · by_cases h1 : x^2+y^2+z^2 ≤ n
    · by_cases h2 : IsSquare (n - (x^2+y^2+z^2))
      · by_cases h3 : IsSquare ((5*x^2+7*y^2+9*z^2)*y*z)
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]
      · simp [h0, h1, h2]
    · simp [h0, h1]
  · simp [h0]

-- ind is 0 if any coordinate ≥ 264 (since 264² > 69383)
lemma ind_zero (x y z : ℕ) (h : 264 ≤ x ∨ 264 ≤ y ∨ 264 ≤ z) : ind 69383 x y z = 0 := by
  unfold ind
  rw [if_neg]
  rintro ⟨hz, hle, _, _⟩
  have : (264:ℕ)^2 ≤ x^2 + y^2 + z^2 := by
    rcases h with h | h | h
    · calc (264:ℕ)^2 ≤ x^2 := Nat.pow_le_pow_left h 2
        _ ≤ x^2+y^2+z^2 := by omega
    · calc (264:ℕ)^2 ≤ y^2 := Nat.pow_le_pow_left h 2
        _ ≤ x^2+y^2+z^2 := by omega
    · calc (264:ℕ)^2 ≤ z^2 := Nat.pow_le_pow_left h 2
        _ ≤ x^2+y^2+z^2 := by omega
  simp only [show (264:ℕ)^2 = 69696 by norm_num] at this
  omega

-- generic range restriction helper
lemma restrict (F : ℕ → ℕ) (hF : ∀ t, 264 ≤ t → F t = 0) :
    ∑ t ∈ range 69384, F t = ∑ t ∈ range 264, F t := by
  refine (Finset.sum_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) ?_).symm
  intro t _ ht2
  rw [mem_range, not_lt] at ht2
  exact hF t ht2

lemma a_restrict : a 69383 = ∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ range 264, ind 69383 x y z := by
  rw [a_eq]
  have inner : ∀ x, (∑ y ∈ range 69384, ∑ z ∈ range 69384, ind 69383 x y z)
      = ∑ y ∈ range 264, ∑ z ∈ range 264, ind 69383 x y z := by
    intro x
    rw [restrict (fun y => ∑ z ∈ range 69384, ind 69383 x y z)
        (fun y hy => Finset.sum_eq_zero (fun z _ => ind_zero x y z (Or.inr (Or.inl hy))))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact restrict (fun z => ind 69383 x y z) (fun z hz => ind_zero x y z (Or.inr (Or.inr hz)))
  rw [show (69383 + 1) = 69384 from rfl]
  rw [restrict (fun x => ∑ y ∈ range 69384, ∑ z ∈ range 69384, ind 69383 x y z)
      (fun x hx => Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun z _ => ind_zero x y z (Or.inl hx))))]
  exact Finset.sum_congr rfl (fun x _ => inner x)

-- witness value
lemma witness_ind : ind 69383 187 147 6 = 1 := by
  unfold ind
  rw [if_pos]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact ⟨113, by norm_num⟩
  · exact ⟨16968, by norm_num⟩
