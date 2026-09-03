import FormalConjecturesUtil

/-! Translation properties of equal sums of two cubes.
These lemmas do not settle the positive-density conjecture. -/

namespace Erdos1206

private lemma cube_pair_sum_le_of_translation
    {a b c d t : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 < t)
    (h₀ : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3)
    (h₁ : (a + t) ^ 3 + (b + t) ^ 3 = (c + t) ^ 3 + (d + t) ^ 3) :
    a + b ≤ c + d := by
  have h₂ : a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 + t * (a + b - c - d) = 0 := by
    have hx : (3 * t) *
        (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 + t * (a + b - c - d)) = 0 := by
      linear_combination h₁ - h₀
    exact (mul_eq_zero.mp hx).resolve_left (by positivity)
  have hf : (a + b - c - d) *
      (3 * t * (a + b) + (a + b - c - d) * (a + b + 2 * (c + d)) + 6 * c * d) = 0 := by
    linear_combination 3 * (a + b) * h₂ - 2 * h₀
  by_contra! hgt
  have hδ : 0 < a + b - c - d := by linarith
  have hs : 0 < a + b := by linarith
  have hfpos : 0 < 3 * t * (a + b) +
      (a + b - c - d) * (a + b + 2 * (c + d)) + 6 * c * d := by positivity
  exact (ne_of_gt (mul_pos hδ hfpos)) hf

/-- An equality of two nonnegative cube sums cannot survive a positive common
translation unless the original unordered pairs were equal. -/
lemma cube_pair_eq_of_common_translation
    {a b c d t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 < t)
    (h₀ : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3)
    (h₁ : (a + t) ^ 3 + (b + t) ^ 3 = (c + t) ^ 3 + (d + t) ^ 3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hs : a + b = c + d := le_antisymm
    (cube_pair_sum_le_of_translation ha hb hc hd ht h₀ h₁)
    (cube_pair_sum_le_of_translation hc hd ha hb ht h₀.symm h₁.symm)
  have h₂ : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
    have hx : (3 * t) * (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) = 0 := by
      linear_combination h₁ - h₀ - 3 * t ^ 2 * hs
    have hz := (mul_eq_zero.mp hx).resolve_left (by positivity)
    linarith
  have hp : (a - c) * (a - d) = 0 := by
    nlinarith [sq_nonneg (a + b - c - d)]
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl ⟨sub_eq_zero.mp h, by linarith⟩
  · exact Or.inr ⟨sub_eq_zero.mp h, by linarith⟩

lemma nat_cube_pair_eq_of_common_translation
    {a b c d t : ℕ} (ht : 0 < t)
    (h₀ : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3)
    (h₁ : (a + t) ^ 3 + (b + t) ^ 3 = (c + t) ^ 3 + (d + t) ^ 3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h := cube_pair_eq_of_common_translation
    (a := (a : ℝ)) (b := (b : ℝ)) (c := (c : ℝ)) (d := (d : ℝ)) (t := (t : ℝ))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast ht) (by exact_mod_cast h₀) (by exact_mod_cast h₁)
  exact_mod_cast h

/-- A nontrivial fixed four-point pattern has at most one nonnegative
translate that gives an equality of two cube sums. -/
lemma cube_collision_translation_unique
    {a b c d u v : ℕ}
    (hproper : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))
    (hu : (a + u) ^ 3 + (b + u) ^ 3 = (c + u) ^ 3 + (d + u) ^ 3)
    (hv : (a + v) ^ 3 + (b + v) ^ 3 = (c + v) ^ 3 + (d + v) ^ 3) :
    u = v := by
  have hle (u v : ℕ)
      (hu : (a + u) ^ 3 + (b + u) ^ 3 = (c + u) ^ 3 + (d + u) ^ 3)
      (hv : (a + v) ^ 3 + (b + v) ^ 3 = (c + v) ^ 3 + (d + v) ^ 3) : v ≤ u := by
    by_contra! h
    have ht : 0 < v - u := Nat.sub_pos_of_lt h
    have hs : u + (v - u) = v := Nat.add_sub_of_le h.le
    have hh : ((a + u) + (v - u)) ^ 3 + ((b + u) + (v - u)) ^ 3 =
        ((c + u) + (v - u)) ^ 3 + ((d + u) + (v - u)) ^ 3 := by
      simpa only [Nat.add_assoc, hs] using hv
    have he := nat_cube_pair_eq_of_common_translation ht hu hh
    apply hproper
    simpa only [Nat.add_right_cancel_iff] using he
  exact Nat.le_antisymm (hle v u hv hu) (hle u v hu hv)

end Erdos1206
