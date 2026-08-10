import FormalConjectures.Util.ProblemImports
open Finset

-- Let's put some of the needed lemmas here from Spec.lean to test
lemma sum_split_half (H : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (2 * H), f k = ∑ k ∈ range H, f k + ∑ k ∈ range H, f (2 * H - 1 - k) := sorry

lemma div_sq_sub_self (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) : (n - k) ^ 2 / n = n - 2 * k + k ^ 2 / n := sorry

lemma sum_div_mod_two_split (H : ℕ) :
    ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 = ∑ k ∈ range H, (k ^ 2 / (2 * H)) % 2 + ∑ k ∈ range H, ((k + 1) ^ 2 / (2 * H)) % 2 := by
  by_cases hH : H = 0
  · subst hH; simp
  have h_split := sum_split_half H (fun k => (k ^ 2 / (2 * H)) % 2)
  rw [h_split]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk_lt : k < H := mem_range.mp hk
  have h_eq : 2 * H - 1 - k = 2 * H - (k + 1) := by omega
  rw [h_eq]
  have hj_le : 2 * (k + 1) ≤ 2 * H := by omega
  have h_sub := div_sq_sub_self (2 * H) (k + 1) (by omega) hj_le
  rw [h_sub]
  omega
