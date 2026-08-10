import Mathlib

/-- The A006368 map. -/
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then (3 * k) / 2
  else if k % 4 = 1 then (3 * k + 1) / 4
  else (3 * k - 1) / 4

/-- Candidate left inverse (this is A006369). -/
def ginv (y : ℕ) : ℕ :=
  if y % 3 = 0 then 2 * (y / 3)
  else if y % 3 = 1 then 4 * (y / 3) + 1
  else 4 * (y / 3) + 3

lemma ginv_A006368 (k : ℕ) : ginv (A006368_map k) = k := by
  unfold A006368_map ginv
  split_ifs <;> omega

lemma A006368_injective : Function.Injective A006368_map :=
  Function.LeftInverse.injective ginv_A006368

def a (n : ℕ) : ℕ := A006368_map^[n - 1] 64

/-- The genuinely OPEN core: the orbit of 64 never returns to 64.
This is the Collatz original-permutation conjecture (OEIS A223086). -/
lemma not_periodic : ∀ d, 0 < d → A006368_map^[d] 64 ≠ 64 := by
  sorry

theorem oeis_223086_conjecture_0 :
    ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj hij
  simp only [a] at hij
  rcases le_total i j with h | h
  · have key : A006368_map^[i - 1] 64
        = A006368_map^[i - 1] (A006368_map^[j - i] 64) := by
      conv_lhs => rw [hij]
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have h64 : (64 : ℕ) = A006368_map^[j - i] 64 :=
      (A006368_injective.iterate (i - 1)) key
    by_contra hne
    exact not_periodic (j - i) (by omega) h64.symm
  · have key : A006368_map^[j - 1] 64
        = A006368_map^[j - 1] (A006368_map^[i - j] 64) := by
      conv_lhs => rw [← hij]
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have h64 : (64 : ℕ) = A006368_map^[i - j] 64 :=
      (A006368_injective.iterate (j - 1)) key
    by_contra hne
    exact not_periodic (i - j) (by omega) h64.symm
