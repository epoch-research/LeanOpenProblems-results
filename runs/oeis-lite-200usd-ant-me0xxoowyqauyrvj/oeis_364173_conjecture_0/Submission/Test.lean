import FormalConjectures.Util.ProblemImports
open scoped BigOperators
def Wp (p x : ℕ) : ℕ := ∏ j ∈ (Finset.Ico 1 (x+1)).filter (fun j => ¬ p ∣ j), j

example (p M : ℕ) (hp : 0 < p) : (M * p).factorial = p ^ M * M.factorial * Wp p (M * p) := by
  have hfact : ∏ j ∈ Finset.Ico 1 (M*p+1), j = (M*p).factorial := Finset.prod_Ico_id_eq_factorial (M*p)
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 (M*p+1)) (fun j => ¬ p ∣ j) (fun j => j)
  have hdiv : ∏ j ∈ (Finset.Ico 1 (M*p+1)).filter (fun j => ¬ ¬ p ∣ j), j = p ^ M * M.factorial := by
    have : (Finset.Ico 1 (M*p+1)).filter (fun j => ¬ ¬ p ∣ j)
        = (Finset.Ico 1 (M+1)).image (fun i => p * i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, not_not]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, hpj⟩
        obtain ⟨i, rfl⟩ := hpj
        have hi0 : 0 < i := by rcases Nat.eq_zero_or_pos i with h | h; · simp [h] at hj1; · exact h
        have hiM : i ≤ M := by
          by_contra hc
          push_neg at hc
          have : p * (M+1) ≤ p * i := Nat.mul_le_mul_left p hc
          nlinarith [this, hj2]
        exact ⟨i, ⟨hi0, by omega⟩, by ring⟩
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, Dvd.intro i rfl⟩
        · nlinarith
        · have : p * i ≤ p * M := Nat.mul_le_mul_left p (by omega)
          nlinarith
    rw [this, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_Ico_id_eq_factorial]
    congr 1
    simp [Nat.card_Ico]
  rw [← hfact, ← hsplit, hdiv]
  unfold Wp
  ring
