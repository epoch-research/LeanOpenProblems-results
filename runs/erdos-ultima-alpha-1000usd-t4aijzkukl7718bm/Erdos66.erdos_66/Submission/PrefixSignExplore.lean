import Submission.SignEnergyExplore

/-! A single finite sign pattern with the energy estimate at every prefix.
This coherence is finite and does not give compatible integer-set prefixes. -/
namespace Erdos66PrefixSign
open Polynomial Erdos66SignEnergy
noncomputable section

def cutPoly (P : ℤ[X]) (h : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range h, monomial i (P.coeff i)

lemma coeff_cutPoly (P : ℤ[X]) (h i : ℕ) :
    (cutPoly P h).coeff i = if i < h then P.coeff i else 0 := by
  simp [cutPoly, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq']

lemma cutPoly_supported (P : ℤ[X]) (h : ℕ) : SupportedBelow (cutPoly P h) h := by
  intro i hi
  rw [coeff_cutPoly, if_neg (by omega)]

lemma cutPoly_eq_self {P : ℤ[X]} {h : ℕ} (hP : SupportedBelow P h) : cutPoly P h = P := by
  ext i
  rw [coeff_cutPoly]
  split_ifs with hi
  · rfl
  · exact (hP i (by omega)).symm

lemma cutPoly_append (P : ℤ[X]) (n h : ℕ) (s : ℤ) (hh : h ≤ n) :
    cutPoly (append P n s) h = cutPoly P h := by
  ext i
  rw [coeff_cutPoly, coeff_cutPoly]
  split_ifs with hi
  · exact append_coeff_old P n s i (lt_of_lt_of_le hi hh)
  · rfl

/-- The greedy choice is made once, so all earlier coefficients are retained. -/
def greedyPoly : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 =>
      if energy (append (greedyPoly n) n 1) (n + 1) ≤
          2 * ((n + 1 : ℕ) : ℤ) ^ 2 - (n + 1) then
        append (greedyPoly n) n 1 else append (greedyPoly n) n (-1)

lemma greedyPoly_properties (n : ℕ) :
    SupportedBelow (greedyPoly n) n ∧
      (∀ i < n, (greedyPoly n).coeff i = 1 ∨ (greedyPoly n).coeff i = -1) ∧
      energy (greedyPoly n) n ≤ 2 * (n : ℤ) ^ 2 - n := by
  induction n with
  | zero => simp [greedyPoly, SupportedBelow, energy]
  | succ n ih =>
      obtain ⟨hP, hsign, hE⟩ := ih
      have hsign' (s : ℤ) (hs : s = 1 ∨ s = -1) :
          ∀ i < n + 1, (append (greedyPoly n) n s).coeff i = 1 ∨
            (append (greedyPoly n) n s).coeff i = -1 := by
        intro i hi
        by_cases hin : i < n
        · rw [append_coeff_old _ _ _ _ hin]
          exact hsign i hin
        · have he : i = n := by omega
          subst i
          rw [append_coeff_last hP s]
          exact hs
      have hav := append_energy_average hP hsign
      rw [greedyPoly]
      split_ifs with h
      · exact ⟨append_supported hP _, hsign' _ (Or.inl rfl), h⟩
      · refine ⟨append_supported hP _, hsign' _ (Or.inr rfl), ?_⟩
        push_cast at h ⊢
        nlinarith

lemma cutPoly_greedy (H h : ℕ) (hh : h ≤ H) : cutPoly (greedyPoly H) h = greedyPoly h := by
  induction H with
  | zero =>
      have he : h = 0 := by omega
      subst h
      simp [greedyPoly, cutPoly]
  | succ H ih =>
      by_cases he : h = H + 1
      · subst h
        exact cutPoly_eq_self (greedyPoly_properties _).1
      · have hh' : h ≤ H := by omega
        rw [greedyPoly]
        split_ifs <;> rw [cutPoly_append _ _ _ _ hh'] <;> exact ih hh'

/-- Every prefix of the same sign polynomial satisfies the small-energy bound. -/
theorem exists_all_prefix_energies (H : ℕ) :
    ∃ P : ℤ[X], SupportedBelow P H ∧
      (∀ i < H, P.coeff i = 1 ∨ P.coeff i = -1) ∧
      ∀ h ≤ H, energy (cutPoly P h) h ≤ 2 * (h : ℤ) ^ 2 - h := by
  refine ⟨greedyPoly H, (greedyPoly_properties H).1, (greedyPoly_properties H).2.1, ?_⟩
  intro h hh
  rw [cutPoly_greedy H h hh]
  exact (greedyPoly_properties h).2.2

end
end Erdos66PrefixSign
