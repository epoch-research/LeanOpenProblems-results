import Submission.AnnulusExplore
import Submission.Explore

/-! Finite prescribed-prefix extensions with logarithmic good annuli.
The starting point of a new annulus is not uniformly bounded by the prefix. -/
namespace Erdos66AnnulusExtension
open Filter AdditiveCombinatorics Erdos66Explore Erdos66Annulus
open scoped Topology Classical

lemma sumRep_union_Iio_le (A : Set ℕ) (L n : ℕ) :
    sumRep (A ∪ Set.Iio L) n ≤ sumRep A n + 2 * L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have he : A ∪ Set.Iio (L + 1) = insert L (A ∪ Set.Iio L) := by
      ext x
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_insert_iff]
      by_cases hx : x ∈ A <;> simp [hx] <;> omega
    rw [he]
    have hh := sumRep_insert_le (A ∪ Set.Iio L) L n
    omega

lemma sumRep_eq_tail_error (A B : Set ℕ) (L n : ℕ)
    (h : ∀ x ≥ L, x ∈ A ↔ x ∈ B) : |(sumRep A n : ℝ) - sumRep B n| ≤ 2 * L := by
  have hAB : A ⊆ B ∪ Set.Iio L := by
    intro x hx
    by_cases hL : x < L
    · exact Or.inr hL
    · exact Or.inl ((h x (by omega)).mp hx)
  have hBA : B ⊆ A ∪ Set.Iio L := by
    intro x hx
    by_cases hL : x < L
    · exact Or.inr hL
    · exact Or.inl ((h x (by omega)).mpr hx)
  have h₁ := (sumRep_mono hAB n).trans (sumRep_union_Iio_le B L n)
  have h₂ := (sumRep_mono hBA n).trans (sumRep_union_Iio_le A L n)
  have h₁' : (sumRep A n : ℝ) ≤ sumRep B n + 2 * L := by exact_mod_cast h₁
  have h₂' : (sumRep B n : ℝ) ≤ sumRep A n + 2 * L := by exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

def replacePrefix (A B : Set ℕ) (L : ℕ) : Set ℕ :=
  (A ∩ Set.Ici L) ∪ (B ∩ Set.Iio L)

lemma replacePrefix_below (A B : Set ℕ) {L n : ℕ} (hn : n < L) :
    n ∈ replacePrefix A B L ↔ n ∈ B := by simp [replacePrefix, hn, show ¬L ≤ n by omega]

lemma replacePrefix_above (A B : Set ℕ) {L n : ℕ} (hn : L ≤ n) :
    n ∈ replacePrefix A B L ↔ n ∈ A := by simp [replacePrefix, hn, show ¬n < L by omega]

lemma replacePrefix_finite (A B : Set ℕ) (L : ℕ) (hA : A.Finite) :
    (replacePrefix A B L).Finite :=
  (hA.subset Set.inter_subset_left).union ((Set.finite_Iio L).subset Set.inter_subset_right)

/-- Every finite prefix has finite extensions with arbitrarily late good annuli.
This has weaker quantifiers than the finite-prefix criterion for the conjecture. -/
theorem exists_annulus_extension (B : Set ℕ) (L : ℕ) (ε : ℝ) (hε : 0 < ε)
    (R N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ A : Set ℕ, A.Finite ∧
      (∀ n < L, n ∈ A ↔ n ∈ B) ∧
      ∀ n : ℕ, N ≤ n → n ≤ R * N → |(sumRep A n : ℝ) / Real.log n - 1| < ε := by
  have hsmall := Erdos66LogTuning.log_nat_atTop.const_div_atTop (2 * (L : ℝ))
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hsmall.eventually_lt_const (half_pos hε))
  obtain ⟨N, hN, hNpos, A, hAfin, hA⟩ :=
    exists_logarithmic_annulus (ε / 2) (half_pos hε) R (max N₀ (max P 2)) hR
  refine ⟨N, by omega, hNpos, replacePrefix A B L, replacePrefix_finite A B L hAfin,
    fun n hn ↦ replacePrefix_below A B hn, ?_⟩
  intro n hnlo hnhi
  have hn2 : 2 ≤ n := by omega
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have he := sumRep_eq_tail_error (replacePrefix A B L) A L n
    (fun x hx ↦ replacePrefix_above A B hx)
  have he' : |(sumRep (replacePrefix A B L) n : ℝ) / Real.log n -
      (sumRep A n : ℝ) / Real.log n| ≤ 2 * L / Real.log n := by
    rw [← sub_div, abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right he hl.le
  have hgood := hA n hnlo hnhi
  have hperturb := hP n (by omega)
  calc
    _ = |((sumRep (replacePrefix A B L) n : ℝ) / Real.log n -
        (sumRep A n : ℝ) / Real.log n) + ((sumRep A n : ℝ) / Real.log n - 1)| := by congr 1; ring
    _ ≤ |(sumRep (replacePrefix A B L) n : ℝ) / Real.log n - (sumRep A n : ℝ) / Real.log n| +
        |(sumRep A n : ℝ) / Real.log n - 1| := abs_add_le _ _
    _ < ε := by linarith

end Erdos66AnnulusExtension
