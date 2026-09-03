import Submission.RelativeChang
import Submission.FourierSmoothing

/-! Maximal approximately dissociated families and relative spectrum control. -/
namespace Erdos3RelativeSpectrum
open Finset Erdos3RelativeRiesz Erdos3RelativeChang Erdos3FiniteFourier
  Erdos3FiniteBohr Erdos3FourierSmoothing Erdos3BohrTranslation
  Erdos3CorrelationSifting Erdos3ChangSpectrum
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2500000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma meanChar_div (C : Finset G) (χ ψ : AddChar G ℂ) :
    meanChar C (χ/ψ) = 𝔼 x : C, χ x * conj (ψ x) := by
  simp only [meanChar, AddChar.div_apply, AddChar.map_neg_eq_inv,
    AddChar.inv_apply_eq_conj]

lemma norm_meanChar_inv (C : Finset G) (χ : AddChar G ℂ) :
    ‖meanChar C χ⁻¹‖ = ‖meanChar C χ‖ := by
  simp only [meanChar, AddChar.inv_apply, AddChar.map_neg_eq_inv,
    AddChar.inv_apply_eq_conj, ← expect_conj, Complex.norm_conj]

lemma norm_meanChar_div_comm (C : Finset G) (χ ψ : AddChar G ℂ) :
    ‖meanChar C (χ/ψ)‖ = ‖meanChar C (ψ/χ)‖ := by
  rw [show χ/ψ = (ψ/χ)⁻¹ by rw [inv_div], norm_meanChar_inv]

lemma ApproxDissociated.norm_meanChar_le {C : Finset G} {ε : ℝ}
    {D : Finset (AddChar G ℂ)} (hD : ApproxDissociated C ε D)
    {s t : Finset (AddChar G ℂ)} (hs : s ⊆ D) (ht : t ⊆ D) (hst : s ≠ t) :
    ‖meanChar C ((∏ χ ∈ s, χ)/(∏ χ ∈ t, χ))‖ ≤ ε := by
  rw [meanChar_div]
  exact hD s hs t ht hst

lemma erase_subset_of_subset_insert {D s : Finset (AddChar G ℂ)}
    {χ : AddChar G ℂ} (hs : s ⊆ insert χ D) : s.erase χ ⊆ D := by
  intro ψ hψ
  have hh := mem_erase.mp hψ
  exact (mem_insert.mp (hs hh.2)).resolve_left hh.1

/-- Failure to extend approximate dissociation yields a character with large C-mean,
expressed using the added character and two subsets of the old generators. -/
lemma extension_obstruction {C : Finset G} {ε : ℝ} {D : Finset (AddChar G ℂ)}
    (hD : ApproxDissociated C ε D) (χ : AddChar G ℂ)
    (hfail : ¬ ApproxDissociated C ε (insert χ D)) :
    ∃ s ⊆ D, ∃ t ⊆ D,
      ε < ‖meanChar C (((∏ ψ ∈ s, ψ)*χ)/(∏ ψ ∈ t, ψ))‖ := by
  unfold ApproxDissociated at hfail
  push_neg at hfail
  obtain ⟨s, hs, t, ht, hst, hbig⟩ := hfail
  rw [← meanChar_div] at hbig
  have hs' := erase_subset_of_subset_insert hs
  have ht' := erase_subset_of_subset_insert ht
  have hnone (S T : Finset (AddChar G ℂ))
      (hS : S ⊆ insert χ D) (hT : T ⊆ insert χ D)
      (hχS : χ ∉ S) (hχT : χ ∉ T) (hST : S ≠ T) :
      ‖meanChar C ((∏ ψ ∈ S, ψ)/(∏ ψ ∈ T, ψ))‖ ≤ ε := by
    apply ApproxDissociated.norm_meanChar_le hD _ _ hST
    · intro ψ hψ
      exact (mem_insert.mp (hS hψ)).resolve_left (fun he ↦ hχS (he ▸ hψ))
    · intro ψ hψ
      exact (mem_insert.mp (hT hψ)).resolve_left (fun he ↦ hχT (he ▸ hψ))
  by_cases hχs : χ ∈ s
  · by_cases hχt : χ ∈ t
    · have herase : s.erase χ ≠ t.erase χ := by
        intro he
        apply hst
        rw [← insert_erase hχs, ← insert_erase hχt, he]
      have hh := ApproxDissociated.norm_meanChar_le hD hs' ht' herase
      have he : ((∏ ψ ∈ s, ψ)/(∏ ψ ∈ t, ψ)) =
          ((∏ ψ ∈ s.erase χ, ψ)/(∏ ψ ∈ t.erase χ, ψ)) := by
        rw [← prod_erase_mul s (fun ψ ↦ ψ) hχs, ← prod_erase_mul t (fun ψ ↦ ψ) hχt]
        exact mul_div_mul_right_eq_div _ _ _
      rw [he] at hbig
      exact (not_lt_of_ge hh hbig).elim
    · refine ⟨s.erase χ, hs', t, ?_, ?_⟩
      · simpa only [erase_eq_of_notMem hχt] using ht'
      · simpa only [prod_erase_mul s (fun ψ ↦ ψ) hχs] using hbig
  · by_cases hχt : χ ∈ t
    · refine ⟨t.erase χ, ht', s, ?_, ?_⟩
      · simpa only [erase_eq_of_notMem hχs] using hs'
      · rw [prod_erase_mul t (fun ψ ↦ ψ) hχt, norm_meanChar_div_comm]
        exact hbig
    · exact (not_lt_of_ge (hnone s t hs ht hχs hχt hst) hbig).elim

/-- A rank cutoff makes the error tolerance independent of the selected family. -/
theorem exists_relative_spectrum_generators (A C : Finset G)
    (hA : A.Nonempty) (hC : C.Nonempty) (hAC : A ⊆ C)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 ≤ ε)
    {R : ℕ} (hR : 4*Real.log (2/((A.card : ℝ)/C.card))/η^2 < R+1)
    (herr : ε*4^(R+1) ≤ 1) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ spectrum A η ∧ D.card ≤ R ∧
      ApproxDissociated C ε D ∧
      ∀ χ ∈ spectrum A η, χ ∉ D →
        ∃ s ⊆ D, ∃ t ⊆ D,
          ε < ‖meanChar C (((∏ ψ ∈ s, ψ)*χ)/(∏ ψ ∈ t, ψ))‖ := by
  let F := (spectrum A η).powerset.filter
    (fun D ↦ D.card ≤ R ∧ ApproxDissociated C ε D)
  have hF : F.Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩⟩
    refine ⟨by simp, ?_⟩
    intro s hs t ht hst
    exact (hst ((subset_empty.mp hs).trans (subset_empty.mp ht).symm)).elim
  obtain ⟨D, hDF, hmax⟩ := exists_max_image F card hF
  obtain ⟨hDspec, hDR, hD⟩ := mem_filter.mp hDF
  have hsub := mem_powerset.mp hDspec
  refine ⟨D, hsub, hDR, hD, ?_⟩
  intro χ hχ hχD
  apply extension_obstruction hD χ
  intro hext
  have hsub' : insert χ D ⊆ spectrum A η := insert_subset hχ hsub
  have hcard : (insert χ D).card = D.card+1 := card_insert_of_notMem hχD
  have herr' : ε*4^(insert χ D).card ≤ 1 := by
    apply le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega : (insert χ D).card ≤ R+1)) hε) herr
  have hb := relative_spectrum_bound A C hA hC hAC hη hη1 hε (insert χ D) hext herr'
    (fun ψ hψ ↦ (mem_filter.mp (hsub' hψ)).2)
  have hcardR : (insert χ D).card ≤ R := by
    have hh := hb.trans_lt hR
    have hn : (insert χ D).card < R+1 := by exact_mod_cast hh
    omega
  have hF' : insert χ D ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hsub', hcardR, hext⟩
  have := hmax (insert χ D) hF'
  omega

#print axioms extension_obstruction
#print axioms exists_relative_spectrum_generators
end Erdos3RelativeSpectrum
