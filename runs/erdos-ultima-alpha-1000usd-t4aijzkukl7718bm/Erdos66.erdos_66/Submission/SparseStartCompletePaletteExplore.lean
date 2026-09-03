import Submission.MinimumIndexedPaletteExplore
import Submission.ActualCardinalityCoverageExplore

/-! Complete finite cyclic palettes whose cardinality coverage starts at
an ACTUAL logarithmic sparse member. This does not supply integer placement
or compatibility across different moduli. -/
namespace Erdos66SparseStartCompletePalette
open Erdos66MinimumIndexedPalette Erdos66ActualCardinalityCoverage
  Erdos66SaturatingCyclicFamily Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 2800000

 theorem exists_sparse_start_complete_palette (c τ η ε : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (hη1 : η ≤ 1)
    (hε : 0<ε) (hε1 : ε ≤ 1) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ (B₀ : Finset (ZMod M)) (P : Finset (Finset (ZMod M))),
        0<B₀.card ∧ B₀∈P ∧
        |actualMean M B₀ B₀/Real.log M-c|<τ ∧
        (∀ B∈P, B₀ ⊆ B) ∧
        (∀ B∈P, ∀ C∈P, B ⊆ C ∨ C ⊆ B) ∧
        (∀ B∈P, ∀ C∈P, ∀ z,
          |(cyclicCount M B C z:ℝ)-actualMean M B C| ≤ η*actualMean M B C) ∧
        (Finset.univ : Finset (ZMod M))∈P ∧ P.card ≤ M+1 ∧
        ∀ x : ℝ, (B₀.card:ℝ) ≤ x → x ≤ M →
          ∃ B∈P, x ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ (1+ε)*x := by
  let I : ℕ := ⌈4/ε⌉₊+1
  have hI : 0<I := by dsimp [I]; omega
  have hIr : (0:ℝ)<I := by exact_mod_cast hI
  have hI2 : (0:ℝ)<(I:ℝ)^2 := sq_pos_of_pos hIr
  have hscale : 4 ≤ ε*(I:ℝ) := by
    have hh := (div_le_iff₀ hε).mp (Nat.le_ceil (4/ε))
    dsimp only [I]
    push_cast
    nlinarith only [hh,hε]
  let σ := min η (min (ε/16) (min (1/16) (τ/(4*(c+1)))))
  have hσ : 0<σ := by dsimp [σ]; positivity
  have hση : σ ≤ η := min_le_left _ _
  have hσε : σ ≤ ε/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hσ16 : σ ≤ 1/16 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hστ : σ ≤ τ/(4*(c+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hσ1 : σ ≤ 1 := by linarith
  have hσcost : σ*(c+1) ≤ τ/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*(c+1))).mp hστ
    nlinarith only [hh]
  let t := min (τ/(4*(I:ℝ)^2)) (1/(I:ℝ)^2)
  have ht : 0<t := by dsimp [t]; positivity
  have htτ : t*(I:ℝ)^2 ≤ τ/4 := by
    have hh := (mul_le_mul_of_nonneg_right (min_le_left (τ/(4*(I:ℝ)^2)) (1/(I:ℝ)^2)) hI2.le)
    have he : (τ/(4*(I:ℝ)^2))*(I:ℝ)^2=τ/4 := by field_simp
    simpa only [t,he] using hh
  have ht1 : t*(I:ℝ)^2 ≤ 1 := by
    have hh := (mul_le_mul_of_nonneg_right (min_le_right (τ/(4*(I:ℝ)^2)) (1/(I:ℝ)^2)) hI2.le)
    simpa only [t,one_div,inv_mul_cancel₀ hI2.ne'] using hh
  obtain ⟨H,hH,hIH,hfamily⟩ := exists_complete_palette_with_minimum_index I (c/(I:ℝ)^2) t σ (ε/4)
    (by positivity) ht hσ hσ1 (by positivity) (by linarith)
  obtain ⟨M,hMN,hodd,hM,μ,hμ,htune,C,hC0,hCmono,hC,P,hmem,hnest,hflat,hfull,hPcard,hcover⟩ :=
    hfamily (max N₀ 2)
  letI := hM
  have hM2 : 2 ≤ M := by omega
  have hlog : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast (show 1<M by omega))
  let w : ℝ := μ*(I:ℝ)^2
  have hw : 0<w := by dsimp [w]; positivity
  have hscaled : |w/Real.log M-c|<t*(I:ℝ)^2 := by
    have hh := mul_lt_mul_of_pos_right htune hI2
    have hh' : |(μ/Real.log M-c/(I:ℝ)^2)*(I:ℝ)^2| < t*(I:ℝ)^2 := by
      simpa only [abs_mul,abs_of_pos hI2] using hh
    have he : (μ/Real.log M-c/(I:ℝ)^2)*(I:ℝ)^2=w/Real.log M-c := by
      dsimp [w]
      field_simp
    rwa [he] at hh'
  have hnear : |w/Real.log M-c|<τ/4 := hscaled.trans_le htτ
  have hnear1 : |w/Real.log M-c|<1 := hscaled.trans_le ht1
  have hself : ∀ i≤H, ∀ z,
      |(cyclicCount M (C i) (C i) z:ℝ)-μ*(i:ℝ)^2| ≤ σ*(μ*(i:ℝ)^2) := by
    intro i hi z
    convert hC i hi i hi z using 1 <;> ring
  have herror : |actualMean M (C I) (C I)-w| ≤ σ*w :=
    actualMean_error M (C I) (C I) w (σ*w) (hself I hIH)
  have hactual : |actualMean M (C I) (C I)/Real.log M-c|<τ := by
    have hdiv := div_le_div_of_nonneg_right herror hlog.le
    have he : |actualMean M (C I) (C I)/Real.log M-w/Real.log M| ≤ σ*(w/Real.log M) := by
      simpa only [←sub_div,abs_div,abs_of_pos hlog,mul_div_assoc] using hdiv
    have hu : w/Real.log M ≤ c+1 := by have hh := (abs_lt.mp hnear1).2; linarith
    have hmul := mul_le_mul_of_nonneg_left hu hσ.le
    have htriangle := abs_sub_le (actualMean M (C I) (C I)/Real.log M) (w/Real.log M) c
    linarith
  have hcardpos : 0<(C I).card := by
    have hmeanpos : 0<actualMean M (C I) (C I) := by
      have hh := (abs_le.mp herror).1
      have hm : 0<(1-σ)*w := mul_pos (by linarith) hw
      nlinarith only [hh,hm]
    by_contra hh
    have hz : (C I).card=0 := by omega
    simp only [actualMean,hz,Nat.cast_zero,zero_mul,zero_div] at hmeanpos
    linarith
  have hCI : C I∈P := hmem I hI hIH
  have hcover_low := linear_family_cardinality_coverage M C μ σ ε hμ.le hσ.le hσε hε hε1 I H hIH hscale hself
  have hcover_all : ∀ x : ℝ, ((C I).card:ℝ) ≤ x → x ≤ M →
      ∃ B∈P, x ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ (1+ε)*x := by
    intro x hxI hxM
    by_cases hxH : x ≤ ((C H).card:ℝ)
    · obtain ⟨j,hIj,hjH,hxj,hju⟩ := hcover_low x hxI hxH
      exact ⟨C j,hmem j (by omega) hjH,hxj,hju⟩
    · obtain ⟨B,hB,hxB,hBu⟩ := hcover x (le_of_not_ge hxH) hxM
      refine ⟨B,hB,hxB,?_⟩
      convert hBu using 1 <;> ring
  let Q := P.filter (fun B ↦ C I ⊆ B)
  have hQI : C I∈Q := Finset.mem_filter.mpr ⟨hCI,Finset.Subset.refl _⟩
  have hQsub : Q ⊆ P := Finset.filter_subset _ _
  refine ⟨M,by omega,hodd,hM,C I,Q,hcardpos,hQI,hactual,
    fun B hB ↦ (Finset.mem_filter.mp hB).2,
    fun B hB E hE ↦ hnest B (hQsub hB) E (hQsub hE),?_,
    Finset.mem_filter.mpr ⟨hfull,Finset.subset_univ _⟩,
    (Finset.card_le_card hQsub).trans hPcard,?_⟩
  · intro B hB E hE z
    exact (hflat B (hQsub hB) E (hQsub hE) z).trans
      (mul_le_mul_of_nonneg_right hση (actualMean_nonneg M B E))
  · intro x hxI hxM
    obtain ⟨B,hB,hxB,hBu⟩ := hcover_all x hxI hxM
    have hsub : C I ⊆ B := by
      rcases hnest (C I) hCI B hB with hh | hh
      · exact hh
      · have hcard : (C I).card ≤ B.card := by exact_mod_cast hxI.trans hxB
        have he := Finset.eq_of_subset_of_card_le hh hcard
        exact he ▸ Finset.Subset.refl B
    exact ⟨B,Finset.mem_filter.mpr ⟨hB,hsub⟩,hxB,hBu⟩

end Erdos66SparseStartCompletePalette
