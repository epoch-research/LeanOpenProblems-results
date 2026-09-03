import Submission.SparseStartCompletePaletteExplore
import Submission.OuterMixedPrefixExplore

/-! Complete logarithmically sparse palettes with uniform mixed endpoint-prefix
control. This is a finite-modulus result, not a natural-number limit. -/
namespace Erdos66PrefixBalancedPalette
open Filter Erdos66SparseStartCompletePalette Erdos66OuterMixedPrefix
  Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily Erdos66CyclicThickening
open scoped Classical Topology
set_option maxHeartbeats 2400000

lemma retune_outer_mean (M K : ℕ) (hM : 1<M) (hK : 0<K)
    (c τ b : ℝ) (hc : 0<c) (hτ : 0<τ)
    (hsmall : c*Real.log K/Real.log M < τ/2)
    (htune : |b/Real.log M-c/K| < τ/(2*K)) :
    |(K:ℝ)*b/Real.log (M*K:ℕ)-c|<τ := by
  have hMr : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hLM : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hLK : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg hK1
  have hlog : Real.log (M*K:ℕ)=Real.log M+Real.log K := by
    rw [Nat.cast_mul,Real.log_mul hMr.ne' hKr.ne']
  have hLN : 0<Real.log (M*K:ℕ) := by rw [hlog]; linarith
  have he : b/Real.log M-c/K = (b-(c/K)*Real.log M)/Real.log M := by field_simp
  rw [he,abs_div,abs_of_pos hLM] at htune
  have hh := mul_lt_mul_of_pos_left ((div_lt_iff₀ hLM).mp htune) hKr
  have he1 : (K:ℝ)*(b-c/K*Real.log M)=K*b-c*Real.log M := by field_simp
  have he2 : (K:ℝ)*(τ/(2*K)*Real.log M)=τ/2*Real.log M := by field_simp
  have hnear : |(K:ℝ)*b-c*Real.log M|<τ/2*Real.log M := by
    rw [←abs_of_pos hKr,←abs_mul,abs_of_pos hKr,he1,he2] at hh
    exact hh
  have hcost := (div_lt_iff₀ hLM).mp hsmall
  have hrest : |c*Real.log M-c*Real.log (M*K:ℕ)|=c*Real.log K := by
    rw [hlog]
    have hh : c*Real.log M-c*(Real.log M+Real.log K)=-(c*Real.log K) := by ring
    rw [hh,abs_neg,abs_of_nonneg (mul_nonneg hc.le hLK)]
  have htri := abs_sub_le ((K:ℝ)*b) (c*Real.log M) (c*Real.log (M*K:ℕ))
  rw [hrest] at htri
  have hnum : |(K:ℝ)*b-c*Real.log (M*K:ℕ)|<τ*Real.log (M*K:ℕ) := by
    rw [hlog] at htri ⊢
    nlinarith only [hnear,hcost,htri,mul_nonneg hτ.le hLK]
  rw [div_sub' hLN.ne',abs_div,abs_of_pos hLN]
  exact (div_lt_iff₀ hLN).mpr (by simpa only [mul_comm c] using hnum)

/-- For every fixed precision, finite palettes can be made simultaneously
mixed-flat and spatially balanced, with actual logarithmic sparse start. -/
theorem exists_prefix_balanced_complete_palette (c τ η ε : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (hη1 : η ≤ 1)
    (hε : 0<ε) (hε1 : ε ≤ 1) (N₀ : ℕ) :
    ∃ N : ℕ, N₀<N ∧ Odd N ∧ ∃ hN : NeZero N,
      ∃ (B₀ : Finset (ZMod N)) (P : Finset (Finset (ZMod N))),
        0<B₀.card ∧ B₀∈P ∧
        |actualMean N B₀ B₀/Real.log N-c|<τ ∧
        (∀ B∈P, B₀ ⊆ B) ∧
        (∀ B∈P, ∀ C∈P, B ⊆ C ∨ C ⊆ B) ∧
        (∀ B∈P, ∀ C∈P, ∀ z,
          |(cyclicCount N B C z:ℝ)-actualMean N B C| ≤ η*actualMean N B C) ∧
        (∀ B∈P, ∀ C∈P, ∀ z u, u ≤ N →
          |(prefixCount N B C z u:ℝ)-((u:ℝ)/N)*actualMean N B C| ≤ η*actualMean N B C) ∧
        (Finset.univ : Finset (ZMod N))∈P ∧ P.card ≤ N+1 ∧
        ∀ x : ℝ, (B₀.card:ℝ) ≤ x → x ≤ N →
          ∃ B∈P, x ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ (1+ε)*x := by
  let K : ℕ := 2*⌈2/η⌉₊+1
  have hK : 0<K := by dsimp [K]; omega
  have hKodd : Odd K := ⟨⌈2/η⌉₊,rfl⟩
  letI : NeZero K := ⟨by omega⟩
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hscale : 2 ≤ η*(K:ℝ) := by
    have hh := (div_le_iff₀ hη).mp (Nat.le_ceil (2/η))
    dsimp only [K]
    push_cast
    nlinarith only [hh,hη]
  have hlim : Tendsto (fun M : ℕ ↦ (c*Real.log K)/Real.log M) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_div_atTop _
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually_lt_const (show 0<τ/2 by positivity))
  obtain ⟨M,hMN,hodd,hM,B₀,P,hBpos,hBmem,htune,hBsub,hnest,hflat,hfull,hPcard,hcover⟩ :=
    exists_sparse_start_complete_palette (c/K) (τ/(2*K)) (η/4) ε
      (by positivity) (by positivity) (by positivity) (by linarith) hε hε1 (max N₀ (max L 2))
  letI := hM
  have hMK : M ≤ M*K := Nat.le_mul_of_pos_right M hK
  have hM2 : 1<M := by omega
  have hactual : |actualMean (M*K) (outerLift M K B₀) (outerLift M K B₀)/Real.log (M*K:ℕ)-c|<τ := by
    rw [outerLift_mean]
    exact retune_outer_mean M K hM2 hK c τ (actualMean M B₀ B₀) hc hτ (hL M (by omega)) htune
  let Q := P.image (outerLift M K)
  have hQmem : outerLift M K B₀∈Q := Finset.mem_image.mpr ⟨B₀,hBmem,rfl⟩
  have hQcard : Q.card ≤ M*K+1 := (Finset.card_image_le.trans hPcard).trans (by omega)
  refine ⟨M*K,by omega,hodd.mul hKodd,inferInstance,outerLift M K B₀,Q,
    by rw [outerLift_card]; positivity,hQmem,hactual,?_,?_,?_,?_,?_,hQcard,?_⟩
  · intro B hB
    obtain ⟨B,hBP,rfl⟩ := Finset.mem_image.mp hB
    exact outerLift_mono M K (hBsub B hBP)
  · intro B hB C hC
    obtain ⟨B,hBP,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C,hCP,rfl⟩ := Finset.mem_image.mp hC
    rcases hnest B hBP C hCP with hh | hh
    · exact Or.inl (outerLift_mono M K hh)
    · exact Or.inr (outerLift_mono M K hh)
  · intro B hB C hC z
    obtain ⟨B,hBP,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C,hCP,rfl⟩ := Finset.mem_image.mp hC
    rw [outer_cyclicCount,outerLift_mean,Nat.cast_mul,←mul_sub,abs_mul,abs_of_pos hKr]
    have hh := mul_le_mul_of_nonneg_left (hflat B hBP C hCP (reduceDigit M K z)) hKr.le
    have hm := actualMean_nonneg M B C
    nlinarith only [hh,mul_nonneg hη.le (mul_nonneg hKr.le hm)]
  · intro B hB C hC
    obtain ⟨B,hBP,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C,hCP,rfl⟩ := Finset.mem_image.mp hC
    simpa only [Nat.cast_mul] using outer_prefix_relative_error M K B C η (η/4) hη.le (by positivity) le_rfl hscale (hflat B hBP C hCP)
  · exact Finset.mem_image.mpr ⟨Finset.univ,hfull,outerLift_univ M K⟩
  · intro x hx₀ hxN
    have hxB : (B₀.card:ℝ) ≤ x/K := by
      rw [outerLift_card,Nat.cast_mul] at hx₀
      apply (le_div_iff₀ hKr).mpr
      nlinarith only [hx₀]
    have hxM : x/K ≤ M := by
      apply (div_le_iff₀ hKr).mpr
      simpa only [Nat.cast_mul] using hxN
    obtain ⟨B,hB,hxB,hBx⟩ := hcover (x/K) hxB hxM
    refine ⟨outerLift M K B,Finset.mem_image.mpr ⟨B,hB,rfl⟩,?_,?_⟩
    · rw [outerLift_card,Nat.cast_mul]
      have hh := (div_le_iff₀ hKr).mp hxB
      nlinarith only [hh]
    · rw [outerLift_card,Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_left hBx hKr.le
      have he : (K:ℝ)*((1+ε)*(x/K))=(1+ε)*x := by field_simp
      rwa [he] at hh

end Erdos66PrefixBalancedPalette
