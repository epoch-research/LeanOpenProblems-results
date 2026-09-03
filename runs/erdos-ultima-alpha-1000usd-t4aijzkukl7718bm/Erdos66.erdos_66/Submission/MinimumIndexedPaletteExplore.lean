import Submission.LogarithmicCompletePaletteExplore

/-! The complete finite palette theorem with a prescribed lower bound on
the largest algebraic index. No integer-scale compatibility is asserted. -/
namespace Erdos66MinimumIndexedPalette
open Filter Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
  Erdos66LogarithmicMixedFamily Erdos66DenseCyclicPaletteCompletion Erdos66LogTuning
  Erdos66LogarithmicCompletePalette
open scoped Topology Classical
set_option maxHeartbeats 2500000

/-- For any fixed requested accuracy and logarithmic base coefficient, a
finite number H of algebraic sparse levels suffices BEFORE choosing an
arbitrarily large odd modulus. They extend to a same-accuracy palette that
reaches full density without multiplicative gaps above its H-th level. -/
theorem exists_complete_palette_with_minimum_index (I₀ : ℕ) (c τ η g : ℝ) (hc : 0 < c) (hτ : 0 < τ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1/4) :
    ∃ H : ℕ, 0 < H ∧ I₀ ≤ H ∧ ∀ N₀ : ℕ,
      ∃ M : ℕ, N₀ < M ∧ Odd M ∧ ∃ hM : NeZero M,
        ∃ μ : ℝ, 0 < μ ∧ |μ/Real.log M-c| < τ ∧
          ∃ C : ℕ → Finset (ZMod M), C 0=∅ ∧ Monotone C ∧
            (∀ i ≤ H, ∀ j ≤ H, ∀ z,
              |(cyclicCount M (C i) (C j) z : ℝ)-μ*i*j| ≤ η*(μ*i*j)) ∧
            ∃ P : Finset (Finset (ZMod M)), (∀ i, 1 ≤ i → i ≤ H → C i∈P) ∧
              (∀ D∈P, ∀ E∈P, D ⊆ E ∨ E ⊆ D) ∧
              (∀ D∈P, ∀ E∈P, ∀ z,
                |(cyclicCount M D E z : ℝ)-actualMean M D E| ≤ η*actualMean M D E) ∧
              (Finset.univ : Finset (ZMod M))∈P ∧ P.card ≤ M+1 ∧
              ∀ x : ℝ, ((C H).card : ℝ) ≤ x → x ≤ M →
                ∃ D∈P, x ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ (1+4*g)*x := by
  obtain ⟨H,hHbig₀⟩ := exists_nat_gt (max (I₀:ℝ) (max (1 : ℝ) (200000/(η^2*g^2*c))))
  have hHbig : max (1 : ℝ) (200000/(η^2*g^2*c)) < H :=
    lt_of_le_of_lt (le_max_right _ _) hHbig₀
  have hI₀ : I₀ ≤ H := by
    have hh := lt_of_le_of_lt (le_max_left _ _) hHbig₀
    exact_mod_cast hh.le
  have hH : 0 < H := by
    have hh := lt_of_le_of_lt (le_max_left _ _) hHbig
    exact_mod_cast (show (0 : ℝ) < H by linarith)
  have hH1 : 1 ≤ H := hH
  have hbudget : 200000 < η^2*g^2*c*H := by
    have hh := (div_lt_iff₀ (by positivity : 0 < η^2*g^2*c)).mp
      (lt_of_le_of_lt (le_max_right _ _) hHbig)
    nlinarith
  let σ := min (η/4) (1/4)
  have hσ : 0 < σ := lt_min (by positivity) (by norm_num)
  have hση : 4*σ ≤ η := by have := min_le_left (η/4) (1/4); dsimp [σ]; linarith
  have hσquarter : σ ≤ 1/4 := min_le_right _ _
  have hσhalf : σ ≤ 1/2 := by linarith
  let τ' := min τ (c/2)
  have hτ' : 0 < τ' := lt_min hτ (by positivity)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (log_nat_atTop.eventually_ge_atTop (128/(η*g*c*(H : ℝ)^2)))
  refine ⟨H,hH,hI₀,fun N₀ ↦ ?_⟩
  obtain ⟨M,hMN,hodd,hM,μ,hμ,htune,C,hC0,hCmono,hC⟩ :=
    exists_logarithmic_mixed_family c τ' σ hc hτ' hσ (by linarith) H (max N₀ (max L 2))
  letI := hM
  have hM2 : 2 ≤ M := by omega
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM2)
  have htuneτ : |μ/Real.log M-c| < τ := htune.trans_le (min_le_left _ _)
  have hμlower : (c/2)*Real.log M ≤ μ := by
    have hh := (abs_lt.mp htune).1
    have hτc : τ' ≤ c/2 := min_le_right _ _
    have hl : c/2 ≤ μ/Real.log M := by linarith
    exact (le_div_iff₀ hlog).mp hl
  have hlow (i j : ℕ) (hi : i ≤ H) (hj : j ≤ H) :
      (μ*i*j)/2 ≤ actualMean M (C i) (C j) := by
    have hh := actualMean_error M (C i) (C j) (μ*i*j) (σ*(μ*i*j)) (hC i hi j hj)
    have hlo := (abs_le.mp hh).1
    have hsmall := mul_le_mul_of_nonneg_right hσhalf (show 0 ≤ μ*i*j by positivity)
    linarith
  have hflat (i j : ℕ) (hi : i ≤ H) (hj : j ≤ H) :
      ∀ z, |(cyclicCount M (C i) (C j) z : ℝ)-actualMean M (C i) (C j)| ≤
        η*actualMean M (C i) (C j) := by
    intro z
    have hh := normalize_to_actualMean M (C i) (C j) (μ*i*j) σ (by positivity) hσ.le hσhalf (hC i hi j hj) z
    exact hh.trans (mul_le_mul_of_nonneg_right hση (actualMean_nonneg M _ _))
  let P₀ : Finset (Finset (ZMod M)) := (Finset.Icc 1 H).image C
  have hmem (i : ℕ) (hi : 1 ≤ i) (hiH : i ≤ H) : C i∈P₀ :=
    Finset.mem_image.mpr ⟨i,Finset.mem_Icc.mpr ⟨hi,hiH⟩,rfl⟩
  have hnest : ∀ D∈P₀, ∀ E∈P₀, D ⊆ E ∨ E ⊆ D := by
    intro D hD E hE
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hE
    rcases le_total i j with hij | hji
    · exact Or.inl (hCmono hij)
    · exact Or.inr (hCmono hji)
  have hflat₀ : ∀ D∈P₀, ∀ E∈P₀, ∀ z,
      |(cyclicCount M D E z : ℝ)-actualMean M D E| ≤ η*actualMean M D E := by
    intro D hD E hE
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hE
    exact hflat i j (Finset.mem_Icc.mp hi).2 (Finset.mem_Icc.mp hj).2
  have hmax₀ : ∀ D∈P₀, D ⊆ C H := by
    intro D hD
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hD
    exact hCmono (Finset.mem_Icc.mp hi).2
  have hmin₀ : ∀ D∈P₀, (C 1).card ≤ D.card := by
    intro D hD
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hD
    exact Finset.card_le_card (hCmono (Finset.mem_Icc.mp hi).1)
  have hlarge : 32 ≤ η*g*(((C H).card : ℝ)^2/M) := by
    have hl := hL M (by omega)
    have hpow : (0 : ℝ) < η*g*c*(H : ℝ)^2 := by positivity
    have hscale := (div_le_iff₀ hpow).mp hl
    have hbase := hlow H H le_rfl le_rfl
    have hmul := mul_le_mul_of_nonneg_left hμlower (show 0 ≤ (H : ℝ)^2/2 by positivity)
    have hmul' := mul_le_mul_of_nonneg_left hbase (show 0 ≤ η*g by positivity)
    have hmul'' := mul_le_mul_of_nonneg_left hmul (show 0 ≤ η*g by positivity)
    dsimp [actualMean] at hmul'
    ring_nf at hscale hmul' hmul'' ⊢
    nlinarith only [hscale,hmul',hmul'']
  have hthreshold : 8192*Real.log (2*((M+2)*M+1)) <
      η^2*g^2*((((C 1).card : ℝ)*(C H).card)/M) := by
    have htest := logarithmic_test_bound M hM2
    have he : (2 : ℝ)*((M+2)*M+1)=2*(M+2)*M+2 := by ring
    rw [he]
    have h₁ := hlow 1 H hH1 le_rfl
    simp only [Nat.cast_one,mul_one] at h₁
    have h₂ := mul_le_mul_of_nonneg_right hμlower (show 0 ≤ (H : ℝ)/2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ η^2*g^2 by positivity)
    have h₄ := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ η^2*g^2 by positivity)
    have h₅ := mul_lt_mul_of_pos_right hbudget hlog
    dsimp [actualMean] at h₃
    nlinarith
  obtain ⟨P,hPP,hPnest,hPflat,hPfull,hPcard,hPcover⟩ :=
    exists_complete_cyclic_palette M hodd P₀ (C H) (C 1).card η g hη hη1 hg hg1
      hnest hflat₀ (hmem H hH1 le_rfl) hmax₀ hmin₀ hlarge hthreshold
  refine ⟨M,by omega,hodd,hM,μ,hμ,htuneτ,C,hC0,hCmono,?_,P,?_,hPnest,hPflat,hPfull,hPcard,hPcover⟩
  · intro i hi j hj z
    exact (hC i hi j hj z).trans (mul_le_mul_of_nonneg_right (by linarith : σ ≤ η) (by positivity))
  · intro i hi hiH
    exact hPP (hmem i hi hiH)

end Erdos66MinimumIndexedPalette
