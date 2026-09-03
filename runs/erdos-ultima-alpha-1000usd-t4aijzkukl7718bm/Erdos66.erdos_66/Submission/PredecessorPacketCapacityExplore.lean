import Submission.InfinitePredecessorReplacementExplore

/-! A capacity restriction on disjoint-cell packet repairs. It concerns this
specific representation-by-packets method, not the original conjecture. -/
namespace Erdos66PredecessorPacketCapacity
open Filter AdditiveCombinatorics Erdos66Counting Erdos66PredecessorCell
open scoped Classical Topology
set_option maxHeartbeats 2200000

lemma cell_capacity (A : Set ℕ) (F : Finset ℕ) (N : ℕ)
    (hmem : ∀ u ∈ F, predecessor A u ∈ A)
    (hinj : Set.InjOn (predecessor A) (F : Set ℕ)) (hsupp : ∀ u ∈ F, u < N) :
    F.card ≤ count A N := by
  have hsub : F.image (predecessor A) ⊆ cutoff A N := by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    have hl := predecessor_le A u
    exact mem_cutoff.mpr ⟨by have := hsupp u hu; omega, hmem u hu⟩
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

lemma packet_capacity {ι : Type*} (A : Set ℕ) (T : Finset ι) (P : ι → Finset ℕ) (N : ℕ)
    (hdis : (T : Set ι).PairwiseDisjoint P)
    (hmem : ∀ i ∈ T, ∀ u ∈ P i, predecessor A u ∈ A)
    (hinj : Set.InjOn (predecessor A) ((T.biUnion P : Finset ℕ) : Set ℕ))
    (hsupp : ∀ i ∈ T, ∀ u ∈ P i, u < N) :
    (∑ i ∈ T, (P i).card) ≤ count A N := by
  rw [← Finset.card_biUnion hdis]
  apply cell_capacity A (T.biUnion P) N
  · intro u hu
    obtain ⟨i,hi,hu⟩ := Finset.mem_biUnion.mp hu
    exact hmem i hi u hu
  · exact hinj
  · intro u hu
    obtain ⟨i,hi,hu⟩ := Finset.mem_biUnion.mp hu
    exact hsupp i hi u hu

lemma uniform_packet_capacity {ι : Type*} (A : Set ℕ) (T : Finset ι) (P : ι → Finset ℕ)
    (N : ℕ) (d : ℝ)
    (hdis : (T : Set ι).PairwiseDisjoint P)
    (hmem : ∀ i ∈ T, ∀ u ∈ P i, predecessor A u ∈ A)
    (hinj : Set.InjOn (predecessor A) ((T.biUnion P : Finset ℕ) : Set ℕ))
    (hsupp : ∀ i ∈ T, ∀ u ∈ P i, u < N)
    (hsize : ∀ i ∈ T, d ≤ ((P i).card : ℝ)) :
    d*T.card ≤ count A N := by
  have hs := Finset.sum_le_sum hsize
  have hc : (∑ i ∈ T, ((P i).card : ℝ)) ≤ count A N :=
    by exact_mod_cast packet_capacity A T P N hdis hmem hinj hsupp
  have he : (∑ _i ∈ T, d) = d*T.card := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [he] at hs
  exact hs.trans hc

lemma packet_target_bound {ι : Type*} (A : Set ℕ) (T : Finset ι) (P : ι → Finset ℕ)
    (N : ℕ) (d K C : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (hdis : (T : Set ι).PairwiseDisjoint P)
    (hmem : ∀ i ∈ T, ∀ u ∈ P i, predecessor A u ∈ A)
    (hinj : Set.InjOn (predecessor A) ((T.biUnion P : Finset ℕ) : Set ℕ))
    (hsupp : ∀ i ∈ T, ∀ u ∈ P i, u < N)
    (hsize : ∀ i ∈ T, d ≤ ((P i).card : ℝ)) :
    (T.card : ℝ) ≤ Real.sqrt (2*N*(K+C*Real.log (2*(N : ℝ)+2)))/d := by
  have hc := uniform_packet_capacity A T P N d hdis hmem hinj hsupp hsize
  have hs := Real.sqrt_le_sqrt (count_sq_log_upper hC hA N)
  rw [Real.sqrt_sq (Nat.cast_nonneg _)] at hs
  apply (le_div_iff₀ hd).mpr
  nlinarith

lemma double_count_coarse_log (A : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (N : ℕ) (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    (count A (2*N) : ℝ)^2 ≤ 4*N*(K+4*C)*Real.log N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hN2
  have harg : 4*(N : ℝ)+2 ≤ 8*N := by linarith
  have hlog8 := Real.log_le_log (show (0 : ℝ) < 4*N+2 by positivity) harg
  rw [Real.log_mul (by norm_num) hNp.ne'] at hlog8
  have he : Real.log (8 : ℝ) = 3*Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [he] at hlog8
  have hl : Real.log (4*(N : ℝ)+2) ≤ 4*Real.log N := by linarith
  have hh := count_sq_log_upper hC hA (2*N)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  have harg' : 2*((2 : ℝ)*N)+2 = 4*N+2 := by ring
  rw [harg'] at hh
  have hbound : K+C*Real.log (4*(N : ℝ)+2) ≤ (K+4*C)*Real.log N := by
    have hc := mul_le_mul_of_nonneg_left hl hC
    have hk := mul_le_mul_of_nonneg_left hlog hK
    nlinarith
  have hc := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ 4*N by positivity)
  nlinarith only [hh,hc]

/-- Logarithmic packet costs and distinct original cells force a stricter
than square-root bound on the number of target packets in each scale. -/
theorem packet_count_div_sqrt_zero {ι : Type*} (A : Set ℕ)
    (T : ℕ → Finset ι) (P : ℕ → ι → Finset ℕ)
    (δ K C : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (hpack : ∀ᶠ N : ℕ in atTop,
      (T N : Set ι).PairwiseDisjoint (P N) ∧
      (∀ i ∈ T N, ∀ u ∈ P N i, predecessor A u ∈ A) ∧
      Set.InjOn (predecessor A) (((T N).biUnion (P N) : Finset ℕ) : Set ℕ) ∧
      (∀ i ∈ T N, ∀ u ∈ P N i, u < 2*N) ∧
      (∀ i ∈ T N, δ*Real.log N ≤ ((P N i).card : ℝ))) :
    Tendsto (fun N ↦ ((T N).card : ℝ)/Real.sqrt N) atTop (𝓝 0) := by
  have hloglim : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ ↦ Real.sqrt ((4*(K+4*C)/δ^2)/Real.log N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (hloglim.const_div_atTop (4*(K+4*C)/δ^2)).sqrt
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ by positivity)) ?_ hlim
  filter_upwards [hpack, eventually_ge_atTop 2, hloglim.eventually_ge_atTop 1] with N hp hN hlog
  obtain ⟨hdis,hmem,hinj,hsupp,hsize⟩ := hp
  have hc := uniform_packet_capacity A (T N) (P N) (2*N) (δ*Real.log N)
    hdis hmem hinj hsupp hsize
  have hcp := double_count_coarse_log A K C hK hC hA N hN hlog
  have hlp : 0 < Real.log (N : ℝ) := by linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ δ*Real.log N*(T N).card by positivity) hc 2
  have hh : δ^2*Real.log N*((T N).card : ℝ)^2 ≤ 4*N*(K+4*C) := by
    apply le_of_mul_le_mul_right (a := Real.log (N : ℝ)) _ hlp
    nlinarith only [hs,hcp]
  have hsq : (((T N).card : ℝ)/Real.sqrt N)^2 ≤ (4*(K+4*C)/δ^2)/Real.log N := by
    rw [div_pow, Real.sq_sqrt hNp.le]
    apply (div_le_div_iff₀ hNp hlp).mpr
    have hδsq : 0 < δ^2 := sq_pos_of_pos hδ
    have hb : ((T N).card : ℝ)^2*Real.log N ≤ 4*N*(K+4*C)/δ^2 := by
      apply (le_div_iff₀ hδsq).mpr
      nlinarith only [hh]
    convert hb using 1 <;> ring
  have hh' := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (show (0 : ℝ) ≤ ((T N).card : ℝ)/Real.sqrt N by positivity)] at hh'

end Erdos66PredecessorPacketCapacity
