import Submission.AbelSquarePrefixExplore

/-! A logarithmic-square prefix estimate controls the natural density of
fixed-tolerance bad targets. It gives no power-saving exceptional count. -/
namespace Erdos66SquarePrefixDensity
open Erdos66AbelSquarePrefix Erdos66Counting
open scoped Classical Topology
open Filter
set_option maxHeartbeats 2400000

noncomputable def logBad (d : ℕ → ℝ) (ε : ℝ) : Set ℕ :=
  {n | ε*Real.log ((n : ℝ)+2) ≤ |d n|}

lemma large_index_square (K N n : ℕ) (hK : 0<K) (hN : K*(K+1) ≤ N)
    (hn : N/K ≤ n) : N ≤ (n+2)^2 := by
  have hq : K+1 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by nlinarith [hN])
  have hr := Nat.lt_mul_div_succ N hK
  have hh : N<K*(n+1) := hr.trans_le (Nat.mul_le_mul_left K (Nat.add_le_add_right hn 1))
  nlinarith

lemma log_bad_density_bound (d : ℕ → ℝ) {ε : ℝ} (hε : 0<ε)
    (K N : ℕ) (hK : 0<K) (hN : K*(K+1) ≤ N) (hN2 : 2 ≤ N) :
    (count (logBad d ε) N : ℝ)/N ≤ 1/(K : ℝ)+(4/ε^2)*
      ((∑ n∈Finset.range N, d n^2)/((N : ℝ)*(Real.log N)^2)) := by
  let T := (cutoff (logBad d ε) N).filter (fun n ↦ N/K ≤ n)
  have hcount : count (logBad d ε) N ≤ N/K+T.card := by
    have hsub : cutoff (logBad d ε) N ⊆ Finset.range (N/K) ∪ T := by
      intro n hn
      by_cases hm : N/K ≤ n
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,hm⟩)
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    exact (Finset.card_le_card hsub).trans (by
      simpa only [Finset.card_range] using Finset.card_union_le (Finset.range (N/K)) T)
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hKp : (0 : ℝ)<K := by exact_mod_cast hK
  have hL : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hpoint (n : ℕ) (hn : n∈T) : ε^2*(Real.log N)^2 ≤ 4*(d n)^2 := by
    obtain ⟨hnE,hnK⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnN,hbad⟩ := mem_cutoff.mp hnE
    change ε*Real.log ((n : ℝ)+2) ≤ |d n| at hbad
    have hnlog : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have harg : (N : ℝ) ≤ ((n : ℝ)+2)^2 := by
      exact_mod_cast large_index_square K N n hK hN hnK
    have hlogs := Real.log_le_log hNp harg
    rw [Real.log_pow] at hlogs
    norm_num only [Nat.cast_ofNat] at hlogs
    have hsq := pow_le_pow_left₀ (mul_nonneg hε.le hnlog.le) hbad 2
    rw [sq_abs,mul_pow] at hsq
    have hcomp : (Real.log N)^2 ≤ 4*(Real.log ((n : ℝ)+2))^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcomp (sq_nonneg ε)]
  have hmass : (T.card : ℝ)*(ε^2*(Real.log N)^2) ≤
      4*(∑ n∈Finset.range N, d n^2) := by
    calc
      _ = ∑ _n∈T, ε^2*(Real.log N)^2 := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ n∈T, 4*(d n)^2 := Finset.sum_le_sum hpoint
      _ = 4*(∑ n∈T, d n^2) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          exact Finset.mem_range.mpr (mem_cutoff.mp (Finset.mem_filter.mp hn).1).1)
          (fun _ _ _ ↦ sq_nonneg _)) (by norm_num)
  have hq : (N/K : ℕ) ≤ N := Nat.div_le_self _ _
  have hqR : ((N/K : ℕ) : ℝ) ≤ (N : ℝ)/K := by
    apply (le_div_iff₀ hKp).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.mul_div_le N K)
  have hcR : (count (logBad d ε) N : ℝ) ≤ ((N/K : ℕ) : ℝ)+(T.card : ℝ) := by exact_mod_cast hcount
  have hmass' := (le_div_iff₀ (mul_pos (sq_pos_of_pos hε) (sq_pos_of_pos hL))).mpr hmass
  have htotal : (count (logBad d ε) N : ℝ) ≤ (N : ℝ)/K+
      4*(∑ n∈Finset.range N, d n^2)/(ε^2*(Real.log N)^2) := by linarith
  have hh := div_le_div_of_nonneg_right htotal hNp.le
  convert hh using 1 <;> field_simp <;> ring

/-- Every fixed relative-error exceptional set has density zero. This is
only o(N), not a fixed-power saving and not a repair-cost estimate. -/
theorem logBad_density_zero (d : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ ↦ (∑ n∈Finset.range N, d n^2)/
      ((N : ℝ)*(Real.log N)^2)) atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun N : ℕ ↦ (count (logBad d ε) N : ℝ)/N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N ↦ ha.trans_le (by positivity))
  · intro δ hδ
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt (half_pos hδ)
    let K := k+1
    have hK : 0<K := by dsimp [K]; omega
    have hk' : 1/(K : ℝ)<δ/2 := by simpa only [K,Nat.cast_add,Nat.cast_one] using hk
    have hh := h.const_mul (4/ε^2)
    simp only [mul_zero] at hh
    filter_upwards [hh.eventually_lt_const (half_pos hδ),eventually_ge_atTop (K*(K+1)),
      eventually_ge_atTop 2] with N hsmall hN hN2
    exact (log_bad_density_bound d hε K N hK hN hN2).trans_lt (by linarith)

lemma density_zero_of_eventual_subset (E F : Set ℕ)
    (hE : Tendsto (fun N : ℕ ↦ (count E N : ℝ)/N) atTop (𝓝 0))
    (hsub : ∀ᶠ n : ℕ in atTop, n∈F → n∈E) :
    Tendsto (fun N : ℕ ↦ (count F N : ℝ)/N) atTop (𝓝 0) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp hsub
  have hlim := ((tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (M : ℝ)).add hE
  simp only [add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun _ ↦ by positivity)
  · apply Eventually.of_forall
    intro N
    have hs : cutoff F N ⊆ Finset.range M ∪ cutoff E N := by
      intro n hn
      obtain ⟨hnN,hnF⟩ := mem_cutoff.mp hn
      by_cases hmn : M ≤ n
      · exact Finset.mem_union_right _ (mem_cutoff.mpr ⟨hnN,hM n hmn hnF⟩)
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    have hc : (count F N : ℝ) ≤ M+(count E N : ℝ) := by
      exact_mod_cast (by simpa only [Finset.card_range] using hh)
    simpa only [add_div] using div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)

end Erdos66SquarePrefixDensity
