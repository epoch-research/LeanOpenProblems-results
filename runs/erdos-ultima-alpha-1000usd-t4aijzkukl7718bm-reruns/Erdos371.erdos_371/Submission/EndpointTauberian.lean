import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! An endpoint-averaged signed estimate would suffice for Erdős 371.
The required arithmetic estimate is a hypothesis, not asserted here. -/

namespace Erdos371EndpointTauberian

open Finset Filter
open scoped Topology

noncomputable def accumulated (D : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, D n

lemma finite_tauberian_bound (D : ℕ → ℝ)
    (hD : ∀ n k, |D (n+k)-D n| ≤ k) (N H : ℕ) :
    (H:ℝ)*|D N| ≤ |accumulated D (N+H)|+|accumulated D N|+(H:ℝ)^2 := by
  have he : accumulated D (N+H)=accumulated D N+∑ k ∈ range H, D (N+k) := by
    exact sum_range_add D N H
  have herr : |(H:ℝ)*D N-∑ k ∈ range H, D (N+k)| ≤ (H:ℝ)^2 := by
    have hs : (H:ℝ)*D N-∑ k ∈ range H, D (N+k) =
        ∑ k ∈ range H, (D N-D (N+k)) := by simp [sum_sub_distrib]
    rw [hs]
    calc
      _ ≤ ∑ k ∈ range H, |D N-D (N+k)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ range H, (H:ℝ) := by
        apply sum_le_sum
        intro k hk
        rw [abs_sub_comm]
        exact (hD N k).trans (Nat.cast_le.mpr (mem_range.mp hk).le)
      _ = _ := by simp [pow_two]
  have hs : |∑ k ∈ range H, D (N+k)| ≤
      |accumulated D (N+H)|+|accumulated D N| := by
    have hh := abs_sub (accumulated D (N+H)) (accumulated D N)
    rw [he] at hh ⊢
    simpa using hh
  have ht := abs_add_le ((H:ℝ)*D N-∑ k ∈ range H, D (N+k))
    (∑ k ∈ range H, D (N+k))
  simp only [sub_add_cancel, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) H)] at ht
  linarith

/-- For a sequence with unit-bounded increments, a vanishing quadratic-scale
    average of its partial sums implies the vanishing linear-scale sequence. -/
theorem tendsto_of_accumulated (D : ℕ → ℝ)
    (hD : ∀ n k, |D (n+k)-D n| ≤ k)
    (hA : Tendsto (fun N : ℕ => accumulated D N/(N:ℝ)^2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => D N/N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hKbig⟩ := exists_nat_gt (4/ε)
  have hKr : (0:ℝ)<K := (div_pos (by norm_num) hε).trans hKbig
  have hK : 0<K := Nat.cast_pos.mp hKr
  have hεK : 4<ε*(K:ℝ) := by
    have hh := (div_lt_iff₀ hε).mp hKbig
    nlinarith
  let δ : ℝ := 1/(100*(K:ℝ)^2)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨N₀,hN₀⟩ := Metric.tendsto_atTop.mp hA δ hδ
  refine ⟨max N₀ (2*K),?_⟩
  intro N hN
  have hNN₀ : N₀≤N := (le_max_left _ _).trans hN
  have hlarge : 2*K≤N := (le_max_right _ _).trans hN
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  let H := N/K
  have hH : 0<H := Nat.div_pos (by omega) hK
  have hh : (0:ℝ)<H := Nat.cast_pos.mpr hH
  have hxle : (K:ℝ)*(H:ℝ)≤N := by
    exact_mod_cast (Nat.mul_div_le N K)
  have hxlo : (N:ℝ)≤2*(K:ℝ)*(H:ℝ) := by
    have hb : N<K*(H+1) := Nat.lt_mul_div_succ N hK
    have hH1 : 1≤H := hH
    have hc : K*(H+1)≤2*K*H := by nlinarith
    exact_mod_cast hb.le.trans hc
  have hHN : H≤N := Nat.div_le_self N K
  have h2N : (N+H:ℕ)≤2*N := by omega
  have hb (M : ℕ) (hM : N≤M) : |accumulated D M| < δ*(M:ℝ)^2 := by
    have hMp : (0:ℝ)<M := hn.trans_le (Nat.cast_le.mpr hM)
    have ht := hN₀ M (hNN₀.trans hM)
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_nonneg (sq_nonneg (M:ℝ))] at ht
    exact (div_lt_iff₀ (sq_pos_of_pos hMp)).mp ht
  have hb0 := hb N le_rfl
  have hb1 := hb (N+H) (by omega)
  have hs : ((N+H:ℕ):ℝ)^2 ≤ 4*(N:ℝ)^2 := by
    have hc : ((N+H:ℕ):ℝ)≤2*(N:ℝ) := by exact_mod_cast h2N
    nlinarith [Nat.cast_nonneg (α := ℝ) (N+H)]
  have hfinite := finite_tauberian_bound D hD N H
  have hsmall : (H:ℝ)*|D N| ≤ 5*δ*(N:ℝ)^2+(H:ℝ)^2 := by
    have hds := mul_le_mul_of_nonneg_left hs hδ.le
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (K:ℝ))
  have hδeq : (K:ℝ)^2*(5*δ)=1/20 := by
    dsimp [δ]
    field_simp
    ring
  have hmain : ((K:ℝ)*(H:ℝ))*((K:ℝ)*|D N|) ≤
      (N:ℝ)^2/20+((K:ℝ)*(H:ℝ))^2 := by
    calc
      _ = (K:ℝ)^2*((H:ℝ)*|D N|) := by ring
      _ ≤ (K:ℝ)^2*(5*δ*(N:ℝ)^2+(H:ℝ)^2) := hscaled
      _ = _ := by rw [mul_add,← mul_assoc,hδeq]; ring
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hn]
  apply (div_lt_iff₀ hn).mpr
  by_contra hbad
  have hbad' : ε*(N:ℝ)≤|D N| := le_of_not_gt hbad
  have hbig : 4*(N:ℝ)<(K:ℝ)*|D N| := by
    have h1 := mul_lt_mul_of_pos_right hεK hn
    have h2 := mul_le_mul_of_nonneg_left hbad' hKr.le
    nlinarith
  have hxpos : 0<(K:ℝ)*(H:ℝ) := mul_pos hKr hh
  have hprod := mul_lt_mul_of_pos_left hbig hxpos
  have hsq : ((K:ℝ)*(H:ℝ))^2≤(N:ℝ)^2 := sq_le_sq₀ hxpos.le hn.le |>.mpr hxle
  have hlow := mul_le_mul_of_nonneg_right hxlo hn.le
  nlinarith

lemma accumulated_tendsto (D : ℕ → ℝ) (h0 : D 0=0)
    (h : Tendsto (fun N : ℕ => D N/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => accumulated D N/(N:ℝ)^2) atTop (𝓝 0) := by
  have hu := ((tendsto_zero_iff_abs_tendsto_zero _).mp h).cesaro
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
    have hp (n : ℕ) (hnN : n∈range N) : |D n|≤(N:ℝ)*|D n/n| := by
      by_cases hn0 : n=0
      · simp [hn0,h0]
      · have hnr : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
        rw [abs_div,abs_of_pos hnr]
        have hh := mul_le_mul_of_nonneg_right
          (Nat.cast_le (α := ℝ).mpr (mem_range.mp hnN).le)
          (div_nonneg (abs_nonneg (D n)) hnr.le)
        have he : (n:ℝ)*(|D n|/n)=|D n| := by field_simp
        rwa [he] at hh
    have hs : |accumulated D N|≤(N:ℝ)*∑ n ∈ range N, |D n/n| := by
      unfold accumulated
      exact (abs_sum_le_sum_abs _ _).trans (by
        rw [mul_sum]
        exact sum_le_sum hp)
    change |accumulated D N/(N:ℝ)^2| ≤ (N:ℝ)⁻¹*∑ n ∈ range N, |D n/n|
    rw [abs_div,abs_of_nonneg (sq_nonneg (N:ℝ))]
    calc
      _ ≤ ((N:ℝ)*∑ n ∈ range N, |D n/n|)/(N:ℝ)^2 :=
        div_le_div_of_nonneg_right hs (sq_nonneg _)
      _ = _ := by field_simp

open Erdos371PrimeDiscrepancy

lemma total_increments (n k : ℕ) : |(total (n+k):ℝ)-(total n:ℝ)|≤k := by
  have he : total (n+k)=total n+∑ j ∈ range k, sign (n+j) :=
    sum_range_add sign n k
  rw [he]
  push_cast
  simp only [add_sub_cancel_left]
  calc
    _ ≤ ∑ j ∈ range k, |(sign (n+j):ℝ)| := abs_sum_le_sum_abs _ _
    _ = _ := by
      have hs (j : ℕ) : |(sign (n+j):ℝ)|=1 := by
        unfold sign
        split_ifs <;> norm_num
      simp [hs]

/-- The averaged signed-count estimate remains an explicit hypothesis. -/
theorem density_half_of_averaged_total
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (total n:ℝ))/(N:ℝ)^2) atTop (𝓝 0)) :
    {n | P n<P (n+1)}.HasDensity (1/2) := by
  apply density_half_iff_total_mean_zero.mpr
  exact tendsto_of_accumulated (fun n => (total n:ℝ)) total_increments h

/-- Endpoint averaging is an exact reformulation, not a proved cancellation
    theorem for the largest-prime-factor comparison. -/
theorem density_half_iff_averaged_total :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, (total n:ℝ))/(N:ℝ)^2) atTop (𝓝 0) := by
  constructor
  · intro h
    exact accumulated_tendsto (fun n => (total n:ℝ)) (by simp [total])
      (density_half_iff_total_mean_zero.mp h)
  · exact density_half_of_averaged_total

end Erdos371EndpointTauberian

#print axioms Erdos371EndpointTauberian.finite_tauberian_bound
#print axioms Erdos371EndpointTauberian.tendsto_of_accumulated
#print axioms Erdos371EndpointTauberian.density_half_of_averaged_total

#print axioms Erdos371EndpointTauberian.density_half_iff_averaged_total
