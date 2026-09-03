import Submission.RoughRadicalComplement
import Submission.AbsoluteKernelObstruction

/-! The unit complementary index is present with absolute weight one on
almost every input, even for the slowly superlinear cutoffs. Thus the short
complementary index range does not give sparsity or an absolute-value proof.
No signed cancellation, or disproof of Erdős 371, is asserted. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma goodRoughPair_product_sq_large (B K N n : ℕ)
    (hn : n ∈ goodRoughPairSet B K N) :
    (N+1)^3 < (roughPrimePart B (n+1)*roughPrimePart B (n+2))^2 := by
  obtain ⟨_,h1,h2⟩ := mem_filter.mp hn
  have ha : (N+1)^3 < (roughPrimePart B (n+1))^4 := by
    exact Nat.lt_of_not_ge (fun h => h1 (Or.inl h))
  have hb : (N+1)^3 < (roughPrimePart B (n+2))^4 := by
    exact Nat.lt_of_not_ge (fun h => h2 (Or.inl h))
  rcases le_total (roughPrimePart B (n+1)) (roughPrimePart B (n+2)) with h | h
  · have hm := Nat.mul_le_mul_left (roughPrimePart B (n+1)) h
    have hs := Nat.pow_le_pow_left hm 2
    nlinarith
  · have hm := Nat.mul_le_mul_right (roughPrimePart B (n+2)) h
    have hs := Nat.pow_le_pow_left hm 2
    nlinarith

lemma goodRoughPair_product_dvd_radical (B K N n : ℕ) (hN : 2≤N)
    (hn : n ∈ goodRoughPairSet B K N) :
    roughPrimePart B (n+1)*roughPrimePart B (n+2) ∣ roughRadical B ((n+1)*(n+2)) := by
  obtain ⟨hnN,h1,h2⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  obtain ⟨_,hsa,haB,_,_⟩ := good_rough_part_data B K N (n+1) hN (by omega) (by omega) h1
  obtain ⟨_,hsb,hbB,_,_⟩ := good_rough_part_data B K N (n+2) hN (by omega) (by omega) h2
  have hda := roughPrimePart_dvd B (n+1) (by omega)
  have hdb := roughPrimePart_dvd B (n+2) (by omega)
  have ha := squarefree_rough_dvd_radical B ((n+1)*(n+2)) _ (by positivity)
    (hda.trans (dvd_mul_right _ _)) hsa haB
  have hb := squarefree_rough_dvd_radical B ((n+1)*(n+2)) _ (by positivity)
    (hdb.trans (dvd_mul_left _ _)) hsb hbB
  exact (divisor_pair_coprime (n+1) _ _ hda hdb).mul_dvd_of_dvd_of_dvd ha hb

lemma goodRoughPair_radical_large (B D K N n : ℕ) (hN : 2≤N)
    (hD : D^2≤(N+1)^3) (hn : n ∈ goodRoughPairSet B K N) :
    D < roughRadical B ((n+1)*(n+2)) := by
  have hp := goodRoughPair_product_sq_large B K N n hn
  have hle := Nat.le_of_dvd (roughRadical_pos B ((n+1)*(n+2)))
    (goodRoughPair_product_dvd_radical B K N n hN hn)
  have hd : D < roughPrimePart B (n+1)*roughPrimePart B (n+2) := by
    by_contra h
    have hs := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 2
    omega
  exact hd.trans_le hle

/-- This is exactly the e=1 summand, including the outer parity factor,
after complementing a rough-divisor tail at D. -/
noncomputable def roughComplementUnit (B D n : ℕ) : ℝ :=
  if D < roughRadical B (n*(n+1)) then
    (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
      divisorSideColour n (roughRadical B (n*(n+1)))
  else 0

lemma roughComplementUnit_eq (B H N n : ℕ) :
    roughComplementUnit B (H*N) n =
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        (if 1∣roughRadical B (n*(n+1)) ∧ (H*N)*1<roughRadical B (n*(n+1)) then
          (ArithmeticFunction.moebius 1 : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/1)
        else 0) := by
  simp only [one_dvd,true_and,mul_one,ArithmeticFunction.moebius_apply_one,
    Int.cast_one,one_mul,Nat.div_one,roughComplementUnit]
  split_ifs <;> simp

lemma roughComplementUnit_norm (B D n : ℕ) :
    ‖roughComplementUnit B D n‖ = if D<roughRadical B (n*(n+1)) then 1 else 0 := by
  have hm : ‖(ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)‖=1 := by
    rw [Real.norm_eq_abs,← Int.cast_abs,ArithmeticFunction.abs_moebius,
      if_pos (roughRadical_squarefree B _),Int.cast_one]
  have hc (d : ℕ) : ‖divisorSideColour n d‖=1 := by
    unfold divisorSideColour
    split_ifs <;> norm_num
  unfold roughComplementUnit
  split_ifs <;> simp [norm_mul,hm,hc]

lemma roughComplementUnit_norm_sum_le (B D N : ℕ) :
    (∑ n ∈ range N, ‖roughComplementUnit B D (n+1)‖) ≤ N := by
  calc
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum fun n _ => by
      rw [roughComplementUnit_norm]; split_ifs <;> norm_num
    _ = _ := by simp

lemma roughComplementUnit_norm_sum_lower (B D K N : ℕ) (hN : 2≤N)
    (hD : D^2≤(N+1)^3) :
    ((goodRoughPairSet B K N).card : ℝ) ≤ ∑ n ∈ range N, ‖roughComplementUnit B D (n+1)‖ := by
  calc
    _ = ∑ n ∈ goodRoughPairSet B K N, ‖roughComplementUnit B D (n+1)‖ := by
      have he (n : ℕ) (hn : n ∈ goodRoughPairSet B K N) : ‖roughComplementUnit B D (n+1)‖=1 := by
        rw [roughComplementUnit_norm]
        exact if_pos (goodRoughPair_radical_large B D K N n hN hD hn)
      rw [sum_congr rfl he]
      simp
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)

/-- A subpower cutoff is eventually below every fixed positive power, here
stated with natural squares for the superlinear multiplier application. -/
lemma subpower_cutoff_add_one_sq_eventually_le (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, (B N+1)^2≤N := by
  filter_upwards [hB.eventually_lt_const (by norm_num : (0 : ℝ)<1/2),
    eventually_gt_atTop (1 : ℕ)] with N hb hn
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast hn)
  have hl : Real.log ((B N+1 : ℝ)^2) ≤ Real.log N := by
    rw [Real.log_pow]
    norm_num
    have := (div_lt_iff₀ hlog).mp hb
    linarith
  have hpow := (Real.log_le_log_iff (by positivity : (0 : ℝ)<(B N+1 : ℝ)^2)
    (by exact_mod_cast (show 0<N by omega))).mp hl
  exact_mod_cast hpow

/-- The absolute average of the unit complementary summand tends to ONE,
not zero. This also applies to the cutoffs chosen by the superlinear diagonal. -/
theorem roughComplementUnit_absolute_average_one (B H : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N≤B N+1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖roughComplementUnit (B N) (H N*N) (n+1)‖)/N)
      atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (goodRoughPairSet_quantile_density_one B hBatTop hB) tendsto_const_nhds
  · filter_upwards [hHB,subpower_cutoff_add_one_sq_eventually_le B hB,
      eventually_ge_atTop (2 : ℕ)] with N hh hb hn
    have hHsq : (H N)^2≤N := (Nat.pow_le_pow_left hh 2).trans hb
    have hd : (H N*N)^2≤(N+1)^3 := by nlinarith [Nat.mul_le_mul_right (N^2) hHsq]
    exact div_le_div_of_nonneg_right
      (roughComplementUnit_norm_sum_lower (B N) (H N*N) (harmonicCofactorCutoff (B N)) N hn hd)
      (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hn
    exact (div_le_one (by exact_mod_cast hn : (0 : ℝ)<N)).mpr
      (roughComplementUnit_norm_sum_le (B N) (H N*N) N)

noncomputable def complementedRoughAbsoluteMass (B H N : ℕ) : ℝ :=
  ∑ n ∈ range N, ∑ e ∈ Icc 1 ((N+1)/H),
    ‖(ArithmeticFunction.moebius (roughRadical B ((n+1)*(n+2))) : ℝ)*
      (if e∣roughRadical B ((n+1)*(n+2)) ∧ (H*N)*e<roughRadical B ((n+1)*(n+2)) then
        (ArithmeticFunction.moebius e : ℝ)*
          divisorSideColour (n+1) (roughRadical B ((n+1)*(n+2))/e)
      else 0)‖

lemma roughComplementUnit_norm_le_absolute_mass (B H N : ℕ) (hH : 0<H) (hHN : H≤N+1) :
    (∑ n ∈ range N, ‖roughComplementUnit B (H*N) (n+1)‖) ≤ complementedRoughAbsoluteMass B H N := by
  have hmem : 1 ∈ Icc 1 ((N+1)/H) := mem_Icc.mpr ⟨le_rfl,
    (Nat.le_div_iff_mul_le hH).mpr (by simpa only [one_mul] using hHN)⟩
  unfold complementedRoughAbsoluteMass
  apply sum_le_sum
  intro n hn
  rw [roughComplementUnit_eq]
  simp only [Nat.add_assoc,Nat.reduceAdd]
  apply single_le_sum (s := Icc 1 ((N+1)/H)) (a := 1)
    (f := fun e : ℕ =>
      ‖(ArithmeticFunction.moebius (roughRadical B ((n+1)*(n+2))) : ℝ)*
        (if e∣roughRadical B ((n+1)*(n+2)) ∧ (H*N)*e<roughRadical B ((n+1)*(n+2)) then
          (ArithmeticFunction.moebius e : ℝ)*
            divisorSideColour (n+1) (roughRadical B ((n+1)*(n+2))/e)
        else 0)‖)
  · intro e he
    exact norm_nonneg _
  · exact hmem

/-- Taking the absolute values of complementary summands still leaves at
least linear mass. The fact that their indices lie in o(N) does not help. -/
theorem complementedRoughAbsoluteMass_eventually_lower (B H : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop) (hHatTop : Tendsto H atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N≤B N+1) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, 1-ε≤complementedRoughAbsoluteMass (B N) (H N) N/N := by
  have ht := roughComplementUnit_absolute_average_one B H hBatTop hB hHB
  filter_upwards [(tendsto_order.mp ht).1 (1-ε) (by linarith),hHB,
    hHatTop.eventually_gt_atTop 0,subpower_cutoff_add_one_sq_eventually_le B hB] with N hl hh hH hb
  have hHN : H N≤N+1 := by nlinarith
  exact hl.le.trans (div_le_div_of_nonneg_right
    (roughComplementUnit_norm_le_absolute_mass (B N) (H N) N hH hHN) (Nat.cast_nonneg N))

theorem complementedRoughAbsoluteMass_not_tendsto_zero (B H : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop) (hHatTop : Tendsto H atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N≤B N+1) :
    ¬Tendsto (fun N : ℕ => complementedRoughAbsoluteMass (B N) (H N) N/N) atTop (𝓝 0) := by
  intro h
  have hl := complementedRoughAbsoluteMass_eventually_lower B H hBatTop hHatTop hB hHB
    (1/2) (by norm_num)
  have hu := h.eventually_lt_const (by norm_num : (0 : ℝ)<1/2)
  obtain ⟨N,hN,hN'⟩ := (hl.and hu).exists
  linarith

#print axioms goodRoughPair_radical_large
#print axioms roughComplementUnit_absolute_average_one
#print axioms complementedRoughAbsoluteMass_not_tendsto_zero
end Erdos371
