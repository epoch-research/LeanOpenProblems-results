import Submission.SyndeticNaturalHalf

/-! For every fixed positive tolerance, a positive lower natural density of
endpoints have ordinary largest-prime rise proportion near one half. This is
not convergence of the proportions at every endpoint. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma rising_proportion_endpoint_bound (M K : ℕ) (hM : 0 < M) (hMK : M ≤ K) :
    |(risingCount K : ℝ)/K-(risingCount M : ℝ)/M| ≤ 2*(K-M : ℕ)/K := by
  let f (n : ℕ) : ℝ := if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then 1 else 0
  have he (N : ℕ) : prefixMean N f = (risingCount N : ℝ)/N := by
    simp [prefixMean,f,risingCount,sum_boole]
  have h := prefixMean_endpoint_bound M K hM hMK f 1
    (fun n _ => by dsimp [f]; split_ifs <;> norm_num)
  simpa only [he,mul_one] using h

lemma rising_proportion_short_interval (ε : ℝ) (hε : 0 < ε) (L M K : ℕ)
    (hL : 0 < L) (hLε : 4/ε < (L : ℝ)) (hM : 0 < M)
    (hnear : |(risingCount M : ℝ)/M-1/2| < ε/2)
    (hK : K ∈ Icc M (M+M/L)) : |(risingCount K : ℝ)/K-1/2| < ε := by
  obtain ⟨hMK,hKM⟩ := mem_Icc.mp hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hM.trans_le hMK
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hmult : (K-M)*L ≤ K := calc
    _ ≤ (M/L)*L := Nat.mul_le_mul_right L (by omega)
    _ ≤ M := Nat.div_mul_le_self M L
    _ ≤ K := hMK
  have herr : 2*(K-M : ℕ)/(K : ℝ) ≤ 2/(L : ℝ) := by
    apply (div_le_div_iff₀ hKr hLr).mpr
    have hh : ((K-M : ℕ) : ℝ)*L ≤ K := by exact_mod_cast hmult
    nlinarith
  have heps : 2/(L : ℝ) < ε/2 := by
    apply (div_lt_iff₀ hLr).mpr
    have hh := (div_lt_iff₀ hε).mp hLε
    nlinarith
  have htri := abs_sub_le ((risingCount K : ℝ)/K) ((risingCount M : ℝ)/M) (1/2)
  have hb := rising_proportion_endpoint_bound M K hM hMK
  linarith

noncomputable def nearHalfEndpointCount (ε : ℝ) (X : ℕ) : ℕ :=
  ((range X).filter fun M => |(risingCount M : ℝ)/M-1/2| < ε).card

/-- A positive proportion of all endpoints, not merely a diverging
subsequence, lies within each fixed tolerance of one half. -/
theorem nearHalfEndpointCount_eventually_positive_proportion (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop, δ ≤ (nearHalfEndpointCount ε X : ℝ)/X := by
  obtain ⟨L,hLε⟩ := exists_nat_gt (4/ε)
  have hLr : (0 : ℝ) < L := lt_trans (div_pos (by norm_num) hε) hLε
  have hL : 0 < L := by exact_mod_cast hLr
  obtain ⟨C,hC,T,hT,hnear⟩ := largest_prime_rises_syndetic_near_half (ε/2) (half_pos hε)
  let D : ℕ := 4*C
  have hD : 0 < D := by dsimp [D]; omega
  refine ⟨1/((2*D*L : ℕ) : ℝ),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (D*T)] with X hX
  let Q := X/D
  have hQT : T ≤ Q := (Nat.le_div_iff_mul_le hD).mpr (by simpa only [mul_comm] using hX)
  have hQ : 0 < Q := hT.trans hQT
  have hX0 : 0 < X := by
    have hh : 0 < D*T := Nat.mul_pos hD hT
    exact hh.trans_le hX
  obtain ⟨M,hQM,hMC,hMnear⟩ := hnear Q hQT
  have hM : 0 < M := hQ.trans_le hQM
  let S := Icc M (M+M/L)
  have hS : S ⊆ (range X).filter (fun K => |(risingCount K : ℝ)/K-1/2| < ε) := by
    intro K hK
    refine mem_filter.mpr ⟨mem_range.mpr ?_,rising_proportion_short_interval ε hε L M K hL hLε hM hMnear hK⟩
    have hKM := (mem_Icc.mp hK).2
    have hdiv : M/L ≤ M := Nat.div_le_self _ _
    have hDQ : D*Q ≤ X := Nat.mul_div_le X D
    have hCQ : 0 < C*Q := Nat.mul_pos (by omega) hQ
    dsimp [D] at hDQ
    nlinarith
  have hcard : M/L+1 ≤ nearHalfEndpointCount ε X := by
    have hc := card_le_card hS
    simpa only [S,Nat.card_Icc,Nat.add_assoc,Nat.add_sub_cancel_left,nearHalfEndpointCount] using hc
  have hXQ : X < 2*D*Q := calc
    X < D*(Q+1) := Nat.lt_mul_div_succ X hD
    _ ≤ D*(2*Q) := Nat.mul_le_mul_left D (by omega)
    _ = _ := by ring
  have hML : M < L*(M/L+1) := Nat.lt_mul_div_succ M hL
  have hbound : X ≤ (2*D*L)*nearHalfEndpointCount ε X := by
    calc
      X ≤ 2*D*Q := hXQ.le
      _ ≤ 2*D*M := Nat.mul_le_mul_left (2*D) hQM
      _ ≤ 2*D*(L*(M/L+1)) := Nat.mul_le_mul_left (2*D) hML.le
      _ = (2*D*L)*(M/L+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left (2*D*L) hcard
  have hDr : (0 : ℝ) < (2*D*L : ℕ) := by positivity
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  apply (div_le_div_iff₀ hDr hXr).mpr
  have hh : (X : ℝ) ≤ (2*D*L : ℕ)*(nearHalfEndpointCount ε X : ℝ) := by exact_mod_cast hbound
  nlinarith

lemma nearHalfEndpoint_partialDensity (ε : ℝ) (X : ℕ) :
    {M : ℕ | |(risingCount M : ℝ)/M-1/2| < ε}.partialDensity Set.univ X =
      (nearHalfEndpointCount ε X : ℝ)/X := by
  have he : {M : ℕ | |(risingCount M : ℝ)/M-1/2| < ε} ∩ Set.Iio X =
      ((range X).filter fun M => |(risingCount M : ℝ)/M-1/2| < ε : Set ℕ) := by
    ext M
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_Iio,mem_coe,mem_filter,mem_range]
    exact and_comm
  simp only [Set.partialDensity,Set.inter_univ,he,Set.ncard_coe_finset,
    Set.univ_inter,Nat.ncard_Iio,nearHalfEndpointCount]

/-- This is a positive lower density of GOOD ENDPOINTS, not the conjectured
density of the original rising set. Its lower bound may depend on ε. -/
theorem near_half_endpoints_positive_lowerDensity (ε : ℝ) (hε : 0 < ε) :
    0 < {M : ℕ | |(risingCount M : ℝ)/M-1/2| < ε}.lowerDensity := by
  obtain ⟨δ,hδ,he⟩ := nearHalfEndpointCount_eventually_positive_proportion ε hε
  let S : Set ℕ := {M : ℕ | |(risingCount M : ℝ)/M-1/2| < ε}
  have hb : IsBoundedUnder (· ≤ ·) atTop (S.partialDensity Set.univ) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun X => Set.partialDensity_le_one S Set.univ X)
  have hd : δ ≤ S.lowerDensity := by
    apply le_liminf_of_le hb.isCoboundedUnder_ge
    filter_upwards [he] with X hX
    simpa only [S,nearHalfEndpoint_partialDensity] using hX
  exact hδ.trans_le hd

#print axioms nearHalfEndpointCount_eventually_positive_proportion
#print axioms near_half_endpoints_positive_lowerDensity
end Erdos371
