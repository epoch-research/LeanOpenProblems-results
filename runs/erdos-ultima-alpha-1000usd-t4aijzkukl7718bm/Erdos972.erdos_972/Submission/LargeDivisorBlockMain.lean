import Submission.ExactLargeDivisorFirstMoment
import Submission.ExplicitLargeDivisorBlock

/-! Evaluation of the explicit large-block first-moment center. The
prime-pair conjecture is not settled by a first-moment calculation. -/
namespace Erdos972LargeDivisorBlockMain

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972ExactLargeDivisorFirstMoment Erdos972ExplicitLargeDivisorBlock
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972PolynomialRowScales Erdos972ChebyshevPNT Erdos972LargeDivisorBlockMoment

set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] root64

lemma reciprocal_sum_eq_harmonic (K : ℕ) :
    (∑ k ∈ Ioc 0 K, 1/(k:ℝ)) = (harmonic K:ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rfl

lemma reciprocal_sum_interval {L K : ℕ} (hLK : L ≤ K) :
    (∑ k ∈ Ioc L K, 1/(k:ℝ)) = (harmonic K:ℝ)-harmonic L := by
  have hh := sum_Ioc_consecutive (fun k => 1/(k:ℝ)) (Nat.zero_le L) hLK
  rw [reciprocal_sum_eq_harmonic, reciprocal_sum_eq_harmonic] at hh
  linarith only [hh]

lemma clipped_harmonic_sum {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : ⌊x⌋₊ ≤ K) :
    (∑ k ∈ Ioc 0 K, min 1 ((k:ℝ)/x)/(k:ℝ)) =
      (⌊x⌋₊:ℝ)/x+(harmonic K:ℝ)-harmonic ⌊x⌋₊ := by
  have hh := sum_Ioc_consecutive (fun k => min 1 ((k:ℝ)/x)/(k:ℝ))
    (Nat.zero_le ⌊x⌋₊) hK
  have hlow : (∑ k ∈ Ioc 0 ⌊x⌋₊, min 1 ((k:ℝ)/x)/(k:ℝ)) = (⌊x⌋₊:ℝ)/x := by
    calc
      _ = ∑ k ∈ Ioc 0 ⌊x⌋₊, 1/x := by
        apply sum_congr rfl
        intro k hk
        have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (mem_Ioc.mp hk).1
        have hkx : (k:ℝ) ≤ x := (Nat.cast_le.mpr (mem_Ioc.mp hk).2).trans (Nat.floor_le hx.le)
        rw [min_eq_right ((div_le_one hx).mpr hkx)]
        field_simp
      _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring
  have hhigh : (∑ k ∈ Ioc ⌊x⌋₊ K, min 1 ((k:ℝ)/x)/(k:ℝ)) =
      (harmonic K:ℝ)-harmonic ⌊x⌋₊ := by
    rw [← reciprocal_sum_interval hK]
    apply sum_congr rfl
    intro k hk
    have hkx : x < (k:ℝ) := (Nat.floor_lt hx.le).mp (mem_Ioc.mp hk).1
    rw [min_eq_left ((one_le_div hx).mpr hkx.le)]
  rw [hlow, hhigh] at hh
  linarith only [hh]

noncomputable def harmonicBlockProfile (x : ℝ) : ℝ :=
  (harmonic ⌊x⌋₊:ℝ)-harmonic ⌊x/2⌋₊+(2*(⌊x/2⌋₊:ℝ)-⌊x⌋₊)/x

lemma clipped_block_sum {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : ⌊x⌋₊ ≤ K) :
    (∑ k ∈ Ioc 0 K, (min 1 (2*(k:ℝ)/x)-min 1 ((k:ℝ)/x))/(k:ℝ)) =
      harmonicBlockProfile x := by
  have hx2 : 0 < x/2 := by positivity
  have hhalf : ⌊x/2⌋₊ ≤ K := (Nat.floor_mono (show x/2 ≤ x by linarith)).trans hK
  simp_rw [sub_div, show ∀ k : ℕ, 2*(k:ℝ)/x = (k:ℝ)/(x/2) from fun _ => by ring]
  rw [sum_sub_distrib, clipped_harmonic_sum hx2 hhalf, clipped_harmonic_sum hx hK]
  unfold harmonicBlockProfile
  ring

lemma floor_half_div_tendsto :
    Tendsto (fun x : ℝ => (⌊x/2⌋₊:ℝ)/x) atTop (𝓝 (1/2)) := by
  have ht : Tendsto (fun x : ℝ => x/2) atTop atTop := by
    simpa only [div_eq_mul_inv] using tendsto_id.atTop_mul_const (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  have hh := (tendsto_nat_floor_div_atTop.comp ht).div_const (2:ℝ)
  simpa only [Function.comp_def, div_div, div_mul_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hh

lemma floor_ratio_tendsto :
    Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)/(⌊x/2⌋₊:ℝ)) atTop (𝓝 2) := by
  have hh := (tendsto_nat_floor_div_atTop (R := ℝ)).div floor_half_div_tendsto
    (by norm_num : (1/2:ℝ)≠0)
  norm_num only [one_div, inv_inv] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  change ((⌊x⌋₊:ℝ)/x)/((⌊x/2⌋₊:ℝ)/x) = (⌊x⌋₊:ℝ)/(⌊x/2⌋₊:ℝ)
  field_simp [hx.ne']

/-- The continuous clipped-sum profile tends to log 2. This part is a
harmonic-number calculation and contains no assertion about prime pairs. -/
theorem harmonicBlockProfile_tendsto :
    Tendsto harmonicBlockProfile atTop (𝓝 (Real.log 2)) := by
  have ht : Tendsto (fun x : ℝ => x/2) atTop atTop := by
    simpa only [div_eq_mul_inv] using tendsto_id.atTop_mul_const (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  have hA := Real.tendsto_harmonic_sub_log.comp (tendsto_nat_floor_atTop (α := ℝ))
  have hB := Real.tendsto_harmonic_sub_log.comp (tendsto_nat_floor_atTop.comp ht)
  have hlog := floor_ratio_tendsto.log (by norm_num : (2:ℝ)≠0)
  have hrem := (floor_half_div_tendsto.const_mul 2).sub (tendsto_nat_floor_div_atTop (R := ℝ))
  have hh := ((hA.sub hB).add hlog).add hrem
  norm_num only [sub_self, zero_add, mul_one_div, div_self (by norm_num : (2:ℝ)≠0), add_zero] at hh
  apply hh.congr'
  filter_upwards [(tendsto_nat_floor_atTop.comp ht).eventually_ge_atTop 1] with x hx
  have hBpos : (0:ℝ) < ⌊x/2⌋₊ := Nat.cast_pos.mpr hx
  have hxpos : 0 < x := by
    have hh := (Nat.one_le_floor_iff (x/2)).mp hx
    linarith
  have hAB : ⌊x/2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
  have hApos : (0:ℝ) < ⌊x⌋₊ := hBpos.trans_le (Nat.cast_le.mpr hAB)
  simp only [Function.comp_def, Real.log_div hApos.ne' hBpos.ne', harmonicBlockProfile]
  ring

lemma outputPrefix_error {α : ℝ} (hα : 1 ≤ α) (m : ℕ) :
    |(outputPrefix α m:ℝ)-(m:ℝ)/α| ≤ 1 := by
  have hα0 : 0 < α := by linarith
  have hy : 0 < ((m:ℝ)+1)/α := by positivity
  have hc : 1 ≤ ⌈((m:ℝ)+1)/α⌉₊ := Nat.ceil_pos.mpr hy
  have hlo := Nat.le_ceil (((m:ℝ)+1)/α)
  have hhi := Nat.ceil_lt_add_one hy.le
  have hi : 1/α ≤ 1 := (div_le_one hα0).mpr hα
  have he : ((m:ℝ)+1)/α = (m:ℝ)/α+1/α := by ring
  rw [outputPrefix, Nat.cast_sub hc, Nat.cast_one, abs_le]
  constructor <;> linarith only [hlo, hhi, hi, he, div_nonneg (by norm_num : (0:ℝ)≤1) hα0.le]

lemma clipped_outputPrefix_error {α : ℝ} (hα : 1 ≤ α) (N m : ℕ) :
    |((min N (outputPrefix α m):ℕ):ℝ)-min (N:ℝ) ((m:ℝ)/α)| ≤ 1 := by
  rw [Nat.cast_min]
  have hh := abs_min_sub_min_le_max (N:ℝ) (outputPrefix α m:ℝ) N ((m:ℝ)/α)
  simp only [sub_self, abs_zero] at hh
  exact hh.trans (max_le (by norm_num) (outputPrefix_error hα m))

noncomputable def linearBlockMain (α : ℝ) (N D K : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 K,
    (min (N:ℝ) (2*(D:ℝ)*k/α)-min (N:ℝ) ((D:ℝ)*k/α))/(k:ℝ)

lemma floor_block_ratio_le {α : ℝ} (hα : 0 ≤ α) {N D K : ℕ}
    (hD : 0 < D) (hNK : floorMul α N ≤ D*K) : ⌊α*N/(D:ℝ)⌋₊ ≤ K := by
  have hDR : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hD1 : (1:ℝ) ≤ D := Nat.one_le_cast.mpr hD
  have hh := Nat.lt_floor_add_one (α*(N:ℝ))
  have hb : (floorMul α N:ℝ) ≤ (D:ℝ)*K := by exact_mod_cast hNK
  change α*N < (floorMul α N:ℝ)+1 at hh
  have hreal : α*N/(D:ℝ) < (K:ℝ)+1 := (div_lt_iff₀ hDR).mpr (by nlinarith only [hh, hb, hD1])
  have hf : ⌊α*N/(D:ℝ)⌋₊ < K+1 := (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast hreal)
  omega

lemma linearBlockMain_eq_profile {α : ℝ} (hα : 0 < α) {N D K : ℕ}
    (hN : 0 < N) (hD : 0 < D) (hNK : floorMul α N ≤ D*K) :
    linearBlockMain α N D K = (N:ℝ)*harmonicBlockProfile (α*N/(D:ℝ)) := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hDR : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hx : 0 < α*N/(D:ℝ) := by positivity
  have hK := floor_block_ratio_le hα.le hD hNK
  rw [← clipped_block_sum hx hK, mul_sum, linearBlockMain]
  apply sum_congr rfl
  intro k hk
  have he₁ : 2*(D:ℝ)*k/α = (N:ℝ)*(2*(k:ℝ)/(α*N/(D:ℝ))) := by
    field_simp
  have he₂ : (D:ℝ)*k/α = (N:ℝ)*((k:ℝ)/(α*N/(D:ℝ))) := by
    field_simp
  rw [he₁, he₂]
  have hmin (t : ℝ) : min (N:ℝ) ((N:ℝ)*t) = (N:ℝ)*min 1 t := by
    rw [mul_min_of_nonneg _ _ hNR.le, mul_one]
  rw [hmin, hmin]
  ring

lemma psi_affine_error {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, |Chebyshev.psi X-(X:ℝ)| ≤ η*X+C := by
  have ht := psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := (Metric.tendsto_nhds.mp ht) η hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp he
  refine ⟨8*(T:ℝ), by positivity, ?_⟩
  intro X
  by_cases hX0 : X = 0
  · subst X
    simp [Chebyshev.psi]
  have hXR : (0:ℝ) < X := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hX0)
  by_cases hTX : T ≤ X
  · have hh := hT X hTX
    simp only [Real.dist_eq, Function.comp_def] at hh
    have heq : Chebyshev.psi X/(X:ℝ)-1 = (Chebyshev.psi X-(X:ℝ))/(X:ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hXR] at hh
    have hb := (div_lt_iff₀ hXR).mp hh
    have hT0 : 0 ≤ (T:ℝ) := Nat.cast_nonneg T
    linarith
  · have hXT : (X:ℝ) ≤ T := Nat.cast_le.mpr (le_of_not_ge hTX)
    have hψ0 := Chebyshev.psi_nonneg (X:ℕ)
    have hψ7 := Erdos972ChebyshevRowMean.psi_le_seven_mul hXR.le
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hη.le hXR.le]

/-- A quantitative comparison of the Chebyshev center with its clipped
linear main term. The constant C handles all small endpoints uniformly. -/
theorem blockChebyshevMain_linear_error {α η C : ℝ} (hα : 1 ≤ α)
    (hη : 0 ≤ η) (hC : 0 ≤ C) (N D K : ℕ)
    (hψ : ∀ X : ℕ, |Chebyshev.psi X-(X:ℝ)| ≤ η*X+C) :
    |blockChebyshevMain α N D K-linearBlockMain α N D K| ≤
      3*η*(D:ℝ)*K/α+2*(K:ℝ)*(η+C+1) := by
  have hα0 : 0 < α := by linarith
  have hterm (m : ℕ) :
      |Chebyshev.psi (min N (outputPrefix α m) : ℕ)-min (N:ℝ) ((m:ℝ)/α)| ≤
        η*((m:ℝ)/α+1)+C+1 := by
    have hround := clipped_outputPrefix_error hα N m
    have hpsi := hψ (min N (outputPrefix α m))
    have hsize : ((min N (outputPrefix α m):ℕ):ℝ) ≤ (m:ℝ)/α+1 := by
      have hr := (abs_le.mp (outputPrefix_error hα m)).2
      have hh : ((min N (outputPrefix α m):ℕ):ℝ) ≤ (outputPrefix α m:ℝ) :=
        Nat.cast_le.mpr (min_le_right _ _)
      linarith only [hr, hh]
    have hh := abs_add_le
      (Chebyshev.psi (min N (outputPrefix α m) : ℕ)-((min N (outputPrefix α m):ℕ):ℝ))
      (((min N (outputPrefix α m):ℕ):ℝ)-min (N:ℝ) ((m:ℝ)/α))
    have hm := mul_le_mul_of_nonneg_left hsize hη
    rw [sub_add_sub_cancel] at hh
    linarith only [hh, hround, hpsi, hm]
  rw [blockChebyshevMain, linearBlockMain, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Ioc 0 K, (3*η*(D:ℝ)/α+2*(η+C+1)) := by
      apply sum_le_sum
      intro k hk
      have hkR : (0:ℝ) < k := Nat.cast_pos.mpr (mem_Ioc.mp hk).1
      have hk1 : (1:ℝ) ≤ k := Nat.one_le_cast.mpr (mem_Ioc.mp hk).1
      have hu := hterm (2*D*k)
      have hl := hterm (D*k)
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hu hl
      rw [← sub_div, abs_div, abs_of_pos hkR]
      apply (div_le_iff₀ hkR).mpr
      have he :
          (Chebyshev.psi (min N (outputPrefix α (2*D*k)) : ℕ)-
           Chebyshev.psi (min N (outputPrefix α (D*k)) : ℕ))-
          (min (N:ℝ) (2*(D:ℝ)*k/α)-min (N:ℝ) ((D:ℝ)*k/α)) =
          (Chebyshev.psi (min N (outputPrefix α (2*D*k)) : ℕ)-min (N:ℝ) (2*(D:ℝ)*k/α))-
          (Chebyshev.psi (min N (outputPrefix α (D*k)) : ℕ)-min (N:ℝ) ((D:ℝ)*k/α)) := by ring
      rw [he]
      apply (abs_sub _ _).trans
      have hm := mul_le_mul_of_nonneg_left hk1 (show 0 ≤ 2*(η+C+1) by positivity)
      have he' : (3*η*(D:ℝ)/α+2*(η+C+1))*(k:ℝ) =
          η*(2*(D:ℝ)*k/α+1)+C+1+(η*((D:ℝ)*k/α+1)+C+1)+
          2*(η+C+1)*((k:ℝ)-1) := by ring
      rw [he']
      nlinarith only [hu, hl, hm]
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

/-- An actual prime-weighted first moment, with its evaluated main term,
for an explicit large-divisor block at arbitrarily large irrational scales. -/
theorem exists_block_firstMoment_log_two {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u D : ℕ, B < u ∧ 0 < u ∧ D = blockStart α (u^6) (root64 u) ∧
      0 < D ∧ D < u^6 ∧
      |(∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
        (u:ℝ)^6*Real.log 2| ≤ ε*(u:ℝ)^6 := by
  have hα0 : 0 < α := by linarith
  let η : ℝ := ε/24
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hψ⟩ := psi_affine_error hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp harmonicBlockProfile_tendsto) (ε/4) (by positivity))
  let V : ℕ := max (⌈α⌉₊+3) ⌈2*max T 1⌉₊
  let L : ℕ := ⌈8*(η+C+1)/ε⌉₊
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp
    ((root64_tendsto.eventually_ge_atTop V).and (eventually_ge_atTop L))
  obtain ⟨u, hBu, hu, hb⟩ := exists_block_firstMoment_scale hα hI
    (show 0 < ε/4 by positivity) (max B Q)
  obtain ⟨hvV, hLu⟩ := hQ u ((le_max_right B Q).trans hBu.le)
  have hvcut : ⌈α⌉₊+3 ≤ root64 u := (le_max_left _ _).trans hvV
  have hv0 := (root64_bounds hu).1
  have hv2 : 2 ≤ root64 u := by omega
  have hvu : root64 u ≤ u :=
    (Nat.le_self_pow (by decide : 64≠0) (root64 u)).trans (root64_bounds hu).2.1
  have hNv : root64 u ≤ u^6 := hvu.trans (Nat.le_self_pow (by decide : 6≠0) u)
  have hαv : α+1 < (root64 u:ℝ) := by
    have hh : (⌈α⌉₊:ℝ)+3 ≤ root64 u := by exact_mod_cast hvcut
    linarith only [hh, Nat.le_ceil α]
  let D := blockStart α (u^6) (root64 u)
  obtain ⟨hD0, hDN, hfloor, hND, hDα, hDv⟩ :=
    blockStart_bounds hα.le hv0 hNv (root64_square_add_two_le_sixth hu hv2) hαv
  change 0 < D at hD0
  change D < u^6 at hDN
  change floorMul α (u^6) ≤ D*root64 u at hfloor
  change (D:ℝ)*root64 u ≤ (α+1)*((u^6:ℕ):ℝ) at hDv
  have hDR : (0:ℝ) < D := Nat.cast_pos.mpr hD0
  have hNR : (0:ℝ) < (u^6:ℕ) := Nat.cast_pos.mpr (Nat.pow_pos hu)
  have hUR : (0:ℝ) < u := Nat.cast_pos.mpr hu
  have hvuR : (root64 u:ℝ) ≤ u := Nat.cast_le.mpr hvu
  have hDv2 : (D:ℝ)*root64 u ≤ 2*α*((u^6:ℕ):ℝ) := by
    have hh := mul_nonneg (show 0 ≤ α-1 by linarith) hNR.le
    nlinarith only [hDv, hh]
  have hxlo : (root64 u:ℝ)/2 ≤ α*(u^6:ℕ)/(D:ℝ) := by
    apply (le_div_iff₀ hDR).mpr
    nlinarith only [hDv2]
  have hTcut : T ≤ (root64 u:ℝ)/2 := by
    have hvceil : ⌈2*max T 1⌉₊ ≤ root64 u := (le_max_right _ _).trans hvV
    have hh := (Nat.le_ceil (2*max T 1)).trans (Nat.cast_le.mpr hvceil)
    linarith only [hh, le_max_left T 1]
  have hprofile : |harmonicBlockProfile (α*(u^6:ℕ)/(D:ℝ))-Real.log 2| ≤ ε/4 := by
    have hh := hT _ (hTcut.trans hxlo)
    simpa only [Real.dist_eq] using hh.le
  have hlinear : |linearBlockMain α (u^6) D (root64 u)-((u^6:ℕ):ℝ)*Real.log 2| ≤
      (ε/4)*((u^6:ℕ):ℝ) := by
    rw [linearBlockMain_eq_profile hα0 (Nat.pow_pos hu) hD0 hfloor,
      ← mul_sub, abs_mul, abs_of_pos hNR]
    have hh := mul_le_mul_of_nonneg_left hprofile hNR.le
    nlinarith only [hh]
  have hbudget : 8*(η+C+1) ≤ ε*(u:ℝ) := by
    have hh := (Nat.le_ceil (8*(η+C+1)/ε)).trans (Nat.cast_le.mpr hLu)
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith only [hh']
  have htail : 2*(root64 u:ℝ)*(η+C+1) ≤ (ε/4)*((u^6:ℕ):ℝ) := by
    have h26 : (u:ℝ)^2 ≤ ((u^6:ℕ):ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right hu (by decide : 2≤6))
    have hh₁ := mul_le_mul_of_nonneg_right hbudget hUR.le
    have hh₂ := mul_le_mul_of_nonneg_right hvuR (show 0 ≤ 2*(η+C+1) by positivity)
    have hh₃ := mul_le_mul_of_nonneg_left h26 hε.le
    nlinarith only [hh₁, hh₂, hh₃]
  have hmain : 3*η*(D:ℝ)*root64 u/α ≤ (ε/4)*((u^6:ℕ):ℝ) := by
    apply (div_le_iff₀ hα0).mpr
    have hh := mul_le_mul_of_nonneg_left hDv2 (show 0 ≤ 3*η by positivity)
    dsimp [η] at hh ⊢
    nlinarith only [hh]
  have hcenter : |blockChebyshevMain α (u^6) D (root64 u)-
      linearBlockMain α (u^6) D (root64 u)| ≤ (ε/2)*((u^6:ℕ):ℝ) := by
    have hh := blockChebyshevMain_linear_error hα.le hη.le hC (u^6) D (root64 u) hψ
    linarith only [hh, hmain, htail]
  have hfirst : |(∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
      blockChebyshevMain α (u^6) D (root64 u)| ≤ (ε/4)*((u^6:ℕ):ℝ) := by
    simpa only [Nat.cast_pow] using hb D (root64 u) hD0 le_rfl hfloor
  refine ⟨u, D, (le_max_left B Q).trans_lt hBu, hu, rfl, hD0, hDN, ?_⟩
  have he :
      (∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-((u^6:ℕ):ℝ)*Real.log 2 =
      ((∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
        blockChebyshevMain α (u^6) D (root64 u))+
      (blockChebyshevMain α (u^6) D (root64 u)-linearBlockMain α (u^6) D (root64 u))+
      (linearBlockMain α (u^6) D (root64 u)-((u^6:ℕ):ℝ)*Real.log 2) := by ring
  have hh := (abs_add_le
    (((∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
      blockChebyshevMain α (u^6) D (root64 u))+
      (blockChebyshevMain α (u^6) D (root64 u)-linearBlockMain α (u^6) D (root64 u)))
    (linearBlockMain α (u^6) D (root64 u)-((u^6:ℕ):ℝ)*Real.log 2)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  rw [← he] at hh
  simp only [Nat.cast_pow] at hh hfirst hcenter hlinear
  linarith only [hh, hfirst, hcenter, hlinear]

/-- Combining the evaluated first moment with the finite row-multiplicity
bound substantially improves the constant in the earlier second-moment
estimate. The logarithmic loss remains. -/
theorem exists_evaluated_block_dispersion {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u D : ℕ, B < u ∧ 0 < u ∧ D = blockStart α (u^6) (root64 u) ∧
      0 < D ∧ D < u^6 ∧
      (∑ d ∈ Ioc D (2*D),
        (row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤
        (u:ℝ)^6*(root64 u:ℝ)*Real.log (u^6 : ℕ)*(Real.log 2+ε)-
          (Chebyshev.psi (u^6 : ℕ)/(D:ℝ))*((Real.log 2-ε)*(u:ℝ)^6)+
          (Chebyshev.psi (u^6 : ℕ))^2/(2*(D:ℝ)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (root64_tendsto.eventually_ge_atTop (⌈α⌉₊+3))
  obtain ⟨u, D, hBu, hu, hDeq, hD, hDN, hfirst⟩ :=
    exists_block_firstMoment_log_two hα hI hε (max B T)
  have hvcut := hT u ((le_max_right B T).trans hBu.le)
  have hv0 := (root64_bounds hu).1
  have hv2 : 2 ≤ root64 u := by omega
  have hvu : root64 u ≤ u :=
    (Nat.le_self_pow (by decide : 64≠0) (root64 u)).trans (root64_bounds hu).2.1
  have hNv : root64 u ≤ u^6 := hvu.trans (Nat.le_self_pow (by decide : 6≠0) u)
  have hαv : α+1 < (root64 u:ℝ) := by
    have hh : (⌈α⌉₊:ℝ)+3 ≤ root64 u := by exact_mod_cast hvcut
    linarith only [hh, Nat.le_ceil α]
  obtain ⟨_, _, _, hND, hDα, _⟩ :=
    blockStart_bounds hα.le hv0 hNv (root64_square_add_two_le_sixth hu hv2) hαv
  rw [← hDeq] at hND hDα
  let R : ℕ → ℝ := fun d => row (Ioc 0 (u^6)) primeWeight (floorMul α) d
  let S : ℝ := ∑ d ∈ Ioc D (2*D), R d
  let L : ℝ := (root64 u:ℝ)*Real.log (u^6 : ℕ)
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hr0 (d : ℕ) (hd : d ∈ Ioc D (2*D)) : 0 ≤ R d := by
    unfold R row
    apply sum_nonneg
    intro p hp
    split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl
  have hrU (d : ℕ) (hd : d ∈ Ioc D (2*D)) : R d ≤ L := by
    have hDd := (mem_Ioc.mp hd).1.le
    exact prime_row_upper_of_large_divisor hα.le hv0
      (hDα.trans_le (Nat.cast_le.mpr hDd))
      (hND.trans (Nat.mul_le_mul_right (root64 u) hDd))
  have hsecond : (∑ d ∈ Ioc D (2*D), (R d)^2) ≤ L*S := by
    unfold S
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    nlinarith only [hr0 d hd, hrU d hd]
  have hSU : S ≤ (Real.log 2+ε)*(u:ℝ)^6 := by
    have hh := (abs_le.mp hfirst).2
    change S-(u:ℝ)^6*Real.log 2 ≤ ε*(u:ℝ)^6 at hh
    linarith only [hh]
  have hSL : (Real.log 2-ε)*(u:ℝ)^6 ≤ S := by
    have hh := (abs_le.mp hfirst).1
    change -(ε*(u:ℝ)^6) ≤ S-(u:ℝ)^6*Real.log 2 at hh
    linarith only [hh]
  have hmU := mul_le_mul_of_nonneg_left hSU hL
  have hmL := mul_le_mul_of_nonneg_left hSL
    (div_nonneg (Chebyshev.psi_nonneg (u^6 : ℕ)) (Nat.cast_nonneg D : (0:ℝ) ≤ D))
  have hc := centered_block_energy_upper R hD (Chebyshev.psi_nonneg (u^6 : ℕ)) hr0
  change _ ≤ (∑ d ∈ Ioc D (2*D), (R d)^2)-
    (Chebyshev.psi (u^6 : ℕ)/(D:ℝ))*S+(Chebyshev.psi (u^6 : ℕ))^2/(2*(D:ℝ)) at hc
  refine ⟨u, D, (le_max_left B T).trans_lt hBu, hu, hDeq, hD, hDN, ?_⟩
  change (∑ d ∈ Ioc D (2*D), (R d-Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤ _
  dsimp [L] at hsecond hmU
  nlinarith only [hc, hsecond, hmU, hmL]

/-- The evaluated first moment gives a definite negative centering
correction. The raw second moment is still present, so this is not the
strict signed off-diagonal gap required for the prime-pair conjecture. -/
theorem exists_negative_centering_correction {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u D : ℕ, B < u ∧ 0 < u ∧ D = blockStart α (u^6) (root64 u) ∧
      0 < D ∧ D < u^6 ∧
      (∑ d ∈ Ioc D (2*D),
        (row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤
        (∑ d ∈ Ioc D (2*D), (row (Ioc 0 (u^6)) primeWeight (floorMul α) d)^2)-
          ((u:ℝ)^6)^2/(8*(D:ℝ)) := by
  have hscale : Tendsto (fun u : ℕ => ((u^6:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop (by decide : 6≠0))
  have ht := psi_div_self_tendsto.comp hscale
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp ht) (1/16) (by norm_num))
  obtain ⟨u, D, hBu, hu, hDeq, hD, hDN, hfirst⟩ :=
    exists_block_firstMoment_log_two hα hI (show (0:ℝ)<1/64 by norm_num) (max B T)
  have hN : (0:ℝ) < (u^6:ℕ) := Nat.cast_pos.mpr (Nat.pow_pos hu)
  have hDR : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hpsi := hT u ((le_max_right B T).trans hBu.le)
  simp only [Real.dist_eq, Function.comp_def] at hpsi
  have hpL : (15/16:ℝ)*((u^6:ℕ):ℝ) ≤ Chebyshev.psi (u^6 : ℕ) := by
    apply (le_div_iff₀ hN).mp
    linarith only [(abs_lt.mp hpsi).1]
  have hpU : Chebyshev.psi (u^6 : ℕ) ≤ (17/16:ℝ)*((u^6:ℕ):ℝ) := by
    apply (div_le_iff₀ hN).mp
    linarith only [(abs_lt.mp hpsi).2]
  let S : ℝ := ∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d
  have hS : (2/3:ℝ)*((u^6:ℕ):ℝ) ≤ S := by
    have hlog : (2/3:ℝ)+1/64 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hh := mul_le_mul_of_nonneg_left hlog hN.le
    have hl := (abs_le.mp hfirst).1
    change -((1/64:ℝ)*(u:ℝ)^6) ≤ S-(u:ℝ)^6*Real.log 2 at hl
    simp only [Nat.cast_pow] at hh ⊢
    linarith only [hh, hl]
  have hgap : (13/96:ℝ)*((u^6:ℕ):ℝ) ≤ S-Chebyshev.psi (u^6 : ℕ)/2 := by
    linarith only [hS, hpU]
  have hm := mul_le_mul hpL hgap (show 0 ≤ (13/96:ℝ)*((u^6:ℕ):ℝ) by positivity)
    (Chebyshev.psi_nonneg (u^6 : ℕ))
  have hprod : ((u^6:ℕ):ℝ)^2/8 ≤
      Chebyshev.psi (u^6 : ℕ)*(S-Chebyshev.psi (u^6 : ℕ)/2) := by
    nlinarith only [hm, sq_nonneg (((u^6:ℕ):ℝ))]
  have hcorrection : ((u^6:ℕ):ℝ)^2/(8*(D:ℝ)) ≤
      (Chebyshev.psi (u^6 : ℕ)/(D:ℝ))*S-(Chebyshev.psi (u^6 : ℕ))^2/(2*(D:ℝ)) := by
    have hh := div_le_div_of_nonneg_right hprod hDR.le
    convert hh using 1 <;> ring
  have hr0 (d : ℕ) (hd : d ∈ Ioc D (2*D)) :
      0 ≤ row (Ioc 0 (u^6)) primeWeight (floorMul α) d := by
    unfold row
    apply sum_nonneg
    intro p hp
    split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl
  have hc := centered_block_energy_upper
    (fun d => row (Ioc 0 (u^6)) primeWeight (floorMul α) d) hD
    (Chebyshev.psi_nonneg (u^6 : ℕ)) hr0
  change _ ≤ _-(Chebyshev.psi (u^6 : ℕ)/(D:ℝ))*S+
    (Chebyshev.psi (u^6 : ℕ))^2/(2*(D:ℝ)) at hc
  refine ⟨u, D, (le_max_left B T).trans_lt hBu, hu, hDeq, hD, hDN, ?_⟩
  simp only [Nat.cast_pow] at hcorrection hc ⊢
  linarith only [hc, hcorrection]

#print axioms clipped_block_sum
#print axioms harmonicBlockProfile_tendsto
#print axioms linearBlockMain_eq_profile
#print axioms blockChebyshevMain_linear_error
#print axioms exists_block_firstMoment_log_two
#print axioms exists_negative_centering_correction
#print axioms exists_evaluated_block_dispersion
end Erdos972LargeDivisorBlockMain
