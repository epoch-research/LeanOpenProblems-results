import Submission.MovingWindowLimitExplore
import Submission.CountingExplore

/-! Quantitative stability of moving-window representation averages under
sparse unions. None of the statements in this file asserts pointwise control. -/
namespace Erdos66WindowPerturbation
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding Erdos66Generating
  Erdos66CumulativeRoundingError Erdos66QuadraticWindowRounding
  Erdos66MovingWindowRounding Erdos66MovingWindowLimit Erdos66Counting Filter
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def localCount (A : Set ℕ) (t w : ℕ) : ℕ :=
  ((Finset.Ico t (t+w)).filter (fun a ↦ a∈A)).card

lemma localCount_eq_sum (A : Set ℕ) (t w : ℕ) :
    (localCount A t w : ℝ)=∑ i∈Finset.Ico t (t+w), indicator A i := by
  simp only [localCount,indicator,Finset.sum_ite,
    Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]

lemma rounded_local_count_bound (t w : ℕ) :
    (localCount (roundedSet profile) t w : ℝ) ≤ 2+prefixSum profile w := by
  rw [localCount_eq_sum]
  have he (N : ℕ) := rounded_prefix_discrepancy profile
    (fun n ↦ ⟨profile_nonneg n,profile_le_one n⟩) N
  have hdiff : (∑ i∈Finset.Ico t (t+w), indicator (roundedSet profile) i) ≤
      2+∑ i∈Finset.Ico t (t+w), profile i := by
    rw [Finset.sum_Ico_eq_sub _ (by omega : t ≤ t+w),
      Finset.sum_Ico_eq_sub _ (by omega : t ≤ t+w)]
    have h₁ := (abs_le.mp (he (t+w))).2
    have h₂ := (abs_le.mp (he t)).1
    simp only [Finset.sum_sub_distrib] at h₁ h₂
    linarith
  apply hdiff.trans
  apply add_le_add le_rfl
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    _ ≤ ∑ i∈Finset.range (t+w-t), profile i := by
      apply Finset.sum_le_sum
      intro i hi
      exact profile_antitone (by omega)
    _ ≤ prefixSum profile w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.range_mono
        omega
      · intro i hi hn
        exact profile_nonneg i

lemma rounded_local_count_sqrt (t w : ℕ) :
    (localCount (roundedSet profile) t w : ℝ) ≤ 2+Real.sqrt (prefixMajorant w) := by
  exact (rounded_local_count_bound t w).trans
    (add_le_add le_rfl (Real.le_sqrt_of_sq_le (profile_prefix_square_bound w)))

noncomputable def pairWindow (S T : Finset ℕ) (n w : ℕ) : Finset (ℕ × ℕ) :=
  (S×ˢT).filter (fun p ↦ p.1+p.2∈movingWindow n w)

lemma mem_pairWindow {S T : Finset ℕ} {n w : ℕ} {p : ℕ × ℕ} :
    p∈pairWindow S T n w ↔ p.1∈S ∧ p.2∈T ∧ p.1+p.2∈movingWindow n w := by
  simp only [pairWindow,Finset.mem_filter,Finset.mem_product]
  tauto

lemma pairWindow_card_comm (S T : Finset ℕ) (n w : ℕ) :
    (pairWindow S T n w).card=(pairWindow T S n w).card := by
  apply Finset.card_bij (fun p _ ↦ p.swap)
  · intro p hp
    obtain ⟨h₁,h₂,h₃⟩ := mem_pairWindow.mp hp
    exact mem_pairWindow.mpr ⟨h₂,h₁,by change p.2+p.1∈_; simpa only [Nat.add_comm] using h₃⟩
  · intro p hp q hq he
    exact Prod.swap_injective he
  · intro p hp
    obtain ⟨h₁,h₂,h₃⟩ := mem_pairWindow.mp hp
    exact ⟨p.swap,mem_pairWindow.mpr ⟨h₂,h₁,by change p.2+p.1∈_; simpa only [Nat.add_comm] using h₃⟩,rfl⟩

lemma pairWindow_mono {S S' T T' : Finset ℕ} (hS : S⊆S') (hT : T⊆T') (n w : ℕ) :
    pairWindow S T n w⊆pairWindow S' T' n w := by
  intro p hp
  obtain ⟨h₁,h₂,h₃⟩ := mem_pairWindow.mp hp
  exact mem_pairWindow.mpr ⟨hS h₁,hT h₂,h₃⟩

lemma pairWindow_union_bound (S D : Finset ℕ) (n w : ℕ) :
    (pairWindow (S∪D) (S∪D) n w).card ≤ (pairWindow S S n w).card+
      2*(pairWindow S D n w).card+D.card^2 := by
  have he : pairWindow (S∪D) (S∪D) n w=
      ((pairWindow S S n w∪pairWindow S D n w)∪pairWindow D S n w)∪pairWindow D D n w := by
    ext p
    simp only [mem_pairWindow,Finset.mem_union]
    tauto
  rw [he]
  have h₁ := Finset.card_union_le
    ((pairWindow S S n w∪pairWindow S D n w)∪pairWindow D S n w) (pairWindow D D n w)
  have h₂ := Finset.card_union_le (pairWindow S S n w∪pairWindow S D n w) (pairWindow D S n w)
  have h₃ := Finset.card_union_le (pairWindow S S n w) (pairWindow S D n w)
  have h₄ : (pairWindow D D n w).card ≤ D.card^2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun p : ℕ×ℕ ↦ p.1+p.2∈movingWindow n w) (D×ˢD))
    simpa only [Finset.card_product,pow_two] using this
  rw [pairWindow_card_comm D S] at h₂
  omega

lemma pairWindow_fibers (S T : Finset ℕ) (n w : ℕ) :
    (pairWindow S T n w).card =
      ∑ d∈T, (S.filter (fun a ↦ a+d∈movingWindow n w)).card := by
  simp only [pairWindow,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  rw [Finset.sum_comm]

lemma pairWindow_local_bound (A : Set ℕ) (S T : Finset ℕ) (n w : ℕ) (L : ℝ)
    (hS : ∀ a∈S, a∈A) (hL : ∀ t, (localCount A t w : ℝ) ≤ L) :
    ((pairWindow S T n w).card : ℝ) ≤ (T.card : ℝ)*L := by
  rw [pairWindow_fibers,Nat.cast_sum]
  calc
    _ ≤ ∑ _d∈T, L := by
      apply Finset.sum_le_sum
      intro d hd
      apply le_trans _ (hL (n+1-d))
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro a ha
      obtain ⟨ha,hw⟩ := Finset.mem_filter.mp ha
      obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hw
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hS a ha⟩
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

lemma representation_window_eq (A : Set ℕ) (n w : ℕ) :
    (∑ k∈movingWindow n w, sumRep A k)=
      (pairWindow (cutoff A (n+w+1)) (cutoff A (n+w+1)) n w).card := by
  calc
    _ = ∑ k∈movingWindow n w,
        (((cutoff A (n+w+1))×ˢ(cutoff A (n+w+1))).filter
          (fun p : ℕ×ℕ ↦ p.1+p.2=k)).card := by
      apply Finset.sum_congr rfl
      intro k hk
      exact sumRep_eq_fiber_card A (n+w+1) k (Finset.mem_Ico.mp hk).2
    _ = _ := Finset.sum_card_fiberwise_eq_card_filter _ _ _

lemma cutoff_union (A D : Set ℕ) (N : ℕ) : cutoff (A∪D) N=cutoff A N∪cutoff D N := by
  ext a
  simp only [mem_cutoff,Set.mem_union,Finset.mem_union]
  tauto

/-- A local-density estimate makes the mixed contribution of sparse added
points much smaller than the trivial pointwise bound. -/
theorem window_union_error_bound (A D : Set ℕ) (n w : ℕ) (L : ℝ)
    (hL : ∀ t, (localCount A t w : ℝ) ≤ L) :
    0 ≤ ∑ k∈movingWindow n w, ((sumRep (A∪D) k : ℝ)-(sumRep A k : ℝ)) ∧
    (∑ k∈movingWindow n w, ((sumRep (A∪D) k : ℝ)-(sumRep A k : ℝ))) ≤
      2*(count D (n+w+1) : ℝ)*L+(count D (n+w+1) : ℝ)^2 := by
  rw [Finset.sum_sub_distrib,← Nat.cast_sum,← Nat.cast_sum,
    representation_window_eq,representation_window_eq,cutoff_union]
  have hlo := Finset.card_le_card (pairWindow_mono
    (Finset.subset_union_left : cutoff A (n+w+1)⊆cutoff A (n+w+1)∪cutoff D (n+w+1))
    (Finset.subset_union_left : cutoff A (n+w+1)⊆cutoff A (n+w+1)∪cutoff D (n+w+1)) n w)
  have hhi := pairWindow_union_bound (cutoff A (n+w+1)) (cutoff D (n+w+1)) n w
  have hloc := pairWindow_local_bound A (cutoff A (n+w+1)) (cutoff D (n+w+1)) n w L
    (fun a ha ↦ (mem_cutoff.mp ha).2) hL
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast hlo)
  · have hh : ((pairWindow (cutoff A (n+w+1)∪cutoff D (n+w+1))
        (cutoff A (n+w+1)∪cutoff D (n+w+1)) n w).card : ℝ) ≤
        ((pairWindow (cutoff A (n+w+1)) (cutoff A (n+w+1)) n w).card : ℝ)+
        2*((pairWindow (cutoff A (n+w+1)) (cutoff D (n+w+1)) n w).card : ℝ)+
        ((cutoff D (n+w+1)).card : ℝ)^2 := by exact_mod_cast hhi
    change _ ≤ 2*((cutoff D (n+w+1)).card : ℝ)*L+((cutoff D (n+w+1)).card : ℝ)^2
    nlinarith

lemma rounded_local_majorant_sq {n w : ℕ} (hw : 1 ≤ w) (hwn : w ≤ n) :
    (2+Real.sqrt (prefixMajorant w))^2 ≤
      18*(w : ℝ)*(1+Real.log 5+Real.log n) := by
  have hb := prefixMajorant_double_bound (n := w) (w := 0) hw (Nat.zero_le w)
  simp only [Nat.add_zero] at hb
  have hlog : Real.log (w : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (show 0<w by omega)) (by exact_mod_cast hwn)
  have hB := prefixMajorant_nonneg w
  have hs := Real.sq_sqrt hB
  have hW : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hn := Real.log_natCast_nonneg n
  have hlogmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 5*w by positivity)
  have hprod : 1 ≤ (w : ℝ)*(1+Real.log 5+Real.log n) :=
    (one_mul (1 : ℝ)).symm.trans_le (mul_le_mul hW (by linarith) (by norm_num) (by positivity))
  nlinarith [sq_nonneg (Real.sqrt (prefixMajorant w)-2)]

lemma normalized_union_error_sq (D : Set ℕ) {n w : ℕ} {K : ℝ}
    (hn : 2 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) (hK : 0 ≤ K)
    (hM : (count D (n+w+1) : ℝ)^2 ≤ K*w) :
    ((∑ k∈movingWindow n w, ((sumRep (roundedSet profile∪D) k : ℝ)-
      (sumRep (roundedSet profile) k : ℝ)))/((w : ℝ)*Real.log n))^2 ≤
      (144*K*(1+Real.log 5+Real.log n)+2*K^2)/(Real.log n)^2 := by
  let M : ℝ := count D (n+w+1)
  let L := 2+Real.sqrt (prefixMajorant w)
  let H := 1+Real.log 5+Real.log n
  let E := ∑ k∈movingWindow n w, ((sumRep (roundedSet profile∪D) k : ℝ)-
    (sumRep (roundedSet profile) k : ℝ))
  have hML := window_union_error_bound (roundedSet profile) D n w L
    (fun t ↦ rounded_local_count_sqrt t w)
  change 0 ≤ E ∧ E ≤ 2*M*L+M^2 at hML
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hLsq : L^2 ≤ 18*(w : ℝ)*H := rounded_local_majorant_sq hw hwn
  have hEsq : E^2 ≤ (2*M*L+M^2)^2 :=
    (sq_le_sq₀ hML.1 (by positivity)).mpr hML.2
  have hcross := mul_le_mul hM hLsq (sq_nonneg L) (by positivity : (0 : ℝ) ≤ K*w)
  have hM4 := (sq_le_sq₀ (sq_nonneg M) (by positivity : (0 : ℝ) ≤ K*w)).mpr hM
  have hbound : E^2 ≤ (144*K*H+2*K^2)*(w : ℝ)^2 := by
    nlinarith [sq_nonneg (2*M*L-M^2)]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  change (E/((w : ℝ)*Real.log n))^2 ≤ (144*K*H+2*K^2)/(Real.log n)^2
  rw [div_pow,mul_pow,← div_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (div_le_iff₀ (by positivity : (0 : ℝ)<(w : ℝ)^2)).mpr hbound

lemma union_error_limit (D : Set ℕ) (w : ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hw : ∀ᶠ n in atTop, 1 ≤ w n ∧ w n ≤ n)
    (hM : ∀ᶠ n in atTop, (count D (n+w n+1) : ℝ)^2 ≤ K*w n) :
    Tendsto (fun n : ℕ ↦
      (∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile∪D) k : ℝ)-
        (sumRep (roundedSet profile) k : ℝ)))/((w n : ℝ)*Real.log n)) atTop (𝓝 0) := by
  have hinv := log_atTop_nat.const_div_atTop 1
  have hbound : Tendsto (fun n : ℕ ↦
      (144*K*(1+Real.log 5+Real.log n)+2*K^2)/(Real.log n)^2) atTop (𝓝 0) := by
    have hh := (hinv.const_mul (144*K)).add
      ((hinv.pow 2).const_mul (144*K*(1+Real.log 5)+2*K^2))
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp
    <;> ring
  have hsq : Tendsto (fun n : ℕ ↦
      ((∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile∪D) k : ℝ)-
        (sumRep (roundedSet profile) k : ℝ)))/((w n : ℝ)*Real.log n))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ sq_nonneg _)) _ hbound
    filter_upwards [eventually_ge_atTop 2,hw,hM] with n hn hw hM
    exact normalized_union_error_sq D hn hw.1 hw.2 hK hM
  have habs := hsq.sqrt
  simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

lemma normalized_union_error_sq_general (D : Set ℕ) {n w : ℕ}
    (hn : 2 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) :
    ((∑ k∈movingWindow n w, ((sumRep (roundedSet profile∪D) k : ℝ)-
      (sumRep (roundedSet profile) k : ℝ)))/((w : ℝ)*Real.log n))^2 ≤
      144*((count D (n+w+1) : ℝ)^2/((w : ℝ)*Real.log n))*
        ((1+Real.log 5+Real.log n)/Real.log n)+
      2*((count D (n+w+1) : ℝ)^2/((w : ℝ)*Real.log n))^2 := by
  have hW : (0 : ℝ)<w := by exact_mod_cast (show 0<w by omega)
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hh := normalized_union_error_sq D hn hw hwn
    (K := (count D (n+w+1) : ℝ)^2/w) (by positivity)
    (by rw [div_mul_cancel₀ _ hW.ne'])
  convert hh using 1
  field_simp
  <;> ring

lemma union_error_limit_of_width (D : Set ℕ) (w : ℕ → ℕ)
    (hw : ∀ᶠ n in atTop, 0<w n ∧ w n ≤ n)
    (hM : Tendsto (fun n : ℕ ↦ (count D (n+w n+1) : ℝ)^2/
      ((w n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦
      (∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile∪D) k : ℝ)-
        (sumRep (roundedSet profile) k : ℝ)))/((w n : ℝ)*Real.log n)) atTop (𝓝 0) := by
  have hfactor : Tendsto (fun n : ℕ ↦ (1+Real.log 5+Real.log n)/Real.log n) atTop (𝓝 1) := by
    have hh := (log_atTop_nat.const_div_atTop (1+Real.log 5)).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp
  have hbound := ((hM.const_mul 144).mul hfactor).add ((hM.pow 2).const_mul 2)
  simp only [mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero] at hbound
  have hsq : Tendsto (fun n : ℕ ↦
      ((∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile∪D) k : ℝ)-
        (sumRep (roundedSet profile) k : ℝ)))/((w n : ℝ)*Real.log n))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ sq_nonneg _)) _ hbound
    filter_upwards [eventually_ge_atTop 2,hw] with n hn hw
    exact normalized_union_error_sq_general D hn hw.1 hw.2
  have habs := hsq.sqrt
  simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-- The sparse union preserves even the strongest shorter-window result
proved for the canonical rounding. -/
theorem rounded_union_window_limit_of_width (D : Set ℕ)
    (hD : ∀ N, (count D N : ℝ)^4 ≤ N) (w : ℕ → ℕ)
    (hw : ∀ᶠ n in atTop, 0<w n ∧ w n ≤ n)
    (hscale : Tendsto (fun n : ℕ ↦ (n : ℝ)/((w n : ℝ)^2*Real.log n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n),
      (sumRep (roundedSet profile∪D) k : ℝ))/((w n : ℝ)*Real.log n)) atTop (𝓝 1) := by
  have hMsq : Tendsto (fun n : ℕ ↦
      ((count D (n+w n+1) : ℝ)^2/((w n : ℝ)*Real.log n))^2) atTop (𝓝 0) := by
    have hbound := (hscale.mul (log_atTop_nat.const_div_atTop 1)).const_mul 3
    simp only [mul_zero] at hbound
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ sq_nonneg _)) _ hbound
    filter_upwards [eventually_ge_atTop 2,hw] with n hn hw
    have hW : (0 : ℝ)<w n := by exact_mod_cast hw.1
    have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have harg : n+w n+1 ≤ 3*n := by omega
    have hM : (count D (n+w n+1) : ℝ)^4 ≤ 3*(n : ℝ) :=
      (hD _).trans (by exact_mod_cast harg)
    rw [div_pow,← pow_mul]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hW hlog))).mpr
    have he : 3*((n : ℝ)/((w n : ℝ)^2*Real.log n)*(1/Real.log n))*
        ((w n : ℝ)*Real.log n)^2=3*(n : ℝ) := by
      field_simp
      <;> ring
    rw [he]
    exact hM
  have hM : Tendsto (fun n : ℕ ↦ (count D (n+w n+1) : ℝ)^2/
      ((w n : ℝ)*Real.log n)) atTop (𝓝 0) := by
    have habs := hMsq.sqrt
    simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at habs
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hh := (rounded_moving_window_limit_of_width w hw hscale).add
    (union_error_limit_of_width D w hw hM)
  simp only [add_zero] at hh
  apply hh.congr
  intro n
  rw [Finset.sum_sub_distrib]
  ring

/-- Sparse perturbations preserve the averaged theorem. This statement does
not assert that either set has a pointwise normalized limit. -/
theorem rounded_union_window_limit (D : Set ℕ)
    (hD : ∀ N, (count D N : ℝ)^4 ≤ N) (w : ℕ → ℕ)
    (hw : ∀ᶠ n in atTop, w n ≤ n ∧ n ≤ (w n)^2) :
    Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n),
      (sumRep (roundedSet profile∪D) k : ℝ))/((w n : ℝ)*Real.log n)) atTop (𝓝 1) := by
  have hw' : ∀ᶠ n in atTop, 1 ≤ w n ∧ w n ≤ n := by
    filter_upwards [eventually_ge_atTop 1,hw] with n hn hw
    exact ⟨by nlinarith [hw.2],hw.1⟩
  have hM : ∀ᶠ n in atTop, (count D (n+w n+1) : ℝ)^2 ≤ 2*w n := by
    filter_upwards [eventually_ge_atTop 1,hw] with n hn hw
    have h₁ : (n+w n+1 : ℕ) ≤ 3*n := by omega
    have h₂ : (n : ℝ) ≤ (w n : ℝ)^2 := by exact_mod_cast hw.2
    have h₃ : ((n+w n+1 : ℕ) : ℝ) ≤ 3*(n : ℝ) := by exact_mod_cast h₁
    have hh := hD (n+w n+1)
    have hM0 : 0 ≤ (count D (n+w n+1) : ℝ)^2 := sq_nonneg _
    have hW : 0 ≤ (w n : ℝ) := by positivity
    nlinarith [sq_nonneg ((count D (n+w n+1) : ℝ)^2-2*(w n : ℝ))]
  have hh := (rounded_moving_window_limit w hw).add
    (union_error_limit D w (K := 2) (by norm_num) hw' hM)
  simp only [add_zero] at hh
  apply hh.congr
  intro n
  rw [Finset.sum_sub_distrib]
  ring

end Erdos66WindowPerturbation
