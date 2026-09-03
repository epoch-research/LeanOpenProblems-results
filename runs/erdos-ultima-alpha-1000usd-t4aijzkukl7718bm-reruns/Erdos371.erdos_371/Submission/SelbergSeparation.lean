import FormalConjecturesUtil
import Submission.CofactorSelberg
import Submission.RectangleSeparation

/-! A quantitative unsigned largest-prime-factor separation estimate using
polynomial-threshold Selberg weights. No orientation balance is asserted. -/

namespace Erdos371SelbergSeparation

open Finset Erdos371Cofactor Erdos371CofactorSelberg
  Erdos371ComparableLowProduct Erdos371ComparableHighProduct
  Erdos371PrimeHarmonicBlocks Erdos371RectangleSeparation

attribute [local instance] Classical.propDecidable

def sieveExponent (k : ℕ) : ℕ := 20*k+40

lemma threshold_eq (k : ℕ) : (4*2^k)^20 = 2^(sieveExponent k) := by
  rw [show 4*2^k = 2^(k+2) by simp [pow_add, mul_comm], ← pow_mul]
  congr 1
  unfold sieveExponent
  omega

lemma factor_mem_inputs {a b p q n N w : ℕ} (ha : 0<a) (hb : 0<b)
    (hp : p.Prime) (hq : q.Prime) (han : a*p=n) (hbn : b*q=n+1)
    (hnN : n<N) (hzp : w≤p) (hzq : w≤q) : n ∈ inputs w a b N := by
  have hpa : n/a=p := by rw [← han, Nat.mul_div_cancel_left p ha]
  have hqb : (n+1)/b=q := by rw [← hbn, Nat.mul_div_cancel_left q hb]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hnN, ⟨p,han.symm⟩, ⟨q,hbn.symm⟩, ?_⟩
  simpa [hpa,hqb] using And.intro hp (And.intro hq (And.intro hzp hzq))

lemma mem_highCover {n N w L t : ℕ} (hw : 0 < w) (hn : 1 < n) (hnN : n < N) (hN : N ≤ 2^t)
    (hr : max (P n) (P (n+1)) ≤ 2^L*min (P n) (P (n+1)))
    (hmin : w ≤ min (P n) (P (n+1)))
    (hprod : (4*w)^20*N < P n*P (n+1)) :
    n ∈ diagonalCover w (L+1) t N := by
  let a := cofactor n
  let b := cofactor (n+1)
  have ha : 0 < a := cofactor_pos hn
  have hb : 0 < b := cofactor_pos (by omega : 1 < n+1)
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have han : a*P n=n := cofactor_mul n
  have hbn : b*P (n+1)=n+1 := cofactor_mul (n+1)
  have hratio := factor_cofactor_ratio ha hb hp.pos hq.pos (by omega : 0 < n) han hbn hr
  have hsmall : a*b*(4*w)^20 < n := cofactor_product_small ha hb han hbn
    ((Nat.mul_le_mul_left ((4*w)^20) (by omega : n+1 ≤ N)).trans_lt hprod)
  let i := Nat.log 2 (min a b)
  let j := Nat.log 2 (max a b)
  have hm0 : 0 < min a b := by omega
  have hma : 2^i ≤ min a b := Nat.pow_log_le_self 2 hm0.ne'
  have hmb : 2^j ≤ max a b := Nat.pow_log_le_self 2 (show max a b ≠ 0 by omega)
  have hmA : min a b ≤ 2*2^i := by
    have h := (Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) (min a b)).le
    simpa [i, pow_succ, mul_comm] using h
  have hmB : max a b ≤ 2*2^j := by
    have h := (Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) (max a b)).le
    simpa [j, pow_succ, mul_comm] using h
  have hij : i ≤ j ∧ j ≤ i+(L+1) := log_ratio_bound hm0 min_le_max (by
    simpa [pow_succ, mul_comm, mul_left_comm] using hratio)
  have hi : i < t+1 := by
    have hmaN : min a b < N := by
      have hac : a ≤ n := by nlinarith [hp.one_lt]
      exact (min_le_left _ _).trans_lt (hac.trans_lt hnN)
    have hit := Nat.log_lt_of_lt_pow hm0.ne' (hmaN.trans_le hN)
    change i < t at hit
    omega
  have hAB : 2^i*2^j ≤ a*b := by
    have hh := Nat.mul_le_mul hma hmb
    simpa [min_mul_max] using hh
  have hmul : (2^i*2^j)*(4*w)^20 ≤ N :=
    ((Nat.mul_le_mul_right ((4*w)^20) hAB).trans hsmall.le).trans hnN.le
  have hthr : 0 < (4*w)^20 := by positivity
  have hABN : 2^i*2^j ≤ N := by nlinarith
  have hlarge : (4*w)^20 ≤ N/(2^i*2^j)+1 := by
    have hh := (Nat.le_div_iff_mul_le (by positivity : 0 < 2^i*2^j)).mpr
      (show (4*w)^20*(2^i*2^j) ≤ N by nlinarith)
    omega
  have hc := factor_mem_inputs ha hb hp hq han hbn hnN
    (hmin.trans (min_le_left _ _)) (hmin.trans (min_le_right _ _))
  apply mem_biUnion.mpr
  refine ⟨i, mem_range.mpr hi, mem_biUnion.mpr ⟨j, mem_Icc.mpr hij, ?_⟩⟩
  rw [admissibleBox, if_pos ⟨hABN,hlarge⟩]
  by_cases hab : a ≤ b
  · rw [min_eq_left hab] at hma hmA
    rw [max_eq_right hab] at hmb hmB
    exact mem_union_left _ (mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨hma,hmA⟩,
      mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨hmb,hmB⟩,hc⟩⟩)
  · have hba : b ≤ a := by omega
    rw [min_eq_right hba] at hma hmA
    rw [max_eq_left hba] at hmb hmB
    exact mem_union_right _ (mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨hmb,hmB⟩,
      mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨hma,hmA⟩,hc⟩⟩)

lemma mem_middleCover {n t E L : ℕ} (hn : 1 < n) (hnN : n < 2^t)
    (hr : max (P n) (P (n+1)) ≤ 2^L*min (P n) (P (n+1)))
    (hprod : 2^t < P n*P (n+1))
    (hprod' : P n*P (n+1) ≤ 2^E*2^t) :
    n ∈ middleCover t (E) L (2^t) := by
  let p := min (P n) (P (n+1))
  let q := max (P n) (P (n+1))
  let j := Nat.log 2 p
  have hp : p.Prime := by
    dsimp [p]
    rcases min_choice (P n) (P (n+1)) with h | h <;> rw [h]
    · exact Nat.prime_maxPrimeFac_of_one_lt _ hn
    · exact Nat.prime_maxPrimeFac_of_one_lt _ (by omega)
  have hpow : 2^j ≤ p := Nat.pow_log_le_self 2 hp.ne_zero
  have hlt : p < 2^(j+1) := Nat.lt_pow_succ_log_self (by decide) p
  have hpq : p*q=P n*P (n+1) := min_mul_max _ _
  have hj1 : t < 2*j+L+2 := by
    have hmul : p*q < 2^L*2^(j+1)*2^(j+1) := by
      have h1 := Nat.mul_le_mul_left p (show q ≤ 2^L*p from hr)
      have h2 := Nat.mul_lt_mul_of_pos_left (Nat.mul_self_lt_mul_self hlt) (Nat.two_pow_pos L)
      nlinarith
    have he : 2^L*2^(j+1)*2^(j+1)=2^(2*j+L+2) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [he] at hmul
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mp
      (hprod.trans (by simpa [hpq] using hmul))
  have hj2 : 2*j ≤ t+E := by
    have hm : 2^j*2^j ≤ p*q := Nat.mul_le_mul hpow (hpow.trans min_le_max)
    have he : 2^j*2^j=2^(2*j) := by rw [← pow_add]; congr 1; omega
    rw [he,hpq] at hm
    rw [← pow_add] at hprod'
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp (hm.trans hprod')
    omega
  apply mem_biUnion.mpr
  refine ⟨j, mem_filter.mpr ⟨mem_range.mpr (by omega),hj1,hj2⟩,
    mem_biUnion.mpr ⟨p,block_of_log hp,?_⟩⟩
  by_cases h : P n ≤ P (n+1)
  · apply mem_union_left
    exact mem_filter.mpr ⟨mem_range.mpr hnN, by omega,
      by simpa [p,min_eq_left h] using (Nat.maxPrimeFac_dvd (n := n))⟩
  · apply mem_union_right
    exact mem_filter.mpr ⟨mem_range.mpr hnN,
      by simpa [p,min_eq_right (by omega : P (n+1) ≤ P n)] using (Nat.maxPrimeFac_dvd (n := n+1))⟩

lemma closeInputs_subset {K k : ℕ} (hK : k ≤ K) (t L : ℕ) :
    closeInputs L (2^t) ⊆ ((smallInputs K (2^t) ∪ fullCover 1 L K (2^t+1) (2^t)) ∪
      middleCover t (sieveExponent k) L (2^t)) ∪ diagonalCover (2^k) (L+1) t (2^t) := by
  intro n hn
  obtain ⟨hnN,hr⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  by_cases hsmall : P n ≤ 2^K ∨ P (n+1) ≤ 2^K
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnN,hsmall⟩)))
  have hn1 : 1 < n := by
    by_contra h
    have hh : n=0 ∨ n=1 := by omega
    rcases hh with rfl | rfl
    · exact hsmall (Or.inl (by simp [P]))
    · exact hsmall (Or.inl (by simpa [P] using (Nat.one_le_two_pow (n := K))))
  have hlarge : 2^K ≤ min (P n) (P (n+1)) := by omega
  by_cases hlow : P n*P (n+1) ≤ 2^t
  · exact mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_lowCover_external hnN' hn1 hr (by simpa using hlow) hlarge)))
  by_cases hmid : P n*P (n+1) ≤ (4*2^k)^20*2^t
  · exact mem_union_left _ (mem_union_right _ (mem_middleCover hn1 hnN' hr (by omega) (by simpa only [threshold_eq] using hmid)))
  · exact mem_union_right _ (mem_highCover (by positivity) hn1 hnN' le_rfl hr
      ((Nat.pow_le_pow_right (by decide) hK).trans hlarge) (by omega))

/-- A finite, quantitative separation bound. The sieve term loses only `L+2`,
not a power of the multiplicative ratio `2^L`. -/
theorem closeInputs_card_bound {K k t L : ℕ} (hK0 : 0 < K) (hK : k ≤ K)
    (hk : 2 ≤ k) (ht : 0 < t) (hLt : 2*(L+2) ≤ t) :
    (closeInputs L (2^t)).card ≤
      2*((smoothInputs K (2^t)).card:ℝ) +
      128*(L+1:ℕ)*(2:ℝ)^t/K + 32*(2:ℝ)^t*(sieveExponent k+L+3:ℕ)/t +
      144*(Real.exp 1)^2*(2:ℝ)^t*(t+1:ℕ)*(L+2:ℕ)/(Real.log ((2^k:ℕ):ℝ))^2 := by
  have hc := card_le_card (closeInputs_subset hK t L)
  have h1 := card_union_le
    ((smallInputs K (2^t) ∪ fullCover 1 L K (2^t+1) (2^t)) ∪ middleCover t (sieveExponent k) L (2^t))
    (diagonalCover (2^k) (L+1) t (2^t))
  have h2 := card_union_le (smallInputs K (2^t) ∪ fullCover 1 L K (2^t+1) (2^t))
    (middleCover t (sieveExponent k) L (2^t))
  have h3 := card_union_le (smallInputs K (2^t)) (fullCover 1 L K (2^t+1) (2^t))
  have h4 := smallInputs_card K (2^t)
  have hb : (closeInputs L (2^t)).card ≤ 2*(smoothInputs K (2^t)).card +
      (fullCover 1 L K (2^t+1) (2^t)).card + (middleCover t (sieveExponent k) L (2^t)).card +
      (diagonalCover (2^k) (L+1) t (2^t)).card := by omega
  have hb' := Nat.cast_le (α := ℝ) |>.mpr hb
  push_cast at hb'
  have hlow := fullCover_card_bound hK0 1 L (2^t+1) (2^t)
  have hmid := middleCover_card_bound ht hLt (sieveExponent k) (2^t)
  have hhigh := diagonalCover_card_bound (2^k) (L+1) t (2^t) (by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    norm_num at hh ⊢
    omega)
  push_cast at hlow hmid hhigh ⊢
  norm_num at hlow
  rw [show (L:ℝ)+1+1=L+2 by ring] at hhigh
  linarith

/-- Normalized quantitative form, for arbitrary admissible integer parameters. -/
theorem closeInputs_ratio_bound {K k t L : ℕ} (hK0 : 0 < K) (hK : k ≤ K)
    (hk : 2 ≤ k) (ht : 0 < t) (hLt : 2*(L+2) ≤ t) :
    ((closeInputs L (2^t)).card:ℝ)/(2:ℝ)^t ≤
      2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+8*(K+2:ℕ)/t +
      128*(L+1:ℕ)/K + 32*(sieveExponent k+L+3:ℕ)/t +
      144*(Real.exp 1)^2*(t+1:ℕ)*(L+2:ℕ)/(Real.log ((2^k:ℕ):ℝ))^2 := by
  have hc := closeInputs_card_bound hK0 hK hk ht hLt
  have hs := smoothInputs_card_bound ht K
  have h0 : (0:ℝ) < (2:ℝ)^t := by positivity
  have hs0 : 0 < Real.sqrt ((2:ℝ)^t) := Real.sqrt_pos.mpr h0
  have hsq := Real.sq_sqrt h0.le
  apply (div_le_iff₀ h0).mpr
  calc
    _ ≤ 2*(Real.sqrt ((2:ℝ)^t)+1+4*(2:ℝ)^t*(K+2:ℕ)/t) +
        128*(L+1:ℕ)*(2:ℝ)^t/K + 32*(2:ℝ)^t*(sieveExponent k+L+3:ℕ)/t +
        144*(Real.exp 1)^2*(2:ℝ)^t*(t+1:ℕ)*(L+2:ℕ)/(Real.log ((2^k:ℕ):ℝ))^2 := by linarith
    _ = _ := by
      have he : (2:ℝ)^t/Real.sqrt ((2:ℝ)^t) = Real.sqrt ((2:ℝ)^t) := by
        rw [div_eq_iff hs0.ne']; nlinarith
      rw [← hsq]
      simp only [Real.sqrt_sq hs0.le]
      field_simp
      ring

noncomputable def sieveConstant : ℝ := 144*(Real.exp 1)^2/(Real.log 2)^2

lemma sieveConstant_nonneg : 0 ≤ sieveConstant := by unfold sieveConstant; positivity

lemma closeInputs_simplified {k t L : ℕ} (hk : 2 ≤ k) (ht : 0 < t)
    (hLt : 2*(L+2) ≤ t) :
    ((closeInputs L (2^t)).card:ℝ)/(2:ℝ)^t ≤
      2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+648*(k:ℝ)/t + 32*(L+44:ℕ)/t +
      128*(L+1:ℕ)/k + sieveConstant*(t+1:ℕ)*(L+2:ℕ)/(k:ℝ)^2 := by
  have hb := closeInputs_ratio_bound (by omega : 0<k) le_rfl hk ht hLt
  apply hb.trans
  have he : 144*(Real.exp 1)^2*(t+1:ℕ)*(L+2:ℕ)/(Real.log ((2^k:ℕ):ℝ))^2 =
      sieveConstant*(t+1:ℕ)*(L+2:ℕ)/(k:ℝ)^2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    unfold sieveConstant
    ring
  rw [he]
  unfold sieveExponent
  push_cast
  simp only [div_eq_mul_inv]
  have hh : 0 ≤ (t:ℝ)⁻¹ := by positivity
  nlinarith

lemma division_parameters {m t : ℕ} (hm : 0 < m) (ht : 2*m ≤ t) :
    2 ≤ t/m ∧ (t/m:ℕ) / (t:ℝ) ≤ 1/(m:ℝ) ∧
      1/((t/m:ℕ):ℝ) ≤ 2*(m:ℝ)/t := by
  have hk : 2 ≤ t/m := (Nat.le_div_iff_mul_le hm).mpr ht
  have ht0 : 0 < t := by omega
  have hm0 : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have ht0' : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  have hk0 : (0:ℝ) < (t/m:ℕ) := Nat.cast_pos.mpr (by omega)
  refine ⟨hk, ?_, ?_⟩
  · apply (div_le_div_iff₀ ht0' hm0).mpr
    norm_num
    have he := Nat.div_mul_le_self t m
    exact_mod_cast he
  · apply (div_le_div_iff₀ hk0 ht0').mpr
    norm_num
    have htm : t < m*(t/m+1) := Nat.lt_mul_div_succ t hm
    have hh : t ≤ 2*m*(t/m) := by nlinarith
    exact_mod_cast hh

noncomputable def remainderConstant (m : ℕ) : ℝ :=
  32+256*m+8*sieveConstant*(m:ℝ)^2

/-- A two-parameter form suited to taking the counting limit first and the
fixed scale parameter `m` to infinity afterwards. -/
theorem closeInputs_fixed_scale {m t L : ℕ} (hm : 0 < m) (ht : 2*m ≤ t)
    (hLt : 2*(L+2) ≤ t) :
    ((closeInputs L (2^t)).card:ℝ)/(2:ℝ)^t ≤
      2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+648/(m:ℝ) +
      remainderConstant m * (L+44:ℕ)/(t:ℝ) := by
  have hp := division_parameters hm ht
  have ht0 : 0 < t := by omega
  have ht0' : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  have htr : (1:ℝ) ≤ t := by exact_mod_cast ht0
  have hk0 : (0:ℝ) < (t/m:ℕ) := Nat.cast_pos.mpr (by omega)
  have hsc := sieveConstant_nonneg
  have hb := closeInputs_simplified hp.1 ht0 hLt
  have hmiddle : 648*((t/m:ℕ):ℝ)/t ≤ 648/(m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hp.2.1 (by norm_num : (0:ℝ) ≤ 648)
    simpa only [← mul_div_assoc, mul_one] using hh
  have hlow : 128*(L+1:ℕ)/((t/m:ℕ):ℝ) ≤ 256*(m:ℝ)*(L+44:ℕ)/t := by
    calc
      _ = 128*(L+1:ℕ)*(1/((t/m:ℕ):ℝ)) := by ring
      _ ≤ 128*(L+44:ℕ)*(2*(m:ℝ)/t) := by
        apply mul_le_mul _ hp.2.2 (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by omega : L+1≤L+44)) (by norm_num)
      _ = _ := by ring
  have hhigh : sieveConstant*(t+1:ℕ)*(L+2:ℕ)/((t/m:ℕ):ℝ)^2 ≤
      8*sieveConstant*(m:ℝ)^2*(L+44:ℕ)/t := by
    calc
      _ = sieveConstant*(t+1:ℕ)*(L+2:ℕ)*(1/((t/m:ℕ):ℝ))^2 := by ring
      _ ≤ sieveConstant*(2*(t:ℝ))*(L+44:ℕ)*(2*(m:ℝ)/t)^2 := by
        apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) hp.2.2 2) (by positivity) (by positivity)
        apply mul_le_mul _ (Nat.cast_le.mpr (by omega : L+2≤L+44)) (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ hsc
        exact_mod_cast (show t+1≤2*t by omega)
      _ = _ := by field_simp; ring
  apply hb.trans
  unfold remainderConstant
  simp only [div_eq_mul_inv] at hmiddle hlow hhigh ⊢
  nlinarith

open Filter
open scoped Topology

/-- Every sublinear logarithmic width has vanishing relative count. -/
theorem sublinear_width_count_tendsto (L : ℕ → ℕ)
    (hL : Tendsto (fun t => (L t:ℝ)/t) atTop (𝓝 0)) :
    Tendsto (fun t => ((closeInputs (L t) (2^t)).card:ℝ)/(2:ℝ)^t) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℕ => (2:ℝ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsqrt : Tendsto (fun t : ℕ => 2/Real.sqrt ((2:ℝ)^t)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hpow)).const_mul 2
  have hsmall : Tendsto (fun t : ℕ => 2/(2:ℝ)^t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hpow).const_mul 2
  have hwidth : Tendsto (fun t => ((L t+44:ℕ):ℝ)/t) atTop (𝓝 0) := by
    simpa [Nat.cast_add, Nat.cast_ofNat, add_div] using
      hL.add (tendsto_const_div_atTop_nhds_zero_nat 44)
  have hadmissible : ∀ᶠ t in atTop, 2*(L t+2) ≤ t := by
    have hh : Tendsto (fun t => 2*((L t:ℝ)/t)+4/(t:ℝ)) atTop (𝓝 0) := by
      simpa using (hL.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat 4)
    filter_upwards [eventually_gt_atTop 0, hh.eventually_lt_const (by norm_num : (0:ℝ)<1)] with t ht hh
    have he : 2*((L t:ℝ)/t)+4/(t:ℝ) = (2*((L t:ℝ)+2))/(t:ℝ) := by ring
    rw [he] at hh
    have ht0 : (0:ℝ)<t := Nat.cast_pos.mpr ht
    have hb := (div_lt_iff₀ ht0).mp hh
    have hb' : 2*((L t:ℝ)+2) ≤ (t:ℝ) := by linarith
    exact_mod_cast hb'
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m,hm,hmε⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat 648).eventually_lt_const (half_pos hε))).exists
  have herr : Tendsto (fun t => 2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+
      remainderConstant m*((L t+44:ℕ):ℝ)/t) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, add_zero, mul_zero] using
      (hsqrt.add hsmall).add (hwidth.const_mul (remainderConstant m))
  obtain ⟨t0,ht0⟩ := eventually_atTop.mp
    (hadmissible.and (herr.eventually_lt_const (half_pos hε)))
  refine ⟨max t0 (2*m), fun t ht => ?_⟩
  obtain ⟨hLt,he⟩ := ht0 t (le_trans (le_max_left _ _) ht)
  have hb := closeInputs_fixed_scale hm (le_trans (le_max_right _ _) ht) hLt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  linarith

/-- A fixed positive logarithmic window is narrow enough to contain fewer
than half of all comparisons, uniformly at sufficiently large dyadic scales. -/
theorem exists_fixed_window : ∃ Q : ℕ, 4 ≤ Q ∧ ∀ᶠ t : ℕ in atTop,
    2 ≤ t/Q ∧ ((closeInputs (t/Q) (2^t)).card:ℝ) ≤ (2:ℝ)^t/2 := by
  let m : ℕ := 5184
  let B := remainderConstant m
  have hB : 0 ≤ B := by dsimp [B,remainderConstant,sieveConstant]; positivity
  obtain ⟨Q,hQ⟩ := exists_nat_gt (max 4 (8*B))
  have hQ4 : (4:ℝ) < Q := (le_max_left _ _).trans_lt hQ
  have hQ0 : 0 < Q := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<4) hQ4)
  have hQ4' : 4 ≤ Q := by exact_mod_cast hQ4.le
  have hBQ : B/(Q:ℝ) < 1/8 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hQ0)).mpr
    have hh := (le_max_right _ _).trans_lt hQ
    linarith
  have hpow : Tendsto (fun t : ℕ => (2:ℝ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsqrt : Tendsto (fun t : ℕ => 2/Real.sqrt ((2:ℝ)^t)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hpow)).const_mul 2
  have hsmall : Tendsto (fun t : ℕ => 2/(2:ℝ)^t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hpow).const_mul 2
  have herr : Tendsto (fun t : ℕ => 2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+44*B/t) atTop (𝓝 0) := by
    simpa using (hsqrt.add hsmall).add (tendsto_const_div_atTop_nhds_zero_nat (44*B))
  refine ⟨Q,hQ4',?_⟩
  filter_upwards [eventually_ge_atTop (2*m), eventually_ge_atTop (2*Q),
    herr.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with t htm htQ herr
  have ht0 : 0 < t := by omega
  have ht0' : (0:ℝ) < t := Nat.cast_pos.mpr ht0
  have hL : 2 ≤ t/Q := (Nat.le_div_iff_mul_le hQ0).mpr htQ
  have hLt : 2*(t/Q+2) ≤ t := by
    have hmul := Nat.div_mul_le_self t Q
    have hh : 4*(t/Q) ≤ t := by nlinarith
    have ht8 : 8 ≤ t := by dsimp [m] at htm; omega
    omega
  have hb := closeInputs_fixed_scale (show 0 < m by norm_num [m]) htm hLt
  have hr : ((t/Q:ℕ):ℝ)/(t:ℝ) ≤ 1/(Q:ℝ) := (division_parameters hQ0 htQ).2.1
  have hm : (648:ℝ)/(m:ℝ)=1/8 := by norm_num [m]
  have he : B*((t/Q+44:ℕ):ℝ)/t ≤ B/(Q:ℝ)+44*B/t := by
    have hh := mul_le_mul_of_nonneg_left hr hB
    push_cast
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  change _ ≤ 2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+648/(m:ℝ)+B*(t/Q+44:ℕ)/t at hb
  rw [hm] at hb
  refine ⟨hL,?_⟩
  have hh : ((closeInputs (t/Q) (2^t)).card:ℝ)/(2:ℝ)^t ≤ 1/2 := by linarith
  have hp0 : (0:ℝ)<(2:ℝ)^t := by positivity
  have h := (div_le_iff₀ hp0).mp hh
  linarith

end Erdos371SelbergSeparation

#print axioms Erdos371SelbergSeparation.closeInputs_ratio_bound

#print axioms Erdos371SelbergSeparation.sublinear_width_count_tendsto

#print axioms Erdos371SelbergSeparation.exists_fixed_window
