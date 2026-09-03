import FormalConjecturesUtil
import Submission.CofactorRectangles
import Submission.ComparableHighProduct
import Submission.LogSmoothCount

/-! A quantitative unsigned separation bound with an aspect-ratio loss only
linear in its binary logarithm. No orientation density is asserted. -/

namespace Erdos371RectangleSeparation

open Finset Erdos371Cofactor Erdos371CofactorRectangles Erdos371CofactorSieve
open Erdos371ComparableLowProduct Erdos371ComparableHighProduct
open Erdos371PrimeHarmonicBlocks Erdos371SieveParameters Erdos371SieveScaleBands
open Erdos371BoundedPrimeGap

attribute [local instance] Classical.propDecidable

lemma mem_lowCover_external {n N A L K : ℕ} (hnN : n < N) (hn1 : 1 < n)
    (hratio : max (P n) (P (n+1)) ≤ 2^L * min (P n) (P (n+1)))
    (hprod : P n * P (n+1) ≤ A*N)
    (hlarge : 2^K ≤ min (P n) (P (n+1))) : n ∈ fullCover A L K (N+1) N := by
  let p := min (P n) (P (n+1))
  let q := max (P n) (P (n+1))
  let k := Nat.log 2 p
  let j := Nat.log 2 q
  have hp0 := Nat.prime_maxPrimeFac_of_one_lt n hn1
  have hq0 := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega : 1 < n+1)
  have hp : p.Prime := by dsimp [p]; rcases min_choice (P n) (P (n+1)) with h | h <;> rwa [h]
  have hq : q.Prime := by dsimp [q]; rcases max_choice (P n) (P (n+1)) with h | h <;> rwa [h]
  have hpk : p ∈ block k := block_of_log hp
  have hqj : q ∈ block j := block_of_log hq
  have hpq : p ≤ q := min_le_max
  have hkj : k ≤ j := Nat.log_mono_right hpq
  have hKk : K ≤ k := Nat.le_log_of_pow_le (by decide) hlarge
  have hkN : k < N+1 := by
    have hh := Nat.log_le_self 2 p
    have hpN : p ≤ N := (min_le_left _ _).trans (Nat.maxPrimeFac_le.trans hnN.le)
    dsimp [k]
    omega
  have hjk : j ≤ k+L := by
    have hqpow : 2^j ≤ q := (mem_block.mp hqj).2.1
    have hplt : p < 2^(k+1) := (mem_block.mp hpk).2.2
    have hmul := Nat.mul_lt_mul_of_pos_left hplt (Nat.two_pow_pos L)
    have hr : q ≤ 2^L*p := hratio
    have he : 2^L * 2^(k+1) = 2^(k+L+1) := by rw [← pow_add]; congr 1; omega
    rw [he] at hmul
    have ht : 2^j < 2^(k+L+1) := hqpow.trans_lt (hr.trans_lt hmul)
    have hh := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mp ht
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_Ico.mpr ⟨hKk, hkN⟩, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨j, Finset.mem_Icc.mpr ⟨hkj, hjk⟩, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨p, hpk, Finset.mem_biUnion.mpr ⟨q, hqj, ?_⟩⟩
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n+1) ≠ P n at hne
  have hneq : p ≠ q := by dsimp [p,q]; omega
  have hcop := (Nat.coprime_primes hp hq).mpr hneq
  have hpqN : p*q ≤ A*N := by
    dsimp [p,q]
    rw [min_mul_max]
    exact hprod
  rw [pairSolutions, if_pos ⟨hcop, hpqN⟩]
  have hpn : P n ∣ n := Nat.maxPrimeFac_dvd
  have hqn : P (n+1) ∣ n+1 := Nat.maxPrimeFac_dvd
  by_cases h : P n ≤ P (n+1)
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hnN, by simpa [p, min_eq_left h] using hpn,
      by simpa [q, max_eq_right h] using hqn⟩
  · have hh : P (n+1) ≤ P n := by omega
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hnN, by simpa [q, max_eq_left hh] using hpn,
      by simpa [p, min_eq_right hh] using hqn⟩


lemma log_ratio_bound {a b C : ℕ} (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 2^C*a) :
    Nat.log 2 a ≤ Nat.log 2 b ∧ Nat.log 2 b ≤ Nat.log 2 a+C := by
  refine ⟨Nat.log_mono_right hab, ?_⟩
  have hb : b < 2^(Nat.log 2 a+C+1) := by
    calc
      _ ≤ 2^C*a := hba
      _ < 2^C*2^(Nat.log 2 a+1) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_succ_log_self (by decide) a) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh := Nat.log_lt_of_lt_pow (show b ≠ 0 by omega) hb
  omega

lemma mem_highCover {n N k L t : ℕ} (hn : 1 < n) (hnN : n < N) (hN : N ≤ 2^t)
    (hr : max (P n) (P (n+1)) ≤ 2^L*min (P n) (P (n+1)))
    (hmin : cutoff k ≤ min (P n) (P (n+1)))
    (hprod : threshold k*N < P n*P (n+1)) :
    n ∈ diagonalCover k (L+1) t N := by
  let a := cofactor n
  let b := cofactor (n+1)
  have ha : 0 < a := cofactor_pos hn
  have hb : 0 < b := cofactor_pos (by omega : 1 < n+1)
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have han : a*P n=n := cofactor_mul n
  have hbn : b*P (n+1)=n+1 := cofactor_mul (n+1)
  have hratio := factor_cofactor_ratio ha hb hp.pos hq.pos (by omega : 0 < n) han hbn hr
  have hsmall : a*b*threshold k < n := cofactor_product_small ha hb han hbn
    ((Nat.mul_le_mul_left (threshold k) (by omega : n+1 ≤ N)).trans_lt hprod)
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
  have hmul : (2^i*2^j)*threshold k ≤ N :=
    ((Nat.mul_le_mul_right (threshold k) hAB).trans hsmall.le).trans hnN.le
  have hthr : 0 < threshold k := by unfold threshold cutoff; positivity
  have hABN : 2^i*2^j ≤ N := by nlinarith
  have hlarge : threshold k ≤ N/(2^i*2^j)+1 := by
    have hh := (Nat.le_div_iff_mul_le (by positivity : 0 < 2^i*2^j)).mpr
      (show threshold k*(2^i*2^j) ≤ N by nlinarith)
    omega
  have hc := factor_mem_cofactorInputs ha hb hp hq han hbn hnN
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

noncomputable def divisorInputs (p N : ℕ) : Finset ℕ :=
  ((range N).filter fun n => n ≠ 0 ∧ p ∣ n) ∪
    ((range N).filter fun n => p ∣ n+1)

lemma divisorInputs_card_bound (p N : ℕ) :
    (divisorInputs p N).card ≤ 2*(N:ℝ)/p := by
  have h1 : ((range N).filter fun n => n ≠ 0 ∧ p ∣ n).card ≤ N/p := by
    rw [← Nat.card_multiples' N p]
    exact card_le_card (filter_subset_filter _ (range_mono (by omega)))
  have h2 : ((range N).filter fun n => p ∣ n+1).card = N/p := Nat.card_multiples N p
  have hc := card_union_le ((range N).filter fun n => n ≠ 0 ∧ p ∣ n)
    ((range N).filter fun n => p ∣ n+1)
  have hh : (divisorInputs p N).card ≤ 2*(N/p) := by
    unfold divisorInputs
    omega
  calc
    _ ≤ 2*((N/p:ℕ):ℝ) := by exact_mod_cast hh
    _ ≤ 2*((N:ℝ)/p) := mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
    _ = _ := by ring

noncomputable def middleIndices (t E L : ℕ) : Finset ℕ :=
  (range (t+E+1)).filter fun j => t < 2*j+L+2 ∧ 2*j ≤ t+E

lemma middleIndices_card (t E L : ℕ) : (middleIndices t E L).card ≤ E+L+3 := by
  calc
    _ ≤ (range (E+L+3)).card := by
      apply card_le_card_of_injOn (fun j => 2*j+L+2-t)
      · intro j hj
        change j ∈ middleIndices t E L at hj
        have h := (mem_filter.mp hj).2
        exact mem_range.mpr (by change 2*j+L+2-t < E+L+3; omega)
      · intro i hi j hj he
        change i ∈ middleIndices t E L at hi
        change j ∈ middleIndices t E L at hj
        have hi := (mem_filter.mp hi).2.1
        have hj := (mem_filter.mp hj).2.1
        change 2*i+L+2-t=2*j+L+2-t at he
        omega
    _ = _ := card_range _

noncomputable def middleCover (t E L N : ℕ) : Finset ℕ :=
  (middleIndices t E L).biUnion fun j => (block j).biUnion fun p => divisorInputs p N

lemma middleCover_card_bound {t L : ℕ} (ht : 0 < t) (hLt : 2*(L+2) ≤ t) (E N : ℕ) :
    (middleCover t E L N).card ≤ 32*(N:ℝ)*(E+L+3:ℕ)/t := by
  have ht' : (0:ℝ) < t := Nat.cast_pos.mpr ht
  have hb (j : ℕ) (hj : j ∈ middleIndices t E L) : blockMass j ≤ 16/(t:ℝ) := by
    have hjt := (mem_filter.mp hj).2.1
    have hj0 : 0 < j := by omega
    have h4 : t ≤ 4*j := by omega
    apply (blockMass_le hj0).trans
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr hj0) ht').mpr
    exact_mod_cast (show 4*t ≤ 16*j by omega)
  have hc : (middleCover t E L N).card ≤
      ∑ j ∈ middleIndices t E L, ∑ p ∈ block j, (divisorInputs p N).card :=
    card_biUnion_le.trans (sum_le_sum (fun _ _ => card_biUnion_le))
  calc
    _ ≤ ∑ j ∈ middleIndices t E L, ∑ p ∈ block j, ((divisorInputs p N).card:ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ j ∈ middleIndices t E L, ∑ p ∈ block j, 2*(N:ℝ)/p :=
      sum_le_sum (fun _ _ => sum_le_sum (fun _ _ => divisorInputs_card_bound _ _))
    _ = 2*(N:ℝ)*∑ j ∈ middleIndices t E L, blockMass j := by
      simp only [blockMass, mul_sum]; congr 1; ext j; congr 1; ext p; ring
    _ ≤ 2*(N:ℝ)*∑ _j ∈ middleIndices t E L, 16/(t:ℝ) := by
      apply mul_le_mul_of_nonneg_left (sum_le_sum hb) (by positivity)
    _ = 32*(N:ℝ)*(middleIndices t E L).card/t := by simp; ring
    _ ≤ _ := by gcongr; exact_mod_cast middleIndices_card t E L

lemma mem_middleCover {n t k L : ℕ} (hn : 1 < n) (hnN : n < 2^t)
    (hr : max (P n) (P (n+1)) ≤ 2^L*min (P n) (P (n+1)))
    (hprod : 2^t < P n*P (n+1))
    (hprod' : P n*P (n+1) ≤ threshold k*2^t) :
    n ∈ middleCover t (exponent k) L (2^t) := by
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
  have hj2 : 2*j ≤ t+exponent k := by
    have hm : 2^j*2^j ≤ p*q := Nat.mul_le_mul hpow (hpow.trans min_le_max)
    have he : 2^j*2^j=2^(2*j) := by rw [← pow_add]; congr 1; omega
    rw [he,hpq] at hm
    rw [threshold_eq_pow, ← pow_add] at hprod'
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

noncomputable def smallInputs (K N : ℕ) : Finset ℕ :=
  (range N).filter fun n => P n ≤ 2^K ∨ P (n+1) ≤ 2^K

noncomputable def smoothInputs (K N : ℕ) : Finset ℕ :=
  (range (N+1)).filter fun n => P n ≤ 2^K

lemma smallInputs_card (K N : ℕ) :
    (smallInputs K N).card ≤ 2*(smoothInputs K N).card := by
  have h1 : ((range N).filter fun n => P n ≤ 2^K).card ≤ (smoothInputs K N).card :=
    card_le_card (filter_subset_filter _ (range_mono (by omega)))
  have h2 : ((range N).filter fun n => P (n+1) ≤ 2^K).card ≤ (smoothInputs K N).card := by
    apply card_le_card_of_injOn (fun n => n+1)
    · intro n hn
      change n ∈ (range N).filter (fun n => P (n+1) ≤ 2^K) at hn
      obtain ⟨hnN,hp⟩ := mem_filter.mp hn
      change n+1 ∈ smoothInputs K N
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (by have := mem_range.mp hnN; omega),hp⟩
    · intro n _ m _ h
      change n+1=m+1 at h
      omega
  have he : smallInputs K N = ((range N).filter fun n => P n ≤ 2^K) ∪
      ((range N).filter fun n => P (n+1) ≤ 2^K) := by
    ext n; simp [smallInputs, and_or_left]
  rw [he]
  have hc := card_union_le ((range N).filter fun n => P n ≤ 2^K)
    ((range N).filter fun n => P (n+1) ≤ 2^K)
  omega

noncomputable def closeInputs (L N : ℕ) : Finset ℕ :=
  (range N).filter fun n => max (P n) (P (n+1)) ≤ 2^L*min (P n) (P (n+1))

lemma closeInputs_subset {K k : ℕ} (hK : 2^k ≤ K) (t L : ℕ) :
    closeInputs L (2^t) ⊆ ((smallInputs K (2^t) ∪ fullCover 1 L K (2^t+1) (2^t)) ∪
      middleCover t (exponent k) L (2^t)) ∪ diagonalCover k (L+1) t (2^t) := by
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
  by_cases hmid : P n*P (n+1) ≤ threshold k*2^t
  · exact mem_union_left _ (mem_union_right _ (mem_middleCover hn1 hnN' hr (by omega) hmid))
  · exact mem_union_right _ (mem_highCover hn1 hnN' le_rfl hr
      ((Nat.pow_le_pow_right (by decide) hK).trans hlarge) (by omega))

/-- A finite, quantitative separation bound. The sieve term loses only `L+2`,
not a power of the multiplicative ratio `2^L`. -/
theorem closeInputs_card_bound {K k t L : ℕ} (hK0 : 0 < K) (hK : 2^k ≤ K)
    (ht : 0 < t) (hLt : 2*(L+2) ≤ t) :
    (closeInputs L (2^t)).card ≤
      2*((smoothInputs K (2^t)).card:ℝ) +
      128*(L+1:ℕ)*(2:ℝ)^t/K + 32*(2:ℝ)^t*(exponent k+L+3:ℕ)/t +
      96*(Real.exp 1)^2*(2:ℝ)^t*(t+1:ℕ)*(L+2:ℕ)/(4:ℝ)^k := by
  have hc := card_le_card (closeInputs_subset hK t L)
  have h1 := card_union_le
    ((smallInputs K (2^t) ∪ fullCover 1 L K (2^t+1) (2^t)) ∪ middleCover t (exponent k) L (2^t))
    (diagonalCover k (L+1) t (2^t))
  have h2 := card_union_le (smallInputs K (2^t) ∪ fullCover 1 L K (2^t+1) (2^t))
    (middleCover t (exponent k) L (2^t))
  have h3 := card_union_le (smallInputs K (2^t)) (fullCover 1 L K (2^t+1) (2^t))
  have h4 := smallInputs_card K (2^t)
  have hb : (closeInputs L (2^t)).card ≤ 2*(smoothInputs K (2^t)).card +
      (fullCover 1 L K (2^t+1) (2^t)).card + (middleCover t (exponent k) L (2^t)).card +
      (diagonalCover k (L+1) t (2^t)).card := by omega
  have hb' := Nat.cast_le (α := ℝ) |>.mpr hb
  push_cast at hb'
  have hlow := fullCover_card_bound hK0 1 L (2^t+1) (2^t)
  have hmid := middleCover_card_bound ht hLt (exponent k) (2^t)
  have hhigh := diagonalCover_card_bound k (L+1) t (2^t)
  push_cast at hlow hmid hhigh ⊢
  norm_num at hlow
  rw [show (L:ℝ)+1+1=L+2 by ring] at hhigh
  linarith

lemma smoothInputs_card_bound {t : ℕ} (ht : 0 < t) (K : ℕ) :
    (smoothInputs K (2^t)).card ≤
      Real.sqrt ((2:ℝ)^t)+1+4*(2:ℝ)^t*(K+2:ℕ)/t := by
  have hN : 1 < (2:ℕ)^t := Nat.one_lt_two_pow ht.ne'
  have hh := Erdos371LogSmoothCount.smooth_count_log_bound (Nat.two_pow_pos K) hN
  change ((smoothInputs K (2^t)).card:ℝ) ≤ _ at hh
  have hl2 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  push_cast at hh
  rw [Real.log_pow,Real.log_pow,hl2] at hh
  have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : 4*(2:ℝ)^t*((K:ℝ)*Real.log 2+2*Real.log 2)/((t:ℝ)*Real.log 2) =
      4*(2:ℝ)^t*(K+2:ℕ)/t := by push_cast; field_simp
  rwa [he] at hh

/-- Normalized quantitative form, for arbitrary admissible integer parameters. -/
theorem closeInputs_ratio_bound {K k t L : ℕ} (hK0 : 0 < K) (hK : 2^k ≤ K)
    (ht : 0 < t) (hLt : 2*(L+2) ≤ t) :
    ((closeInputs L (2^t)).card:ℝ)/(2:ℝ)^t ≤
      2/Real.sqrt ((2:ℝ)^t)+2/(2:ℝ)^t+8*(K+2:ℕ)/t +
      128*(L+1:ℕ)/K + 32*(exponent k+L+3:ℕ)/t +
      96*(Real.exp 1)^2*(t+1:ℕ)*(L+2:ℕ)/(4:ℝ)^k := by
  have hc := closeInputs_card_bound hK0 hK ht hLt
  have hs := smoothInputs_card_bound ht K
  have h0 : (0:ℝ) < (2:ℝ)^t := by positivity
  have hs0 : 0 < Real.sqrt ((2:ℝ)^t) := Real.sqrt_pos.mpr h0
  have hsq := Real.sq_sqrt h0.le
  apply (div_le_iff₀ h0).mpr
  calc
    _ ≤ 2*(Real.sqrt ((2:ℝ)^t)+1+4*(2:ℝ)^t*(K+2:ℕ)/t) +
        128*(L+1:ℕ)*(2:ℝ)^t/K + 32*(2:ℝ)^t*(exponent k+L+3:ℕ)/t +
        96*(Real.exp 1)^2*(2:ℝ)^t*(t+1:ℕ)*(L+2:ℕ)/(4:ℝ)^k := by linarith
    _ = _ := by
      have he : (2:ℝ)^t/Real.sqrt ((2:ℝ)^t) = Real.sqrt ((2:ℝ)^t) := by
        rw [div_eq_iff hs0.ne']; nlinarith
      rw [← hsq]
      simp only [Real.sqrt_sq hs0.le]
      field_simp
      ring

end Erdos371RectangleSeparation

#print axioms Erdos371RectangleSeparation.closeInputs_card_bound
#print axioms Erdos371RectangleSeparation.closeInputs_ratio_bound
