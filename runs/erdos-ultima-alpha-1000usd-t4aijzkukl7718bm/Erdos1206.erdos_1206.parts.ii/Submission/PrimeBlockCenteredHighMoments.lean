import Submission.SmallPrimeBlockMoments
import Submission.PrimePowerWindowMass
import Submission.PrimeBlockMeanOscillation

/-!
High-moment estimates combining a small-prime independent-model comparison
with a deterministic large-prime tail. No cubic separation is asserted.
-/
namespace Erdos1206.PrimeBlockCenteredHighMoments
open Finset PrimeBlockVariance SharpPrimeBlockVariance SmallPrimeBlockMoments
open scoped Classical

lemma prefix_mean_difference (P : Finset ℕ) (w : ℕ → ℝ) {T U : ℕ} (hTU : T ≤ U) :
    mean (P.filter (fun p => p ≤ U)) w-mean (P.filter (fun p => p ≤ T)) w=
      ∑ p∈P.filter (fun p => T < p ∧ p ≤ U),w p/p := by
  simp only [mean,sum_filter,←sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hT : p ≤ T
  · have hU := hT.trans hTU
    simp [hT,hU,show ¬T < p by omega]
  · by_cases hU : p ≤ U <;> simp [hT,hU,show T < p by omega]

lemma prefix_mean_difference_abs (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p∈P,|w p| ≤ 1) {T U : ℕ} (hTU : T ≤ U) :
    |mean (P.filter (fun p => p ≤ U)) w-mean (P.filter (fun p => p ≤ T)) w| ≤
      ∑ p∈P.filter (fun p => T < p ∧ p ≤ U),(1:ℝ)/p := by
  rw [prefix_mean_difference P w hTU]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  rw [abs_div,show |(p:ℝ)|=(p:ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
  exact div_le_div_of_nonneg_right (hw p (mem_filter.mp hp).1) (Nat.cast_nonneg p)

/-- A general prefix-center comparison lemma. The moment constant is uniform
in the prime block once the center differs by at most B*k from the small
prime center. -/
theorem prefix_moment_of_center_comparison (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1)
    {k N T : ℕ} (hk : 0 < k) (hTN : T^(2*k) ≤ N) (hNT : N < (T+1)^(2*k))
    {μ B : ℝ} (_hB : 0 ≤ B)
    (hcenter : |mean (P.filter (fun p => p ≤ T)) w-μ| ≤ B*k) :
    (∑ n∈Icc 1 N,(primeSum P w n-μ)^(2*k)) ≤
      (N:ℝ)*(16*max 12 ((B+2)^2)*(k:ℝ)*(mass P w+k))^k := by
  let S := P.filter (fun p => p ≤ T)
  let Q := P.filter (fun p => ¬p ≤ T)
  let M := mass P w
  let L := max 12 ((B+2)^2)
  let Z := L*(k:ℝ)*(M+k)
  have hM : 0 ≤ M := mass_nonneg P w
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hL : (0:ℝ) ≤ L := le_trans (by norm_num) (le_max_left _ _)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hS : ∀ p∈S,p.Prime := fun p hp => hP p (mem_filter.mp hp).1
  have hwS : ∀ p∈S,|w p| ≤ 1 := fun p hp => hw p (mem_filter.mp hp).1
  have hcard : S.card ≤ T := by
    have hs : S ⊆ Icc 1 T := fun p hp =>
      mem_Icc.mpr ⟨(hS p hp).pos,(mem_filter.mp hp).2⟩
    simpa using card_le_card hs
  have hsmall := small_moment_le S hS w hwS hk
    ((Nat.pow_le_pow_left hcard (2*k)).trans hTN)
  have hmass : mass S w ≤ M :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have hMS : 0 ≤ mass S w := mass_nonneg S w
  have hbase : 12*(k:ℝ)*(mass S w+k) ≤ Z := by
    dsimp [Z]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg k)
    · linarith
    · positivity
    · positivity
  have hsmallZ : (∑ n∈Icc 1 N,(primeSum S w n-mean S w)^(2*k)) ≤ 3*(N:ℝ)*Z^k := by
    apply hsmall.trans
    gcongr
  have hsplit (n : ℕ) : primeSum P w n=primeSum S w n+primeSum Q w n :=
    (sum_filter_add_sum_filter_not P (fun p => p ≤ T) (fun p => w p*indicator p n)).symm
  have htail (n : ℕ) (hn : n∈Icc 1 N) :
      |primeSum Q w n+mean S w-μ| ≤ (B+2)*k := by
    have hh := SmallPrimeBlockMoments.tail_abs_le Q w
      (fun p hp => ⟨hP p (mem_filter.mp hp).1,by have := (mem_filter.mp hp).2; omega⟩)
      (fun p hp => hw p (mem_filter.mp hp).1) (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hNT
    have he : primeSum Q w n+mean S w-μ=primeSum Q w n+(mean S w-μ) := by ring
    rw [he]
    have ht := abs_add_le (primeSum Q w n) (mean S w-μ)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
    dsimp only [S] at ht
    linarith
  have htailZ (n : ℕ) (hn : n∈Icc 1 N) :
      (primeSum Q w n+mean S w-μ)^(2*k) ≤ Z^k := by
    have he : Even (2*k) := even_two_mul k
    rw [←he.pow_abs]
    have ht := pow_le_pow_left₀ (abs_nonneg _) (htail n hn) (2*k)
    apply ht.trans
    rw [pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg _)
    dsimp [Z]
    have hcoef : (B+2)^2 ≤ L := le_max_right _ _
    have hkk : (k:ℝ)^2 ≤ (k:ℝ)*(M+k) := by nlinarith
    calc
      _ = (B+2)^2*(k:ℝ)^2 := mul_pow _ _ _
      _ ≤ L*((k:ℝ)*(M+k)) := mul_le_mul hcoef hkk (sq_nonneg _) hL
      _ = _ := by ring
  have hpoint (n : ℕ) (hn : n∈Icc 1 N) :
      (primeSum P w n-μ)^(2*k) ≤
        (4:ℝ)^k*((primeSum S w n-mean S w)^(2*k)+Z^k) := by
    have he : primeSum P w n-μ=(primeSum S w n-mean S w)+
        (primeSum Q w n+mean S w-μ) := by rw [hsplit]; ring
    rw [he]
    exact (even_add_le _ _ k).trans (mul_le_mul_of_nonneg_left
      (show (primeSum S w n-mean S w)^(2*k)+(primeSum Q w n+mean S w-μ)^(2*k) ≤
        (primeSum S w n-mean S w)^(2*k)+Z^k by linarith [htailZ n hn]) (by positivity))
  have hsum := sum_le_sum hpoint
  simp only [←mul_sum,sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hsum
  have hfour : (4:ℝ) ≤ (4:ℝ)^k := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (show 1 ≤ k from hk)
  calc
    _ ≤ (4:ℝ)^k*((∑ n∈Icc 1 N,(primeSum S w n-mean S w)^(2*k))+(N:ℝ)*Z^k) := hsum
    _ ≤ (4:ℝ)^k*(3*(N:ℝ)*Z^k+(N:ℝ)*Z^k) := by gcongr
    _ = (N:ℝ)*(4:ℝ)^k*4*Z^k := by ring
    _ ≤ (N:ℝ)*(4:ℝ)^k*(4:ℝ)^k*Z^k := by gcongr
    _ = _ := by
      rw [mul_assoc (N:ℝ),mul_assoc (N:ℝ),←mul_pow,←mul_pow]
      congr 2
      dsimp [Z,M,L]
      ring

#print axioms prefix_mean_difference_abs
#print axioms prefix_moment_of_center_comparison
end Erdos1206.PrimeBlockCenteredHighMoments
