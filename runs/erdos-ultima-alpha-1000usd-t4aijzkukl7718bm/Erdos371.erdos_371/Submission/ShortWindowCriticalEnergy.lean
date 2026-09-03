import Submission.ShortSeparationCollisionRemoval

/-! Critical loser energy on a short ordinary interval. Same-sign label
fibers are p-spaced, and opposite-sign cross terms can be discarded for an
upper bound. No cancellation on fixed-ratio windows is concluded. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma same_sign_loser_dvd_sub (n m : ℕ) (hp : primeLoser n=primeLoser m)
    (hs : factorSign n=factorSign m) : primeLoser n ∣ m-n := by
  by_cases hn : Nat.maxPrimeFac n<Nat.maxPrimeFac (n+1) <;>
    by_cases hm : Nat.maxPrimeFac m<Nat.maxPrimeFac (m+1)
  · have he : Nat.maxPrimeFac n=Nat.maxPrimeFac m := by
      simpa only [primeLoser,min_eq_left hn.le,min_eq_left hm.le] using hp
    have hd : Nat.maxPrimeFac n ∣ m := by rw [he]; exact Nat.maxPrimeFac_dvd
    simpa only [primeLoser,min_eq_left hn.le] using Nat.dvd_sub hd (Nat.maxPrimeFac_dvd (n := n))
  · norm_num [factorSign,predicateSign,hn,hm] at hs
  · norm_num [factorSign,predicateSign,hn,hm] at hs
  · have he : Nat.maxPrimeFac (n+1)=Nat.maxPrimeFac (m+1) := by
      simpa only [primeLoser,min_eq_right (not_lt.mp hn),min_eq_right (not_lt.mp hm)] using hp
    have hd : Nat.maxPrimeFac (n+1) ∣ m+1 := by rw [he]; exact Nat.maxPrimeFac_dvd
    have h := Nat.dvd_sub hd (Nat.maxPrimeFac_dvd (n := n+1))
    simpa only [primeLoser,min_eq_right (not_lt.mp hn),Nat.add_sub_add_right] using h

/-- A p-spaced set in an interval has weighted cardinality at most the
interval length plus p. This includes p=0 without division by zero. -/
lemma spaced_interval_label_card (S : Finset ℕ) (L U p : ℕ)
    (hS : S⊆Ico L U) (hspace : ∀ n∈S, ∀ m∈S, p ∣ m-n) :
    p*S.card ≤ (U-L)+p := by
  by_cases hp : p=0
  · subst p
    simp only [zero_mul,add_zero]
    omega
  have hp0 : 0<p := Nat.pos_of_ne_zero hp
  by_cases hne : S.Nonempty
  · let a := S.min' hne
    have ha : a∈S := S.min'_mem hne
    have haL := (mem_Ico.mp (hS ha)).1
    have hcard : S.card ≤ ((U-L)/p+1) := by
      have hi := card_le_card_of_injOn (fun n => (n-a)/p) (s := S)
        (t := range ((U-L)/p+1)) (by
          intro n hn
          have hnU := (mem_Ico.mp (hS hn)).2
          apply mem_range.mpr
          have hd : n-a ≤ U-L := by omega
          have hdiv : (n-a)/p ≤ (U-L)/p := Nat.div_le_div_right hd
          dsimp only
          omega)
        (by
          intro n hn m hm he
          have han : a ≤ n := S.min'_le n hn
          have ham : a ≤ m := S.min'_le m hm
          have hnd := Nat.div_mul_cancel (hspace a ha n hn)
          have hmd := Nat.div_mul_cancel (hspace a ha m hm)
          dsimp only at he
          have he' := congrArg (fun k : ℕ => k*p) he
          dsimp only at he'
          rw [hnd,hmd] at he'
          omega)
      simpa only [card_range] using hi
    have hh := Nat.mul_le_mul_left p hcard
    have hd := Nat.mul_div_le (U-L) p
    nlinarith
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [he,card_empty,mul_zero]
    omega

lemma interval_loser_same_sign_card (L U p : ℕ) (s : ℝ) :
    p*(((Ico L U).filter (fun n => primeLoser n=p ∧ factorSign n=s)).card)  ≤  (U-L)+p := by
  apply spaced_interval_label_card _ L U p (filter_subset _ _)
  intro n hn m hm
  obtain ⟨_,hnp,hns⟩ := mem_filter.mp hn
  obtain ⟨_,hmp,hms⟩ := mem_filter.mp hm
  simpa only [hnp] using same_sign_loser_dvd_sub n m (hnp.trans hmp.symm) (hns.trans hms.symm)

lemma factorSign_eq_neg_one_of_ne_one (n : ℕ) (h : factorSign n≠1) : factorSign n= -1 := by
  unfold factorSign predicateSign at *
  split_ifs at * <;> norm_num at *

lemma reciprocal_sum_sq_le_card (S : Finset ℕ) :
    (∑ n ∈ S, (1 : ℝ)/n)^2 ≤ (S.card : ℝ)*∑ n ∈ S, (1 : ℝ)/(n : ℝ)^2 := by
  have h := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => (1 : ℝ)/n)
  simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,div_pow] using h

lemma interval_primeLoser_weighted_square_bound (L U p : ℕ) :
    (p : ℝ)*(∑ n ∈ (Ico L U).filter (fun n => primeLoser n=p), factorSign n/n)^2  ≤ 
      ((U-L : ℕ)+p : ℝ)*
        ∑ n ∈ (Ico L U).filter (fun n => primeLoser n=p), (1 : ℝ)/(n : ℝ)^2 := by
  let S := (Ico L U).filter fun n => primeLoser n=p
  let A := S.filter fun n => factorSign n=1
  let B := S.filter fun n => ¬factorSign n=1
  let a : ℝ := ∑ n ∈ A, (1 : ℝ)/n
  let b : ℝ := ∑ n ∈ B, (1 : ℝ)/n
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA : p*A.card ≤ (U-L)+p := by
    simpa only [A,S,filter_filter] using interval_loser_same_sign_card L U p 1
  have hB : p*B.card ≤ (U-L)+p := by
    have he : B=(Ico L U).filter (fun n => primeLoser n=p ∧ factorSign n= -1) := by
      ext n
      simp only [B,S,mem_filter]
      constructor
      · rintro ⟨⟨hn,hp⟩,hs⟩
        exact ⟨hn,hp,factorSign_eq_neg_one_of_ne_one n hs⟩
      · rintro ⟨hn,hp,hs⟩
        exact ⟨⟨hn,hp⟩,by rw [hs]; norm_num⟩
    rw [he]
    exact interval_loser_same_sign_card L U p (-1)
  have he : (∑ n ∈ S, factorSign n/n)=a-b := by
    calc
      _ = ∑ n ∈ S, if factorSign n=1 then (1 : ℝ)/n else -(1/(n : ℝ)) := by
        apply sum_congr rfl
        intro n _
        by_cases hn : factorSign n=1
        · rw [if_pos hn,hn]
        · rw [if_neg hn,factorSign_eq_neg_one_of_ne_one n hn]
          ring
      _ = _ := by rw [sum_ite,sum_neg_distrib]; rfl
  have hsq : (a-b)^2 ≤ a^2+b^2 := by nlinarith [mul_nonneg ha hb]
  have hpa : (p : ℝ)*a^2 ≤ ((U-L : ℕ)+p : ℝ)*∑ n ∈ A, (1 : ℝ)/(n : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left (reciprocal_sum_sq_le_card A) (Nat.cast_nonneg (α := ℝ) p)
    have hc : (p : ℝ)*A.card ≤ ((U-L : ℕ)+p : ℝ) := by exact_mod_cast hA
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ ∑ n ∈ A, (1 : ℝ)/(n : ℝ)^2 by positivity)
    dsimp only [a]
    nlinarith
  have hpb : (p : ℝ)*b^2 ≤ ((U-L : ℕ)+p : ℝ)*∑ n ∈ B, (1 : ℝ)/(n : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left (reciprocal_sum_sq_le_card B) (Nat.cast_nonneg (α := ℝ) p)
    have hc : (p : ℝ)*B.card ≤ ((U-L : ℕ)+p : ℝ) := by exact_mod_cast hB
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ ∑ n ∈ B, (1 : ℝ)/(n : ℝ)^2 by positivity)
    dsimp only [b]
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) p)
  have hsum := sum_filter_add_sum_filter_not S (fun n => factorSign n=1) (fun n => (1 : ℝ)/(n : ℝ)^2)
  change (∑ n ∈ A, (1 : ℝ)/(n : ℝ)^2)+(∑ n ∈ B, (1 : ℝ)/(n : ℝ)^2)=_ at hsum
  change (p : ℝ)*(∑ n ∈ S, factorSign n/n)^2 ≤ _
  rw [he,← hsum,mul_add]
  nlinarith

noncomputable def intervalPrimeLoserCriticalEnergy (L U : ℕ) : ℝ :=
  ∑ p ∈ range (U+1), (p : ℝ)*(rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L)^2

lemma intervalPrimeLoserCriticalEnergy_nonneg (L U : ℕ) :
    0 ≤ intervalPrimeLoserCriticalEnergy L U := by
  unfold intervalPrimeLoserCriticalEnergy
  positivity

/-- The loss consists of a summable diagonal and a QUADRATIC relative
window length. This does not imply decay for U=2L. -/
theorem intervalPrimeLoserCriticalEnergy_bound (L U : ℕ) (hL : 0<L) (hLU : L ≤ U) :
    intervalPrimeLoserCriticalEnergy L U  ≤ 
      (∑ n ∈ Ico L U, primeLoserHarmonicDiagonal n)+((U-L : ℕ) : ℝ)^2/(L : ℝ)^2 := by
  let H := U-L
  have hraw (p : ℕ) : rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L =
      ∑ n ∈ (Ico L U).filter (fun n => primeLoser n=p), factorSign n/n := by
    unfold rawPrimeLoserHarmonic
    rw [← sum_Ico_eq_sub _ hLU,sum_filter]
    rfl
  have hmap : ∀ n∈Ico L U, primeLoser n∈range (U+1) := by
    intro n hn
    have hnU := (mem_Ico.mp hn).2
    have hp : primeLoser n ≤ n := (min_le_left (Nat.maxPrimeFac n) _).trans Nat.maxPrimeFac_le
    exact mem_range.mpr (by omega)
  have hsum : (∑ p ∈ range (U+1), ((H+p : ℕ) : ℝ)*
      ∑ n ∈ (Ico L U).filter (fun n => primeLoser n=p), (1 : ℝ)/(n : ℝ)^2) =
      ∑ n ∈ Ico L U, ((H+primeLoser n : ℕ) : ℝ)/(n : ℝ)^2 := by
    rw [← sum_fiberwise_of_maps_to hmap (fun n => ((H+primeLoser n : ℕ) : ℝ)/(n : ℝ)^2)]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [(mem_filter.mp hn).2]
    ring
  have hfirst : intervalPrimeLoserCriticalEnergy L U  ≤ 
      ∑ n ∈ Ico L U, ((H+primeLoser n : ℕ) : ℝ)/(n : ℝ)^2 := by
    rw [← hsum,intervalPrimeLoserCriticalEnergy]
    apply sum_le_sum
    intro p _
    rw [hraw]
    simpa only [Nat.cast_add,H] using interval_primeLoser_weighted_square_bound L U p
  have hsecond : (∑ n ∈ Ico L U, (H : ℝ)/(n : ℝ)^2) ≤ (H : ℝ)^2/(L : ℝ)^2 := by
    calc
      _  ≤  ∑ _n ∈ Ico L U, (H : ℝ)/(L : ℝ)^2 := by
        apply sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg H) (sq_pos_of_pos (by exact_mod_cast hL))
        exact pow_le_pow_left₀ (Nat.cast_nonneg L) (by exact_mod_cast (mem_Ico.mp hn).1) 2
      _ = _ := by rw [sum_const,Nat.card_Ico,nsmul_eq_mul]; dsimp [H]; ring
  have he : (∑ n ∈ Ico L U, ((H+primeLoser n : ℕ) : ℝ)/(n : ℝ)^2) =
      (∑ n ∈ Ico L U, (H : ℝ)/(n : ℝ)^2)+∑ n ∈ Ico L U, primeLoserHarmonicDiagonal n := by
    simp only [Nat.cast_add,add_div,sum_add_distrib,primeLoserHarmonicDiagonal]
  rw [he] at hfirst
  change _ ≤ _+(H : ℝ)^2/(L : ℝ)^2
  linarith

lemma intervalLoserDiagonal_le_tail (L U : ℕ) :
    (∑ n ∈ Ico L U, primeLoserHarmonicDiagonal n) ≤
      ∑' j, primeLoserHarmonicDiagonal (j+L) := by
  rw [sum_Ico_eq_sum_range]
  have hs : Summable (fun j => primeLoserHarmonicDiagonal (j+L)) :=
    (summable_nat_add_iff L).mpr summable_primeLoserHarmonicDiagonal
  simpa only [Nat.add_comm] using hs.sum_le_tsum (range (U-L))
    (fun j _ => primeLoserHarmonicDiagonal_nonneg (j+L))

/-- The diagonal error is small uniformly over EVERY upper endpoint.
The quadratic relative-length term is retained, not declared small. -/
theorem intervalPrimeLoserCriticalEnergy_uniform_error (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ L : ℕ in atTop, ∀ U : ℕ, L ≤ U →
      intervalPrimeLoserCriticalEnergy L U ≤ ε+((U-L : ℕ) : ℝ)^2/(L : ℝ)^2 := by
  filter_upwards [primeLoserHarmonicDiagonal_tail_zero.eventually_lt_const hε,
    eventually_gt_atTop (0 : ℕ)] with L htail hL
  intro U hLU
  have hd := (intervalLoserDiagonal_le_tail L U).trans htail.le
  exact (intervalPrimeLoserCriticalEnergy_bound L U hL hLU).trans (add_le_add hd le_rfl)

/-- Unnormalized critical loser energy vanishes on EVERY interval whose
length is sublinear in its lower endpoint. Fixed-ratio windows are excluded. -/
theorem intervalPrimeLoserCriticalEnergy_sublinear_zero (L U : ℕ → ℕ)
    (hL : Tendsto L atTop atTop) (hLU : ∀ j, L j ≤ U j)
    (hshort : Tendsto (fun j => ((U j-L j : ℕ) : ℝ)/(L j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => intervalPrimeLoserCriticalEnergy (L j) (U j)) atTop (𝓝 0) := by
  have hU : Tendsto U atTop atTop := tendsto_atTop_mono hLU hL
  have ht := summable_primeLoserHarmonicDiagonal.hasSum.tendsto_sum_nat
  have hd := (ht.comp hU).sub (ht.comp hL)
  simp only [sub_self] at hd
  have hdiag : Tendsto (fun j => ∑ n ∈ Ico (L j) (U j), primeLoserHarmonicDiagonal n)
      atTop (𝓝 0) := by
    apply hd.congr
    intro j
    exact (sum_Ico_eq_sub primeLoserHarmonicDiagonal (hLU j)).symm
  have hs := hdiag.add (hshort.pow 2)
  simp only [zero_pow (by norm_num : (2 : ℕ)≠0),add_zero,div_pow] at hs
  apply squeeze_zero' (Eventually.of_forall (fun j => intervalPrimeLoserCriticalEnergy_nonneg _ _)) _ hs
  filter_upwards [hL.eventually_gt_atTop 0] with j hj
  exact intervalPrimeLoserCriticalEnergy_bound (L j) (U j) hj (hLU j)

#print axioms intervalPrimeLoserCriticalEnergy_uniform_error
#print axioms intervalPrimeLoserCriticalEnergy_sublinear_zero
#print axioms same_sign_loser_dvd_sub
#print axioms interval_primeLoser_weighted_square_bound
#print axioms intervalPrimeLoserCriticalEnergy_bound
end Erdos371
