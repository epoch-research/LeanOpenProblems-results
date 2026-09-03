import Submission.PrimeWinnerHarmonicFlux

/-! A certified negative INFINITE harmonic current at the prime seven.
Finite divisor-box enumeration is supplemented by an absolute Euler-product
remainder, so no completeness theorem for S-unit solutions is assumed.
This refutes an auxiliary positivity proposal, not Erdős 371. -/
namespace Erdos371
open Finset Filter
open scoped Topology Pointwise
set_option autoImplicit false

private def sevenBox : ℕ := 2^17 * 3^10 * 5^7 * 7^6
private def sevenPairs : Finset ℕ :=
  {6,7,14,20,27,35,48,49,63,125,224,2400,4374}

private lemma sevenBox_ne_zero : sevenBox ≠ 0 := by norm_num [sevenBox]
private lemma sevenBox_smooth : sevenBox ∈ Nat.smoothNumbers 8 := by decide +kernel

private lemma sevenBox_smoothReciprocal (n : ℕ) (hn : n ∣ sevenBox) :
    smoothReciprocal 7 n = 1/n := by
  exact if_pos (Nat.mem_smoothNumbers_of_dvd sevenBox_smooth hn)

private lemma sevenBox_sum_divisors :
    (∑ n ∈ sevenBox.divisors, n) = 311223981113330718888 := by
  have h1 : (2^17*3^10*5^7).Coprime (7^6) := by decide +kernel
  have h2 : (2^17*3^10).Coprime (5^7) := by decide +kernel
  have h3 : (2^17).Coprime (3^10) := by decide +kernel
  rw [sevenBox, h1.sum_divisors_mul, h2.sum_divisors_mul, h3.sum_divisors_mul]
  rw [Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 2),
    Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 3),
    Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 5),
    Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 7)]
  norm_num [sum_range_succ]

private lemma sevenBox_reciprocal_sum :
    (∑ n ∈ sevenBox.divisors, (1 : ℝ)/n) =
      311223981113330718888/71137851402240000000 := by
  have he := Nat.sum_div_divisors sevenBox (fun n => (n : ℝ))
  have hs : (∑ n ∈ sevenBox.divisors, (sevenBox : ℝ)/n) =
      (∑ n ∈ sevenBox.divisors, n : ℕ) := by
    rw [Nat.cast_sum, ← he]
    apply sum_congr rfl
    intro n hn
    exact (Nat.cast_div_charZero (Nat.mem_divisors.mp hn).1).symm
  have hz : (sevenBox : ℝ) ≠ 0 := by exact_mod_cast sevenBox_ne_zero
  have hm : (sevenBox : ℝ)*(∑ n ∈ sevenBox.divisors, (1 : ℝ)/n) =
      311223981113330718888 := by
    rw [mul_sum]
    simp only [mul_one_div]
    rw [hs, sevenBox_sum_divisors]
    norm_num
  apply (eq_div_iff (by norm_num : (71137851402240000000 : ℝ) ≠ 0)).mpr
  have hcast : (sevenBox : ℝ) = 71137851402240000000 := by norm_num [sevenBox]
  rw [hcast] at hm
  nlinarith

private lemma seven_smoothReciprocal_hasSum : HasSum (smoothReciprocal 7) (35/8) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖reciprocalNatHom p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp 8).2
  have hi := hasSum_subtype_iff_indicator.mp h
  have hprod : (∏ p ∈ (8 : ℕ).primesBelow, (1-reciprocalNatHom p)⁻¹) = (35/8 : ℝ) := by
    norm_num [Nat.primesBelow, prod_filter, prod_range_succ, reciprocalNatHom]
  rw [hprod] at hi
  convert hi using 1
  funext n
  simp only [smoothReciprocal, Set.indicator_apply, one_div]
  rfl

private noncomputable def sevenBoxTail (n : ℕ) : ℝ :=
  if n ∣ sevenBox then 0 else smoothReciprocal 7 n

private lemma sevenBoxTail_nonneg (n : ℕ) : 0 ≤ sevenBoxTail n := by
  unfold sevenBoxTail
  split_ifs
  · rfl
  · exact smoothReciprocal_nonneg 7 n

private lemma sevenBoxTail_summable : Summable sevenBoxTail := by
  convert (summable_smoothReciprocal 7).indicator {n | ¬n ∣ sevenBox} using 1
  funext n
  simp only [sevenBoxTail, Set.indicator_apply, Set.mem_setOf_eq, ite_not]

private lemma sevenBoxTail_tsum :
    (∑' n, sevenBoxTail n) = 908018401517/15682947840000000 := by
  classical
  let f : ℕ → ℝ := fun n => if n ∣ sevenBox then 1/n else 0
  have hz (n : ℕ) (hn : n ∉ sevenBox.divisors) : f n = 0 := by
    have hd : ¬n ∣ sevenBox := fun hd => hn (Nat.mem_divisors.mpr ⟨hd,sevenBox_ne_zero⟩)
    simp [f,hd]
  have hf : Summable f := summable_of_ne_finset_zero hz
  have hfs : (∑' n, f n) = 311223981113330718888/71137851402240000000 := by
    rw [tsum_eq_sum hz]
    calc
      _ = ∑ n ∈ sevenBox.divisors, (1 : ℝ)/n := by
        apply sum_congr rfl
        intro n hn
        simp [f,(Nat.mem_divisors.mp hn).1]
      _ = _ := sevenBox_reciprocal_sum
  have he : (fun n => f n+sevenBoxTail n) = smoothReciprocal 7 := by
    funext n
    by_cases hd : n ∣ sevenBox
    · simp [f,sevenBoxTail,hd,sevenBox_smoothReciprocal n hd]
    · simp [f,sevenBoxTail,hd]
  have ht := hf.tsum_add sevenBoxTail_summable
  rw [he,seven_smoothReciprocal_hasSum.tsum_eq,hfs] at ht
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma seven_box_certificate :
    ∀ (a : Fin 18) (b : Fin 11) (c : Fin 8) (d : Fin 7),
      (2^a.val*3^b.val*5^c.val*7^d.val+1) ∣ sevenBox →
      (7 ∣ 2^a.val*3^b.val*5^c.val*7^d.val ∨
        7 ∣ 2^a.val*3^b.val*5^c.val*7^d.val+1) →
      2^a.val*3^b.val*5^c.val*7^d.val ∈ sevenPairs := by
  decide +kernel

private lemma divisor_mul_split (m l n : ℕ) (h0 : m*l ≠ 0) (hn : n ∣ m*l) :
    ∃ u ∈ m.divisors, ∃ v ∈ l.divisors, u*v=n := by
  have hm := Nat.mem_divisors.mpr ⟨hn,h0⟩
  rw [Nat.divisors_mul] at hm
  exact Finset.mem_mul.mp hm

private lemma sevenBox_divisor_exponents (n : ℕ) (hn : n ∣ sevenBox) :
    ∃ (a : Fin 18) (b : Fin 11) (c : Fin 8) (d : Fin 7),
      n = 2^a.val*3^b.val*5^c.val*7^d.val := by
  obtain ⟨u,hu,v,hv,huv⟩ := divisor_mul_split (2^17*3^10*5^7) (7^6) n
    (by norm_num) hn
  obtain ⟨w,hw,x,hx,hwx⟩ := divisor_mul_split (2^17*3^10) (5^7) u
    (by norm_num) (Nat.mem_divisors.mp hu).1
  obtain ⟨y,hy,z,hz,hyz⟩ := divisor_mul_split (2^17) (3^10) w
    (by norm_num) (Nat.mem_divisors.mp hw).1
  obtain ⟨a,ha,rfl⟩ := (Nat.mem_divisors_prime_pow (by norm_num : Nat.Prime 2) 17).mp hy
  obtain ⟨b,hb,rfl⟩ := (Nat.mem_divisors_prime_pow (by norm_num : Nat.Prime 3) 10).mp hz
  obtain ⟨c,hc,rfl⟩ := (Nat.mem_divisors_prime_pow (by norm_num : Nat.Prime 5) 7).mp hx
  obtain ⟨d,hd,rfl⟩ := (Nat.mem_divisors_prime_pow (by norm_num : Nat.Prime 7) 6).mp hv
  refine ⟨⟨a,by omega⟩,⟨b,by omega⟩,⟨c,by omega⟩,⟨d,by omega⟩,?_⟩
  dsimp only
  rw [← huv, ← hwx, ← hyz]

private noncomputable def sevenBoxCut (n : ℕ) : ℝ :=
  if n ∣ sevenBox ∧ n+1 ∣ sevenBox then primeWinnerHarmonicTerm 7 n else 0

private lemma sevenBoxCut_support (n : ℕ) (hn : n ∉ sevenPairs) : sevenBoxCut n = 0 := by
  unfold sevenBoxCut
  split_ifs with hd
  · by_cases hw : primeWinner n = 7
    · have hp : 7 ∣ n ∨ 7 ∣ n+1 := by
        by_cases h : Nat.maxPrimeFac n ≤ Nat.maxPrimeFac (n+1)
        · have he : Nat.maxPrimeFac (n+1)=7 := by
            simpa only [primeWinner,max_eq_right h] using hw
          exact Or.inr (he ▸ Nat.maxPrimeFac_dvd)
        · have he : Nat.maxPrimeFac n=7 := by
            simpa only [primeWinner,max_eq_left (not_le.mp h).le] using hw
          exact Or.inl (he ▸ Nat.maxPrimeFac_dvd)
      obtain ⟨a,b,c,d,he⟩ := sevenBox_divisor_exponents n hd.1
      have hm := seven_box_certificate a b c d (he ▸ hd.2) (he ▸ hp)
      exact (hn (he ▸ hm)).elim
    · simp only [primeWinnerHarmonicTerm,if_neg hw]
  · rfl

private lemma sevenPairs_divide : ∀ n ∈ sevenPairs, n ∣ sevenBox ∧ n+1 ∣ sevenBox := by
  decide +kernel

private lemma sevenBoxCut_tsum : (∑' n, sevenBoxCut n) = -90077/214326000 := by
  rw [tsum_eq_sum sevenBoxCut_support]
  have he : (∑ n ∈ sevenPairs, sevenBoxCut n) =
      ∑ n ∈ sevenPairs, primeWinnerHarmonicTerm 7 n := by
    apply sum_congr rfl
    intro n hn
    exact if_pos (sevenPairs_divide n hn)
  rw [he]
  have hq : (∑ n ∈ sevenPairs, if primeWinner n=7 then
      (if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then (1 : ℚ) else -1)/(n : ℚ)
        else 0) = -90077/214326000 := by
    decide +kernel
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  simp only [Rat.cast_sum,apply_ite,Rat.cast_div,Rat.cast_natCast,Rat.cast_zero,
    Rat.cast_one,Rat.cast_neg,Rat.cast_ofNat] at hr
  simpa only [primeWinnerHarmonicTerm,factorSign,predicateSign] using hr

private lemma sevenBoxCut_error_bound (n : ℕ) :
    primeWinnerHarmonicTerm 7 n ≤ sevenBoxCut n+sevenBoxTail n+2*sevenBoxTail (n+1) := by
  have ht0 := sevenBoxTail_nonneg n
  have ht1 := sevenBoxTail_nonneg (n+1)
  by_cases hd : n ∣ sevenBox ∧ n+1 ∣ sevenBox
  · rw [sevenBoxCut,if_pos hd]
    linarith
  · rw [sevenBoxCut,if_neg hd,zero_add]
    by_cases hw : primeWinner n=7
    · by_cases hn : n=0
      · subst n
        simp only [primeWinnerHarmonicTerm,Nat.cast_zero,div_zero,ite_self]
        positivity
      have he : ‖primeWinnerHarmonicTerm 7 n‖ = 1/(n : ℝ) := by
        rw [primeWinnerHarmonicTerm,if_pos hw,norm_div,factorSign_norm,Real.norm_natCast]
      have hl : primeWinnerHarmonicTerm 7 n ≤ 1/(n : ℝ) := by
        rw [← he,Real.norm_eq_abs]
        exact le_abs_self _
      by_cases hdn : n ∣ sevenBox
      · have hdn1 : ¬n+1 ∣ sevenBox := fun h => hd ⟨hdn,h⟩
        rw [sevenBoxTail,if_pos hdn,sevenBoxTail,if_neg hdn1,zero_add,
          smoothReciprocal_of_maxPrimeFac_le 7 (n+1) (by omega) (hw ▸ le_max_right _ _)]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hb : (1 : ℝ)/n ≤ 2/(n+1 : ℝ) := by
          apply (div_le_div_iff₀ hn0 (by positivity)).mpr
          linarith
        push_cast
        simpa only [mul_one_div] using hl.trans hb
      · rw [sevenBoxTail,if_neg hdn,
          smoothReciprocal_of_maxPrimeFac_le 7 n hn (hw ▸ le_max_left _ _)]
        linarith
    · rw [primeWinnerHarmonicTerm,if_neg hw]
      positivity

/-- The infinite prime-seven harmonic current is strictly negative.
Unlike a finite partial-sum example, this includes a certified bound for
ALL omitted smooth pairs, via the finite reciprocal Euler product. -/
theorem primeWinnerHarmonicLimit_seven_neg : primeWinnerHarmonicLimit 7 < -1/5000 := by
  have hc : Summable sevenBoxCut := summable_of_ne_finset_zero sevenBoxCut_support
  have hs : Summable (fun n => sevenBoxTail (n+1)) :=
    (summable_nat_add_iff 1).mpr sevenBoxTail_summable
  have hzero : sevenBoxTail 0 = 0 := by
    simp [sevenBoxTail,smoothReciprocal,Nat.smoothNumbers]
  have hshift := sevenBoxTail_summable.sum_add_tsum_nat_add 1
  simp only [sum_range_one,hzero,zero_add] at hshift
  have ht := Summable.tsum_le_tsum sevenBoxCut_error_bound
    (summable_primeWinnerHarmonicTerm_norm 7).of_norm
    ((hc.add sevenBoxTail_summable).add (hs.mul_left 2))
  rw [(hc.add sevenBoxTail_summable).tsum_add (hs.mul_left 2),
    hc.tsum_add sevenBoxTail_summable,hs.tsum_mul_left 2,
    hshift,sevenBoxCut_tsum,sevenBoxTail_tsum] at ht
  change primeWinnerHarmonicLimit 7 ≤ _ at ht
  exact ht.trans_lt (by norm_num)

/-- Thus nonnegative divergence cannot be strengthened to nonnegative
individual winner currents even AFTER taking the fixed-prime limit. -/
theorem not_primeWinnerHarmonicLimit_nonneg :
    ¬∀ p : ℕ, p.Prime → 0 ≤ primeWinnerHarmonicLimit p := by
  intro h
  have hp := h 7 (by norm_num)
  linarith [primeWinnerHarmonicLimit_seven_neg]

#print axioms primeWinnerHarmonicLimit_seven_neg
#print axioms not_primeWinnerHarmonicLimit_nonneg
end Erdos371
