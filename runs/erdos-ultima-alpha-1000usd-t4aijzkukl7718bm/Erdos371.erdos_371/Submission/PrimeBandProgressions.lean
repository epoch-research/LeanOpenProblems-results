import Submission.UpperHalfSmoothSkew

/-! Exact arithmetic-progression form of the upper-half prime-band skew.
The opposite-residue prime discrepancy is not estimated here. -/

namespace Erdos371
open Finset

/-- The minus flag selects multiples one above a multiple of p. -/
def cofactorResidueCount (X p q : ℕ) (minus : Bool) : ℕ :=
  ((Icc 1 (X/q)).filter fun b => p ∣ if minus then b*q-1 else b*q+1).card

lemma bilinearCount_cofactor_positive (N p q : ℕ) (hq : 2 ≤ q) :
    bilinearCount N p q = cofactorResidueCount (N+1) p q true := by
  unfold bilinearCount cofactorResidueCount
  simp only [if_true]
  apply card_bij (fun n _ => (n+2)/q)
  · intro n hn
    obtain ⟨hn,hp,hqd⟩ := mem_filter.mp hn
    have hn := mem_range.mp hn
    have he := Nat.div_mul_cancel hqd
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · have hle := Nat.le_of_dvd (by omega : 0 < n+2) hqd
      exact Nat.div_pos hle (by omega)
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < q)).mpr
      omega
    · simpa only [he,show n+2-1=n+1 by omega] using hp
  · intro n hn m hm he
    have hnd := (mem_filter.mp hn).2.2
    have hmd := (mem_filter.mp hm).2.2
    have he' := congrArg (fun b => b*q) he
    dsimp at he'
    rw [Nat.div_mul_cancel hnd,Nat.div_mul_cancel hmd] at he'
    omega
  · intro b hb
    obtain ⟨hb,hp⟩ := mem_filter.mp hb
    obtain ⟨hb0,hbX⟩ := mem_Icc.mp hb
    have hsize := (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hbX
    have hprod : 2 ≤ b*q := by nlinarith
    have he : b*q-2+2=b*q := by omega
    have hn : b*q-2 ∈ (range N).filter (fun n => p ∣ n+1 ∧ q ∣ n+2) := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega),?_,?_⟩
      · simpa only [show b*q-2+1=b*q-1 by omega] using hp
      · rw [he]
        exact dvd_mul_left q b
    refine ⟨b*q-2,hn,?_⟩
    dsimp
    rw [he,Nat.mul_div_cancel _ (by omega)]

lemma bilinearCount_cofactor_negative (N p q : ℕ) (hq : 0 < q) :
    bilinearCount N q p = cofactorResidueCount N p q false := by
  unfold bilinearCount cofactorResidueCount
  simp only [Bool.false_eq_true, if_false]
  apply card_bij (fun n _ => (n+1)/q)
  · intro n hn
    obtain ⟨hn,hqd,hp⟩ := mem_filter.mp hn
    have hn := mem_range.mp hn
    have he := Nat.div_mul_cancel hqd
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hqd) hq
    · apply (Nat.le_div_iff_mul_le hq).mpr
      omega
    · simpa only [he,show n+1+1=n+2 by omega] using hp
  · intro n hn m hm he
    have hnd := (mem_filter.mp hn).2.1
    have hmd := (mem_filter.mp hm).2.1
    have he' := congrArg (fun b => b*q) he
    dsimp at he'
    rw [Nat.div_mul_cancel hnd,Nat.div_mul_cancel hmd] at he'
    omega
  · intro b hb
    obtain ⟨hb,hp⟩ := mem_filter.mp hb
    obtain ⟨hb0,hbX⟩ := mem_Icc.mp hb
    have hsize := (Nat.le_div_iff_mul_le hq).mp hbX
    have hprod : 1 ≤ b*q := by nlinarith
    have he : b*q-1+1=b*q := by omega
    have hn : b*q-1 ∈ (range N).filter (fun n => q ∣ n+1 ∧ p ∣ n+2) := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega),?_,?_⟩
      · rw [he]
        exact dvd_mul_left q b
      · simpa only [show b*q-1+2=b*q+1 by omega] using hp
    refine ⟨b*q-1,hn,?_⟩
    dsimp
    rw [he,Nat.mul_div_cancel _ hq]

/-- Prime counts with bq congruent to +1 (minus=true) or -1
(minus=false) modulo p. The two signs use the same prime interval. -/
def oppositePrimeCount (C X p b : ℕ) (minus : Bool) : ℕ :=
  ((Ioc C X).filter fun q => q.Prime ∧ p ∣ if minus then b*q-1 else b*q+1).card

lemma cofactorResidueCount_expand (X p q L : ℕ) (minus : Bool)
    (hq : 0 < q) (hL : X/q ≤ L) :
    cofactorResidueCount X p q minus =
      ∑ b ∈ Icc 1 L, if b*q ≤ X ∧ p ∣ (if minus then b*q-1 else b*q+1) then 1 else 0 := by
  rw [sum_boole,Nat.cast_id]
  unfold cofactorResidueCount
  congr 1
  ext b
  simp only [mem_filter,mem_Icc]
  constructor
  · rintro ⟨⟨hb0,hb⟩,hp⟩
    exact ⟨⟨hb0,hb.trans hL⟩,(Nat.le_div_iff_mul_le hq).mp hb,hp⟩
  · rintro ⟨⟨hb0,_⟩,hb,hp⟩
    exact ⟨⟨hb0,(Nat.le_div_iff_mul_le hq).mpr hb⟩,hp⟩

lemma oppositePrimeCount_expand (N C X p b : ℕ) (minus : Bool)
    (hX : X ≤ N+1) (hb : 0 < b) :
    oppositePrimeCount C (X/b) p b minus =
      ∑ q ∈ (range (N+2)).filter (fun q => q.Prime ∧ C < q),
        if b*q ≤ X ∧ p ∣ (if minus then b*q-1 else b*q+1) then 1 else 0 := by
  rw [sum_boole,Nat.cast_id]
  unfold oppositePrimeCount
  congr 1
  ext q
  simp only [mem_filter,mem_Ioc,mem_range]
  have hdiv : q ≤ X/b ↔ b*q ≤ X := by
    rw [Nat.le_div_iff_mul_le hb,mul_comm]
  constructor
  · rintro ⟨⟨hC,hqX⟩,hp,hres⟩
    have hqN := hqX.trans (Nat.div_le_self X b)
    exact ⟨⟨by omega,hp,hC⟩,hdiv.mp hqX,hres⟩
  · rintro ⟨⟨_,hp,hC⟩,hqX,hres⟩
    exact ⟨⟨hC,hdiv.mpr hqX⟩,hp,hres⟩

lemma sum_cofactorResidueCount (N C X p : ℕ) (minus : Bool) (hX : X ≤ N+1) :
    (∑ q ∈ (range (N+2)).filter (fun q => q.Prime ∧ C < q),
      cofactorResidueCount X p q minus) =
    ∑ b ∈ Icc 1 (X/(C+1)), oppositePrimeCount C (X/b) p b minus := by
  calc
    _ = ∑ q ∈ (range (N+2)).filter (fun q => q.Prime ∧ C < q),
        ∑ b ∈ Icc 1 (X/(C+1)),
          if b*q ≤ X ∧ p ∣ (if minus then b*q-1 else b*q+1) then 1 else 0 := by
      apply sum_congr rfl
      intro q hq
      obtain ⟨_,hp,hC⟩ := mem_filter.mp hq
      exact cofactorResidueCount_expand X p q _ minus hp.pos
        (Nat.div_le_div_left (by omega) (by omega))
    _ = ∑ b ∈ Icc 1 (X/(C+1)),
        ∑ q ∈ (range (N+2)).filter (fun q => q.Prime ∧ C < q),
          if b*q ≤ X ∧ p ∣ (if minus then b*q-1 else b*q+1) then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro b hb
      exact (oppositePrimeCount_expand N C X p b minus hX (mem_Icc.mp hb).1).symm

/-- Exact progressions form. The two endpoints differ because the original
positive orientation uses n+2 whereas the negative orientation uses n+1.
This identity does not assert cancellation of these prime counts. -/
theorem primeBandDiscrepancy_progressions (B C N : ℕ) :
    primeBandDiscrepancy B C N =
      ∑ p ∈ (range (N+2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C),
        ((∑ b ∈ Icc 1 ((N+1)/(C+1)),
          (oppositePrimeCount C ((N+1)/b) p b true : ℝ)) -
         (∑ b ∈ Icc 1 (N/(C+1)),
          (oppositePrimeCount C (N/b) p b false : ℝ))) := by
  unfold primeBandDiscrepancy
  apply sum_congr rfl
  intro p hp
  calc
    _ = ∑ q ∈ (range (N+2)).filter (fun q => q.Prime ∧ C < q),
        ((cofactorResidueCount (N+1) p q true : ℝ)-
          cofactorResidueCount N p q false) := by
      apply sum_congr rfl
      intro q hq
      have hqp := (mem_filter.mp hq).2.1
      rw [bilinearCount_cofactor_positive N p q hqp.two_le,
        bilinearCount_cofactor_negative N p q hqp.pos]
    _ = _ := by
      rw [sum_sub_distrib,← Nat.cast_sum,← Nat.cast_sum,
        sum_cofactorResidueCount N C (N+1) p true le_rfl,
        sum_cofactorResidueCount N C N p false (by omega)]
      simp only [Nat.cast_sum]

/-- In the upper-half regime every occurring cofactor is smaller than
both prime moduli. In particular these are invertible residue classes. -/
lemma progression_cofactor_coprime (B C N p b : ℕ) (hp : p.Prime)
    (hBp : B < p) (hBC : B ≤ C) (hsize : N+1 ≤ B^2)
    (hb : b ∈ Icc 1 ((N+1)/(C+1))) : p.Coprime b := by
  obtain ⟨hb0,hbN⟩ := mem_Icc.mp hb
  have hprod := (Nat.le_div_iff_mul_le (by omega : 0 < C+1)).mp hbN
  have hbB : b < B := by
    by_contra hn
    have hBb : B ≤ b := by omega
    have hprod' : B*(B+1) ≤ b*(C+1) := Nat.mul_le_mul hBb (by omega)
    nlinarith
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have := Nat.le_of_dvd hb0 hd
  omega

lemma dvd_sub_one_iff_zmod (p b q : ℕ) (hbq : 1 ≤ b*q) :
    p ∣ b*q-1 ↔ (b : ZMod p)*(q : ZMod p) = 1 := by
  rw [← Nat.modEq_iff_dvd' hbq,← ZMod.natCast_eq_natCast_iff 1 (b*q) p]
  simp only [Nat.cast_one,Nat.cast_mul,eq_comm]

lemma dvd_add_one_iff_zmod (p b q : ℕ) :
    p ∣ b*q+1 ↔ (b : ZMod p)*(q : ZMod p) = -1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,add_eq_zero_iff_eq_neg]

lemma zmod_unit_mul_eq (p b q : ℕ) (hbp : b.Coprime p) (r : ZMod p) :
    (b : ZMod p)*(q : ZMod p) = r ↔ (q : ZMod p) = (b : ZMod p)⁻¹*r := by
  have hmul := ZMod.coe_mul_inv_eq_one b hbp
  have hmul' : (b : ZMod p)⁻¹*(b : ZMod p) = 1 := by
    rw [mul_comm]
    exact hmul
  constructor
  · intro h
    calc
      (q : ZMod p) = ((b : ZMod p)⁻¹*(b : ZMod p))*(q : ZMod p) := by rw [hmul',one_mul]
      _ = (b : ZMod p)⁻¹*r := by rw [mul_assoc,h]
  · intro h
    rw [h,← mul_assoc,hmul,one_mul]

/-- Conventional residue-class prime counting on an interval. -/
def primeResidueClassCount (C X p : ℕ) (r : ZMod p) : ℕ :=
  ((Ioc C X).filter fun q : ℕ => q.Prime ∧ (q : ZMod p) = r).card

/-- The two classes are precisely the inverse and negative inverse of b.
No equidistribution of primes in these classes is asserted. -/
theorem oppositePrimeCount_residue_classes (C X p b : ℕ) (hb : 0 < b)
    (hbp : b.Coprime p) (minus : Bool) :
    oppositePrimeCount C X p b minus =
      primeResidueClassCount C X p (if minus then (b : ZMod p)⁻¹ else -(b : ZMod p)⁻¹) := by
  unfold oppositePrimeCount primeResidueClassCount
  congr 1
  ext q
  simp only [mem_filter]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hq
  cases minus with
  | false =>
    simp only [Bool.false_eq_true,if_false]
    rw [dvd_add_one_iff_zmod,zmod_unit_mul_eq p b q hbp]
    simp only [mul_neg,mul_one]
  | true =>
    simp only [if_true]
    rw [dvd_sub_one_iff_zmod p b q (by have := hq.pos; nlinarith),
      zmod_unit_mul_eq p b q hbp]
    simp only [mul_one]

#print axioms oppositePrimeCount_residue_classes
#print axioms primeBandDiscrepancy_progressions
#print axioms progression_cofactor_coprime
end Erdos371
