import Submission.ParityDiscrepancyCovariance

/-! Exact energy of the alternating-sign inclusion-exclusion profile.
All identities below are over complete prime-product periods. -/
namespace Erdos970.ParityDiscrepancy
open Finset

def primeProduct (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

def covarianceKernel (Q R : Finset ℕ) : ℚ :=
  (-1) ^ (Q.card + R.card) * (primeProduct (Q ∩ R) : ℚ) ^ 2 /
    ((primeProduct Q : ℚ) * primeProduct R)

def profile (P : Finset ℕ) (a : ℕ) : ℚ :=
  ∑ Q ∈ P.powerset, (-1) ^ Q.card * residueSign (primeProduct Q) a

lemma primeProduct_odd (P : Finset ℕ) (hP : ∀ p ∈ P, Odd p) : Odd (primeProduct P) := by
  induction P using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p P hp ih =>
    rw [primeProduct, prod_insert hp]
    exact (hP p (mem_insert_self _ _)).mul (ih (fun q hq => hP q (mem_insert_of_mem hq)))

lemma primeProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) : 0 < primeProduct P :=
  prod_pos hP

lemma primeProduct_inter_sdiff (Q R : Finset ℕ) :
    primeProduct (Q ∩ R) * primeProduct (Q \ R) = primeProduct Q := by
  simpa only [primeProduct, sdiff_inter_self_left, mul_comm] using
    (prod_sdiff (f := fun p : ℕ => p) (inter_subset_left (s₂ := R) (s₁ := Q)))

/-- The joint covariance depends only on the common prime factors. -/
theorem covariance_subsets (P Q R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (hQ : Q ⊆ P) (hR : R ⊆ P) :
    (∑ a ∈ range (primeProduct P), residueSign (primeProduct Q) a * residueSign (primeProduct R) a) =
      (primeProduct P : ℚ) * (primeProduct (Q ∩ R) : ℚ) ^ 2 /
        ((primeProduct Q : ℚ) * primeProduct R) := by
  let g := primeProduct (Q ∩ R)
  let d := primeProduct (Q \ R)
  let e := primeProduct (R \ Q)
  let t := primeProduct (P \ (Q ∪ R))
  have hod (A : Finset ℕ) (hA : A ⊆ P) : Odd (primeProduct A) :=
    primeProduct_odd A (fun p hp => (hP p (hA hp)).2)
  have hg : Odd g := hod _ (inter_subset_left.trans hQ)
  have hd : Odd d := hod _ (sdiff_subset.trans hQ)
  have he : Odd e := hod _ (sdiff_subset.trans hR)
  have hde : d.Coprime e := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes (hP p (hQ (mem_sdiff.mp hp).1)).1
      (hP q (hR (mem_sdiff.mp hq).1)).1).mpr
    rintro rfl
    exact (mem_sdiff.mp hp).2 (mem_sdiff.mp hq).1
  have hQe : g * d = primeProduct Q := primeProduct_inter_sdiff Q R
  have hRe : g * e = primeProduct R := by
    simpa only [inter_comm] using primeProduct_inter_sdiff R Q
  have hU : g * (d * e) = primeProduct (Q ∪ R) := by
    apply Nat.eq_of_mul_eq_mul_right hg.pos
    calc
      _ = (g * d) * (g * e) := by ring
      _ = primeProduct Q * primeProduct R := by rw [hQe, hRe]
      _ = primeProduct (Q ∪ R) * g := (prod_union_inter (f := fun p : ℕ => p)).symm
  have hN : (g * (d * e)) * t = primeProduct P := by
    rw [hU, mul_comm]
    exact prod_sdiff (union_subset hQ hR)
  have hv := covariance_multiple g d e t hg hd he hde
  rw [hN, hQe, hRe] at hv
  rw [hv, ← hN, ← hQe, ← hRe]
  change (t : ℚ) * g = ((g * (d * e) * t : ℕ) : ℚ) * (g : ℚ) ^ 2 /
    (((g * d : ℕ) : ℚ) * ((g * e : ℕ) : ℚ))
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hg.pos.ne'
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.pos.ne'
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he.pos.ne'
  simp only [Nat.cast_mul]
  field_simp

lemma covarianceKernel_insert_left (p : ℕ) (Q R : Finset ℕ) (hpQ : p ∉ Q) (hpR : p ∉ R) :
    covarianceKernel (insert p Q) R = -covarianceKernel Q R / p := by
  simp only [covarianceKernel, inter_insert, hpR, if_false,
    card_insert_of_notMem hpQ, primeProduct, prod_insert hpQ, Nat.cast_mul]
  rw [show Q.card + 1 + R.card = (Q.card + R.card) + 1 by omega, pow_succ]
  ring

lemma covarianceKernel_comm (Q R : Finset ℕ) : covarianceKernel Q R = covarianceKernel R Q := by
  simp only [covarianceKernel, inter_comm, add_comm, mul_comm]

lemma covarianceKernel_insert_right (p : ℕ) (Q R : Finset ℕ) (hpQ : p ∉ Q) (hpR : p ∉ R) :
    covarianceKernel Q (insert p R) = -covarianceKernel Q R / p := by
  rw [covarianceKernel_comm, covarianceKernel_insert_left p R Q hpR hpQ, covarianceKernel_comm Q R]

lemma covarianceKernel_insert_both (p : ℕ) (hp : p ≠ 0) (Q R : Finset ℕ)
    (hpQ : p ∉ Q) (hpR : p ∉ R) :
    covarianceKernel (insert p Q) (insert p R) = covarianceKernel Q R := by
  have hpI : p ∉ Q ∩ R := fun h => hpQ (mem_inter.mp h).1
  have heq : insert p Q ∩ insert p R = insert p (Q ∩ R) := by ext; simp only [mem_inter, mem_insert]; tauto
  simp only [covarianceKernel, heq, card_insert_of_notMem hpQ,
    card_insert_of_notMem hpR, primeProduct, prod_insert hpQ, prod_insert hpR, prod_insert hpI,
    Nat.cast_mul]
  rw [show Q.card + 1 + (R.card + 1) = (Q.card + R.card) + 2 by omega, pow_add]
  norm_num
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  field_simp

lemma covarianceKernel_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0) :
    (∑ Q ∈ P.powerset, ∑ R ∈ P.powerset, covarianceKernel Q R) =
      ∏ p ∈ P, (2 - 2 / (p : ℚ)) := by
  induction P using Finset.induction_on with
  | empty => simp [covarianceKernel, primeProduct]
  | @insert p P hp ih =>
    have hp0 := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q ≠ 0 := fun q hq => hP q (mem_insert_of_mem hq)
    have hnot (Q : Finset ℕ) (hQ : Q ∈ P.powerset) : p ∉ Q := fun h => hp (mem_powerset.mp hQ h)
    calc
      _ = ∑ Q ∈ P.powerset, ∑ R ∈ P.powerset,
          (covarianceKernel Q R + covarianceKernel Q (insert p R) +
            covarianceKernel (insert p Q) R + covarianceKernel (insert p Q) (insert p R)) := by
        simp only [sum_powerset_insert hp, sum_add_distrib]
        ring
      _ = (2 - 2 / (p : ℚ)) * (∑ Q ∈ P.powerset, ∑ R ∈ P.powerset, covarianceKernel Q R) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro Q hQ
        rw [mul_sum]
        apply sum_congr rfl
        intro R hR
        rw [covarianceKernel_insert_left p Q R (hnot Q hQ) (hnot R hR),
          covarianceKernel_insert_right p Q R (hnot Q hQ) (hnot R hR),
          covarianceKernel_insert_both p hp0 Q R (hnot Q hQ) (hnot R hR)]
        ring
      _ = _ := by rw [ih hP', prod_insert hp]

/-- Exact second moment: each odd prime multiplies the average square by
`2*(1-1/p)`. This is not a bound at quadratic interval length. -/
theorem profile_energy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    (∑ a ∈ range (primeProduct P), profile P a ^ 2) =
      (primeProduct P : ℚ) * ∏ p ∈ P, (2 - 2 / (p : ℚ)) := by
  have hexpand (a : ℕ) : profile P a ^ 2 =
      ∑ Q ∈ P.powerset, ∑ R ∈ P.powerset,
        ((-1 : ℚ) ^ (Q.card + R.card)) *
          (residueSign (primeProduct Q) a * residueSign (primeProduct R) a) := by
    rw [profile, pow_two, sum_mul_sum]
    apply sum_congr rfl
    intro Q hQ
    apply sum_congr rfl
    intro R hR
    rw [pow_add]
    ring
  simp_rw [hexpand]
  rw [sum_comm]
  calc
    _ = ∑ Q ∈ P.powerset, ∑ R ∈ P.powerset,
        (primeProduct P : ℚ) * covarianceKernel Q R := by
      apply sum_congr rfl
      intro Q hQ
      rw [sum_comm]
      apply sum_congr rfl
      intro R hR
      rw [← mul_sum, covariance_subsets P Q R hP (mem_powerset.mp hQ) (mem_powerset.mp hR)]
      dsimp only [covarianceKernel]
      ring
    _ = _ := by
      simp only [← mul_sum]
      rw [covarianceKernel_sum P (fun p hp => (hP p hp).1.ne_zero)]

#print axioms covariance_subsets
#print axioms profile_energy
end Erdos970.ParityDiscrepancy
