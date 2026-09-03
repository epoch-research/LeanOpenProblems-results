import Submission.Sublinear

/-!
# Extracting smooth predecessors from a sparse prime support

The support need not be an initial segment of the primes. A finite covering
argument controls how many members are lost when replacing that support by
a smoothness cutoff. No new prime supply is assumed or asserted here.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.SparsePredecessors
set_option maxHeartbeats 2000000

lemma predecessor_multiple_card_le (P : Finset ℕ) (X q : ℕ) (hq : 0 < q)
    (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ X) :
    ((P.filter (fun p => q ∣ p-1)).card : ℝ) ≤ (X : ℝ)/q := by
  let A := P.filter (fun p => q ∣ p-1)
  have hcard : A.card ≤ ((Icc 1 X).filter (fun n => q ∣ n)).card := by
    apply Finset.card_le_card_of_injOn (fun p => p-1)
    · intro p hp
      obtain ⟨hpP,hqp⟩ := mem_filter.mp hp
      have hh := hP p hpP
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hqp⟩
    · intro a ha b hb he
      have ha2 := (hP a (mem_filter.mp ha).1).1
      have hb2 := (hP b (mem_filter.mp hb).1).1
      change a-1=b-1 at he
      omega
  exact (show (A.card : ℝ) ≤ ((Icc 1 X).filter (fun n => q ∣ n)).card by
    exact_mod_cast hcard).trans (Erdos821.card_multiples_Icc_le_div X q hq)

/-- Only the reciprocal weight of the excluded support labels is charged. -/
theorem nonsmooth_card_le_support_reciprocal (P Q : Finset ℕ) (X Y : ℕ)
    (hY : 0 < Y) (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ X)
    (hQ : ∀ p ∈ P, (p-1).primeFactors ⊆ Q) :
    ((P.filter (fun p => p-1 ∉ Nat.smoothNumbers Y)).card : ℝ) ≤
      (X : ℝ)*∑ q ∈ Q with Y ≤ q, (q : ℝ)⁻¹ := by
  let R := Q.filter (fun q => Y ≤ q)
  let F := fun q => P.filter (fun p => q ∣ p-1)
  have hsub : P.filter (fun p => p-1 ∉ Nat.smoothNumbers Y) ⊆ R.biUnion F := by
    intro p hp
    obtain ⟨hpP,hps⟩ := mem_filter.mp hp
    rw [Nat.mem_smoothNumbers'] at hps
    push_neg at hps
    obtain ⟨q,hq,hqp,hqY⟩ := hps
    have hp2 := (hP p hpP).1
    have hqQ := hQ p hpP (Nat.mem_primeFactors.mpr ⟨hq,hqp,by omega⟩)
    exact mem_biUnion.mpr ⟨q,mem_filter.mpr ⟨hqQ,hqY⟩,mem_filter.mpr ⟨hpP,hqp⟩⟩
  have hcard := (card_le_card hsub).trans (card_biUnion_le (s := R) (t := F))
  calc
    _ ≤ ∑ q ∈ R, ((F q).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ q ∈ R, (X : ℝ)/q := by
      apply sum_le_sum
      intro q hq
      exact predecessor_multiple_card_le P X q (hY.trans_le (mem_filter.mp hq).2) hP
    _ = _ := by simp only [R,div_eq_mul_inv,mul_sum]

lemma nonsmooth_card_le_support_card (P Q : Finset ℕ) (X Y : ℕ)
    (hY : 0 < Y) (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ X)
    (hQ : ∀ p ∈ P, (p-1).primeFactors ⊆ Q) :
    ((P.filter (fun p => p-1 ∉ Nat.smoothNumbers Y)).card : ℝ) ≤
      (Q.card : ℝ)*X/Y := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hweight : (∑ q ∈ Q with Y ≤ q, (q : ℝ)⁻¹) ≤ (Q.card : ℝ)/Y := by
    calc
      _ ≤ ∑ _q ∈ Q.filter (fun q => Y ≤ q), (Y : ℝ)⁻¹ := by
        apply sum_le_sum
        intro q hq
        exact inv_anti₀ hY0 (by exact_mod_cast (mem_filter.mp hq).2)
      _ = ((Q.filter (fun q => Y ≤ q)).card : ℝ)*(Y : ℝ)⁻¹ := by
        rw [sum_const,nsmul_eq_mul]
      _ ≤ (Q.card : ℝ)*(Y : ℝ)⁻¹ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_le Q (fun q => Y ≤ q)) (inv_nonneg.mpr hY0.le)
      _ = _ := by rw [div_eq_mul_inv]
  apply (nonsmooth_card_le_support_reciprocal P Q X Y hY hP hQ).trans
  have hh := mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg X)
  convert hh using 1
  ring

/-- A positive retained proportion follows whenever the support budget is
small enough. The lemma supplies the retained members, not the input family. -/
theorem smooth_subfamily_card_lower (P Q : Finset ℕ) (X Y : ℕ)
    (hY : 0 < Y) (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ X)
    (hQ : ∀ p ∈ P, (p-1).primeFactors ⊆ Q) (δ : ℝ)
    (hbudget : (Q.card : ℝ)*X ≤ δ*Y*P.card) :
    (1-δ)*(P.card : ℝ) ≤ (P.filter (fun p => p-1 ∈ Nat.smoothNumbers Y)).card := by
  have hbad := nonsmooth_card_le_support_card P Q X Y hY hP hQ
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hbound : (Q.card : ℝ)*X/Y ≤ δ*P.card := by
    apply (div_le_iff₀ hY0).mpr
    nlinarith only [hbudget]
  have hpartition := card_filter_add_card_filter_not (s := P)
    (fun p => p-1 ∈ Nat.smoothNumbers Y)
  have hpartitionR : ((P.filter (fun p => p-1 ∈ Nat.smoothNumbers Y)).card : ℝ)+
      (P.filter (fun p => p-1 ∉ Nat.smoothNumbers Y)).card = P.card := by
    exact_mod_cast hpartition
  nlinarith only [hbad,hbound,hpartitionR]

end Erdos821.SparsePredecessors
