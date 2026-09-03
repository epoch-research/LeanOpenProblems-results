import Submission.PrimeDivisorOvershoot
import Submission.DampedPrimePairs

/-! Transporting the small-prime cofactor sieve to the actual quadratic
large-product pair multiplicities. -/
namespace Erdos371
open Finset FiniteSieve
set_option autoImplicit false

def smallCrossPrimePairs (D X n : ℕ) : Finset (ℕ×ℕ) :=
  (largeCrossPrimePairs D n).filter fun pq => min pq.1 pq.2 ≤ X

lemma leftSmallCrossPrimePairs_sum_bound (D X : ℕ) :
    (∑ n ∈ range D, ((largeCrossPrimePairs D n).filter fun pq => pq.1 ≤ X).card) ≤
      ∑ p ∈ (X+1).primesBelow, (primeDivisorOvershoot D p 1).card := by
  rw [← card_sigma,← card_sigma]
  apply card_le_card_of_injOn (fun x : Σ _n : ℕ, ℕ×ℕ =>
    (⟨x.2.1,(x.1+1,x.2.2)⟩ : Σ _p : ℕ, ℕ×ℕ))
  · intro x hx
    simp only [mem_coe,mem_sigma,mem_filter] at hx
    obtain ⟨hn,hpair,hpX⟩ := hx
    obtain ⟨hpair,hlarge⟩ := mem_filter.mp hpair
    obtain ⟨hpp,hqp⟩ := mem_product.mp hpair
    have hp := Nat.prime_of_mem_primeFactors hpp
    have hq := Nat.prime_of_mem_primeFactors hqp
    have hpd := Nat.dvd_of_mem_primeFactors hpp
    have hqd := Nat.dvd_of_mem_primeFactors hqp
    have hnD := mem_range.mp hn
    have hqD := (Nat.le_of_dvd (by omega : 0 < x.1+1) hqd).trans (by omega : x.1+1 ≤ D)
    simp only [mem_coe,mem_sigma]
    refine ⟨Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,?_⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
      Nat.mem_primesBelow.mpr ⟨by omega,hq⟩⟩,hqd,hlarge,?_⟩
    simpa using hpd.modEq_zero_nat.add_right 1
  · intro x hx y hy he
    have hp := congrArg Sigma.fst he
    have hn := congrArg (fun z : Σ _p : ℕ, ℕ×ℕ => z.2.1) he
    have hq := congrArg (fun z : Σ _p : ℕ, ℕ×ℕ => z.2.2) he
    dsimp only at hp hn hq
    apply Sigma.ext (by omega)
    exact heq_of_eq (Prod.ext hp hq)

lemma dvd_succ_modEq_pred (p n : ℕ) (hp : 1 ≤ p) (hd : p ∣ n+1) :
    Nat.ModEq p n (p-1) := by
  have he : Nat.ModEq p ((p-1)+1) 0 := by
    rw [Nat.sub_add_cancel hp]
    exact (dvd_refl p).modEq_zero_nat
  exact (hd.modEq_zero_nat.trans he.symm).add_right_cancel' 1

lemma rightSmallCrossPrimePairs_sum_bound (D X : ℕ) :
    (∑ n ∈ range D, ((largeCrossPrimePairs D n).filter fun pq => pq.2 ≤ X).card) ≤
      ∑ p ∈ (X+1).primesBelow, (primeDivisorOvershoot D p (p-1)).card := by
  rw [← card_sigma,← card_sigma]
  apply card_le_card_of_injOn (fun x : Σ _n : ℕ, ℕ×ℕ =>
    (⟨x.2.2,(x.1,x.2.1)⟩ : Σ _p : ℕ, ℕ×ℕ))
  · intro x hx
    simp only [mem_coe,mem_sigma,mem_filter] at hx
    obtain ⟨hn,hpair,hpX⟩ := hx
    obtain ⟨hpair,hlarge⟩ := mem_filter.mp hpair
    obtain ⟨hqp,hpp⟩ := mem_product.mp hpair
    have hp := Nat.prime_of_mem_primeFactors hpp
    have hq := Nat.prime_of_mem_primeFactors hqp
    have hpd := Nat.dvd_of_mem_primeFactors hpp
    have hqd := Nat.dvd_of_mem_primeFactors hqp
    have hn0 := (Nat.mem_primeFactors.mp hqp).2.2
    have hnD := mem_range.mp hn
    have hqD := (Nat.le_of_dvd (by omega : 0 < x.1) hqd).trans (by omega : x.1 ≤ D)
    simp only [mem_coe,mem_sigma]
    refine ⟨Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,?_⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
      Nat.mem_primesBelow.mpr ⟨by omega,hq⟩⟩,hqd,?_,?_⟩
    · dsimp only
      nlinarith
    · exact dvd_succ_modEq_pred _ _ hp.one_le hpd
  · intro x hx y hy he
    have hp := congrArg Sigma.fst he
    have hn := congrArg (fun z : Σ _p : ℕ, ℕ×ℕ => z.2.1) he
    have hq := congrArg (fun z : Σ _p : ℕ, ℕ×ℕ => z.2.2) he
    dsimp only at hp hn hq
    apply Sigma.ext hn
    exact heq_of_eq (Prod.ext hq hp)

lemma smallCrossPrimePairs_sum_bound (D X : ℕ) :
    (∑ n ∈ range D, (smallCrossPrimePairs D X n).card) ≤
      ∑ p ∈ (X+1).primesBelow,
        ((primeDivisorOvershoot D p 1).card+(primeDivisorOvershoot D p (p-1)).card) := by
  have hpoint (n : ℕ) : (smallCrossPrimePairs D X n).card ≤
      ((largeCrossPrimePairs D n).filter fun pq => pq.1 ≤ X).card+
      ((largeCrossPrimePairs D n).filter fun pq => pq.2 ≤ X).card := by
    have hsub : smallCrossPrimePairs D X n ⊆
        ((largeCrossPrimePairs D n).filter fun pq => pq.1 ≤ X) ∪
        ((largeCrossPrimePairs D n).filter fun pq => pq.2 ≤ X) := by
      intro pq hpq
      obtain ⟨hpq,hX⟩ := mem_filter.mp hpq
      rcases min_le_iff.mp hX with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨hpq,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hpq,h⟩)
    exact (card_le_card hsub).trans (card_union_le _ _)
  have hs := sum_le_sum (fun n (_ : n ∈ range D) => hpoint n)
  rw [sum_add_distrib] at hs
  rw [sum_add_distrib]
  exact hs.trans (Nat.add_le_add (leftSmallCrossPrimePairs_sum_bound D X)
    (rightSmallCrossPrimePairs_sum_bound D X))

/-- The estimate counts every low-prime large-product mark, even when a
single input has several such marks. -/
theorem smallCrossPrimePairs_finite_bound (D X z : ℕ) (hX : 1 ≤ X) (hXD : X ≤ D)
    (hz : 1 ≤ z) (hsize : X*z ≤ D) :
    (∑ n ∈ range D, ((smallCrossPrimePairs D X n).card : ℝ)) ≤
      72*Real.exp 2*D*Real.log (X+1 : ℝ)/Real.log (z+1 : ℝ)+
      4*(X+1 : ℝ)^10*(z+1 : ℝ)^32 := by
  have hc := (Nat.cast_le (α := ℝ)).mpr (smallCrossPrimePairs_sum_bound D X)
  push_cast at hc
  exact hc.trans (small_prime_overshoot_total_bound D X z hX hXD hz hsize)

#print axioms smallCrossPrimePairs_sum_bound
#print axioms smallCrossPrimePairs_finite_bound
end Erdos371
