import Submission.SupportPrefixCertificate
import Submission.SupportPrimeEmbedding
import Submission.SupportArithmetic

/-! An auxiliary arithmetic necessary condition: an odd distinct covering
system must have a modulus with at least four distinct prime factors. This
DOES NOT settle the unrestricted conjecture in Submission/Spec.lean. -/
namespace Erdos7SupportThreeArithmetic
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportScheduledBudget Erdos7SupportPrefixCertificate
open Erdos7SupportPrimeEmbedding Erdos7CompressionSieve Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

lemma scheduled_arithmetic_not_cover {κ : Type*} [Fintype κ]
    (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) (hs : Schedule N P E C)
    (hcop : Pairwise (Function.onFun Nat.Coprime (fun i : Fin N => P i)))
    (e : κ → Fin N → ℕ) (he : Function.Injective e)
    (he0 : ∀ k,∃ i,e k i≠0) (heE : ∀ k i,e k i ≤ E i)
    (hsize : ∀ k,(expSupport (e k)).card ≤ 3) (a : κ → ℤ) :
    ¬ ∀ x : ℤ,∃ k,((∏ i : Fin N,P i^e k i:ℕ):ℤ) ∣ x-a k := by
  intro hcover
  have hh := arithmetic_support_convex_bound (fun i : Fin N => P i) (fun i : Fin N => E i)
    (fun i => (hs.bounds i i.isLt).1) hcop 2 e he he0 heE hsize a
    (fun i => C i) (fun i => 1/((P i:ℚ)-1))
    (fun i => (hs.bounds i i.isLt).2.1) (fun i => (hs.bounds i i.isLt).2.2)
    (fun i => by
      have hp : (1:ℚ) < P i := by exact_mod_cast (hs.bounds i i.isLt).1
      exact one_div_pos.mpr (by linarith))
    (fun i => positive_power_sum_le (P i) (hs.bounds i i.isLt).1 (E i)) hcover
  have hb := budget_bound N P E C hs
  linarith

/-- All finite prime supports and all finite exponents are allowed. The
hypothesis being excluded is the uniform bound THREE on support cardinality. -/
theorem arithmetic_exists_large_support {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    ∃ k,4 ≤ (m k).primeFactors.card := by
  classical
  by_contra! hsmall
  have hsize (k : κ) : (m k).primeFactors.card ≤ 3 := by have := hsmall k; omega
  have hm0 (k : κ) : m k≠0 := by have := (hc.2.1 k).1; omega
  let Q := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hQ (q : ℕ) (hq : q ∈ Q) : q.Prime ∧ 3 ≤ q := by
    obtain ⟨k,_,hqk⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hprime,hdvd,hzero⟩ := Nat.mem_primeFactors.mp hqk
    have h2 : q≠2 := by
      intro heq
      rw [heq] at hdvd
      exact (Nat.not_even_iff_odd.mpr (hc.2.1 k).2) (even_iff_two_dvd.mpr hdvd)
    exact ⟨hprime,by have := hprime.two_le; omega⟩
  let T := Q.filter (fun q => 1000 < q)
  have hT (q : ℕ) (hq : q ∈ T) : q.Prime ∧ 1000 < q :=
    ⟨(hQ q (Finset.mem_filter.mp hq).1).1,(Finset.mem_filter.mp hq).2⟩
  let N := 167+T.card
  let P := primeSeq T
  let e (k : κ) (i : Fin N) := (m k).factorization (P i)
  let E (t : ℕ) := if ht : t < N then max 13 (Finset.univ.sup (fun k => e k ⟨t,ht⟩)) else 13
  have hE (i : Fin 167) : 12 < E i := by
    have hi : i.val < N := by have := i.isLt; dsimp [N]; omega
    dsimp only [E]
    rw [dif_pos hi]
    exact lt_of_lt_of_le (by omega : 12 < 13) (le_max_left _ _)
  have hs : Schedule N P E capSeq := padded_schedule T hT E hE
  have hpinj : Function.Injective (fun i : Fin N => P i) := by
    intro i j hij
    have hh : candidate T i=candidate T j := by simpa only [P,primeSeq_at] using hij
    exact (candidate_strictMono T (fun q hq => (hT q hq).2)).injective hh
  have hp (i : Fin N) : (P i).Prime := by
    simpa only [P,primeSeq_at] using (candidate_prime T hT i).1
  have hcop : Pairwise (Function.onFun Nat.Coprime (fun i : Fin N => P i)) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hpinj h))
  have hprod (k : κ) : m k=∏ i : Fin N,P i^e k i := by
    let S := Finset.univ.image (fun i : Fin N => P i)
    have hsub : (m k).primeFactors ⊆ S := by
      intro q hq
      have hqQ : q ∈ Q := Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hq⟩
      obtain ⟨i,hi⟩ := candidate_covers T q (hQ q hqQ).1 (hQ q hqQ).2
        (fun h => Finset.mem_filter.mpr ⟨hqQ,h⟩)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [P,primeSeq_at] using hi⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) S hsub
    rw [Finset.prod_coe_sort S (fun q => q^(m k).factorization q)] at hh
    rw [hh]
    exact Finset.prod_image (fun i _ j _ hij => hpinj hij)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k,hprod l,hkl]
  have he0 (k : κ) : ∃ i,e k i≠0 := by
    by_contra! hz
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  have heE (k : κ) (i : Fin N) : e k i ≤ E i := by
    dsimp only [E]
    rw [dif_pos i.isLt]
    exact (Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)).trans (le_max_right _ _)
  have heSize (k : κ) : (expSupport (e k)).card ≤ 3 := by
    apply le_trans _ (hsize k)
    apply Finset.card_le_card_of_injOn (fun i : Fin N => P i)
    · intro i hi
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr ((mem_expSupport (e k) i).mp hi)
    · intro i _ j _ hij
      exact hpinj hij
  apply scheduled_arithmetic_not_cover N P E capSeq hs hcop e hei he0 heE heSize a
  simpa only [← hprod] using hc.2.2

theorem exists_large_support (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i,¬ C.moduli i ≤ Ideal.span {2}) :
    ∃ i,4 ≤ ((C.moduli i).absNorm).primeFactors.card := by
  letI := C.fintypeIndex
  exact arithmetic_exists_large_support (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,(ideal_not_le_two_iff _).mp (hodd i)⟩,
      arithmetic_cover C⟩

#print axioms arithmetic_exists_large_support
#print axioms exists_large_support
end Erdos7SupportThreeArithmetic
