import Submission.UniformSuccessorIntervalScales

/-!
# Prime-pair counts and a finite hyperbolic rectangle cover

The primality of the inner variable is now explicit. The conversion uses
a lower bound for its logarithm and does not discard prime-power errors.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

def cofactorPrimePairPool (c A B M N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc (A+1) B ×ˢ Icc (M+1) N).filter
    (fun x => x.2.Prime ∧ (c*x.1*x.2+1).Prime)

lemma cofactor_successor_gt_inner (c a n : ℕ) (hc : 0 < c) (ha : 0 < a) :
    n < c*a*n+1 := by
  have hca : 1 ≤ c*a := Nat.mul_pos hc ha
  have hh := Nat.mul_le_mul_right n hca
  simpa only [one_mul] using Nat.lt_succ_of_le hh

lemma cofactor_prime_pair_log_weight (c A B M N z : ℕ) (hc : 0 < c)
    (hM : 1 ≤ M) (hz : z ≤ M) :
    Real.log (M : ℝ)*((cofactorPrimePairPool c A B M N).card : ℝ) ≤
      cofactorIntervalPrimeSuccessorWeight c A B M N z := by
  let P := cofactorPrimePairPool c A B M N
  have hsub : P ⊆ (Icc (A+1) B ×ˢ Icc (M+1) N).filter
      (fun x => (c*x.1*x.2+1).Prime ∧ z<c*x.1*x.2+1) := by
    intro x hx
    obtain ⟨hxI,hprime,hsucc⟩ := mem_filter.mp hx
    obtain ⟨hxa,hxn⟩ := mem_product.mp hxI
    have ha : 0 < x.1 := by have := (mem_Icc.mp hxa).1; omega
    have hn : M < x.2 := (mem_Icc.mp hxn).1
    exact mem_filter.mpr ⟨hxI,hsucc,(hz.trans_lt hn).trans (cofactor_successor_gt_inner c x.1 x.2 hc ha)⟩
  have hlog (x : ℕ × ℕ) (hx : x ∈ P) : Real.log (M : ℝ) ≤ vonMangoldt x.2 := by
    obtain ⟨hxI,hprime,_⟩ := mem_filter.mp hx
    rw [vonMangoldt_apply_prime hprime]
    apply Real.log_le_log (by exact_mod_cast hM : (0 : ℝ)<M)
    exact_mod_cast (show M ≤ x.2 from Nat.le_of_succ_le (mem_Icc.mp (mem_product.mp hxI).2).1)
  calc
    _ = ∑ _x ∈ P, Real.log (M : ℝ) := by simp only [sum_const,nsmul_eq_mul,mul_comm]; rfl
    _ ≤ ∑ x ∈ P, vonMangoldt x.2 := sum_le_sum hlog
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)

lemma cofactor_prime_pair_count_le_weight (c A B M N z : ℕ) (hc : 0 < c)
    (hM : 2 ≤ M) (hz : z ≤ M) :
    ((cofactorPrimePairPool c A B M N).card : ℝ) ≤
      cofactorIntervalPrimeSuccessorWeight c A B M N z/Real.log (M : ℝ) := by
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1<M by omega))
  apply (le_div_iff₀ hlog).mpr
  simpa only [mul_comm] using cofactor_prime_pair_log_weight c A B M N z hc (by omega) hz

def hyperbolicPrimePairPool (c H Y Z : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 H ×ˢ Icc (Y+1) Z).filter
    (fun x => x.1*x.2 ≤ H ∧ x.2.Prime ∧ (c*x.1*x.2+1).Prime)

/-- A finite cover with arbitrary overlapping prime-variable intervals.
Only the sum of the actual rectangle cardinalities is charged. -/
lemma hyperbolic_prime_pair_card_le_sum {ι : Type*} (I : Finset ι)
    (c H Y Z : ℕ) (M N B : ι → ℕ)
    (hM : ∀ i ∈ I, 0 < M i)
    (hB : ∀ i ∈ I, H/(M i) ≤ B i)
    (hcover : ∀ q ∈ Icc (Y+1) Z, ∃ i ∈ I, M i<q ∧ q ≤ N i) :
    (hyperbolicPrimePairPool c H Y Z).card ≤
      ∑ i ∈ I, (cofactorPrimePairPool c 0 (B i) (M i) (N i)).card := by
  classical
  have hsub : hyperbolicPrimePairPool c H Y Z ⊆
      I.biUnion (fun i => cofactorPrimePairPool c 0 (B i) (M i) (N i)) := by
    intro x hx
    obtain ⟨hxI,hprod,hprime,hsucc⟩ := mem_filter.mp hx
    obtain ⟨hxa,hxn⟩ := mem_product.mp hxI
    obtain ⟨i,hi,hMi,hNi⟩ := hcover x.2 hxn
    have haB : x.1 ≤ B i := by
      have hfirst : x.1 ≤ H/x.2 := (Nat.le_div_iff_mul_le hprime.pos).mpr hprod
      exact hfirst.trans ((Nat.div_le_div_left hMi.le (hM i hi)).trans (hB i hi))
    refine mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,hprime,hsucc⟩⟩
    · exact mem_Icc.mpr ⟨(mem_Icc.mp hxa).1,haB⟩
    · exact mem_Icc.mpr ⟨hMi,hNi⟩
  exact (card_le_card hsub).trans card_biUnion_le

/-- The weighted rectangle estimate applies to the whole hyperbolic count
once each member of the cover has a positive logarithmic lower cutoff. -/
lemma hyperbolic_prime_pair_card_le_weights {ι : Type*} (I : Finset ι)
    (c H Y Z : ℕ) (hc : 0 < c) (M N B z : ι → ℕ)
    (hM : ∀ i ∈ I, 2 ≤ M i) (hz : ∀ i ∈ I, z i ≤ M i)
    (hB : ∀ i ∈ I, H/(M i) ≤ B i)
    (hcover : ∀ q ∈ Icc (Y+1) Z, ∃ i ∈ I, M i<q ∧ q ≤ N i) :
    ((hyperbolicPrimePairPool c H Y Z).card : ℝ) ≤
      ∑ i ∈ I, cofactorIntervalPrimeSuccessorWeight c 0 (B i) (M i) (N i) (z i)/Real.log (M i : ℝ) := by
  have hnat := hyperbolic_prime_pair_card_le_sum I c H Y Z M N B (fun i hi => by have := hM i hi; omega) hB hcover
  have hreal := Nat.cast_le (α := ℝ).mpr hnat
  rw [Nat.cast_sum] at hreal
  exact hreal.trans (sum_le_sum (fun i hi => cofactor_prime_pair_count_le_weight c 0 (B i) (M i) (N i) (z i) hc (hM i hi) (hz i hi)))

end Erdos821.AnalyticSieve
