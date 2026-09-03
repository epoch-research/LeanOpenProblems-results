import Submission.FinitePatternComparison
import Submission.CoprimeResidueSieve

/-! Low-degree inclusion data for the coloured prime-divisibility pattern of
consecutive integers. Incompatible choices of both colours have zero mass. -/
namespace Erdos371.FiniteSieve
open Finset

abbrev PrimeAtom := ℕ × Bool

def primeAtomResidue (a : PrimeAtom) : ℕ := if a.2 then a.1-1 else 0

def primeAtoms (P : Finset ℕ) : Finset PrimeAtom := P ×ˢ univ

def activePrimeAtoms (P : Finset ℕ) (n : ℕ) : Finset PrimeAtom :=
  (primeAtoms P).filter (fun a => n % a.1 = primeAtomResidue a)

lemma activePrimeAtoms_subset (P : Finset ℕ) (n : ℕ) : activePrimeAtoms P n ⊆ primeAtoms P :=
  filter_subset _ _

lemma primeAtomResidue_lt (a : PrimeAtom) (ha : 1 < a.1) : primeAtomResidue a < a.1 := by
  unfold primeAtomResidue
  split_ifs <;> omega

lemma activePrimeAtoms_injective (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) (n : ℕ) :
    Set.InjOn Prod.fst (activePrimeAtoms P n : Set PrimeAtom) := by
  intro a ha b hb he
  obtain ⟨ha,hra⟩ := mem_filter.mp ha
  obtain ⟨hb,hrb⟩ := mem_filter.mp hb
  have hpa := hP a.1 (mem_product.mp ha).1
  rcases a with ⟨p,c⟩
  rcases b with ⟨q,d⟩
  change p=q at he
  subst q
  cases c <;> cases d <;> simp_all [primeAtomResidue] <;> omega

noncomputable def primeAtomModel (T : Finset PrimeAtom) : ℝ :=
  if Set.InjOn Prod.fst (T : Set PrimeAtom) then ∏ a ∈ T, (1 : ℝ)/a.1 else 0

lemma primeAtomModel_le (T : Finset PrimeAtom) :
    primeAtomModel T ≤ ∏ a ∈ T, (1 : ℝ)/a.1 := by
  classical
  unfold primeAtomModel
  split_ifs
  · rfl
  · exact prod_nonneg fun _ _ => by positivity

lemma primeAtomModel_nonneg (T : Finset PrimeAtom) : 0 ≤ primeAtomModel T := by
  classical
  unfold primeAtomModel
  split_ifs
  · exact prod_nonneg fun _ _ => by positivity
  · rfl

lemma prime_pattern_inclusion_count (P : Finset ℕ) (N : ℕ) (T : Finset PrimeAtom)
    (hT : T ⊆ primeAtoms P) :
    patternInclusionMass (range N) (fun _ => (1 : ℝ)/N) (activePrimeAtoms P) T =
      (intersectionCount (range N) (fun a n => n % a.1 ∈ ({primeAtomResidue a} : Finset ℕ)) T : ℝ)/N := by
  classical
  have he (n : ℕ) : T ⊆ activePrimeAtoms P n ↔ ∀ a ∈ T, n % a.1 ∈ ({primeAtomResidue a} : Finset ℕ) := by
    simp only [mem_singleton]
    exact ⟨fun h a ha => (mem_filter.mp (h ha)).2,
      fun h a ha => mem_filter.mpr ⟨hT ha,h a ha⟩⟩
  unfold patternInclusionMass
  simp only [he]
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  simp only [intersectionCount,mul_one_div]
  congr 2
  congr 1
  ext n
  simp only [mem_filter]

/-- The coarse error is a product of the selected moduli, divided by N.
It is valid for all patterns, including incompatible ones. -/
theorem prime_pattern_inclusion_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (hN : 0 < N) (T : Finset PrimeAtom) (hT : T ⊆ primeAtoms P) :
    |patternInclusionMass (range N) (fun _ => (1 : ℝ)/N) (activePrimeAtoms P) T-
      primeAtomModel T| ≤ (∏ a ∈ T, (a.1 : ℝ))/N := by
  classical
  have hprime (a : PrimeAtom) (ha : a ∈ T) : a.1.Prime := hP a.1 (mem_product.mp (hT ha)).1
  by_cases hi : Set.InjOn Prod.fst (T : Set PrimeAtom)
  · have hc : (T : Set PrimeAtom).Pairwise (Function.onFun Nat.Coprime Prod.fst) := by
      intro a ha b hb hab
      apply (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr
      exact fun he => hab (hi ha hb he)
    have hr (a : PrimeAtom) (ha : a ∈ T) : ({primeAtomResidue a} : Finset ℕ) ⊆ range a.1 := by
      intro r hr
      rw [mem_singleton] at hr
      subst r
      exact mem_range.mpr (primeAtomResidue_lt a (hprime a ha).one_lt)
    have h := intersectionCount_residue_error T Prod.fst (fun a => {primeAtomResidue a})
      (fun a ha => (hprime a ha).ne_zero) hc hr N
    simp only [card_singleton,Nat.cast_one] at h
    rw [prime_pattern_inclusion_count P N T hT,primeAtomModel,if_pos hi]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have he : (intersectionCount (range N) (fun a n => n % a.1 ∈ ({primeAtomResidue a} : Finset ℕ)) T : ℝ)/N-
        (∏ a ∈ T, (1 : ℝ)/a.1) =
      ((intersectionCount (range N) (fun a n => n % a.1 ∈ ({primeAtomResidue a} : Finset ℕ)) T : ℝ)-
        N*(∏ a ∈ T, (1 : ℝ)/a.1))/N := by field_simp
    rw [he,abs_div,abs_of_pos hNr]
    exact div_le_div_of_nonneg_right h hNr.le
  · have hz (n : ℕ) : ¬T ⊆ activePrimeAtoms P n := by
      intro ht
      exact hi ((activePrimeAtoms_injective P (fun p hp => (hP p hp).one_lt) n).mono ht)
    simp only [patternInclusionMass,hz,if_false,sum_const_zero,primeAtomModel,if_neg hi,
      sub_self,abs_zero]
    positivity

lemma primeAtom_reciprocal_sum (P : Finset ℕ) :
    (∑ a ∈ primeAtoms P, (1 : ℝ)/a.1) = 2*∑ p ∈ P, (1 : ℝ)/p := by
  simp [primeAtoms,sum_product,mul_sum,two_mul]

/-- A quantitative finite-pattern estimate for the actual consecutive-prime
configuration. The model term is explicit and still needs symmetry or a
separate evaluation for each chosen observable. -/
theorem prime_pattern_comparison (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (hN : 0 < N) (L : ℕ) (F : Finset PrimeAtom → ℝ)
    (hF : ∀ T ⊆ primeAtoms P, |F T| ≤ 1) :
    |(∑ n ∈ range N, F (activePrimeAtoms P n))/N-
      ∑ T ∈ (primeAtoms P).powerset, if T.card < L then patternDifference F T*primeAtomModel T else 0| ≤
      (1+3^L)*((2*∑ p ∈ P, (1 : ℝ)/p)^L/L.factorial+
        ∑ T ∈ (primeAtoms P).powersetCard L, (∏ a ∈ T, (a.1 : ℝ))/N) +
      ∑ T ∈ (primeAtoms P).powerset, if T.card < L then
        (2 : ℝ)^T.card*((∏ a ∈ T, (a.1 : ℝ))/N) else 0 := by
  have h := finite_pattern_comparison_factorial F (primeAtoms P) L (range N) (fun _ => (1 : ℝ)/N)
    (activePrimeAtoms P) (fun n _ => activePrimeAtoms_subset P n) (fun _ _ => by positivity)
    hF primeAtomModel (fun T => (∏ a ∈ T, (a.1 : ℝ))/N) (fun a => (1 : ℝ)/a.1)
    (fun _ _ => by positivity) (fun T _ => primeAtomModel_le T)
    (fun T hT _ => prime_pattern_inclusion_error P hP N hN T hT)
  rw [primeAtom_reciprocal_sum] at h
  have hs : (∑ x ∈ range N, (1 : ℝ)/N*F (activePrimeAtoms P x)) =
      (∑ x ∈ range N, F (activePrimeAtoms P x))/N := by
    rw [← mul_sum]
    ring
  simpa only [hs] using h

#print axioms prime_pattern_comparison
end Erdos371.FiniteSieve
