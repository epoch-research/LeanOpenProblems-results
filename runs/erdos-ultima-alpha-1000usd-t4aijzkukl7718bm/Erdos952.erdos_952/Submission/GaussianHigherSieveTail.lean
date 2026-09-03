import Submission.GaussianHigherSieveParameters

/-! Finite small-prime exceptions can be avoided by anchoring the exact
higher-order kernel sufficiently far along any injective ray. This step
uses only finiteness and does not turn sieve survivors into actual primes. -/
namespace Erdos952Investigation.GaussianHigherSieveTail
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianPolynomialBoxCounts GaussianWeightedSieve
open GaussianIteratedSmoothing FiniteSampleSmoothing GaussianHigherSmoothingLower GaussianHigherSmoothingUpper
open GaussianHigherPolynomialCounts GaussianHigherOptimizedSieve GaussianHigherSieveParameters
open GaussianPrimePatternSieve GaussianSelbergMainOptimization FiniteSelbergOptimization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

def offsets (R n : ℕ) : Finset GaussianInt :=
  Finset.univ.image (fun s : Sample (Box 0 R) (n+1) × Sample (Box 0 R) (n+1) =>
    tupleValue 0 R (n+1) s.1-tupleValue 0 R (n+1) s.2)

lemma kernel_offset_mem (a : GaussianInt) (R n : ℕ)
    (s : KernelSample (Sample (Box 0 R) n) a R) :
    kernelValue (tupleValue 0 R n) a R s-a ∈ offsets R n := by
  apply Finset.mem_image.mpr
  refine ⟨kernelEquiv a R n s,Finset.mem_univ _,?_⟩
  rw [kernelEquiv_value]
  abel

def badAnchors (E : Finset GaussianInt) (R n : ℕ) : Finset GaussianInt :=
  (E.product (offsets R n)).image (fun s => s.1-s.2)

lemma kernel_avoids_of_anchor_not_bad (E : Finset GaussianInt) (a : GaussianInt) (R n : ℕ)
    (ha : a ∉ badAnchors E R n) :
    ∀ s : KernelSample (Sample (Box 0 R) n) a R,
      kernelValue (tupleValue 0 R n) a R s ∉ E := by
  intro s hs
  apply ha
  refine Finset.mem_image.mpr ⟨(kernelValue (tupleValue 0 R n) a R s,
    kernelValue (tupleValue 0 R n) a R s-a),?_,?_⟩
  · exact Finset.mem_product.mpr ⟨hs,kernel_offset_mem a R n s⟩
  · dsimp
    abel

lemma higher_finset_count_eq_zero (E : Finset GaussianInt) (a : GaussianInt) (R n : ℕ)
    (ha : a ∉ badAnchors E R n) : higherCount (fun z => z ∈ E) a R n = 0 := by
  have hh := kernel_avoids_of_anchor_not_bad E a R n ha
  simp only [higherCount,kernelCount_sum,hh,if_false,Finset.sum_const_zero,zero_div]

lemma injective_eventually_not_mem (E : Finset GaussianInt) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) : ∃ N, ∀ b ≥ N, x b ∉ E := by
  let B : ℕ := E.sup (fun z => z.norm.natAbs)
  obtain ⟨N,hN⟩ := injective_escapes_norm x hx (B : ℤ)
  refine ⟨N,?_⟩
  intro b hb he
  have hn : (x b).norm.natAbs ≤ B := Finset.le_sup (f := fun z => z.norm.natAbs) he
  have hn' : (x b).norm ≤ (B : ℤ) := by
    have hh : ((x b).norm.natAbs : ℤ) ≤ B := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs,abs_of_nonneg (GaussianInt.norm_nonneg _)] using hh
  exact (hN b hb).not_ge hn'

lemma injective_eventually_zero_exception_count (E : Finset GaussianInt) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (R n : ℕ) :
    ∃ N, ∀ b ≥ N, higherCount (fun z => z ∈ E) (x b) R n = 0 := by
  obtain ⟨N,hN⟩ := injective_eventually_not_mem (badAnchors E R n) x hx
  exact ⟨N,fun b hb => higher_finset_count_eq_zero E (x b) R n (hN b hb)⟩

/-- The tail threshold depends on the finite pattern, chosen sieve and
kernel parameters. No uniform threshold over changing parameters is asserted. -/
lemma prime_count_le_sifted_on_tail {κ : Type*} [Fintype κ] (z : κ → GaussianInt)
    (D Q : Finset GaussianInt) (hD : Supported D Q) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (R n : ℕ) :
    ∃ N, ∀ b ≥ N, higherCount (fun t => ∀ i, Prime (t+z i)) (x b) R n ≤
      higherCount (Sifted D (patternPolynomial z)) (x b) R n := by
  obtain ⟨N,hN⟩ := injective_eventually_zero_exception_count (exceptionSet z Q) x hx R n
  refine ⟨N,?_⟩
  intro b hb
  have hh := kernelCount_le_add (tupleValue 0 R n) (fun t => ∀ i, Prime (t+z i))
    (Sifted D (patternPolynomial z)) (fun t => t ∈ exceptionSet z Q)
    (prime_pattern_sifted_or_exception z D Q hD) (x b) R
  change higherCount (fun t => ∀ i, Prime (t+z i)) (x b) R n ≤
    higherCount (Sifted D (patternPolynomial z)) (x b) R n+
      higherCount (fun t => t ∈ exceptionSet z Q) (x b) R n at hh
  simpa only [hN b hb,add_zero] using hh

def primeSupport {ι : Type*} (D : Finset (Finset ι)) (g : ι → GaussianInt) : Finset GaussianInt :=
  (D.biUnion id).image g

lemma modulusSupport_supported {ι : Type*} (D : Finset (Finset ι))
    (g : ι → GaussianInt) (hg : ∀ i, Prime (g i)) :
    Supported (modulusSupport D g) (primeSupport D g) := by
  intro d hd hd1
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
  have hsne : s.Nonempty := by
    by_contra hn
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact hd1 (by simp [modulus,he])
  obtain ⟨i,hi⟩ := hsne
  refine ⟨g i,?_,hg i,Finset.dvd_prod_of_mem g hi⟩
  apply Finset.mem_image.mpr
  exact ⟨i,Finset.mem_biUnion.mpr ⟨s,hs,hi⟩,rfl⟩

/-- Optimal higher-order prime-pattern bound with NO finite-exception term,
valid at all sufficiently late anchors of an injective sequence. -/
theorem optimized_prime_bound_on_tail {ι κ : Type*} [Fintype κ]
    (z : κ → GaussianInt) (D : Finset (Finset ι)) (hD : DownClosed D) (hD0 : ∅ ∈ D)
    (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (hρ : ∀ i, 0 < rho (patternPolynomial z) (g i) ∧
      rho (patternPolynomial z) (g i) < (g i).norm.natAbs)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (R n A : ℕ)
    (hR : 0 < R) (hAR : A ≤ R) (hlevel : ∀ s ∈ D, (modulus g s).norm.natAbs ≤ A) :
    ∃ N, ∀ b ≥ N, higherCount (fun t => ∀ i, Prime (t+z i)) (x b) R n ≤
      (R : ℝ)^2/denominator D (fun i => localDensity (patternPolynomial z) (g i))+
        sieveError (modulusSupport D g) R n A := by
  obtain ⟨N,hN⟩ := prime_count_le_sifted_on_tail z (modulusSupport D g) (primeSupport D g)
    (modulusSupport_supported D g hg) x hx R n
  exact ⟨N,fun b hb => (hN b hb).trans (optimized_higher_sifted_bound D hD hD0 g hg hc
    (patternPolynomial z) hρ (x b) R n A hR hAR hlevel)⟩

#print axioms injective_eventually_zero_exception_count
#print axioms prime_count_le_sifted_on_tail
#print axioms optimized_prime_bound_on_tail
end
end Erdos952Investigation.GaussianHigherSieveTail
