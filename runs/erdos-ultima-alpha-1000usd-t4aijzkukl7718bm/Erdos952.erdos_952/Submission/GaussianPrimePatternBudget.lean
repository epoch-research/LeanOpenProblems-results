import Submission.GaussianHigherSieveTail

/-! A finite-family budget for prime patterns, including path-pattern
entropy. The smoothing order absorbs the sum of discrepancy errors. What
remains is an explicit sum of reciprocal Selberg denominators; no estimate
strong enough to exclude every prime ray is asserted. -/
namespace Erdos952Investigation.GaussianPrimePatternBudget
open GaussianIdealBoxCounts GaussianPolynomialBoxCounts GaussianWeightedSieve
open GaussianIteratedSmoothing GaussianHigherSmoothingLower GaussianHigherPolynomialCounts
open GaussianHigherOptimizedSieve GaussianHigherSieveParameters GaussianHigherSieveTail
open GaussianSelbergMainOptimization FiniteSelbergOptimization PrimePathCounting
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

lemma higherCount_exists_le_sum {J : Type*} [Fintype J] (p : J → GaussianInt → Prop)
    (a : GaussianInt) (R n : ℕ) :
    higherCount (fun z => ∃ j, p j z) a R n ≤ ∑ j, higherCount (p j) a R n := by
  classical
  have hpoint (z : GaussianInt) : (if ∃ j, p j z then (1 : ℝ) else 0) ≤
      ∑ j, if p j z then (1 : ℝ) else 0 := by
    by_cases h : ∃ j, p j z
    · obtain ⟨j,hj⟩ := h
      rw [if_pos ⟨j,hj⟩]
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset J))
        (f := fun j => if p j z then (1 : ℝ) else 0)
        (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa only [if_pos hj] using hh
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  simp only [higherCount,kernelCount_sum]
  rw [← Finset.sum_div,Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro s hs
  by_cases h : ∃ j, p j (kernelValue (tupleValue 0 R n) a R s)
  · simpa only [h,if_true] using hpoint (kernelValue (tupleValue 0 R n) a R s)
  · simpa only [h,if_false] using hpoint (kernelValue (tupleValue 0 R n) a R s)

lemma dyadic_family_error (H k : ℕ) (hH : H ≤ 4^k) :
    (H : ℝ)*((1/2 : ℝ)^(2*k)/16) ≤ 1/16 := by
  have hH' : (H : ℝ) ≤ (4 : ℝ)^k := by exact_mod_cast hH
  apply (mul_le_mul_of_nonneg_right hH' (by positivity)).trans_eq
  have hp : (4 : ℝ)^k*(1/2 : ℝ)^(2*k) = 1 := by
    rw [pow_mul,← mul_pow]
    norm_num
  rw [← mul_div_assoc,hp]

/-- A family of at most 4^k patterns has TOTAL discrepancy <=1/16 at order
4m+k. Finite small-prime exceptions vanish at sufficiently late anchors. -/
theorem finite_family_tail_bound {J ι κ : Type*} [Fintype J] [Fintype κ]
    (z : J → κ → GaussianInt) (D : J → Finset (Finset ι))
    (hD : ∀ j, DownClosed (D j)) (hD0 : ∀ j, ∅ ∈ D j)
    (g : J → ι → GaussianInt) (hg : ∀ j i, Prime (g j i))
    (hc : ∀ j, Pairwise (fun i l => IsCoprime (g j i) (g j l)))
    (hρ : ∀ j i, 0 < rho (patternPolynomial (z j)) (g j i) ∧
      rho (patternPolynomial (z j)) (g j i) < (g j i).norm.natAbs)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (R m k A : ℕ)
    (hR : 0 < R) (hAR : 16*A ≤ R) (hRm : R ≤ 2^m) (hJ : Fintype.card J ≤ 4^k)
    (hlevel : ∀ j, ∀ s ∈ D j, (modulus (g j) s).norm.natAbs ≤ A) :
    ∃ N, ∀ b ≥ N,
      higherCount (fun t => ∃ j, ∀ i, Prime (t+z j i)) (x b) R (4*m+k) ≤
        (R : ℝ)^2*(∑ j, 1/denominator (D j)
          (fun i => localDensity (patternPolynomial (z j)) (g j i)))+1/16 := by
  have hlocal (j : J) := optimized_prime_bound_on_tail (z j) (D j) (hD j) (hD0 j)
    (g j) (hg j) (hc j) (hρ j) x hx R (4*m+k) A hR (by omega) (hlevel j)
  choose N hN using hlocal
  refine ⟨Finset.univ.sup N,?_⟩
  intro b hb
  have herror (j : J) : sieveError (modulusSupport (D j) (g j)) R (4*m+k) A ≤
      (1/2 : ℝ)^(2*k)/16 := by
    have h1 : 1 ∈ modulusSupport (D j) (g j) :=
      Finset.mem_image.mpr ⟨∅,hD0 j,by simp [modulus]⟩
    apply dyadic_sieveError_le _ h1 A R m k _ hAR hRm
    intro d hd
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
    exact hlevel j s hs
  apply (higherCount_exists_le_sum (fun j t => ∀ i, Prime (t+z j i)) (x b) R (4*m+k)).trans
  calc
    _ ≤ ∑ j, ((R : ℝ)^2/denominator (D j)
          (fun i => localDensity (patternPolynomial (z j)) (g j i))+(1/2 : ℝ)^(2*k)/16) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hN j b ((Finset.le_sup (f := N) hj).trans hb)).trans
        (add_le_add le_rfl (herror j))
    _ = (R : ℝ)^2*(∑ j, 1/denominator (D j)
          (fun i => localDensity (patternPolynomial (z j)) (g j i)))+
        (Fintype.card J : ℝ)*((1/2 : ℝ)^(2*k)/16) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Finset.mul_sum,mul_one_div]
    _ ≤ _ := add_le_add le_rfl (dyadic_family_error _ k hJ)

/-- A hypothetical prime ray forces the displayed reciprocal-denominator
budget. The finite family must cover EVERY prime-path starting point of
the chosen length. That covering and all local-density hypotheses are
explicit assumptions, not conclusions of an inverse-sieve argument. -/
theorem prime_ray_denominator_budget {J ι κ : Type*} [Fintype J] [Fintype κ]
    (z : J → κ → GaussianInt) (D : J → Finset (Finset ι))
    (hD : ∀ j, DownClosed (D j)) (hD0 : ∀ j, ∅ ∈ D j)
    (g : J → ι → GaussianInt) (hg : ∀ j i, Prime (g j i))
    (hc : ∀ j, Pairwise (fun i l => IsCoprime (g j i) (g j l)))
    (hρ : ∀ j i, 0 < rho (patternPolynomial (z j)) (g j i) ∧
      rho (patternPolynomial (z j)) (g j i) < (g j i).norm.natAbs)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (L M m k A : ℕ) (hM : 0 < M)
    (hcover : ∀ t, Starts C L t → ∃ j, ∀ i, Prime (t+z j i))
    (hAR : 16*A ≤ 5*(M*C.toNat)) (hRm : 5*(M*C.toNat) ≤ 2^m)
    (hJ : Fintype.card J ≤ 4^k)
    (hlevel : ∀ j, ∀ s ∈ D j, (modulus (g j) s).norm.natAbs ≤ A) :
    (M : ℝ)+1 ≤ 625*((4*m+k : ℕ)+1 : ℝ)^2*
      (((5*(M*C.toNat) : ℕ) : ℝ)^2*(∑ j, 1/denominator (D j)
          (fun i => localDensity (patternPolynomial (z j)) (g j i)))+1/16) := by
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (hp 0).2
  have hCn : 0 < C.toNat := by omega
  have hR : 0 < 5*(M*C.toNat) := Nat.mul_pos (by decide) (Nat.mul_pos hM hCn)
  obtain ⟨N,hN⟩ := finite_family_tail_bound z D hD hD0 g hg hc hρ x hx
    (5*(M*C.toNat)) m k A hR hAR hRm hJ hlevel
  have hx' : Function.Injective (fun n => x (N+n)) :=
    fun i j he => Nat.add_left_cancel (hx he)
  have hp' (n : ℕ) : Prime (x (N+n)) ∧ (x (N+(n+1))-x (N+n)).norm < C := by
    simpa only [Nat.add_assoc] using hp (N+n)
  have hl := GaussianSmoothingBuckets.ray_forces_higher_smoothed_count
    (fun n => x (N+n)) C hx' hp' M L (4*m+k) hM
  simp only [Nat.add_zero] at hl
  have hm := kernelCount_mono (tupleValue 0 (5*(M*C.toNat)) (4*m+k))
    (Starts C L) (fun t => ∃ j, ∀ i, Prime (t+z j i)) hcover (x N) (5*(M*C.toNat))
  have hu := hm.trans (hN N le_rfl)
  exact hl.trans (mul_le_mul_of_nonneg_left hu (by positivity))

#print axioms finite_family_tail_bound
#print axioms prime_ray_denominator_budget
end
end Erdos952Investigation.GaussianPrimePatternBudget
