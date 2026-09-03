import Submission.AbelResiduePrimeDensity

/-! Abel-prime cancellation for fixed periodic odd functions and fixed cyclic
antisymmetric observables. All moduli and cyclic processes are fixed before
the Abel parameter tends to one; no growing-cycle uniformity is asserted. -/
namespace Erdos371.AbelPrimes
open Finset Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Topology

noncomputable def primePeriodicCoeff {q : ℕ} (g : ZMod q → ℝ) (n : ℕ) : ℝ :=
  if n.Prime then g n * Real.log n else 0

lemma primePeriodicCoeff_expansion {q : ℕ} [NeZero q] (g : ZMod q → ℝ) (n : ℕ) :
    primePeriodicCoeff g n = ∑ a : ZMod q, g a * primeResidueCoeff a n := by
  classical
  by_cases hp : n.Prime
  · simp [primePeriodicCoeff,primeResidueCoeff,hp,residueClass,
      Set.indicator_apply, eq_comm, vonMangoldt_apply_prime hp]
  · simp [primePeriodicCoeff,primeResidueCoeff,hp]

lemma primePeriodicDirichlet_expansion {q : ℕ} [NeZero q] (g : ZMod q → ℝ)
    (s : ℝ) (hs : 1 < s) :
    realDirichlet (primePeriodicCoeff g) s =
      ∑ a : ZMod q, g a * realDirichlet (primeResidueCoeff a) s := by
  classical
  unfold realDirichlet
  simp_rw [primePeriodicCoeff_expansion, sum_div, mul_div_assoc]
  rw [Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
  · intro a _
    exact (primeResidue_summable a s hs).mul_left (g a)

lemma unit_residue_sum_odd {q : ℕ} [NeZero q] (g : ZMod q → ℝ)
    (hg : ∀ a, g (-a) = -g a) :
    (∑ a : ZMod q, g a * (if IsUnit a then (q.totient : ℝ)⁻¹ else 0)) = 0 := by
  classical
  let f : ZMod q → ℝ := fun a => g a * (if IsUnit a then (q.totient : ℝ)⁻¹ else 0)
  have he (a : ZMod q) : f (-a) = -f a := by
    have hu : IsUnit (-a) ↔ IsUnit a := ⟨fun h => by simpa using h.neg, IsUnit.neg⟩
    dsimp [f]
    simp only [hg,hu,neg_mul]
  have hs := Equiv.sum_comp (Equiv.neg (ZMod q)) f
  change (∑ a, f (-a)) = ∑ a, f a at hs
  simp_rw [he,sum_neg_distrib] at hs
  change (∑ a, f a) = 0
  linarith

/-- Fixed periodic odd functions have zero normalized Abel-prime mean. -/
theorem prime_periodic_odd_abel_limit {q : ℕ} [NeZero q] (g : ZMod q → ℝ)
    (hg : ∀ a, g (-a) = -g a) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet (primePeriodicCoeff g) s)
      (𝓝[>] 1) (𝓝 0) := by
  classical
  have ht := tendsto_finset_sum (univ : Finset (ZMod q))
    (fun a _ => (prime_residue_abel_limit q a).const_mul (g a))
  rw [unit_residue_sum_odd g hg] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primePeriodicDirichlet_expansion g s hs,mul_sum]
  apply sum_congr rfl
  intro a _
  ring

noncomputable def cyclicSkew {q : ℕ} [NeZero q] {A : Type*}
    (L : ZMod q → A) (C : A → A → ℝ) (h : ZMod q) : ℝ :=
  (∑ x : ZMod q, C (L x) (L (x+h))) / q

lemma cyclicSkew_odd {q : ℕ} [NeZero q] {A : Type*}
    (L : ZMod q → A) (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b)
    (h : ZMod q) : cyclicSkew L C (-h) = -cyclicSkew L C h := by
  have hs := Equiv.sum_comp (Equiv.addRight h) (fun x => C (L x) (L (x + -h)))
  simp only [Equiv.coe_addRight,add_neg_cancel_right] at hs
  unfold cyclicSkew
  rw [← hs]
  simp only [hC (L _) (L (_+h)),sum_neg_distrib,neg_div]

/-- A fixed cyclic process has zero Abel-prime average for every real
antisymmetric pair observable. This is not uniform in the cycle length. -/
theorem fixed_cyclic_prime_skew_abel_limit {q : ℕ} [NeZero q] {A : Type*}
    (L : ZMod q → A) (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet (primePeriodicCoeff (cyclicSkew L C)) s)
      (𝓝[>] 1) (𝓝 0) :=
  prime_periodic_odd_abel_limit _ (cyclicSkew_odd L C hC)

#print axioms prime_periodic_odd_abel_limit
#print axioms fixed_cyclic_prime_skew_abel_limit
end Erdos371.AbelPrimes
