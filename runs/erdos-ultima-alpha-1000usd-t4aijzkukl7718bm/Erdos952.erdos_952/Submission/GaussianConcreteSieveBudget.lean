import Submission.GaussianNormalizedPathPatterns
import Submission.GaussianAdmissibleRootDensities
import Submission.GaussianLevelSupports
import Submission.GaussianPrimePatternBudget

/-! Concrete Selberg budget over ALL admissible normalized bounded-step
path shapes. Covering and strict local root-density conditions are proved,
not assumed. The still-missing estimate is explicitly a smallness bound on
the resulting finite sum of reciprocal denominators. -/
namespace Erdos952Investigation.GaussianConcreteSieveBudget
open GaussianNormalizedPathPatterns GaussianAdmissibleRootDensities GaussianLevelSupports
open GaussianPrimePatternBudget GaussianSelbergMainOptimization GaussianPolynomialBoxCounts
open GaussianHigherPolynomialCounts GaussianIteratedSmoothing PrimePathCounting
open FiniteSelbergOptimization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

/-- The actual finite sum, not a guessed density or a formal free parameter. -/
def reciprocalBudget {ι : Type*} [Fintype ι] (C : ℤ) (L A : ℕ) (g : ι → GaussianInt) : ℝ :=
  ∑ s : AdmissibleShape C L, 1/denominator (levelSupports g A)
    (fun i => localDensity (patternPolynomial s.val.val) (g i))

def entropyOrder (C : ℤ) (L : ℕ) : ℕ := Nat.clog 4 (Fintype.card (AdmissibleShape C L))

def smoothingOrder (C : ℤ) (L R : ℕ) : ℕ := 4*Nat.clog 2 R+entropyOrder C L

lemma family_card_le_pow (C : ℤ) (L : ℕ) :
    Fintype.card (AdmissibleShape C L) ≤ 4^(entropyOrder C L) :=
  Nat.le_pow_clog (by decide) _

lemma entropyOrder_le_alphabet (C : ℤ) (L : ℕ) :
    entropyOrder C L ≤ Nat.clog 4 ((Fintype.card (Step C))^L) :=
  Nat.clog_mono_right 4 (admissible_shape_card_le C L)

/-- Every starting point is covered on a common tail, and every retained
shape satisfies all optimizer density hypotheses. Only the prime family
and the norm level remain free choices. -/
theorem concrete_starts_bound_on_tail {ι : Type*} [Fintype ι]
    (C : ℤ) (L A R : ℕ) (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (hA : 1 ≤ A) (hR : 0 < R) (hAR : 16*A ≤ R)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) :
    ∃ N, ∀ b ≥ N, higherCount (Starts C L) (x b) R (smoothingOrder C L R) ≤
      (R : ℝ)^2*reciprocalBudget C L A g+1/16 := by
  let J := AdmissibleShape C L
  let z : J → Fin (L+1) → GaussianInt := fun s => s.val.val
  have hD : DownClosed (levelSupports g A) :=
    levelSupports_downClosed g (fun i => (hg i).ne_zero) A
  have hD0 : ∅ ∈ levelSupports g A := empty_mem_levelSupports g A hA
  have hρ (s : J) (i : ι) :
      0 < GaussianWeightedSieve.rho (patternPolynomial (z s)) (g i) ∧
        GaussianWeightedSieve.rho (patternPolynomial (z s)) (g i) < (g i).norm.natAbs :=
    admissible_root_density_bounds s.val.val s.property (g i) (hg i)
  have hl (s : J) (u : Finset ι) (hu : u ∈ levelSupports g A) : (modulus g u).norm.natAbs ≤ A :=
    (mem_levelSupports g A u).mp hu
  obtain ⟨N₁,hN₁⟩ := finite_family_tail_bound z (fun _ => levelSupports g A)
    (fun _ => hD) (fun _ => hD0) (fun _ => g) (fun _ => hg) (fun _ => hc) hρ
    x hx R (Nat.clog 2 R) (entropyOrder C L) A hR hAR (Nat.le_pow_clog (by decide) R)
    (family_card_le_pow C L) hl
  obtain ⟨N₂,hN₂⟩ := starts_covered_on_tail C L x hx R (smoothingOrder C L R)
  refine ⟨max N₁ N₂,?_⟩
  intro b hb
  exact (hN₂ b ((le_max_right _ _).trans hb)).trans (hN₁ b ((le_max_left _ _).trans hb))

/-- Final explicit necessary inequality supplied by this sieve approach.
No covering assumption, admissibility assumption on arbitrary paths, or
unproved local-density bound occurs in its hypotheses. -/
theorem prime_ray_concrete_budget {ι : Type*} [Fintype ι]
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (L M A : ℕ) (hM : 0 < M) (hA : 1 ≤ A)
    (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j))) (hAR : 16*A ≤ 5*(M*C.toNat)) :
    (M : ℝ)+1 ≤ 625*((smoothingOrder C L (5*(M*C.toNat)) : ℝ)+1)^2*
      (((5*(M*C.toNat) : ℕ) : ℝ)^2*reciprocalBudget C L A g+1/16) := by
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (hp 0).2
  have hCn : 0 < C.toNat := by omega
  have hR : 0 < 5*(M*C.toNat) := Nat.mul_pos (by decide) (Nat.mul_pos hM hCn)
  obtain ⟨N,hN⟩ := concrete_starts_bound_on_tail C L A (5*(M*C.toNat)) g hg hc hA hR hAR x hx
  have hx' : Function.Injective (fun n => x (N+n)) := fun i j he => Nat.add_left_cancel (hx he)
  have hp' (n : ℕ) : Prime (x (N+n)) ∧ (x (N+(n+1))-x (N+n)).norm < C := by
    simpa only [Nat.add_assoc] using hp (N+n)
  have hl := GaussianSmoothingBuckets.ray_forces_higher_smoothed_count (fun n => x (N+n)) C hx' hp'
    M L (smoothingOrder C L (5*(M*C.toNat))) hM
  simp only [Nat.add_zero] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (hN N le_rfl) (by positivity))

/-- A precise still-unproved sufficient criterion. It concerns an explicit
finite family of Gaussian primes and the canonical level support, not the
existence of unspecified good sieve weights. -/
def DenominatorObstruction : Prop :=
  ∀ C : ℤ, 0 < C → ∃ (q L M A : ℕ) (g : Fin q → GaussianInt),
    (∀ i, Prime (g i)) ∧ Pairwise (fun i j => IsCoprime (g i) (g j)) ∧
      0 < M ∧ 1 ≤ A ∧ 16*A ≤ 5*(M*C.toNat) ∧
      625*((smoothingOrder C L (5*(M*C.toNat)) : ℝ)+1)^2*
        (((5*(M*C.toNat) : ℕ) : ℝ)^2*reciprocalBudget C L A g+1/16) < (M : ℝ)+1

/-- Conditional only: DenominatorObstruction has NOT been proved. -/
theorem denominator_obstruction_implies_disproof (h : DenominatorObstruction) :
    ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C := by
  rintro ⟨x,C,hx,hp⟩
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (hp 0).2
  obtain ⟨q,L,M,A,g,hg,hc,hM,hA,hAR,hsmall⟩ := h C hC
  exact hsmall.not_ge (prime_ray_concrete_budget x C hx hp L M A hM hA g hg hc hAR)

#print axioms concrete_starts_bound_on_tail
#print axioms prime_ray_concrete_budget
#print axioms denominator_obstruction_implies_disproof
end
end Erdos952Investigation.GaussianConcreteSieveBudget
