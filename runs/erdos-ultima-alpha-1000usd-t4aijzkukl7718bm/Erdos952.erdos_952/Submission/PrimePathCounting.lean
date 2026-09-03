import Submission.FiniteCertificates
import Submission.SievePeriodicDrift

/-! An exact counting formulation of the Gaussian moat negation. A prime ray
forces linearly many starting points of arbitrarily long finite prime paths.
No upper bound contradicting that lower bound is asserted here. -/
namespace Erdos952Investigation.PrimePathCounting
open SievePeriodicDrift
set_option maxHeartbeats 0

/-- The starting vertex is required to be prime even for a zero-edge path. -/
def Starts (C : ℤ) (L : ℕ) (z : GaussianInt) : Prop :=
  Prime z ∧ Nonempty (RayReduction.Prefix (primeGraph C) z L)

noncomputable def startsInBall (C R : ℤ) (L : ℕ) : Finset GaussianInt := by
  classical
  exact (norm_sublevel_finite (R^2)).toFinset.filter (Starts C L)

lemma mem_startsInBall (C R : ℤ) (L : ℕ) (z : GaussianInt) :
    z ∈ startsInBall C R L ↔ z.norm ≤ R^2 ∧ Starts C L z := by
  classical
  simp [startsInBall]

lemma starts_antitone (C : ℤ) {L M : ℕ} (hLM : L ≤ M) {z : GaussianInt}
    (hz : Starts C M z) : Starts C L z :=
  ⟨hz.1,hz.2.map (RayReduction.restrict (primeGraph C) z hLM)⟩

lemma starts_of_prime_ray (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (a L : ℕ) :
    Starts C L (x a) := by
  refine ⟨(h a).1,⟨⟨fun i => x (a+i.val),by simp,?_,?_⟩⟩⟩
  · intro i j he
    exact Fin.ext (Nat.add_left_cancel (hx he))
  · intro i
    refine ⟨(h _).1,(h _).1,?_,?_⟩
    · intro he
      have hh := hx he
      simp only [Fin.val_castSucc,Fin.val_succ] at hh
      omega
    · simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_assoc] using (h (a+i.val)).2

lemma norm_le_taxicab_sq (z : GaussianInt) : z.norm ≤ (taxicab z)^2 := by
  have hr := sq_abs z.re
  have hi := sq_abs z.im
  have hp := mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)
  simp only [gaussian_norm_sq,taxicab]
  nlinarith

lemma ray_norm_bound (x : ℕ → GaussianInt) (C : ℤ)
    (hx0 : x 0 = (3 : GaussianInt))
    (hs : ∀ n, (x (n+1)-x n).norm < C) (n : ℕ) :
    (x n).norm ≤ ((n : ℤ)*C+3)^2 := by
  have hC : 0 ≤ C := (GaussianInt.norm_nonneg _).trans (hs 0).le
  have hh := taxicab_drift_le x C hs 0 n
  simp only [Nat.zero_add,hx0] at hh
  have ht := taxicab_add_le (x n-3) (3 : GaussianInt)
  have h3 : taxicab (3 : GaussianInt) = 3 := by norm_num [taxicab]
  rw [sub_add_cancel,h3] at ht
  have hz : 0 ≤ taxicab (x n) := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg _
  have hb := norm_le_taxicab_sq (x n)
  have hlarge : taxicab (x n) ≤ (n : ℤ)*C+3 := by omega
  nlinarith

/-- The first M+1 vertices of a ray from 3 lie in this disk. Every one is a
starting point for a prime path of any prescribed finite length L. -/
theorem ray_forces_linear_count (x : ℕ → GaussianInt) (C : ℤ)
    (hx0 : x 0 = (3 : GaussianInt)) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (M L : ℕ) :
    M+1 ≤ (startsInBall C ((M : ℤ)*C+3) L).card := by
  classical
  have hC : 0 ≤ C := (GaussianInt.norm_nonneg _).trans (h 0).2.le
  have hmem (i : Fin (M+1)) : x i.val ∈ startsInBall C ((M : ℤ)*C+3) L := by
    apply (mem_startsInBall _ _ _ _).mpr
    refine ⟨?_,starts_of_prime_ray x C hx h i.val L⟩
    have hh := ray_norm_bound x C hx0 (fun n => (h n).2) i.val
    have hi : (i.val : ℤ) ≤ M := by exact_mod_cast (show i.val ≤ M by omega)
    have hmul := mul_le_mul_of_nonneg_right hi hC
    have hnonneg : (0 : ℤ) ≤ (i.val : ℤ)*C := mul_nonneg (Int.natCast_nonneg _) hC
    nlinarith
  let f : Fin (M+1) → (startsInBall C ((M : ℤ)*C+3) L) :=
    fun i => ⟨x i.val,hmem i⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (hx (congrArg Subtype.val he))
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin,Fintype.card_coe] using hh

/-- This is the missing estimate in a path-counting approach, not a theorem
asserting that the estimate holds. The length L may depend on the radius. -/
def CountingObstruction : Prop :=
  ∀ C : ℤ, 0 < C → ∃ M L : ℕ, 0 < M ∧
    (startsInBall C ((M : ℤ)*C+3) L).card ≤ M

theorem counting_obstruction_implies_disproof (hc : CountingObstruction) :
    ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C := by
  intro h
  obtain ⟨C,hCinf⟩ := gaussian_moat_fixed_seed_equivalence.mp h
  obtain ⟨x,hx0,hx,ha⟩ :=
    (RayReduction.ray_iff_infinite_component (primeGraph C) 3).mpr hCinf
  have hp (n : ℕ) : Prime (x n) ∧ (x (n+1)-x n).norm < C :=
    ⟨(ha n).1,(ha n).2.2.2⟩
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (hp 0).2
  obtain ⟨M,L,_,hML⟩ := hc C hC
  have hh := ray_forces_linear_count x C hx0 hx hp M L
  omega

/-- If the original conjecture is false, then in each fixed finite ball a
sufficiently long finite prime path has no starting point. No uniform length
bound over all balls is asserted. -/
theorem eventually_no_starts_in_fixed_ball
    (hno : ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (C R : ℤ) :
    ∃ L : ℕ, startsInBall C R L = ∅ := by
  classical
  have hEach (z : GaussianInt) : ∃ L, ¬ Starts C L z := by
    by_contra! hh
    obtain ⟨x,_,hx,ha⟩ := RayReduction.ray_of_prefixes (primeGraph C) z
      (fun L => (hh L).2)
    exact hno ⟨x,C,hx,fun n => ⟨(ha n).1,(ha n).2.2.2⟩⟩
  choose ell hell using hEach
  let S := (norm_sublevel_finite (R^2)).toFinset
  let L := S.sup ell
  refine ⟨L,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro z hz
  obtain ⟨hn,hs⟩ := (mem_startsInBall C R L z).mp hz
  have hzS : z ∈ S := by simpa [S] using hn
  have hzL : ell z ≤ L := Finset.le_sup hzS
  exact hell z (starts_antitone C hzL hs)

/-- An exact reformulation, not a settlement: the required counting
obstruction has not been established unconditionally. -/
theorem negation_iff_counting_obstruction :
    (¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔ CountingObstruction := by
  refine ⟨?_,counting_obstruction_implies_disproof⟩
  intro h C _
  obtain ⟨L,hL⟩ := eventually_no_starts_in_fixed_ball h C (C+3)
  refine ⟨1,L,by decide,?_⟩
  simpa only [Nat.cast_one,one_mul,hL,Finset.card_empty] using (show 0 ≤ 1 by omega)

#print axioms ray_forces_linear_count
#print axioms counting_obstruction_implies_disproof
#print axioms negation_iff_counting_obstruction
end Erdos952Investigation.PrimePathCounting
