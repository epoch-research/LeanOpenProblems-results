import Submission.PeriodicSieveOneEnd
import Submission.ExceptionSieveReduction

/-! Existence and uniqueness of the infinite component survive the finite
small-prime modification of each sieve. No uniform rejecting cutoff is asserted. -/
namespace Erdos952Investigation.FiniteSievePerturbation
open FiniteSieveReduction PeriodicSieveComponents SieveInfiniteUniqueness
open PeriodicSieveEnds ExceptionSieveReduction
set_option maxHeartbeats 0

lemma outside_of_large_norm (R : ℤ) (hR : 0 ≤ R) (v : GaussianInt)
    (hv : 2*R^2 < v.norm) : Outside R v := by
  by_contra hn
  have hh : |v.re| ≤ R ∧ |v.im| ≤ R := by simpa only [Outside,not_or,not_lt] using hn
  have hr : v.re^2 ≤ R^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hR] using hh.1)
  have hi : v.im^2 ≤ R^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hR] using hh.2)
  rw [gaussian_norm_sq] at hv
  linarith

/-- An infinite component of a locally finite finite perturbation contains
arbitrarily distant vertices lying in infinite original-sieve components. -/
lemma infinite_component_has_far_sieve_vertex {C : ℤ} {N : ℕ}
    (H : SimpleGraph GaussianInt) [H.LocallyFinite] (R : ℤ) (hR : 0 ≤ R)
    (hHG : ∀ {a b}, H.Adj a b → Outside R a → Outside R b → (sieveGraph C N).Adj a b)
    {z : GaussianInt} (hz : {v | H.Reachable z v}.Infinite) (F : ℤ) :
    ∃ v : GaussianInt, H.Reachable z v ∧ Outside F v ∧
      {w | (sieveGraph C N).Reachable v w}.Infinite := by
  obtain ⟨x,hx0,hx,hxa⟩ := (RayReduction.ray_iff_infinite_component H z).mpr hz
  let B := max R (max F 0)
  have hB : 0 ≤ B := (le_max_right F 0).trans (le_max_right R (max F 0))
  obtain ⟨T,hT⟩ := injective_escapes_norm x hx (2*B^2)
  have hout (n : ℕ) : Outside B (x (T+n)) :=
    outside_of_large_norm B hB _ (hT _ (by omega))
  have houtR (n : ℕ) : Outside R (x (T+n)) :=
    (hout n).imp (fun h => (le_max_left R (max F 0)).trans_lt h)
      (fun h => (le_max_left R (max F 0)).trans_lt h)
  have hstep (n : ℕ) : (sieveGraph C N).Adj (x (T+n)) (x (T+(n+1))) := by
    apply hHG (by simpa only [Nat.add_assoc] using hxa (T+n)) (houtR n) (houtR (n+1))
  have hr (n : ℕ) : (sieveGraph C N).Reachable (x T) (x (T+n)) := by
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans (hstep n).reachable
  have hroot (n : ℕ) : H.Reachable z (x n) := by
    induction n with
    | zero => rw [hx0]
    | succ n ih => exact ih.trans (hxa n).reachable
  refine ⟨x T,hroot T,?_,?_⟩
  · have hh := hout 0
    have hFB : F ≤ B := (le_max_left F 0).trans (le_max_right R (max F 0))
    simpa only [Nat.add_zero] using hh.imp (hFB.trans_lt) (hFB.trans_lt)
  · have hinj : Function.Injective (fun n : ℕ => x (T+n)) := hx.comp (fun _ _ hij => Nat.add_left_cancel hij)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro w ⟨n,rfl⟩
    exact hr n

/-- A finite perturbation of a finite Gaussian sieve has at most one infinite
component, provided it remains locally finite. -/
theorem finite_perturbation_infinite_unique {C : ℤ} {N : ℕ}
    (H : SimpleGraph GaussianInt) [H.LocallyFinite] (R : ℤ) (hR : 0 ≤ R)
    (hGH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b)
    (hHG : ∀ {a b}, H.Adj a b → Outside R a → Outside R b → (sieveGraph C N).Adj a b)
    {z w : GaussianInt} (hz : {v | H.Reachable z v}.Infinite)
    (hw : {v | H.Reachable w v}.Infinite) : H.Reachable z w := by
  obtain ⟨u,_,_,hu⟩ := infinite_component_has_far_sieve_vertex H R hR hHG hz 0
  obtain ⟨F,_,a,ha⟩ := far_component_detours hu H R hR hGH
  obtain ⟨v,hzv,hvF,hv⟩ := infinite_component_has_far_sieve_vertex H R hR hHG hz F
  obtain ⟨t,hwt,htF,ht⟩ := infinite_component_has_far_sieve_vertex H R hR hHG hw F
  have hav := ha v (infinite_components_unique hu hv) hvF
  have hat := ha t (infinite_components_unique hu ht) htF
  exact hzv.trans ((hav.symm.trans hat).trans hwt.symm)

lemma norm_large_of_outside (N : ℕ) (z : GaussianInt) (hz : Outside (N : ℤ) z) :
    (N : ℤ)^2 < z.norm := by
  have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg _
  rw [gaussian_norm_sq]
  rcases hz with hr | hi
  · nlinarith [sq_abs z.re,sq_nonneg z.im]
  · nlinarith [sq_abs z.im,sq_nonneg z.re]

lemma candidate_adj_of_sieve_outside {C : ℤ} {N : ℕ} {z w : GaussianInt}
    (h : (sieveGraph C N).Adj z w) (hz : Outside (N : ℤ) z) (hw : Outside (N : ℤ) w) :
    (candidateGraph C N).Adj z w :=
  ⟨(candidate_iff_allowed_of_large (norm_large_of_outside N z hz)).mpr h.1,
    (candidate_iff_allowed_of_large (norm_large_of_outside N w hw)).mpr h.2.1,h.2.2⟩

lemma sieve_adj_of_candidate_outside {C : ℤ} {N : ℕ} {z w : GaussianInt}
    (h : (candidateGraph C N).Adj z w) (hz : Outside (N : ℤ) z) (hw : Outside (N : ℤ) w) :
    (sieveGraph C N).Adj z w :=
  ⟨(candidate_iff_allowed_of_large (norm_large_of_outside N z hz)).mp h.1,
    (candidate_iff_allowed_of_large (norm_large_of_outside N w hw)).mp h.2.1,h.2.2⟩

/-- At each cutoff, the exception-retaining candidate graph has at most one
infinite component. This does not say the component of `3` belongs to it. -/
theorem candidate_infinite_components_unique {C : ℤ} {N : ℕ} {z w : GaussianInt}
    (hz : {v | (candidateGraph C N).Reachable z v}.Infinite)
    (hw : {v | (candidateGraph C N).Reachable w v}.Infinite) :
    (candidateGraph C N).Reachable z w :=
  finite_perturbation_infinite_unique (candidateGraph C N) (N : ℤ) (Int.natCast_nonneg _)
    candidate_adj_of_sieve_outside sieve_adj_of_candidate_outside hz hw

/-- Existence of some infinite component is unchanged by keeping the small
prime exceptions. The root is deliberately not fixed in this equivalence. -/
theorem candidate_has_infinite_iff_sieve_ray (C : ℤ) (N : ℕ) :
    (∃ z : GaussianInt, {v | (candidateGraph C N).Reachable z v}.Infinite) ↔
      HasSieveRay C N := by
  rw [sieve_ray_iff_infinite_component]
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨v,_,_,hv⟩ := infinite_component_has_far_sieve_vertex (candidateGraph C N)
      (N : ℤ) (Int.natCast_nonneg _) sieve_adj_of_candidate_outside hz 0
    exact ⟨v,hv⟩
  · rintro ⟨z,hz⟩
    exact infinite_component_survives_finite_change hz (candidateGraph C N)
      (N : ℤ) (Int.natCast_nonneg _) candidate_adj_of_sieve_outside

#print axioms finite_perturbation_infinite_unique
#print axioms candidate_infinite_components_unique
#print axioms candidate_has_infinite_iff_sieve_ray
end Erdos952Investigation.FiniteSievePerturbation
