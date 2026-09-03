import Submission.ParityOneHitDyadic

/-! Sharpness of uniform one-hit separation. Odd core primes cannot force two
given positions to collide with a forbidden class. Only parity forces a common
survivor residue. This concerns the one-hit method, not the Jacobsthal target. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

/-- A common phase can leave both zero and d alive whenever parity allows it. -/
theorem exists_phase_avoiding_zero_and (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) (hpar : 2 ∈ P → 2 ∣ d) :
    ∃ r : Phase P, (∀ q : P, 0 % q.val ≠ (r q).val) ∧
      (∀ q : P, d % q.val ≠ (r q).val) := by
  classical
  have htwo (q : P) (h : d % q.val = 1) : 2 < q.val := by
    have hq := (hP q.val q.property).two_le
    have hq2 : q.val ≠ 2 := by
      intro he
      have hd := Nat.mod_eq_zero_of_dvd (hpar (he ▸ q.property))
      rw [he,hd] at h
      omega
    omega
  let r : Phase P := fun q => if h : d % q.val = 1 then ⟨2,htwo q h⟩
    else ⟨1,(hP q.val q.property).two_le.trans_lt' (by decide)⟩
  refine ⟨r,?_,?_⟩
  · intro q
    dsimp [r]
    split_ifs <;> simp
  · intro q
    dsimp [r]
    split_ifs with h
    · change d % q.val ≠ 2
      omega
    · exact h

/-- Both positions occur in the doubled interval and have the same tail
residue. This gives an actual exceptional core phase, not a numerical probe. -/
theorem exists_core_residue_collision (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p d : ℕ) (hd0 : 0 < d) (hdm : d < 2*m) (hpd : p ∣ d)
    (hpar : 2 ∈ P → 2 ∣ d) :
    ∃ r : Phase P, ¬Set.InjOn (fun x => x % p)
      (populationSurvivors (range (2*m)) P r) := by
  obtain ⟨r,h0,hd⟩ := exists_phase_avoiding_zero_and P hP d hpar
  refine ⟨r,?_⟩
  intro hi
  have hz : 0 ∈ populationSurvivors (range (2*m)) P r :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),h0⟩
  have hd' : d ∈ populationSurvivors (range (2*m)) P r :=
    mem_filter.mpr ⟨mem_range.mpr hdm,hd⟩
  have he := hi hz hd' (by simp only [Nat.zero_mod,Nat.mod_eq_zero_of_dvd hpd])
  omega

/-- Without a parity core, the ambient-span cutoff is necessary as well as
sufficient for uniform injectivity. -/
theorem uniform_core_injective_iff_of_no_parity (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (h2 : 2 ∉ P) (m p : ℕ) (hp : 0 < p) :
    (∀ r : Phase P, Set.InjOn (fun x => x % p)
      (populationSurvivors (range (2*m)) P r)) ↔ 2*m ≤ p := by
  constructor
  · intro hi
    by_contra hlt
    obtain ⟨r,hr⟩ := exists_core_residue_collision P hP m p p hp (by omega)
      (dvd_refl _) (fun h => (h2 h).elim)
    exact hr (hi r)
  · intro hmp r x hx y hy hxy
    have hx' := mem_range.mp (mem_filter.mp hx).1
    have hy' := mem_range.mp (mem_filter.mp hy).1
    change x % p = y % p at hxy
    rwa [Nat.mod_eq_of_lt (by omega : x < p),Nat.mod_eq_of_lt (by omega : y < p)] at hxy

/-- For an odd tail prime, parity improves the threshold by exactly two.
Adding more core primes cannot improve this uniform threshold further. -/
theorem uniform_core_injective_iff_of_parity (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (h2 : 2 ∈ P) (m p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (∀ r : Phase P, Set.InjOn (fun x => x % p)
      (populationSurvivors (range (2*m)) P r)) ↔ m ≤ p := by
  constructor
  · intro hi
    by_contra hlt
    obtain ⟨r,hr⟩ := exists_core_residue_collision P hP m p (2*p)
      (by have := hp.pos; omega) (by omega) (dvd_mul_left p 2)
      (fun _ => dvd_mul_right 2 p)
    exact hr (hi r)
  · intro hmp r
    exact residue_injective_of_parity P _ m p subset_rfl h2 hp hp2 hmp r

/-- A single failed phase contributes at least the reciprocal of the entire
core period to the collision probability. The size of this loss is explicit. -/
theorem coreCollisionFraction_ge_single_phase (P R S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : Phase P)
    (hr : ¬∀ p ∈ R, Set.InjOn (fun x => x % p) (populationSurvivors S P r)) :
    1/(∏ p ∈ P, (p : ℝ)) ≤ coreCollisionFraction P R S := by
  classical
  have hprod : (∏ p ∈ P, (p : ℝ)) = ∏ p : P, (p.val : ℝ) :=
    (prod_coe_sort P (fun p : ℕ => (p : ℝ))).symm
  rw [hprod,coreCollisionFraction,phaseMean]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := single_le_sum (s := (univ : Finset (Phase P)))
    (f := fun r => if (∀ p ∈ R, Set.InjOn (fun x => x % p) (populationSurvivors S P r))
      then (0 : ℝ) else 1) (fun r _ => by dsimp only; split_ifs <;> norm_num) (mem_univ r)
  simpa only [if_neg hr] using hh


lemma coreCollisionFraction_eq_zero_iff (P R S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    coreCollisionFraction P R S = 0 ↔ ∀ r : Phase P, ∀ p ∈ R,
      Set.InjOn (fun x => x % p) (populationSurvivors S P r) := by
  constructor
  · intro hz r
    by_contra hr
    have hh := coreCollisionFraction_ge_single_phase P R S hP r hr
    rw [hz] at hh
    have hp : (0 : ℝ) < 1/(∏ p ∈ P, (p : ℝ)) :=
      one_div_pos.mpr (prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos))
    exact hp.not_ge hh
  · intro hi
    unfold coreCollisionFraction phaseMean
    have hs : (∑ r : Phase P, if (∀ p ∈ R, Set.InjOn (fun x => x % p)
        (populationSurvivors S P r)) then (0 : ℝ) else 1) = 0 := by
      apply sum_eq_zero
      intro r hr
      exact if_pos (hi r)
    rw [hs,zero_div]

/-- Exact vanishing criterion for the collision remainder. Uniform zero error
cannot be recovered below the parity/span cutoff by enlarging the core. -/
theorem coreCollisionFraction_zero_iff_cutoff (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (m : ℕ) :
    coreCollisionFraction P R (range (2*m)) = 0 ↔
      ∀ p ∈ R, (if 2 ∈ P then m else 2*m) ≤ p := by
  classical
  rw [coreCollisionFraction_eq_zero_iff P R _ hP]
  by_cases h2 : 2 ∈ P
  · simp only [if_pos h2]
    have hp2 (p : ℕ) (hp : p ∈ R) : p ≠ 2 := by
      intro he
      subst p
      exact disjoint_left.mp hPR h2 hp
    constructor
    · intro hi p hp
      exact (uniform_core_injective_iff_of_parity P hP h2 m p (hR p hp) (hp2 p hp)).mp
        (fun r => hi r p hp)
    · intro hl r p hp
      exact (uniform_core_injective_iff_of_parity P hP h2 m p (hR p hp) (hp2 p hp)).mpr
        (hl p hp) r
  · simp only [if_neg h2]
    constructor
    · intro hi p hp
      exact (uniform_core_injective_iff_of_no_parity P hP h2 m p (hR p hp).pos).mp
        (fun r => hi r p hp)
    · intro hl r p hp
      exact (uniform_core_injective_iff_of_no_parity P hP h2 m p (hR p hp).pos).mpr (hl p hp) r

#print axioms coreCollisionFraction_zero_iff_cutoff

#print axioms exists_phase_avoiding_zero_and
#print axioms uniform_core_injective_iff_of_no_parity
#print axioms uniform_core_injective_iff_of_parity
#print axioms coreCollisionFraction_ge_single_phase
end Erdos970.OneHitLogConcavity
