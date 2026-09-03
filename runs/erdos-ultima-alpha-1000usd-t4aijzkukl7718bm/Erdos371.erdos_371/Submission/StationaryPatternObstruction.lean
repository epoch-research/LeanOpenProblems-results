import Submission.StationaryMomentObstruction

/-! The finite stationary moment obstruction persists for arbitrary finite
patterns of total observed mass within the CRT budget. This remains a finite
model, with ties and without the actual prime-factor marginal or dilation law;
it is NOT a counterexample to the original arithmetic conjecture. -/
namespace Erdos371.StationaryPatternObstruction
open Finset StationaryMomentObstruction
set_option autoImplicit false

noncomputable def splitValue (i : Fin 7) : ℝ := (splitDirection i : ℝ)
noncomputable def mergeValue (i : Fin 7) : ℝ := (mergeDirection i : ℝ)
noncomputable def transitionReal (i j : Fin 7) : ℝ := (transitionWeight i j : ℝ)

lemma transitionReal_eq (i j : Fin 7) :
    transitionReal i j=2+splitValue i*mergeValue j := by
  have h : ∀ i j : Fin 7, (transitionWeight i j : ℤ)=2+splitDirection i*mergeDirection j := by
    decide +kernel
  have he := congrArg (fun z : ℤ => (z : ℝ)) (h i j)
  simpa only [transitionReal,splitValue,mergeValue,Int.cast_natCast,Int.cast_add,Int.cast_mul,Int.cast_ofNat] using he

lemma split_mul_merge_zero (i : Fin 7) : splitValue i*mergeValue i=0 := by
  have h : ∀ i : Fin 7, splitDirection i*mergeDirection i=0 := by decide +kernel
  have he := congrArg (fun z : ℤ => (z : ℝ)) (h i)
  simpa only [splitValue,mergeValue,Int.cast_mul,Int.cast_zero] using he

noncomputable def pathContinuation : List (Finset (Fin 7)) → Fin 7 → ℝ
  | [], _ => 1
  | A::L, i => ∑ j ∈ A, transitionReal i j*pathContinuation L j

noncomputable def observationPathMass : List (Finset (Fin 7)) → ℝ
  | [] => 1
  | A::L => ∑ i ∈ A, pathContinuation L i

lemma pathContinuation_affine (L : List (Finset (Fin 7))) :
    ∃ a b : ℝ, ∀ i, pathContinuation L i=a+b*splitValue i := by
  cases L with
  | nil => exact ⟨1,0,by intro i; simp [pathContinuation]⟩
  | cons A L =>
    refine ⟨2*(∑ j ∈ A, pathContinuation L j),∑ j ∈ A, mergeValue j*pathContinuation L j,?_⟩
    intro i
    simp only [pathContinuation,transitionReal_eq,add_mul,sum_add_distrib,← mul_sum]
    rw [show (∑ j ∈ A, splitValue i*mergeValue j*pathContinuation L j)=
        splitValue i*(∑ j ∈ A, mergeValue j*pathContinuation L j) by rw [mul_sum]; apply sum_congr rfl; intros; ring]
    ring

lemma merge_weighted_continuation (B : Finset (Fin 7)) (L : List (Finset (Fin 7))) :
    ∃ a : ℝ, (∑ j ∈ B, mergeValue j*pathContinuation L j)=a*(∑ j ∈ B, mergeValue j) := by
  obtain ⟨a,b,hab⟩ := pathContinuation_affine L
  refine ⟨a,?_⟩
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [hab]
  calc
    _ = a*mergeValue j+b*(splitValue j*mergeValue j) := by ring
    _ = _ := by rw [split_mul_merge_zero,mul_zero,add_zero]

lemma observationPathMass_two_cons (A B : Finset (Fin 7)) (L : List (Finset (Fin 7)))
    (hAB : (∑ i ∈ A, splitValue i)*(∑ j ∈ B, mergeValue j)=0) :
    observationPathMass (A::B::L)=2*A.card*observationPathMass (B::L) := by
  obtain ⟨a,ha⟩ := merge_weighted_continuation B L
  have he (i : Fin 7) : pathContinuation (B::L) i =
      2*observationPathMass (B::L)+splitValue i*(∑ j ∈ B, mergeValue j*pathContinuation L j) := by
    simp only [pathContinuation,observationPathMass,transitionReal_eq,add_mul,sum_add_distrib,← mul_sum]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [observationPathMass]
  simp_rw [he,ha,sum_add_distrib,← sum_mul,sum_const,nsmul_eq_mul]
  have hz : (∑ i ∈ A, splitValue i)*(a*(∑ j ∈ B, mergeValue j))=0 := by
    calc
      _ = a*((∑ i ∈ A, splitValue i)*(∑ j ∈ B, mergeValue j)) := by ring
      _ = 0 := by rw [hAB,mul_zero]
  rw [hz,add_zero]
  ring

def CompatibleObservations : List (Finset (Fin 7)) → Prop
  | [] => True
  | [_] => True
  | A::B::L => (∑ i ∈ A, splitValue i)*(∑ j ∈ B, mergeValue j)=0 ∧ CompatibleObservations (B::L)

/-- Every nonconstant transition contribution vanishes under the indicated
adjacent observation conditions, for arbitrary path length. -/
theorem compatible_path_mass (L : List (Finset (Fin 7))) (hL : L≠[])
    (hcompat : CompatibleObservations L) :
    observationPathMass L=(2 : ℝ)^(L.length-1)*(L.map (fun A => (A.card : ℝ))).prod := by
  induction L with
  | nil => exact (hL rfl).elim
  | cons A L ih =>
    cases L with
    | nil => simp [observationPathMass,pathContinuation]
    | cons B L =>
      obtain ⟨hAB,hrest⟩ := hcompat
      rw [observationPathMass_two_cons A B L hAB,ih (by simp) hrest]
      simp only [List.length_cons,List.map_cons,List.prod_cons,Nat.add_sub_cancel]
      rw [pow_succ]
      ring

lemma observation_classes_compatible (s t : Finset ℕ) (U V : Finset Bool)
    (hst : (∑ a ∈ s, a)+(∑ b ∈ t, b)≤966) :
    (∑ i ∈ observationClass s U, splitValue i)*
      (∑ j ∈ observationClass t V, mergeValue j)=0 := by
  have hh := small_moment_factors s t U V hst
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hh
  simp only [gapMoment,transitionPower_one,Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat] at hr
  have he : (∑ i ∈ observationClass s U, ∑ j ∈ observationClass t V, transitionReal i j)=
      2*(observationClass s U).card*(observationClass t V).card+
        (∑ i ∈ observationClass s U, splitValue i)*(∑ j ∈ observationClass t V, mergeValue j) := by
    simp only [transitionReal_eq,sum_add_distrib,← mul_sum,← sum_mul,sum_const,nsmul_eq_mul]
    ring
  change (∑ i ∈ observationClass s U, ∑ j ∈ observationClass t V, transitionReal i j)=_ at hr
  linarith

abbrev Observation := Finset ℕ × Finset Bool

def observedMass (o : Observation) : ℕ := ∑ a ∈ o.1, a

def observationStateSet (o : Observation) : Finset (Fin 7) := observationClass o.1 o.2

lemma low_total_mass_compatible (L : List Observation)
    (hL : (L.map observedMass).sum≤966) : CompatibleObservations (L.map observationStateSet) := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    cases L with
    | nil => trivial
    | cons b L =>
      have hmass : observedMass a+observedMass b+(L.map observedMass).sum≤966 := by
        simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using hL
      have hp : observedMass a+observedMass b≤966 := by omega
      have ht : ((b::L).map observedMass).sum≤966 := by simp only [List.map_cons,List.sum_cons]; omega
      refine ⟨?_,ih ht⟩
      exact observation_classes_compatible a.1 b.1 a.2 b.2 hp

/-- All finite low-total-mass patterns factor as under the independent
uniform state model, despite the already checked biased adjacent comparison.
This does not represent the actual arithmetic prime-factor process. -/
theorem low_mass_patterns_factor (L : List Observation) (hne : L≠[])
    (hL : (L.map observedMass).sum≤966) :
    observationPathMass (L.map observationStateSet)=
      (2 : ℝ)^(L.length-1)*(L.map (fun o => ((observationStateSet o).card : ℝ))).prod := by
  have h := compatible_path_mass (L.map observationStateSet) (by simpa using hne)
    (low_total_mass_compatible L hL)
  simpa only [List.length_map,List.map_map,Function.comp_def] using h

lemma pathContinuation_univ (k : ℕ) (i : Fin 7) :
    pathContinuation (List.replicate k (univ : Finset (Fin 7))) i=(14 : ℝ)^k := by
  induction k generalizing i with
  | zero => simp [pathContinuation]
  | succ k ih =>
    simp only [List.replicate_succ,pathContinuation,ih,← sum_mul,transitionReal,
      ← Nat.cast_sum,transition_row_mass]
    rw [pow_succ]
    ring

lemma total_path_mass (k : ℕ) :
    observationPathMass (List.replicate (k+1) (univ : Finset (Fin 7)))=7*(14 : ℝ)^k := by
  simp [List.replicate_succ,observationPathMass,pathContinuation_univ]

/-- After division by the actual total path mass, all low-mass pattern
probabilities equal those of independent uniform states. -/
theorem normalized_low_mass_patterns_factor (L : List Observation) (hne : L≠[])
    (hL : (L.map observedMass).sum≤966) :
    observationPathMass (L.map observationStateSet)/(7*(14 : ℝ)^(L.length-1))=
      (L.map (fun o => ((observationStateSet o).card : ℝ))).prod/(7 : ℝ)^L.length := by
  rw [low_mass_patterns_factor L hne hL]
  have hlen : L.length=(L.length-1)+1 := by
    have hp : 0<L.length := List.length_pos_iff.mpr hne
    omega
  have hp : (7 : ℝ)^L.length=7*(7 : ℝ)^(L.length-1) := by
    conv_lhs => rw [hlen,pow_succ]
    ring
  rw [hp,show (14 : ℝ)=2*7 by norm_num,mul_pow]
  field_simp

#print axioms normalized_low_mass_patterns_factor

#print axioms compatible_path_mass
#print axioms low_mass_patterns_factor
#print axioms StationaryMomentObstruction.largest_comparison_biased
end Erdos371.StationaryPatternObstruction
