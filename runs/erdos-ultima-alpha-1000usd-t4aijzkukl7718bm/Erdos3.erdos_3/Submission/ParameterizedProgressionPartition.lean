import Submission.HigherDifferenceDilation
import Submission.ParameterizedPartitionCosts
import Submission.IntervalPartitionAssembly
import Submission.CanonicalPartialPartition

/-! Almost-complete, density-preserving flat progression partitions for
polynomial phases of arbitrary fixed degree. Every good cell is exactly a
proper arithmetic progression of the prescribed length. -/
namespace Erdos3ParameterizedProgressionPartition
open Finset Erdos3HigherPhaseDifferences Erdos3HigherPhaseRepresentation
  Erdos3HigherDifferenceDilation Erdos3HigherPartitionParameters Erdos3ParameterizedPartitionCosts
  Erdos3SimultaneousPolynomialRecurrence Erdos3IntervalPartitionAssembly
  Erdos3CanonicalPartialPartition Erdos3IntervalProgressionPartition
  Erdos3FinitePartitionIncrement Erdos3ProgressionFiberEquivalence Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

/-- Simultaneously flatten all supplied phases on all but 2^-s of an interval.
The output is a genuine partition; each nonexceptional cell is exactly a proper
length-L progression. The threshold and stride bounds are independent of the phases. -/
theorem polynomial_partition_of_recurrence {I : Type*} [Fintype I]
    (C : ℕ → ℕ)
    (hrec : ∀ k (v : I → ℂ), (∀ i, ‖v i‖ = 1) → ∀ u : ℕ,
      ∃ d : ℕ, 0 < d ∧ d ≤ 2^(C k*(u+1)) ∧
        ∀ i, ‖(v i)^(d^(k+1))-1‖ ≤ (1/2:ℝ)^u)
    (k : ℕ) (f : I → ℕ → Additive Circle) (hf : ∀ i, diffIter (k+1) (f i) = 0)
    (N L s : ℕ) (hL : 0 < L) (hN : flatThreshold C k L s ≤ N) :
    ∃ c : Fin N → Option (Fin N), ∃ w : I → Fin N → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧ cellMass c none ≤ (1/2 : ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i x.val)-w i j‖ ≤ (1/2 : ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ flatStride C k L s ∧
          (∀ n < L, a+n*d < N) ∧
          ∀ x : Fin N, c x = some j ↔ ∃ n : Fin L, x.val = a+n.val*d := by
  induction k generalizing f N s with
  | zero =>
    have hN0 : 0 < N := (flatThreshold_pos C 0 L s hL).trans_le hN
    letI : Nonempty (Fin N) := ⟨⟨0,hN0⟩⟩
    have hconst (i : I) (n : ℕ) : f i n = f i 0 :=
      congr_fun (diffIter_constant_of_next_zero (f i) 0 (hf i)) n
    refine ⟨progressionLabel N 1 L,fun i _ ↦ phase (f i 0),fun i _ ↦ phase_norm _,?_,?_,?_⟩
    · rw [cellMass_eq_card,progressionLabel_bad_card (by decide) hL,Fintype.card_fin]
      have hb : (1 : ℝ)*(L : ℝ)/(N : ℝ) ≤ (1/2 : ℝ)^s := by
        simpa only [Nat.cast_one] using
          block_loss_dyadic hN0 (le_refl 1) (by simpa only [one_mul,flatThreshold] using hN)
      apply le_trans _ hb
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast (Nat.mod_lt N (by simpa only [one_mul] using hL : 0 < 1*L)).le
    · intro x j _ i
      rw [hconst i x.val,sub_self,norm_zero]
      positivity
    · intro j hj
      obtain ⟨hpoints,hfiber⟩ := progressionLabel_fiber (by decide : 0 < 1) hL j hj
      exact ⟨j.val,1,by decide,le_refl _,hpoints,hfiber⟩
  | succ k ih =>
    let M := coarseLength C k L s
    let u := topAccuracy C k L s
    let B := topStride C k L s
    have hM : 0 < M := flatThreshold_pos C k L (s+1) hL
    have hN0 : 0 < N := (flatThreshold_pos C (k+1) L s hL).trans_le hN
    letI : Nonempty (Fin N) := ⟨⟨0,hN0⟩⟩
    letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
    let z : I → Additive Circle := fun i ↦ diffIter (k+1) (f i) 0
    have htop (i : I) : diffIter (k+1) (f i) = fun _ ↦ z i :=
      diffIter_constant_of_next_zero (f i) (k+1) (hf i)
    obtain ⟨d₀,hd₀,hdb,hcurve⟩ := hrec k (fun i ↦ phase (z i)) (fun i ↦ phase_norm _) u
    have hdB : d₀ ≤ B := hdb
    let z' : I → Additive Circle := fun i ↦ (d₀^(k+1)) • z i
    let F : Fin N → I → ℕ → Additive Circle := fun a i n ↦ f i (a.val+n*d₀)
    let g : Fin N → I → ℕ → Additive Circle := fun a i n ↦ F a i n-n.choose (k+1) • z' i
    have hcurve' (i : I) : ‖phase (z' i)-1‖ ≤ (1/2 : ℝ)^u := by
      simpa only [z',phase_nsmul] using hcurve i
    have hg (a : Fin N) (i : I) : diffIter (k+1) (g a i) = 0 :=
      subtract_top_difference_zero (k+1) (F a i) (z' i)
        (diffIter_dilate_top (k+1) (f i) (z i) (htop i) a.val d₀)
    have hinner (a : Fin N) := ih (g a) (hg a) M (s+1) (le_refl M)
    choose b w hw hbad hflat hgeom using hinner
    let c := coordinateRefineLabel N d₀ M hM b
    let w' : I → (Fin N × Fin M) → ℂ := fun i ab ↦ w ab.1 i ab.2
    have hw' (i : I) (ab : Fin N × Fin M) : ‖w' i ab‖ = 1 := hw ab.1 i ab.2
    have hbudget : B*M*2^(s+1) ≤ N := hN
    have hbad' : cellMass c none ≤ (1/2 : ℝ)^s := by
      have hb := coordinateRefineLabel_bad_mass hN0 hd₀ hM b
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (s+1)) hbad
      have ho := block_loss_dyadic hN0 hdB hbudget
      exact hb.trans ((add_le_add ho le_rfl).trans_eq (dyadic_halves s))
    have herr : (M : ℝ)^(k+1)*(1/2 : ℝ)^u ≤ (1/2 : ℝ)^(s+1) :=
      top_accuracy_error k M s
    have hflat' : ∀ x ab, c x = some ab → ∀ i,
        ‖phase (f i x.val)-w' i ab‖ ≤ (1/2 : ℝ)^s := by
      intro x ab hx i
      obtain ⟨hxa,hxb⟩ := (coordinateRefineLabel_some_iff hM b x ab.1 ab.2).mp hx
      let y : Fin M := ⟨x.val/d₀%M,Nat.mod_lt _ hM⟩
      have hval : f i x.val = F ab.1 i y.val := congrArg (f i) (progressionLabel_reconstruct hxa)
      have htoperr : ‖phase (F ab.1 i y.val)-phase (g ab.1 i y.val)‖ ≤ (1/2 : ℝ)^(s+1) :=
        (subtract_top_phase_error (F ab.1 i) (z' i) (k+1) M (hcurve' i) y.val y.isLt.le).trans herr
      have hinnererr : ‖phase (g ab.1 i y.val)-w ab.1 i ab.2‖ ≤ (1/2 : ℝ)^(s+1) :=
        hflat ab.1 y ab.2 hxb i
      change ‖phase (f i x.val)-w ab.1 i ab.2‖ ≤ _
      rw [hval]
      exact (norm_sub_le_norm_sub_add_norm_sub _ (phase (g ab.1 i y.val)) _).trans
        ((add_le_add htoperr hinnererr).trans_eq (dyadic_halves s))
    have hgeom' : ∀ ab, (cell c (some ab)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ flatStride C (k+1) L s ∧
          (∀ n < L, a+n*d < N) ∧
          ∀ x : Fin N, c x = some ab ↔ ∃ n : Fin L, x.val = a+n.val*d := by
      intro ab hab
      obtain ⟨a,d,hd,hdb,hpoints,hfiber⟩ := coordinateRefineLabel_geometry hd₀ hM b hgeom ab.1 ab.2 hab
      exact ⟨a,d,hd,hdb.trans (Nat.mul_le_mul_left _ hdB),hpoints,hfiber⟩
    obtain ⟨c',w'',hw'',hmass,hflat'',hgeom''⟩ := canonical_progression_partition
      c w' (fun i x ↦ phase (f i x.val)) hw' hflat' hgeom'
    exact ⟨c',w'',hw'',hmass.le.trans hbad',hflat'',hgeom''⟩

#print axioms polynomial_partition_of_recurrence
end Erdos3ParameterizedProgressionPartition
