import Submission.TaggedFeatureLocalization

/-! End-to-end bounded strong U3 regularity with stable local quadratic-factor
representations. All coarse geometric parameters use only the STRICT prior
accuracy prefix. The actual coarse/fine and local errors are independently
prescribed and verified. -/
namespace Erdos3StrongLocalQuadraticRepresentation
open Finset Erdos3TaggedFeatureLocalization Erdos3BudgetedStrongQuadraticRegularity
  Erdos3BudgetedStrongRegularity Erdos3SummableStageBudgets
  Erdos3AdaptiveStrongRegularity Erdos3StrongQuadraticRegularity
  Erdos3WeakQuadraticRegularity Erdos3NormalizedQuadraticInverse
  Erdos3NormalizedQuadraticPowerBounds Erdos3SingleExponentialQuadraticInverse
  Erdos3CommonQuadraticWindow Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3ClippedWeakRegularity Erdos3FiniteUniformity Erdos3LocalQuadraticInverse
open scoped BigOperators Classical
set_option maxHeartbeats 7000000

noncomputable def priorRank (δ : ℕ → ℝ) (m : ℕ) : ℕ :=
  (range m).sup (fun j ↦ normalizedRank (δ j))

noncomputable def priorTolerance (δ : ℕ → ℝ) (τ : ℝ) (m : ℕ) : ℕ :=
  (range m).sup (stageTolerance (fun j ↦ gainWeight (δ j)) τ)+1

lemma priorRank_le (δ : ℕ → ℝ) {j m : ℕ} (hj : j < m) :
    normalizedRank (δ j) ≤ priorRank δ m :=
  le_sup (f := fun j ↦ normalizedRank (δ j)) (mem_range.mpr hj)

lemma priorTolerance_le (δ : ℕ → ℝ) (τ : ℝ) {j m : ℕ} (hj : j < m) :
    stageTolerance (fun j ↦ gainWeight (δ j)) τ j ≤ priorTolerance δ τ m := by
  exact (le_sup (mem_range.mpr hj)).trans (Nat.le_succ _)

lemma priorTolerance_pos (δ : ℕ → ℝ) (τ : ℝ) (m : ℕ) : 0 < priorTolerance δ τ m := by
  unfold priorTolerance
  omega

lemma gainWeight_le_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : gainWeight δ ≤ 1 := by
  have hC : 1 ≤ correlationDenominator := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) extractionConstant_ge_one 5
    norm_num at hp
    unfold correlationDenominator
    nlinarith
  have hgain : regularityGain δ ≤ 1 := by
    unfold regularityGain
    apply (div_le_one correlationDenominator_pos).mpr
    exact (pow_le_one₀ hδ.le hδ1).trans hC
  have h : (gainWeight δ : ℝ) ≤ 1 := by rw [gainWeight_coe hδ]; exact hgain
  exact_mod_cast h

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- No approximation or inverse hypothesis is left unproved. Distribution of
the local phases and an actual configuration-count lower bound are not asserted. -/
theorem strong_local_quadratic_representation
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j ≤ 1)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) {u : ℕ} (hu : 0 < u) :
    let ρ := fun j ↦ gainWeight (δ j)
    let z := stageTolerance ρ τ
    ∃ m : ℕ, ∃ t : List (TaggedTest G), ∃ g g' : G → ℝ,
      ∃ C : Finset (AddChar G ℂ), ∃ r : ℝ,
      m ≤ complexityBudget (blockSize f ρ) (⌈(𝔼 x : G, f x)/ε^2⌉₊+1) ∧ t.length ≤ m ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) ∧
      uniformityPower 2 (fun x ↦ ((f x-g' x : ℝ) : ℂ)) ≤ δ m ∧ squaredError g g' ≤ ε^2 ∧
      C.card ≤ m*priorRank δ m ∧
      commonWidth (priorRank δ m) (priorTolerance δ τ m)/2 ≤ r ∧
      r ≤ commonWidth (priorRank δ m) (priorTolerance δ τ m) ∧ RelativeStable C u r ∧
      Fintype.card G ≤ (512*windowDenominator (priorRank δ m) (priorTolerance δ τ m)+1)^
        (2*(m*priorRank δ m))*(bohr C r).card ∧
      Fintype.card (Σ i : Fin t.length, Fin ((z (t.get i).1)^2)) ≤ m*(priorTolerance δ τ m)^2 ∧
      ∀ a : G, ∃ H : ((Σ i : Fin t.length, Fin ((z (t.get i).1)^2)) → ℂ) → ℝ,
        ∃ Q : (Σ i : Fin t.length, Fin ((z (t.get i).1)^2)) → G → ℂ,
          (∀ v, 0 ≤ H v ∧ H v ≤ 1) ∧ LipschitzWith (m : NNReal) H ∧
          (∀ p x, ‖Q p x‖ = 1) ∧ (∀ p, IsLocallyQuadratic (bohr C r : Set G) (Q p)) ∧
          (𝔼 x : bohr C r, (g (a+x)-H (fun p ↦ Q p x))^2) ≤ τ^2 := by
  dsimp only
  let ρ : ℕ → NNReal := fun j ↦ gainWeight (δ j)
  let z := stageTolerance ρ τ
  obtain ⟨m,t,g,g',hm,hlen,htag,hcost,hmin,hg,hg',hU,hclose⟩ :=
    budgeted_strong_U3_regularity h2 f hf δ hδ hδ1 hε hτ
  have hR (p : TaggedTest G) (hp : p ∈ t) : normalizedRank (δ p.1) ≤ priorRank δ m :=
    priorRank_le δ (htag p hp).1
  have hZ (p : TaggedTest G) (hp : p ∈ t) : z p.1 ≤ priorTolerance δ τ m :=
    priorTolerance_le δ τ (htag p hp).1
  obtain ⟨C,r,hC,hr,hrmax,hstable,hcard,hlocal⟩ := tagged_stable_local_factor
    t ρ g hmin.1 (fun j ↦ normalizedRank (δ j)) z (stageTolerance_pos ρ τ)
    (fun p hp ↦ (htag p hp).2) hR (priorTolerance_pos δ τ m) hZ hu hτ hcost
  have hCm : C.card ≤ m*priorRank δ m := hC.trans (Nat.mul_le_mul_right _ hlen)
  have hcard' : Fintype.card G ≤
      (512*windowDenominator (priorRank δ m) (priorTolerance δ τ m)+1)^
        (2*(m*priorRank δ m))*(bohr C r).card := by
    apply hcard.trans
    gcongr
    omega
  have hphase := (tagged_phase_count_bound t z hZ).trans
    (Nat.mul_le_mul_right ((priorTolerance δ τ m)^2) hlen)
  have hmass : (∑ i : Fin t.length, ρ (t.get i).1) ≤ (m : NNReal) := by
    calc
      _ ≤ ∑ _i : Fin t.length, (1 : NNReal) :=
        sum_le_sum (fun i _ ↦ gainWeight_le_one (hδ _) (hδ1 _))
      _ = (t.length : NNReal) := by simp
      _ ≤ _ := by exact_mod_cast hlen
  refine ⟨m,t,g,g',C,r,hm,hlen,hg,hg',hU,hclose,hCm,hr,hrmax,hstable,hcard',hphase,?_⟩
  intro a
  obtain ⟨H,Q,hH,hLip,hQ,hpoly,herr⟩ := hlocal a
  refine ⟨H,Q,hH,?_,hQ,hpoly,herr⟩
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact (hLip.dist_le_mul v w).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hmass) dist_nonneg)

#print axioms strong_local_quadratic_representation
end Erdos3StrongLocalQuadraticRepresentation
