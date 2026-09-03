import Submission.ZModBohrIndices

/-! A flat progression partition on a stable cyclic Bohr set, with all
exceptional-mass costs expressed in terms of rank and the modulus. -/
namespace Erdos3StableBohrQuadraticPartition
open Finset Erdos3ZModBohrIndices Erdos3BohrLocalQuadraticPartition
  Erdos3BohrCoarseProgressionPartition Erdos3FiniteBohr Erdos3RelativeStableBohr
  Erdos3LocalQuadraticInverse Erdos3SimultaneousQuadraticRecurrence Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

/-- Stable radius bounds pay for the Bohr boundary. A fixed-radius Bohr size
bound converts the terminal-block loss to an explicit rank-dependent cost
per modulus. -/
theorem stable_bohr_quadratic_partition {I : Type*} [Fintype I]
    (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) (q : I → ZMod p → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) {R R' : ℝ} (hR : 1/64 ≤ R) (hRR' : R ≤ R')
    (hquad : ∀ i, IsLocallyQuadratic (bohr C R' : Set (ZMod p)) (q i))
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z R)
    (K M L n n₀ t : ℕ) (hK : 0 < K) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) (hn₀ : 0 < n₀)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ relativeWidth C z R) :
    ∃ c : bohrIndices C R 0 1 p → Option (Fin p × (Fin K × Fin M)),
    ∃ w : I → (Fin p × (Fin K × Fin M)) → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧
      cellMass c none ≤
        (((2*n₀+1)^(2*C.card)*K*257^(2*C.card) : ℕ) : ℝ)/(p : ℝ)+1/(z : ℝ)+
        ((recurrenceBound (Fintype.card I) t : ℝ)*(M : ℝ)/(K : ℝ)+
          (((2*n+1)^(2*Fintype.card I) : ℕ) : ℝ)*(L : ℝ)/(M : ℝ)) ∧
      (∀ x j, c x = some j → ∀ i,
        ‖q i (x.val.val : ZMod p)-w i j‖ ≤ 2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)) ∧
      (∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧
          d ≤ (recurrenceBound (Fintype.card I) t*(2*n+1)^(2*Fintype.card I))*(2*n₀+1)^(2*C.card) ∧
          (∀ k < L, ∃ x : bohrIndices C R 0 1 p, x.val.val = b+k*d) ∧
          ∀ x : bohrIndices C R 0 1 p, c x = some j ↔ ∃ k : Fin L, x.val.val = b+k.val*d) := by
  have hR0 : 0 ≤ R := by linarith
  have hB := bohrIndices_nonempty p C hR0
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := bohr_local_quadratic_partition C q hq hquad hRR' 0 1
    p K M L n n₀ t hK hM hL hn hn₀ hmesh hB
  have hboundary := stable_index_boundary_fraction p C hz hR0 hstable
  have hBpos : (0 : ℝ) < (bohrIndices C R 0 1 p).card := by exact_mod_cast hB.card_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hcard : (p : ℝ) ≤ (257^(2*C.card) : ℕ)*((bohrIndices C R 0 1 p).card : ℝ) := by
    exact_mod_cast bohrIndices_card_lower p C hR
  have hterm : (((2*n₀+1)^(2*C.card)*K : ℕ) : ℝ)/((bohrIndices C R 0 1 p).card : ℝ) ≤
      (((2*n₀+1)^(2*C.card)*K*257^(2*C.card) : ℕ) : ℝ)/(p : ℝ) := by
    apply (div_le_div_iff₀ hBpos hp).mpr
    have hh := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg ((2*n₀+1)^(2*C.card)*K) :
      (0 : ℝ) ≤ ((2*n₀+1)^(2*C.card)*K : ℕ))
    simpa only [Nat.cast_mul,mul_assoc] using hh
  refine ⟨c,w,hw,?_,?_,hgeom⟩
  · rw [add_div] at hbad
    exact hbad.trans (add_le_add (add_le_add hterm hboundary) le_rfl)
  · simpa only [zero_add,nsmul_eq_mul,mul_one] using hflat

#print axioms stable_bohr_quadratic_partition
end Erdos3StableBohrQuadraticPartition
