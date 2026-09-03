import Submission.BinaryProfileCodegreeExplore
import Submission.SignedProfileDeletionExplore

/-! Killing all exceptional coarse sums gives a uniformly controlled signed
profile. Only the unsigned profile retains holes at the forbidden targets. -/
namespace Erdos66DeletedBinaryProfile
open AdditiveCombinatorics Erdos66ExceptionalPairDeletion Erdos66SignedProfileDeletion
  Erdos66AffineRootAggregate Erdos66RealWeightedCharacterEnergy Erdos66SharedParameterKernel
  Erdos66BinaryProfileCodegree
open scoped Classical
set_option maxHeartbeats 2200000

lemma finite_rep_mono (D E : Finset ℕ) (hED : E ⊆ D) (q : ℕ) :
    sumRep (E : Set ℕ) q ≤ sumRep (D : Set ℕ) q := by
  classical
  simp only [sumRep_def]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1,hED hx.2.1,hED hx.2.2⟩

lemma signed_fiber_abs_le_rep (p : ℕ) [Fact p.Prime] (D : Finset ℕ) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (a : ZMod p) :
    |signedFiber h (selectedWeight D) a q| ≤ (sumRep (D : Set ℕ) q : ℝ) := by
  have hσ (i : ℕ) : |(quadraticChar (ZMod p) (a+(i : ZMod p)) : ℝ)| ≤ 1 := by
    have hh := Erdos66FiniteField.quadraticChar_abs_le_one (a+(i : ZMod p))
    exact_mod_cast hh
  have hh := signed_fiber_loss D ∅ (Finset.empty_subset D) h q hD _ hσ
  have hzero : labelFiber h (fun i ↦ selectedWeight ∅ i*(quadraticChar (ZMod p) (a+(i : ZMod p)) : ℝ)) q=0 := by
    simp [labelFiber,selectedWeight]
  have hrep : sumRep ((∅ : Finset ℕ) : Set ℕ) q=0 := by simp [sumRep_def]
  rw [hzero,hrep,Nat.cast_zero,sub_zero,sub_zero] at hh
  exact hh

/-- The collateral loss is the explicit quantity 2 |T| R. There is no
multiplicative loss proportional to the original representation scale. -/
theorem delete_profile_exceptions (p : ℕ) [Fact p.Prime] (D T : Finset ℕ)
    (L q₀ R : ℕ) (a : ZMod p) (μ η : ℝ) (hη : 0<η)
    (hD : D ⊆ Finset.range (L+1))
    (hupper : ∀ q, (sumRep (D : Set ℕ) q : ℝ) ≤ μ+η)
    (hlower : ∀ q, q₀ ≤ q → q ≤ L → |(sumRep (D : Set ℕ) q : ℝ)-μ| < η)
    (hsigned : ∀ q, q ≤ 2*L → q∉T → |signedFiber (L+1) (selectedWeight D) a q| < η)
    (hR : ∀ b q, b≠q → codegree D b q ≤ R) :
    ∃ E : Finset ℕ, E ⊆ D ∧
      (∀ q∈T, sumRep (E : Set ℕ) q=0) ∧
      (∀ q, (sumRep (E : Set ℕ) q : ℝ) ≤ μ+η) ∧
      (∀ q, q₀ ≤ q → q ≤ L → q∉T →
        |(sumRep (E : Set ℕ) q : ℝ)-μ| < η+2*(T.card : ℝ)*R) ∧
      (∀ q, q ≤ 2*L → |signedFiber (L+1) (selectedWeight E) a q| < η+2*(T.card : ℝ)*R) := by
  let E := kept D T
  have hED : E ⊆ D := kept_subset D T
  have hm (q : ℕ) : sumRep (E : Set ℕ) q ≤ sumRep (D : Set ℕ) q := finite_rep_mono D E hED q
  have hmr (q : ℕ) : (sumRep (E : Set ℕ) q : ℝ) ≤ (sumRep (D : Set ℕ) q : ℝ) := by exact_mod_cast hm q
  have hloss (q : ℕ) (hq : q∉T) :
      (sumRep (D : Set ℕ) q : ℝ)-(sumRep (E : Set ℕ) q : ℝ) ≤ 2*(T.card : ℝ)*R := by
    have hh := representation_loss_le D T R q hq (fun b _ hbq ↦ hR b q hbq)
    have hmon := hm q
    exact_mod_cast hh
  refine ⟨E,hED,(fun q hq ↦ kept_rep_zero D T q hq),fun q ↦ (hmr q).trans (hupper q),?_,?_⟩
  · intro q hq₀ hq hqT
    have hh := abs_lt.mp (hlower q hq₀ hq)
    have hc := hloss q hqT
    have hn : 0 ≤ 2*(T.card : ℝ)*R := by positivity
    rw [abs_lt]
    constructor <;> linarith [hmr q]
  · intro q hq
    by_cases hqT : q∈T
    · have hh := signed_fiber_abs_le_rep p E (L+1) q (hED.trans hD) a
      rw [kept_rep_zero D T q hqT,Nat.cast_zero] at hh
      have hn : 0 ≤ 2*(T.card : ℝ)*R := by positivity
      linarith
    · have hc := signed_kept_loss p D T (L+1) R q hD a hqT (fun b _ hbq ↦ hR b q hbq)
      have ht := abs_sub_le (signedFiber (L+1) (selectedWeight E) a q)
        (signedFiber (L+1) (selectedWeight D) a q) 0
      rw [sub_zero,sub_zero,abs_sub_comm (signedFiber (L+1) (selectedWeight E) a q)] at ht
      linarith [hsigned q hq hqT]

/-- A simultaneous finite profile after deletion. The signed bound now holds
at every coarse target, while all exceptional unsigned sums are zero. -/
theorem exists_deleted_binary_profile (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (s q₀ L R : ℕ) (hpL : 4*(L+1)<p) (μ ε t : ℝ) (ht : 0<t)
    (hμ : 1 ≤ μ) (hε : 0<ε) (hε1 : ε ≤ 1) (hlarge : 8 ≤ ε*μ)
    (hs : μ ≤ (s : ℝ)+1)
    (hstart : 64*(s : ℝ)^2 ≤ ε^2*((q₀ : ℝ)+1))
    (hsmall : 6*(2*(L : ℝ)+1)*Real.exp (-ε^2*(μ+1)/512) +
      (2*(L : ℝ)+1)^2*Real.exp ((2-(R : ℝ))*t+
        (Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) < 1) :
    ∃ (a : ZMod p) (T E : Finset ℕ), E ⊆ Finset.range (L+1) ∧
      (∀ i<L+1, a+(i : ZMod p) ≠ 0) ∧
      (∀ q<2*(L+1), 2*a+(q : ZMod p) ≠ 0) ∧
      (T.card : ℝ) ≤ 128*(1+Real.log ((L+1 : ℕ) : ℝ))^2/ε^2 ∧
      (∀ q∈T, ε*((s : ℝ)+1)<4*((q : ℝ)+1)) ∧
      (∀ q∈T, sumRep (E : Set ℕ) q=0) ∧
      (∀ q, (sumRep (E : Set ℕ) q : ℝ) ≤ (1+ε)*μ) ∧
      (∀ q, q₀ ≤ q → q ≤ L → q∉T →
        |(sumRep (E : Set ℕ) q : ℝ)-μ| < ε*μ+2*(T.card : ℝ)*R) ∧
      (∀ q, q ≤ 2*L → |signedFiber (L+1) (selectedWeight E) a q| < ε*μ+2*(T.card : ℝ)*R) := by
  obtain ⟨a,T,D,hD,ha,hop,hT,hloc,hu,hl,hsgn,hcd⟩ :=
    exists_binary_signed_profile_codegrees p hp s q₀ L R hpL μ ε t ht hμ hε hε1 hlarge hs hstart hsmall
  have hu' : ∀ q, (sumRep (D : Set ℕ) q : ℝ) ≤ μ+ε*μ := by intro q; nlinarith [hu q]
  obtain ⟨E,hED,hzero,huE,hlE,hsgnE⟩ := delete_profile_exceptions p D T L q₀ R a μ (ε*μ)
    (mul_pos hε (by linarith)) hD hu' hl hsgn hcd
  refine ⟨a,T,E,hED.trans hD,ha,hop,hT,hloc,hzero,?_,hlE,hsgnE⟩
  intro q
  nlinarith [huE q]

end Erdos66DeletedBinaryProfile
