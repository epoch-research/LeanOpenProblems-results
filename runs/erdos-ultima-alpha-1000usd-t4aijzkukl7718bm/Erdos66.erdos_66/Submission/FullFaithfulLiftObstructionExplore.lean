import Submission.FaithfulParabolaCardinalityExplore
import Submission.QuadraticPrefixMassExplore

/-! A hypothetical witness cannot contain full prefix-faithful lifts at
arbitrarily large prime cutoffs. This is a restriction on a construction,
not a negation of the original conjecture. -/
namespace Erdos66FullFaithfulLiftObstruction
open Erdos66Counting Erdos66InheritedOriginLift
  Erdos66PrefixFaithfulParabolaLift Erdos66FaithfulParabolaCardinality
  Erdos66QuadraticPrefixMass
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1600000

noncomputable def prefixParameters (A : Set ℕ) (p : ℕ) : Finset (ZMod p) :=
  (cutoff A p).image (fun n : ℕ ↦ (n : ZMod p))

lemma prefixParameters_card (A : Set ℕ) (p : ℕ) [NeZero p] :
    (prefixParameters A p).card=count A p := by
  apply Finset.card_image_iff.mpr
  intro n hn m hm he
  have hn' := (mem_cutoff.mp hn).1
  have hm' := (mem_cutoff.mp hm).1
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt hn', ZMod.val_natCast_of_lt hm'] using hv

lemma full_lift_forces_mass (A : Set ℕ) (p : ℕ) [Fact p.Prime] (a : ZMod p)
    (ha : ∀ u∈translated (prefixParameters A p) a, u≠0)
    (hsub : ∀ n∈encodePlane p (faithfulLift (prefixParameters A p) a), n∈A) :
    (p-1)*count A p ≤ count A (p^2) := by
  have hinc : encodePlane p (faithfulLift (prefixParameters A p) a) ⊆ cutoff A (p^2) := by
    intro n hn
    exact mem_cutoff.mpr ⟨encodePlane_lt p _ hn, hsub n hn⟩
  have hcard := Finset.card_le_card hinc
  rw [faithful_encoded_card p _ a ha, prefixParameters_card] at hcard
  simpa only [Nat.mul_comm] using hcard

/-- All sufficiently large prime cutoffs forbid containing the entire lift
of the actual old prefix. Thinning the lift is not excluded. -/
theorem eventually_no_full_faithful_lift {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ∀ a : ZMod p, (∀ u∈translated (prefixParameters A p) a, u≠0) →
        ¬ (∀ n∈encodePlane p (faithfulLift (prefixParameters A p) a), n∈A) := by
  filter_upwards [eventual_no_linear_mass_amplification hc ht] with p hpMass
  intro hp
  letI : Fact p.Prime := ⟨hp⟩
  intro a ha hsub
  exact (not_le_of_gt hpMass) (full_lift_forces_mass A p a ha hsub)

end Erdos66FullFaithfulLiftObstruction
