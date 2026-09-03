import Submission.SummableMatchingSpikesExplore
import Submission.RepeatedCentersExplore

/-! Arbitrary nonnegative multiplicities, including zeros, can be prescribed
under their actual weighted cost. No dummy packet is charged at a zero. -/
namespace Erdos66MultiplicityMatchingSpikes
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66RepeatedCenters
open scoped Classical Topology

noncomputable def packetWeight (n : ℕ) : ℝ :=
  Real.sqrt (logScale n)/Real.sqrt ((n : ℝ)+1)

lemma packetWeight_nonneg (n : ℕ) : 0 ≤ packetWeight n := by
  unfold packetWeight
  positivity

/-- Prescribe a multiplicity function directly, instead of first supplying
an injective list of exceptional targets with positive multiplicities. -/
theorem asymptotic_multiplicity_spikes (A : Set ℕ) (K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (m : ℕ → ℕ) (hm : Summable (fun z ↦ (m z : ℝ)*packetWeight z)) :
    ∃ B : Set ℕ, A ⊆ B ∧
      (∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ)+2*m z ≤ sumRep B z) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
        (sumRep B z : ℝ) ≤ sumRep A z+2*m z+ε*logScale z := by
  let S : Set ℕ := {z | 0 < m z}
  rcases S.finite_or_infinite with hS | hS
  · obtain ⟨N,hN⟩ := hS.bddAbove
    have hz : ∀ᶠ z : ℕ in atTop, m z = 0 := by
      filter_upwards [eventually_ge_atTop (N+1)] with z hz
      by_contra hh
      have hpos : z ∈ S := Nat.pos_of_ne_zero hh
      have := hN hpos
      omega
    refine ⟨A,Set.Subset.rfl,?_,?_⟩
    · filter_upwards [hz] with z he
      simp [he]
    · intro ε hε
      filter_upwards [hz] with z he
      simp only [he,Nat.cast_zero,mul_zero,add_zero]
      exact le_add_of_nonneg_right (mul_nonneg hε.le (logScale_pos z).le)
  · letI : Infinite S := hS.to_subtype
    let e : ℕ ≃o S := Nat.Subtype.orderIsoOfNat S
    let n : ℕ → ℕ := fun k ↦ (e k).val
    let r : ℕ → ℕ := fun k ↦ m (n k)
    have hn : Function.Injective n := Subtype.val_injective.comp e.injective
    have hr (k : ℕ) : 0 < r k := (e k).property
    have hrange : Set.range n = S := by
      ext z
      constructor
      · rintro ⟨k,rfl⟩
        exact (e k).property
      · intro hz
        obtain ⟨k,hk⟩ := e.surjective ⟨z,hz⟩
        exact ⟨k,congrArg Subtype.val hk⟩
    have hcost : Summable (fun k ↦ (r k : ℝ)*packetWeight (n k)) :=
      hm.comp_injective hn
    have hrep : Summable (fun i ↦ packetWeight (repeated n r hr i)) := by
      apply summable_of_block_bound r hr _ (fun k ↦ packetWeight (n k))
        (fun i ↦ packetWeight_nonneg _) (fun k ↦ packetWeight_nonneg _) _ hcost
      intro p
      rw [repeat_position]
    have hmult : Erdos66RepeatedCenters.multiplicity n r = m := by
      funext z
      by_cases hz : z ∈ Set.range n
      · obtain ⟨k,rfl⟩ := hz
        exact multiplicity_at n r hn k
      · rw [multiplicity_off n r z hz]
        rw [hrange] at hz
        change ¬0 < m z at hz
        omega
    have hstab (z : ℕ) := centerCount_repeat_stabilizes n r hn hr z
    rw [hmult] at hstab
    exact Erdos66SummableMatchingSpikes.asymptotic_prescribed_spikes A K C hK hC hA
      (repeated n r hr) hrep m hstab

end Erdos66MultiplicityMatchingSpikes
