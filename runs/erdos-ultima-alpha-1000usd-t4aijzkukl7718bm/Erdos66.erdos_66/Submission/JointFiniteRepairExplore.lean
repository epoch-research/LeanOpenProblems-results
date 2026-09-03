import Submission.MultiPacketSelectionExplore

/-! A finite simultaneous repair criterion, with one global non-designated
self-count bound for all packets combined. -/
namespace Erdos66JointFiniteRepair
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66HeterogeneousSelection
  Erdos66OriginRepair Erdos66FiniteRepair
open scoped Classical
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, DecidableEq (α i)]

lemma joint_packet_avoids (A : Finset ℤ) (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (ω : ∀ i, α i) (hω : ∀ i, ω i ∉ forbidden A (n i) (x i)) :
    Disjoint A (Erdos66MultiPacket.packet n (chosen x ω)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hp
  obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp hp
  have hh := hω i
  have hn : ¬(x i (ω i) ∈ A ∨ n i - x i (ω i) ∈ A) := by
    simpa only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  cases b <;> simp only [point, chosen, Bool.false_eq_true, if_false, if_true] at ha
  · exact hn (Or.inl ha)
  · exact hn (Or.inr ha)

lemma joint_mixed_le_hits (A : Finset ℤ) (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (ω : ∀ i, α i) (z : ℤ) :
    (pairCount (Erdos66MultiPacket.packet n (chosen x ω)) A z : ℝ) ≤
      2 * hits (fun i ↦ hitChoices A (n i) (x i) z) ω := by
  have hh := pairCount_image_le (point n (chosen x ω)) A z
  have hh' : (pairCount (Erdos66MultiPacket.packet n (chosen x ω)) A z : ℝ) ≤
      ∑ u : Label ι, if z - point n (chosen x ω) u ∈ A then (1 : ℝ) else 0 := by
    exact_mod_cast (show pairCount (Erdos66MultiPacket.packet n (chosen x ω)) A z ≤
      ∑ u : Label ι, if z - point n (chosen x ω) u ∈ A then 1 else 0 by
        simpa only [Finset.card_filter] using hh)
  apply hh'.trans
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, point, chosen, if_true, Bool.false_eq_true, if_false]
  rw [hits, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h₁ : z - x i (ω i) ∈ A <;> by_cases h₂ : z - (n i - x i (ω i)) ∈ A <;>
    norm_num [hitChoices, h₁, h₂]

/-- Arbitrarily many target packets can share one error term, provided the
joint collision-and-hit potential is small. -/
theorem exists_joint_finite_repair (A : Finset ℤ) (n : ι → ℤ)
    (x : ∀ i, α i → ℤ) (hx : ∀ i, Function.Injective (x i))
    (v₂ : Label ι × Label ι → ι) (v₄ : Quad ι → ι)
    (hv₂ : ∀ p ∈ (pointEvents : Finset (Label ι × Label ι)), v₂ p = p.1.1 ∨ v₂ p = p.2.1)
    (hv₄ : ∀ p ∈ (pairEvents : Finset (Quad ι)),
      v₄ p = p.1.1 ∨ v₄ p = p.2.1.1 ∨ v₄ p = p.2.2.1.1 ∨ v₄ p = p.2.2.2.1)
    (T : Finset ℤ) (R t : ℤ → ℝ) (ht : ∀ z ∈ T, 0 < t z)
    (hsmall : (∑ p ∈ (pointEvents : Finset (Label ι × Label ι)), 1 / (Fintype.card (α (v₂ p)) : ℝ)) +
      (∑ p ∈ (pairEvents : Finset (Quad ι)), 1 / (Fintype.card (α (v₄ p)) : ℝ)) +
      hitMass (fun i ↦ forbidden A (n i) (x i)) +
      (∑ z ∈ T, Real.exp (Real.exp (t z) * hitMass (fun i ↦ hitChoices A (n i) (x i) z) - t z * R z)) < 1) :
    ∃ F : Finset ℤ, F.card = 2 * Fintype.card ι ∧ Disjoint A F ∧
      (∀ a ∈ F, ∃ i : ι, ∃ y : α i, a = x i y ∨ a = n i - x i y) ∧
      (∀ z : ℤ, 2 * (Finset.univ.filter (fun i ↦ n i = z)).card ≤ pairCount F F z ∧
        pairCount F F z ≤ 2 * (Finset.univ.filter (fun i ↦ n i = z)).card + 2) ∧
      ∀ z ∈ T,
        (2 * (Finset.univ.filter (fun i ↦ n i = z)).card : ℝ) ≤
          (pairCount (A ∪ F) (A ∪ F) z : ℝ) - pairCount A A z ∧
        (pairCount (A ∪ F) (A ∪ F) z : ℝ) - pairCount A A z <
          2 * (Finset.univ.filter (fun i ↦ n i = z)).card + 4 * R z + 2 := by
  obtain ⟨ω, hinj, havoid, hunique, hhits⟩ := exists_joint_packets n x hx
    (fun i ↦ forbidden A (n i) (x i)) v₂ v₄ hv₂ hv₄ T
    (fun z i ↦ hitChoices A (n i) (x i) z) R t ht hsmall
  let F := Erdos66MultiPacket.packet n (chosen x ω)
  have hdis : Disjoint A F := joint_packet_avoids A n x ω havoid
  have hself := packet_bound n (chosen x ω) hinj hunique
  refine ⟨F, ?_, hdis, ?_, hself, ?_⟩
  · simp only [F, Erdos66MultiPacket.packet, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    omega
  · intro a ha
    obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨i, ω i, ?_⟩
    cases b <;> simp [point, chosen]
  · intro z hz
    have hs := hself z
    have hs₁ : (2 * (Finset.univ.filter (fun i ↦ n i = z)).card : ℝ) ≤ pairCount F F z := by
      exact_mod_cast hs.1
    have hs₂ : (pairCount F F z : ℝ) ≤ 2 * (Finset.univ.filter (fun i ↦ n i = z)).card + 2 := by
      exact_mod_cast hs.2
    have hm := joint_mixed_le_hits A n x ω z
    have ht' := hhits z hz
    have hmix : (0 : ℝ) ≤ pairCount F A z := Nat.cast_nonneg _
    rw [pairCount_union_self _ _ _ hdis]
    push_cast
    change (pairCount F A z : ℝ) ≤ _ at hm
    constructor <;> linarith

end Erdos66JointFiniteRepair
