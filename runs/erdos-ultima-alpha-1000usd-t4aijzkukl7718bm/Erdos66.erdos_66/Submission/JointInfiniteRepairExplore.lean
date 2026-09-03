import Submission.InfinitePacketSelectionExplore
import Submission.JointWindowExplore
import Submission.RepairChainExplore

/-! Prescribed sparse spikes can be added jointly to a set with a logarithmic
upper envelope. The explicit uniform prefix-cost hypotheses are not asserted
for a dense collection of repair targets. -/
namespace Erdos66JointInfiniteRepair
open Filter AdditiveCombinatorics Erdos66InfinitePacketSelection
  Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66HeterogeneousSelection
  Erdos66JointWindow Erdos66JointFiniteRepair Erdos66ClippedRepair
  Erdos66NaturalRepairBridge Erdos66OriginRepair Erdos66FiniteRepair
  Erdos66FiniteChoiceCompactness Erdos66RepairChain
open scoped Topology Classical
set_option maxHeartbeats 1800000

noncomputable def centerCount (n : ℕ → ℕ) (L z : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin L ↦ n i.val = z)).card

/-- Uniformly small collision and avoidance costs give an infinite superset
whose representation increment is the prescribed even spike profile, up to
an error o(log z). Multiplicities are encoded by the repeated centers n_i. -/
theorem prescribed_spikes (A : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (n q : ℕ → ℕ) [∀ i, NeZero (q i)] (a : ℕ → ℤ)
    (hsupport : ∀ i (b : Fin (q i)), 0 ≤ a i + (b.val : ℤ) ∧ a i + (b.val : ℤ) ≤ n i)
    (Q : ℝ) (hQ : ∀ L : ℕ, (∑ i : Fin L, 1 / Real.sqrt (q i.val : ℝ)) ≤ Q)
    (hcost : ∀ L : ℕ,
      (∑ i : Fin L, 4*((i.val : ℝ)+1)^2 / q i.val) +
      (∑ i : Fin L, 16*((i.val : ℝ)+1)^4 / q i.val) +
      (∑ i : Fin L, (2*Real.sqrt (2*envelopeCoeff K C))*Real.sqrt (logScale (n i.val)) /
        Real.sqrt (q i.val : ℝ)) ≤ 1/2)
    (m : ℕ → ℕ) (hm : ∀ z, ∃ J : ℕ, ∀ L ≥ J, centerCount n L z = m z) :
    ∃ B : Set ℕ, A ⊆ B ∧
      (∀ z, (sumRep A z : ℝ) + 2*m z ≤ sumRep B z) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
        (sumRep B z : ℝ) ≤ sumRep A z + 2*m z + ε*logScale z := by
  let x : ∀ i : ℕ, Fin (q i) → ℤ := fun i b ↦ a i + (b.val : ℤ)
  let nn : ℕ → ℤ := fun i ↦ (n i : ℤ)
  let B₀ : ∀ i : ℕ, Finset (Fin (q i)) := fun i ↦ forbidden (intCutoff A (n i)) (nn i) (x i)
  let H : ℕ → ∀ i : ℕ, Finset (Fin (q i)) := fun z i ↦
    hitChoices (intCutoff A z) (nn i) (x i) (z : ℤ)
  let D : ℝ := 2*Real.sqrt (2*envelopeCoeff K C)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hx : ∀ i, Function.Injective (x i) := by
    intro i b d he
    apply Fin.ext
    dsimp only [x] at he
    exact_mod_cast add_left_cancel he
  have hforbid (L : ℕ) : hitMass (fun i : Fin L ↦ B₀ i.val) ≤
      ∑ i : Fin L, D*Real.sqrt (logScale (n i.val)) / Real.sqrt (q i.val : ℝ) := by
    unfold hitMass
    simp only [Fintype.card_fin]
    apply Finset.sum_le_sum
    intro i hi
    have hh := (local_choice_bounds hK hC hA (n i.val) (n i.val) (q i.val) (a i.val)
      le_rfl (hsupport i.val)).1
    simpa only [mul_one_div] using hh
  have hc (L : ℕ) :
      (∑ i : Fin L, 4*((i.val : ℝ)+1)^2 / q i.val) +
      (∑ i : Fin L, 16*((i.val : ℝ)+1)^4 / q i.val) +
      hitMass (fun i : Fin L ↦ B₀ i.val) ≤ 1/2 := by
    have hh := hcost L
    have hf := hforbid L
    dsimp only [D] at hf
    linarith
  have hmass (L z : ℕ) : hitMass (fun i : Fin L ↦ H z i.val) ≤ (D*Q)*Real.sqrt (logScale z) := by
    have hb (i : Fin L) : ((H z i.val).card : ℝ) / q i.val ≤
        D*Real.sqrt (logScale z)*(1/Real.sqrt (q i.val : ℝ)) := by
      have hh := (local_choice_bounds hK hC hA (max (n i.val) z) (n i.val) (q i.val) (a i.val)
        (le_max_left _ _) (hsupport i.val)).2 z (le_max_right _ _)
      rw [hit_cutoff_eq A (max (n i.val) z) (n i.val) z _ (le_max_right _ _) (hsupport i.val)] at hh
      exact hh
    unfold hitMass
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∑ i : Fin L, D*Real.sqrt (logScale z)*(1/Real.sqrt (q i.val : ℝ)) :=
        Finset.sum_le_sum (fun i _ ↦ hb i)
      _ = (D*(∑ i : Fin L, 1/Real.sqrt (q i.val : ℝ)))*Real.sqrt (logScale z) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hQ L) hD) (Real.sqrt_nonneg _)
  obtain ⟨ω,hgood,hhits⟩ := exists_infinite_joint_selection q nn x B₀ hx H (D*Q) hc hmass
  let P (L : ℕ) : Finset ℤ := Erdos66MultiPacket.packet (fun i : Fin L ↦ nn i.val)
    (chosen (fun i : Fin L ↦ x i.val) (restrict q L ω))
  have hPmem {L : ℕ} {b : ℤ} (hb : b ∈ P L) :
      ∃ i : Fin L, b = x i.val (ω i.val) ∨ b = nn i.val-x i.val (ω i.val) := by
    obtain ⟨⟨i,d⟩, _, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨i, ?_⟩
    cases d <;> simp [point, chosen, restrict]
  have hPpos (L : ℕ) (b : ℤ) (hb : b ∈ P L) : 0 ≤ b := by
    obtain ⟨i,hi⟩ := hPmem hb
    have hh := hsupport i.val (ω i.val)
    dsimp only [x,nn] at hi
    rcases hi with rfl | rfl <;> omega
  have hPdis (L z : ℕ) : Disjoint (intCutoff A z) (P L) := by
    apply Finset.disjoint_left.mpr
    intro b hbA hbP
    obtain ⟨i,hi⟩ := hPmem hbP
    have hh := hsupport i.val (ω i.val)
    have hbz := (intCutoff_bounds hbA).2
    have hbn : b ≤ (n i.val : ℤ) := by dsimp only [x,nn] at hi; rcases hi with rfl | rfl <;> omega
    have hb : b ∈ intCutoff A (n i.val) := (mem_intCutoff_congr A z (n i.val) b hbz hbn).mp hbA
    have hn := (hgood L).2.1 i
    apply hn
    change ω i.val ∈ forbidden (intCutoff A (n i.val)) (nn i.val) (x i.val)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hi with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb
  have hPmono : Monotone P := by
    intro L M hLM b hb
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨liftLabel hLM u, Finset.mem_univ _, ?_⟩
    exact hu
  let F (L : ℕ) : Finset ℕ := (P L).image Int.toNat
  let S (L : ℕ) : Set ℕ := A ∪ (F L : Set ℕ)
  have hSmono : Monotone S := by
    intro L M hLM
    exact Set.union_subset_union_right A (Finset.coe_subset.mpr (Finset.image_subset_image (hPmono hLM)))
  let B : Set ℕ := ⋃ L, S L
  have hAB : A ⊆ B := (Set.subset_union_left : A ⊆ S 0).trans (Set.subset_iUnion S 0)
  have hstage (L z : ℕ) :
      (sumRep A z : ℝ) + 2*centerCount n L z ≤ sumRep (S L) z ∧
      (sumRep (S L) z : ℝ) ≤ sumRep A z + 2*centerCount n L z +
        4*hits (fun i : Fin L ↦ H z i.val) (restrict q L ω) + 2 := by
    have hg := hgood L
    have hs := packet_bound (fun i : Fin L ↦ nn i.val)
      (chosen (fun i : Fin L ↦ x i.val) (restrict q L ω)) hg.1 hg.2.2 (z : ℤ)
    have hcenter : (Finset.univ.filter (fun i : Fin L ↦ nn i.val = (z : ℤ))).card = centerCount n L z := by
      simp only [nn, Nat.cast_inj, centerCount]
    rw [hcenter] at hs
    have hs₁ : (2*centerCount n L z : ℝ) ≤ pairCount (P L) (P L) (z : ℤ) := by exact_mod_cast hs.1
    have hs₂ : (pairCount (P L) (P L) (z : ℤ) : ℝ) ≤ 2*centerCount n L z + 2 := by exact_mod_cast hs.2
    have hmixed := joint_mixed_le_hits (intCutoff A z) (fun i : Fin L ↦ nn i.val)
      (fun i : Fin L ↦ x i.val) (restrict q L ω) (z : ℤ)
    change (pairCount (P L) (intCutoff A z) (z : ℤ) : ℝ) ≤
      2*hits (fun i : Fin L ↦ H z i.val) (restrict q L ω) at hmixed
    have hmixed0 : (0 : ℝ) ≤ pairCount (P L) (intCutoff A z) (z : ℤ) := Nat.cast_nonneg _
    have he := cutoff_union_rep A z z (P L) (hPpos L) le_rfl
    change sumRep (S L) z = _ at he
    rw [he, pairCount_union_self _ _ _ (hPdis L z), cutoff_rep_eq A z z le_rfl]
    push_cast
    constructor <;> linarith
  have hlower (z : ℕ) : (sumRep A z : ℝ) + 2*m z ≤ sumRep B z := by
    obtain ⟨J,hJ⟩ := hm z
    obtain ⟨L,hJL,he⟩ := sumRep_iUnion_attained S hSmono z J
    have hh := (hstage L z).1
    rw [hJ L hJL, ← he] at hh
    exact hh
  refine ⟨B,hAB,hlower,?_⟩
  intro ε hε
  have hlarge := (logScale_atTop.const_div_atTop (2 : ℝ)).eventually_lt_const
    (show (0 : ℝ) < ε/2 by positivity)
  filter_upwards [hhits (ε/8) (by positivity), hlarge] with z hz hlargez
  obtain ⟨J,hJ⟩ := hm z
  obtain ⟨L,hJL,he⟩ := sumRep_iUnion_attained S hSmono z J
  have hh := (hstage L z).2
  rw [hJ L hJL, ← he] at hh
  have hb := hz L
  have h2 := (div_lt_iff₀ (logScale_pos z)).mp hlargez
  change (sumRep B z : ℝ) ≤ _ at hh
  nlinarith

end Erdos66JointInfiniteRepair
