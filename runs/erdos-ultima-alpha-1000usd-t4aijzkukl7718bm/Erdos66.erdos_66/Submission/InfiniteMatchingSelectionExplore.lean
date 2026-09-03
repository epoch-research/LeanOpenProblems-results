import Submission.MatchingPotentialExplore
import Submission.InfinitePacketSelectionExplore

/-! Compactness for packet selections with summably controlled point
collisions and uniformly small mixed and unintended self counts. -/
namespace Erdos66InfiniteMatchingSelection
open Filter Erdos66MatchingPotential Erdos66MatchingPacketSelection
  Erdos66PacketMatchingMass Erdos66PacketMatching Erdos66InfinitePacketSelection
  Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66HeterogeneousSelection
  Erdos66FiniteChoiceCompactness Erdos66ClippedRepair
open scoped Topology Classical
set_option maxHeartbeats 1800000

lemma grid_combined_bound (B Q : ℝ) (Z : ℕ → ℕ)
    (hZ : ∀ k (T : Finset ℕ), (∀ z ∈ T, Z k ≤ z) →
      ∑ z ∈ T, combined B Q (accuracy k) z < share k) (L : ℕ) :
    (∑ p ∈ testGrid Z L, combined B Q (accuracy p.1) p.2) ≤ 1/4 := by
  rw [testGrid,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  have hh : (∑ k ∈ Finset.range (L+1), ∑ z ∈ Finset.range (L+1),
      if Z k ≤ z then combined B Q (accuracy k) z else 0) ≤
      ∑ k ∈ Finset.range (L+1), share k := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← Finset.sum_filter]
    exact (hZ k _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)).le
  exact hh.trans (share_sum_le (L+1))

variable (q : ℕ → ℕ) [∀ i, NeZero (q i)]
variable (n : ℕ → ℤ) (x : ∀ i : ℕ, Fin (q i) → ℤ)
variable (B₀ : ∀ i : ℕ, Finset (Fin (q i)))

noncomputable def finiteOff (L z : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) : Finset (Edge (Fin L)) :=
  offPairs (fun i : Fin L ↦ n i.val) (fun i : Fin L ↦ x i.val) (z : ℤ) ω

def simpleGood (L : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) : Prop :=
  Function.Injective (finitePoint q n x L ω) ∧ ∀ i : Fin L, ω i ∉ B₀ i.val

lemma simpleGood_restrict {L M : ℕ} (h : M ≤ L) (ω : ∀ i : Fin L, Fin (q i.val))
    (hω : simpleGood q n x B₀ L ω) : simpleGood q n x B₀ M (restrictFinite q h ω) := by
  refine ⟨?_,?_⟩
  · intro u v he
    have he' : finitePoint q n x L ω (liftLabel h u) = finitePoint q n x L ω (liftLabel h v) := he
    exact liftLabel_injective h (hω.1 he')
  · intro i
    exact hω.2 ⟨i.val,lt_of_lt_of_le i.isLt h⟩

lemma finiteOff_restrict_le {L M : ℕ} (h : M ≤ L) (z : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) :
    (finiteOff q n x M z (restrictFinite q h ω)).card ≤ (finiteOff q n x L z ω).card := by
  let f : Edge (Fin M) → Edge (Fin L) := fun p ↦ (liftLabel h p.1,liftLabel h p.2)
  have hf : Function.Injective f := by
    intro p r he
    exact Prod.ext (liftLabel_injective h (congrArg Prod.fst he))
      (liftLabel_injective h (congrArg Prod.snd he))
  have hsub : (finiteOff q n x M z (restrictFinite q h ω)).image f ⊆ finiteOff q n x L z ω := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    simp only [finiteOff,offPairs,sumEvents,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
    refine ⟨?_,?_⟩
    · exact fun hd ↦ hr.1 ((designated_lift_iff h r.1 r.2).mp hd)
    · exact hr.2
  calc
    _ = ((finiteOff q n x M z (restrictFinite q h ω)).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- A bounded reciprocal-square-root mass and small point/old-set avoidance
costs suffice for one infinite selection. Unintended self counts and mixed
hit counts are both uniformly o(log z) over every finite prefix. -/
theorem exists_infinite_matching_selection (hx : ∀ i, Function.Injective (x i))
    (S : ℕ → ∀ i : ℕ, Finset (Fin (q i))) (B Q : ℝ)
    (hQ : ∀ L : ℕ, sqrtMass (fun i : Fin L ↦ q i.val) ≤ Q)
    (hcost : ∀ L : ℕ, 4*(sqrtMass (fun i : Fin L ↦ q i.val))^2+
      hitMass (fun i : Fin L ↦ B₀ i.val) ≤ 1/2)
    (hmass : ∀ L z : ℕ, hitMass (fun i : Fin L ↦ S z i.val) ≤ B*Real.sqrt (logScale z)) :
    ∃ ω : ∀ i : ℕ, Fin (q i),
      (∀ L, simpleGood q n x B₀ L (restrict q L ω)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop, ∀ L : ℕ,
        hits (fun i : Fin L ↦ S z i.val) (restrict q L ω) ≤ ε*logScale z ∧
        ((finiteOff q n x L z (restrict q L ω)).card : ℝ) ≤ ε*logScale z := by
  choose Z hZ using fun k ↦ exists_combined_tail B Q (accuracy k) (share k) (share_pos k)
  let Good (L : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) : Prop :=
    simpleGood q n x B₀ L ω ∧ ∀ k ≤ L, ∀ z ≤ L, Z k ≤ z →
      hits (fun i : Fin L ↦ S z i.val) ω ≤ accuracy k*logScale z ∧
      ((finiteOff q n x L z ω).card : ℝ) ≤ accuracy k*logScale z
  have hne (L : ℕ) : ∃ ω, Good L ω := by
    let R : ℕ × ℕ → ℝ := fun p ↦ accuracy p.1*logScale p.2
    let t : ℕ × ℕ → ℝ := fun p ↦ 4/accuracy p.1
    have ht : ∀ p ∈ testGrid Z L, 0 < t p := fun p _ ↦ div_pos (by norm_num) (accuracy_pos p.1)
    have hpot : (∑ p ∈ testGrid Z L,
        (Real.exp (Real.exp (t p)*hitMass (fun i : Fin L ↦ S p.2 i.val)-t p*R p)+
        Real.exp ((Real.exp (8*t p)-1)*4*(sqrtMass (fun i : Fin L ↦ q i.val))^2-t p*R p))) ≤ 1/4 := by
      apply (Finset.sum_le_sum (fun p (_ : p ∈ testGrid Z L) ↦
        combined_bound B Q (accuracy p.1) _ _ (accuracy_pos p.1)
          (Finset.sum_nonneg (fun _ _ ↦ by positivity)) (hQ L) p.2 (hmass L p.2))).trans
      exact grid_combined_bound B Q Z hZ L
    have hsmall : 4*(sqrtMass (fun i : Fin L ↦ Fintype.card (Fin (q i.val))))^2+
        hitMass (fun i : Fin L ↦ B₀ i.val)+
        (∑ p ∈ testGrid Z L,
        (Real.exp (Real.exp (t p)*hitMass (fun i : Fin L ↦ S p.2 i.val)-t p*R p)+
        Real.exp ((Real.exp (8*t p)-1)*4*(sqrtMass (fun i : Fin L ↦ Fintype.card (Fin (q i.val))))^2-t p*R p))) < 1 := by
      simp only [Fintype.card_fin]
      have hc := hcost L
      linarith
    obtain ⟨ω,hinj,havoid,htests⟩ := exists_matching_packets
      (fun i : Fin L ↦ n i.val) (fun i : Fin L ↦ x i.val) (fun i ↦ hx i.val)
      (fun i : Fin L ↦ B₀ i.val) (testGrid Z L) (fun p ↦ (p.2 : ℤ))
      (fun p i ↦ S p.2 i.val) R t ht hsmall
    refine ⟨ω,⟨hinj,havoid⟩,fun k hk z hz hkz ↦ ?_⟩
    have hp : (k,z) ∈ testGrid Z L := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,hkz⟩
    exact ⟨(htests (k,z) hp).1.le,(htests (k,z) hp).2.le⟩
  have hres (L M : ℕ) (h : M ≤ L) (ω : ∀ i : Fin L, Fin (q i.val))
      (hω : Good L ω) : Good M (restrictFinite q h ω) := by
    refine ⟨simpleGood_restrict q n x B₀ h ω hω.1,?_⟩
    intro k hk z hz hkz
    have hh := hω.2 k (hk.trans h) z (hz.trans h) hkz
    refine ⟨(hits_restrict_le q h (S z) ω).trans hh.1,?_⟩
    have ho : ((finiteOff q n x M z (restrictFinite q h ω)).card : ℝ) ≤
        (finiteOff q n x L z ω).card := by exact_mod_cast finiteOff_restrict_le q n x h z ω
    exact ho.trans hh.2
  obtain ⟨ω,hω⟩ := exists_coherent q Good hne hres
  refine ⟨ω,fun L ↦ (hω L).1,?_⟩
  intro ε hε
  obtain ⟨k,hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε).exists
  filter_upwards [eventually_ge_atTop (Z k)] with z hz
  intro M
  let L := max M (max k z)
  have hML : M ≤ L := le_max_left _ _
  have hkL : k ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hzL : z ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hh := (hω L).2 k hkL z hzL hz
  have hlast : accuracy k*logScale z ≤ ε*logScale z :=
    mul_le_mul_of_nonneg_right hk.le (logScale_pos z).le
  refine ⟨(hits_restrict_le q hML (S z) (restrict q L ω)).trans (hh.1.trans hlast),?_⟩
  have ho : ((finiteOff q n x M z (restrict q M ω)).card : ℝ) ≤
      (finiteOff q n x L z (restrict q L ω)).card := by
    exact_mod_cast finiteOff_restrict_le q n x hML z (restrict q L ω)
  exact ho.trans (hh.2.trans hlast)

end Erdos66InfiniteMatchingSelection
