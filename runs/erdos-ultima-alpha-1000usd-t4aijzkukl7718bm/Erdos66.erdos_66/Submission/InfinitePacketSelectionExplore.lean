import Submission.PacketCollisionCostExplore
import Submission.JointRepairPotentialExplore
import Submission.FiniteChoiceCompactnessExplore

/-! Compactness turns uniform finite joint-packet estimates into one infinite
selection. This is conditional on the collision/avoidance and hit-mass bounds;
no base set for Erdős 66 is asserted here. -/
namespace Erdos66InfinitePacketSelection
open Filter Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66HeterogeneousSelection
  Erdos66PacketCollisionCost Erdos66JointRepairPotential Erdos66ClippedRepair
  Erdos66FiniteChoiceCompactness
open scoped Topology Classical
set_option maxHeartbeats 1600000

noncomputable def accuracy (k : ℕ) : ℝ := 1 / ((k : ℝ)+1)
noncomputable def share (k : ℕ) : ℝ := (1/8 : ℝ)*(1/2 : ℝ)^k
lemma accuracy_pos (k : ℕ) : 0 < accuracy k := by dsimp [accuracy]; positivity
lemma share_pos (k : ℕ) : 0 < share k := by dsimp [share]; positivity
lemma share_sum_le (L : ℕ) : (∑ k ∈ Finset.range L, share k) ≤ 1/4 := by
  have hh := geom_sum_mul_neg (1/2 : ℝ) L
  have hp : 0 ≤ (1/2 : ℝ)^L := by positivity
  simp only [share, ← Finset.mul_sum]
  nlinarith

noncomputable def testGrid (Z : ℕ → ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (L+1)).product (Finset.range (L+1))).filter (fun p ↦ Z p.1 ≤ p.2)

lemma grid_potential_bound (B : ℝ) (Z : ℕ → ℕ)
    (hZ : ∀ k (T : Finset ℕ), (∀ z ∈ T, Z k ≤ z) →
      ∑ z ∈ T, potential B (accuracy k) z < share k) (L : ℕ) :
    (∑ p ∈ testGrid Z L, potential B (accuracy p.1) p.2) ≤ 1/4 := by
  rw [testGrid, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  have hh : (∑ k ∈ Finset.range (L+1), ∑ z ∈ Finset.range (L+1),
      if Z k ≤ z then potential B (accuracy k) z else 0) ≤
      ∑ k ∈ Finset.range (L+1), share k := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← Finset.sum_filter]
    exact (hZ k _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)).le
  exact hh.trans (share_sum_le (L+1))

variable (q : ℕ → ℕ) [∀ i, NeZero (q i)]
variable (n : ℕ → ℤ) (x : ∀ i : ℕ, Fin (q i) → ℤ)
variable (B₀ : ∀ i : ℕ, Finset (Fin (q i)))

def finitePoint (L : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) : Label (Fin L) → ℤ :=
  point (fun i : Fin L ↦ n i.val) (chosen (fun i : Fin L ↦ x i.val) ω)

def finiteGood (L : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) : Prop :=
  Function.Injective (finitePoint q n x L ω) ∧ (∀ i : Fin L, ω i ∉ B₀ i.val) ∧
    ∀ u v w t : Label (Fin L), ¬ Designated u v → ¬ Designated w t →
      finitePoint q n x L ω u + finitePoint q n x L ω v =
        finitePoint q n x L ω w + finitePoint q n x L ω t →
      (u=w ∧ v=t) ∨ (u=t ∧ v=w)

def liftLabel {L M : ℕ} (h : M ≤ L) (u : Label (Fin M)) : Label (Fin L) :=
  (⟨u.1.val, lt_of_lt_of_le u.1.isLt h⟩, u.2)

lemma liftLabel_injective {L M : ℕ} (h : M ≤ L) : Function.Injective (liftLabel h) := by
  intro u v he
  have h₁ := congrArg (fun p : Label (Fin L) ↦ p.1.val) he
  have h₂ := congrArg Prod.snd he
  exact Prod.ext (Fin.ext h₁) h₂

lemma designated_lift_iff {L M : ℕ} (h : M ≤ L) (u v : Label (Fin M)) :
    Designated (liftLabel h u) (liftLabel h v) ↔ Designated u v := by
  simp [Designated, liftLabel, Fin.ext_iff]

lemma point_lift {L M : ℕ} (h : M ≤ L) (ω : ∀ i : Fin L, Fin (q i.val)) (u : Label (Fin M)) :
    finitePoint q n x L ω (liftLabel h u) =
      finitePoint q n x M (restrictFinite q h ω) u := rfl

lemma finiteGood_restrict {L M : ℕ} (h : M ≤ L) (ω : ∀ i : Fin L, Fin (q i.val))
    (hω : finiteGood q n x B₀ L ω) : finiteGood q n x B₀ M (restrictFinite q h ω) := by
  obtain ⟨hinj, havoid, hunique⟩ := hω
  refine ⟨?_, ?_, ?_⟩
  · intro u v he
    have he' : finitePoint q n x L ω (liftLabel h u) = finitePoint q n x L ω (liftLabel h v) := he
    exact liftLabel_injective h (hinj he')
  · intro i
    exact havoid ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  · intro u v w t h₁ h₂ he
    have h₁' : ¬ Designated (liftLabel h u) (liftLabel h v) := by rwa [designated_lift_iff]
    have h₂' : ¬ Designated (liftLabel h w) (liftLabel h t) := by rwa [designated_lift_iff]
    have hh := hunique (liftLabel h u) (liftLabel h v) (liftLabel h w) (liftLabel h t) h₁' h₂' he
    rcases hh with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨liftLabel_injective h ha, liftLabel_injective h hb⟩
    · exact Or.inr ⟨liftLabel_injective h ha, liftLabel_injective h hb⟩

/-- Uniform prefix costs suffice for one choice whose mixed hit count is
uniformly o(log z), including a bound for every finite coordinate prefix. -/
theorem exists_infinite_joint_selection (hx : ∀ i, Function.Injective (x i))
    (S : ℕ → ∀ i : ℕ, Finset (Fin (q i))) (B : ℝ)
    (hcost : ∀ L : ℕ,
      (∑ i : Fin L, 4*((i.val : ℝ)+1)^2 / q i.val) +
      (∑ i : Fin L, 16*((i.val : ℝ)+1)^4 / q i.val) +
      hitMass (fun i : Fin L ↦ B₀ i.val) ≤ 1/2)
    (hmass : ∀ L z : ℕ, hitMass (fun i : Fin L ↦ S z i.val) ≤ B * Real.sqrt (logScale z)) :
    ∃ ω : ∀ i : ℕ, Fin (q i),
      (∀ L, finiteGood q n x B₀ L (restrict q L ω)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop, ∀ L : ℕ,
        hits (fun i : Fin L ↦ S z i.val) (restrict q L ω) ≤ ε * logScale z := by
  obtain ⟨Z,hZ⟩ := exists_accuracy_thresholds B accuracy share share_pos
  let Good (L : ℕ) (ω : ∀ i : Fin L, Fin (q i.val)) : Prop :=
    finiteGood q n x B₀ L ω ∧ ∀ k ≤ L, ∀ z ≤ L, Z k ≤ z →
      hits (fun i : Fin L ↦ S z i.val) ω ≤ accuracy k * logScale z
  have hne (L : ℕ) : ∃ ω, Good L ω := by
    let R : ℕ × ℕ → ℝ := fun p ↦ accuracy p.1 * logScale p.2
    let t : ℕ × ℕ → ℝ := fun p ↦ 4 / accuracy p.1
    have ht : ∀ p ∈ testGrid Z L, 0 < t p := fun p _ ↦ div_pos (by norm_num) (accuracy_pos p.1)
    have hb := collision_cost_bounds (fun i : Fin L ↦ q i.val)
    have hpot : (∑ p ∈ testGrid Z L,
        Real.exp (Real.exp (t p) * hitMass (fun i : Fin L ↦ S p.2 i.val) - t p * R p)) ≤ 1/4 := by
      apply (Finset.sum_le_sum (fun p (_ : p ∈ testGrid Z L) ↦
        hit_potential_le B (accuracy p.1) _ (accuracy_pos p.1) p.2 (hmass L p.2))).trans
      exact grid_potential_bound B Z hZ L
    have hsmall : (∑ p ∈ (pointEvents : Finset (Label (Fin L) × Label (Fin L))),
        1 / (Fintype.card (Fin (q (largest₂ p).val)) : ℝ)) +
        (∑ p ∈ (pairEvents : Finset (Quad (Fin L))), 1 / (Fintype.card (Fin (q (largest₄ p).val)) : ℝ)) +
        hitMass (fun i : Fin L ↦ B₀ i.val) +
        (∑ p ∈ testGrid Z L, Real.exp (Real.exp (t p) * hitMass (fun i : Fin L ↦ S p.2 i.val) - t p * R p)) < 1 := by
      simp only [Fintype.card_fin]
      have hc := hcost L
      linarith [hb.1,hb.2]
    obtain ⟨ω,hinj,havoid,hunique,hhit⟩ := exists_joint_packets
      (fun i : Fin L ↦ n i.val) (fun i : Fin L ↦ x i.val) (fun i ↦ hx i.val)
      (fun i : Fin L ↦ B₀ i.val) largest₂ largest₄
      (fun p _ ↦ largest₂_mem p) (fun p _ ↦ largest₄_mem p)
      (testGrid Z L) (fun p i ↦ S p.2 i.val) R t ht hsmall
    refine ⟨ω, ⟨hinj,havoid,hunique⟩, fun k hk z hz hkz ↦ ?_⟩
    have hp : (k,z) ∈ testGrid Z L := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hkz⟩
    exact (hhit (k,z) hp).le
  have hres (L M : ℕ) (h : M ≤ L) (ω : ∀ i : Fin L, Fin (q i.val))
      (hω : Good L ω) : Good M (restrictFinite q h ω) := by
    refine ⟨finiteGood_restrict q n x B₀ h ω hω.1, ?_⟩
    intro k hk z hz hkz
    have hh := hω.2 k (hk.trans h) z (hz.trans h) hkz
    exact (hits_restrict_le q h (S z) ω).trans hh
  obtain ⟨ω,hω⟩ := exists_coherent q Good hne hres
  refine ⟨ω, fun L ↦ (hω L).1, ?_⟩
  intro ε hε
  obtain ⟨k,hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε).exists
  filter_upwards [eventually_ge_atTop (Z k)] with z hz
  intro M
  let L := max M (max k z)
  have hML : M ≤ L := le_max_left _ _
  have hkL : k ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hzL : z ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hh := (hω L).2 k hkL z hzL hz
  have hp := hits_restrict_le q hML (S z) (restrict q L ω)
  have hlast : accuracy k * logScale z ≤ ε * logScale z :=
    mul_le_mul_of_nonneg_right hk.le (logScale_pos z).le
  exact hp.trans (hh.trans hlast)

end Erdos66InfinitePacketSelection
