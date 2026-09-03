import Submission.AdaptivePacketAlgebraExplore

/-! Available choices for coordinated rank-assigned packets. Prior assignments
are excluded at each step; the availability cost is linear in the number of
previously selected points. -/
namespace Erdos66AdaptivePacketChoice
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
  Erdos66AdaptivePacketAlgebra
open scoped Classical
set_option maxHeartbeats 2500000
variable {α : Type*} [Fintype α]

lemma bool_exists_card (P : Bool → α → Prop) (K : ℝ)
    (hP : ∀ b, ((Finset.univ.filter (P b)).card : ℝ) ≤ K) :
    ((Finset.univ.filter (fun a ↦ ∃ b, P b a)).card : ℝ) ≤ 2*K := by
  have h := bool_union_card_bound P (fun _ _ ↦ False) K 0 hP (by simp)
  simpa only [or_false,mul_zero,add_zero] using h

lemma injective_partner_card (F : Finset ℕ) (f : α → ℕ)
    (hf : Function.Injective f) (z : ℕ) :
    (Finset.univ.filter (fun a ↦ f a ≤ z ∧ z-f a∈F)).card ≤ F.card := by
  apply Finset.card_le_card_of_injOn (fun a ↦ z-f a)
  · intro a ha
    exact (Finset.mem_filter.mp ha).2.2
  · intro a ha b hb he
    have h1 := (Finset.mem_filter.mp ha).2.1
    have h2 := (Finset.mem_filter.mp hb).2.1
    dsimp only at he
    exact hf (by omega)

lemma injective_double_card (f : α → ℕ) (hf : Function.Injective f) (z : ℕ) :
    (Finset.univ.filter (fun a ↦ 2*f a=z)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := (Finset.mem_filter.mp ha).2
  have h2 := (Finset.mem_filter.mp hb).2
  exact hf (by omega)

lemma extraHits_card (F : Finset ℕ) (n : ℕ) (x : α → ℕ)
    (hinj : ∀ b, Function.Injective (endpoint n x b)) (z : ℕ) :
    ((extraHits F n x z).card : ℝ) ≤ 2*F.card+2 := by
  have hh := bool_union_card_bound
    (fun b a ↦ endpoint n x b a ≤ z ∧ z-endpoint n x b a∈F)
    (fun b a ↦ 2*endpoint n x b a=z) F.card 1 (by
      intro b
      have hc : ((Finset.univ.filter (fun a ↦ endpoint n x b a ≤ z ∧ z-endpoint n x b a∈F)).card : ℝ) ≤ F.card := by
        exact_mod_cast injective_partner_card F (endpoint n x b) (hinj b) z
      convert hc using 1
      congr 3) (by
      intro b
      have hc : ((Finset.univ.filter (fun a ↦ 2*endpoint n x b a=z)).card : ℝ) ≤ 1 := by
        exact_mod_cast injective_double_card (endpoint n x b) (hinj b) z
      convert hc using 1
      congr 3)
  convert hh using 1
  · congr 3
    ext a
    simp [extraHits]
  · ring

lemma jointHits_card (A F : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (hinj : ∀ b, Function.Injective (endpoint n x b)) (z : ℕ) (K : ℝ)
    (hK : ((Erdos66AssignedPacketRepair.swapHits A assign n x z).card : ℝ) ≤ K) :
    ((jointHits A F assign n x z).card : ℝ) ≤ K+2*F.card+2 := by
  have hu : ((jointHits A F assign n x z).card : ℝ) ≤
      (Erdos66AssignedPacketRepair.swapHits A assign n x z).card+(extraHits F n x z).card := by
    exact_mod_cast Finset.card_union_le _ _
  linarith [extraHits_card F n x hinj z]

noncomputable def usedChoices (F : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ) : Finset α :=
  Finset.univ.filter (fun a ↦ ∃ b : Bool, assign (endpoint n x b a)∈F.image assign)

noncomputable def blocked (A F C : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ) : Finset α :=
  Erdos66AssignedPacketRepair.badChoices A assign n x ∪ usedChoices F assign n x ∪
    C.biUnion (jointHits A F assign n x)

noncomputable def available (A F C : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ) : Finset α :=
  Finset.univ \ blocked A F C assign n x

lemma usedChoices_card (F : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ) (H : ℕ)
    (hfiber : ∀ b r, (Finset.univ.filter (fun a ↦ assign (endpoint n x b a)=r)).card ≤ H) :
    ((usedChoices F assign n x).card : ℝ) ≤ 2*H*(F.image assign).card := by
  have hh := bool_exists_card (fun b a ↦ assign (endpoint n x b a)∈F.image assign)
    ((H : ℝ)*(F.image assign).card) (by
      intro b
      have hc := bounded_preimage_card (fun a ↦ assign (endpoint n x b a)) H
        (by intro r; convert hfiber b r using 1; congr 2) (F.image assign)
      have hc' : ((Finset.univ.filter (fun a ↦ assign (endpoint n x b a)∈F.image assign)).card : ℝ) ≤
          (H : ℝ)*(F.image assign).card := by
        have hc₀ : (Finset.univ.filter (fun a ↦ assign (endpoint n x b a)∈F.image assign)).card ≤
            H*(F.image assign).card := by
          convert hc using 1
          congr 2
        exact_mod_cast hc₀
      convert hc' using 1
      congr 3)
  convert hh using 1
  · congr 3
    ext a
    simp [usedChoices]
  · ring

lemma blocked_card (A F C : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (hinj : ∀ b, Function.Injective (endpoint n x b)) (H : ℕ)
    (hfiber : ∀ b r, (Finset.univ.filter (fun a ↦ assign (endpoint n x b a)=r)).card ≤ H)
    (B K : ℝ)
    (hB : ((Erdos66AssignedPacketRepair.badChoices A assign n x).card : ℝ) ≤ B)
    (hK : ∀ z∈C, ((Erdos66AssignedPacketRepair.swapHits A assign n x z).card : ℝ) ≤ K) :
    ((blocked A F C assign n x).card : ℝ) ≤
      B+2*H*(F.image assign).card+C.card*(K+2*F.card+2) := by
  have hu : ((blocked A F C assign n x).card : ℝ) ≤
      (Erdos66AssignedPacketRepair.badChoices A assign n x).card+(usedChoices F assign n x).card+
        (C.biUnion (jointHits A F assign n x)).card := by
    have h1 := Finset.card_union_le
      (Erdos66AssignedPacketRepair.badChoices A assign n x ∪ usedChoices F assign n x)
      (C.biUnion (jointHits A F assign n x))
    have h2 := Finset.card_union_le (Erdos66AssignedPacketRepair.badChoices A assign n x) (usedChoices F assign n x)
    exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
  have hc : ((C.biUnion (jointHits A F assign n x)).card : ℝ) ≤ C.card*(K+2*F.card+2) := by
    have hh : ((C.biUnion (jointHits A F assign n x)).card : ℝ) ≤
        ∑ z∈C, ((jointHits A F assign n x z).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    apply hh.trans
    calc
      _ ≤ ∑ _z∈C, (K+2*F.card+2) :=
        Finset.sum_le_sum (fun z hz ↦ jointHits_card A F assign n x hinj z K (hK z hz))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  linarith [usedChoices_card F assign n x H hfiber]

lemma available_card (A F C : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (hinj : ∀ b, Function.Injective (endpoint n x b)) (H m : ℕ)
    (hF : F.card ≤ 2*m)
    (hfiber : ∀ b r, (Finset.univ.filter (fun a ↦ assign (endpoint n x b a)=r)).card ≤ H)
    (B K q : ℝ)
    (hB : ((Erdos66AssignedPacketRepair.badChoices A assign n x).card : ℝ) ≤ B)
    (hK : ∀ z∈C, ((Erdos66AssignedPacketRepair.swapHits A assign n x z).card : ℝ) ≤ K)
    (hbudget : q+B+4*H*m+C.card*(K+4*m+2) ≤ Fintype.card α) :
    q ≤ (available A F C assign n x).card := by
  have hb := blocked_card A F C assign n x hinj H hfiber B K hB hK
  have hFc : (F.card : ℝ) ≤ 2*m := by exact_mod_cast hF
  have hDc : ((F.image assign).card : ℝ) ≤ 2*m := by
    have hc : ((F.image assign).card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_image_le (s := F) (f := assign)
    exact hc.trans hFc
  have hH := Nat.cast_nonneg (α := ℝ) H
  have hC := Nat.cast_nonneg (α := ℝ) C.card
  have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (blocked A F C assign n x))
  have her : ((available A F C assign n x).card : ℝ)+(blocked A F C assign n x).card=Fintype.card α := by
    exact_mod_cast he
  nlinarith [mul_le_mul_of_nonneg_left hDc (show (0 : ℝ) ≤ 2*H by positivity),
    mul_le_mul_of_nonneg_left hFc (show (0 : ℝ) ≤ 2*C.card by positivity)]

lemma available_properties (A F C : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (a : α) (ha : a∈available A F C assign n x) :
    Disjoint A (packet n x a) ∧ Disjoint F (packet n x a) ∧
      Disjoint (F.image assign) ((packet n x a).image assign) ∧
      ∀ z∈C, a∉jointHits A F assign n x z := by
  have hn := (Finset.mem_sdiff.mp ha).2
  have hb : a∉Erdos66AssignedPacketRepair.badChoices A assign n x := fun h ↦
    hn (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hu : a∉usedChoices F assign n x := fun h ↦
    hn (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hD : Disjoint (F.image assign) ((packet n x a).image assign) := by
    apply Finset.disjoint_left.mpr
    intro u huf hup
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hup
    obtain ⟨b,rfl⟩ := (mem_packet_iff n x a v).mp hv
    exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,huf⟩)
  refine ⟨?_,?_,hD,?_⟩
  · apply Finset.disjoint_left.mpr
    intro u hua hup
    obtain ⟨b,rfl⟩ := (mem_packet_iff n x a u).mp hup
    exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,Or.inl hua⟩)
  · apply Finset.disjoint_left.mpr
    intro u huf hup
    exact Finset.disjoint_left.mp hD (Finset.mem_image.mpr ⟨u,huf,rfl⟩) (Finset.mem_image.mpr ⟨u,hup,rfl⟩)
  · intro z hz hhit
    exact hn (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z,hz,hhit⟩))

omit [Fintype α] in
lemma assigned_packet_injOn (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ) (a : α)
    (hsep : Function.Injective (fun b ↦ assign (endpoint n x b a))) :
    Set.InjOn assign (packet n x a : Set ℕ) := by
  intro u hu v hv he
  obtain ⟨b,rfl⟩ := (mem_packet_iff n x a u).mp hu
  obtain ⟨c,rfl⟩ := (mem_packet_iff n x a v).mp hv
  rw [hsep he]

lemma injOn_union_disjoint_image (F P : Finset ℕ) (assign : ℕ → ℕ)
    (hF : Set.InjOn assign (F : Set ℕ)) (hP : Set.InjOn assign (P : Set ℕ))
    (hD : Disjoint (F.image assign) (P.image assign)) :
    Set.InjOn assign (F∪P : Finset ℕ) := by
  intro u hu v hv he
  rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
  · exact hF hu hv he
  · exact (Finset.disjoint_left.mp hD (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
      (Finset.mem_image.mpr ⟨v,hv,he.symm⟩)).elim
  · exact (Finset.disjoint_left.mp hD (Finset.mem_image.mpr ⟨v,hv,he.symm⟩)
      (Finset.mem_image.mpr ⟨u,hu,rfl⟩)).elim
  · exact hP hu hv he

end Erdos66AdaptivePacketChoice
