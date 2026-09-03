import Submission.AssignedPacketDegreeExplore

/-! Algebra for adjoining one symmetric packet to a jointly selected family.
The load includes deletions and all undesignated new/new pairs. -/
namespace Erdos66AdaptivePacketAlgebra
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
open scoped Classical
set_option maxHeartbeats 2500000

variable {α : Type*}

noncomputable def packet (n : ℕ) (x : α → ℕ) (a : α) : Finset ℕ := {x a,n-x a}

lemma mem_packet_iff (n : ℕ) (x : α → ℕ) (a : α) (u : ℕ) :
    u∈packet n x a ↔ ∃ b, u=endpoint n x b a := by
  simp only [packet,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  · rintro ⟨b,rfl⟩
    cases b <;> simp [endpoint]

lemma packet_card (n : ℕ) (x : α → ℕ) (a : α) (hh : 2*x a<n) :
    (packet n x a).card=2 := by
  have he : x a≠n-x a := by omega
  simp [packet,he]

lemma pairs_singletons (u v z : ℕ) :
    pairs {u} {v} z=if u+v=z then 1 else 0 := by
  rw [pairs,Finset.product_eq_sprod,Finset.singleton_product_singleton,Finset.filter_singleton]
  split_ifs <;> simp_all

lemma singleton_rep (u z : ℕ) :
    sumRep ({u} : Set ℕ) z=if 2*u=z then 1 else 0 := by
  have hh := pairs_singletons u u z
  rw [pairs_self] at hh
  simpa only [Finset.coe_singleton,two_mul] using hh

lemma packet_rep (n : ℕ) (x : α → ℕ) (a : α) (hh : 2*x a<n) (z : ℕ) :
    sumRep (packet n x a : Set ℕ) z=
      (if 2*x a=z then 1 else 0)+2*(if n=z then 1 else 0)+
        (if 2*(n-x a)=z then 1 else 0) := by
  have hxy : x a≠n-x a := by omega
  have hd : Disjoint ({x a} : Finset ℕ) {n-x a} := by simpa using hxy
  have hu : ({x a} : Finset ℕ)∪{n-x a}=packet n x a := by ext u; simp [packet,or_comm]
  have h := sumRep_union_self {x a} {n-x a} z hd
  rw [hu,pairs_singletons] at h
  simp only [Finset.coe_singleton,singleton_rep] at h
  simpa only [show x a+(n-x a)=n by omega] using h

variable [Fintype α]

noncomputable def extraHits (F : Finset ℕ) (n : ℕ) (x : α → ℕ) (z : ℕ) : Finset α :=
  Finset.univ.filter (fun a ↦ ∃ b : Bool,
    (endpoint n x b a ≤ z ∧ z-endpoint n x b a∈F) ∨ 2*endpoint n x b a=z)

omit [Fintype α] in
lemma packet_pairs_le (n : ℕ) (x : α → ℕ) (a : α) (B : Finset ℕ) (z : ℕ) :
    pairs (packet n x a) B z ≤ 2 := by
  rw [pairs_eq_filter]
  exact (Finset.card_filter_le _ _).trans Finset.card_le_two

omit [Fintype α] in
lemma assigned_packet_pairs_le (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ) (a : α)
    (B : Finset ℕ) (z : ℕ) :
    pairs ((packet n x a).image assign) B z ≤ 2 := by
  rw [pairs_eq_filter]
  exact (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans Finset.card_le_two)

lemma no_extra_hits (F : Finset ℕ) (n : ℕ) (x : α → ℕ) (a : α) (z : ℕ)
    (ha : a∉extraHits F n x z) :
    pairs (packet n x a) F z=0 ∧ 2*x a≠z ∧ 2*(n-x a)≠z := by
  have hn (b : Bool) : ¬((endpoint n x b a ≤ z ∧ z-endpoint n x b a∈F) ∨
      2*endpoint n x b a=z) := by
    intro hb
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hb⟩)
  refine ⟨?_,fun he ↦ hn false (Or.inr he),fun he ↦ hn true (Or.inr he)⟩
  apply pairs_eq_zero_of_no_partner
  intro u hu huz huf
  obtain ⟨b,rfl⟩ := (mem_packet_iff n x a u).mp hu
  exact hn b (Or.inl ⟨huz,huf⟩)

lemma no_old_hits (A : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (a : α) (z : ℕ) (ha : a∉Erdos66AssignedPacketRepair.swapHits A assign n x z) :
    pairs (packet n x a) A z=0 ∧ pairs ((packet n x a).image assign) A z=0 := by
  have hn (b : Bool) : ¬((endpoint n x b a ≤ z ∧ z-endpoint n x b a∈A) ∨
      (assign (endpoint n x b a) ≤ z ∧ z-assign (endpoint n x b a)∈A)) := by
    intro hb
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hb⟩)
  constructor
  · apply pairs_eq_zero_of_no_partner
    intro u hu huz hua
    obtain ⟨b,rfl⟩ := (mem_packet_iff n x a u).mp hu
    exact hn b (Or.inl ⟨huz,hua⟩)
  · apply pairs_eq_zero_of_no_partner
    intro u hu huz hua
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,rfl⟩ := (mem_packet_iff n x a v).mp hv
    exact hn b (Or.inr ⟨huz,hua⟩)

noncomputable def jointHits (A F : Finset ℕ) (assign : ℕ → ℕ)
    (n : ℕ) (x : α → ℕ) (z : ℕ) : Finset α :=
  Erdos66AssignedPacketRepair.swapHits A assign n x z ∪ extraHits F n x z

/-- Symmetric upper/lower collateral certificate before subtracting the
prescribed packet contribution. -/
noncomputable def energy (A F : Finset ℕ) (assign : ℕ → ℕ) (z : ℕ) : ℝ :=
  2*pairs F A z+2*pairs (F.image assign) A z+sumRep (F : Set ℕ) z

lemma energy_step (A F : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (a : α) (hh : 2*x a<n)
    (hF : Disjoint F (packet n x a))
    (hD : Disjoint (F.image assign) ((packet n x a).image assign)) (z : ℕ) :
    energy A (F∪packet n x a) assign z-energy A F assign z-
      2*(if n=z then (1 : ℝ) else 0) ≤
        14*(if a∈jointHits A F assign n x z then (1 : ℝ) else 0) := by
  have he : energy A (F∪packet n x a) assign z-energy A F assign z-
      2*(if n=z then (1 : ℝ) else 0) =
      2*pairs (packet n x a) A z+2*pairs ((packet n x a).image assign) A z+
      2*pairs (packet n x a) F z+(if 2*x a=z then (1 : ℝ) else 0)+
        (if 2*(n-x a)=z then (1 : ℝ) else 0) := by
    rw [energy,energy,Finset.image_union,pairs_union_left _ _ _ _ hF,
      pairs_union_left _ _ _ _ hD,sumRep_union_self _ _ _ hF,
      packet_rep n x a hh z,pairs_comm F (packet n x a)]
    push_cast
    ring
  rw [he]
  by_cases ha : a∈jointHits A F assign n x z
  · rw [if_pos ha]
    have h1 : (pairs (packet n x a) A z : ℝ) ≤ 2 := by exact_mod_cast packet_pairs_le n x a A z
    have h2 : (pairs ((packet n x a).image assign) A z : ℝ) ≤ 2 := by
      exact_mod_cast assigned_packet_pairs_le assign n x a A z
    have h3 : (pairs (packet n x a) F z : ℝ) ≤ 2 := by exact_mod_cast packet_pairs_le n x a F z
    split_ifs <;> linarith
  · rw [if_neg ha]
    have ha' := Finset.notMem_union.mp ha
    obtain ⟨h1,h2⟩ := no_old_hits A assign n x a z ha'.1
    obtain ⟨h3,h4,h5⟩ := no_extra_hits F n x a z ha'.2
    simp [h1,h2,h3,h4,h5]

lemma energy_center_step (A F : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (a : α) (hh : 2*x a<n) (z : ℕ) (ha : a∉jointHits A F assign n x z)
    (hF : Disjoint F (packet n x a))
    (hD : Disjoint (F.image assign) ((packet n x a).image assign)) :
    pairs (F∪packet n x a) A z=pairs F A z ∧
    pairs ((F∪packet n x a).image assign) A z=pairs (F.image assign) A z ∧
    sumRep (F∪packet n x a : Finset ℕ) z=
      sumRep (F : Set ℕ) z+2*(if n=z then 1 else 0) := by
  have ha' := Finset.notMem_union.mp ha
  obtain ⟨h1,h2⟩ := no_old_hits A assign n x a z ha'.1
  obtain ⟨h3,h4,h5⟩ := no_extra_hits F n x a z ha'.2
  rw [pairs_union_left _ _ _ _ hF,Finset.image_union,pairs_union_left _ _ _ _ hD,
    sumRep_union_self _ _ _ hF,packet_rep n x a hh z,pairs_comm F (packet n x a)]
  simp [h1,h2,h3,h4,h5]

lemma swapped_no_old_hits (A D F : Finset ℕ) (hD : D ⊆ A) (hF : Disjoint A F)
    (z : ℕ) (hd : pairs D A z=0) (hf : pairs F A z=0) :
    sumRep (swapped A D F : Set ℕ) z=sumRep (A : Set ℕ) z+sumRep (F : Set ℕ) z := by
  have hdd := pairs_mono_right hD (A := D) z
  have hdc := pairs_mono_right (show A\D ⊆ A from Finset.sdiff_subset) (A := D) z
  rw [hd,pairs_self] at hdd
  rw [hd,pairs_comm D (A\D)] at hdc
  have hs := sumRep_union_self (A\D) D z Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD] at hs
  have hfc := pairs_mono_right (show A\D ⊆ A from Finset.sdiff_subset) (A := F) z
  rw [hf,pairs_comm F (A\D)] at hfc
  rw [swapped,sumRep_union_self _ _ _ (hF.mono_left Finset.sdiff_subset)]
  omega

lemma swapped_error_le_energy (A F : Finset ℕ) (assign : ℕ → ℕ)
    (hD : F.image assign ⊆ A) (hF : Disjoint A F) (z : ℕ) :
    |(sumRep (swapped A (F.image assign) F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z| ≤
      energy A F assign z := by
  have hu := sumRep_swapped_upper A (F.image assign) F hF z
  have hl := sumRep_swapped_lower A (F.image assign) F hD z
  have hu' : (sumRep (swapped A (F.image assign) F : Set ℕ) z : ℝ) ≤
      sumRep (A : Set ℕ) z+2*pairs F A z+sumRep (F : Set ℕ) z := by exact_mod_cast hu
  have hl' : (sumRep (A : Set ℕ) z : ℝ) ≤
      sumRep (swapped A (F.image assign) F : Set ℕ) z+2*pairs (F.image assign) A z := by exact_mod_cast hl
  rw [abs_le]
  dsimp only [energy]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (pairs F A z),
    Nat.cast_nonneg (α := ℝ) (pairs (F.image assign) A z),Nat.cast_nonneg (α := ℝ) (sumRep (F : Set ℕ) z)]

end Erdos66AdaptivePacketAlgebra
