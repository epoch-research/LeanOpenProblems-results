import FormalConjecturesUtil
import Submission.ThetaRigidOutsidePacking

/-! An explicit rigid theta-free family in which one zero-codegree pair
is charged at arbitrarily many distinct roots. This does not refute the
density-gap target: no small light-pair density is asserted. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713ThetaRigidChargeExample
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaBookTriangles
set_option maxHeartbeats 2000000

abbrev Rows (N : ℕ) := Fin 3 × Fin N
abbrev Cols (N r : ℕ) := Fin 3 ⊕ ((Fin N × Fin 2) ⊕ (Rows N × Fin r))

def Inc (N r : ℕ) (a : Rows N) : Cols N r → Prop
  | Sum.inl s => a.1=s
  | Sum.inr (Sum.inl p) => a.2=p.1
  | Sum.inr (Sum.inr p) => a=p.1

def hub {N r : ℕ} (s : Fin 3) : Cols N r := Sum.inl s
def anchor {N r : ℕ} (i : Fin N) (j : Fin 2) : Cols N r := Sum.inr (Sum.inl (i,j))
def petal {N r : ℕ} (a : Rows N) (j : Fin r) : Cols N r := Sum.inr (Sum.inr (a,j))

lemma common_of_index_ne {N r : ℕ} {a b : Rows N} (hne : a.2 ≠ b.2)
    {x : Cols N r} (ha : Inc N r a x) (hb : Inc N r b x) : x = hub a.1 := by
  rcases x with s | p
  · simp only [Inc] at ha
    simp only [hub,ha]
  · rcases p with p | p
    · exact (hne (ha.trans hb.symm)).elim
    · have he : a=b := ha.trans hb.symm
      exact (hne (congrArg Prod.snd he)).elim

lemma anchor_injective {N r : ℕ} (i : Fin N) : Function.Injective (@anchor N r i) := by
  intro j k he
  exact congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj he))

lemma petal_injective {N r : ℕ} (a : Rows N) : Function.Injective (@petal N r a) := by
  intro j k he
  exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj he))

lemma common_same_index {N r : ℕ} {a b : Rows N} (hne : a ≠ b) (hi : a.2=b.2) :
    row (Inc N r) a ∩ row (Inc N r) b = univ.image (@anchor N r a.2) := by
  have hs : a.1 ≠ b.1 := fun hh => hne (Prod.ext hh hi)
  ext x
  rcases x with s | p
  · simp only [mem_inter,mem_row,Inc,mem_image,mem_univ,true_and]
    simp only [anchor,Sum.inr_ne_inl,exists_false]
    exact ⟨fun h => hs (h.1.trans h.2.symm),False.elim⟩
  · rcases p with ⟨i,j⟩ | ⟨c,j⟩
    · simp [mem_row,Inc,anchor,hi,eq_comm]
    · simp only [mem_inter,mem_row,Inc,mem_image,mem_univ,true_and]
      simp only [anchor,Sum.inr.injEq,Sum.inl_ne_inr,exists_false]
      exact ⟨fun h => hne (h.1.trans h.2.symm),False.elim⟩


lemma private_common_side {N r : ℕ} {a b c : Rows N} (hac : a ≠ c)
    (hi : a.2=b.2) {x : Cols N r} (ha : Inc N r a x) (hc : Inc N r c x)
    (hb : ¬ Inc N r b x) : a.1=c.1 := by
  rcases x with t | p
  · exact ha.trans hc.symm
  · rcases p with p | p
    · exact (hb (hi.symm.trans ha)).elim
    · exact (hac (ha.trans hc.symm)).elim

theorem no_theta (N r : ℕ) : ¬ HasTheta (Inc N r) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hne01 : a 0 ≠ a 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (ha he)
  have hne02 : a 0 ≠ a 2 := fun he => (by decide : (0 : Fin 3) ≠ 2) (ha he)
  have hne12 : a 1 ≠ a 2 := fun he => (by decide : (1 : Fin 3) ≠ 2) (ha he)
  have hi : (a 0).2=(a 1).2 := by
    by_contra hne
    have h0 := common_of_index_ne hne h00 h10
    have h1 := common_of_index_ne hne h01 h11
    exact (by decide : (0 : Fin 4) ≠ 1) (hb (h0.trans h1.symm))
  have hcard : (row (Inc N r) (a 0) ∩ row (Inc N r) (a 1)).card = 2 := by
    rw [common_same_index hne01 hi,card_image_of_injective _ (anchor_injective _)]
    simp
  have hpair : row (Inc N r) (a 0) ∩ row (Inc N r) (a 1) = {b 0,b 1} := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [mem_row,h00,h10,h01,h11]
    · rw [hcard]
      simp [show b 0 ≠ b 1 from fun he => (by decide : (0 : Fin 4) ≠ 1) (hb he)]
  have hx : ¬ Inc N r (a 1) (b 2) := by
    intro hx
    have hm : b 2 ∈ row (Inc N r) (a 0) ∩ row (Inc N r) (a 1) := by simp [mem_row,h02,hx]
    rw [hpair] at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with he | he
    · exact (by decide : (2 : Fin 4) ≠ 0) (hb he)
    · exact (by decide : (2 : Fin 4) ≠ 1) (hb he)
  have hy : ¬ Inc N r (a 0) (b 3) := by
    intro hy
    have hm : b 3 ∈ row (Inc N r) (a 0) ∩ row (Inc N r) (a 1) := by simp [mem_row,h13,hy]
    rw [hpair] at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with he | he
    · exact (by decide : (3 : Fin 4) ≠ 0) (hb he)
    · exact (by decide : (3 : Fin 4) ≠ 1) (hb he)
  have hs0 := private_common_side hne02 hi h02 h22 hx
  have hs1 := private_common_side hne12 hi.symm h13 h23 hy
  exact hne01 (Prod.ext (hs0.trans hs1.symm) hi)

lemma row_eq (N r : ℕ) (a : Rows N) :
    row (Inc N r) a = insert (hub a.1)
      ((univ.image (@anchor N r a.2)) ∪ (univ.image (@petal N r a))) := by
  ext x
  rcases x with s | p
  · simp [mem_row,Inc,hub,anchor,petal,eq_comm]
  · rcases p with ⟨i,j⟩ | ⟨b,j⟩ <;> simp [mem_row,Inc,hub,anchor,petal,eq_comm]

lemma row_card (N r : ℕ) (a : Rows N) : (row (Inc N r) a).card = r+3 := by
  have hd : Disjoint (univ.image (@anchor N r a.2)) (univ.image (@petal N r a)) := by
    apply Finset.disjoint_left.mpr
    simp [anchor,petal]
  rw [row_eq,card_insert_of_notMem,card_union_of_disjoint hd,
    card_image_of_injective _ (anchor_injective _),card_image_of_injective _ (petal_injective _)]
  · simp
    omega
  · simp [hub,anchor,petal]


theorem rigid (N r : ℕ) (a b : Rows N) (hne : a ≠ b) :
    (row (Inc N r) a ∩ row (Inc N r) b).card ≤ 2 := by
  by_cases hi : a.2=b.2
  · rw [common_same_index hne hi,card_image_of_injective _ (anchor_injective _)]
    simp
  · have hs : row (Inc N r) a ∩ row (Inc N r) b ⊆ {hub a.1} := by
      intro x hx
      have hh := mem_inter.mp hx
      have he := common_of_index_ne hi ((mem_row _ _ _).mp hh.1) ((mem_row _ _ _).mp hh.2)
      simpa only [mem_singleton] using he
    exact (card_le_card hs).trans (by simp)

lemma matched_adj (N r : ℕ) (i : Fin N) :
    (overlapGraph (Inc N r)).Adj (0,i) (1,i) := by
  have hne : ((0 : Fin 3),i) ≠ (1,i) := by simp
  have hcard : (row (Inc N r) (0,i) ∩ row (Inc N r) (1,i)).card = 2 := by
    rw [common_same_index (r := r) hne rfl,card_image_of_injective _ (anchor_injective _)]
    simp
  refine ⟨hne,?_⟩
  convert hcard.ge using 1
  congr 1
  ext x
  simp only [Finset.mem_inter]

lemma anchor_codegree (N r : ℕ) (i : Fin N) :
    codegree (Inc N r) (anchor i 0) (anchor i 1) = 3 := by
  let e : {a : Rows N // Inc N r a (anchor i 0) ∧ Inc N r a (anchor i 1)} ≃ Fin 3 := {
    toFun := fun a => a.val.1
    invFun := fun s => ⟨(s,i),rfl,rfl⟩
    left_inv := fun a => Subtype.ext (Prod.ext rfl a.property.1.symm)
    right_inv := fun s => rfl }
  change Nat.card _ = 3
  rw [Nat.card_congr e]
  simp

lemma hubs_zero (N r : ℕ) : codegree (Inc N r) (hub 0) (hub 1) = 0 := by
  have hh : IsEmpty {a : Rows N // Inc N r a (hub 0) ∧ Inc N r a (hub 1)} := by
    refine ⟨fun a => ?_⟩
    have he : (0 : Fin 3)=1 := a.property.1.symm.trans a.property.2
    exact (by decide : (0 : Fin 3) ≠ 1) he
  letI := hh
  exact Nat.card_of_isEmpty

lemma heavy_witness (N r : ℕ) (i : Fin N) :
    ((anchor i 0,anchor i 1),(1,i)) ∈
      Erdos713ThetaAllWitnessPacking.witnesses (Inc N r) univ (0,i) := by
  have hc : (Erdos713ThetaAnchorPacking.commonRows (Inc N r) univ
      (anchor i 0,anchor i 1)).card = 3 := by
    simpa only [Erdos713ThetaAnchorPacking.commonRows,codegree,Nat.card_eq_fintype_card,
      Fintype.card_subtype,mem_univ,true_and] using anchor_codegree N r i
  rw [Erdos713ThetaAllWitnessPacking.mem_witnesses]
  refine ⟨?_,?_,by simp⟩
  · apply mem_filter.mpr
    refine ⟨mem_offDiag.mpr ⟨?_,?_,?_⟩,hc.ge⟩
    · simp [mem_row,Inc,anchor]
    · simp [mem_row,Inc,anchor]
    · intro he
      have hh := anchor_injective i he
      exact (by decide : (0 : Fin 2) ≠ 1) hh
  · simp [Erdos713ThetaAnchorPacking.commonRows,Inc,anchor]

lemma private_hub (N r : ℕ) (i : Fin N) :
    hub 1 ∈ Erdos713ThetaPrivatePetals.privatePetal (Inc N r) univ
      (anchor i 0,anchor i 1) (1,i) := by
  rw [Erdos713ThetaPrivatePetals.mem_privatePetal]
  refine ⟨rfl,by simp [hub,anchor],by simp [hub,anchor],?_⟩
  intro a ha hne hh
  have hi : a.2=i := (mem_filter.mp ha).2.1
  exact hne (Prod.ext hh hi)

/-- The original all-witness packing construction counts this SAME zero
pair at N distinct roots, using genuinely heavy anchors. -/
theorem actual_witnesses (N r : ℕ) :
    ∃ u : Fin N → Rows N, Function.Injective u ∧ ∀ i,
      ∃ w ∈ Erdos713ThetaAllWitnessPacking.witnesses (Inc N r) univ (u i),
        hub 0 ∈ row (Inc N r) (u i) \ row (Inc N r) w.2 ∧
        hub 1 ∈ Erdos713ThetaPrivatePetals.privatePetal (Inc N r) univ w.1 w.2 := by
  refine ⟨fun i => (0,i),fun i j he => congrArg Prod.snd he,?_⟩
  intro i
  exact ⟨((anchor i 0,anchor i 1),(1,i)),heavy_witness N r i,
    by simp [mem_row,hub,Inc],private_hub N r i⟩

/-- One zero pair belongs to private-petal rectangles at N distinct roots,
even with an arbitrarily large common row degree and full rigidity. -/
theorem unbounded_root_multiplicity (N r : ℕ) :
    ¬ HasTheta (Inc N r) ∧
    (∀ a b, a ≠ b → (row (Inc N r) a ∩ row (Inc N r) b).card ≤ 2) ∧
    (∀ a, (row (Inc N r) a).card = r+3) ∧
    codegree (Inc N r) (hub 0) (hub 1) = 0 ∧
    (∀ i : Fin N, codegree (Inc N r) (anchor i 0) (anchor i 1) = 3) ∧
    ∃ u v : Fin N → Rows N, Function.Injective u ∧ Function.Injective v ∧
      ∀ i, (overlapGraph (Inc N r)).Adj (u i) (v i) ∧
        hub 0 ∈ row (Inc N r) (u i) \ row (Inc N r) (v i) ∧
        hub 1 ∈ row (Inc N r) (v i) \ row (Inc N r) (u i) := by
  refine ⟨no_theta N r,rigid N r,row_card N r,hubs_zero N r,anchor_codegree N r,
    (fun i => (0,i)),(fun i => (1,i)),?_,?_,?_⟩
  · intro i j he
    exact congrArg Prod.snd he
  · intro i j he
    exact congrArg Prod.snd he
  · intro i
    exact ⟨matched_adj N r i,by simp [mem_row,hub,Inc],by simp [mem_row,hub,Inc]⟩

#print axioms no_theta
#print axioms rigid
#print axioms row_card
#print axioms anchor_codegree
#print axioms unbounded_root_multiplicity
#print axioms actual_witnesses
end Erdos713ThetaRigidChargeExample
