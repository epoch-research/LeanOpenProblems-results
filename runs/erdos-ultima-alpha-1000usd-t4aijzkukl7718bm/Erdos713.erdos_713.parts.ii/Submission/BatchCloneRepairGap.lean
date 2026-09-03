import FormalConjecturesUtil
import Submission.CloneRepairGap

/-! Uniform C4 repair bounds for a batch of new vertices. Arbitrary old-edge
deletions and arbitrary edges inside the new batch are allowed. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713BatchCloneRepairGap
open Erdos713C4 Erdos713PartialCloning Erdos713CloneRepairGap
variable {V W : Type*}
set_option maxHeartbeats 2000000

/-- A linear set system has at most choose(t,2) incidences beyond its union. -/
lemma sum_card_le_union_add_choose (T : Finset W) (Q : W → Finset V)
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ T, (Q i).card) ≤ (T.biUnion Q).card + T.card.choose 2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hT : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → (Q j ∩ Q k).card ≤ 1 := by
      intro j hj k hk hjk
      exact h j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hjk
    have hh := ih hT
    have hinter : (Q i ∩ T.biUnion Q).card ≤ T.card := by
      rw [inter_biUnion]
      calc
        _ ≤ ∑ j ∈ T, (Q i ∩ Q j).card := card_biUnion_le
        _ ≤ ∑ _j ∈ T, 1 := sum_le_sum (fun j hj =>
          h i (mem_insert_self _ _) j (mem_insert_of_mem hj)
            (fun he => hi (he ▸ hj)))
        _ = T.card := by simp
    have hc := card_union_add_card_inter (Q i) (T.biUnion Q)
    rw [sum_insert hi, biUnion_insert, card_insert_of_notMem hi]
    have hchoose : (T.card+1).choose 2 = T.card + T.card.choose 2 := by
      simpa using Nat.choose_succ_succ T.card 1
    rw [hchoose]
    omega

/-- Old graph K, arbitrary new graph L, and prescribed old-new incidences. -/
def relationPatch (K : SimpleGraph V) (L : SimpleGraph W) (P : W → V → Prop) :
    SimpleGraph (V ⊕ W) where
  Adj
    | .inl a,.inl b => K.Adj a b
    | .inl a,.inr b => P b a
    | .inr a,.inl b => P a b
    | .inr a,.inr b => L.Adj a b
  symm := by
    rintro (a|a) (b|b) h <;> first | exact h | exact h.symm
  loopless := by
    rintro (a|a) h
    · exact K.loopless a h
    · exact L.loopless a h

def patch (K : SimpleGraph V) (L : SimpleGraph W) (Q : W → Finset V) :
    SimpleGraph (V ⊕ W) := relationPatch K L (fun w v => v ∈ Q w)

lemma partial_free (K : SimpleGraph V) (L : SimpleGraph W) (Q : W → Finset V)
    (hf : K22.Free (patch K L Q)) (w : W) : K22.Free (partialClone K (Q w)) := by
  have hc : partialClone K (Q w) ⊑ patch K L Q := by
    refine ⟨⟨⟨(fun a => match a with | none => Sum.inr w | some v => Sum.inl v),?_⟩,?_⟩⟩
    · rintro (_|a) (_|b) h
      · exact h.elim
      · exact h
      · exact h
      · exact h
    · rintro (_|a) (_|b) h <;> simp_all
  exact fun h => hf (h.trans hc)

lemma pair_intersection_le_one (K : SimpleGraph V) (L : SimpleGraph W) (Q : W → Finset V)
    (hf : K22.Free (patch K L Q)) (i j : W) (hij : i ≠ j) :
    (Q i ∩ Q j).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  apply Sum.inl_injective
  exact unique_common_of_free hf (u := Sum.inr i) (v := Sum.inr j)
    (by simpa using hij) (mem_inter.mp ha).1 (mem_inter.mp ha).2
      (mem_inter.mp hb).1 (mem_inter.mp hb).2

lemma cross_budget [Fintype V] [Fintype W]
    (G K : SimpleGraph V) (L : SimpleGraph W) (S : Finset V) (Q : W → Finset V)
    (hcover : ∀ w v, v ∈ Q w → ∃ s ∈ S, G.Adj s v)
    (hf : K22.Free (patch K L Q)) :
    (∑ w, (Q w).card) ≤ (G.edgeFinset \ K.edgeFinset).card +
      (Fintype.card W+1)*S.card + (Fintype.card W).choose 2 := by
  classical
  let A := univ.biUnion Q
  have hA : ∀ v ∈ A, ∃ s ∈ S, G.Adj s v := by
    intro v hv
    obtain ⟨w,_,hw⟩ := mem_biUnion.mp hv
    exact hcover w v hw
  have hret : ∀ v ∈ S, (A.filter (K.Adj v)).card ≤ Fintype.card W := by
    intro v _
    have he : A.filter (K.Adj v) = univ.biUnion (fun w => (Q w).filter (K.Adj v)) := by
      ext x
      simp only [A,mem_filter,mem_biUnion,mem_univ,true_and]
      aesop
    rw [he]
    calc
      _ ≤ ∑ w : W, ((Q w).filter (K.Adj v)).card := card_biUnion_le
      _ ≤ ∑ _w : W, 1 := sum_le_sum (fun w _ =>
        retained_common_card_le_one K (Q w) (partial_free K L Q hf w) v)
      _ = Fintype.card W := by simp
  have hb := covered_budget G K S A hA (Fintype.card W) hret
  have hi := sum_card_le_union_add_choose univ Q
    (fun i _ j _ hij => pair_intersection_le_one K L Q hf i j hij)
  simp only [card_univ] at hi
  dsimp [A] at hb
  omega

lemma relationPatch_card [Fintype V] [Fintype W]
    (K : SimpleGraph V) (L : SimpleGraph W) (P : W → V → Prop) :
    Nat.card (relationPatch K L P).edgeSet = Nat.card K.edgeSet + Nat.card L.edgeSet +
      Nat.card {p : W × V // P p.1 p.2} := by
  classical
  have h := (relationPatch K L P).two_mul_card_edgeFinset
  have hK := K.two_mul_card_edgeFinset
  have hL := L.two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,Fintype.sum_sum_type,relationPatch,
    sum_add_distrib,edgeFinset_card,← Nat.card_eq_fintype_card] at h hK hL
  rw [sum_comm (f := fun v w => if P w v then 1 else 0)] at h
  have hP : (∑ w : W, ∑ v : V, if P w v then 1 else 0) =
      Nat.card {p : W × V // P p.1 p.2} := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,Fintype.sum_prod_type]
  rw [hP,← hK,← hL] at h
  change 2*Nat.card (relationPatch K L P).edgeSet = _ at h
  omega

lemma patch_card [Fintype V] [Fintype W]
    (K : SimpleGraph V) (L : SimpleGraph W) (Q : W → Finset V) :
    Nat.card (patch K L Q).edgeSet = Nat.card K.edgeSet + Nat.card L.edgeSet +
      ∑ w, (Q w).card := by
  rw [patch, relationPatch_card]
  congr 1
  let e : {p : W × V // p.2 ∈ Q p.1} ≃ (w : W) × Q w := {
    toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
    left_inv := by rintro ⟨⟨w,v⟩,h⟩; rfl
    right_inv := by rintro ⟨w,⟨v,h⟩⟩; rfl }
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_coe] using Nat.card_congr e

/-- A t-vertex C4-free patch covered by k old neighbourhoods gains at most
(t+1)k+2*choose(t,2) edges, regardless of how many old edges are deleted. -/
theorem net_gain_le [Fintype V] [Fintype W]
    (G K : SimpleGraph V) (L : SimpleGraph W) (S : Finset V) (Q : W → Finset V)
    (hle : K ≤ G) (hcover : ∀ w v, v ∈ Q w → ∃ s ∈ S, G.Adj s v)
    (hf : K22.Free (patch K L Q)) :
    Nat.card (patch K L Q).edgeSet ≤ Nat.card G.edgeSet +
      (Fintype.card W+1)*S.card + 2*(Fintype.card W).choose 2 := by
  classical
  have hb := cross_budget G K L S Q hcover hf
  have he := card_sdiff_add_card_eq_card (edgeFinset_mono hle)
  have hL : Nat.card L.edgeSet ≤ (Fintype.card W).choose 2 := by
    simpa only [edgeFinset_card,Nat.card_eq_fintype_card] using L.card_edgeFinset_le_card_choose_two
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at he
  rw [patch_card]
  omega

/-- Cofinal exact C4 extremizers are arbitrarily far from every bounded
batch repair of this form, even compared with the next single-vertex extremal
number. The batch, old-edge deletions, and its internal edges are arbitrary. -/
theorem exact_hosts_batch_gap (N D k t : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n ∧ K22.Free G ∧
      Nat.card G.edgeSet = extremalNumber n K22 ∧
      ∀ (K : SimpleGraph (Fin n)) (L : SimpleGraph (Fin t))
        (S : Finset (Fin n)) (Q : Fin t → Finset (Fin n)),
        K ≤ G → S.card ≤ k →
        (∀ w v, v ∈ Q w → ∃ s ∈ S, G.Adj s v) → K22.Free (patch K L Q) →
        Nat.card (patch K L Q).edgeSet + D < extremalNumber (n+1) K22 := by
  obtain ⟨n,hn,hinc⟩ := Erdos713CloneIncrementGap.c4_cofinal_large_increment N
    (D+(t+1)*k+2*t.choose 2)
  have hedge : ∃ a b, K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [K22,completeBipartiteGraph]⟩
  obtain ⟨G,hG,he⟩ := Erdos713CloneSymm.exists_ordinary_optimal K22 hedge n
  refine ⟨n,G,hn,hG.free,he,?_⟩
  intro K L S Q hle hS hcover hf
  have hb := net_gain_le G K L S Q hle hcover hf
  simp only [Fintype.card_fin,he] at hb
  have hm := Nat.mul_le_mul_left (t+1) hS
  omega

end Erdos713BatchCloneRepairGap
