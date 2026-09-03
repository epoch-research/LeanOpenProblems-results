import FormalConjecturesUtil
import Submission.CloneIncrementGap

/-! Deleting arbitrary old edges does not make bounded-neighbourhood cloning
competitive with global C4 extremal increments. This is an auxiliary obstruction,
not a proof or disproof of the rationality conjecture. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713CloneRepairGap
open Erdos713C4 Erdos713PartialCloning Erdos713CloneIncrementGap
variable {V : Type*}
set_option maxHeartbeats 2000000

lemma retained_common_card_le_one (K : SimpleGraph V) (Q : Finset V)
    (hf : K22.Free (partialClone K Q)) (v : V) :
    (Q.filter (K.Adj v)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, hva⟩ := mem_filter.mp ha
  obtain ⟨hb, hvb⟩ := mem_filter.mp hb
  apply Option.some.inj
  exact unique_common_of_free hf (u := none) (v := some v)
    (by simp) ha hva hb hvb

/-- Charge covered vertices to retained incidences or distinct deleted edges. -/
theorem covered_budget [Fintype V] (G K : SimpleGraph V) (S Q : Finset V)
    (hcover : ∀ w ∈ Q, ∃ v ∈ S, G.Adj v w)
    (r : ℕ) (hret : ∀ v ∈ S, (Q.filter (K.Adj v)).card ≤ r) :
    Q.card ≤ (r+1)*S.card + (G.edgeFinset \ K.edgeFinset).card := by
  classical
  let T := S.biUnion (fun v => Q.filter (K.Adj v))
  have hT : T.card ≤ r*S.card := by
    calc
      T.card ≤ ∑ v ∈ S, (Q.filter (K.Adj v)).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S, r := sum_le_sum hret
      _ = r*S.card := by simp [Nat.mul_comm]
  let B := (Q \ S) \ T
  let D := G.edgeFinset \ K.edgeFinset
  have hBQ (w : B) : w.val ∈ Q := (mem_sdiff.mp (mem_sdiff.mp w.property).1).1
  have hBS (w : B) : w.val ∉ S := (mem_sdiff.mp (mem_sdiff.mp w.property).1).2
  have hBT (w : B) : w.val ∉ T := (mem_sdiff.mp w.property).2
  let r : B → V := fun w => Classical.choose (hcover w.val (hBQ w))
  have hr (w : B) : r w ∈ S ∧ G.Adj (r w) w.val :=
    Classical.choose_spec (hcover w.val (hBQ w))
  have hnot (w : B) : ¬ K.Adj (r w) w.val := by
    intro h
    apply hBT w
    exact mem_biUnion.mpr ⟨r w,(hr w).1,mem_filter.mpr ⟨hBQ w,h⟩⟩
  let f : B → D := fun w => ⟨s(r w,w.val),by
    apply mem_sdiff.mpr
    constructor
    · simpa only [mem_edgeFinset, mem_edgeSet] using (hr w).2
    · simpa only [mem_edgeFinset, mem_edgeSet] using hnot w⟩
  have hinj : Function.Injective f := by
    intro w z h
    have he : s(r w,w.val) = s(r z,z.val) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp he with h | h
    · exact Subtype.ext h.2
    · exact False.elim (hBS w (h.2 ▸ (hr z).1))
  have hB : B.card ≤ D.card := by
    simpa using Fintype.card_le_of_injective f hinj
  have hsub : Q ⊆ S ∪ T ∪ B := by
    intro w hw
    by_cases hs : w ∈ S
    · exact mem_union_left _ (mem_union_left _ hs)
    by_cases ht : w ∈ T
    · exact mem_union_left _ (mem_union_right _ ht)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hw,hs⟩,ht⟩)
  have hu : Q.card ≤ S.card+T.card+B.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  dsimp [D] at hB
  nlinarith

/-- New neighbours covered by k old neighbourhoods require at least |Q|-2k
old-edge deletions if the repaired extension is C4-free. -/
theorem neighbour_budget [Fintype V] (G K : SimpleGraph V) (S Q : Finset V)
    (hcover : ∀ w ∈ Q, ∃ v ∈ S, G.Adj v w)
    (hf : K22.Free (partialClone K Q)) :
    Q.card ≤ 2*S.card + (G.edgeFinset \ K.edgeFinset).card :=
  covered_budget G K S Q hcover 1 (fun v _ => retained_common_card_le_one K Q hf v)

/-- Even an arbitrary edge deletion before cloning cannot create an
unbounded net gain from a bounded union of old vertex neighbourhoods. -/
theorem net_gain_le [Fintype V] (G K : SimpleGraph V) (S Q : Finset V)
    (hle : K ≤ G) (hcover : ∀ w ∈ Q, ∃ v ∈ S, G.Adj v w)
    (hf : K22.Free (partialClone K Q)) :
    Nat.card (partialClone K Q).edgeSet ≤ Nat.card G.edgeSet + 2*S.card := by
  classical
  have hb := neighbour_budget G K S Q hcover hf
  have he := card_sdiff_add_card_eq_card (edgeFinset_mono hle)
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he
  rw [card_edges]
  omega

/-- Exact C4 extremizers have cofinally large gaps from every such repaired
extension, uniformly over the chosen roots, deleted old edges and new star. -/
theorem exact_hosts_repair_gap (N D k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n ∧ K22.Free G ∧
      Nat.card G.edgeSet = extremalNumber n K22 ∧
      ∀ (K : SimpleGraph (Fin n)) (S Q : Finset (Fin n)), K ≤ G → S.card ≤ k →
        (∀ w ∈ Q, ∃ v ∈ S, G.Adj v w) → K22.Free (partialClone K Q) →
        Nat.card (partialClone K Q).edgeSet + D < extremalNumber (n+1) K22 := by
  obtain ⟨n,hn,hinc⟩ := c4_cofinal_large_increment N (D+2*k)
  have hedge : ∃ a b, K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [K22,completeBipartiteGraph]⟩
  obtain ⟨G,hG,he⟩ := Erdos713CloneSymm.exists_ordinary_optimal K22 hedge n
  refine ⟨n,G,hn,hG.free,he,?_⟩
  intro K S Q hle hS hcover hf
  have hbound := net_gain_le G K S Q hle hcover hf
  rw [he] at hbound
  omega

end Erdos713CloneRepairGap
