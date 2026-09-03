import FormalConjecturesUtil
import Submission.PartialCloning

/-! Maximal disjoint neighbourhood supports leave a safe partial clone.
Disjointness is only for these supports, not for whole folded copies. -/
open SimpleGraph Finset
namespace Erdos713PartialCloning
open Erdos713Cloning
variable {W V : Type*}

lemma SupportedFold.card_ge_min_degree [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {v : V} {A : Finset V} (h : SupportedFold H G v A) {k : ℕ}
    (hdeg : ∀ a, k ≤ Nat.card (H.neighborSet a)) : k ≤ A.card := by
  classical
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber,hs⟩ := h
  let e : H.neighborSet a ↪ A := ⟨fun w => ⟨f w.val,hs w.val w.property⟩,by
    intro u w he
    apply Subtype.ext
    have hEq : f u.val = f w.val := congrArg Subtype.val he
    rcases hfiber u.val w.val hEq with hh | ⟨hu,hw⟩ | ⟨hu,hw⟩
    · exact hh
    · have huAdj : H.Adj a u.val := u.property
      exact (huAdj.ne hu.symm).elim
    · have hwAdj : H.Adj a w.val := w.property
      exact (hwAdj.ne hw.symm).elim⟩
  have hle : Nat.card (H.neighborSet a) ≤ A.card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Fintype.card_le_of_injective e e.injective
  exact (hdeg a).trans hle

/-- A bounded nonempty neighbour support carrying a folded copy. -/
def SmallSupport [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V) (v : V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (∀ w ∈ A, G.Adj v w) ∧ A.card ≤ Fintype.card W ∧ SupportedFold H G v A

def Packing [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V) (v : V)
    (F : Finset (Finset V)) : Prop :=
  (∀ A ∈ F, SmallSupport H G v A) ∧ (F : Set (Finset V)).PairwiseDisjoint id

lemma packing_empty [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V) (v : V) :
    Packing H G v ∅ := by simp [Packing]

/-- The uncovered neighbours form an H-free partial clone. -/
lemma exists_packing_with_safe_remainder [Fintype W] [Fintype V]
    (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (G : SimpleGraph V) (hfree : H.Free G) (v : V) :
    ∃ F : Finset (Finset V), Packing H G v F ∧
      ∃ Q : Finset V, (∀ w ∈ Q, G.Adj v w) ∧ H.Free (partialClone G Q) ∧
        Nat.card (G.neighborSet v) ≤ Q.card+Fintype.card W*F.card := by
  classical
  let P : Finset (Finset (Finset V)) := univ.filter (Packing H G v)
  have hP : P.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_univ _,packing_empty H G v⟩⟩
  obtain ⟨F,hFP,hmax⟩ := P.exists_max_image Finset.card hP
  have hF : Packing H G v F := (mem_filter.mp hFP).2
  let N := G.neighborFinset v
  let U := F.biUnion id
  let Q := N \ U
  have hQ : ∀ w ∈ Q, G.Adj v w := by
    intro w hw
    simpa only [N,mem_neighborFinset] using (mem_sdiff.mp hw).1
  have hSafe : H.Free (partialClone G Q) := by
    intro hcopy
    obtain ⟨A,hAQ,hNe,hAdj,hCard,hFold⟩ :=
      (supported_of_copy H G v Q hQ hfree hcopy).small_support hNoIso
    have hSmall : SmallSupport H G v A := ⟨hNe,hAdj,hCard,hFold⟩
    have hAU : ∀ w ∈ A, w ∉ U := fun w hw => (mem_sdiff.mp (hAQ hw)).2
    have hAnot : A ∉ F := by
      intro hAF
      obtain ⟨w,hw⟩ := hNe
      exact hAU w hw (mem_biUnion.mpr ⟨A,hAF,hw⟩)
    have hDis (B : Finset V) (hBF : B ∈ F) : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro w hwA hwB
      exact hAU w hwA (mem_biUnion.mpr ⟨B,hBF,hwB⟩)
    have hNew : Packing H G v (insert A F) := by
      refine ⟨?_,?_⟩
      · intro B hB
        rcases mem_insert.mp hB with rfl | hB
        · exact hSmall
        · exact hF.1 B hB
      · simpa only [coe_insert] using hF.2.insert_of_notMem hAnot hDis
    have hm := hmax (insert A F) (mem_filter.mpr ⟨mem_univ _,hNew⟩)
    rw [card_insert_of_notMem hAnot] at hm
    omega
  have hN : N.card = Nat.card (G.neighborSet v) := by
    simp only [N,card_neighborFinset_eq_degree,← card_neighborSet_eq_degree,Fintype.card_eq_nat_card]
  have hNU : N ⊆ Q ∪ U := by
    intro w hw
    by_cases hwU : w ∈ U
    · exact mem_union_right Q hwU
    · exact mem_union_left U (mem_sdiff.mpr ⟨hw,hwU⟩)
  have hCount : N.card ≤ Q.card+U.card := (card_le_card hNU).trans (card_union_le Q U)
  have hUnion : U.card ≤ Fintype.card W*F.card := by
    calc
      U.card ≤ ∑ A ∈ F, A.card := card_biUnion_le
      _ ≤ ∑ _A ∈ F, Fintype.card W := sum_le_sum (fun A hA => (hF.1 A hA).2.2.1)
      _ = Fintype.card W*F.card := by simp [Nat.mul_comm]
  refine ⟨F,hF,Q,hQ,hSafe,?_⟩
  rw [hN] at hCount
  omega

lemma exists_support_packing [Fintype W] [Fintype V]
    (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (G : SimpleGraph V) (hfree : H.Free G) (hB : G.IsBipartite) (v : V) :
    ∃ F : Finset (Finset V), Packing H G v F ∧
      Nat.card G.edgeSet+Nat.card (G.neighborSet v) ≤
        Erdos713BipExtremal.number (Fintype.card V+1) H+Fintype.card W*F.card := by
  obtain ⟨F,hF,Q,hQ,hSafe,hDeg⟩ := exists_packing_with_safe_remainder H hNoIso G hfree v
  have hs := safe_bound H G hB v Q hQ hSafe
  exact ⟨F,hF,by omega⟩

#print axioms SupportedFold.card_ge_min_degree
#print axioms exists_packing_with_safe_remainder
#print axioms exists_support_packing
end Erdos713PartialCloning
