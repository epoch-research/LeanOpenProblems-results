import FormalConjecturesUtil
import Submission.CloneSupportPacking

/-! A support of a forbidden single fold has bounded common neighbourhood.
The bound is for the full common neighbourhood, not only the designated root. -/
open SimpleGraph Finset
namespace Erdos713PartialCloning
variable {W V : Type*}

open scoped Classical in
lemma SupportedFold.common_neighbors_le [Fintype W] [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} {v : V} {A : Finset V}
    (hfree : H.Free G) (h : SupportedFold H G v A) :
    (univ.filter (fun u => ∀ w ∈ A, G.Adj u w)).card ≤ Fintype.card W - 1 := by
  classical
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber,hs⟩ := h
  let I := (univ.erase a).image f
  have hmem (w : W) (hw : w ≠ a) : f w ∈ I :=
    mem_image_of_mem f (mem_erase.mpr ⟨hw,mem_univ _⟩)
  have hsubset : univ.filter (fun u => ∀ w ∈ A, G.Adj u w) ⊆ I := by
    intro u hu
    have huAdj := (mem_filter.mp hu).2
    by_contra huI
    let g : H →g G := {
      toFun := fun w => if w = a then u else f w
      map_rel' := by
        intro x y hxy
        by_cases hx : x = a
        · subst x
          have hy : y ≠ a := hxy.ne.symm
          simp only [if_neg hy]
          exact huAdj (f y) (hs y hxy)
        · by_cases hy : y = a
          · subst y
            simp only [if_neg hx]
            exact (huAdj (f x) (hs x hxy.symm)).symm
          · simp only [if_neg hx,if_neg hy]
            exact f.map_adj hxy }
    have hg : Function.Injective g := by
      intro x y he
      change (if x = a then u else f x) = (if y = a then u else f y) at he
      by_cases hx : x = a
      · by_cases hy : y = a
        · exact hx.trans hy.symm
        · simp only [if_pos hx,if_neg hy] at he
          exact (huI (he ▸ hmem y hy)).elim
      · by_cases hy : y = a
        · simp only [if_neg hx,if_pos hy] at he
          exact (huI (he ▸ hmem x hx)).elim
        · simp only [if_neg hx,if_neg hy] at he
          rcases hfiber x y he with hh | ⟨hxa,hyb⟩ | ⟨hxb,hya⟩
          · exact hh
          · exact (hx hxa).elim
          · exact (hy hya).elim
    exact hfree ⟨⟨g,hg⟩⟩
  calc
    _ ≤ I.card := card_le_card hsubset
    _ ≤ (univ.erase a).card := card_image_le
    _ = Fintype.card W - 1 := by simp

open scoped Classical in
/-- Counting occurrences of supports at roots. Disjointness within each
packing is not required for this multiplicity bound. -/
lemma support_occurrences_le [Fintype W] [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} (hfree : H.Free G)
    (F : V → Finset (Finset V))
    (hF : ∀ v A, A ∈ F v → SmallSupport H G v A) :
    ∑ v, (F v).card ≤ (Fintype.card W-1)*(univ.biUnion F).card := by
  classical
  let U := univ.biUnion F
  have hRoots (A : Finset V) (hAU : A ∈ U) :
      (univ.filter (fun v => A ∈ F v)).card ≤ Fintype.card W-1 := by
    obtain ⟨v,hv,hAv⟩ := mem_biUnion.mp hAU
    have hBound := (hF v A hAv).2.2.2.common_neighbors_le hfree
    apply le_trans (card_le_card ?_) hBound
    intro w hw
    exact mem_filter.mpr ⟨mem_univ w,(hF w A (mem_filter.mp hw).2).2.1⟩
  have hCount : ∑ v, (F v).card = ∑ A ∈ U, (univ.filter (fun v => A ∈ F v)).card := by
    calc
      ∑ v, (F v).card = ∑ v, ∑ A ∈ U, (if A ∈ F v then 1 else 0 : ℕ) := by
        apply sum_congr rfl
        intro v hv
        have hSub : F v ⊆ U := fun A hA => mem_biUnion.mpr ⟨v,mem_univ v,hA⟩
        rw [← sum_filter]
        simp only [sum_const,smul_eq_mul,mul_one]
        congr 1
        ext A
        simp only [mem_filter]
        exact ⟨fun hA => ⟨hSub hA,hA⟩,fun hA => hA.2⟩
      _ = ∑ A ∈ U, ∑ v, (if A ∈ F v then 1 else 0 : ℕ) := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro A hA
        rw [← sum_filter]
        simp
  rw [hCount]
  calc
    _ ≤ ∑ _A ∈ U, (Fintype.card W-1) := sum_le_sum hRoots
    _ = _ := by simp [U,Nat.mul_comm]

#print axioms SupportedFold.common_neighbors_le
#print axioms support_occurrences_le
end Erdos713PartialCloning
