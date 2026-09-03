import Submission.CountThreeOrder

/-! Finite vertex labelings with a prescribed initial neighbor block. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteNeighborLabels
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma exists_labeling (G : SimpleGraph V) (v : V) (n d : ℕ)
    (hn : Fintype.card V = n) (hd : G.degree v = d) :
    ∃ e : Fin n ≃ V, e ⟨0,by have := G.degree_lt_card_verts v; omega⟩ = v ∧
      ∀ i : Fin n, G.Adj v (e i) ↔ 0 < i.val ∧ i.val ≤ d := by
  have hdn : d < n := by have := G.degree_lt_card_verts v; omega
  have hnpos : 0 < n := by omega
  have hnN : Fintype.card (G.neighborSet v) = d := by
    rw [card_neighborSet_eq_degree,hd]
  let N := Fintype.equivFinOfCardEq hnN
  let f : Fin n → V := fun i =>
    if hi : i.val = 0 then v else
    if hi' : i.val ≤ d then (N.symm ⟨i.val-1,by omega⟩).val else v
  let S : Finset (Fin n) := Finset.univ.filter (fun i => i.val ≤ d)
  have hf0 : f ⟨0,hnpos⟩ = v := by simp [f]
  have hfN (i : Fin n) (hi : 0 < i.val) (hid : i.val ≤ d) :
      f i = (N.symm ⟨i.val-1,by omega⟩).val := by
    simp [f,Nat.ne_of_gt hi,hid]
  have hfAdj (i : Fin n) (hi : 0 < i.val) (hid : i.val ≤ d) : G.Adj v (f i) := by
    rw [hfN i hi hid]
    exact (N.symm _).property
  have hinj : Set.InjOn f (S : Set (Fin n)) := by
    intro i hi j hj heq
    have hid : i.val ≤ d := by simpa only [S,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hjd : j.val ≤ d := by simpa only [S,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    by_cases hi0 : i.val = 0
    · have hiv : f i = v := by simp [f,hi0]
      by_cases hj0 : j.val = 0
      · exact Fin.ext (hi0.trans hj0.symm)
      · have hjadj := hfAdj j (by omega) hjd
        rw [← heq,hiv] at hjadj
        exact (G.loopless v hjadj).elim
    by_cases hj0 : j.val = 0
    · have hjv : f j = v := by simp [f,hj0]
      have hiadj := hfAdj i (by omega) hid
      rw [heq,hjv] at hiadj
      exact (G.loopless v hiadj).elim
    have hNi : f i = (N.symm ⟨i.val-1,by omega⟩).val := hfN i (by omega) hid
    have hNj : f j = (N.symm ⟨j.val-1,by omega⟩).val := hfN j (by omega) hjd
    rw [hNi,hNj] at heq
    have hsub := N.symm.injective (Subtype.ext heq)
    have hval := congrArg Fin.val hsub
    simp only [Fin.val_mk] at hval
    exact Fin.ext (by omega)
  obtain ⟨g,hg⟩ := Finset.exists_equiv_extend_of_card_eq
    (α := Fin n) (t := (Finset.univ : Finset V)) (by simp [hn])
    (s := S) (f := f) (Finset.subset_univ _) hinj
  let e : Fin n ≃ V := g.trans (Equiv.subtypeUnivEquiv (fun x : V => Finset.mem_univ x))
  have heS (i : Fin n) (hi : i.val ≤ d) : e i = f i :=
    hg i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  refine ⟨e,(heS ⟨0,hnpos⟩ (by simp)).trans hf0,?_⟩
  intro i
  constructor
  · intro hadj
    let j : Fin n := ⟨(N ⟨e i,hadj⟩).val + 1,by have := (N ⟨e i,hadj⟩).isLt; omega⟩
    have hjpos : 0 < j.val := by dsimp only [j]; omega
    have hjd : j.val ≤ d := by have := (N ⟨e i,hadj⟩).isLt; dsimp only [j]; omega
    have hej : e j = e i := by
      rw [heS j hjd,hfN j hjpos hjd]
      have hj : (⟨j.val-1,by omega⟩ : Fin d) = N ⟨e i,hadj⟩ := by
        apply Fin.ext
        dsimp only [j]
        omega
      rw [hj,N.symm_apply_apply]
    have hji := e.injective hej
    exact hji ▸ ⟨hjpos,hjd⟩
  · rintro ⟨hi,hid⟩
    rw [heS i hid]
    exact hfAdj i hi hid

end Erdos184.FiniteNeighborLabels
