import Submission.RingChords

/-! A shortest strong contact ring has only its prescribed singleton intersections. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open RingIndices
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}

/-- The only intersections are the designated junctions of consecutive pieces. -/
def Ring.Clean (R : Ring G n) : Prop :=
  ∀ i j, i ≠ j → ∀ x, x ∈ (R.piece i).verts → x ∈ (R.piece j).verts →
    (j = i+1 ∧ x = R.vertex j) ∨ (i = j+1 ∧ x = R.vertex i)

lemma Ring.no_chord (R : Ring G n)
    (hsmall : ∀ m < n, ¬ Nonempty (Ring G m))
    (hadj : ∀ i x, x ∈ (R.piece i).verts → x ∈ (R.piece (i+1)).verts → x = R.vertex (i+1))
    (i j : Fin (n+3)) (hij : i ≠ j) (hnext : j ≠ i+1) (hprev : i ≠ j+1)
    (x : V) (hxi : x ∈ (R.piece i).verts) (hxj : x ∈ (R.piece j).verts) : False := by
  let T := R.rotate i
  let q : Fin (n+3) := j-i
  have hqi : q+i = j := sub_add_cancel j i
  have hq0 : q ≠ 0 := by
    intro he
    rw [he,zero_add] at hqi
    exact hij hqi
  have hq1 : q ≠ 1 := by
    intro he
    rw [he,add_comm 1 i] at hqi
    exact hnext hqi.symm
  have hqnext : q+1 ≠ 0 := by
    intro he
    apply hprev
    calc
      i = (q+1)+i := by rw [he,zero_add]
      _ = j+1 := by rw [add_right_comm,hqi]
  have hqbound : q.val+1 < n+3 := by
    by_contra hn
    apply hqnext
    apply Fin.ext
    simp only [Fin.val_add_eq_ite,Fin.val_one,Fin.val_zero]
    split_ifs <;> omega
  have hx0 : x ∈ (T.piece 0).verts := by simpa only [T,Ring.rotate,zero_add] using hxi
  have hxq : x ∈ (T.piece q).verts := by simpa only [T,Ring.rotate,hqi] using hxj
  have hxnot1 : x ∉ (T.piece 1).verts := by
    intro hx1
    have hx1' : x ∈ (R.piece (i+1)).verts := by simpa only [T,Ring.rotate,add_comm 1 i] using hx1
    have he := hadj i x hxi hx1'
    have heT : x = T.vertex 1 := by simpa only [T,Ring.rotate,add_comm 1 i] using he
    rw [heT] at hxq
    rcases (T.incidence 1 q).mp hxq with he | he
    · exact hq1 he.symm
    · have he' : q+1 = 0+1 := by simpa using he.symm
      exact hq0 (add_right_cancel he')
  let S : Finset (Fin (n+3)) := Finset.univ.filter (fun k => k ≠ 0 ∧ x ∈ (T.piece k).verts)
  have hqS : q ∈ S := by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hq0,hxq⟩
  have hSne : S.Nonempty := ⟨q,hqS⟩
  let k := S.min' hSne
  have hkS : k ∈ S := Finset.min'_mem _ _
  have hk : k ≠ 0 ∧ x ∈ (T.piece k).verts := (Finset.mem_filter.mp hkS).2
  have hkq : k ≤ q := Finset.min'_le S q hqS
  have hk1 : k ≠ 1 := fun he => hxnot1 (he ▸ hk.2)
  have hk0v : k.val ≠ 0 := by simpa using hk.1
  have hk1v : k.val ≠ 1 := by
    intro he
    apply hk1
    exact Fin.ext (by simpa using he)
  have hkqv : k.val ≤ q.val := hkq
  have hk2 : 2 ≤ k.val := by omega
  let m := k.val-2
  have hm : m+3 < n+3 := by dsimp [m]; omega
  have heend : initial hm (Fin.last (m+2)) = k := by
    apply Fin.ext
    simp only [initial,Fin.val_castLE,Fin.val_last]
    dsimp [m]
    omega
  have hwend : x ∈ (T.piece (initial hm (Fin.last (m+2)))).verts := by rw [heend]; exact hk.2
  have havoid (l : Fin (m+3)) (hl0 : 0 < l.val) (hle : l.val < m+2) :
      x ∉ (T.piece (initial hm l)).verts := by
    intro hxl
    have hlne : initial hm l ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      simp only [initial,Fin.val_castLE,Fin.val_zero] at hv
      omega
    have hlS : initial hm l ∈ S := by
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hlne,hxl⟩
    have hkle : k.val ≤ l.val := Finset.min'_le S (initial hm l) hlS
    dsimp [m] at hle
    omega
  exact hsmall m (by dsimp [m]; omega) (T.shorten_chord hm hx0 hwend havoid)

lemma Ring.clean_of_no_shorter (R : Ring G n)
    (hsmall : ∀ m < n, ¬ Nonempty (Ring G m))
    (hadj : ∀ i x, x ∈ (R.piece i).verts → x ∈ (R.piece (i+1)).verts → x = R.vertex (i+1)) : R.Clean := by
  intro i j hij x hxi hxj
  by_cases hn : j = i+1
  · subst j
    exact Or.inl ⟨rfl,hadj i x hxi hxj⟩
  by_cases hp : i = j+1
  · subst i
    exact Or.inr ⟨rfl,hadj j x hxj hxi⟩
  exact (R.no_chord hsmall hadj i j hij hn hp x hxi hxj).elim

#print axioms Ring.no_chord
#print axioms Ring.clean_of_no_shorter
end Erdos184Work.CycleRings
