import FormalConjecturesUtil

/-! An oriented partial-cloning operation cannot create an eight-cycle over a
forest. This is a finite preservation result, not a rationality proof. -/
open SimpleGraph
namespace Erdos713OrientedCloneC8
set_option maxHeartbeats 2000000

variable {V : Type*}

def graph {W : Type*} (G : SimpleGraph V) (P : W → V → Prop) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr u, .inl v => P u v
    | .inl u, .inr v => P v u
    | .inr _, .inr _ => False
  symm := by rintro (u|u) (v|v) h <;> first | exact h | exact h.symm
  loopless := by rintro (u|u) h; exact G.loopless u h; exact h

def root : V ⊕ V → V := Sum.elim id id

lemma adj_root {G : SimpleGraph V} {P : V → V → Prop}
    (hP : ∀ u v, P u v → G.Adj u v) {x y : V ⊕ V}
    (h : (graph G P).Adj x y) : G.Adj (root x) (root y) := by
  rcases x with x|x <;> rcases y with y|y
  · exact h
  · exact (hP _ _ h).symm
  · exact hP _ _ h
  · exact h.elim

lemma three_same_root {x y z : V ⊕ V}
    (hxy : root x = root y) (hyz : root y = root z) :
    x = y ∨ y = z ∨ x = z := by
  rcases x with x|x <;> rcases y with y|y <;> rcases z with z|z <;>
    simp_all [root]

/-- Asymmetry of P deletes the two disjoint mixed edges over each base edge.
Consequently, lifted edges with the same projection always meet. -/
lemma same_edge_meets {G : SimpleGraph V} {P : V → V → Prop}
    (hP : ∀ u v, P u v → ¬ P v u) {x y z w : V ⊕ V}
    (hxy : (graph G P).Adj x y) (hzw : (graph G P).Adj z w)
    (he : s(root x,root y) = s(root z,root w)) :
    x = z ∨ x = w ∨ y = z ∨ y = w := by
  rcases x with x|x <;> rcases y with y|y <;>
    rcases z with z|z <;> rcases w with w|w
  all_goals simp only [graph] at hxy hzw
  all_goals simp only [root,Sum.elim_inl,Sum.elim_inr,id_eq,Sym2.eq_iff] at he
  all_goals rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals try simp
  all_goals exact (hP _ _ hxy hzw).elim

lemma forest_edge_repeats {G : SimpleGraph V} (hG : G.IsAcyclic)
    (f : Fin 8 → V) (hf : ∀ i, G.Adj (f i) (f (i+1))) :
    s(f 0,f 1) = s(f 1,f 2) ∨ s(f 0,f 1) = s(f 2,f 3) ∨
    s(f 0,f 1) = s(f 3,f 4) ∨ s(f 0,f 1) = s(f 4,f 5) ∨
    s(f 0,f 1) = s(f 5,f 6) ∨ s(f 0,f 1) = s(f 6,f 7) ∨
    s(f 0,f 1) = s(f 7,f 0) := by
  let p : G.Walk (f 1) (f 0) :=
    .cons (hf 1) (.cons (hf 2) (.cons (hf 3) (.cons (hf 4)
      (.cons (hf 5) (.cons (hf 6) (.cons (hf 7) .nil))))))
  have hb := (isAcyclic_iff_forall_adj_isBridge.mp hG) (hf 0)
  have hm := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hb).2 p.reverse
  simpa only [Walk.edges_reverse,List.mem_reverse,p,Walk.edges_cons,Walk.edges_nil,
    List.mem_cons,List.not_mem_nil,or_false] using hm

lemma backtrack_zero {G : SimpleGraph V} {P : V → V → Prop}
    (hG : G.IsAcyclic) (hP : ∀ u v, P u v → G.Adj u v)
    (hPA : ∀ u v, P u v → ¬ P v u) (f : Fin 8 → V ⊕ V)
    (hinj : Function.Injective f) (hf : ∀ i, (graph G P).Adj (f i) (f (i+1))) :
    root (f 0) = root (f 2) ∨ root (f 7) = root (f 1) := by
  have hr (i : Fin 8) := adj_root hP (hf i)
  have hh := forest_edge_repeats hG (fun i => root (f i)) hr
  have hdis (i : Fin 8) (h0 : i ≠ 0) (h1 : i ≠ 1) (h7 : i ≠ 7) :
      s(root (f 0),root (f 1)) ≠ s(root (f i),root (f (i+1))) := by
    intro he
    have hm := same_edge_meets hPA (hf 0) (hf i) he
    simp only [hinj.eq_iff] at hm
    rcases hm with hm|hm|hm|hm
    · exact h0 hm.symm
    · have : i = 7 := by revert hm; fin_cases i <;> decide
      exact h7 this
    · exact h1 hm.symm
    · have : i = 0 := by revert hm; fin_cases i <;> decide
      exact h0 this
  rcases hh with hh|hh|hh|hh|hh|hh|hh
  · rcases Sym2.eq_iff.mp hh with hh|hh
    · exact ((hr 0).ne hh.1).elim
    · exact Or.inl hh.1
  · exact (hdis 2 (by decide) (by decide) (by decide) hh).elim
  · exact (hdis 3 (by decide) (by decide) (by decide) hh).elim
  · exact (hdis 4 (by decide) (by decide) (by decide) hh).elim
  · exact (hdis 5 (by decide) (by decide) (by decide) hh).elim
  · exact (hdis 6 (by decide) (by decide) (by decide) hh).elim
  · rcases Sym2.eq_iff.mp hh with hh|hh
    · exact ((hr 0).ne hh.2.symm).elim
    · exact Or.inr hh.2.symm

/-- No injective octagon in the oriented lift of a forest. -/
theorem no_octagon_of_acyclic {G : SimpleGraph V} {P : V → V → Prop}
    (hG : G.IsAcyclic) (hP : ∀ u v, P u v → G.Adj u v)
    (hPA : ∀ u v, P u v → ¬ P v u) (f : Fin 8 → V ⊕ V)
    (hinj : Function.Injective f) (hf : ∀ i, (graph G P).Adj (f i) (f (i+1))) : False := by
  have hb (a : Fin 8) :
      root (f a) = root (f (a+2)) ∨ root (f (a+7)) = root (f (a+1)) := by
    have hi : Function.Injective (fun i : Fin 8 => f (a+i)) :=
      hinj.comp (add_right_injective a)
    simpa only [add_zero,add_assoc] using
      backtrack_zero hG hP hPA (fun i => f (a+i)) hi (fun i => by
        simpa only [add_assoc] using hf (a+i))
  have htri (i j k : Fin 8) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (hij' : root (f i) = root (f j)) (hjk' : root (f j) = root (f k)) : False := by
    have hh := three_same_root hij' hjk'
    simp only [hinj.eq_iff] at hh
    exact hh.elim hij (fun hh => hh.elim hjk hik)
  have hdis (i : Fin 8) (h0 : i ≠ 0) (h1 : i ≠ 1) (h7 : i ≠ 7)
      (he : s(root (f 0),root (f 1)) = s(root (f i),root (f (i+1)))) : False := by
    have hm := same_edge_meets hPA (hf 0) (hf i) he
    simp only [hinj.eq_iff] at hm
    rcases hm with hm|hm|hm|hm
    · exact h0 hm.symm
    · have : i = 7 := by revert hm; fin_cases i <;> decide
      exact h7 this
    · exact h1 hm.symm
    · have : i = 0 := by revert hm; fin_cases i <;> decide
      exact h0 this
  rcases hb 0 with h02|h71
  · rcases hb 2 with h24|h13
    · exact htri 0 2 4 (by decide) (by decide) (by decide) h02 h24
    · exact hdis 2 (by decide) (by decide) (by decide)
        (Sym2.eq_iff.mpr (Or.inl ⟨h02,h13⟩))
  · rcases hb 6 with h60|h57
    · exact hdis 6 (by decide) (by decide) (by decide)
        (Sym2.eq_iff.mpr (Or.inl ⟨h60.symm,h71.symm⟩))
    · exact htri 5 7 1 (by decide) (by decide) (by decide) h57 h71

/-- The girth hypothesis is needed only on the at most eight projected vertices. -/
theorem no_octagon_of_small_acyclic {G : SimpleGraph V} {P : V → V → Prop}
    (hG : ∀ S : Finset V, S.card ≤ 8 → (G.induce (S : Set V)).IsAcyclic)
    (hP : ∀ u v, P u v → G.Adj u v) (hPA : ∀ u v, P u v → ¬ P v u)
    (f : Fin 8 → V ⊕ V) (hinj : Function.Injective f)
    (hf : ∀ i, (graph G P).Adj (f i) (f (i+1))) : False := by
  classical
  let S : Finset V := Finset.univ.image (fun i => root (f i))
  have hs (i : Fin 8) : root (f i) ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  let incl : S ⊕ S → V ⊕ V := Sum.map Subtype.val Subtype.val
  let lift : (z : V ⊕ V) → root z ∈ S → S ⊕ S
    | .inl v, h => .inl ⟨v,h⟩
    | .inr v, h => .inr ⟨v,h⟩
  have hl (z : V ⊕ V) (hz : root z ∈ S) : incl (lift z hz) = z := by
    rcases z with z|z <;> rfl
  let Q : S → S → Prop := fun u v => P u.val v.val
  let g : Fin 8 → S ⊕ S := fun i => lift (f i) (hs i)
  have hg : Function.Injective g := by
    intro i j hij
    apply hinj
    simpa only [g,hl] using congrArg incl hij
  have hmap (x y : S ⊕ S) :
      (graph (G.induce (S : Set V)) Q).Adj x y ↔
      (graph G P).Adj (incl x) (incl y) := by
    rcases x with x|x <;> rcases y with y|y <;> rfl
  apply no_octagon_of_acyclic (hG S (by
    exact (Finset.card_image_le).trans (by simp))) (fun u v h => hP _ _ h)
    (fun u v h => hPA _ _ h) g hg
  intro i
  apply (hmap _ _).mpr
  simpa only [g,hl] using hf i

theorem free_of_small_acyclic {G : SimpleGraph V} {P : V → V → Prop}
    (hG : ∀ S : Finset V, S.card ≤ 8 → (G.induce (S : Set V)).IsAcyclic)
    (hP : ∀ u v, P u v → G.Adj u v) (hPA : ∀ u v, P u v → ¬ P v u) :
    (cycleGraph 8).Free (graph G P) := by
  rintro ⟨f⟩
  apply no_octagon_of_small_acyclic hG hP hPA f f.injective
  intro i
  exact f.toHom.map_rel (cycleGraph_adj.mpr (Or.inr (by abel)))

#print axioms no_octagon_of_acyclic
#print axioms free_of_small_acyclic
end Erdos713OrientedCloneC8
