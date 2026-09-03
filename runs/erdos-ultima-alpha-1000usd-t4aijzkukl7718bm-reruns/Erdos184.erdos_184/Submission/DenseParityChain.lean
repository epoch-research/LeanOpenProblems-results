import Submission.ParitySupportChargeObstruction

/-!
Dense chains show that increasing a fixed coefficient on odd vertices does
not repair the parity/support-loss charge. This is an auxiliary obstruction,
not a disproof of the cycle decomposition conjecture.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.DenseParityChain
open ParitySupportChargeObstruction
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

abbrev Port (q : ℕ) := Bool ⊕ Fin q
abbrev Vert (q L : ℕ) := Fin (L+1) × Port q

def block (q : ℕ) : SimpleGraph (Port q) where
  Adj x y := match x, y with
    | .inl _, .inl _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr a, .inr b => a ≠ b
  symm := by intro x y; cases x <;> cases y <;> simp_all [ne_comm]
  loopless := by intro x; cases x <;> simp

def inside (q L : ℕ) : SimpleGraph (Vert q L) where
  Adj x y := x.1 = y.1 ∧ (block q).Adj x.2 y.2
  symm := by rintro x y ⟨h,hb⟩; exact ⟨h.symm,hb.symm⟩
  loopless := by rintro x ⟨_,h⟩; exact (block q).loopless x.2 h

def bridges (q L : ℕ) : SimpleGraph (Vert q L) where
  Adj x y := match x.2, y.2 with
    | .inl true, .inl false => x.1.val+1 = y.1.val
    | .inl false, .inl true => y.1.val+1 = x.1.val
    | _, _ => False
  symm := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    cases x with
    | inl x => cases y with
      | inl y => cases x <;> cases y <;> simp
      | inr y => simp
    | inr x => cases y <;> simp
  loopless := by
    rintro ⟨i,x⟩
    cases x with
    | inl x => cases x <;> simp
    | inr x => simp

abbrev graph (q L : ℕ) := inside q L ⊔ bridges q L

lemma block_degree_port (q : ℕ) (b : Bool) : (block q).degree (.inl b) = q := by
  have hn : (block q).neighborFinset (.inl b) =
      Finset.univ.map (Function.Embedding.inr : Fin q ↪ Port q) := by
    ext x
    cases x <;> simp [block]
  rw [degree,hn,Finset.card_map]
  simp

lemma block_degree_core (q : ℕ) (a : Fin q) : (block q).degree (.inr a) = q+1 := by
  have hn : (block q).neighborFinset (.inr a) = Finset.univ.erase (.inr a) := by
    ext x
    cases x <;> simp [block,ne_comm]
  rw [degree,hn,Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Nat.add_comm]

lemma inside_degree (q L : ℕ) (i : Fin (L+1)) (x : Port q) :
    (inside q L).degree (i,x) = (block q).degree x := by
  let e : Port q ↪ Vert q L := ⟨fun y => (i,y), fun _ _ h => Prod.mk.inj h |>.2⟩
  have hn : (inside q L).neighborFinset (i,x) = ((block q).neighborFinset x).map e := by
    ext v
    rcases v with ⟨j,y⟩
    simp only [mem_neighborFinset,Finset.mem_map]
    constructor
    · rintro ⟨hij,hxy⟩
      exact ⟨y,hxy,by simpa [e,hij]⟩
    · rintro ⟨z,hxz,hz⟩
      have hp : i=j ∧ z=y := Prod.mk.inj hz
      exact ⟨hp.1,hp.2 ▸ hxz⟩
  rw [degree,hn,Finset.card_map]
  exact card_neighborFinset_eq_degree _ _

lemma bridges_degree_left (q L : ℕ) (i : Fin (L+1)) :
    (bridges q L).degree (i,.inl false) = if i.val=0 then 0 else 1 := by
  by_cases hi : i.val=0
  · have hn : (bridges q L).neighborFinset (i,.inl false) = ∅ := by
      ext v
      rcases v with ⟨j,y⟩
      cases y with
      | inl y => cases y <;> simp [bridges,hi]
      | inr y => simp [bridges]
    rw [degree,hn]
    simp [hi]
  · let j : Fin (L+1) := ⟨i.val-1,by omega⟩
    have hn : (bridges q L).neighborFinset (i,.inl false) = {(j,.inl true)} := by
      ext v
      rcases v with ⟨k,y⟩
      cases y with
      | inl y =>
        cases y
        · simp [bridges]
        · simp only [mem_neighborFinset,bridges,Finset.mem_singleton,Prod.mk.injEq,and_true]
          rw [Fin.ext_iff]
          dsimp [j]
          omega
      | inr y => simp [bridges]
    rw [degree,hn]
    simp [hi]

lemma bridges_degree_right (q L : ℕ) (i : Fin (L+1)) :
    (bridges q L).degree (i,.inl true) = if i.val=L then 0 else 1 := by
  by_cases hi : i.val=L
  · have hn : (bridges q L).neighborFinset (i,.inl true) = ∅ := by
      ext v
      rcases v with ⟨j,y⟩
      cases y with
      | inl y =>
        cases y
        · simp only [mem_neighborFinset,bridges,Finset.notMem_empty,iff_false]
          have hj := j.isLt
          omega
        · simp [bridges]
      | inr y => simp [bridges]
    rw [degree,hn]
    simp [hi]
  · let j : Fin (L+1) := ⟨i.val+1,by omega⟩
    have hn : (bridges q L).neighborFinset (i,.inl true) = {(j,.inl false)} := by
      ext v
      rcases v with ⟨k,y⟩
      cases y with
      | inl y =>
        cases y
        · simp only [mem_neighborFinset,bridges,Finset.mem_singleton,Prod.mk.injEq,and_true]
          rw [Fin.ext_iff]
          dsimp [j]
          omega
        · simp [bridges]
      | inr y => simp [bridges]
    rw [degree,hn]
    simp [hi]

lemma bridges_degree_core (q L : ℕ) (i : Fin (L+1)) (a : Fin q) :
    (bridges q L).degree (i,.inr a) = 0 := by
  have hn : (bridges q L).neighborFinset (i,.inr a) = ∅ := by
    ext v
    rcases v with ⟨j,y⟩
    cases y <;> simp [bridges]
  rw [degree,hn]
  simp

lemma sdiff_inside (q L : ℕ) : graph q L \ inside q L = bridges q L := by
  ext x y
  rcases x with ⟨i,x⟩
  rcases y with ⟨j,y⟩
  cases x with
  | inl x => cases y with
    | inl y => cases x <;> cases y <;> simp [graph,inside,bridges,block]
    | inr y => simp [graph,inside,bridges,block]
  | inr x => cases y <;> simp [graph,inside,bridges,block]

lemma degree_add (q L : ℕ) (v : Vert q L) :
    (bridges q L).degree v + (inside q L).degree v = (graph q L).degree v := by
  have h := complement_degree_add (show inside q L ≤ graph q L from le_sup_left) v
  simpa only [sdiff_inside,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h

lemma graph_min_degree (q L : ℕ) (v : Vert q L) : q ≤ (graph q L).degree v := by
  rcases v with ⟨i,x⟩
  have h := degree_add q L (i,x)
  rw [inside_degree] at h
  cases x with
  | inl b => rw [block_degree_port] at h; omega
  | inr a => rw [block_degree_core] at h; omega

lemma graph_odd_card (C L : ℕ) : (oddVertices (graph (4*C+3) L)).card = 2 := by
  let u : Vert (4*C+3) L := (0,.inl false)
  let v : Vert (4*C+3) L := (Fin.last L,.inl true)
  have hn : oddVertices (graph (4*C+3) L) = {u,v} := by
    ext x
    rcases x with ⟨i,x⟩
    have h := degree_add (4*C+3) L (i,x)
    rw [inside_degree] at h
    cases x with
    | inl b =>
      rw [block_degree_port] at h
      cases b
      · rw [bridges_degree_left] at h
        simp only [oddVertices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
          Finset.mem_singleton,u,v,Prod.mk.injEq,Sum.inl.injEq,Bool.false_eq_true,
          eq_self,and_false,or_false,and_true,Fin.ext_iff,
          Fin.val_zero,Fin.val_last,Nat.odd_iff]
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
        split_ifs at h <;> omega
      · rw [bridges_degree_right] at h
        simp only [oddVertices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
          Finset.mem_singleton,u,v,Prod.mk.injEq,Sum.inl.injEq,Bool.true_eq_false,
          eq_self,and_false,false_or,and_true,Fin.ext_iff,
          Fin.val_zero,Fin.val_last,Nat.odd_iff]
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
        split_ifs at h <;> omega
    | inr a =>
      rw [block_degree_core,bridges_degree_core] at h
      simp [oddVertices,u,v,Nat.odd_iff]
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
      omega
  rw [hn,Finset.card_pair]
  simp [u,v]

/-- The edges crossing a two-colouring. -/
def cut {V : Type*} (G : SimpleGraph V) (f : V → Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ f x ≠ f y
  symm := by rintro x y ⟨h,hf⟩; exact ⟨h.symm,hf.symm⟩
  loopless := by rintro x ⟨_,h⟩; exact h rfl

lemma cut_column {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → Bool)
    (e : Sym2 V) :
    (∑ x ∈ Finset.univ.filter (fun x => f x=true), G.incMatrix (ZMod 2) x e) =
      if e ∈ (cut G f).edgeSet then 1 else 0 := by
  induction e using Sym2.ind with
  | h u v =>
    by_cases h : G.Adj u v
    · have hc (x : V) : G.incMatrix (ZMod 2) x s(u,v) =
          (if x=u then 1 else 0) + (if x=v then 1 else 0) := by
        by_cases hu : x=u
        · subst x
          simp [incMatrix_apply',h,h.ne]
        · by_cases hv : x=v
          · subst x
            simp [incMatrix_apply',mk'_mem_incidenceSet_iff,h,h.ne.symm]
          · simp [incMatrix_apply',mk'_mem_incidenceSet_iff,h,hu,hv]
      simp_rw [hc]
      rw [Finset.sum_add_distrib]
      cases hu : f u <;> cases hv : f v <;>
        simp [cut,h,hu,hv,CharTwo.add_self_eq_zero]
    · have hz (x : V) : G.incMatrix (ZMod 2) x s(u,v) = 0 := by
        apply incMatrix_of_notMem_incidenceSet
        intro he
        exact h he.1
      simp [hz,cut,h]

lemma cut_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (f : V → Bool) :
    Even (cut G f).edgeSet.ncard := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hh : (∑ e : Sym2 V, if e ∈ (cut G f).edgeSet then (1:ZMod 2) else 0) =
      ((cut G f).edgeSet.ncard : ZMod 2) := by
    rw [Finset.sum_boole]
    congr 1
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    simp
  rw [← hh]
  simp_rw [← cut_column G f]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  rw [sum_incMatrix_apply G]
  exact ZMod.natCast_eq_zero_iff_even.mpr (he v)

lemma no_unique_crossing {V : Type*} [Fintype V] {G A : SimpleGraph V}
    (hA : A ≤ G) (he : ∀ v, Even (A.degree v)) (f : V → Bool) {u v : V}
    (hf : f u ≠ f v)
    (honly : ∀ x y, G.Adj x y → f x ≠ f y → s(x,y)=s(u,v)) :
    ¬ A.Adj u v := by
  intro huv
  have heq : (cut A f).edgeSet = {s(u,v)} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨huv,hf⟩,?_⟩
    intro e he
    induction e using Sym2.ind with
    | h x y => exact honly x y (hA he.1) he.2
  have hh := cut_even A he f
  rw [heq,Set.ncard_singleton] at hh
  norm_num at hh

def joinEdge (q L : ℕ) (i : Fin L) : Sym2 (Vert q L) :=
  s((i.castSucc,Sum.inl true),(i.succ,Sum.inl false))

lemma cross_prefix {q L : ℕ} (i : Fin L) {x y : Vert q L}
    (hxy : (graph q L).Adj x y) (hx : x.1.val ≤ i.val) (hy : i.val < y.1.val) :
    x=(i.castSucc,.inl true) ∧ y=(i.succ,.inl false) := by
  rcases x with ⟨j,x⟩
  rcases y with ⟨k,y⟩
  rcases hxy with hxy | hxy
  · have hjk := congrArg Fin.val hxy.1
    dsimp at hx hy hjk
    omega
  · cases x with
    | inl x => cases y with
      | inl y =>
        cases x <;> cases y <;> simp only [bridges] at hxy
        · dsimp at hx hy hxy
          omega
        · have hj : j=i.castSucc := by apply Fin.ext; dsimp at *; omega
          have hk : k=i.succ := by apply Fin.ext; dsimp at *; omega
          exact ⟨by rw [hj],by rw [hk]⟩
      | inr y => cases x <;> exact False.elim hxy
    | inr x => cases y <;> exact False.elim hxy

lemma joining_edge_omitted {q L : ℕ} (A : SimpleGraph (Vert q L))
    (hA : A ≤ graph q L) (he : ∀ v, Even (A.degree v)) (i : Fin L) :
    joinEdge q L i ∉ A.edgeSet := by
  let f : Vert q L → Bool := fun x => decide (x.1.val ≤ i.val)
  apply no_unique_crossing hA he f
  · simp [f]
  · intro x y hxy hdiff
    by_cases hx : x.1.val ≤ i.val
    · have hy : i.val < y.1.val := by
        by_contra! hy
        exact hdiff (by simp [f,hx,hy])
      obtain ⟨rfl,rfl⟩ := cross_prefix i hxy hx hy
      rfl
    · have hy : y.1.val ≤ i.val := by
        by_contra hy
        exact hdiff (by simp [f,hx,hy])
      obtain ⟨rfl,rfl⟩ := cross_prefix i hxy.symm hy (by omega)
      exact Sym2.eq_swap

lemma joinEdge_injective (q L : ℕ) : Function.Injective (joinEdge q L) := by
  intro i j hij
  rw [joinEdge,joinEdge,Sym2.eq_iff] at hij
  rcases hij with ⟨h,_⟩ | ⟨h,_⟩
  · exact Fin.castSucc_injective _ (Prod.mk.inj h).1
  · have hh := (Prod.mk.inj h).2
    cases hh

lemma removed_edges_lower {q L : ℕ} (A : SimpleGraph (Vert q L))
    (hA : A ≤ graph q L) (he : ∀ v, Even (A.degree v)) :
    L ≤ ((graph q L) \ A).edgeSet.ncard := by
  have hsub : Set.range (joinEdge q L) ⊆ ((graph q L) \ A).edgeSet := by
    rintro e ⟨i,rfl⟩
    refine ⟨Or.inr ?_,joining_edge_omitted A hA he i⟩
    simp [bridges]
  have hh := Set.ncard_le_ncard hsub
  have hc : (Set.range (joinEdge q L)).ncard = L := by
    rw [← Set.image_univ,Set.ncard_image_of_injective _ (joinEdge_injective q L)]
    simp
  rwa [hc] at hh

/-- Neither coefficient can be repaired by choosing a larger fixed value.
The restriction may delete arbitrary additional cycles. -/
theorem charge_failure (a C : ℕ) (A : SimpleGraph (Vert (4*C+3) (4*a+1)))
    (hA : A ≤ graph (4*C+3) (4*a+1)) (he : ∀ v, Even (A.degree v)) :
    a*(oddVertices (graph (4*C+3) (4*a+1))).card +
        C*((graph (4*C+3) (4*a+1)).support \ A.support).ncard <
      ((graph (4*C+3) (4*a+1)) \ A).edgeSet.ncard := by
  have hl := removed_edges_lower A hA he
  have hs := lost_support_incidence_bound hA (4*C+3)
    (fun v _ => by
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using graph_min_degree (4*C+3) (4*a+1) v)
  rw [graph_odd_card]
  by_contra! hb
  have hmul := Nat.mul_le_mul_left (4*C+3) hb
  have hinc := Nat.mul_le_mul_left C hs
  have hlow := Nat.mul_le_mul_left (2*C+3) hl
  nlinarith

/-- This is a negation of an auxiliary parity-repair assertion, NOT the
negation of Erdős 184. -/
theorem no_fixed_odd_support_charge :
    ¬ ∃ a C : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      ∃ A : SimpleGraph V, A ≤ G ∧ (∀ v, Even (A.degree v)) ∧
        (G \ A).edgeSet.ncard ≤ a*(oddVertices G).card +
          C*(G.support \ A.support).ncard := by
  rintro ⟨a,C,h⟩
  obtain ⟨A,hA,he,hb⟩ := h (graph (4*C+3) (4*a+1))
  exact (charge_failure a C A hA he).not_ge hb

lemma block_reachable (q : ℕ) (hq : 0<q) (x y : Port q) : (block q).Reachable x y := by
  let z : Port q := .inr ⟨0,hq⟩
  have hz (w : Port q) : (block q).Reachable w z := by
    by_cases hw : w=z
    · exact hw ▸ Reachable.refl w
    · apply Adj.reachable
      cases w with
      | inl w => trivial
      | inr w => exact fun h => hw (congrArg Sum.inr h)
  exact (hz x).trans (hz y).symm

lemma within_reachable (q L : ℕ) (hq : 0<q) (i : Fin (L+1)) (x y : Port q) :
    (graph q L).Reachable (i,x) (i,y) := by
  let f : block q →g graph q L := {
    toFun := fun x => (i,x)
    map_rel' := fun h => Or.inl ⟨rfl,h⟩ }
  exact (block_reachable q hq x y).map f

lemma graph_connected (q L : ℕ) (hq : 0<q) : (graph q L).Connected := by
  let u : Vert q L := (0,.inl false)
  have hr (i : Fin (L+1)) : (graph q L).Reachable u (i,.inl false) := by
    induction i using Fin.induction with
    | zero => exact Reachable.refl _
    | succ i ih =>
      have hj : (graph q L).Adj (i.castSucc,.inl true) (i.succ,.inl false) := by
        exact Or.inr (by simp [bridges])
      exact (ih.trans (within_reachable q L hq i.castSucc _ _)).trans hj.reachable
  have ha (x : Vert q L) : (graph q L).Reachable u x :=
    (hr x.1).trans (within_reachable q L hq x.1 _ x.2)
  haveI : Nonempty (Vert q L) := ⟨u⟩
  exact ⟨fun x y => (ha x).symm.trans (ha y)⟩

/-- The obstruction persists at arbitrarily large minimum degree, on
connected graphs with exactly two odd vertices. -/
theorem exists_dense_connected_failure (a C d : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧ (∀ v, d ≤ G.degree v) ∧ (oddVertices G).card=2 ∧
      ∀ A : SimpleGraph V, A ≤ G → (∀ v, Even (A.degree v)) →
        a*(oddVertices G).card + C*(G.support \ A.support).ncard <
          (G \ A).edgeSet.ncard := by
  let q := 4*(C+d)+3
  let L := 4*a+1
  refine ⟨Vert q L,inferInstance,graph q L,graph_connected q L (by dsimp [q]; omega),?_,
    graph_odd_card (C+d) L,?_⟩
  · intro v
    have hh := graph_min_degree q L v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh ⊢
    dsimp [q] at hh ⊢
    omega
  · intro A hA he
    have hh := charge_failure a (C+d) A hA (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v)
    have hmul := Nat.mul_le_mul_right ((graph q L).support \ A.support).ncard
      (Nat.le_add_right C d)
    exact lt_of_le_of_lt (Nat.add_le_add_left hmul _) hh

end Erdos184.DenseParityChain
