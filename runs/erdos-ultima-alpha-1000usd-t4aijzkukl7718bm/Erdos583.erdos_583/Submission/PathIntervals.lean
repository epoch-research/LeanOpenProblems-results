import Submission.Work

/-! Ordered subintervals of a simple path. -/
namespace Erdos583PathIntervalsDevelopment
open SimpleGraph Erdos583Work
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {a b : V}

def interval (P : G.Walk a b) (i j : ℕ) (hij : i ≤ j) : G.Walk (P.getVert i) (P.getVert j) :=
  ((P.drop i).take (j-i)).copy rfl (by rw [Walk.drop_getVert,Nat.add_sub_of_le hij])

lemma interval_edges_congr (P : G.Walk a b) {i j i' j' : ℕ} (hij : i ≤ j) (hij' : i' ≤ j')
    (hi : i=i') (hj : j=j') :
    (interval P i j hij).toSubgraph.edgeSet=(interval P i' j' hij').toSubgraph.edgeSet := by
  subst i' j'
  rfl

lemma interval_support_congr (P : G.Walk a b) {i j i' j' : ℕ} (hij : i ≤ j) (hij' : i' ≤ j')
    (hi : i=i') (hj : j=j') : (interval P i j hij).support=(interval P i' j' hij').support := by
  subst i' j'
  rfl

lemma interval_length (P : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length) :
    (interval P i j hij).length=j-i := by
  simp only [interval,Walk.length_copy,Walk.take_length,Walk.drop_length]
  omega

lemma interval_getVert (P : G.Walk a b) {i j m : ℕ} (hij : i ≤ j) (hm : m ≤ j-i) :
    (interval P i j hij).getVert m=P.getVert (i+m) := by
  simp only [interval,Walk.getVert_copy,Walk.take_getVert,Walk.drop_getVert,inf_eq_right.mpr hm]

lemma interval_isPath (P : G.Walk a b) (hp : P.IsPath) {i j : ℕ} (hij : i ≤ j) :
    (interval P i j hij).IsPath := by
  have hp' : ((P.take i).append (P.drop i)).IsPath := by simpa using hp
  have hq : (((P.drop i).take (j-i)).append ((P.drop i).drop (j-i))).IsPath := by
    simpa using hp'.of_append_right
  simpa only [interval,Walk.isPath_copy] using hq.of_append_left

lemma interval_support (P : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length) (x : V) :
    x ∈ (interval P i j hij).support ↔ ∃ m, i ≤ m ∧ m ≤ j ∧ x=P.getVert m := by
  rw [Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨m,hx,hm⟩
    rw [interval_length P hij hj] at hm
    rw [interval_getVert P hij hm] at hx
    exact ⟨i+m,by omega,by omega,hx.symm⟩
  · rintro ⟨m,him,hmj,hx⟩
    refine ⟨m-i,?_,?_⟩
    · rw [interval_getVert P hij (by omega),Nat.add_sub_of_le him]
      exact hx.symm
    · rw [interval_length P hij hj]
      omega

lemma interval_core (P : G.Walk a b) (hp : P.IsPath) {i j m : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.length) (hm : m ≤ P.length) :
    P.getVert m ∈ (interval P i j hij).support ↔ i ≤ m ∧ m ≤ j := by
  rw [interval_support P hij hj]
  constructor
  · rintro ⟨l,hil,hlj,he⟩
    have hml := hp.getVert_injOn hm (show l ≤ P.length from hlj.trans hj) he
    omega
  · rintro ⟨him,hmj⟩
    exact ⟨m,him,hmj,rfl⟩

lemma interval_support_inter (P : G.Walk a b) (hp : P.IsPath)
    {i j l m : ℕ} (hij : i ≤ j) (hlm : l ≤ m) (hjm : j ≤ l)
    (hm : m ≤ P.length) {x : V}
    (hx : x ∈ (interval P i j hij).support) (hy : x ∈ (interval P l m hlm).support) :
    j=l ∧ x=P.getVert j := by
  obtain ⟨s,his,hsj,hxs⟩ := (interval_support P hij (by omega) x).mp hx
  obtain ⟨t,hlt,htm,hxt⟩ := (interval_support P hlm hm x).mp hy
  have hst := hp.getVert_injOn (show s ≤ P.length by omega) (show t ≤ P.length by omega) (hxs.symm.trans hxt)
  have hsj' : s=j := by omega
  exact ⟨by omega,hsj' ▸ hxs⟩

lemma interval_edges_disjoint (P : G.Walk a b) (hp : P.IsPath)
    {i j l m : ℕ} (hij : i ≤ j) (hlm : l ≤ m) (hjl : j ≤ l) (hm : m ≤ P.length) :
    Disjoint (interval P i j hij).toSubgraph.edgeSet (interval P l m hlm).toSubgraph.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | h x y =>
    have hx := interval_support_inter P hp hij hlm hjl hm
      (Walk.mem_support_of_adj_toSubgraph he) (Walk.mem_support_of_adj_toSubgraph hf)
    have hy := interval_support_inter P hp hij hlm hjl hm
      (Walk.mem_support_of_adj_toSubgraph ((interval P i j hij).toSubgraph.symm he))
      (Walk.mem_support_of_adj_toSubgraph ((interval P l m hlm).toSubgraph.symm hf))
    have hxy : x=y := hx.2.trans hy.2.symm
    subst y
    exact (interval P i j hij).toSubgraph.loopless x he

lemma edges_positions (P : G.Walk a b) (e : Sym2 V) :
    e ∈ P.edges ↔ ∃ i, i < P.length ∧ e=s(P.getVert i,P.getVert (i+1)) := by
  induction P with
  | nil => simp
  | @cons u v b h Q ih =>
    rw [Walk.edges_cons,List.mem_cons,ih]
    constructor
    · rintro (he|⟨i,hi,he⟩)
      · exact ⟨0,by simp,by simpa using he⟩
      · exact ⟨i+1,by simpa using hi,by simpa using he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact Or.inl (by simpa using he)
      | succ i => exact Or.inr ⟨i,by simpa using hi,by simpa using he⟩

lemma interval_edges (P : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length) (e : Sym2 V) :
    e ∈ (interval P i j hij).toSubgraph.edgeSet ↔
      ∃ m, i ≤ m ∧ m < j ∧ e=s(P.getVert m,P.getVert (m+1)) := by
  rw [Walk.mem_edges_toSubgraph,edges_positions]
  constructor
  · rintro ⟨m,hm,he⟩
    rw [interval_length P hij hj] at hm
    rw [interval_getVert P hij (by omega),interval_getVert P hij (by omega)] at he
    exact ⟨i+m,by omega,by omega,by simpa only [Nat.add_assoc] using he⟩
  · rintro ⟨m,him,hmj,he⟩
    refine ⟨m-i,?_,?_⟩
    · rw [interval_length P hij hj]; omega
    · rw [interval_getVert P hij (by omega),interval_getVert P hij (by omega),Nat.add_sub_of_le him]
      rw [show i+(m-i+1)=m+1 by omega]
      exact he

lemma interval_edges_subset (P : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length) :
    (interval P i j hij).toSubgraph.edgeSet ⊆ P.toSubgraph.edgeSet := by
  intro e he
  obtain ⟨m,him,hmj,he⟩ := (interval_edges P hij hj e).mp he
  exact P.mem_edges_toSubgraph.mpr ((edges_positions P e).mpr ⟨m,by omega,he⟩)

lemma interval_edges_append (P : G.Walk a b) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ P.length) :
    (interval P i j hij).toSubgraph.edgeSet ∪ (interval P j k hjk).toSubgraph.edgeSet =
      (interval P i k (hij.trans hjk)).toSubgraph.edgeSet := by
  ext e
  simp only [Set.mem_union,interval_edges P hij (hjk.trans hk),interval_edges P hjk hk,
    interval_edges P (hij.trans hjk) hk]
  constructor
  · rintro (⟨m,him,hmj,he⟩|⟨m,hjm,hmk,he⟩) <;> exact ⟨m,by omega,by omega,he⟩
  · rintro ⟨m,him,hmk,he⟩
    by_cases hmj : m < j
    · exact Or.inl ⟨m,him,hmj,he⟩
    · exact Or.inr ⟨m,by omega,hmk,he⟩

lemma interval_append_drop (P : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length) :
    (interval P i j hij).append (P.drop j)=P.drop i := by
  apply Walk.ext_getVert
  intro k
  rw [Walk.getVert_append,interval_length P hij hj,Walk.drop_getVert]
  by_cases hk : k < j-i
  · rw [if_pos hk,interval_getVert P hij hk.le,Walk.drop_getVert]
  · rw [if_neg hk,Walk.drop_getVert]
    congr 1
    omega

lemma split_interval (P : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length) :
    P=(P.take i).append ((interval P i j hij).append (P.drop j)) := by
  rw [interval_append_drop P hij hj,Walk.append_take_drop_eq]

lemma take_support (P : G.Walk a b) {i : ℕ} (hi : i ≤ P.length) (x : V) :
    x ∈ (P.take i).support ↔ ∃ m, m ≤ i ∧ x=P.getVert m := by
  rw [Walk.mem_support_iff_exists_getVert]
  simp only [Walk.take_length,inf_eq_left.mpr hi]
  constructor
  · rintro ⟨m,hx,hm⟩
    rw [Walk.take_getVert,inf_eq_right.mpr hm] at hx
    exact ⟨m,hm,hx.symm⟩
  · rintro ⟨m,hm,hx⟩
    exact ⟨m,by rw [Walk.take_getVert,inf_eq_right.mpr hm]; exact hx.symm,hm⟩

lemma drop_support (P : G.Walk a b) {i : ℕ} (hi : i ≤ P.length) (x : V) :
    x ∈ (P.drop i).support ↔ ∃ m, i ≤ m ∧ m ≤ P.length ∧ x=P.getVert m := by
  rw [Walk.mem_support_iff_exists_getVert]
  simp only [Walk.drop_length,Walk.drop_getVert]
  constructor
  · rintro ⟨m,hx,hm⟩
    exact ⟨i+m,by omega,by omega,hx.symm⟩
  · rintro ⟨m,him,hm,hx⟩
    exact ⟨m-i,by rw [Nat.add_sub_of_le him]; exact hx.symm,by omega⟩

end Erdos583PathIntervalsDevelopment
