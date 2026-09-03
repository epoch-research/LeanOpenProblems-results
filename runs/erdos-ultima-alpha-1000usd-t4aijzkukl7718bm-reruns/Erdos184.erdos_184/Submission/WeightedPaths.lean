import Submission.Circumference

/-! Maximum-weight path rotation and nonnegative weighted cycle bounds. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.WeightedPaths
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 600000

noncomputable def walkWeight (w : Sym2 V → ℝ) {u v : V} (p : G.Walk u v) : ℝ :=
  (p.edges.map w).sum

@[simp] lemma weight_nil (w : Sym2 V → ℝ) (u : V) :
    walkWeight w (Walk.nil : G.Walk u u) = 0 := rfl

@[simp] lemma weight_cons (w : Sym2 V → ℝ) {u v z : V} (h : G.Adj u v)
    (p : G.Walk v z) : walkWeight w (p.cons h) = w s(u,v) + walkWeight w p := rfl

@[simp] lemma weight_append (w : Sym2 V → ℝ) {u v z : V}
    (p : G.Walk u v) (q : G.Walk v z) :
    walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
  simp [walkWeight,Walk.edges_append]

@[simp] lemma weight_reverse (w : Sym2 V → ℝ) {u v : V} (p : G.Walk u v) :
    walkWeight w p.reverse = walkWeight w p := by
  simp [walkWeight]

@[simp] lemma weight_copy (w : Sym2 V → ℝ) {u v a b : V} (p : G.Walk u v)
    (ha : u = a) (hb : v = b) : walkWeight w (p.copy ha hb) = walkWeight w p := by
  simp [walkWeight]

lemma weight_nonneg (w : Sym2 V → ℝ) (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    {u v : V} (p : G.Walk u v) : 0 ≤ walkWeight w p := by
  apply List.sum_nonneg
  intro t ht
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
  exact hn e (p.edges_subset_edgeSet he)

lemma exists_maximum_weight_path [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      ∀ a b (q : G.Walk a b), q.IsPath → walkWeight w q ≤ walkWeight w p := by
  let P := (u : V) × (v : V) × G.Path u v
  let x : V := Classical.choice inferInstance
  have hP : (Finset.univ : Finset P).Nonempty :=
    ⟨⟨x,x,⟨Walk.nil,Walk.IsPath.nil⟩⟩,Finset.mem_univ _⟩
  obtain ⟨⟨u,v,p⟩,_,hm⟩ := Finset.exists_max_image (Finset.univ : Finset P)
    (fun p => walkWeight w p.2.2.val) hP
  exact ⟨u,v,p.val,p.property,fun a b q hq => hm ⟨a,b,⟨q,hq⟩⟩ (Finset.mem_univ _)⟩

/-- Rotate a path at a chord from its first vertex. -/
lemma rotate_isPath {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (h : G.Adj b c) (ha : G.Adj a c) (hpq : (p.append (q.cons h)).IsPath) :
    (p.reverse.append (q.cons ha)).IsPath := by
  have hp := hpq.of_append_left
  have hq := hpq.of_append_right
  have hdis : p.support.Disjoint q.support := by
    have hh := hpq.support_nodup
    rw [Walk.support_append,Walk.support_cons,List.tail_cons,List.nodup_append'] at hh
    exact hh.2.2
  rw [Walk.isPath_def,Walk.support_append,Walk.support_cons,List.tail_cons,List.nodup_append']
  exact ⟨hp.reverse.support_nodup, (Walk.cons_isPath_iff h q).mp hq |>.1.support_nodup,
    fun x hx hy => hdis (by simpa using hx) hy⟩

lemma maximum_path_chord {a b c d : V} (w : Sym2 V → ℝ)
    (p : G.Walk a b) (q : G.Walk c d) (h : G.Adj b c) (ha : G.Adj a c)
    (hpq : (p.append (q.cons h)).IsPath)
    (hm : ∀ x y (r : G.Walk x y), r.IsPath →
      walkWeight w r ≤ walkWeight w (p.append (q.cons h))) :
    w s(a,c) ≤ w s(b,c) := by
  have hh := hm _ _ _ (rotate_isPath p q h ha hpq)
  simp only [weight_append,weight_reverse,weight_cons] at hh
  linarith

lemma positive_neighbors_on_maximum_path (w : Sym2 V → ℝ) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ x y (q : G.Walk x y), q.IsPath → walkWeight w q ≤ walkWeight w p)
    {x : V} (hx : G.Adj u x) (hw : 0 < w s(u,x)) : x ∈ p.support := by
  by_contra hn
  have hh := hm _ _ _ (hp.cons (h := hx.symm) hn)
  simp only [weight_cons,Sym2.eq_swap] at hh
  linarith

lemma take_cons_drop {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i < p.length) :
    (p.take i).append ((p.drop (i+1)).cons (p.adj_getVert_succ hi)) = p := by
  induction p generalizing i with
  | nil => simp at hi
  | cons h q ih =>
    cases i with
    | zero => cases q <;> rfl
    | succ i =>
      simpa only [Walk.take,Walk.drop,Walk.cons_append] using
        congrArg (Walk.cons h) (ih i (by simpa using hi))

lemma maximum_path_chord_index (w : Sym2 V → ℝ) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ x y (q : G.Walk x y), q.IsPath → walkWeight w q ≤ walkWeight w p)
    {i : ℕ} (hi : i < p.length) (ha : G.Adj u (p.getVert (i+1))) :
    w s(u,p.getVert (i+1)) ≤ w s(p.getVert i,p.getVert (i+1)) := by
  apply maximum_path_chord w (p.take i) (p.drop (i+1)) (p.adj_getVert_succ hi) ha
  · rwa [take_cons_drop p i hi]
  · simpa only [take_cons_drop p i hi] using hm

lemma weight_eq_sum_range (w : Sym2 V → ℝ) {u v : V} (p : G.Walk u v) :
    walkWeight w p = ∑ i ∈ Finset.range p.length, w s(p.getVert i,p.getVert (i+1)) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [weight_cons,Walk.length_cons,Finset.sum_range_succ']
    simp only [Walk.getVert_cons_succ,Walk.getVert_zero]
    rw [ih]
    ring

noncomputable def star (G : SimpleGraph V) (w : Sym2 V → ℝ) (u x : V) : ℝ :=
  if G.Adj u x then w s(u,x) else 0

@[simp] lemma star_self (G : SimpleGraph V) (w : Sym2 V → ℝ) (u : V) :
    star G w u u = 0 := by simp [star]

lemma star_nonneg (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e) (u x : V) : 0 ≤ star G w u x := by
  unfold star
  split_ifs with h
  · exact hn _ h
  · exact le_rfl

lemma star_pos_iff (G : SimpleGraph V) (w : Sym2 V → ℝ) (u x : V) :
    0 < star G w u x ↔ G.Adj u x ∧ 0 < w s(u,x) := by
  by_cases h : G.Adj u x <;> simp [star,h]

lemma maximum_path_star_index (w : Sym2 V → ℝ)
    (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ x y (q : G.Walk x y), q.IsPath → walkWeight w q ≤ walkWeight w p)
    {i : ℕ} (hi : i < p.length) :
    star G w u (p.getVert (i+1)) ≤ w s(p.getVert i,p.getVert (i+1)) := by
  unfold star
  split_ifs with ha
  · exact maximum_path_chord_index w p hp hm hi ha
  · exact hn _ (p.adj_getVert_succ hi)

lemma star_sum_eq_prefix [Fintype V] (w : Sym2 V → ℝ) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (k : ℕ) (hk : k ≤ p.length)
    (hz : ∀ x, star G w u x ≠ 0 → ∃ i ≤ k, p.getVert i = x) :
    (∑ x, star G w u x) = ∑ i ∈ Finset.range k, star G w u (p.getVert (i+1)) := by
  have hh : (∑ i ∈ Finset.range (k+1), star G w u (p.getVert i)) = ∑ x, star G w u x := by
    apply Finset.sum_of_injOn p.getVert
    · intro i hi j hj hij
      apply hp.getVert_injOn (show i ≤ p.length from by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk)
        (show j ≤ p.length from (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hk) hij
    · intro i hi; exact Finset.mem_univ _
    · intro x _ hx
      by_contra hnz
      obtain ⟨i,hi,heq⟩ := hz x hnz
      exact hx ⟨i,Finset.mem_range.mpr (by omega),heq⟩
    · intro i hi; rfl
  rw [Finset.sum_range_succ'] at hh
  simpa using hh.symm

/-- With nonnegative edge weights and cycle/edge weights at most one, some
vertex has incident weight at most one. -/
lemma exists_star_sum_le_one [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (he : ∀ e ∈ G.edgeSet, w e ≤ 1)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    ∃ u, (∑ x, star G w u x) ≤ 1 := by
  obtain ⟨u,v,p,hp,hm⟩ := exists_maximum_weight_path G w
  let S := (Finset.range (p.length+1)).filter (fun i => 0 < star G w u (p.getVert i))
  have index_of_pos (x : V) (hx : 0 < star G w u x) :
      ∃ i ∈ S, p.getVert i = x := by
    obtain ⟨hax,hwx⟩ := (star_pos_iff G w u x).mp hx
    have hmem := positive_neighbors_on_maximum_path w p hp hm hax hwx
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [hi]⟩,hi⟩
  refine ⟨u,?_⟩
  by_cases hS : S.Nonempty
  · let k := S.max' hS
    have hkm := S.max'_mem hS
    have hk : k ≤ p.length := by
      have hh := Finset.mem_range.mp (Finset.mem_filter.mp hkm).1
      change k < p.length+1 at hh
      omega
    have hkpos : 0 < star G w u (p.getVert k) := (Finset.mem_filter.mp hkm).2
    have hk0 : k ≠ 0 := by intro h; simpa [h] using hkpos
    have hka := ((star_pos_iff G w u (p.getVert k)).mp hkpos).1
    have hz : ∀ x, star G w u x ≠ 0 → ∃ i ≤ k, p.getVert i = x := by
      intro x hx
      obtain ⟨i,hi,heq⟩ := index_of_pos x (lt_of_le_of_ne (star_nonneg G w hn u x) (Ne.symm hx))
      exact ⟨i,S.le_max' i hi,heq⟩
    rw [star_sum_eq_prefix w p hp k hk hz]
    have hsum : (∑ i ∈ Finset.range k, star G w u (p.getVert (i+1))) ≤ walkWeight w (p.take k) := by
      calc
        _ ≤ ∑ i ∈ Finset.range k, w s(p.getVert i,p.getVert (i+1)) :=
          Finset.sum_le_sum (fun i hi => maximum_path_star_index w hn p hp hm
            ((Finset.mem_range.mp hi).trans_le hk))
        _ = walkWeight w (p.take k) := by
          rw [weight_eq_sum_range,Walk.take_length,min_eq_left hk]
          apply Finset.sum_congr rfl
          intro i hi
          have hik : i+1 ≤ k := Finset.mem_range.mp hi
          simp only [Walk.take_getVert,min_eq_right hik,min_eq_right (by omega : i ≤ k)]
    apply hsum.trans
    have hq : (p.take k).IsPath :=
      Walk.IsPath.of_append_left (q := p.drop k) (by simpa using hp)
    by_cases hk2 : 2 ≤ k
    · have hcy := path_close_isCycle (p.take k) hq (by simpa [min_eq_left hk] using hk2) hka.symm
      have hh := hc _ _ hcy
      simp only [weight_cons] at hh
      have hw := hn s(p.getVert k,u) hka.symm
      linarith
    · have hk1 : k = 1 := by omega
      have hw := he s(u,p.getVert k) hka
      rw [weight_eq_sum_range,Walk.take_length,min_eq_left hk]
      simpa [hk1] using hw
  · have hz : ∀ x, star G w u x = 0 := by
      intro x
      by_contra hx
      obtain ⟨i,hi,_⟩ := index_of_pos x (lt_of_le_of_ne (star_nonneg G w hn u x) (Ne.symm hx))
      exact hS ⟨i,hi⟩
    simp only [hz,Finset.sum_const_zero]
    norm_num

end Erdos184.WeightedPaths
