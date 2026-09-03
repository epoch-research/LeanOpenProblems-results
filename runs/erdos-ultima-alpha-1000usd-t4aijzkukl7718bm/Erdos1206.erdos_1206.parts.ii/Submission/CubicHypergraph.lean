import Submission.CubicPairCodegree
import Submission.StrictCubeCollision

/-! The finite cubic collision hypergraph and a uniform pair-codegree bound. -/
namespace Erdos1206.CubicHypergraph
open Finset CubicPairCodegree
open scoped Classical

def IsEdge (e : Finset ℕ) : Prop := ∃ a b c d : ℕ,
  e={a,b,c,d} ∧ a < b ∧ b < c ∧ c < d ∧ a^3+d^3=b^3+c^3

noncomputable def edges (N : ℕ) (S : Set ℕ) : Finset (Finset ℕ) :=
  (range N).powerset.filter (fun e => (e : Set ℕ) ⊆ S ∧ IsEdge e)

lemma mem_edges {N : ℕ} {S : Set ℕ} {e : Finset ℕ} :
    e ∈ edges N S ↔ e ⊆ range N ∧ (e : Set ℕ) ⊆ S ∧ IsEdge e := by
  simp [edges]

lemma IsEdge.card {e : Finset ℕ} (he : IsEdge e) : e.card=4 := by
  obtain ⟨a,b,c,d,rfl,hab,hbc,hcd,_⟩ := he
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hbd := hbc.trans hcd
  simp [hab.ne,hac.ne,had.ne,hbc.ne,hbd.ne,hcd.ne]

lemma ordered_completion {a b c d x y N : ℕ}
    (haN : a < N) (hbN : b < N) (hcN : c < N) (hdN : d < N)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3)
    (hx : x ∈ ({a,b,c,d} : Finset ℕ)) (hy : y ∈ ({a,b,c,d} : Finset ℕ))
    (hxy : x < y) : ∃ p ∈ completions N x y, ({a,b,c,d} : Finset ℕ)={x,y,p.1,p.2} := by
  have hab3 := Nat.pow_lt_pow_left hab (by decide : 3≠0)
  have hbc3 := Nat.pow_lt_pow_left hbc (by decide : 3≠0)
  have hcd3 := Nat.pow_lt_pow_left hcd (by decide : 3≠0)
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;> try omega
  · refine ⟨(c,d),mem_union_right _ (mem_diffPairs.mpr ⟨hcN,hdN,hcd,by omega⟩),?_⟩
    rfl
  · refine ⟨(b,d),mem_union_right _ (mem_diffPairs.mpr ⟨hbN,hdN,hbc.trans hcd,by omega⟩),?_⟩
    ext n; simp only [mem_insert,mem_singleton]; tauto
  · refine ⟨(b,c),mem_union_left _ (mem_sumPairs.mpr ⟨hbN,hcN,hbc,he.symm⟩),?_⟩
    ext n; simp only [mem_insert,mem_singleton]; tauto
  · refine ⟨(a,d),mem_union_left _ (mem_sumPairs.mpr ⟨haN,hdN,hab.trans (hbc.trans hcd),he⟩),?_⟩
    ext n; simp only [mem_insert,mem_singleton]; tauto
  · refine ⟨(a,c),mem_union_right _ (mem_diffPairs.mpr ⟨haN,hcN,hab.trans hbc,by omega⟩),?_⟩
    ext n; simp only [mem_insert,mem_singleton]; tauto
  · refine ⟨(a,b),mem_union_right _ (mem_diffPairs.mpr ⟨haN,hbN,hab,by omega⟩),?_⟩
    ext n; simp only [mem_insert,mem_singleton]; tauto

/-- A link is covered by the possible remaining pairs. -/
lemma link_subset_image (N : ℕ) (S : Set ℕ) {x y : ℕ} (hxy : x < y) :
    (edges N S).filter (fun e => x ∈ e ∧ y ∈ e) ⊆
      (completions N x y).image (fun p => ({x,y,p.1,p.2} : Finset ℕ)) := by
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨heN,_,a,b,c,d,heq,hab,hbc,hcd,hcube⟩ := mem_edges.mp he
  subst e
  have hN (n : ℕ) (hn : n ∈ ({a,b,c,d} : Finset ℕ)) : n < N := mem_range.mp (heN hn)
  obtain ⟨p,hp,hp'⟩ := ordered_completion (hN a (by simp)) (hN b (by simp))
    (hN c (by simp)) (hN d (by simp)) hab hbc hcd hcube hx hy hxy
  exact mem_image.mpr ⟨p,hp,hp'.symm⟩

/-- Uniformly for every source, pair-codegrees in a prefix of length `t^12`
are bounded by a constant times `t^3`. -/
theorem pair_codegree_bound (S : Set ℕ) {x y t : ℕ} (hxy : x≠y) :
    ((edges (t^12) S).filter (fun e => x ∈ e ∧ y ∈ e)).card ≤ codegreeConstant*t^3 := by
  wlog hlt : x < y generalizing x y
  · have hyx : y < x := by omega
    have hh := this hxy.symm hyx
    simpa only [and_comm] using hh
  by_cases hyN : y < t^12
  · calc
      _ ≤ ((completions (t^12) x y).image (fun p => ({x,y,p.1,p.2} : Finset ℕ))).card :=
        card_le_card (link_subset_image _ _ hlt)
      _ ≤ (completions (t^12) x y).card := card_image_le
      _ ≤ _ := completions_card_le_power hlt hyN
  · have hempty : (edges (t^12) S).filter (fun e => x ∈ e ∧ y ∈ e)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,_,hy⟩ := mem_filter.mp he
      exact hyN (mem_range.mp ((mem_edges.mp he).1 hy))
    rw [hempty,card_empty]
    exact Nat.zero_le _

/-- Independence in all finite cubic hypergraphs is exactly Sidonness of the
cube image; the existing descent theorem handles repeated-root collisions. -/
theorem independent_iff_cubeSidon (A : Set ℕ) :
    (∀ N, edges N A=∅) ↔ IsSidon ((fun n : ℕ => n^3) '' A) := by
  rw [cubeSidon_iff_no_strict_positive]
  constructor
  · intro h a ha b hb c hc d hd _ hab hbc hcd he
    have he' : {a,b,c,d} ∈ edges (d+1) A := by
      apply mem_edges.mpr
      refine ⟨?_,?_,a,b,c,d,rfl,hab,hbc,hcd,he⟩
      · intro n hn
        simp only [mem_insert,mem_singleton] at hn
        rcases hn with rfl | rfl | rfl | rfl <;> simp only [mem_range] <;> omega
      · intro n hn
        simp only [mem_coe,mem_insert,mem_singleton] at hn
        rcases hn with rfl | rfl | rfl | rfl <;> assumption
    rw [h] at he'
    exact notMem_empty _ he'
  · intro h N
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨_,hS,a,b,c,d,rfl,hab,hbc,hcd,heq⟩ := mem_edges.mp he
    have ha0 := (weak_cube_collision_is_strict_positive hab hbc.le hcd heq).1
    exact h a (hS (by simp)) b (hS (by simp)) c (hS (by simp)) d (hS (by simp))
      ha0 hab hbc hcd heq

#print axioms pair_codegree_bound
#print axioms independent_iff_cubeSidon
end Erdos1206.CubicHypergraph
