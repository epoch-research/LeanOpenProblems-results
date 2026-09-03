import FormalConjecturesUtil
import Submission.MergePathLifting
import Submission.C8SplitPaths
import Submission.TwoPathSparseRoots

/-! Two individually safe vertex identifications can interact to create C8,
but their interacting endpoint quadruples are sparse under an explicit
subcritical maximum-degree bound. No such bound is asserted for exact
extremal hosts. -/
open SimpleGraph Finset Filter
namespace Erdos713C8TwoMergers
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
open Erdos713MergePathLifting Erdos713TwoPathRootCounting Erdos713TwoPathSparseRoots
variable {V : Type*} {G : SimpleGraph V} {u v : V}
set_option maxHeartbeats 2000000

lemma contains_merge_of_path (_huv : u ≠ v) (hn : ¬ G.Adj u v)
    (p : G.Walk u v) (hp : p.IsPath) (hl : p.length = 8) :
    cycleGraph 8 ⊑ merge G u v hn := by
  classical
  have hnot (i : Fin 8) : p.getVert i.val ≠ v := by
    intro he
    have hh : i.val = p.length := hp.getVert_injOn
      (by change i.val ≤ p.length; omega) (by simp)
      (he.trans p.getVert_length.symm)
    omega
  let f : Fin 8 → {a : V // a ≠ v} := fun i => ⟨p.getVert i.val,hnot i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) (congrArg Subtype.val hij)
  have hnext (i : Fin 8) : (merge G u v hn).Adj (f i) (f (i+1)) := by
    apply (merge_adj G u v hn _ _).mpr
    by_cases hi : i.val < 7
    · apply Or.inl
      change G.Adj (p.getVert i.val) (p.getVert (i+1).val)
      have he : (i+1).val = i.val+1 := by rw [Fin.val_add]; norm_num; omega
      rw [he]
      exact p.adj_getVert_succ (by omega)
    · have hi' : i = 7 := by apply Fin.ext; omega
      subst i
      apply Or.inr
      apply Or.inr
      constructor
      · simp [f]
      · have hlast := p.adj_getVert_succ (i := 7) (by omega)
        have h8 : p.getVert 8 = v := by rw [← hl,p.getVert_length]
        simpa only [show 7+1=8 from rfl,h8] using hlast.symm
  refine ⟨⟨⟨f,?_⟩,hf⟩⟩
  intro i j hij
  rcases cycleGraph_adj.mp hij with h | h
  · have he : i = j+1 := by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
    rw [he]
    exact (hnext j).symm
  · have he : j = i+1 := by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
    rw [he]
    exact hnext i

lemma contains_merge_iff_path (hf : (cycleGraph 8).Free G) (huv : u ≠ v)
    (hn : ¬ G.Adj u v) :
    cycleGraph 8 ⊑ merge G u v hn ↔
      ∃ p : G.Walk u v, p.IsPath ∧ p.length = 8 := by
  constructor
  · intro hc
    obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_copy_of_merge hf hn hc
    obtain ⟨p,hp,hl⟩ := Erdos713C8SplitPaths.split_has_path_eight w S hL hR
    let q : G.Walk v u := (p.map f.toHom).copy hv hu
    have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr
      (Walk.map_isPath_of_injective f.injective hp)
    refine ⟨q.reverse,hq.reverse,?_⟩
    simpa only [q,Walk.length_reverse,Walk.length_copy,Walk.length_map] using hl
  · rintro ⟨p,hp,hl⟩
    exact contains_merge_of_path huv hn p hp hl

/-- Both individual mergers are C8-free, while their successive performance
creates a C8. The four distinguished roots are pairwise distinct. -/
structure GenuineDouble (G : SimpleGraph V) (a b c d : V) : Prop where
  originalFree : (cycleGraph 8).Free G
  ab : a ≠ b
  ca : c ≠ a
  cb : c ≠ b
  da : d ≠ a
  db : d ≠ b
  cd : c ≠ d
  nonadjAB : ¬ G.Adj a b
  nonadjCD : ¬ G.Adj c d
  nonadjSecond : ¬ (merge G a b nonadjAB).Adj ⟨c,cb⟩ ⟨d,db⟩
  firstFree : (cycleGraph 8).Free (merge G a b nonadjAB)
  secondFree : (cycleGraph 8).Free (merge G c d nonadjCD)
  doubleContains : cycleGraph 8 ⊑
    merge (merge G a b nonadjAB) ⟨c,cb⟩ ⟨d,db⟩ nonadjSecond

lemma genuine_mem_total [Fintype V] {a b c d : V} (h : GenuineDouble G a b c d) :
    ((a,b),(c,d)) ∈ totalLengthRoots G 8 := by
  obtain ⟨p,hp,hl⟩ := (contains_merge_iff_path h.firstFree
    (show (⟨c,h.cb⟩ : {x : V // x ≠ b}) ≠ ⟨d,h.db⟩ from
      fun he => h.cd (congrArg Subtype.val he)) h.nonadjSecond).mp h.doubleContains
  rcases path_lifts_or_two_walks h.ab h.nonadjAB h.ca h.da p hp with ⟨q,hq,hql⟩ | hh
  · exact (h.secondFree (contains_merge_of_path h.cd h.nonadjCD q hq (hql.trans hl))).elim
  · simpa only [hl] using hh

open scoped Classical in
noncomputable def genuineRoots [Fintype V] (G : SimpleGraph V) : Finset ((V × V) × (V × V)) :=
  univ.filter (fun p => GenuineDouble G p.1.1 p.1.2 p.2.1 p.2.2)

lemma genuineRoots_subset [Fintype V] (G : SimpleGraph V) :
    genuineRoots G ⊆ totalLengthRoots G 8 := by
  classical
  intro p hp
  exact genuine_mem_total (mem_filter.mp hp).2

open scoped Classical in
lemma card_genuineRoots_le [Fintype V] (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) :
    (genuineRoots G).card ≤ 18*(Fintype.card V)^2*D^8 := by
  exact (card_le_card (genuineRoots_subset G)).trans
    (by simpa using card_totalLengthRoots_le G D hD 8)

open scoped Classical in
theorem eventually_genuine_sparse {β C ε : ℝ} (hβ : β < 1/4) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) (D : ℕ),
      (∀ v, G.degree v ≤ D) → (D : ℝ) ≤ C*(n : ℝ)^β →
      ((genuineRoots G).card : ℝ) ≤ ε*(n : ℝ)^4 := by
  classical
  filter_upwards [eventually_eight_roots_sparse (C := C) hβ hε] with n hn
  intro G D hD hDC
  exact (Nat.cast_le.mpr (card_le_card (genuineRoots_subset G))).trans (hn G D hD hDC)

#print axioms contains_merge_iff_path
#print axioms genuine_mem_total
#print axioms eventually_genuine_sparse
end Erdos713C8TwoMergers
