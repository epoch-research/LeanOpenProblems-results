import Submission.CountableExtensionGraph

/-!
Countable universality of the explicit K4-free finite-extension graph.
This does not assert any corresponding universality of its ultrafilter
extensions, or settle Erdős 595.
-/

open SimpleGraph Set
open Erdos595Work Erdos595CountableExtension
namespace Erdos595CountableGenericUniversality

structure Partial (H : SimpleGraph ℕ) (n : ℕ) where
  f : ℕ → Vertex
  inj : ∀ i < n, ∀ j < n, f i = f j → i = j
  rel : ∀ i < n, ∀ j < n, G.Adj (f i) (f j) ↔ H.Adj i j

private theorem extend (H : SimpleGraph ℕ) (hH : H.CliqueFree 4) (n : ℕ)
    (p : Partial H n) :
    ∃ q : Partial H (n+1), ∀ i < n, q.f i = p.f i := by
  classical
  let s := ((Finset.range n).filter (H.Adj n)).image p.f
  let t := ((Finset.range n).filter (fun i => ¬H.Adj n i)).image p.f
  have hs : ∀ v, v ∈ s ↔ ∃ i < n, H.Adj n i ∧ p.f i = v := by
    intro v
    simp only [s,Finset.mem_image,Finset.mem_filter,Finset.mem_range]
    aesop
  have ht : ∀ v, v ∈ t ↔ ∃ i < n, ¬H.Adj n i ∧ p.f i = v := by
    intro v
    simp only [t,Finset.mem_image,Finset.mem_filter,Finset.mem_range]
    aesop
  have hst : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro v hvs hvt
    obtain ⟨i,hi,hai,hei⟩ := (hs v).mp hvs
    obtain ⟨j,hj,haj,hej⟩ := (ht v).mp hvt
    have he := p.inj i hi j hj (hei.trans hej.symm)
    exact haj (he ▸ hai)
  have htf : (G.induce (s : Set Vertex)).CliqueFree 3 := by
    intro F hF
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hF
    obtain ⟨i,hi,hai,hei⟩ := (hs a.val).mp a.property
    obtain ⟨j,hj,haj,hej⟩ := (hs b.val).mp b.property
    obtain ⟨k,hk,hak,hek⟩ := (hs c.val).mp c.property
    have hij : H.Adj i j := (p.rel i hi j hj).mp (by simpa only [hei,hej] using hab)
    have hik : H.Adj i k := (p.rel i hi k hk).mp (by simpa only [hei,hek] using hac)
    have hjk : H.Adj j k := (p.rel j hj k hk).mp (by simpa only [hej,hek] using hbc)
    exact no_adj_common_neighbors hH hai haj hij hak hik hjk
  obtain ⟨v,hv,hvs,hvt⟩ := finite_extension s t htf hst
  have hold : ∀ i < n, p.f i ∈ s ∪ t := by
    intro i hi
    by_cases h : H.Adj n i
    · exact Finset.mem_union_left _ ((hs _).mpr ⟨i,hi,h,rfl⟩)
    · exact Finset.mem_union_right _ ((ht _).mpr ⟨i,hi,h,rfl⟩)
  have hne : ∀ i < n, v ≠ p.f i := by
    intro i hi he
    exact hv (he ▸ hold i hi)
  have hadj : ∀ i < n, G.Adj v (p.f i) ↔ H.Adj n i := by
    intro i hi
    constructor
    · intro h
      by_contra hn
      exact hvt _ ((ht _).mpr ⟨i,hi,hn,rfl⟩) h
    · intro h
      exact hvs _ ((hs _).mpr ⟨i,hi,h,rfl⟩)
  let f := Function.update p.f n v
  have hf : ∀ i, i ≠ n → f i = p.f i := fun i hi => Function.update_of_ne hi _ _
  have hfn : f n = v := Function.update_self _ _ _
  refine ⟨⟨f,?_,?_⟩,?_⟩
  · intro i hi j hj he
    by_cases hin : i = n
    · subst i
      by_cases hjn : j = n
      · exact hjn.symm
      · have hj' : j < n := by omega
        exact (hne j hj' (by simpa only [hfn,hf j hjn] using he)).elim
    · by_cases hjn : j = n
      · subst j
        have hi' : i < n := by omega
        exact (hne i hi' (by simpa only [hfn,hf i hin] using he.symm)).elim
      · exact p.inj i (by omega) j (by omega) (by simpa only [hf i hin,hf j hjn] using he)
  · intro i hi j hj
    by_cases hin : i = n
    · subst i
      by_cases hjn : j = n
      · subst j
        simp only [SimpleGraph.irrefl]
      · rw [hfn,hf j hjn]
        exact hadj j (by omega)
    · by_cases hjn : j = n
      · subst j
        rw [hf i hin,hfn,G.adj_comm,H.adj_comm]
        exact hadj i (by omega)
      · rw [hf i hin,hf j hjn]
        exact p.rel i (by omega) j (by omega)
  · intro i hi
    exact hf i (by omega)

private noncomputable def chain (H : SimpleGraph ℕ) (hH : H.CliqueFree 4) :
    (n : ℕ) → Partial H n
  | 0 => ⟨fun _ => seed 0,by omega,by omega⟩
  | n+1 => (extend H hH n (chain H hH n)).choose

private lemma chain_agree (H : SimpleGraph ℕ) (hH : H.CliqueFree 4)
    {i n m : ℕ} (hin : i < n) (hnm : n ≤ m) :
    (chain H hH m).f i = (chain H hH n).f i := by
  induction m,hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    exact ((extend H hH m (chain H hH m)).choose_spec i (hin.trans_le hm)).trans ih

/-- Every K4-free graph on N has an induced embedding into the explicit base. -/
theorem universal_nat (H : SimpleGraph ℕ) (hH : H.CliqueFree 4) : Nonempty (H ↪g G) := by
  let f : ℕ → Vertex := fun i => (chain H hH (i+1)).f i
  have hf : ∀ i n, i < n → f i = (chain H hH n).f i := by
    intro i n hin
    exact (chain_agree H hH (Nat.lt_succ_self i) (by omega)).symm
  refine ⟨{ toFun := f, inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j he
    let n := max i j + 1
    have hi : i < n := by omega
    have hj : j < n := by omega
    exact (chain H hH n).inj i hi j hj (by simpa only [hf i n hi,hf j n hj] using he)
  · intro i j
    let n := max i j + 1
    have hi : i < n := by omega
    have hj : j < n := by omega
    change G.Adj (f i) (f j) ↔ H.Adj i j
    rw [hf i n hi,hf j n hj]
    exact (chain H hH n).rel i hi j hj

/-- Countability, not merely a countable vertex coloring, is assumed here. -/
theorem universal_countable {A : Type*} [Countable A]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) : Nonempty (H ↪g G) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl h =>
    refine ⟨{ toFun := isEmptyElim, inj' := ?_, map_rel_iff' := ?_ }⟩
    · intro a; exact isEmptyElim a
    · intro a; exact isEmptyElim a
  | inr h =>
    obtain ⟨e,he⟩ := exists_injective_nat A
    let f : A ↪ ℕ := ⟨e,he⟩
    obtain ⟨g⟩ := universal_nat (H.map f) (SimpleGraph.cliqueFree_map_iff.mpr hH)
    exact ⟨g.comp (SimpleGraph.Embedding.map f H)⟩

#print axioms universal_nat
#print axioms universal_countable
end Erdos595CountableGenericUniversality
