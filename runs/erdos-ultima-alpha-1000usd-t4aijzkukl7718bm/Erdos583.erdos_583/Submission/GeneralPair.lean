import Submission.Work

/-! Unrestricted replacement of two indexed trail members. -/
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
namespace Erdos583GeneralPairDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma replace_two {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j) (a b c d : V)
    (p : G.Walk a b) (q : G.Walk c d)
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ S : TrailFamily G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = q.toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.score + (T.walk i).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + q.toSubgraph.verts.ncard := by
  classical
  let aa : Fin k → V := fun l ↦ if l=i then a else if l=j then c else T.start l
  let bb : Fin k → V := fun l ↦ if l=i then b else if l=j then d else T.finish l
  have hwalk (l : Fin k) : ∃ r : G.Walk (aa l) (bb l), r.IsTrail ∧
      r.toSubgraph = if l=i then p.toSubgraph else if l=j then q.toSubgraph else (T.walk l).toSubgraph := by
    by_cases hli : l = i
    · subst l
      rw [show aa i = a by simp [aa],show bb i = b by simp [bb]]
      simp only [↓reduceIte]
      exact ⟨p, hp, rfl⟩
    · by_cases hlj : l = j
      · subst l
        rw [show aa j = c by simp [aa,hij.symm],show bb j = d by simp [bb,hij.symm]]
        simp only [if_neg hij.symm, ↓reduceIte]
        exact ⟨q, hq, rfl⟩
      · have ha : aa l = T.start l := by simp [aa,hli,hlj]
        have hb : bb l = T.finish l := by simp [bb,hli,hlj]
        rw [ha,hb]
        simp only [if_neg hli, if_neg hlj]
        exact ⟨T.walk l, T.isTrail l, rfl⟩
  choose r hr hre using hwalk
  have hri : (r i).toSubgraph = p.toSubgraph := by simpa using hre i
  have hrj : (r j).toSubgraph = q.toSubgraph := by simpa [hij.symm] using hre j
  have hrl (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      (r l).toSubgraph = (T.walk l).toSubgraph := by simpa [hli, hlj] using hre l
  have hcross (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      Disjoint (p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet) (T.walk l).toSubgraph.edgeSet := by
    rw [hu]
    exact disjoint_sup_left.mpr ⟨T.disjoint hli.symm, T.disjoint hlj.symm⟩
  have hdis : Pairwise fun l m ↦ Disjoint (r l).toSubgraph.edgeSet (r m).toSubgraph.edgeSet := by
    intro l m hlm
    by_cases hli : l = i
    · subst l
      rw [hri]
      by_cases hmj : m = j
      · subst m; rw [hrj]; exact hpq
      · rw [hrl m hlm.symm hmj]
        exact (disjoint_sup_left.mp (hcross m hlm.symm hmj)).1
    · by_cases hlj : l = j
      · subst l
        rw [hrj]
        by_cases hmi : m = i
        · subst m; rw [hri]; exact hpq.symm
        · rw [hrl m hmi hlm.symm]
          exact (disjoint_sup_left.mp (hcross m hmi hlm.symm)).2
      · rw [hrl l hli hlj]
        by_cases hmi : m = i
        · subst m; rw [hri]
          exact (disjoint_sup_left.mp (hcross l hli hlj)).1.symm
        · by_cases hmj : m = j
          · subst m; rw [hrj]
            exact (disjoint_sup_left.mp (hcross l hli hlj)).2.symm
          · rw [hrl m hmi hmj]
            exact T.disjoint hlm
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ l, e ∈ (r l).toSubgraph.edgeSet := by
    constructor
    · intro he
      obtain ⟨l, hl⟩ := (T.cover e).mp he
      by_cases hli : l = i
      · subst l
        have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inl hl
        exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
      · by_cases hlj : l = j
        · subst l
          have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inr hl
          exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
        · exact ⟨l, (hrl l hli hlj).symm ▸ hl⟩
    · rintro ⟨l, hl⟩
      exact (r l).toSubgraph.edgeSet_subset hl
  let S : TrailFamily G k :=
    { start := aa
      finish := bb
      walk := r
      isTrail := hr
      disjoint := hdis
      cover := hcover }
  refine ⟨S, hri, hrj, hrl, ?_⟩
  · have hsum : ∑ l ∈ (Finset.univ.erase i).erase j, (S.walk l).toSubgraph.verts.ncard =
        ∑ l ∈ (Finset.univ.erase i).erase j, (T.walk l).toSubgraph.verts.ncard := by
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hlj, hl⟩ := Finset.mem_erase.mp hl
      have hli := (Finset.mem_erase.mp hl).1
      change (r l).toSubgraph.verts.ncard = _
      rw [hrl l hli hlj]
    have hS := NormalTrailSystem.sum_extract_two (fun l ↦ (S.walk l).toSubgraph.verts.ncard) i j hij
    have hT := NormalTrailSystem.sum_extract_two (fun l ↦ (T.walk l).toSubgraph.verts.ncard) i j hij
    change S.score = (r i).toSubgraph.verts.ncard + (r j).toSubgraph.verts.ncard + _ at hS
    rw [hri, hrj, hsum] at hS
    change T.score = _ at hT
    dsimp only at hS hT
    omega
end Erdos583GeneralPairDevelopment
