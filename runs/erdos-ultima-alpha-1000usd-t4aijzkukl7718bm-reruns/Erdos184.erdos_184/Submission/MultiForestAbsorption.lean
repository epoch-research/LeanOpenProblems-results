import Submission.TwoForestAbsorption

/-!
A marked graph containing k edge-disjoint connected spanning subgraphs can
absorb any prescribed partition of its complement into k+1 forests.
This is a conditional auxiliary theorem, not a settlement of Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MultiForestAbsorption
open TwoForestAbsorption

variable {V : Type*} [Fintype V]

lemma hitting_of_acyclic_complement (G R : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hf : (G \ R).IsAcyclic) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ R.edgeFinset.card := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G he
  have hh : ∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty := by
    intro H hH
    apply cycle_hits_marked G R hf H (hc H hH).1
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v
  refine ⟨D,?_,hd,hh,decomposition_edge_transversal_bound G R D hd hh⟩
  intro H hH
  refine ⟨(hc H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v

lemma even_parity_union (X F : SimpleGraph V) (hd : Disjoint X.edgeSet F.edgeSet)
    (hp : ∀ v, (X.degree v : ZMod 2) = (F.degree v : ZMod 2)) :
    ∀ v, Even ((X ⊔ F).degree v) := by
  intro v
  have hdeg := degree_sup_of_edge_disjoint X F hd v
  have hpar := hp v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hpar ⊢
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [hdeg,Nat.cast_add,hpar,CharTwo.add_self_eq_zero]

lemma even_difference {G A : SimpleGraph V} (hAG : A ≤ G)
    (hG : ∀ v, Even (Nat.card (G.neighborSet v)))
    (hA : ∀ v, Even (Nat.card (A.neighborSet v))) :
    ∀ v, Even (Nat.card ((G \ A).neighborSet v)) := by
  intro v
  have hdeg := degree_sdiff_of_le hAG v
  have hgv := hG v
  have hav := hA v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hgv hav ⊢
  rw [hdeg]
  obtain ⟨a,ha⟩ := hgv
  obtain ⟨b,hb⟩ := hav
  exact ⟨a-b,by omega⟩

set_option maxHeartbeats 800000 in
/-- The connected marked subgraphs are separate parity resources. Their
number is an explicit hypothesis, not inferred from connectedness alone. -/
theorem hitting_of_forest_partition (k : ℕ) (G R : SimpleGraph V)
    (F : Fin (k+1) → SimpleGraph V) (S : Fin k → SimpleGraph V)
    (hRG : R ≤ G) (he : ∀ v, Even (G.degree v))
    (hforest : ∀ i, (F i).IsAcyclic)
    (hFdis : Pairwise (fun i j => Disjoint (F i).edgeSet (F j).edgeSet))
    (hcover : ∀ u v, (G \ R).Adj u v ↔ ∃ i, (F i).Adj u v)
    (hS : ∀ i, S i ≤ R) (hconn : ∀ i, (S i).Connected)
    (hSdis : Pairwise (fun i j => Disjoint (S i).edgeSet (S j).edgeSet)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ R.edgeFinset.card := by
  induction k generalizing G R with
  | zero =>
      apply hitting_of_acyclic_complement G R he
      have hg : G \ R = F 0 := by
        ext u v
        rw [hcover]
        constructor
        · rintro ⟨i,hi⟩
          fin_cases i
          exact hi
        · intro h
          exact ⟨0,h⟩
      rw [hg]
      exact hforest 0
  | succ k ih =>
      have hsub (i : Fin (k+1+1)) : F i ≤ G \ R := by
        intro u v h
        exact (hcover u v).mpr ⟨i,h⟩
      obtain ⟨X,hXS,hpar⟩ := ParityCompletion.exists_parity_subgraph (S 0) (F 0) (hconn 0)
      have hXR : X ≤ R := hXS.trans (hS 0)
      have hdis : Disjoint X.edgeSet (F 0).edgeSet := by
        apply Set.disjoint_left.mpr
        intro e hx hf
        have hr := SimpleGraph.edgeSet_mono hXR hx
        have hb := SimpleGraph.edgeSet_mono (hsub 0) hf
        rw [edgeSet_sdiff] at hb
        exact hb.2 hr
      let A := X ⊔ F 0
      have hAG : A ≤ G := sup_le (hXR.trans hRG) ((hsub 0).trans sdiff_le)
      have heA : ∀ v, Even (A.degree v) := by
        have h := even_parity_union X (F 0) hdis hpar
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h v
      have heC : ∀ v, Even ((G \ A).degree v) := by
        have hg : ∀ v, Even (Nat.card (G.neighborSet v)) := by
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he
        have ha : ∀ v, Even (Nat.card (A.neighborSet v)) := by
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heA
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using even_difference hAG hg ha
      let R' := R \ X
      have hR'G : R' ≤ G \ A := by
        intro u v h
        refine ⟨hRG h.1,?_⟩
        rintro (hx | hf)
        · exact h.2 hx
        · exact (hsub 0 hf).2 h.1
      have hFtail : ∀ u v, ((G \ A) \ R').Adj u v ↔
          ∃ i : Fin (k+1), (F i.succ).Adj u v := by
        intro u v
        constructor
        · intro h
          have hnotX : ¬X.Adj u v := fun hx => h.1.2 (Or.inl hx)
          have hnotR : ¬R.Adj u v := fun hr => h.2 ⟨hr,hnotX⟩
          obtain ⟨i,hi⟩ := (hcover u v).mp ⟨h.1.1,hnotR⟩
          refine Fin.cases ?_ (fun j hj => ⟨j,hj⟩) i hi
          intro h0
          exact (h.1.2 (Or.inr h0)).elim
        · rintro ⟨i,hi⟩
          have hb := hsub i.succ hi
          have hnotX : ¬X.Adj u v := fun hx => hb.2 (hXR hx)
          have hnotF : ¬(F 0).Adj u v := by
            intro h0
            have hh := hFdis (show (0 : Fin (k+1+1)) ≠ i.succ by exact (Fin.succ_ne_zero i).symm)
            exact Set.disjoint_left.mp hh (show s(u,v) ∈ (F 0).edgeSet from h0)
              (show s(u,v) ∈ (F i.succ).edgeSet from hi)
          exact ⟨⟨hb.1,fun h => h.elim hnotX hnotF⟩,fun h => hb.2 h.1⟩
      have hStail (i : Fin k) : S i.succ ≤ R' := by
        intro u v h
        refine ⟨hS i.succ h,?_⟩
        intro hx
        have hh := hSdis (show (0 : Fin (k+1)) ≠ i.succ by exact (Fin.succ_ne_zero i).symm)
        exact Set.disjoint_left.mp hh (show s(u,v) ∈ (S 0).edgeSet from hXS hx)
          (show s(u,v) ∈ (S i.succ).edgeSet from h)
      obtain ⟨DC,hcC,hdC,hhC,hbC⟩ := ih (G \ A) R'
        (fun i => F i.succ) (fun i => S i.succ) hR'G (by
          intro v
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heC v)
        (fun i => hforest i.succ)
        (fun i j hij => hFdis (fun h => hij (Fin.succ_injective _ h))) hFtail hStail
        (fun i => hconn i.succ)
        (fun i j hij => hSdis (fun h => hij (Fin.succ_injective _ h)))
      have hfA : (A \ R).IsAcyclic := by
        apply SimpleGraph.IsAcyclic.anti (G' := F 0) _ (hforest 0)
        intro u v h
        rcases h.1 with hx | hf
        · exact (h.2 (hXR hx)).elim
        · exact hf
      obtain ⟨DA,hcA,hdA⟩ := even_cycle_decomposition A (by
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heA v)
      refine combine_hitting G R A hAG DA DC ?_ ?_ hdA hdC ?_ ?_
      · intro H hH
        refine ⟨(hcA H hH).1,?_⟩
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcA H hH).2 v
      · intro H hH
        refine ⟨(hcC H hH).1,?_⟩
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcC H hH).2 v
      · intro H hH
        apply cycle_hits_marked A R hfA H (hcA H hH).1
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcA H hH).2 v
      · intro H hH
        obtain ⟨e,heH,heR⟩ := hhC H hH
        exact ⟨e,heH,SimpleGraph.edgeSet_mono (show R' ≤ R from sdiff_le) heR⟩

end Erdos184.MultiForestAbsorption
