import Submission.GuardedMatchingRestoration

/-! Initializing active guards by an induced seed matching.  This is a
conditional restoration criterion, not an unrestricted Gallai theorem. -/
namespace Erdos583SeedMatchingRestorationDevelopment
open SimpleGraph Erdos583Work Erdos583EvenEdgeRestorationDevelopment
open Erdos583NormalForestRestorationDevelopment
open Erdos583GuardedMatchingRestorationDevelopment
open Erdos583LocalZeroNormalizationDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.EvenMatchingRestore
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma matching_support_delete {V : Type*} {F : SimpleGraph V}
    (hm : ∀ x, (F.neighborSet x).Subsingleton) {u v : V} (h : F.Adj v u) (x : V) :
    x ∈ (F.deleteEdges {s(v,u)}).support ↔ x ∈ F.support ∧ x ≠ u ∧ x ≠ v := by
  constructor
  · rintro ⟨y,hxy⟩
    have hh := matching_delete_endpoints hm h hxy
    exact ⟨⟨y,F.deleteEdges_le _ hxy⟩,hh.2,hh.1⟩
  · rintro ⟨⟨y,hxy⟩,hxu,hxv⟩
    refine ⟨y,?_⟩
    change (F.deleteEdges {s(v,u)}).Adj x y
    rw [deleteEdges_adj,Set.mem_singleton_iff]
    refine ⟨hxy,?_⟩
    intro heq
    rcases Sym2.eq_iff.mp heq with hh|hh
    · exact hxv hh.1
    · exact hxu hh.1

/-- All seed edges can be oriented arbitrarily when their endpoints induce
exactly the seed matching. Their chosen heads end with quota two, their tails
with quota zero, and all other quotas stay one. -/
lemma restore_induced_seed_matching {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (hind : ∀ ⦃x y⦄, G.Adj x y → x ∈ F.support → y ∈ F.support → F.Adj x y)
    (A : Set V) (hside : ∀ ⦃x y⦄, F.Adj x y → (x ∈ A ↔ y ∉ A))
    {k : ℕ} (T : TrailFamily (G \ F) k) (hp : ∀ i, (T.walk i).IsPath)
    (hq : ∀ x, T.quota x=1) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧
      ∀ x, P.quota x=if x ∈ F.support then (if x ∈ A then 2 else 0) else 1 := by
  classical
  induction hn : F.edgeSet.ncard using Nat.strong_induction_on generalizing G F with
  | h n ih =>
    by_cases hbot : F=⊥
    · have hEq : G \ F=G := by
        ext a b
        simp only [hbot,sdiff_adj,bot_adj,not_false_eq_true,and_true]
      revert T
      rw [hEq]
      intro T hp hq
      exact ⟨T,hp,by simpa [hbot] using hq⟩
    obtain ⟨v,u,h,hvA,huA⟩ : ∃ v u, F.Adj v u ∧ v ∈ A ∧ u ∉ A := by
      obtain ⟨v,u,h⟩ := ne_bot_iff_exists_adj.mp hbot
      by_cases hvA : v ∈ A
      · exact ⟨v,u,h,hvA,(hside h).mp hvA⟩
      · have huA : u ∈ A := by
          by_contra huA
          exact hvA ((hside h).mpr huA)
        exact ⟨u,v,h.symm,huA,hvA⟩
    let J := G.deleteEdges {s(v,u)}
    let K := F.deleteEdges {s(v,u)}
    have hKJ : K ≤ J := deleteEdges_mono hFG
    have hKF : K ≤ F := F.deleteEdges_le _
    have hKm : ∀ x, (K.neighborSet x).Subsingleton := by
      intro x a ha b hb
      exact hm x (hKF ha) (hKF hb)
    have hKi : ∀ ⦃x y⦄, J.Adj x y → x ∈ K.support → y ∈ K.support → K.Adj x y := by
      intro x y hxy hx hy
      exact ⟨hind (G.deleteEdges_le _ hxy) (support_mono hKF hx) (support_mono hKF hy),hxy.2⟩
    have hKs : ∀ ⦃x y⦄, K.Adj x y → (x ∈ A ↔ y ∉ A) := by
      intro x y hxy
      exact hside (hKF hxy)
    have hdiff : J \ K=G \ F := by
      ext a b
      simp only [J,K,sdiff_adj,deleteEdges_adj,Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hab,hne⟩,hn⟩
        exact ⟨hab,fun hF ↦ hn ⟨hF,hne⟩⟩
      · rintro ⟨hab,hn⟩
        refine ⟨⟨hab,?_⟩,fun hh ↦ hn hh.1⟩
        intro heq
        exact hn ((F.adj_congr_of_sym2 heq).mpr h)
    have hlt : K.edgeSet.ncard<n := by
      rw [←hn]
      change (F.deleteEdges {s(v,u)}).edgeSet.ncard < F.edgeSet.ncard
      rw [edgeSet_deleteEdges]
      exact Set.ncard_diff_singleton_lt_of_mem (show s(v,u) ∈ F.edgeSet from h)
    have hex : ∃ U : TrailFamily J k, (∀ i, (U.walk i).IsPath) ∧
        ∀ x, U.quota x=if x ∈ K.support then (if x ∈ A then 2 else 0) else 1 := by
      generalize hB : G \ F=B at T hp hq
      have hEq : J \ K=B := hdiff.trans hB
      cases hEq
      obtain ⟨P,hP,hPq⟩ := ih K.edgeSet.ncard hlt J K hKJ hKm hKi hKs T hp hq rfl
      refine ⟨P,hP,?_⟩
      intro x
      have hh := hPq x
      by_cases hx : x ∈ K.support <;> simp only [hx,↓reduceIte] at hh ⊢ <;> exact hh
    obtain ⟨U,hU,hUq⟩ := hex
    have hsupp (x : V) : x ∈ K.support ↔ x ∈ F.support ∧ x ≠ u ∧ x ≠ v := matching_support_delete hm h x
    have huK : u ∉ K.support := by simp [hsupp]
    have hvK : v ∉ K.support := by simp [hsupp]
    have hqu : U.quota u=1 := by simp [hUq,huK]
    have hqv : U.quota v=1 := by simp [hUq,hvK]
    have havoid (x : V) (hvx : G.Adj v x) : U.quota x ≠ 0 := by
      have hxK : x ∉ K.support := by
        intro hx
        have hFx : F.Adj v x := hind hvx ⟨u,h⟩ (support_mono hKF hx)
        have hxu : x=u := hm v hFx h
        exact (hsupp x).mp hx |>.2.1 hxu
      simp [hUq,hxK]
    obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota U (v := u) (by omega)
    have hc : G.edgeSet=insert s(v,u) J.edgeSet := by
      rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
      exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from hFG h)).symm
    obtain ⟨P,hP,hPq⟩ := append_edge_away_from_inactive (G.deleteEdges_le _) U hU i hi
      (hFG h) (by simp) hc havoid
    refine ⟨P,hP,?_⟩
    intro x
    have hh := hPq x
    by_cases hxu : x=u
    · subst x
      have huF : u ∈ F.support := ⟨v,h.symm⟩
      simp only [hqu,h.ne,↓reduceIte,add_zero] at hh
      simp only [huF,huA,↓reduceIte]
      omega
    by_cases hxv : x=v
    · subst x
      have hvF : v ∈ F.support := ⟨u,h⟩
      simp only [hqv,h.ne.symm,↓reduceIte,add_zero] at hh
      simp only [hvF,hvA,↓reduceIte]
      omega
    · simp only [Ne.symm hxu,Ne.symm hxv,↓reduceIte,add_zero] at hh
      rw [hh,hUq]
      by_cases hx : x ∈ F.support
      · have hxK := (hsupp x).mpr ⟨hx,hxu,hxv⟩
        simp only [hx,hxK,↓reduceIte]
      · have hxK : x ∉ K.support := fun hh ↦ hx ((hsupp x).mp hh).1
        simp only [hx,hxK,↓reduceIte]

/-- A perfect matching on the even vertices can be restored within the sharp
all-odd budget if an induced submatching supplies a feedback guard set. -/
lemma gallai_of_seeded_matching {V : Type*} [Fintype V] (G F S : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (hcover : ∀ x, Even (Nat.card (G.neighborSet x)) → (F.neighborSet x).Nonempty)
    (hSF : S ≤ F)
    (hind : ∀ ⦃x y⦄, G.Adj x y → x ∈ S.support → y ∈ S.support → S.Adj x y)
    (A : Set V) (hAS : A ⊆ S.support)
    (hside : ∀ ⦃x y⦄, S.Adj x y → (x ∈ A ↔ y ∉ A))
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A}).IsAcyclic) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity D x ≤ 2 := by
  classical
  let R := F \ S
  let H := G \ R
  have hRF : R ≤ F := sdiff_le
  have hRG : R ≤ G := hRF.trans hFG
  have hRm : ∀ x, (R.neighborSet x).Subsingleton := by
    intro x a ha b hb
    exact hm x (hRF ha) (hRF hb)
  have hRe : ∀ ⦃x y⦄, R.Adj x y → Even (Nat.card (G.neighborSet x)) := by
    intro x y hxy; exact he (hRF hxy)
  have hRA : ∀ ⦃x y⦄, R.Adj x y → x ∉ A := by
    intro x y hxy hxA
    obtain ⟨z,hxz⟩ := hAS hxA
    have hyz : y=z := hm x (hRF hxy) (hSF hxz)
    exact hxy.2 (hyz.symm ▸ hxz)
  have hSH : S ≤ H := by
    intro x y hxy
    exact ⟨hFG (hSF hxy),fun hh ↦ hh.2 hxy⟩
  have hSm : ∀ x, (S.neighborSet x).Subsingleton := by
    intro x a ha b hb
    exact hm x (hSF ha) (hSF hb)
  have hSi : ∀ ⦃x y⦄, H.Adj x y → x ∈ S.support → y ∈ S.support → S.Adj x y := by
    intro x y hxy hx hy
    exact hind hxy.1 hx hy
  have hdiff : H \ S=G \ F := by
    ext x y
    simp only [H,R,sdiff_adj]
    constructor
    · rintro ⟨⟨hG,hR⟩,hS⟩
      exact ⟨hG,fun hF ↦ hR ⟨hF,hS⟩⟩
    · rintro ⟨hG,hF⟩
      exact ⟨⟨hG,fun hh ↦ hF hh.1⟩,fun hS ↦ hF (hSF hS)⟩
  have ho (x : V) : Odd (Nat.card ((G \ F).neighborSet x)) := by
    apply Nat.not_even_iff_odd.mp
    intro hx
    obtain ⟨hev,hempty⟩ := (even_after_matching_iff G F hFG hm he x).mp hx
    exact (hcover x hev).ne_empty hempty
  obtain ⟨D,hD,hDn,hDb⟩ := PendantCompletion.exists_normal_decomposition (G \ F)
  have hDq (x : V) : endpointMultiplicity D x=1 := (hDb x).2.mpr (by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho x)
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hDn
  have hq (x : V) : T.quota x=1 := (hTq x).trans (hDq x)
  have hcard : 2*D.card=Fintype.card V := by
    have hh := RootEnergy.sum_quota T
    simp only [hq,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hh
    omega
  have hex : ∃ U : TrailFamily H D.card, (∀ i, (U.walk i).IsPath) ∧
      ∀ x, U.quota x=if x ∈ S.support then (if x ∈ A then 2 else 0) else 1 := by
    have hbase : ∃ T' : TrailFamily (H \ S) D.card,
        (∀ i, (T'.walk i).IsPath) ∧ ∀ x, T'.quota x=1 := by
      rw [hdiff]
      exact ⟨T,hT,hq⟩
    obtain ⟨T',hT',hq'⟩ := hbase
    exact restore_induced_seed_matching H S hSH hSm hSi A hside T' hT' hq' 
  obtain ⟨U,hU,hUq⟩ := hex
  have hUb (x : V) : U.quota x ≤ 2 := by rw [hUq]; split_ifs <;> omega
  have hUA (x : V) (hx : x ∈ A) : 0 < U.quota x := by simp only [hUq,hAS hx,hx,↓reduceIte]; omega
  obtain ⟨P,hP,hPb,_⟩ := restore_matching_guarded G R hRG hRm hRe A hRA hf U hU hUb hUA
  obtain ⟨E,hE,hEc,hEn,hEq⟩ := path_family_partition_quota_le P hP
  exact ⟨E,hE,by omega,hEn,fun x ↦ (hEq x).trans (hPb x)⟩

end Erdos583SeedMatchingRestorationDevelopment
