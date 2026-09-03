import Submission.Work

/-! Endpoint separation in all-odd normal path systems. -/
open SimpleGraph Erdos583Work
open Erdos583Work.NormalTrailSystem Erdos583Work.TrailNormalization
namespace Erdos583EndpointUnpairingDevelopment
open scoped Classical
set_option maxHeartbeats 1200000
set_option Elab.async false

lemma separate_nonadjacent_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : NormalTrailSystem G k) (hp : ∀ i, (T.walk i).IsPath)
    (a b : V) (hab : a ≠ b) (hnadj : ¬G.Adj a b) :
    ∃ U : NormalTrailSystem G k, (∀ i, (U.walk i).IsPath) ∧
      U.score = T.score ∧ owner U a ≠ owner U b := by
  classical
  by_cases hown : owner T a = owner T b
  · let i := owner T a
    have ha : a = T.start i ∨ a = T.finish i := owner_spec T a
    have hb : b = T.start i ∨ b = T.finish i := by
      simpa only [i, hown] using owner_spec T b
    obtain ⟨S,hS,hSa,_,hSe⟩ := orient_receiver T i a ha
    have hSp : ∀ j, (S.walk j).IsPath := by
      apply S.score_eq_edges_add_iff.mp
      rw [hS]
      exact T.score_eq_edges_add_iff.mpr hp
    have hbS : b = S.start i ∨ b = S.finish i := by
      obtain ⟨h1,h2⟩ := SingletonRotation.endpoints_of_path_subgraph S i (T.walk i)
        (hp i) (Walk.not_nil_of_ne (T.endpoints_ne i)) (hSe i)
      exact hb.elim (fun h => h ▸ h1) (fun h => h ▸ h2)
    have hSb : S.finish i = b := by
      rcases hbS with h | h
      · exact (hab (hSa.symm.trans h.symm)).elim
      · exact h.symm
    let p : G.Walk a b := (S.walk i).copy hSa hSb
    have hpp : p.IsPath := by simpa only [p,Walk.isPath_copy] using hSp i
    have hpe : (S.walk i).toSubgraph = p.toSubgraph :=
      (NormalTrailSystem.walk_copy_subgraph _ _ _).symm
    cases hpdef : p with
    | nil => exact (hab rfl).elim
    | @cons a y b h q =>
      rw [hpdef] at hpp hpe
      have hqn : ¬q.Nil := fun hn => hnadj (hn.eq ▸ h)
      obtain ⟨U,hU,hUi⟩ := InducedBuffer.shorten_path_member_nonadj S i h q hqn hpp hnadj hpe
      have hUp : ∀ j, (U.walk j).IsPath := by
        apply U.score_eq_edges_add_iff.mp
        rw [hU,hS]
        exact T.score_eq_edges_add_iff.mpr hp
      have hbU : owner U b = i := (endpoint_iff_owner U b i).mp
        (SingletonRotation.endpoints_of_path_subgraph U i q hpp.of_cons hqn hUi).2
      refine ⟨U,hUp,hU.trans hS,?_⟩
      intro he
      have hae := (endpoint_iff_owner U a i).mpr (he.trans hbU)
      have hmem : a ∈ (U.walk i).support := hae.elim
        (fun h => h.symm ▸ (U.walk i).start_mem_support)
        (fun h => h.symm ▸ (U.walk i).end_mem_support)
      rw [←Walk.mem_verts_toSubgraph,hUi,Walk.mem_verts_toSubgraph] at hmem
      exact (Walk.cons_isPath_iff h q).mp hpp |>.2 hmem
  · exact ⟨T,hp,rfl,hown⟩

end Erdos583EndpointUnpairingDevelopment
