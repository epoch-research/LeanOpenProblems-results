import Submission.ButterflyContiguous

/-! The finite alternating order of four outer vertices on two triangles. -/
namespace Erdos583ButterflyPairsDevelopment
open SimpleGraph Erdos583Work
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
set_option maxHeartbeats 2400000
set_option Elab.async false

def paired (u v : Fin 4) : Prop :=
  ∃ i : Fin 6, s(baseSource i,baseTarget i)=s(outer u,outer v)

instance (u v : Fin 4) : Decidable (paired u v) := by unfold paired; infer_instance

lemma opposite_pairs_vec : ∀ u v w z : Fin 4,
    [u,v,w,z].Nodup → ¬paired u v → ¬paired v w → ¬paired w z →
    paired u w ∧ paired v z := by decide

lemma core_relabel_vec : ∀ u v w z : Fin 4,
    [u,v,w,z].Nodup → ¬paired u v → ¬paired v w → ¬paired w z →
    ({s(0,1),s(1,2),s(2,0),s(0,3),s(3,4),s(4,0)} : Set (Sym2 (Fin 5)))=
      {s(0,outer u),s(0,outer v),s(0,outer w),s(0,outer z),s(outer u,outer w),s(outer v,outer z)} := by
  intro u v w z hn huv hvw hwz
  ext e
  revert u v w z e
  decide

lemma base_coreEdges_eq {V : Type*} (f : Fin 5 → V) :
    coreEdges baseSource baseTarget f=
      {s(f 0,f 1),s(f 1,f 2),s(f 2,f 0),s(f 0,f 3),s(f 3,f 4),s(f 4,f 0)} := by
  ext e
  simp [coreEdges,Fin.exists_fin_succ,baseSource,baseTarget,eq_comm]

lemma mapped_core_relabel {V : Type*} (f : Fin 5 → V) {u v w z : Fin 4}
    (hn : [u,v,w,z].Nodup) (huv : ¬paired u v) (hvw : ¬paired v w) (hwz : ¬paired w z) :
    coreEdges baseSource baseTarget f=
      {s(f 0,f (outer u)),s(f 0,f (outer v)),s(f 0,f (outer w)),s(f 0,f (outer z)),
        s(f (outer u),f (outer w)),s(f (outer v),f (outer z))} := by
  rw [base_coreEdges_eq]
  have hh := congrArg (fun S : Set (Sym2 (Fin 5)) ↦ Sym2.map f '' S) (core_relabel_vec u v w z hn huv hvw hwz)
  simpa only [Set.image_insert_eq,Set.image_singleton,Sym2.map_mk] using hh

lemma hub_adj {V : Type*} {G : SimpleGraph V} (f : Fin 5 → V)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i))) (u : Fin 4) : G.Adj (f 0) (f (outer u)) := by
  fin_cases u
  · exact ha 0
  · exact (ha 2).symm
  · exact ha 3
  · exact (ha 5).symm

lemma paired_adj {V : Type*} {G : SimpleGraph V} (f : Fin 5 → V)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i))) {u v : Fin 4} (h : paired u v) :
    G.Adj (f (outer u)) (f (outer v)) := by
  obtain ⟨i,hi⟩ := h
  rcases Sym2.eq_iff.mp hi with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · simpa only [hu,hv] using ha i
  · simpa only [hu,hv] using (ha i).symm

end Erdos583ButterflyPairsDevelopment
