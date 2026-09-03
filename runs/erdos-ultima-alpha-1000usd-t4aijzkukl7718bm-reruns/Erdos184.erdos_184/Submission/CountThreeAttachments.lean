import Submission.CountThreeAttachmentData

/-! Verified finite attachment completeness and interpretation as graph decompositions.
Arbitrary-graph outside classification is not asserted here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CountThreeAttachmentData
open CyclePairCertificate
set_option maxHeartbeats 1000000

lemma enumerate_complete (m : Model) (pre suf : List (Finset (Fin 4)))
    (choices : List (List (Finset (Fin 4))))
    (hchoices : List.Forall₂ (fun x xs => x ∈ xs) suf choices)
    (hvalid : valid m (pre.reverse ++ suf) = true) :
    pre.reverse ++ suf ∈ enumerate m pre choices := by
  induction hchoices generalizing pre with
  | nil => simpa [enumerate] using hvalid
  | @cons a b as bs hab ht ih =>
    apply List.mem_flatMap.mpr
    refine ⟨a,hab,?_⟩
    have heq : (a :: pre).reverse ++ as = pre.reverse ++ a :: as := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    have hh := ih (a :: pre) (by rwa [heq])
    rwa [heq] at hh

lemma config_mem {m : Model} {config : List (Finset (Fin 4))}
    (hchoices : List.Forall₂ (fun x xs => x ∈ xs) config m.options)
    (hvalid : valid m config = true) : config ∈ configs m := by
  have hh := enumerate_complete m [] config m.options hchoices (by simpa using hvalid)
  simpa only [List.reverse_nil,List.nil_append,configs] using hh

lemma certificate_sound (m : Model) (c : Certificate)
    (hc : checkCertificate m c = true) :
    let G := fromEdgeSet (fullEdges m c.config : Set (Sym2 (Fin 11)))
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  have hp : Function.Injective c.first.vertex ∧ Function.Injective c.second.vertex ∧
      Disjoint (cycleEdges c.first.vertex) (cycleEdges c.second.vertex) ∧
      cycleEdges c.first.vertex ∪ cycleEdges c.second.vertex = fullEdges m c.config :=
    of_decide_eq_true hc
  obtain ⟨D,hD,hdec,hcard⟩ := decomposition_of_edge_certificate (fullEdges m c.config)
    c.first.vertex c.second.vertex hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  refine ⟨D,?_,hdec,hcard⟩
  intro H hH
  refine ⟨(hD H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hD H hH).2 v

/-- Every allowable attachment to one of the twelve normalized outside models
has a genuine two-cycle partition. -/
lemma model_completion (i : Fin 12) (config : List (Finset (Fin 4)))
    (hchoices : List.Forall₂ (fun x xs => x ∈ xs) config (model i).options)
    (hvalid : valid (model i) config = true) :
    let G := fromEdgeSet (fullEdges (model i) config : Set (Sym2 (Fin 11)))
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  have hm := config_mem hchoices hvalid
  rw [configs_checked] at hm
  obtain ⟨c,hc,hcfg⟩ := List.mem_map.mp hm
  have hcheck : checkCertificate (model i) c = true := by
    apply List.all_eq_true.mp (show (records i).toList.all (checkCertificate (model i)) = true from by
      simpa using certificates_checked i) c hc
  have hh := certificate_sound (model i) c hcheck
  rwa [hcfg] at hh

end Erdos184.CountThreeAttachmentData
