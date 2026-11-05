import Submission.Chain

/-!
# Compactness: from finite induced subgraphs to the whole graph
-/

open SimpleGraph

namespace Erdos74Aux

variable {V : Type*}

/-- de Bruijn–Erdős type compactness for colorings (via Tychonoff). -/
theorem colorable_of_finite_induce (G : SimpleGraph V) (n : ℕ) (hn : 0 < n)
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable n) : G.Colorable n := by
  classical
  let ι := {p : V × V // G.Adj p.1 p.2}
  let t : ι → Set (V → Fin n) := fun p => {c | c p.1.1 ≠ c p.1.2}
  have htc : ∀ i, IsClosed (t i) := by
    intro i
    have hcont : Continuous (fun c : V → Fin n => (c i.1.1, c i.1.2)) := by fun_prop
    exact (isClosed_discrete {q : Fin n × Fin n | q.1 ≠ q.2}).preimage hcont
  have hne : (⋂ i, t i).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed t htc (by simpa using hemp)
    let s : Finset V := u.biUnion (fun i => {i.1.1, i.1.2})
    obtain ⟨col⟩ := h s
    let c : V → Fin n := fun v => if hv : v ∈ s then col ⟨v, hv⟩ else ⟨0, hn⟩
    have hc : c ∈ Set.univ ∩ ⋂ i ∈ u, t i := by
      refine ⟨Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter]
      intro i hi
      have h1 : i.1.1 ∈ s := Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩
      have h2 : i.1.2 ∈ s := Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩
      show c i.1.1 ≠ c i.1.2
      simp only [c, h1, h2, dif_pos]
      exact col.valid (by simpa using i.2)
    rw [hu] at hc
    exact hc
  obtain ⟨c, hc⟩ := hne
  refine ⟨Coloring.mk c (fun {a b} hab => ?_)⟩
  exact Set.mem_iInter.mp hc ⟨(a, b), hab⟩

/-- Transfer of hitting sets to induced subgraphs. -/
lemma hits_induce {G : SimpleGraph V} (s : Set V) {F : Finset (Sym2 V)} {L : ℕ}
    (hF : HitsShortOdd G (F : Set (Sym2 V)) L) :
    ∃ F' : Finset (Sym2 s), F'.card ≤ F.card ∧ HitsShortOdd (G.induce s) (F' : Set (Sym2 s)) L := by
  classical
  have hinj : Function.Injective (Sym2.map (Subtype.val : s → V)) :=
    Sym2.map.injective Subtype.val_injective
  refine ⟨F.preimage (Sym2.map Subtype.val) hinj.injOn, ?_, ?_⟩
  · apply Finset.card_le_card_of_injOn (Sym2.map Subtype.val)
    · intro e he
      simpa using he
    · exact hinj.injOn
  · intro v w hodd hlen
    let f : G.induce s →g G := (Embedding.induce s).toHom
    have hodd' : Odd (w.map f).length := by simpa using hodd
    have hlen' : (w.map f).length ≤ L := by simpa using hlen
    obtain ⟨e, he, heF⟩ := hF _ (w.map f) hodd' hlen'
    rw [Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    refine ⟨e', he', ?_⟩
    simp only [Finset.coe_preimage, Set.mem_preimage, Finset.mem_coe]
    exact heF

/-- The main structural theorem: nested hitting sets for short odd closed walks force
`3`-colorability. -/
theorem colorable_of_hits (G : SimpleGraph V)
    (hhit : ∀ j, ∃ F : Finset (Sym2 V), F.card ≤ j ∧
      HitsShortOdd G (F : Set (Sym2 V)) (ell (j + 1))) :
    G.Colorable 3 := by
  apply colorable_of_finite_induce G 3 (by norm_num)
  intro s
  choose F hFcard hF using hhit
  have := fun j => hits_induce (s : Set V) (hF j)
  choose F' hF'card hF' using this
  exact chain_colorable (G.induce (s : Set V)) F' (fun j => (hF'card j).trans (hFcard j)) hF'

end Erdos74Aux
