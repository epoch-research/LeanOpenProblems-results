import Submission.WeightedPaths

/-! Total-weight bounds obtained by weighted vertex deletion. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.WeightedPaths
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 600000

lemma weight_map {U : Type*} {A : SimpleGraph U} (f : A →g G) (w : Sym2 V → ℝ)
    {a b : U} (p : A.Walk a b) :
    walkWeight w (p.map f) = walkWeight (w ∘ Sym2.map f) p := by
  simp [walkWeight,Walk.edges_map,List.map_map]

lemma star_sum_eq_incidence [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ) (u : V) :
    (∑ x, star G w u x) = ∑ e ∈ G.incidenceFinset u, w e := by
  have hn : G.neighborFinset u = Finset.univ.filter (G.Adj u) := by ext; simp
  calc
    _ = ∑ x ∈ G.neighborFinset u, w s(u,x) := by simp [hn,Finset.sum_filter,star]
    _ = _ := by
      apply Finset.sum_bij (fun x _ => s(u,x))
      · intro x hx
        simpa using hx
      · intro a _ b _ hab
        exact Sym2.congr_right.mp hab
      · intro e he
        induction e using Sym2.inductionOn with | _ a b =>
          obtain ⟨hab,hua | hub⟩ := (G.mk'_mem_incidenceSet_iff).mp ((G.mem_incidenceFinset u _).mp he)
          · subst a
            exact ⟨b,by simpa using hab,rfl⟩
          · subst b
            exact ⟨a,by simpa using hab.symm,Sym2.eq_swap⟩
      · intro x hx; rfl

lemma sum_edges_delete_vertex [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ) (u : V) :
    (∑ e ∈ (G.induce ({u}ᶜ : Set V)).edgeFinset, w (Sym2.map Subtype.val e)) +
      (∑ x, star G w u x) = ∑ e ∈ G.edgeFinset, w e := by
  let s : Set V := {u}ᶜ
  have hmap : (G.induce s).edgeFinset.map (Function.Embedding.subtype (· ∈ s)).sym2Map =
      G.edgeFinset \ G.incidenceFinset u := by
    rw [G.map_edgeFinset_induce]
    ext e
    induction e using Sym2.inductionOn with | _ a b =>
      simp only [Finset.mem_inter,Finset.mem_sdiff,mem_incidenceFinset,
        mk'_mem_incidenceSet_iff,mem_edgeFinset,mem_edgeSet,Finset.mk_mem_sym2_iff,
        Set.mem_toFinset,s,Set.mem_compl_iff,Set.mem_singleton_iff]
      tauto
  have hh := Finset.sum_sdiff (f := w) (G.incidenceFinset_subset u)
  rw [← hmap,Finset.sum_map] at hh
  rw [star_sum_eq_incidence]
  exact hh

/-- The nonnegative weighted cycle/edge inequalities give a linear total-weight bound. -/
lemma sum_edges_le_card [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (he : ∀ e ∈ G.edgeSet, w e ≤ 1)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    (∑ e ∈ G.edgeFinset, w e) ≤ Fintype.card V := by
  generalize hcard : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    cases isEmpty_or_nonempty V with
    | inl hV =>
      haveI := hV
      have hF : G.edgeFinset = ∅ := by
        ext e
        induction e using Sym2.inductionOn with | _ a b => exact isEmptyElim a
      rw [hF,Finset.sum_empty]
      positivity
    | inr hV =>
      haveI := hV
      obtain ⟨u,hu⟩ := exists_star_sum_le_one G w hn he hc
      let S : Set V := {u}ᶜ
      let A := G.induce S
      let w' : Sym2 S → ℝ := w ∘ Sym2.map Subtype.val
      let f : A →g G := (SimpleGraph.Embedding.induce S).toHom
      have hnA : Fintype.card S < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := u) (by simp [S])
      have hedge (e : Sym2 S) (he : e ∈ A.edgeSet) : Sym2.map Subtype.val e ∈ G.edgeSet := by
        induction e using Sym2.inductionOn with | _ a b => exact he
      have hcn : ∀ x (p : A.Walk x x), p.IsCycle → walkWeight w' p ≤ 1 := by
        intro x p hp
        have hh := hc x.val (p.map f) (hp.map Subtype.val_injective)
        simpa only [weight_map] using hh
      have hb := ih _ hnA A w' (fun e he => hn _ (hedge e he))
        (fun e he' => he _ (hedge e he')) hcn rfl
      have hs := sum_edges_delete_vertex G w u
      have hcnat : Fintype.card S + 1 ≤ n := by omega
      have hcr : (Fintype.card S : ℝ) + 1 ≤ n := by exact_mod_cast hcnat
      change (∑ e ∈ A.edgeFinset, w' e) + (∑ x, star G w u x) = _ at hs
      linarith

end Erdos184.WeightedPaths
