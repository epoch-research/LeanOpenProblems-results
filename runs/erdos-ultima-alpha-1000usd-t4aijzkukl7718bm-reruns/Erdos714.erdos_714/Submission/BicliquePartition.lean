import Submission.ColoredTensorThinning

/-! Exact relative edge-density bounds for hosts partitioned into large
complete bipartite blocks. These are construction obstructions, not Erdős 714. -/

set_option maxHeartbeats 3000000
noncomputable section
open Classical SimpleGraph Finset
namespace Erdos714BicliquePartition

variable {A B : Type*}

def completeIso (e : A ≃ A) (f : B ≃ B) :
    completeBipartiteGraph A B ≃g completeBipartiteGraph A B where
  toEquiv := e.sumCongr f
  map_rel_iff' := by intro p q; cases p <;> cases q <;> simp

lemma edge_rep (e : (completeBipartiteGraph A B).edgeSet) :
    ∃ a b, e.val=s(Sum.inl a,Sum.inr b) := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    cases p with
    | inl a =>
      cases q with
      | inl a' => simp at he
      | inr b => exact ⟨a,b,rfl⟩
    | inr b =>
      cases q with
      | inl a => exact ⟨a,b,Sym2.eq_swap⟩
      | inr b' => simp at he

lemma complete_edge_transitive [Fintype A] [Fintype B] :
    Erdos714GraphAveraging.EdgeTransitive (completeBipartiteGraph A B) := by
  intro e f
  obtain ⟨a,b,he⟩ := edge_rep e
  obtain ⟨c,d,hf⟩ := edge_rep f
  refine ⟨completeIso (Equiv.swap a c) (Equiv.swap b d),?_⟩
  apply Subtype.ext
  change Sym2.map (completeIso (Equiv.swap a c) (Equiv.swap b d)) e.val=f.val
  rw [he,hf]
  simp [completeIso]

lemma complete_density [Fintype A] [Fintype B] (H : SimpleGraph (A ⊕ B)) (r t : ℕ)
    (hA : t ≤ Fintype.card A) (hB : t ≤ Fintype.card B)
    (hH : H ≤ completeBipartiteGraph A B)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    t^2*H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) *
        (Fintype.card A*Fintype.card B) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin t) (β := A) (by simpa using hA)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin t) (β := B) (by simpa using hB)
  let c : Copy (completeBipartiteGraph (Fin t) (Fin t)) (completeBipartiteGraph A B) :=
    ⟨⟨e.sumMap f,by intro p q hpq; cases p <;> cases q <;> simp_all⟩,(e.sumMap f).injective⟩
  simpa only [Erdos714GraphAveraging.complete_bipartite_edges] using
    Erdos714GraphAveraging.biclique_bound H (completeBipartiteGraph A B) r t c hH hfree
      complete_edge_transitive

variable {V I : Type*} [Fintype V] [Fintype I]
variable {L R : I → Type*} [∀ i, Fintype (L i)] [∀ i, Fintype (R i)]

def edgeMap (G : SimpleGraph V) (c : ∀ i, (completeBipartiteGraph (L i) (R i)).Copy G) :
    (Σ i, (completeBipartiteGraph (L i) (R i)).edgeSet) → G.edgeSet :=
  fun p => (c p.1).mapEdgeSet p.2

private lemma comap_edge {X Y : Type*} (H : SimpleGraph Y) (f : X → Y) (e : Sym2 X) :
    Sym2.map f e ∈ H.edgeSet ↔ e ∈ (H.comap f).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf x y => rfl

omit [Fintype V] in
private lemma selected_local_card (H : SimpleGraph V) (G : SimpleGraph V)
    (c : (completeBipartiteGraph A B).Copy G) [Fintype A] [Fintype B] :
    Fintype.card {e : (completeBipartiteGraph A B).edgeSet //
      Sym2.map c e.val ∈ H.edgeSet} =
      ((completeBipartiteGraph A B) ⊓ H.comap c).edgeFinset.card := by
  rw [edgeFinset_card]
  apply Fintype.card_congr
  refine Equiv.ofBijective (fun e => (⟨e.val.val,?_⟩ :
    ((completeBipartiteGraph A B) ⊓ H.comap c).edgeSet)) ?_
  · rw [edgeSet_inf]
    exact ⟨e.val.property,(comap_edge H c e.val.val).mp e.property⟩
  · constructor
    · intro e f hef
      apply Subtype.ext
      apply Subtype.ext
      change e.val.val=f.val.val
      exact congrArg (fun z : ((completeBipartiteGraph A B) ⊓ H.comap c).edgeSet => z.val) hef
    · rintro ⟨e,he⟩
      have hb : e ∈ (completeBipartiteGraph A B).edgeSet := edgeSet_mono inf_le_left he
      have hs : Sym2.map c e ∈ H.edgeSet := by
        have hh := edgeSet_mono inf_le_right he
        induction e using Sym2.inductionOn with
        | hf x y => exact hh
      exact ⟨⟨⟨e,hb⟩,hs⟩,rfl⟩

/-- The partition hypothesis is a bijection on actual edges, so overlaps and
unequal block sizes cause no hidden multiplicity factor. -/
theorem density_bound (H G : SimpleGraph V)
    (c : ∀ i, (completeBipartiteGraph (L i) (R i)).Copy G)
    (hpartition : Function.Bijective (edgeMap G c))
    (r t : ℕ) (hL : ∀ i, t ≤ Fintype.card (L i)) (hR : ∀ i, t ≤ Fintype.card (R i))
    (hHG : H ≤ G) (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    t^2*H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r))*G.edgeFinset.card := by
  let K (i : I) := (completeBipartiteGraph (L i) (R i)) ⊓ H.comap (c i)
  have hlocal (i : I) : t^2*(K i).edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r))*
        (Fintype.card (L i)*Fintype.card (R i)) := by
    have hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (K i) := by
      intro hc
      exact (Erdos714GraphAveraging.free_comap _ H (c i).toEmbedding hfree)
        (hc.mono_right inf_le_right)
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using
      complete_density (K i) r t (hL i) (hR i) inf_le_left hf
  have hGcard : G.edgeFinset.card = ∑ i, Fintype.card (L i)*Fintype.card (R i) := by
    rw [edgeFinset_card,←Fintype.card_congr (Equiv.ofBijective (edgeMap G c) hpartition)]
    simp only [Fintype.card_sigma,←edgeFinset_card,Erdos714GraphAveraging.complete_bipartite_edges]
  let E (i : I) := {e : (completeBipartiteGraph (L i) (R i)).edgeSet //
    Sym2.map (c i) e.val ∈ H.edgeSet}
  let f : (Σ i, E i) → H.edgeSet := fun p => ⟨Sym2.map (c p.1) p.2.val.val,p.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have hh : edgeMap G c ⟨p.1,p.2.val⟩ = edgeMap G c ⟨q.1,q.2.val⟩ := by
        apply Subtype.ext
        change Sym2.map (c p.1) p.2.val.val=Sym2.map (c q.1) q.2.val.val
        exact congrArg Subtype.val he
      have hpq := hpartition.1 hh
      rcases p with ⟨i,p⟩
      rcases q with ⟨j,q⟩
      have hij : i=j := congrArg Sigma.fst hpq
      subst j
      have hval : p.val=q.val := by simpa using hpq
      have hp : p=q := Subtype.ext hval
      cases hp
      rfl
    · intro e
      obtain ⟨⟨i,a⟩,he⟩ := hpartition.2 ⟨e.val,edgeSet_mono hHG e.property⟩
      have hev : Sym2.map (c i) a.val=e.val := congrArg Subtype.val he
      refine ⟨⟨i,⟨a,?_⟩⟩,?_⟩
      · rw [hev]; exact e.property
      · exact Subtype.ext hev
  have hHcard : H.edgeFinset.card = ∑ i, (K i).edgeFinset.card := by
    rw [edgeFinset_card,←Fintype.card_congr (Equiv.ofBijective f hf),Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact selected_local_card H G (c i)
  rw [hHcard,hGcard,Finset.mul_sum,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hlocal i)

lemma extremal_fourth (t : ℕ) :
    (extremalNumber (2*t) (completeBipartiteGraph (Fin 4) (Fin 4)))^4 ≤ 10368*t^7 := by
  have hn : completeBipartiteGraph (Fin 4) (Fin 4) ≠ ⊥ := by
    intro he
    have hh : (completeBipartiteGraph (Fin 4) (Fin 4)).Adj (.inl 0) (.inr 0) := by simp
    rw [he] at hh
    exact hh
  obtain ⟨G,inst,hG⟩ := exists_isExtremal_free (V := Fin (2*t)) hn
  have hp := Erdos714BlockThinning.fourth_power_bound G hG.prop
  have he := card_edgeFinset_of_isExtremal_free hG
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hp he
  simp only [Nat.card_fin] at hp he
  rw [he] at hp
  simpa only [mul_pow,show (2:ℕ)^7=128 from rfl,
    ←mul_assoc,show (81:ℕ)*128=10368 from rfl] using hp

/-- A convenient purely integral form: the retained density is O(t^(-1/4)). -/
theorem fourth_density_bound (H G : SimpleGraph V)
    (c : ∀ i, (completeBipartiteGraph (L i) (R i)).Copy G)
    (hpartition : Function.Bijective (edgeMap G c))
    (t : ℕ) (hL : ∀ i, t ≤ Fintype.card (L i)) (hR : ∀ i, t ≤ Fintype.card (R i))
    (hHG : H ≤ G) (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    t*H.edgeFinset.card^4 ≤ 10368*G.edgeFinset.card^4 := by
  by_cases ht : t=0
  · simp [ht]
  have hp := Nat.pow_le_pow_left (density_bound H G c hpartition 4 t hL hR hHG hfree) 4
  rw [mul_pow,mul_pow,←pow_mul] at hp
  have hb := hp.trans (Nat.mul_le_mul_right (G.edgeFinset.card^4) (extremal_fourth t))
  apply Nat.le_of_mul_le_mul_left (c := t^7) _ (pow_pos (Nat.pos_of_ne_zero ht) 7)
  convert hb using 1 <;> ring

end Erdos714BicliquePartition
#print axioms Erdos714BicliquePartition.density_bound

#print axioms Erdos714BicliquePartition.fourth_density_bound
