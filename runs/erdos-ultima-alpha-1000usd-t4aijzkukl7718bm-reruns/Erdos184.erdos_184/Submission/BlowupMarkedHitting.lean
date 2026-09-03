import Submission.LinearFamilyEfficient
import Submission.HamiltonReduction

/-!
A marked-hitting decomposition in an unbounded-degree family. Reflections
in two vertex parts move every Hamilton piece onto an edge of the original
marked Hamilton cycle, for every positive order.
This is a special family, not a settlement of Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.LinearFamilyGap.MarkedHitting
open Efficient

variable {q : ℕ}

/-- Two reflections on two vertex parts. Unlike multiplication by two,
these are permutations in every order, including even order. -/
def relabel : Equiv.Perm (Fin 6 × ZMod q) where
  toFun v := (v.1, if v.1 = 1 then -v.2 else if v.1 = 3 then 1-v.2 else v.2)
  invFun v := (v.1, if v.1 = 1 then -v.2 else if v.1 = 3 then 1-v.2 else v.2)
  left_inv := by
    rintro ⟨i,x⟩
    by_cases h1 : i = 1 <;> by_cases h3 : i = 3 <;> simp [h1,h3]
  right_inv := by
    rintro ⟨i,x⟩
    by_cases h1 : i = 1 <;> by_cases h3 : i = 3 <;> simp [h1,h3]

lemma relabel_fst (v : Fin 6 × ZMod q) : (relabel v).1 = v.1 := rfl

lemma relabel_zero (x : ZMod q) : relabel (0,x) = (0,x) := by simp [relabel]
lemma relabel_one (x : ZMod q) : relabel (1,x) = (1,-x) := by simp [relabel]
lemma relabel_two (x : ZMod q) : relabel (2,x) = (2,x) := by simp [relabel]
lemma relabel_three (x : ZMod q) : relabel (3,x) = (3,1-x) := by simp [relabel]

lemma relabel_adj (u v : Fin 6 × ZMod q) :
    (G (ZMod q)).Adj (relabel u) (relabel v) ↔ (G (ZMod q)).Adj u v := Iff.rfl

variable [NeZero q]

def A (t : ZMod q) : SimpleGraph (Fin 6 × ZMod q) :=
  (F t).comap (relabel)

lemma A_le (t : ZMod q) : A t ≤ G (ZMod q) := by
  intro u v h
  exact (relabel_adj u v).mp (F_le t h)

lemma A_connected (t : ZMod q) : (A t).Connected :=
  (SimpleGraph.Iso.comap (relabel) (F t)).connected_iff.mpr (F_connected t)

lemma A_regular (t : ZMod q) : (A t).IsRegularOfDegree 2 := by
  intro v
  have hd := (SimpleGraph.Iso.comap (relabel) (F t)).degree_eq v
  have hr := F_regular t (relabel v)
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hr ⊢
  exact hd.symm.trans hr

/-- At least one of -t and 1-t is a double: use the parity of the
canonical natural representative of -t. -/
lemma double_or_double (t : ZMod q) :
    (∃ x : ZMod q, x+x = -t) ∨ (∃ x : ZMod q, x+x = 1-t) := by
  rcases Nat.even_or_odd (-t).val with ⟨k,hk⟩ | ⟨k,hk⟩
  · left
    refine ⟨(k : ZMod q),?_⟩
    have hz := ZMod.natCast_zmod_val (-t)
    rw [hk,Nat.cast_add] at hz
    exact hz
  · right
    refine ⟨(k : ZMod q)+1,?_⟩
    have hz := ZMod.natCast_zmod_val (-t)
    rw [hk,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hz
    linear_combination hz

/-- Every relabeled Hamilton piece meets the original marked Hamilton cycle. -/
lemma common_edge (t : ZMod q) :
    ∃ u v, (A t).Adj u v ∧ (F (q := q) 0).Adj u v := by
  rcases double_or_double t with ⟨x,hx⟩ | ⟨x,hx⟩
  · refine ⟨(0,x),(1,x),?_,?_⟩
    · change (F t).Adj (relabel (0,x)) (relabel (1,x))
      rw [relabel_zero,relabel_one]
      apply Or.inl
      apply Prod.ext
      · rfl
      · dsimp [next,shift]
        linear_combination hx
    · apply Or.inl
      simp [next,shift]
  · refine ⟨(2,x),(3,x),?_,?_⟩
    · change (F t).Adj (relabel (2,x)) (relabel (3,x))
      rw [relabel_two,relabel_three]
      apply Or.inl
      apply Prod.ext
      · rfl
      · dsimp [next,shift]
        linear_combination hx
    · apply Or.inl
      simp [next,shift]

def Q (t : ZMod q) : (G (ZMod q)).Subgraph :=
  SimpleGraph.toSubgraph (A t) (A_le t)

lemma Q_cycles (t : ZMod q) :
    (Q t).coe.Connected ∧ (Q t).coe.IsRegularOfDegree 2 := by
  constructor
  · apply (Subgraph.spanningCoeEquivCoeOfSpanning (Q t)
      (SimpleGraph.toSubgraph.isSpanning (A t) (A_le t))).connected_iff.mp
    exact A_connected t
  · intro v
    rw [Subgraph.coe_degree,← Subgraph.degree_spanningCoe]
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using A_regular t v.val

lemma Q_injective : Function.Injective (Q (q := q)) := by
  intro t s heq
  obtain ⟨u,v,ht,_⟩ := common_edge t
  have ht' : (Q t).Adj u v := ht
  have hs : (Q s).Adj u v := heq ▸ ht' 
  exact edge_parameter ht hs

noncomputable def D : Finset (G (ZMod q)).Subgraph :=
  Finset.univ.image (Q)

lemma mem_D (H : (G (ZMod q)).Subgraph) :
    H ∈ D ↔ ∃ t, H = Q t := by simp [D,eq_comm]

lemma D_card : (D (q := q)).card = q := by
  rw [D,Finset.card_image_of_injective _ (Q_injective)]
  simp only [Finset.card_univ,ZMod.card]

lemma D_cycles :
    ∀ H ∈ D (q := q), H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  obtain ⟨t,rfl⟩ := (mem_D H).mp hH
  exact Q_cycles t

lemma D_decomposition : IsDecomposition (G (ZMod q)) (D) := by
  constructor
  · intro H hH K hK hne
    obtain ⟨t,rfl⟩ := (mem_D H).mp hH
    obtain ⟨s,rfl⟩ := (mem_D K).mp hK
    change Disjoint (Q t).edgeSet (Q s).edgeSet
    rw [Set.disjoint_left]
    intro e ht hs
    induction e using Sym2.ind with
    | h u v =>
      have ht' : (F t).Adj (relabel u) (relabel v) := ht
      have hs' : (F s).Adj (relabel u) (relabel v) := hs
      exact hne (congrArg (Q) (edge_parameter ht' hs'))
  · ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_iUnion,exists_prop]
      constructor
      · rintro ⟨H,_,he⟩
        exact H.edgeSet_subset he
      · intro he
        obtain ⟨t,ht⟩ := Efficient.edge_covered (relabel u) (relabel v)
          ((relabel_adj u v).mpr he)
        exact ⟨Q t,(mem_D _).mpr ⟨t,rfl⟩,ht⟩

lemma D_hitting :
    ∀ H ∈ D, (H.edgeSet ∩ (F (q := q) 0).edgeSet).Nonempty := by
  intro H hH
  obtain ⟨t,rfl⟩ := (mem_D H).mp hH
  obtain ⟨u,v,ht,hr⟩ := common_edge t
  exact ⟨s(u,v),ht,hr⟩

/-- For every positive q, the blowup admits q Hamilton pieces all hitting the
specified marked Hamilton cycle. Their number is also minimum. -/
theorem marked_hamilton_decomposition_all_orders :
    ∃ D : Finset (G (ZMod q)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G (ZMod q)) D ∧
      (∀ H ∈ D, (H.edgeSet ∩ (F (q := q) 0).edgeSet).Nonempty) ∧ D.card = q :=
  ⟨D,D_cycles,D_decomposition,D_hitting,D_card⟩

/-- Backward-compatible odd-order corollary of the stronger all-order result. -/
theorem marked_hamilton_decomposition (_hq : Odd q) :
    ∃ D : Finset (G (ZMod q)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G (ZMod q)) D ∧
      (∀ H ∈ D, (H.edgeSet ∩ (F (q := q) 0).edgeSet).Nonempty) ∧ D.card = q :=
  marked_hamilton_decomposition_all_orders

def blue : SimpleGraph (Fin 6 × ZMod q) := G (ZMod q) \ F 0

lemma blue_regular : (blue (q := q)).IsRegularOfDegree (2*(q-1)) := by
  intro v
  have hd := degree_sdiff_of_le (F_le (0 : ZMod q)) v
  have hg := graph_regular (ZMod q) v
  have hr := F_regular (0 : ZMod q) v
  rw [ZMod.card] at hg
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hg hr ⊢
  change Nat.card ((G (ZMod q) \ F 0).neighborSet v) = _
  omega

lemma blue_edge_card : (blue (q := q)).edgeFinset.card = 6*q*(q-1) := by
  have hs := (blue (q := q)).sum_degrees_eq_twice_card_edges
  have hd (v : Fin 6 × ZMod q) : (blue (q := q)).degree v = 2*(q-1) := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using blue_regular (q := q) v
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Fintype.card_prod,Fintype.card_fin,ZMod.card] at hs
  nlinarith

/-- Even allowing overlaps, covering the unmarked graph by forests needs
at least q forests when q>1. Thus the marked-hitting construction above
handles arbitrarily large unmarked arboricity. -/
theorem forest_cover_lower_bound (hq : 1 < q) (k : ℕ)
    (J : Fin k → SimpleGraph (Fin 6 × ZMod q)) (hf : ∀ i, (J i).IsAcyclic)
    (hcover : ∀ u v, (blue (q := q)).Adj u v → ∃ i, (J i).Adj u v) : q ≤ k := by
  have hsub : (blue (q := q)).edgeFinset ⊆ Finset.univ.biUnion (fun i => (J i).edgeFinset) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨i,hi⟩ := hcover u v (mem_edgeFinset.mp he)
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,mem_edgeFinset.mpr hi⟩
  have hsum := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hbound : ∑ i : Fin k, (J i).edgeFinset.card ≤ k*(6*q-1) := by
    calc
      ∑ i : Fin k, (J i).edgeFinset.card ≤ ∑ _i : Fin k, (6*q-1) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := forest_edge_card_lt_vertex_card (J i) (hf i)
        simp only [Fintype.card_prod,Fintype.card_fin,ZMod.card] at hh
        simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hh ⊢
        omega
      _ = k*(6*q-1) := by simp
  have hh := hsum.trans hbound
  have hc := blue_edge_card (q := q)
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hh hc
  rw [hc] at hh
  by_contra! hk
  have hkle : k ≤ q-1 := by omega
  have hmul := Nat.mul_le_mul_right (6*q-1) hkle
  have hsubq : 6*q-1+1 = 6*q := by omega
  have hqpos : 0 < q-1 := by omega
  nlinarith

end Erdos184.LinearFamilyGap.MarkedHitting
