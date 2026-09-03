import FormalConjecturesUtil

/-!
A parity-correction charge by half the odd-vertex count plus a fixed multiple
of lost support is impossible. The examples are K_(4C+3,4C+4), obtained by
vertex deletion from an even regular complete bipartite graph.
This refutes only that induction mechanism, not Erdős Problem 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.ParitySupportChargeObstruction
set_option maxHeartbeats 1000000

noncomputable def oddVertices {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => Odd (G.degree v))

lemma complement_degree_add {V : Type*} [Fintype V] {G A : SimpleGraph V}
    (hAG : A ≤ G) (v : V) : (G \ A).degree v + A.degree v = G.degree v := by
  have hn : (G \ A).neighborSet v = G.neighborSet v \ A.neighborSet v := rfl
  have hs : A.neighborSet v ⊆ G.neighborSet v := fun _ h => hAG h
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, hn]
  exact Set.ncard_diff_add_ncard_of_subset hs

/-- Isolating vertices of minimum degree d requires at least d incidences
of deleted edges per lost vertex. No parity assumption is needed. -/
lemma lost_support_incidence_bound {V : Type*} [Fintype V]
    {G A : SimpleGraph V} (hAG : A ≤ G) (d : ℕ)
    (hd : ∀ v ∈ G.support, d ≤ G.degree v) :
    d * (G.support \ A.support).ncard ≤ 2 * (G \ A).edgeSet.ncard := by
  let S := (G.support \ A.support).toFinset
  have hl : d*S.card ≤ ∑ v ∈ S, (G \ A).degree v := by
    calc
      _ = ∑ _v ∈ S, d := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have hv' := Set.mem_toFinset.mp hv
        have hz := (A.degree_eq_zero_iff_notMem_support v).mpr hv'.2
        have hh := complement_degree_add hAG v
        have hb := hd v hv'.1
        simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          at hz hh hb ⊢
        omega
  have hu := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (f := fun v => (G \ A).degree v) (by intros; omega)
  have hs := (G \ A).sum_degrees_eq_twice_card_edges
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hs
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hu hs ⊢
  have hc : S.card = (G.support \ A.support).ncard := by
    exact (Set.ncard_eq_toFinset_card' _).symm
  rw [hc] at hl
  exact hl.trans (hu.trans_eq hs)

lemma complete_degree_left (m n : ℕ) (v : Fin m) :
    (completeBipartiteGraph (Fin m) (Fin n)).degree (Sum.inl v) = n := by
  have hn : (completeBipartiteGraph (Fin m) (Fin n)).neighborFinset (.inl v) =
      Finset.univ.map Function.Embedding.inr := by
    ext x
    cases x <;> simp [completeBipartiteGraph]
  rw [degree, hn, Finset.card_map]
  simp

lemma complete_degree_right (m n : ℕ) (v : Fin n) :
    (completeBipartiteGraph (Fin m) (Fin n)).degree (Sum.inr v) = m := by
  have hn : (completeBipartiteGraph (Fin m) (Fin n)).neighborFinset (.inr v) =
      Finset.univ.map Function.Embedding.inl := by
    ext x
    cases x <;> simp [completeBipartiteGraph]
  rw [degree, hn, Finset.card_map]
  simp

abbrev Vert (C : ℕ) := Fin (4*C+3) ⊕ Fin (4*C+4)
abbrev graph (C : ℕ) : SimpleGraph (Vert C) :=
  completeBipartiteGraph (Fin (4*C+3)) (Fin (4*C+4))

lemma graph_min_degree (C : ℕ) (v : Vert C) : 4*C+3 ≤ (graph C).degree v := by
  cases v with
  | inl v => rw [complete_degree_left]; omega
  | inr v => rw [complete_degree_right]

lemma graph_support (C : ℕ) : (graph C).support = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  exact ((graph C).degree_pos_iff_mem_support v).mp (by
    have h := graph_min_degree C v
    omega)

lemma graph_odd_vertices (C : ℕ) : oddVertices (graph C) =
    Finset.univ.map (Function.Embedding.inr : Fin (4*C+4) ↪ Vert C) := by
  ext v
  cases v <;> simp [oddVertices, complete_degree_left, complete_degree_right, Nat.odd_iff]
  all_goals omega

lemma graph_odd_card (C : ℕ) : (oddVertices (graph C)).card = 4*C+4 := by
  rw [graph_odd_vertices, Finset.card_map]
  simp

lemma bipartite_of_le {m n : ℕ} {B : SimpleGraph (Fin m ⊕ Fin n)}
    (hB : B ≤ completeBipartiteGraph (Fin m) (Fin n)) :
    B.IsBipartiteWith
      (Finset.univ.map (Function.Embedding.inl : Fin m ↪ Fin m ⊕ Fin n) : Set _)
      (Finset.univ.map (Function.Embedding.inr : Fin n ↪ Fin m ⊕ Fin n) : Set _) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro v hl hr
    cases v with
    | inl v => simp at hr
    | inr v => simp at hl
  · intro v w hvw
    have hh := hB hvw
    cases v <;> cases w <;> simp_all [completeBipartiteGraph]

/-- Every right vertex is odd and every deleted edge has exactly one right
endpoint, so even restriction must delete at least 4C+4 edges. -/
lemma removed_edges_lower (C : ℕ) (A : SimpleGraph (Vert C))
    (hA : A ≤ graph C) (heA : ∀ v, Even (A.degree v)) :
    4*C+4 ≤ ((graph C) \ A).edgeSet.ncard := by
  let B := (graph C) \ A
  have hb : B ≤ graph C := sdiff_le
  have hsum := isBipartiteWith_sum_degrees_eq_card_edges' (bipartite_of_le hb)
  rw [Finset.sum_map] at hsum
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hsum
  change (∑ v : Fin (4*C+4), B.degree (.inr v)) = B.edgeSet.ncard at hsum
  have hl : ∀ v : Fin (4*C+4), 1 ≤ B.degree (Sum.inr v) := by
    intro v
    have hh := complement_degree_add hA (Sum.inr v)
    have hd : (graph C).degree (.inr v) = 4*C+3 :=
      complete_degree_right (4*C+3) (4*C+4) v
    have he := heA (Sum.inr v)
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      at hh hd he ⊢
    obtain ⟨k,hk⟩ := he
    change 1 ≤ Nat.card (((graph C) \ A).neighborSet (.inr v))
    omega
  have ht := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin (4*C+4)))) => hl v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at ht hsum
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at ht hsum
  exact ht.trans_eq hsum

/-- This excludes ALL even restrictions, not merely a prescribed parity
forest, and allows the restriction to discard arbitrary additional cycles. -/
theorem charge_failure (C : ℕ) (A : SimpleGraph (Vert C))
    (hA : A ≤ graph C) (heA : ∀ v, Even (A.degree v)) :
    (oddVertices (graph C)).card / 2 + C * ((graph C).support \ A.support).ncard <
      ((graph C) \ A).edgeSet.ncard := by
  have hl := removed_edges_lower C A hA heA
  have hs := lost_support_incidence_bound hA (4*C+3)
    (fun v _ => graph_min_degree C v)
  rw [graph_odd_card]
  have hdiv : (4*C+4)/2 = 2*C+2 := by omega
  rw [hdiv]
  by_contra! hb
  have hmul := Nat.mul_le_mul_left (4*C+3) hb
  have hinc := Nat.mul_le_mul_left C hs
  have hlow := Nat.mul_le_mul_left (2*C+3) hl
  nlinarith

/-- In particular no natural constant makes this parity/support charge
available for every finite simple graph. This is NOT the conjecture's negation. -/
theorem no_uniform_charge :
    ¬ ∃ C : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      ∃ A : SimpleGraph V, A ≤ G ∧ (∀ v, Even (A.degree v)) ∧
        (G \ A).edgeSet.ncard ≤ (oddVertices G).card / 2 + C*(G.support \ A.support).ncard := by
  rintro ⟨C,hC⟩
  obtain ⟨A,hA,heA,hb⟩ := hC (graph C)
  exact (charge_failure C A hA heA).not_ge hb


abbrev FullVert (C : ℕ) := Fin (4*C+4) ⊕ Fin (4*C+4)
abbrev source (C : ℕ) : SimpleGraph (FullVert C) :=
  completeBipartiteGraph (Fin (4*C+4)) (Fin (4*C+4))
def removedVertex (C : ℕ) : FullVert C := Sum.inl (Fin.last (4*C+3))
def embed (C : ℕ) : Vert C → FullVert C
  | Sum.inl v => Sum.inl v.castSucc
  | Sum.inr v => Sum.inr v

lemma source_regular (C : ℕ) : (source C).IsRegularOfDegree (4*C+4) := by
  intro v
  cases v with
  | inl v => exact complete_degree_left _ _ v
  | inr v => exact complete_degree_right _ _ v

lemma source_even (C : ℕ) : ∀ v, Even ((source C).degree v) := by
  intro v
  rw [source_regular C v]
  exact ⟨2*C+2, by omega⟩

lemma embed_injective (C : ℕ) : Function.Injective (embed C) := by
  intro v w hvw
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      have hh := Sum.inl.inj hvw
      exact congrArg Sum.inl (Fin.castSucc_injective _ hh)
    | inr w => cases hvw
  | inr v =>
    cases w with
    | inl w => cases hvw
    | inr w => exact congrArg Sum.inr (Sum.inr.inj hvw)

lemma embed_avoids (C : ℕ) (v : Vert C) : embed C v ≠ removedVertex C := by
  cases v with
  | inl v => exact fun h => v.castSucc_ne_last (Sum.inl.inj h)
  | inr v => simp [embed,removedVertex]

lemma embed_surjective_off_vertex (C : ℕ) (v : FullVert C)
    (hv : v ≠ removedVertex C) : ∃ w, embed C w = v := by
  cases v with
  | inl v =>
    rcases Fin.eq_castSucc_or_eq_last v with ⟨w,rfl⟩ | rfl
    · exact ⟨Sum.inl w,rfl⟩
    · exact (hv rfl).elim
  | inr v => exact ⟨Sum.inr v,rfl⟩

/-- Exact adjacency transport from the regular source after deleting its
specified vertex. Together with the preceding injection and surjection this
identifies the entire deletion, not just a subgraph of it. -/
lemma deleted_source_adj (C : ℕ) (v w : Vert C) :
    ((source C).deleteIncidenceSet (removedVertex C)).Adj (embed C v) (embed C w) ↔
      (graph C).Adj v w := by
  rw [deleteIncidenceSet_adj]
  have hv := embed_avoids C v
  have hw := embed_avoids C w
  have ha : (source C).Adj (embed C v) (embed C w) ↔ (graph C).Adj v w := by
    cases v <;> cases w <;> simp [source,graph,embed,completeBipartiteGraph]
  exact ⟨fun h => ha.mp h.1, fun h => ⟨ha.mpr h,hv,hw⟩⟩

end Erdos184.ParitySupportChargeObstruction
