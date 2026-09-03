import Submission.Auxiliary

/-!
# Finite induced universality from the absence of homogeneous pairs

This standalone extension uses only the verified counting lemmas in `Auxiliary`.
It does not import `Spec` or use any statement of the Erdős–Hajnal conjecture.

For a graph with no disjoint complete or anticomplete `q` by `q` pair, disjoint
vertex pools of size at least `q ^ (h - 1)` contain every prescribed induced graph
on `h` vertices, with one vertex in each pool. Consequently `h * q ^ (h - 1)`
vertices suffice. Only the prescribed adjacency color is retained at each step.
-/

namespace Auxiliary.FiniteMixing

open SimpleGraph

variable {V : Type*}

/-- Prescribing just one color for each target costs at most `q - 1` bad candidates
per target, rather than the `2 * (q - 1)` needed to preserve both colors. -/
theorem exists_vertex_prescribed {G : SimpleGraph V} [DecidableRel G.Adj]
    {ι : Type*} {q s : ℕ} (hmix : NoHomogeneousPair G q)
    (J : Finset ι) (A : ι → Finset V) (B : Finset V)
    (c : ι → Prop) [DecidablePred c]
    (hdisj : ∀ j ∈ J, Disjoint B (A j))
    (hA : ∀ j ∈ J, q * s ≤ (A j).card)
    (hB : J.card * (q - 1) + 1 ≤ B.card) :
    ∃ b ∈ B, ∀ j ∈ J,
      s ≤ ((A j).filter (fun a => c j ↔ G.Adj b a)).card := by
  classical
  let bad : ι → Finset V := fun j =>
    B.filter (fun b => ((A j).filter (fun a => c j ↔ G.Adj b a)).card < s)
  have hbad : ∀ j ∈ J, (bad j).card ≤ q - 1 := by
    intro j hj
    have hlt : (bad j).card < q := by
      by_cases hc : c j
      · simpa [bad, hc] using
          card_few_neighbors_lt hmix (A j) B (hdisj j hj) (hA j hj)
      · simpa [bad, hc] using
          card_few_nonneighbors_lt hmix (A j) B (hdisj j hj) (hA j hj)
    omega
  have hU : (J.biUnion bad).card ≤ J.card * (q - 1) :=
    Finset.card_biUnion_le_card_mul J bad (q - 1) hbad
  obtain ⟨b, hbB, hbU⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (J.biUnion bad).card < B.card by omega)
  refine ⟨b, hbB, ?_⟩
  intro j hj
  by_contra! hsmall
  apply hbU
  exact Finset.mem_biUnion.mpr
    ⟨j, hj, Finset.mem_filter.mpr ⟨hbB, hsmall⟩⟩

/-- The prescribed-color lemma for a family indexed by `Fin k`. -/
theorem exists_vertex_prescribed_fin {G : SimpleGraph V} [DecidableRel G.Adj]
    {q s k : ℕ} (hmix : NoHomogeneousPair G q)
    (A : Fin k → Finset V) (B : Finset V) (c : Fin k → Prop) [DecidablePred c]
    (hdisj : ∀ j, Disjoint B (A j))
    (hA : ∀ j, q * s ≤ (A j).card)
    (hB : k * (q - 1) + 1 ≤ B.card) :
    ∃ b ∈ B, ∀ j : Fin k,
      s ≤ ((A j).filter (fun a => c j ↔ G.Adj b a)).card := by
  obtain ⟨b, hb, hgood⟩ := exists_vertex_prescribed hmix Finset.univ A B c
    (fun j _ => hdisj j) (fun j _ => hA j) (by simpa using hB)
  exact ⟨b, hb, fun j => hgood j (Finset.mem_univ j)⟩

/-- The elementary Bernoulli bound used to find a good vertex in the current pool. -/
theorem mul_pred_add_one_le_pow {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    n * (q - 1) + 1 ≤ q ^ n := by
  have heq : 1 + (q - 1) = q := by omega
  have h := one_add_le_pow_of_two_add_nonneg (R := ℕ) (a := q - 1)
    (Nat.zero_le _) n
  simpa only [Nat.cast_id, heq, Nat.add_comm 1] using h

/-- An induced embedding with one vertex in each of `n` pairwise disjoint pools.
The membership conclusion is the induction invariant that guarantees injectivity
when the next vertex is added. The empty graph is included. -/
theorem exists_induced_embedding_in_pools_fin {G : SimpleGraph V} {q n : ℕ}
    (hmix : NoHomogeneousPair G q) (H : SimpleGraph (Fin n))
    (A : Fin n → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsize : ∀ i, q ^ (n - 1) ≤ (A i).card) :
    ∃ g : Fin n ↪ V, (∀ i, g i ∈ A i) ∧ H = G.comap g := by
  classical
  induction n with
  | zero =>
      let g : Fin 0 ↪ V := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      refine ⟨g, fun i => Fin.elim0 i, ?_⟩
      ext i j
      exact Fin.elim0 i
  | succ n ih =>
      have htarget : ∀ j : Fin n, q * q ^ (n - 1) ≤ (A j.succ).card := by
        intro j
        have hn : 1 ≤ n := by have := j.isLt; omega
        calc
          q * q ^ (n - 1) = q ^ n := by
            rw [← pow_succ', Nat.sub_add_cancel hn]
          _ ≤ (A j.succ).card := by simpa using hsize j.succ
      have hcurrent : n * (q - 1) + 1 ≤ (A 0).card :=
        (mul_pred_add_one_le_pow hmix.pos n).trans (by simpa using hsize 0)
      obtain ⟨b, hb, hgood⟩ := exists_vertex_prescribed_fin hmix
        (fun j : Fin n => A j.succ) (A 0) (fun j => H.Adj 0 j.succ)
        (fun j => hdisj (Fin.succ_ne_zero j).symm) htarget hcurrent
      let A' : Fin n → Finset V := fun j =>
        (A j.succ).filter (fun a => H.Adj 0 j.succ ↔ G.Adj b a)
      have hsub : ∀ j, A' j ⊆ A j.succ := fun j => Finset.filter_subset _ _
      have hdisj' : Pairwise (fun i j => Disjoint (A' i) (A' j)) := by
        intro i j hij
        exact (hdisj (fun heq => hij (Fin.succ_injective _ heq))).mono (hsub i) (hsub j)
      obtain ⟨g', hgmem, hgH⟩ := ih (H.comap Fin.succ) A' hdisj' hgood
      have hbnot : b ∉ Set.range g' := by
        rintro ⟨j, hj⟩
        have hmem : g' j ∈ A j.succ := hsub j (hgmem j)
        rw [hj] at hmem
        exact Finset.disjoint_left.mp (hdisj (Fin.succ_ne_zero j).symm)
          hb hmem
      let g : Fin (n + 1) ↪ V := Fin.Embedding.cons g' hbnot
      have hzero : g 0 = b := by simp [g]
      have hsucc : ∀ i : Fin n, g i.succ = g' i := by intro i; simp [g]
      have hcolor : ∀ j : Fin n, H.Adj 0 j.succ ↔ G.Adj b (g' j) := by
        intro j
        exact (Finset.mem_filter.mp (hgmem j)).2
      refine ⟨g, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => simpa only [hzero] using hb
        | succ i => simpa only [hsucc] using hsub i (hgmem i)
      · ext i j
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => simp
            | succ j => simpa only [SimpleGraph.comap_adj, hzero, hsucc] using hcolor j
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                simpa only [SimpleGraph.comap_adj, hzero, hsucc, H.adj_comm,
                  G.adj_comm] using hcolor i
            | succ j =>
                have htail : H.Adj i.succ j.succ ↔ G.Adj (g' i) (g' j) := by
                  change (H.comap Fin.succ).Adj i j ↔ (G.comap g').Adj i j
                  rw [hgH]
                simpa only [SimpleGraph.comap_adj, hsucc] using htail

/-- **Finite induced universality.** If `G` has no homogeneous disjoint `q`-pair,
then `|H| * q ^ (|H| - 1)` vertices suffice for an induced copy of `H`.

In particular this gives the stated bound for `q ≥ 2`. No separate positivity
hypothesis on `q` is needed: it follows from `hmix`. The empty and one-vertex
patterns are included. -/
theorem exists_induced_embedding {α : Type*} [Fintype α] [Fintype V]
    (H : SimpleGraph α) {G : SimpleGraph V} {q : ℕ}
    (hmix : NoHomogeneousPair G q)
    (hcard : Fintype.card α * q ^ (Fintype.card α - 1) ≤ Fintype.card V) :
    ∃ g : α ↪ V, H = G.comap g := by
  classical
  let h := Fintype.card α
  let m := q ^ (h - 1)
  obtain ⟨e : (Fin h × Fin m) ↪ V⟩ :=
    Function.Embedding.nonempty_of_card_le (α := Fin h × Fin m) (β := V)
      (by simpa [h, m] using hcard)
  let A : Fin h → Finset V := fun i =>
    Finset.univ.image (fun j : Fin m => e (i, j))
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hvi
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hvj
    exact hij (congrArg Prod.fst (e.injective (hx.trans hy.symm)))
  have hcardA : ∀ i, (A i).card = m := by
    intro i
    calc
      (A i).card = (Finset.univ : Finset (Fin m)).card :=
        Finset.card_image_of_injective _
          (fun x y hxy => congrArg Prod.snd (e.injective hxy))
      _ = m := by simp
  let eα : α ≃ Fin h := Fintype.equivFin α
  obtain ⟨f, _, hf⟩ := exists_induced_embedding_in_pools_fin hmix
    (H.comap eα.symm) A hdisj (fun i => (hcardA i).ge)
  let g : α ↪ V := eα.toEmbedding.trans f
  refine ⟨g, ?_⟩
  ext a b
  change H.Adj a b ↔ G.Adj (f (eα a)) (f (eα b))
  have hadj : (H.comap eα.symm).Adj (eα a) (eα b) ↔
      (G.comap f).Adj (eα a) (eα b) := by rw [hf]
  simpa only [SimpleGraph.comap_adj, Equiv.symm_apply_apply] using hadj

/-- The universality theorem in the `Fin n` form used by the exact forbidden-induced-
subgraph predicate. -/
theorem exists_induced_embedding_fin {α : Type*} [Fintype α]
    (H : SimpleGraph α) {n q : ℕ} {G : SimpleGraph (Fin n)}
    (hmix : NoHomogeneousPair G q)
    (hcard : Fintype.card α * q ^ (Fintype.card α - 1) ≤ n) :
    ∃ g : α ↪ Fin n, H = G.comap g := by
  exact exists_induced_embedding H hmix (by simpa using hcard)

end Auxiliary.FiniteMixing

#print axioms Auxiliary.FiniteMixing.exists_vertex_prescribed
#print axioms Auxiliary.FiniteMixing.exists_vertex_prescribed_fin
#print axioms Auxiliary.FiniteMixing.mul_pred_add_one_le_pow
#print axioms Auxiliary.FiniteMixing.exists_induced_embedding_in_pools_fin
#print axioms Auxiliary.FiniteMixing.exists_induced_embedding
#print axioms Auxiliary.FiniteMixing.exists_induced_embedding_fin
