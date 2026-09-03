import Submission.EdgeTransitiveLocal
import Submission.WeightedPowerSymmetry

/-!
The sharp local K44-free bound inside K46 and its constant-fraction averaging
consequence. A constant density loss does not resolve Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
namespace Erdos714FourBySix
abbrev Forbidden := completeBipartiteGraph (Fin 4) (Fin 4)
abbrev Block := completeBipartiteGraph (Fin 4) (Fin 6)

/-- At most three columns can meet all four rows. Every other column has degree
at most three, giving the sharp bound21 rather than the crude bound23. -/
theorem incidence_bound (S : Fin 4 → Finset (Fin 6))
    (hf : Forbidden.Free (Erdos714Packing.incidence S)) :
    (Erdos714Packing.incidence S).edgeFinset.card ≤ 21 := by
  let T := (univ : Finset (Fin 6)).filter (fun j => ∀ i, j ∈ S i)
  have hT : T.card ≤ 3 := by
    have h := (Erdos714Packing.free_iff_common_card S (by decide : 0 < 4)).mp hf
      (Function.Embedding.refl (Fin 4))
    have he : Erdos714Packing.common S (Function.Embedding.refl (Fin 4)) = T := by
      ext j
      simp [Erdos714Packing.mem_common, T]
    rw [he] at h
    omega
  have hdegree (j : Fin 6) : (univ.filter (fun i => j ∈ S i)).card ≤
      3+(if j ∈ T then 1 else 0) := by
    by_cases hj : j ∈ T
    · have h := Finset.card_filter_le (univ : Finset (Fin 4)) (fun i => j ∈ S i)
      simpa [hj] using h
    · have hnot : ¬ ∀ i, j ∈ S i := by simpa [T] using hj
      obtain ⟨i,hi⟩ := not_forall.mp hnot
      have hs : univ.filter (fun a => j ∈ S a) ⊆ (univ : Finset (Fin 4)).erase i := by
        intro a ha
        refine mem_erase.mpr ⟨?_, mem_univ _⟩
        intro he
        subst a
        exact hi (mem_filter.mp ha).2
      have h := Finset.card_le_card hs
      simpa [hj] using h
  have hcount : ∑ i, (S i).card = ∑ j : Fin 6, (univ.filter (fun i => j ∈ S i)).card := by
    calc
      _ = ∑ i, ((univ : Finset (Fin 6)).filter (fun j => j ∈ S i)).card := by simp
      _ = _ := by simp only [Finset.card_filter]; exact Finset.sum_comm
  rw [Erdos714Packing.incidence_edges, hcount]
  calc
    _ ≤ ∑ j : Fin 6, (3+(if j ∈ T then 1 else 0)) := sum_le_sum (fun j _ => hdegree j)
    _ = 18+T.card := by simp [sum_add_distrib]
    _ ≤ 21 := by omega

/-- The local bound applies to any selected edge graph on the block. -/
theorem block_bound (H : SimpleGraph (Fin 4 ⊕ Fin 6)) (hH : H ≤ Block)
    (hf : Forbidden.Free H) : H.edgeFinset.card ≤ 21 := by
  let S (i : Fin 4) := (univ : Finset (Fin 6)).filter (fun j => H.Adj (.inl i) (.inr j))
  have he : H = Erdos714Packing.incidence S := by
    ext v w
    cases v with
    | inl i =>
      cases w with
      | inl j =>
        have hn : ¬ H.Adj (.inl i) (.inl j) := by
          intro h
          have hh := hH h
          simp [Block] at hh
        simp [Erdos714Packing.incidence, hn]
      | inr j => simp [Erdos714Packing.incidence, S]
    | inr j =>
      cases w with
      | inl i => simp [Erdos714Packing.incidence, S, adj_comm]
      | inr i =>
        have hn : ¬ H.Adj (.inr j) (.inr i) := by
          intro h
          have hh := hH h
          simp [Block] at hh
        simp [Erdos714Packing.incidence, hn]
  rw [he] at hf ⊢
  exact incidence_bound S hf

/-- Delete precisely the edges from row0 to the last three columns. -/
def sharpRows (i : Fin 4) : Finset (Fin 6) := univ.filter (fun j => j.val < 3 ∨ i ≠ 0)
def sharpGraph : SimpleGraph (Fin 4 ⊕ Fin 6) := Erdos714Packing.incidence sharpRows

lemma sharpGraph_le : sharpGraph ≤ Block := by
  intro v w h
  cases v <;> cases w <;> simp_all [sharpGraph, Erdos714Packing.incidence, Block]

/-- The local bound is attainable, so K46 averaging alone cannot improve it. -/
theorem sharpGraph_free : Forbidden.Free sharpGraph := by
  apply (Erdos714Packing.free_iff_common_card sharpRows (by decide : 0 < 4)).mpr
  intro f
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp f.injective) 0
  have hs : Erdos714Packing.common sharpRows f ⊆
      (univ : Finset (Fin 6)).filter (fun j => j.val < 3) := by
    intro j hj
    have h := (Erdos714Packing.mem_common sharpRows f j).mp hj i
    simpa [sharpRows, hi] using h
  have hcard : ((univ : Finset (Fin 6)).filter (fun j => j.val < 3)).card = 3 := by decide
  have h := Finset.card_le_card hs
  rw [hcard] at h
  omega

theorem sharpGraph_edges : sharpGraph.edgeFinset.card = 21 := by
  rw [sharpGraph, Erdos714Packing.incidence_edges]
  decide

/-- This factor is a fixed7/8, not a quantity tending to zero with field size. -/
theorem edge_transitive_bound {V : Type*} [Fintype V] (G H : SimpleGraph V)
    (htrans : Erdos714GraphAveraging.EdgeTransitive G) (c : Block.Copy G)
    (hHG : H ≤ G) (hf : Forbidden.Free H) :
    8*H.edgeFinset.card ≤ 7*G.edgeFinset.card := by
  have h := Erdos714LocalAveraging.edge_transitive_local_bound Forbidden H G Block c
    hHG hf htrans 21 block_bound
  rw [Erdos714GraphAveraging.complete_bipartite_edges] at h
  norm_num only [Fintype.card_fin] at h
  omega

/-- Conditional weighted-norm/power application: the K46 copy is an explicit
hypothesis. No such copy is silently inferred from a K44 certificate. -/
theorem weighted_power_bound {E W : Type*} [Field E] [CommGroup W] [Fintype E] [Fintype W]
    (ν : Eˣ →* W) (c : Block.Copy (Erdos714WeightedPower.graph ν))
    (H : SimpleGraph ((E × W) ⊕ (E × W))) (hH : H ≤ Erdos714WeightedPower.graph ν)
    (hf : Forbidden.Free H) :
    8*H.edgeFinset.card ≤ 7*(Erdos714WeightedPower.graph ν).edgeFinset.card :=
  edge_transitive_bound _ H (Erdos714WeightedPower.edge_transitive ν) c hH hf

#print axioms block_bound
#print axioms sharpGraph_free
#print axioms sharpGraph_edges
#print axioms edge_transitive_bound
#print axioms weighted_power_bound
end Erdos714FourBySix
