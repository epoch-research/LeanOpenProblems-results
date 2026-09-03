import Submission.QuadrilateralOutsideData
import Submission.BinaryVectorEncode
import Submission.FiniteNeighborLabels

/-! Encodings of small graphs with an initially labeled neighbor block. -/
open SimpleGraph
namespace Erdos184.SmallGraphEncoding
open QuadrilateralOutsideData
set_option maxHeartbeats 1000000

lemma edgeIndex_comm (i j : ℕ) : edgeIndex i j = edgeIndex j i := by
  simp only [edgeIndex,max_comm,min_comm]

def starAdj (d code i j : ℕ) : Bool :=
  if i = j then false else
  if i = 0 then decide (j ≤ d) else
  if j = 0 then decide (i ≤ d) else
  decide (code / 2 ^ edgeIndex i j % 2 = 1)

lemma starAdj_comm (d code i j : ℕ) : starAdj d code i j = starAdj d code j i := by
  by_cases hij : i = j
  · subst j; rfl
  by_cases hi : i = 0
  · subst i; simp [starAdj,hij,Ne.symm hij]
  by_cases hj : j = 0
  · subst j; simp [starAdj,hij,Ne.symm hij]
  simp [starAdj,hij,Ne.symm hij,hi,hj,edgeIndex_comm]

def graph (N d code : ℕ) : SimpleGraph (Fin N) where
  Adj i j := starAdj d code i.val j.val = true
  symm := by intro i j h; rwa [starAdj_comm]
  loopless := by intro i; simp [starAdj]

instance (N d code : ℕ) : DecidableRel (graph N d code).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

def degreeCode (N d code i : ℕ) : ℕ :=
  ((List.range N).map (fun j => if starAdj d code i j then 1 else 0)).sum

lemma graph_degree (N d code : ℕ) (i : Fin N) :
    (graph N d code).degree i = degreeCode N d code i.val := by
  have hh := (graph N d code).degree_eq_sum_if_adj (R := ℕ) i
  simp only [Nat.cast_id] at hh
  rw [hh]
  change (∑ j : Fin N, if starAdj d code i.val j.val = true then 1 else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if starAdj d code i.val j = true then (1 : ℕ) else 0) N]
  unfold degreeCode
  simpa only [List.toFinset_range] using
    (List.sum_toFinset (fun j : ℕ => if starAdj d code i.val j = true then (1 : ℕ) else 0)
      (l := List.range N) List.nodup_range)

lemma starAdj_two (code i j : ℕ) : starAdj 2 code i j = adjCode code i j := rfl

lemma degreeCode_two (code i : ℕ) : degreeCode 7 2 code i = QuadrilateralOutsideData.degreeCode code i := rfl

/-- Data needed to encode the edges away from vertex zero. -/
structure EdgeTable (N M : ℕ) where
  endpoints : Fin M → Fin N × Fin N
  complete : ∀ i j : Fin N, i ≠ j → i.val ≠ 0 → j.val ≠ 0 →
    ∃ k : Fin M, edgeIndex i.val j.val = k.val ∧
      (endpoints k = (i,j) ∨ endpoints k = (j,i))

lemma encode_graph {N M : ℕ} (table : EdgeTable N M) (G : SimpleGraph (Fin N))
    (d : ℕ) (hroot : ∀ i j : Fin N, i.val = 0 →
      (G.Adj i j ↔ 0 < j.val ∧ j.val ≤ d)) :
    ∃ code : ℕ, code < 2^M ∧ graph N d code = G := by
  classical
  let f : Fin M → ℕ := fun k => if G.Adj (table.endpoints k).1 (table.endpoints k).2 then 1 else 0
  have hf : ∀ k, f k < 2 := by intro k; dsimp only [f]; split_ifs <;> omega
  let code := BinaryVectorEncode.encode M f
  refine ⟨code,BinaryVectorEncode.encode_lt M f hf,?_⟩
  ext i j
  change starAdj d code i.val j.val = true ↔ G.Adj i j
  by_cases hij : i = j
  · subst j; simp [starAdj]
  have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases hi : i.val = 0
  · have hj : 0 < j.val := by omega
    simpa [starAdj,hi,hj.ne',Ne.symm hj.ne',hijv,hj] using (hroot i j hi).symm
  by_cases hj : j.val = 0
  · have hi' : 0 < i.val := by omega
    rw [G.adj_comm]
    simpa [starAdj,hi,hj,hijv,hi'] using (hroot j i hj).symm
  obtain ⟨k,hidx,hpair⟩ := table.complete i j hij hi hj
  have hbit := BinaryVectorEncode.digit_encode M f hf k
  simp only [starAdj,if_neg hijv,if_neg hi,if_neg hj,hidx,decide_eq_true_eq]
  change code / 2^k.val % 2 = 1 ↔ G.Adj i j
  rw [hbit]
  dsimp only [f]
  rcases hpair with hpair | hpair
  · rw [hpair]
    simp
  · rw [hpair]
    simp [G.adj_comm]

def table6 : EdgeTable 6 10 where
  endpoints := ![(1,2),(1,3),(2,3),(1,4),(2,4),(3,4),(1,5),(2,5),(3,5),(4,5)]
  complete := by decide

def table7 : EdgeTable 7 15 where
  endpoints := ![(1,2),(1,3),(2,3),(1,4),(2,4),(3,4),(1,5),(2,5),(3,5),(4,5),
    (1,6),(2,6),(3,6),(4,6),(5,6)]
  complete := by decide

end Erdos184.SmallGraphEncoding
