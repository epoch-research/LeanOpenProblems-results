import Submission.CyclicSegments
import Submission.TourCover

/-! Cyclic vertex models and paths complementary to a clean oriented arc. -/
open SimpleGraph
open scoped Classical
open Fin.NatCast
namespace Erdos184.CyclicModel
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}
set_option maxHeartbeats 400000

lemma rotation_iterate (m : ℕ) (a : Fin (n+3)) :
    (finRotate (n+3) : Fin (n+3) → Fin (n+3))^[m] a = a + (↑m : Fin (n+3)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih,finRotate_succ_apply]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc]

lemma rotation_period (a : Fin (n+3)) :
    (finRotate (n+3) : Fin (n+3) → Fin (n+3))^[n+3] a = a := by
  rw [rotation_iterate,Fin.natCast_self,add_zero]

lemma rotation_injective (a : Fin (n+3)) :
    Set.InjOn (fun m : ℕ => (finRotate (n+3) : Fin (n+3) → Fin (n+3))^[m] a)
      {m | m < n+3} := by
  intro i hi j hj hij
  dsimp only at hij
  rw [rotation_iterate,rotation_iterate] at hij
  have hh := add_left_cancel hij
  have hv := congrArg Fin.val hh
  simpa only [Fin.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hv

lemma rotation_visit (a b : Fin (n+3)) :
    ∃ m : ℕ, m < n+3 ∧ (finRotate (n+3) : Fin (n+3) → Fin (n+3))^[m] a = b := by
  refine ⟨(b-a).val,(b-a).isLt,?_⟩
  rw [rotation_iterate]
  simp

lemma rotation_transitive (a b : Fin (n+3)) :
    ∃ m : ℕ, (finRotate (n+3) : Fin (n+3) → Fin (n+3))^[m] a = b := by
  obtain ⟨m,_,hm⟩ := rotation_visit a b
  exact ⟨m,hm⟩

structure Model (G : SimpleGraph V) (n : ℕ) where
  vertex : Fin (n+3) → V
  injective : Function.Injective vertex
  adj : ∀ i, G.Adj (vertex i) (vertex (finRotate (n+3) i))

lemma model_of_cycle {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ n : ℕ, ∃ M : Model G n, Set.range M.vertex = p.toSubgraph.verts := by
  let n := p.length-3
  have hn : p.length = n+3 := by have hh := hp.three_le_length; omega
  let f := tourCycleHom p hn
  have hi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
      (by change j.val ≤ p.length-1; omega) hij
  let M : Model G n := {
    vertex := f
    injective := hi
    adj := fun i => f.map_adj ((cycleGraph_adj_successor _ _).mpr (by
      left; exact finRotate_succ_apply i)) }
  refine ⟨n,M,?_⟩
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact p.mem_verts_toSubgraph.mpr (p.getVert_mem_support i.val)
  · intro hx
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp (p.mem_verts_toSubgraph.mp hx)
    by_cases he : j = p.length
    · refine ⟨0,?_⟩
      change p.getVert 0 = x
      simpa only [he,Walk.getVert_length,Walk.getVert_zero] using hj
    · exact ⟨⟨j,by omega⟩,hj⟩

/-- Follow the complementary arc. All marked vertices stay on this path if
the removed open arc contained no marked vertex. -/
lemma complementary_path (M : Model G n) (a : Fin (n+3)) (r : ℕ)
    (hr0 : 0 < r) (hrN : r < n+3) (T : Set V) (hT : T ⊆ Set.range M.vertex)
    (hclean : ∀ i, 0 < i → i < r →
      M.vertex ((finRotate (n+3) : Fin (n+3) → Fin (n+3))^[i] a) ∉ T) :
    ∃ q : G.Walk
      (M.vertex ((finRotate (n+3) : Fin (n+3) → Fin (n+3))^[r] a)) (M.vertex a),
      q.IsPath ∧ (∀ x, x ∈ q.support → x ∈ Set.range M.vertex) ∧
      (∀ x ∈ T, x ∈ q.support) := by
  let f : Fin (n+3) → Fin (n+3) := finRotate (n+3)
  let b := f^[r] a
  let v : ℕ → V := fun i => M.vertex (f^[i] b)
  have hadj : ∀ i, i < n+3-r → G.Adj (v i) (v (i+1)) := by
    intro i _
    dsimp only [v]
    rw [Function.iterate_succ_apply']
    exact M.adj _
  have hlast : f^[n+3-r] b = a := by
    dsimp only [b]
    rw [← Function.iterate_add_apply,Nat.sub_add_cancel (by omega : r ≤ n+3)]
    exact rotation_period a
  let p := MengerMatching.sequenceWalk v (n+3-r) hadj
  let q : G.Walk (M.vertex b) (M.vertex a) := p.copy (by simp [v]) (by simp [v,hlast])
  have hp : p.IsPath := by
    apply MengerMatching.sequenceWalk_isPath
    intro i hi j hj hij
    apply rotation_injective b (by change i < n+3; change i ≤ n+3-r at hi; omega)
      (by change j < n+3; change j ≤ n+3-r at hj; omega)
    exact M.injective hij
  have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr hp
  have hsupport (x : V) : x ∈ q.support ↔ ∃ i, i ≤ n+3-r ∧ x = v i := by
    simp only [q,p,Walk.support_copy,MengerMatching.sequenceWalk_support]
  refine ⟨q,hq,?_,?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := (hsupport x).mp hx
    exact ⟨f^[i] b,rfl⟩
  · intro x hx
    obtain ⟨j,hj⟩ := hT hx
    obtain ⟨m,hmN,hm⟩ := rotation_visit a j
    by_cases hm0 : m = 0
    · have hja : a = j := by simpa only [hm0,Function.iterate_zero,Function.id_def] using hm
      have hxa : x = M.vertex a := hj.symm.trans (congrArg M.vertex hja.symm)
      rw [hxa]
      exact q.end_mem_support
    · have hmr : r ≤ m := by
        by_contra! hh
        exact hclean m (by omega) hh (by rw [hm,hj]; exact hx)
      apply (hsupport x).mpr
      refine ⟨m-r,by omega,?_⟩
      dsimp only [v,b]
      rw [← Function.iterate_add_apply,Nat.sub_add_cancel hmr]
      exact hj.symm.trans (congrArg M.vertex hm.symm)

end Erdos184.CyclicModel
