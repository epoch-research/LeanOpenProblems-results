import Submission.ShortestOddInducedCycle

/-!
Neighbors of a shortest odd cycle of length at least five occupy at most two
rim positions. This is a local necessary condition in the persistent-wheel
reduction, not a proof or disproof of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
open scoped Classical
namespace Erdos595MinimalOddCycleNeighbors
open Erdos595ShortestOddInducedCycle

variable {V : Type*} {G : SimpleGraph V} {a x : V}

/-- The two cyclic distances between two rim neighbors are 2 and n-2. -/
lemma neighbor_gap (w : G.Walk a a) (h5 : 5 ≤ w.length) (ho : Odd w.length)
    (hm : MinimalOdd G w.length) {i j : ℕ} (hij : i < j) (hj : j < w.length)
    (hxi : G.Adj x (w.getVert i)) (hxj : G.Adj x (w.getVert j)) :
    j-i = 2 ∨ j-i = w.length-2 := by
  let p := ((segment w i j hij.le).concat hxj.symm).concat hxi
  let q := ((complement w i j).concat hxi.symm).concat hxj
  have hp : p.length = j-i+2 := by
    simp only [p,SimpleGraph.Walk.length_concat,segment_length w hij.le hj.le]
  have hq : q.length = w.length-j+i+2 := by
    simp only [q,SimpleGraph.Walk.length_concat,
      complement_length w (hij.le.trans hj.le)]
  by_cases hd : Odd (j-i)
  · have hpo : Odd p.length := by rw [hp]; exact hd.add_even (by decide)
    have hpmin := hm _ p hpo
    have heq : j-i = w.length-2 := by
      obtain ⟨r,hr⟩ := hd
      obtain ⟨s,hs⟩ := ho
      omega
    exact Or.inr heq
  · have he := Nat.not_odd_iff_even.mp hd
    have hqo : Odd q.length := by
      obtain ⟨r,hr⟩ := he
      obtain ⟨s,hs⟩ := ho
      apply Nat.odd_iff.mpr
      omega
    have hqmin := hm _ q hqo
    have heq : j-i = 2 := by
      obtain ⟨r,hr⟩ := he
      omega
    exact Or.inl heq

/-- Three distinct increasing positions cannot all be adjacent to x. -/
lemma not_three_neighbors (w : G.Walk a a) (h5 : 5 ≤ w.length) (ho : Odd w.length)
    (hm : MinimalOdd G w.length) {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hk : k < w.length) (hxi : G.Adj x (w.getVert i))
    (hxj : G.Adj x (w.getVert j)) (hxk : G.Adj x (w.getVert k)) : False := by
  have h₁ := neighbor_gap w h5 ho hm hij (hjk.trans hk) hxi hxj
  have h₂ := neighbor_gap w h5 ho hm hjk hk hxj hxk
  have h₃ := neighbor_gap w h5 ho hm (hij.trans hjk) hk hxi hxk
  obtain ⟨s,hs⟩ := ho
  omega

/-- The bound is on positions, so it applies directly to the existing walk
formulation without an extra choice of an induced-cycle embedding. -/
theorem neighbor_positions_card_le_two (w : G.Walk a a)
    (h5 : 5 ≤ w.length) (ho : Odd w.length) (hm : MinimalOdd G w.length) (x : V) :
    Nat.card {i : Fin w.length // G.Adj x (w.getVert i.val)} ≤ 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let S := Finset.univ.filter (fun i : Fin w.length => G.Adj x (w.getVert i.val))
  change S.card ≤ 2
  by_contra hn
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq h3
  let e := T.orderEmbOfFin hT
  have he (i : Fin 3) : G.Adj x (w.getVert (e i).val) := by
    exact (Finset.mem_filter.mp (hTS (T.orderEmbOfFin_mem hT i))).2
  exact not_three_neighbors w h5 ho hm (e.strictMono (by decide))
    (e.strictMono (by decide)) (e 2).isLt (he 0) (he 1) (he 2)

/-- The profile bound is in the ambient graph R, even when the wheel itself
is required to avoid an additional deleted edge graph. -/
theorem wheel_in_subgraph_sparse_profiles (R H : SimpleGraph V) (hHR : H ≤ R)
    {n : ℕ} (h5 : 5 ≤ n) (ho : Odd n)
    (hmin : ∀ m < n, Odd m → ¬Erdos595RobustOddWheel.WheelWalk R m)
    (hw : Erdos595RobustOddWheel.WheelWalk H n) :
    ∃ v : V, ∃ a : H.neighborSet v,
      ∃ w : (H.induce (H.neighborSet v)).Walk a a,
        w.length = n ∧ ∀ x : R.neighborSet v,
          Nat.card {i : Fin w.length //
            R.Adj x.val (w.getVert i.val).val} ≤ 2 := by
  obtain ⟨v,a,w,hw⟩ := hw
  refine ⟨v,a,w,hw,?_⟩
  let f : H.induce (H.neighborSet v) →g R.induce (R.neighborSet v) :=
    ⟨fun x => ⟨x.val,hHR x.property⟩,fun h => hHR h⟩
  have hlen : (w.map f).length = n := (SimpleGraph.Walk.length_map f w).trans hw
  intro x
  have hh := neighbor_positions_card_le_two (w.map f) (hlen ▸ h5) (hlen ▸ ho)
    (hlen ▸ minimal_neighbor R hmin R le_rfl v) x
  let e : {i : Fin w.length // R.Adj x.val (w.getVert i.val).val} ≃
      {i : Fin (w.map f).length //
        (R.induce (R.neighborSet v)).Adj x ((w.map f).getVert i.val)} :=
    (finCongr (SimpleGraph.Walk.length_map f w).symm).subtypeEquiv (fun i => by
      simp only [finCongr_apply, Fin.val_cast, SimpleGraph.Walk.getVert_map]
      rfl)
  rw [Nat.card_congr e]
  exact hh

/-- One fixed odd rim length with sparse ambient profiles survives every
covered deletion. This remains conditional on a non-covered graph. -/
theorem persistent_sparse_rims (G : SimpleGraph V) (hK : G.CliqueFree 4)
    (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G) :
    ∃ (E : SimpleGraph V) (n : ℕ),
      Erdos595Work.IsCountableUnionOfTriangleFree E ∧
      (G \ E).CliqueFree 4 ∧
      ¬Erdos595Work.IsCountableUnionOfTriangleFree (G \ E) ∧
      5 ≤ n ∧ Odd n ∧
      (∀ m < n, Odd m → ¬Erdos595RobustOddWheel.WheelWalk (G \ E) m) ∧
      ∀ D : SimpleGraph V, Erdos595Work.IsCountableUnionOfTriangleFree D →
        ∃ v : V, ∃ a : ((G \ E) \ D).neighborSet v,
          ∃ w : (((G \ E) \ D).induce (((G \ E) \ D).neighborSet v)).Walk a a,
            w.length = n ∧ ∀ x : (G \ E).neighborSet v,
              Nat.card {i : Fin w.length //
                (G \ E).Adj x.val (w.getVert i.val).val} ≤ 2 := by
  obtain ⟨E,n,hE,hK',hG',h5,ho,hp,hmin⟩ :=
    Erdos595MinimalRobustOddWheel.minimal_residual G hK hG
  refine ⟨E,n,hE,hK',hG',h5,ho,hmin,?_⟩
  intro D hD
  exact wheel_in_subgraph_sparse_profiles (G \ E) ((G \ E) \ D)
    (fun _ _ h => h.1) h5 ho hmin (hp D hD)

#print axioms wheel_in_subgraph_sparse_profiles
#print axioms persistent_sparse_rims
#print axioms neighbor_gap
#print axioms not_three_neighbors
#print axioms neighbor_positions_card_le_two
end Erdos595MinimalOddCycleNeighbors
