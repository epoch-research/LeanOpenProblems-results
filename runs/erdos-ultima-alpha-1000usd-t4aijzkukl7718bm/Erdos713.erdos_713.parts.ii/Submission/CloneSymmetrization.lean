import FormalConjecturesUtil
import Submission.CompactCloneAverageAudit

/-! Degree-square symmetrization among bipartite extremal hosts.
This supplies additional necessary structure, not a rate-transfer theorem. -/
open SimpleGraph Finset
namespace Erdos713CloneSymm
open Erdos713Cloning Erdos713BipExtremal

variable {V W : Type*}

open scoped Classical in
noncomputable def degreeEnergy [Fintype V] (G : SimpleGraph V) : ℤ :=
  ∑ x, (Nat.card (G.neighborSet x) : ℤ)^2

open scoped Classical in
lemma replace_copy_clone (G : SimpleGraph V) (s t : V) :
    G.replaceVertex s t ⊑ clone G s := by
  let f : V → Option V := fun x => if x = t then none else some x
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro x y hxy
    change G.Adj (project s (f x)) (project s (f y))
    by_cases hx : x = t <;> by_cases hy : y = t <;>
      simp_all [f,project,SimpleGraph.replaceVertex]
  · intro x y hxy
    change f x = f y at hxy
    by_cases hx : x = t <;> by_cases hy : y = t <;> simp_all [f]

open scoped Classical in
lemma replace_bipartite {G : SimpleGraph V} (hB : G.IsBipartite) (s t : V) :
    (G.replaceVertex s t).IsBipartite := by
  obtain ⟨f⟩ := replace_copy_clone G s t
  exact (clone_bipartite hB s).of_hom f.toHom

open scoped Classical in
lemma safe_replace {H : SimpleGraph W} {G : SimpleGraph V} {s : V}
    (hs : H.Free (clone G s)) (t : V) : H.Free (G.replaceVertex s t) :=
  fun h => hs (h.trans (replace_copy_clone G s t))

open scoped Classical in
lemma degree_as_sum [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (Nat.card (G.neighborSet x) : ℤ) = ∑ y : V, if G.Adj x y then (1 : ℤ) else 0 := by
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,← card_neighborFinset_eq_degree,Finset.card_eq_sum_ones]
  push_cast
  simpa only [neighborFinset_eq_filter] using
    (sum_filter (s := univ) (p := G.Adj x) (f := fun _ => (1 : ℤ)))

open scoped Classical in
lemma replace_degree_other [Fintype V] (G : SimpleGraph V) (s t x : V) (hxt : x ≠ t) :
    (Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) = (Nat.card (G.neighborSet x) : ℤ) +
      (if G.Adj x s then 1 else 0) - (if G.Adj x t then 1 else 0) := by
  rw [degree_as_sum (G.replaceVertex s t) x,degree_as_sum G x]
  have hR := sum_erase_add (s := (univ : Finset V))
    (f := fun y => if (G.replaceVertex s t).Adj x y then (1 : ℤ) else 0) (mem_univ t)
  have hG := sum_erase_add (s := (univ : Finset V))
    (f := fun y => if G.Adj x y then (1 : ℤ) else 0) (mem_univ t)
  have he : (∑ y ∈ univ.erase t, if (G.replaceVertex s t).Adj x y then (1 : ℤ) else 0) =
      ∑ y ∈ univ.erase t, if G.Adj x y then (1 : ℤ) else 0 := by
    apply sum_congr rfl
    intro y hy
    simp only [G.adj_replaceVertex_iff_of_ne s hxt (mem_erase.mp hy).1]
  have ht : (if (G.replaceVertex s t).Adj x t then (1 : ℤ) else 0) =
      (if G.Adj x s then 1 else 0) := by simp [SimpleGraph.replaceVertex,hxt]
  dsimp only at hR hG
  simp only [he,ht] at hR
  omega

open scoped Classical in
lemma replace_degree_source [Fintype V] (G : SimpleGraph V) (s t : V)
    (hn : ¬ G.Adj s t) : Nat.card ((G.replaceVertex s t).neighborSet s) =
      Nat.card (G.neighborSet s) := by
  have he : (G.replaceVertex s t).neighborSet s = G.neighborSet s := by
    ext y
    by_cases hy : y = t
    · subst y
      simp [hn,not_adj_replaceVertex_same]
    · exact G.adj_replaceVertex_iff_of_ne_left s hy
  rw [he]

open scoped Classical in
lemma replace_degree_target [Fintype V] (G : SimpleGraph V) (s t : V)
    (hn : ¬ G.Adj s t) : Nat.card ((G.replaceVertex s t).neighborSet t) =
      Nat.card (G.neighborSet s) := by
  have he : (G.replaceVertex s t).neighborSet t = G.neighborSet s := by
    ext y
    by_cases hy : y = t
    · subst y
      simp [hn]
    · exact G.adj_replaceVertex_iff_of_ne_right s hy
  rw [he]

open scoped Classical in
lemma paired_degrees [Fintype V] (G : SimpleGraph V) (s t : V)
    (hn : ¬ G.Adj s t) (hd : Nat.card (G.neighborSet s) = Nat.card (G.neighborSet t)) (x : V) :
    (Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) + (Nat.card ((G.replaceVertex t s).neighborSet x) : ℤ) =
      2*(Nat.card (G.neighborSet x) : ℤ) := by
  have hn' : ¬ G.Adj t s := fun h => hn h.symm
  by_cases hx : x = s
  · subst x
    rw [replace_degree_source G s t hn,replace_degree_target G t s hn',hd]
    ring
  · by_cases hxt : x = t
    · subst x
      rw [replace_degree_source G t s hn',replace_degree_target G s t hn,hd]
      ring
    · rw [replace_degree_other G s t x hxt,replace_degree_other G t s x hx]
      ring

/-- Maximize edges first, then the degree-square sum, among bipartite H-free
hosts on the same vertex type. -/
structure Optimal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : Prop where
  free : H.Free G
  bipartite : G.IsBipartite
  max_edges : ∀ K : SimpleGraph V, H.Free K → K.IsBipartite →
    Nat.card K.edgeSet ≤ Nat.card G.edgeSet
  max_energy : ∀ K : SimpleGraph V, H.Free K → K.IsBipartite →
    Nat.card K.edgeSet = Nat.card G.edgeSet → degreeEnergy K ≤ degreeEnergy G

lemma exists_optimal {H : SimpleGraph W} {n : ℕ} (hn : 0 < number n H) :
    ∃ G : SimpleGraph (Fin n), Optimal H G ∧ Nat.card G.edgeSet = number n H := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | H.Free G ∧ G.IsBipartite ∧
    Nat.card G.edgeSet = number n H}
  have hS : S.Nonempty := by
    obtain ⟨G,hf,hb,he⟩ := exists_extremal_of_pos H n hn
    exact ⟨G,by simpa only [S,mem_filter,mem_univ,true_and] using And.intro hf (And.intro hb he)⟩
  obtain ⟨G,hG,hmax⟩ := S.exists_max_image degreeEnergy hS
  obtain ⟨hf,hb,he⟩ : H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H := by
    simpa only [S,mem_filter,mem_univ,true_and] using hG
  refine ⟨G,⟨hf,hb,?_,?_⟩,he⟩
  · intro K hK hKB
    rw [he]
    exact card_bound_fin H K hK hKB
  · intro K hK hKB hKe
    apply hmax K
    simpa only [S,mem_filter,mem_univ,true_and] using And.intro hK (And.intro hKB (hKe.trans he))

open scoped Classical in
/-- Only the replacement comparisons needed by the symmetrization argument. -/
structure CloneOptimal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : Prop where
  max_edges : ∀ s t : V, H.Free (clone G s) →
    Nat.card (G.replaceVertex s t).edgeSet ≤ Nat.card G.edgeSet
  max_energy : ∀ s t : V, H.Free (clone G s) →
    Nat.card (G.replaceVertex s t).edgeSet = Nat.card G.edgeSet →
      degreeEnergy (G.replaceVertex s t) ≤ degreeEnergy G

lemma Optimal.cloneOptimal [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hopt : Optimal H G) : CloneOptimal H G where
  max_edges s t hs := hopt.max_edges _ (safe_replace hs t) (replace_bipartite hopt.bipartite s t)
  max_energy s t hs he := hopt.max_energy _ (safe_replace hs t) (replace_bipartite hopt.bipartite s t) he

open scoped Classical in
lemma CloneOptimal.safe_degrees_eq [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hopt : CloneOptimal H G) {s t : V} (hn : ¬ G.Adj s t)
    (hs : H.Free (clone G s)) (ht : H.Free (clone G t)) :
    Nat.card (G.neighborSet s) = Nat.card (G.neighborSet t) := by
  have hn' : ¬ G.Adj t s := fun h => hn h.symm
  have hR := hopt.max_edges s t hs
  have hL := hopt.max_edges t s ht
  have hcR := G.card_edgeFinset_replaceVertex_of_not_adj hn
  have hcL := G.card_edgeFinset_replaceVertex_of_not_adj hn'
  simp only [edgeFinset_card,←card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hcR hcL
  omega

open scoped Classical in
lemma paired_energy [Fintype V] (G : SimpleGraph V) (s t : V)
    (hn : ¬ G.Adj s t) (hd : Nat.card (G.neighborSet s) = Nat.card (G.neighborSet t)) :
    degreeEnergy (G.replaceVertex s t) + degreeEnergy (G.replaceVertex t s) =
      2*degreeEnergy G + ∑ x : V, 2*((Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) -
        (Nat.card (G.neighborSet x) : ℤ))^2 := by
  unfold degreeEnergy
  rw [←sum_add_distrib]
  calc
    _ = ∑ x : V, (2*(Nat.card (G.neighborSet x) : ℤ)^2 +
        2*((Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) -
          (Nat.card (G.neighborSet x) : ℤ))^2) := by
      apply sum_congr rfl
      intro x _
      have hh := paired_degrees G s t hn hd x
      have he : (Nat.card ((G.replaceVertex t s).neighborSet x) : ℤ) =
          2*(Nat.card (G.neighborSet x) : ℤ)-(Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) := by
        omega
      rw [he]
      ring
    _ = _ := by rw [sum_add_distrib,←mul_sum]

open scoped Classical in
lemma CloneOptimal.safe_twins [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hopt : CloneOptimal H G) {s t : V} (hn : ¬ G.Adj s t)
    (hs : H.Free (clone G s)) (ht : H.Free (clone G t)) :
    G.neighborSet s = G.neighborSet t := by
  have hn' : ¬ G.Adj t s := fun h => hn h.symm
  have hd := hopt.safe_degrees_eq hn hs ht
  have heR : Nat.card (G.replaceVertex s t).edgeSet = Nat.card G.edgeSet := by
    have hh := G.card_edgeFinset_replaceVertex_of_not_adj hn
    simp only [edgeFinset_card,←card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hh
    omega
  have heL : Nat.card (G.replaceVertex t s).edgeSet = Nat.card G.edgeSet := by
    have hh := G.card_edgeFinset_replaceVertex_of_not_adj hn'
    simp only [edgeFinset_card,←card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hh
    omega
  have hR := hopt.max_energy s t hs heR
  have hL := hopt.max_energy t s ht heL
  have henergy := paired_energy G s t hn hd
  have hsum : (∑ x : V, 2*((Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) -
        (Nat.card (G.neighborSet x) : ℤ))^2) ≤ 0 := by omega
  have heach (x : V) : Nat.card ((G.replaceVertex s t).neighborSet x) =
      Nat.card (G.neighborSet x) := by
    have hh := (single_le_sum (f := fun x : V =>
      2*((Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) -
        (Nat.card (G.neighborSet x) : ℤ))^2)
      (fun y _ => mul_nonneg (by norm_num) (sq_nonneg _)) (mem_univ x)).trans hsum
    have hz : ((Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) -
        (Nat.card (G.neighborSet x) : ℤ))^2 = 0 := by
      nlinarith [sq_nonneg
          ((Nat.card ((G.replaceVertex s t).neighborSet x) : ℤ) - (Nat.card (G.neighborSet x) : ℤ))]
    have hh := sq_eq_zero_iff.mp hz
    omega
  ext x
  change G.Adj s x ↔ G.Adj t x
  by_cases hxt : x = t
  · subst x
    simp [hn]
  · have hh := replace_degree_other G s t x hxt
    rw [heach x] at hh
    suffices hiff : G.Adj x s ↔ G.Adj x t from
      ⟨fun h => (hiff.mp h.symm).symm,fun h => (hiff.mpr h.symm).symm⟩
    by_cases hxs : G.Adj x s <;> by_cases hxt' : G.Adj x t <;>
      simp only [hxs,hxt',ite_true,ite_false] at hh ⊢ <;> omega

lemma twins_card_or_degree [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hf : H.Free G)
    (S : Finset V) {v : V}
    (hTw : ∀ u ∈ S, G.neighborSet u = G.neighborSet v) :
    S.card < Fintype.card W ∨ Nat.card (G.neighborSet v) < Fintype.card W := by
  classical
  by_contra hh
  push_neg at hh
  obtain ⟨A,hAS,hAc⟩ := exists_subset_card_eq hh.1
  have hd : Fintype.card W ≤ (G.neighborFinset v).card := by
    simpa only [card_neighborFinset_eq_degree,←card_neighborSet_eq_degree,
      Fintype.card_eq_nat_card] using hh.2
  obtain ⟨B,hBN,hBc⟩ := exists_subset_card_eq hd
  apply hf
  apply (Erdos713KST.bipartite_contained H hHB).trans
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨A,B,by simpa using hAc,by simpa using hBc,?_⟩
  intro a ha b hb
  have hb' : b ∈ G.neighborSet v := by simpa using hBN hb
  rw [← hTw a (hAS ha)] at hb'
  exact hb'

lemma twins_mass_bound [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hf : H.Free G)
    (S : Finset V) (hTw : ∀ u ∈ S, ∀ v ∈ S, G.neighborSet u = G.neighborSet v) :
    (∑ v ∈ S, Nat.card (G.neighborSet v)) ≤ Fintype.card W * Fintype.card V := by
  classical
  obtain hS | ⟨v,hv⟩ := S.eq_empty_or_nonempty
  · simp [hS]
  have he : (∑ u ∈ S, Nat.card (G.neighborSet u)) = S.card * Nat.card (G.neighborSet v) := by
    calc
      _ = ∑ _u ∈ S, Nat.card (G.neighborSet v) := by
        apply sum_congr rfl
        intro u hu
        rw [hTw u hu v hv]
      _ = _ := by simp
  rw [he]
  rcases twins_card_or_degree hHB hf S (fun u hu => hTw u hu v hv) with hcard | hdeg
  · have hdeg' : Nat.card (G.neighborSet v) ≤ Fintype.card V := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_le _
    exact Nat.mul_le_mul hcard.le hdeg'
  · calc
      _ ≤ Fintype.card V * Fintype.card W := Nat.mul_le_mul (card_le_univ S) hdeg.le
      _ = _ := Nat.mul_comm _ _

open scoped Classical in
lemma Optimal.safe_mass_bound [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hopt : Optimal H G) :
    (∑ v : V, if H.Free (clone G v) then Nat.card (G.neighborSet v) else 0) ≤
      2*Fintype.card W*Fintype.card V := by
  classical
  obtain ⟨c⟩ := hopt.bipartite
  let S (i : Fin 2) : Finset V := {v | H.Free (clone G v) ∧ c v = i}
  have hbound (i : Fin 2) : (∑ v ∈ S i, Nat.card (G.neighborSet v)) ≤
      Fintype.card W * Fintype.card V := by
    apply twins_mass_bound hHB hopt.free
    intro u hu v hv
    obtain ⟨hsu,hcu⟩ : H.Free (clone G u) ∧ c u = i := by simpa [S] using hu
    obtain ⟨hsv,hcv⟩ : H.Free (clone G v) ∧ c v = i := by simpa [S] using hv
    apply hopt.cloneOptimal.safe_twins (fun h => c.valid h (hcu.trans hcv.symm)) hsu hsv
  have he : (∑ v : V, if H.Free (clone G v) then Nat.card (G.neighborSet v) else 0) =
      (∑ v ∈ S 0, Nat.card (G.neighborSet v)) + (∑ v ∈ S 1, Nat.card (G.neighborSet v)) := by
    simp only [S,sum_filter]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases hv : H.Free (clone G v)
    · have hcv : c v = 0 ∨ c v = 1 := by omega
      rcases hcv with hcv | hcv <;> simp [hv,hcv]
    · simp [hv]
  rw [he]
  have h0 := hbound 0
  have h1 := hbound 1
  nlinarith

lemma Optimal.obstruction_mass [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hopt : Optimal H G) :
    2*(Nat.card G.edgeSet : ℝ)-2*Fintype.card W*Fintype.card V ≤
      Erdos713CloneAverage.mass H G := by
  classical
  have hs := hopt.safe_mass_bound hHB
  have hsR : (∑ v : V, if H.Free (clone G v) then (Nat.card (G.neighborSet v) : ℝ) else 0) ≤
      2*(Fintype.card W : ℝ)*Fintype.card V := by exact_mod_cast hs
  have hsplit : Erdos713CloneAverage.mass H G +
      (∑ v : V, if H.Free (clone G v) then (Nat.card (G.neighborSet v) : ℝ) else 0) =
        2*(Nat.card G.edgeSet : ℝ) := by
    unfold Erdos713CloneAverage.mass
    rw [←sum_add_distrib]
    calc
      _ = ∑ v : V, (Nat.card (G.neighborSet v) : ℝ) := by
        apply sum_congr rfl
        intro v _
        by_cases hv : SingleFold H G v
        · have hn : ¬ H.Free (clone G v) := fun h => h hv.obstructed
          simp [hv,hn]
        · have hn : H.Free (clone G v) := fun h => hv (fold_of_obstructed H G v hopt.free h)
          simp [hv,hn]
      _ = _ := by
        have hh := G.sum_degrees_eq_twice_card_edges
        simp only [edgeFinset_card,←card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hh
        exact_mod_cast hh
  linarith

lemma exists_clique_nonneighbor_cover [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    ∃ C : Finset V, C ⊆ S ∧ G.IsClique (C : Set V) ∧
      ∀ v ∈ S, ∃ u ∈ C, ¬ G.Adj v u := by
  classical
  let T : Finset (Finset V) := S.powerset.filter (fun C => G.IsClique (C : Set V))
  have hT : T.Nonempty := ⟨∅,by simp [T]⟩
  obtain ⟨C,hC,hmax⟩ := T.exists_max_image Finset.card hT
  obtain ⟨hCS,hClique⟩ : C ⊆ S ∧ G.IsClique (C : Set V) := by simpa [T] using hC
  refine ⟨C,hCS,hClique,?_⟩
  intro v hv
  by_contra hh
  push_neg at hh
  have hvC : v ∉ C := fun h => G.loopless v (hh v h)
  have hCC : G.IsClique ((insert v C : Finset V) : Set V) := by
    rw [coe_insert,isClique_insert]
    exact ⟨hClique,fun u hu _ => hh u hu⟩
  have hCT : insert v C ∈ T := by
    simp only [T,mem_filter,mem_powerset]
    exact ⟨insert_subset hv hCS,hCC⟩
  have hc := hmax (insert v C) hCT
  rw [card_insert_of_notMem hvC] at hc
  omega

lemma free_clique_card_lt [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    (hf : H.Free G) {C : Finset V} (hC : G.IsClique (C : Set V)) : C.card < Fintype.card W := by
  classical
  have hcf : G.CliqueFree (Fintype.card W) :=
    cliqueFree_iff_top_free.mpr (fun h => hf ((IsContained.of_le (show H ≤ ⊤ from le_top)).trans h))
  by_contra hh
  obtain ⟨A,hAC,hAc⟩ := exists_subset_card_eq (Nat.le_of_not_lt hh)
  exact hcf A ⟨hC.subset hAC,hAc⟩

open scoped Classical in
lemma CloneOptimal.safe_mass_bound [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hf : H.Free G) (hopt : CloneOptimal H G) :
    (∑ v : V, if H.Free (clone G v) then Nat.card (G.neighborSet v) else 0) ≤
      (Fintype.card W)^2*Fintype.card V := by
  classical
  let S : Finset V := {v | H.Free (clone G v)}
  obtain ⟨C,hCS,hClique,hCover⟩ := exists_clique_nonneighbor_cover G S
  have hCard : C.card < Fintype.card W := free_clique_card_lt hf hClique
  let T (u : V) : Finset V := S.filter (fun v => ¬ G.Adj v u)
  have hTw (u : V) (hu : u ∈ C) (v : V) (hv : v ∈ T u) : G.neighborSet v = G.neighborSet u := by
    obtain ⟨hvS,hvu⟩ := mem_filter.mp hv
    have hvs : H.Free (clone G v) := by simpa only [S,mem_filter,mem_univ,true_and] using hvS
    have hus : H.Free (clone G u) := by simpa only [S,mem_filter,mem_univ,true_and] using hCS hu
    exact hopt.safe_twins hvu hvs hus
  have hBound (u : V) (hu : u ∈ C) : (∑ v ∈ T u, Nat.card (G.neighborSet v)) ≤
      Fintype.card W*Fintype.card V := by
    apply twins_mass_bound hHB hf
    intro v hv w hw
    exact (hTw u hu v hv).trans (hTw u hu w hw).symm
  calc
    _ = ∑ v ∈ S, Nat.card (G.neighborSet v) := by simp [S,sum_filter]
    _ ≤ ∑ u ∈ C, ∑ v ∈ T u, Nat.card (G.neighborSet v) := by
      simp only [T,sum_filter]
      rw [sum_comm]
      apply sum_le_sum
      intro v hv
      obtain ⟨u,hu,hvu⟩ := hCover v hv
      calc
        _ = if ¬ G.Adj v u then Nat.card (G.neighborSet v) else 0 := by simp [hvu]
        _ ≤ _ := single_le_sum (f := fun u : V => if ¬ G.Adj v u then Nat.card (G.neighborSet v) else 0)
          (fun _ _ => Nat.zero_le _) hu
    _ ≤ ∑ _u ∈ C, Fintype.card W*Fintype.card V := sum_le_sum hBound
    _ = C.card*(Fintype.card W*Fintype.card V) := by simp
    _ ≤ (Fintype.card W)^2*Fintype.card V := by
      calc
        _ ≤ Fintype.card W*(Fintype.card W*Fintype.card V) :=
          Nat.mul_le_mul_right _ hCard.le
        _ = _ := by ring

/-- Ordinary extremality with the same degree-square tie-breaker. -/
structure OrdinaryOptimal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : Prop where
  free : H.Free G
  max_edges : ∀ K : SimpleGraph V, H.Free K → Nat.card K.edgeSet ≤ Nat.card G.edgeSet
  max_energy : ∀ K : SimpleGraph V, H.Free K →
    Nat.card K.edgeSet = Nat.card G.edgeSet → degreeEnergy K ≤ degreeEnergy G

lemma OrdinaryOptimal.cloneOptimal [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hopt : OrdinaryOptimal H G) : CloneOptimal H G where
  max_edges s t hs := hopt.max_edges _ (safe_replace hs t)
  max_energy s t hs he := hopt.max_energy _ (safe_replace hs t) he

lemma exists_ordinary_optimal (H : SimpleGraph W) (hEdge : ∃ a b, H.Adj a b) (n : ℕ) :
    ∃ G : SimpleGraph (Fin n), OrdinaryOptimal H G ∧ Nat.card G.edgeSet = extremalNumber n H := by
  classical
  obtain ⟨G₀,hf₀,he₀⟩ := Erdos713CloneAverage.exists_extremal_family H hEdge
  let S : Finset (SimpleGraph (Fin n)) := {G | H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H}
  have hS : S.Nonempty := ⟨G₀ n,by simpa [S] using And.intro (hf₀ n) (he₀ n)⟩
  obtain ⟨G,hG,hmax⟩ := S.exists_max_image degreeEnergy hS
  obtain ⟨hf,he⟩ : H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H := by simpa [S] using hG
  refine ⟨G,⟨hf,?_,?_⟩,he⟩
  · intro K hK
    rw [he]
    have hh := card_edgeFinset_le_extremalNumber hK
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Fintype.card_fin,Nat.card_fin] using hh
  · intro K hK hKe
    apply hmax K
    simpa only [S,mem_filter,mem_univ,true_and] using And.intro hK (hKe.trans he)

lemma OrdinaryOptimal.obstruction_mass [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hopt : OrdinaryOptimal H G) :
    2*(Nat.card G.edgeSet : ℝ)-(Fintype.card W : ℝ)^2*Fintype.card V ≤
      Erdos713CloneAverage.mass H G := by
  classical
  have hs := hopt.cloneOptimal.safe_mass_bound hHB hopt.free
  have hsR : (∑ v : V, if H.Free (clone G v) then (Nat.card (G.neighborSet v) : ℝ) else 0) ≤
      (Fintype.card W : ℝ)^2*Fintype.card V := by exact_mod_cast hs
  have hsplit : Erdos713CloneAverage.mass H G +
      (∑ v : V, if H.Free (clone G v) then (Nat.card (G.neighborSet v) : ℝ) else 0) =
        2*(Nat.card G.edgeSet : ℝ) := by
    unfold Erdos713CloneAverage.mass
    rw [←sum_add_distrib]
    calc
      _ = ∑ v : V, (Nat.card (G.neighborSet v) : ℝ) := by
        apply sum_congr rfl
        intro v _
        by_cases hv : SingleFold H G v
        · have hn : ¬ H.Free (clone G v) := fun h => h hv.obstructed
          simp [hv,hn]
        · have hn : H.Free (clone G v) := fun h => hv (fold_of_obstructed H G v hopt.free h)
          simp [hv,hn]
      _ = _ := by
        have hh := G.sum_degrees_eq_twice_card_edges
        simp only [edgeFinset_card,←card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hh
        exact_mod_cast hh
  linarith

open scoped Classical in
lemma CloneOptimal.high_safe_card [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hf : H.Free G) (hopt : CloneOptimal H G) :
    (univ.filter (fun v => H.Free (clone G v) ∧ Fintype.card W ≤ Nat.card (G.neighborSet v))).card ≤
      (Fintype.card W)^2 := by
  classical
  let S : Finset V := {v | H.Free (clone G v) ∧ Fintype.card W ≤ Nat.card (G.neighborSet v)}
  obtain ⟨C,hCS,hClique,hCover⟩ := exists_clique_nonneighbor_cover G S
  have hCard : C.card < Fintype.card W := free_clique_card_lt hf hClique
  let T (u : V) : Finset V := S.filter (fun v => ¬ G.Adj v u)
  have hBound (u : V) (hu : u ∈ C) : (T u).card ≤ Fintype.card W := by
    obtain ⟨hus,huDeg⟩ : H.Free (clone G u) ∧ Fintype.card W ≤ Nat.card (G.neighborSet u) := by
      simpa only [S,mem_filter,mem_univ,true_and] using hCS hu
    have hTw (v : V) (hv : v ∈ T u) : G.neighborSet v = G.neighborSet u := by
      obtain ⟨hvS,hvu⟩ := mem_filter.mp hv
      obtain ⟨hvs,_⟩ : H.Free (clone G v) ∧ Fintype.card W ≤ Nat.card (G.neighborSet v) := by
        simpa only [S,mem_filter,mem_univ,true_and] using hvS
      exact hopt.safe_twins hvu hvs hus
    rcases twins_card_or_degree hHB hf (T u) hTw with hsmall | hsmall
    · exact hsmall.le
    · omega
  change S.card ≤ _
  calc
    _ = ∑ _v ∈ S, (1 : ℕ) := by simp
    _ ≤ ∑ u ∈ C, (T u).card := by
      simp only [Finset.card_eq_sum_ones,T,sum_filter]
      rw [sum_comm]
      apply sum_le_sum
      intro v hv
      obtain ⟨u,hu,hvu⟩ := hCover v hv
      calc
        _ = if ¬ G.Adj v u then (1 : ℕ) else 0 := by simp [hvu]
        _ ≤ _ := single_le_sum (f := fun u : V => if ¬ G.Adj v u then (1 : ℕ) else 0)
          (fun _ _ => Nat.zero_le _) hu
    _ ≤ ∑ _u ∈ C, Fintype.card W := sum_le_sum hBound
    _ = C.card*Fintype.card W := by simp
    _ ≤ (Fintype.card W)^2 := by nlinarith

open scoped Classical in
lemma CloneOptimal.safe_card_of_min_degree [Fintype V] {H : SimpleGraph W} [Fintype W]
    (hHB : H.IsBipartite) {G : SimpleGraph V} (hf : H.Free G) (hopt : CloneOptimal H G)
    (hmin : ∀ v, Fintype.card W ≤ Nat.card (G.neighborSet v)) :
    (univ.filter (fun v => H.Free (clone G v))).card ≤ (Fintype.card W)^2 := by
  simpa only [hmin,and_true] using hopt.high_safe_card hHB hf

lemma exists_ordinary_family (H : SimpleGraph W) (hEdge : ∃ a b, H.Adj a b) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin n),
      (∀ n, OrdinaryOptimal H (G n)) ∧
      (∀ n, Nat.card (G n).edgeSet = extremalNumber n H) := by
  choose G hopt he using exists_ordinary_optimal H hEdge
  exact ⟨G,hopt,he⟩

open Filter Asymptotics
open scoped Topology
lemma asymptotic_obstruction_mass [Fintype W] (H : SimpleGraph W) (hHB : H.IsBipartite)
    (G : (n : ℕ) → SimpleGraph (Fin n)) (hopt : ∀ n, OrdinaryOptimal H (G n))
    (he : ∀ n, Nat.card (G n).edgeSet = extremalNumber n H)
    {α c : ℝ} (hα : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n => Erdos713CloneAverage.mass H (G n)/(extremalNumber n H : ℝ)) atTop (𝓝 2) := by
  have ht : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ)/(n : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using Erdos713FutureRecords.lower_ratio_top hα hc h
  have hi : Tendsto (fun n : ℕ => (n : ℝ)/(extremalNumber n H : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,inv_div] using tendsto_inv_atTop_zero.comp ht
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (extremalNumber n H : ℝ) := by
    filter_upwards [ht.eventually_gt_atTop 0] with n hn
    rcases div_pos_iff.mp hn with hh | hh
    · exact hh.1
    · exact ((not_lt_of_ge (Nat.cast_nonneg (extremalNumber n H))) hh.1).elim
  have hl : Tendsto (fun n : ℕ => (2 : ℝ)-(Fintype.card W : ℝ)^2 *
      ((n : ℝ)/(extremalNumber n H : ℝ))) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hpos] with n hn
    have hlo := (hopt n).obstruction_mass hHB
    simp only [he n,Fintype.card_fin] at hlo
    have hh := div_le_div_of_nonneg_right hlo hn.le
    convert hh using 1 <;> field_simp
  · filter_upwards [hpos] with n hn
    apply (div_le_iff₀ hn).mpr
    simpa only [he n] using Erdos713CloneAverage.mass_le H (G n)

lemma exists_asymptotic_obstruction_mass [Fintype W] (H : SimpleGraph W)
    (hHB : H.IsBipartite) (hEdge : ∃ a b, H.Adj a b)
    {α c : ℝ} (hα : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin n),
      (∀ n, OrdinaryOptimal H (G n)) ∧
      (∀ n, Nat.card (G n).edgeSet = extremalNumber n H) ∧
      Tendsto (fun n => Erdos713CloneAverage.mass H (G n)/(extremalNumber n H : ℝ)) atTop (𝓝 2) := by
  obtain ⟨G,hopt,he⟩ := exists_ordinary_family H hEdge
  exact ⟨G,hopt,he,asymptotic_obstruction_mass H hHB G hopt he hα hc h⟩

#print axioms CloneOptimal.safe_twins
#print axioms exists_optimal
#print axioms Optimal.safe_mass_bound
#print axioms Optimal.obstruction_mass
#print axioms CloneOptimal.safe_mass_bound
#print axioms exists_ordinary_optimal
#print axioms OrdinaryOptimal.obstruction_mass
#print axioms CloneOptimal.high_safe_card
#print axioms CloneOptimal.safe_card_of_min_degree
#print axioms exists_asymptotic_obstruction_mass
end Erdos713CloneSymm
