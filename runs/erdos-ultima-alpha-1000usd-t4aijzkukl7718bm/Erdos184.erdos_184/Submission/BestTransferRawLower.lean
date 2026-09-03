import Submission.BestTransferRawData

/-! A full transfer along a Best singleton edge need not preserve the RAW
minimum count. No hull inequality or conjecture disproof is claimed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.BestTransferRaw
open Critical MaximumCycles Subfamilies SingletonExchange
open ChainRing (deg degree_eq_of_adj_iff degree_zero_of_no_adj even_two_degrees degree_split_at deg_mono)
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
lemma block_internal_degree {S : SimpleGraph V} (hS : S ≤ source) (i : Fin 2) (v : V)
    (hl : v ≠ leftPort i) (hr : v ≠ rightPort i) :
    deg (S ⊓ block i) v = deg S v ∨ deg (S ⊓ block i) v = 0 := by
  rcases block_internal_or_zero i v hl hr with h | h
  · left
    apply degree_eq_of_adj_iff
    intro w
    exact ⟨And.left,fun hw => ⟨hw,(h w).mpr (hS hw)⟩⟩
  · right
    exact degree_zero_of_no_adj (S ⊓ block i) v (fun w hw => h w hw.2)

lemma block_boundary_even {S : SimpleGraph V} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (i : Fin 2) :
    Even (deg (S ⊓ block i) (leftPort i) + deg (S ⊓ block i) (rightPort i)) := by
  apply even_two_degrees _ (ports_ne i)
  intro v hl hr
  rcases block_internal_degree hS i v hl hr with h | h
  · rw [h]; exact heven v
  · rw [h]; exact ⟨0,rfl⟩

lemma inf_closing (S : SimpleGraph V) :
    S ⊓ closing = if S.Adj (0 : V) (9 : V) then closing else ⊥ := by
  ext x y
  simp only [SimpleGraph.inf_adj]
  split_ifs with h
  · constructor
    · exact And.right
    · intro hc
      rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨h,hc⟩
      · exact ⟨h.symm,hc⟩
  · constructor
    · rintro ⟨hs,hc⟩
      rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h hs
      · exact h hs.symm
    · exact False.elim


noncomputable def closingCount (S : SimpleGraph V) : ℕ := if S.Adj 0 9 then 1 else 0
lemma closingCount_le (S : SimpleGraph V) : closingCount S ≤ 1 := by unfold closingCount; split_ifs <;> omega
lemma closing_degree_at (S : SimpleGraph V) :
    deg (S ⊓ closing) 0 = closingCount S ∧ deg (S ⊓ closing) 9 = closingCount S := by
  rw [inf_closing]
  unfold closingCount
  split_ifs
  · have h0 := closing_degree_left
    have h9 := closing_degree_right
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using And.intro h0 h9
  · simp [deg]

lemma port_splits {S : SimpleGraph V} (hS : S ≤ source) :
    deg S 0 = deg (S ⊓ block 0) 0 + deg (S ⊓ closing) 0 ∧
    deg S 3 = deg (S ⊓ block 0) 3 + deg (S ⊓ block 1) 3 ∧
    deg S 9 = deg (S ⊓ block 1) 9 + deg (S ⊓ closing) 9 := by
  have c0 : ∀ w, source.Adj 0 w → (block 0).Adj 0 w ∨ closing.Adj 0 w := by decide +kernel
  have c3 : ∀ w, source.Adj 3 w → (block 0).Adj 3 w ∨ (block 1).Adj 3 w := by decide +kernel
  have c9 : ∀ w, source.Adj 9 w → (block 1).Adj 9 w ∨ closing.Adj 9 w := by decide +kernel
  exact ⟨degree_split_at S (block 0) closing 0 (fun w h => c0 w (hS h)) (by decide +kernel),
    degree_split_at S (block 0) (block 1) 3 (fun w h => c3 w (hS h)) (by decide +kernel),
    degree_split_at S (block 1) closing 9 (fun w h => c9 w (hS h)) (by decide +kernel)⟩

lemma boundary_parity {S : SimpleGraph V} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (i : Fin 2) :
    deg (S ⊓ block i) (leftPort i) % 2 = closingCount S ∧
      deg (S ⊓ block i) (rightPort i) % 2 = closingCount S := by
  have hb0 := block_boundary_even hS heven 0
  have hb1 := block_boundary_even hS heven 1
  have hp := port_splits hS
  have hc := closing_degree_at S
  have he0 := heven 0
  have he3 := heven 3
  have he9 := heven 9
  change Even (deg (S ⊓ block 0) 0 + deg (S ⊓ block 0) 3) at hb0
  change Even (deg (S ⊓ block 1) 3 + deg (S ⊓ block 1) 9) at hb1
  rw [Nat.even_iff] at hb0 hb1 he0 he3 he9
  have hl := closingCount_le S
  fin_cases i
  · change deg (S ⊓ block 0) 0 % 2 = closingCount S ∧ deg (S ⊓ block 0) 3 % 2 = closingCount S
    omega
  · change deg (S ⊓ block 1) 3 % 2 = closingCount S ∧ deg (S ⊓ block 1) 9 % 2 = closingCount S
    omega
lemma block_even_of_no_closing {S : SimpleGraph V} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (he : ¬ S.Adj (0 : V) (9 : V)) (i : Fin 2) :
    ∀ v, Even (deg (S ⊓ block i) v) := by
  intro v
  have hp := boundary_parity hS heven i
  simp only [closingCount,if_neg he] at hp
  by_cases hl : v = leftPort i
  · rw [hl,Nat.even_iff]; exact hp.1
  by_cases hr : v = rightPort i
  · rw [hr,Nat.even_iff]; exact hp.2
  rcases block_internal_degree hS i v hl hr with h | h
  · rw [h]; exact heven v
  · rw [h]; exact ⟨0,rfl⟩

lemma block_boundary_one {S : SimpleGraph V} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (hmax : ∀ v, deg S v ≤ 2)
    (he : S.Adj (0 : V) (9 : V)) (i : Fin 2) :
    deg (S ⊓ block i) (leftPort i) = 1 ∧ deg (S ⊓ block i) (rightPort i) = 1 := by
  have hp := boundary_parity hS heven i
  simp only [closingCount,if_pos he] at hp
  have hl := (deg_mono (inf_le_left : S ⊓ block i ≤ S) (leftPort i)).trans (hmax _)
  have hr := (deg_mono (inf_le_left : S ⊓ block i ≤ S) (rightPort i)).trans (hmax _)
  omega

lemma cycle_piece_even_max (H : source.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∀ v, Even (deg H.spanningCoe v)) ∧ (∀ v, deg H.spanningCoe v ≤ 2) := by
  have hd (v : V) : deg H.spanningCoe v = if v ∈ H.verts then 2 else 0 := by
    have hh := regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh
  constructor
  · intro v
    rw [hd]
    split_ifs <;> decide
  · intro v
    rw [hd]
    split_ifs <;> omega

lemma single_piece_edges (H : source.Subgraph) (hH : H.coe.edgeFinset.card = 1) :
    ∃ e, H.edgeSet = {e} := by
  apply Set.ncard_eq_one.mp
  have hh := (subgraph_edge_card H).trans hH
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hh

lemma piece_edges_nonempty (H : source.Subgraph) (hH : IsCycleOrEdge H.coe) : H.edgeSet.Nonempty := by
  rcases hH with hc | hs
  · exact cycle_piece_edgeSet_nonempty H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc)
  · obtain ⟨e,he⟩ := single_piece_edges H hs
    exact ⟨e,he.symm ▸ Set.mem_singleton e⟩

lemma cycle_without_closing_local (H : source.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (he : ¬ H.spanningCoe.Adj (0 : V) (9 : V)) : ∃ i, H.spanningCoe ≤ block i := by
  obtain ⟨e,heH⟩ := cycle_piece_edgeSet_nonempty H (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH)
  have hcode := GraphCircuitCode.cycle_circuit H (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH)
  have heven := (cycle_piece_even_max H hH).1
  induction e using Sym2.ind with | h x y =>
  rcases source_edge_cases x y (H.edgeSet_subset heH) with hc | ⟨i,hi⟩
  · rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (he heH).elim
    · exact (he (show H.spanningCoe.Adj (0 : V) (9 : V) from heH.symm)).elim
  · let T := H.spanningCoe ⊓ block i
    have hTe : ∀ v, Even (T.degree v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
        block_even_of_no_closing H.spanningCoe_le heven he i
    have hv : (GraphCircuitCode.code source).valid T.edgeFinset := by
      refine ⟨T,inf_le_left.trans H.spanningCoe_le,?_,?_⟩
      · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hTe
      · ext e
        simp only [SimpleGraph.mem_edgeFinset]
    have hsub : T.edgeFinset ⊆ H.spanningCoe.edgeFinset := SimpleGraph.edgeFinset_mono inf_le_left
    have hn : T.edgeFinset.Nonempty := ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr ⟨heH,hi⟩⟩
    have heq := hcode.2.2 _ hsub hv hn
    have hTG : T = H.spanningCoe := SimpleGraph.edgeFinset_inj.mp heq
    exact ⟨i,hTG ▸ (show T ≤ block i from inf_le_right)⟩

lemma piece_without_closing_local (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : ¬ H.spanningCoe.Adj (0 : V) (9 : V)) : ∃ i, H.spanningCoe ≤ block i := by
  rcases hH with hc | hs
  · exact cycle_without_closing_local H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc) he
  · obtain ⟨e,hed⟩ := single_piece_edges H hs
    have heH : e ∈ H.edgeSet := hed.symm ▸ Set.mem_singleton e
    induction e using Sym2.ind with | h x y =>
    rcases source_edge_cases x y (H.edgeSet_subset heH) with hc | ⟨i,hi⟩
    · rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (he heH).elim
      · exact (he (show H.spanningCoe.Adj (0 : V) (9 : V) from heH.symm)).elim
    · refine ⟨i,?_⟩
      intro a b hab
      have hm : s(a,b) ∈ H.edgeSet := hab
      rw [hed,Set.mem_singleton_iff] at hm
      change s(a,b) ∈ (block i).edgeSet
      exact hm.symm ▸ hi

lemma single_closing_le (H : source.Subgraph) (hs : H.coe.edgeFinset.card = 1)
    (he : H.spanningCoe.Adj (0 : V) (9 : V)) : H.spanningCoe ≤ closing := by
  obtain ⟨e,hed⟩ := single_piece_edges H hs
  have he' : s((0 : V),(9 : V)) = e := by
    have hm : s((0 : V),(9 : V)) ∈ H.edgeSet := he
    simpa only [hed,Set.mem_singleton_iff] using hm
  intro x y hxy
  have hm : s(x,y) ∈ H.edgeSet := hxy
  rw [hed,Set.mem_singleton_iff,← he'] at hm
  change s(x,y) ∈ closing.edgeSet
  rw [hm]
  exact (closing_adj_iff _ _).mpr (Or.inl ⟨rfl,rfl⟩)


lemma hub_sum (i : Fin 2) (f : V → ℕ) :
    (∑ v ∈ hubs i, f v) = f (leftPort i) + f (hubOne i) + f (hubTwo i) := by
  fin_cases i <;> simp [hubs,leftPort,hubOne,hubTwo,add_assoc]

def residual (H : source.Subgraph) : SimpleGraph V := source \ H.spanningCoe
def rowResidual (H : source.Subgraph) (i : Fin 2) : SimpleGraph V := residual H ⊓ block i

lemma residual_degree_add (H : source.Subgraph) (i : Fin 2) (v : V) :
    deg (rowResidual H i) v + deg (H.spanningCoe ⊓ block i) v = deg (block i) v := by
  have he : rowResidual H i = block i \ (H.spanningCoe ⊓ block i) := by
    ext x y
    have hh := block_le_source i (v := x) (w := y)
    simp only [rowResidual,residual,SimpleGraph.inf_adj,SimpleGraph.sdiff_adj]
    tauto
  rw [he]
  have h := degree_sdiff_add (block i) (H.spanningCoe ⊓ block i) inf_le_right v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h

lemma rowResidual_number_ge_six (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : H.spanningCoe.Adj 0 9) (i : Fin 2) : 6 ≤ number (rowResidual H i) := by
  let R := rowResidual H i
  have hRS : R ≤ source := inf_le_left.trans sdiff_le
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum R
  have hs := sizes i
  have hb := block_degrees i
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb
  rcases hH with hc | hsH
  · have hcy : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
      simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    have hcm := cycle_piece_even_max H hcy
    have hbd := block_boundary_one H.spanningCoe_le hcm.1 hcm.2 he i
    have ha := residual_degree_add H i (leftPort i)
    have h1 := residual_degree_add H i (hubOne i)
    have h2 := residual_degree_add H i (hubTwo i)
    have h1m := (deg_mono (inf_le_left : H.spanningCoe ⊓ block i ≤ H.spanningCoe) (hubOne i)).trans (hcm.2 _)
    have h2m := (deg_mono (inf_le_left : H.spanningCoe ⊓ block i ≤ H.spanningCoe) (hubTwo i)).trans (hcm.2 _)
    have hsum : 12 ≤ ∑ v ∈ hubs i, deg R v := by
      rw [hub_sum]
      change 12 ≤ deg (rowResidual H i) (leftPort i) + deg (rowResidual H i) (hubOne i) + deg (rowResidual H i) (hubTwo i)
      dsimp only [deg,R] at *
      omega
    have hodd : ∀ v ∈ rights i, Odd (R.degree v) := by
      intro v hv
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.odd_iff]
      rcases rights_cover i v hv with rfl | hv
      · have h := residual_degree_add H i (rightPort i)
        change deg R (rightPort i) % 2 = 1
        dsimp only [deg,R] at *
        omega
      · have hd := interior_degree i v hv
        have hp := interior_not_ports i v hv
        have hh := block_internal_degree H.spanningCoe_le i v hp.1 hp.2
        have hm : Even (deg (H.spanningCoe ⊓ block i) v) := by
          rcases hh with hh | hh
          · rw [hh]; exact hcm.1 v
          · rw [hh]; exact ⟨0,rfl⟩
        have ha := residual_degree_add H i v
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
        rw [Nat.even_iff] at hm
        change deg R v % 2 = 1
        dsimp only [deg,R] at *
        omega
    have hl := ParityDegreeLower.independent_odd_degree_bound D hD hdec
      (hubs i) (rights i) (rights i) (by rw [hs.1]; decide) (hubs_rights_disjoint i)
      (fun u hu v hv huv => rights_independent i u hu v hv (hRS huv)) hodd hodd
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl
    change _ ≤ 2 * (hubs i).card * D.card at hl
    rw [hs.1,hs.2.1,hcard] at hl
    change 6 ≤ number R
    dsimp only [deg,R] at *
    omega
  · have hle := single_closing_le H hsH he
    have hz : H.spanningCoe ⊓ block i = ⊥ := by
      ext x y
      exact ⟨fun h => (block_no_closing i x y ⟨h.2,hle h.1⟩).elim,False.elim⟩
    have hdeg (v : V) : deg R v = deg (block i) v := by
      have hh := residual_degree_add H i v
      rw [hz] at hh
      simpa [deg,R] using hh
    have hsum : (∑ v ∈ hubs i, deg R v) = 17 := by
      rw [hub_sum,hdeg,hdeg,hdeg]
      dsimp only [deg,R] at *
      omega
    have hodd : ∀ v ∈ interiorRights i, Odd (R.degree v) := by
      intro v hv
      have hd := interior_degree i v hv
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd ⊢
      change Odd (deg R v)
      rw [hdeg]
      rw [show deg (block i) v = 3 from hd]
      decide
    have hl := ParityDegreeLower.independent_odd_degree_bound D hD hdec
      (hubs i) (interiorRights i) (interiorRights i) (by rw [hs.1]; decide) (hubs_interior_disjoint i)
      (fun u hu v hv huv => rights_independent i u (interior_subset i hu) v (interior_subset i hv) (hRS huv)) hodd hodd
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl
    change _ ≤ 2 * (hubs i).card * D.card at hl
    rw [hsum,hs.1,hs.2.2,hcard] at hl
    change 6 ≤ number R
    dsimp only [deg,R] at *
    omega
lemma family_block_lower (R : SimpleGraph V) (hR : R ≤ base)
    (D : Finset source.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hp : Set.PairwiseDisjoint (D : Set source.Subgraph) (fun H => H.edgeSet))
    (hu : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) :
    (∑ i : Fin 2, number (R ⊓ block i)) ≤ D.card := by
  have hle (H) (hH : H ∈ D) : H.spanningCoe ≤ R := by
    intro x y hxy
    have hm : s(x,y) ∈ ⋃ K ∈ D, K.edgeSet :=
      Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,hxy⟩⟩
    rwa [hu] at hm
  have hlocal (H) (hH : H ∈ D) : ∃ i, H.spanningCoe ≤ block i :=
    piece_without_closing_local H (hD H hH) (fun he => base_no_closing (hR (hle H hH he)))
  let f : source.Subgraph → Fin 2 := fun H => if h : H ∈ D then Classical.choose (hlocal H h) else 0
  have hf (H) (hH : H ∈ D) : H.spanningCoe ≤ block (f H) := by
    dsimp only [f]
    rw [dif_pos hH]
    exact Classical.choose_spec (hlocal H hH)
  let A (i : Fin 2) := D.filter (fun H => f H = i)
  have hcover (i : Fin 2) : (⋃ H ∈ A i, H.edgeSet) = (R ⊓ block i).edgeSet := by
    ext e
    induction e using Sym2.ind with | h x y =>
    constructor
    · intro he
      obtain ⟨H,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hH,heH⟩ := Set.mem_iUnion.mp he
      obtain ⟨hHD,hfi⟩ := Finset.mem_filter.mp hH
      exact ⟨hle H hHD heH,hfi ▸ hf H hHD heH⟩
    · rintro ⟨heR,heB⟩
      have heR' : s(x,y) ∈ ⋃ H ∈ D, H.edgeSet := hu.symm ▸ heR
      obtain ⟨H,he⟩ := Set.mem_iUnion.mp heR'
      obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp he
      have hfi : f H = i := by
        by_contra hn
        exact blocks_disjoint (f H) i hn x y ⟨hf H hHD heH,heB⟩
      exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hHD,hfi⟩,heH⟩⟩
  have hn (i : Fin 2) : number (R ⊓ block i) ≤ (A i).card := by
    have hh := number_le (lowerFamily (A i) (hcover i))
      (lowerFamily_property IsCycleOrEdge (A i) (hcover i)
        (fun H hH => hD H (Finset.mem_filter.mp hH).1))
      (lowerFamily_decomposition (A i) (hcover i)
        (fun _ hH _ hK hne => hp (Finset.mem_filter.mp hH).1 (Finset.mem_filter.mp hK).1 hne))
    simpa only [lowerFamily_card] using hh
  calc
    _ ≤ ∑ i : Fin 2, (A i).card := Finset.sum_le_sum (fun i _ => hn i)
    _ = D.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (by
        intro H hH
        exact Finset.mem_univ (f H))

lemma residual_le_base (H : source.Subgraph)
    (he : H.spanningCoe.Adj 0 9) : residual H ≤ base := by
  intro x y hxy
  rcases source_edge_cases x y hxy.1 with hc | ⟨i,hi⟩
  · rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (hxy.2 he).elim
    · exact (hxy.2 he.symm).elim
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

lemma source_number_ge_thirteen : 13 ≤ number source := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum source
  have he : s((0 : V),(9 : V)) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ source_closing
  obtain ⟨H,he⟩ := Set.mem_iUnion.mp he
  obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp he
  let A := D.erase H
  have hAD : A ⊆ D := Finset.erase_subset _ _
  have hcover : (⋃ K ∈ A, K.edgeSet) = (residual H).edgeSet := by
    rw [residual,SimpleGraph.edgeSet_sdiff]
    ext e
    constructor
    · intro he
      obtain ⟨K,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp he
      exact ⟨K.edgeSet_subset heK,fun heH =>
        Set.disjoint_left.mp (hdec.1 (hAD hK) hHD (Finset.mem_erase.mp hK).1) heK heH⟩
    · rintro ⟨heG,heH⟩
      rw [← hdec.2] at heG
      obtain ⟨K,heG⟩ := Set.mem_iUnion.mp heG
      obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp heG
      have hne : K ≠ H := by rintro rfl; exact heH heK
      exact Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hne,hK⟩,heK⟩⟩
  have hl := family_block_lower (residual H) (residual_le_base H heH) A
    (fun K hK => hD K (hAD hK)) (fun _ hK _ hL hne => hdec.1 (hAD hK) (hAD hL) hne) hcover
  have hs : 12 ≤ ∑ i : Fin 2, number (rowResidual H i) := by
    calc
      _ = ∑ _i : Fin 2, 6 := by decide
      _ ≤ _ := Finset.sum_le_sum (fun i _ => rowResidual_number_ge_six H (hD H hHD) heH i)
  have hc : A.card + 1 = D.card := Finset.card_erase_add_one hHD
  change (∑ i : Fin 2, number (rowResidual H i)) ≤ A.card at hl
  omega


end Erdos184Work.BestTransferRaw
#print axioms Erdos184Work.BestTransferRaw.source_number_ge_thirteen
