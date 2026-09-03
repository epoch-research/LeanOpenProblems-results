import Submission.PetersenSubfamilyFractional
import Submission.Cycles

/-!
Projection from the actual 25-vertex simple subdivision of doubled Petersen
to the complete circuit-multiplicity certificate. This is auxiliary graph
infrastructure, not a settlement of Erdős 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.DoubledPetersenSimple
open DoubledPetersenCertificate (ends incident Multiplicity EvenVector NonzeroVector MinimalEven)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

abbrev V := Fin 25
abbrev E := Fin 15
abbrev Core := Fin 10
abbrev OccEdge := E × Fin 3

def old (v : Core) : V := ⟨v.val,by omega⟩
def mid (e : E) : V := ⟨10+e.val,by omega⟩
def edge (e : E) : Fin 3 → Sym2 V :=
  ![s(old (ends e).1,old (ends e).2),s(old (ends e).1,mid e),s(mid e,old (ends e).2)]
def edges : Finset (Sym2 V) := Finset.univ.image (fun p : OccEdge => edge p.1 p.2)
def G : SimpleGraph V := fromEdgeSet (edges : Set (Sym2 V))
instance : DecidableRel G.Adj := by unfold G; infer_instance
lemma edge_injective : Function.Injective (fun p : OccEdge => edge p.1 p.2) := by decide
lemma edge_mem (e : E) (j : Fin 3) : edge e j ∈ G.edgeSet := by revert e j; decide
lemma G_even (v : V) : Even (G.degree v) := by revert v; decide
lemma vertex_cases (v : V) : (∃ u : Core, old u = v) ∨ ∃ e : E, mid e = v := by
  revert v; decide
lemma edge_cases (x y : V) (h : G.Adj x y) : ∃ p : OccEdge, edge p.1 p.2 = s(x,y) := by
  revert x y; decide

def neigh : Core → Fin 3 → Core :=
  ![![1,4,5],![0,2,6],![1,3,7],![2,4,8],![0,3,9],![0,7,8],![1,8,9],![2,5,9],![3,5,6],![4,6,7]]
def coreNbr (v : Core) (p : Bool × Fin 3) : V :=
  if p.1 then mid (incident v p.2) else old (neigh v p.2)
def spoke (v : Core) (i : Fin 3) : Fin 3 :=
  if (ends (incident v i)).1 = v then 1 else 2
lemma spoke_cases (v : Core) (i : Fin 3) : spoke v i = 1 ∨ spoke v i = 2 := by
  simp only [spoke]; split_ifs <;> simp
lemma coreNbr_injective (v : Core) : Function.Injective (coreNbr v) := by revert v; decide
lemma coreNbr_complete (v : Core) (w : V) :
    G.Adj (old v) w ↔ ∃ i, coreNbr v i = w := by revert v w; decide
lemma coreNbr_false (v : Core) (i : Fin 3) :
    s(old v,coreNbr v (false,i)) = edge (incident v i) 0 := by revert v i; decide
lemma coreNbr_true (v : Core) (i : Fin 3) :
    s(old v,coreNbr v (true,i)) = edge (incident v i) (spoke v i) := by revert v i; decide

def midNbr (e : E) : Fin 2 → V := ![old (ends e).1,old (ends e).2]
lemma midNbr_injective (e : E) : Function.Injective (midNbr e) := by revert e; decide
lemma midNbr_complete (e : E) (w : V) :
    G.Adj (mid e) w ↔ ∃ i, midNbr e i = w := by revert e w; decide
lemma midNbr_zero (e : E) : s(mid e,midNbr e 0) = edge e 1 := by revert e; decide
lemma midNbr_one (e : E) : s(mid e,midNbr e 1) = edge e 2 := by revert e; decide

lemma degree_of_neighbors {W K : Type*} [Fintype W] [Fintype K]
    (B A : SimpleGraph W) (hAB : A ≤ B) (v : W) (n : K → W)
    (hi : Function.Injective n) (hc : ∀ w, B.Adj v w ↔ ∃ i, n i = w) :
    A.degree v = ∑ i, if A.Adj v (n i) then 1 else 0 := by
  let F : Finset K := Finset.univ.filter (fun i => A.Adj v (n i))
  have hN : A.neighborFinset v = F.image n := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image]
    constructor
    · intro hw
      obtain ⟨i,rfl⟩ := (hc w).mp (hAB hw)
      exact ⟨i,by simp [F,hw],rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact (Finset.mem_filter.mp hi).2
  rw [← SimpleGraph.card_neighborFinset_eq_degree,hN,Finset.card_image_of_injective F hi]
  simp [F]

noncomputable def ind (A : SimpleGraph V) (e : E) (j : Fin 3) : ℕ :=
  if edge e j ∈ A.edgeSet then 1 else 0
noncomputable def trace (A : SimpleGraph V) (e : E) : ℕ := ind A e 0 + ind A e 1
lemma ind_le_one (A : SimpleGraph V) (e : E) (j : Fin 3) : ind A e j ≤ 1 := by
  unfold ind; split_ifs <;> omega
lemma ind_pos_iff (A : SimpleGraph V) (e : E) (j : Fin 3) :
    0 < ind A e j ↔ edge e j ∈ A.edgeSet := by
  unfold ind; split_ifs <;> simp_all
lemma degree_mid (A : SimpleGraph V) (hAG : A ≤ G) (e : E) :
    A.degree (mid e) = ind A e 1 + ind A e 2 := by
  rw [degree_of_neighbors G A hAG (mid e) (midNbr e) (midNbr_injective e) (midNbr_complete e),
    Fin.sum_univ_two]
  have h0 : (if A.Adj (mid e) (midNbr e 0) then 1 else 0) = ind A e 1 := by
    unfold ind
    rw [← midNbr_zero]
    rfl
  have h1 : (if A.Adj (mid e) (midNbr e 1) then 1 else 0) = ind A e 2 := by
    unfold ind
    rw [← midNbr_one]
    rfl
  rw [h0,h1]

lemma spokes_equal (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v)) (e : E) :
    ind A e 1 = ind A e 2 := by
  have hh := he (mid e)
  rw [degree_mid A hAG e] at hh
  have h1 := ind_le_one A e 1
  have h2 := ind_le_one A e 2
  obtain ⟨k,hk⟩ := hh
  omega

lemma degree_old (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v)) (v : Core) :
    A.degree (old v) = trace A (incident v 0) + trace A (incident v 1) + trace A (incident v 2) := by
  rw [degree_of_neighbors G A hAG (old v) (coreNbr v) (coreNbr_injective v) (coreNbr_complete v)]
  have hf (i : Fin 3) : (if A.Adj (old v) (coreNbr v (false,i)) then 1 else 0) =
      ind A (incident v i) 0 := by
    unfold ind
    rw [← coreNbr_false]
    rfl
  have ht (i : Fin 3) : (if A.Adj (old v) (coreNbr v (true,i)) then 1 else 0) =
      ind A (incident v i) 1 := by
    have hh : (if A.Adj (old v) (coreNbr v (true,i)) then 1 else 0) =
        ind A (incident v i) (spoke v i) := by
      unfold ind
      rw [← coreNbr_true]
      rfl
    rw [hh]
    rcases spoke_cases v i with h | h
    · rw [h]
    · rw [h,← spokes_equal A hAG he]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Fin.sum_univ_three,hf,ht,trace]
  omega

lemma trace_even (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v)) :
    EvenVector (trace A) := by
  intro v
  have hh := he (old v)
  rw [degree_old A hAG he v] at hh
  exact Nat.even_iff.mp hh

lemma edge_pos_trace (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v))
    (e : E) (j : Fin 3) (hj : edge e j ∈ A.edgeSet) : 0 < trace A e := by
  have hp := (ind_pos_iff A e j).mpr hj
  fin_cases j
  · change 0 < ind A e 0 at hp
    dsimp [trace]; omega
  · change 0 < ind A e 1 at hp
    dsimp [trace]; omega
  · change 0 < ind A e 2 at hp
    have hh := spokes_equal A hAG he e
    dsimp [trace]
    omega

lemma trace_nonzero (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v))
    (hn : A ≠ ⊥) : NonzeroVector (trace A) := by
  obtain ⟨x,y,hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hn
  obtain ⟨⟨e,j⟩,hj⟩ := edge_cases x y (hAG hxy)
  have hp := edge_pos_trace A hAG he e j (hj.symm ▸ hxy)
  exact ⟨e,by omega⟩

lemma trace_pos_old_support (A : SimpleGraph V) (e : E) (hp : 0 < trace A e) :
    old (ends e).1 ∈ A.support := by
  have hh : 0 < ind A e 0 ∨ 0 < ind A e 1 := by
    dsimp [trace] at hp
    omega
  rcases hh with hh | hh
  · have ha := (ind_pos_iff A e 0).mp hh
    exact ⟨old (ends e).2,ha⟩
  · have ha := (ind_pos_iff A e 1).mp hh
    exact ⟨mid e,ha⟩

noncomputable def proj (v : V) : Core :=
  if h : v.val < 10 then ⟨v.val,h⟩ else (ends ⟨v.val-10,by omega⟩).1
lemma proj_old (v : Core) : proj (old v) = v := by revert v; decide
lemma proj_mid (e : E) : proj (mid e) = (ends e).1 := by revert e; decide
lemma incident_left (e : E) : ∃ i, incident (ends e).1 i = e := by revert e; decide
lemma incident_right (e : E) : ∃ i, incident (ends e).2 i = e := by revert e; decide
lemma edge_projection (e : E) (j : Fin 3) (x y : V) (h : edge e j = s(x,y)) :
    proj x = proj y ∨
      ((∃ i, incident (proj x) i = e) ∧ (∃ i, incident (proj y) i = e)) := by
  revert e j x y
  decide

lemma adj_projection (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v))
    {x y : V} (hxy : A.Adj x y) :
    proj x = proj y ∨ ∃ e : E, 0 < trace A e ∧
      (∃ i, incident (proj x) i = e) ∧ (∃ i, incident (proj y) i = e) := by
  obtain ⟨⟨e,j⟩,hj⟩ := edge_cases x y (hAG hxy)
  rcases edge_projection e j x y hj with h | h
  · exact Or.inl h
  · exact Or.inr ⟨e,edge_pos_trace A hAG he e j (hj.symm ▸ hxy),h⟩

def row (m : Multiplicity) (v : Core) : ℕ := ∑ i : Fin 3, m (incident v i)
lemma coordinate_le_row (m : Multiplicity) (v : Core) (i : Fin 3) :
    m (incident v i) ≤ row m v := by
  unfold row
  exact Finset.single_le_sum (f := fun i => m (incident v i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma row_saturate (m q : Multiplicity) (hq : ∀ e, q e ≤ m e) (heq : EvenVector q)
    (hm : ∀ v, row m v ≤ 2) (v : Core) (hp : 0 < row q v) :
    ∀ i, q (incident v i) = m (incident v i) := by
  have hle : row q v ≤ row m v := Finset.sum_le_sum (fun i _ => hq _)
  have hev : row q v % 2 = 0 := by
    simpa only [row,Fin.sum_univ_three] using heq v
  have hq2 : row q v = 2 := by have hh := hm v; omega
  have hm2 : row m v = 2 := by have hh := hm v; omega
  have hs : (∑ i : Fin 3, q (incident v i)) = ∑ i : Fin 3, m (incident v i) := by
    change row q v = row m v
    omega
  have hh := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hq _)).mp hs
  exact fun i => hh i (Finset.mem_univ _)

lemma row_positive_across (m q : Multiplicity) (hq : ∀ e, q e ≤ m e) (heq : EvenVector q)
    (hm : ∀ v, row m v ≤ 2) {u v : Core} {e : E} (hu : ∃ i, incident u i = e)
    (hv : ∃ i, incident v i = e) (he : 0 < m e) (hp : 0 < row q u) : 0 < row q v := by
  obtain ⟨i,hi⟩ := hu
  obtain ⟨j,hj⟩ := hv
  have hs := row_saturate m q hq heq hm u hp i
  rw [hi] at hs
  have hh := coordinate_le_row q v j
  rw [hj] at hh
  omega

lemma cycle_even (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) :
    ∀ v, Even (H.spanningCoe.degree v) := by
  intro v
  rw [Subgraph.degree_spanningCoe]
  by_cases hv : v ∈ H.verts
  · have hh := hr ⟨v,hv⟩
    rw [Subgraph.coe_degree] at hh
    simp only [Subgraph.degree,← Nat.card_eq_fintype_card] at hh ⊢
    rw [hh]
    decide
  · rw [Subgraph.degree_of_notMem_verts hv]
    decide

lemma cycle_degree_le_two (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) (v : V) :
    H.spanningCoe.degree v ≤ 2 := by
  rw [Subgraph.degree_spanningCoe]
  by_cases hv : v ∈ H.verts
  · have hh := hr ⟨v,hv⟩
    rw [Subgraph.coe_degree] at hh
    simp only [Subgraph.degree,← Nat.card_eq_fintype_card] at hh ⊢
    exact hh.le
  · rw [Subgraph.degree_of_notMem_verts hv]
    omega

lemma cycle_ne_bot (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    H.spanningCoe ≠ ⊥ := by
  obtain ⟨e,he⟩ := cycle_edgeSet_nonempty H hc (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hr v)
  intro hh
  have hm : e ∈ H.spanningCoe.edgeSet := he
  simp [hh] at hm

/-- A genuine simple cycle projects to a MINIMAL even multiplicity vector.
The degree-two subdivision vertices prevent partial path occurrences; at
old vertices degree two gives saturation, which connectedness propagates. -/
lemma trace_cycle_minimal (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    MinimalEven (trace H.spanningCoe) := by
  let m := trace H.spanningCoe
  have hhe := cycle_even H hr
  have hAG := H.spanningCoe_le
  have hbound (v : Core) : row m v ≤ 2 := by
    have hh := cycle_degree_le_two H hr (old v)
    rw [degree_old H.spanningCoe hAG hhe v] at hh
    simpa only [row,Fin.sum_univ_three,m] using hh
  refine ⟨trace_nonzero _ hAG hhe (cycle_ne_bot H hc hr),trace_even _ hAG hhe,?_⟩
  intro q hq hqn hqe
  obtain ⟨e,he⟩ := hqn
  have hqe_pos : 0 < q e := by omega
  have hme_pos : 0 < m e := lt_of_lt_of_le hqe_pos (hq e)
  have hu : old (ends e).1 ∈ H.verts := by
    obtain ⟨w,hw⟩ := trace_pos_old_support H.spanningCoe e hme_pos
    exact H.edge_vert hw
  have hup : 0 < row q (proj (old (ends e).1)) := by
    rw [proj_old]
    obtain ⟨i,hi⟩ := incident_left e
    have hh := coordinate_le_row q (ends e).1 i
    rw [hi] at hh
    omega
  have hwalk : ∀ {x y : H.verts} (p : H.coe.Walk x y),
      0 < row q (proj x.val) → 0 < row q (proj y.val) := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih =>
      intro hp
      apply ih
      rcases adj_projection H.spanningCoe hAG hhe hxy with heq | ⟨f,hf,hx,hy⟩
      · simpa only [← heq] using hp
      · exact row_positive_across m q hq hqe hbound hx hy hf hp
  funext f
  change q f = m f
  by_cases hf : m f = 0
  · exact le_antisymm (hq f) (by rw [hf]; exact Nat.zero_le _)
  · have hmf : 0 < m f := by omega
    have hv : old (ends f).1 ∈ H.verts := by
      obtain ⟨w,hw⟩ := trace_pos_old_support H.spanningCoe f hmf
      exact H.edge_vert hw
    obtain ⟨p⟩ := hc ⟨old (ends e).1,hu⟩ ⟨old (ends f).1,hv⟩
    have hvp := hwalk p hup
    rw [proj_old] at hvp
    obtain ⟨i,hi⟩ := incident_left f
    have hh := row_saturate m q hq hqe hbound (ends f).1 hvp i
    rwa [hi] at hh

lemma trace_cycle_is_type (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    ∃ i : Fin 72, trace H.spanningCoe = DoubledPetersenCertificate.digit i :=
  DoubledPetersenCertificate.minimalEven_is_type _ (trace_cycle_minimal H hc hr)

/-- Edge-disjoint coverage counts each actual occurrence exactly once. -/
lemma decomposition_ind (D : Finset G.Subgraph) (hd : IsDecomposition G D)
    (e : E) (j : Fin 3) : (∑ H ∈ D, ind H.spanningCoe e j) = 1 := by
  have he := edge_mem e j
  rw [← hd.2] at he
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
  rw [Finset.sum_eq_single H]
  · simp only [ind,if_pos (show edge e j ∈ H.spanningCoe.edgeSet from heH)]
  · intro K hK hne
    apply if_neg
    intro heK
    exact Set.disjoint_left.mp (hd.1 hK hH hne) heK heH
  · simp [hH]

lemma decomposition_trace (D : Finset G.Subgraph) (hd : IsDecomposition G D)
    (e : E) : (∑ H ∈ D, trace H.spanningCoe e) = 2 := by
  simp only [trace,Finset.sum_add_distrib,decomposition_ind D hd]

lemma decomposition_projects (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    DoubledPetersenCertificate.IsCircuitPartition
      (D.toList.map (fun H => trace H.spanningCoe)) := by
  constructor
  · intro m hm
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hm
    exact trace_cycle_minimal H (hc H (Finset.mem_toList.mp hH)).1
      (hc H (Finset.mem_toList.mp hH)).2
  · intro e
    rw [List.map_map]
    rw [← List.sum_toFinset _ (Finset.nodup_toList D),Finset.toList_toFinset]
    exact decomposition_trace D hd e

/-- The finite circuit certificate bounds EVERY actual simple-cycle partition,
not only the five displayed pieces or the externally enumerated cycles. -/
lemma cycle_decomposition_card_lower (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : 5 ≤ D.card := by
  have hh := DoubledPetersenCertificate.circuitPartition_length_lower _
    (decomposition_projects D hc hd)
  simpa only [List.length_map,Finset.length_toList] using hh

end Erdos184.DoubledPetersenSimple
