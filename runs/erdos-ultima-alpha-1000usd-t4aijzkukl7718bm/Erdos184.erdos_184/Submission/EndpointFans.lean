import Submission.PartialInjectionFan

/-! Every unused neighbor begins a finite branch fan ending at the endpoint
of a path avoiding the center.  Distinct unused neighbors have disjoint fans.
These are structural facts; they do not assert absorption of an unused cycle. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def fanStep (L : List (Piece G)) (v a : V) : V :=
  if ha : a ∈ (touchingEndpoints L v).erase v then (branchMap L v ⟨a,ha⟩).val else a

lemma fanStep_branch (L : List (Piece G)) (v : V) {a : V}
    (ha : a ∈ (touchingEndpoints L v).erase v) : Branch L v a (fanStep L v a) := by
  rw [fanStep,dif_pos ha]
  exact branchMap_spec L v ⟨a,ha⟩

lemma fanStep_injective {L : List (Piece G)} (hn : (edgeList L).Nodup) (v : V) :
    Set.InjOn (fanStep L v) ((touchingEndpoints L v).erase v) := by
  intro a ha b hb he
  exact (fanStep_branch L v ha).endpoint_unique hn (he ▸ fanStep_branch L v hb)

lemma Admissible.fanDomain_card {L : List (Piece G)} (hL : Admissible L) (v : V) :
    ((touchingEndpoints L v).erase v).card = (coveredGraph L).degree v := by
  have hc := hL.touchingEndpoints_card v
  have he := Finset.card_erase_add_one (hL.mem_touchingEndpoints_self v)
  omega

lemma Admissible.fanStep_image {L : List (Piece G)} (hL : Admissible L) (v : V) :
    ((touchingEndpoints L v).erase v).image (fanStep L v) = (coveredGraph L).neighborFinset v := by
  ext w
  constructor
  · rintro hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
    exact ((coveredGraph L).mem_neighborFinset v _).mpr (fanStep_branch L v ha).covered
  · intro hw
    obtain ⟨a,he⟩ := (hL.branchMap_bijective v).2 ⟨w,hw⟩
    refine Finset.mem_image.mpr ⟨a.val,a.property,?_⟩
    rw [fanStep,dif_pos a.property]
    exact congrArg Subtype.val he

/-- An unused incident edge starts a branch fan.  The terminal endpoint's
packed path avoids the center; each step follows an actual branch of a path. -/
lemma Admissible.exists_endpoint_fan {L : List (Piece G)} (hL : Admissible L)
    {v x : V} (hx : (G \ coveredGraph L).Adj v x) :
    ∃ n : ℕ, n ≤ (coveredGraph L).degree v ∧
      (∀ i < n, (fanStep L v)^[i] x ∈ (touchingEndpoints L v).erase v) ∧
      (fanStep L v)^[n] x ∉ touchingEndpoints L v ∧
      (∀ i ≤ n, G.Adj v ((fanStep L v)^[i] x)) ∧
      (∀ i < n, Branch L v ((fanStep L v)^[i] x) ((fanStep L v)^[i+1] x)) ∧
      Function.Injective (fun i : Fin (n+1) => (fanStep L v)^[i.val] x) ∧
      (∃ p ∈ L, ((fanStep L v)^[n] x = p.src ∨ (fanStep L v)^[n] x = p.dst) ∧
        v ∉ p.walk.support) := by
  have hstart : x ∉ ((touchingEndpoints L v).erase v).image (fanStep L v) := by
    rw [hL.fanStep_image]
    exact fun h => hx.2 (((coveredGraph L).mem_neighborFinset v x).mp h)
  obtain ⟨n,hn,hbefore,hexit,hinj⟩ := PartialInjectionFan.exists_first_exit
    ((touchingEndpoints L v).erase v) (fanStep L v) (fanStep_injective hL.1 v) x hstart
  have hadj : ∀ i ≤ n, G.Adj v ((fanStep L v)^[i] x) := by
    intro i hi
    cases i with
    | zero => exact hx.1
    | succ i =>
      rw [Function.iterate_succ_apply']
      exact coveredGraph_le L ((fanStep_branch L v (hbefore i (by omega))).covered)
  have hnot : (fanStep L v)^[n] x ∉ touchingEndpoints L v := by
    intro hm
    apply hexit
    exact Finset.mem_erase.mpr ⟨(hadj n (by omega)).ne.symm,hm⟩
  refine ⟨n,?_,hbefore,hnot,hadj,?_,hinj,hL.endpoint_path_avoids_of_not_touching hnot⟩
  · rwa [hL.fanDomain_card] at hn
  · intro i hi
    rw [Function.iterate_succ_apply']
    exact fanStep_branch L v (hbefore i hi)

/-- Fans beginning at different unused neighbors cannot meet, even at their
terminal endpoints.  The two terminal endpoints can still belong to one path. -/
lemma Admissible.endpoint_fans_disjoint {L : List (Piece G)} (hL : Admissible L)
    {v x y : V} (hx : (G \ coveredGraph L).Adj v x) (hy : (G \ coveredGraph L).Adj v y)
    (hxy : x ≠ y) {n m : ℕ}
    (hxn : ∀ i < n, (fanStep L v)^[i] x ∈ (touchingEndpoints L v).erase v)
    (hym : ∀ j < m, (fanStep L v)^[j] y ∈ (touchingEndpoints L v).erase v)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    (fanStep L v)^[i] x ≠ (fanStep L v)^[j] y := by
  intro he
  apply hxy
  apply PartialInjectionFan.meeting_implies_same_start
    ((touchingEndpoints L v).erase v) (fanStep L v) (fanStep_injective hL.1 v) x y _ _
    i j (fun k hk => hxn k (by omega)) (fun k hk => hym k (by omega)) he
  · rw [hL.fanStep_image]
    exact fun h => hx.2 (((coveredGraph L).mem_neighborFinset v x).mp h)
  · rw [hL.fanStep_image]
    exact fun h => hy.2 (((coveredGraph L).mem_neighborFinset v y).mp h)

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Admissible.exists_endpoint_fan
#print axioms Erdos184Work.OddPaths.Admissible.endpoint_fans_disjoint
