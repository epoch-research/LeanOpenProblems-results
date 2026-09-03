import Submission.ConePaths
import Submission.Rigidity
import Submission.EnvelopeFactorBounds

/-! Apex deletion can have a large cycle-envelope loss even when the apex
starts a longest path. The estimates below do not assume count-criticality. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.ConeEnvelopeLoss
open FanPaths CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

abbrev fullCone (H : SimpleGraph V) : SimpleGraph (Option V) := cone H Set.univ

lemma degree_apex (H : SimpleGraph V) : (fullCone H).degree none = Fintype.card V := by
  have hn : (fullCone H).neighborSet none = Option.some '' (Set.univ : Set V) := by
    ext x
    cases x <;> simp [fullCone, cone, SimpleGraph.neighborSet]
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, hn, Set.ncard_image_of_injective _ (Option.some_injective V), Set.ncard_univ]

lemma degree_old (H : SimpleGraph V) (v : V) :
    (fullCone H).degree (some v) = H.degree v + 1 := by
  have hn : (fullCone H).neighborSet (some v) = insert none (Option.some '' H.neighborSet v) := by
    ext x
    cases x <;> simp [fullCone, cone, SimpleGraph.neighborSet]
  have hnot : (none : Option V) ∉ Option.some '' H.neighborSet v := by simp
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, hn, Set.ncard_insert_of_notMem hnot,
    Set.ncard_image_of_injective _ (Option.some_injective V)]

lemma deleted_degree_old (H : SimpleGraph V) (v : V) :
    ((fullCone H).deleteIncidenceSet none).degree (some v) = H.degree v := by
  have hn : ((fullCone H).deleteIncidenceSet none).neighborSet (some v) =
      Option.some '' H.neighborSet v := by
    ext x
    cases x <;> simp [SimpleGraph.neighborSet, deleteIncidenceSet_adj, fullCone, cone]
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, hn, Set.ncard_image_of_injective _ (Option.some_injective V)]

lemma cone_even_of_odd (H : SimpleGraph V) (hn : Even (Fintype.card V))
    (hd : ∀ v, Odd (H.degree v)) : ∀ x, Even ((fullCone H).degree x) := by
  intro x
  cases x with
  | none => simpa only [degree_apex] using hn
  | some v =>
    rw [degree_old]
    obtain ⟨r,hr⟩ := hd v
    exact ⟨r+1,by omega⟩

lemma apex_envelope_lower (H : SimpleGraph V) (he : ∀ x, Even ((fullCone H).degree x)) :
    Fintype.card V ≤ 2 * CycleEnvelope.envelope (fullCone H) := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists (fullCone H) he
  have hh := cycle_decomposition_degree_lower (fullCone H) D hc hd none
  rw [degree_apex,hcard] at hh
  exact hh.trans (Nat.mul_le_mul_left 2 (CycleEnvelope.number_le_envelope le_rfl he))

/-- Every even subgraph of the deleted cone is degree at most two. Its
three-edges-per-cycle bound is therefore a vertex bound. -/
lemma deleted_envelope_upper (H : SimpleGraph V) (hdeg : ∀ v, H.degree v ≤ 3) :
    3 * CycleEnvelope.envelope ((fullCone H).deleteIncidenceSet none) ≤ Fintype.card V := by
  obtain ⟨A,hAH,he,hval⟩ := CycleEnvelope.attained ((fullCone H).deleteIncidenceSet none)
  have hz : A.degree none = 0 := by
    have hh := degree_le_of_le (v := none) hAH
    have hh' : ((fullCone H).deleteIncidenceSet none).degree none = 0 := by
      simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      simp [deleteIncidenceSet_adj]
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hh' ⊢
    omega
  have ha (v : V) : A.degree (some v) ≤ 2 := by
    have hh := degree_le_of_le (v := some v) hAH
    have hh' := deleted_degree_old H v
    have hd := hdeg v
    obtain ⟨r,hr⟩ := he (some v)
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hh' hd hr ⊢
    omega
  have hsum : (∑ x, A.degree x) ≤ 2 * Fintype.card V := by
    rw [Fintype.sum_option, hz, zero_add]
    calc
      (∑ v, A.degree (some v)) ≤ ∑ _ : V, 2 := Finset.sum_le_sum (fun v _ => ha v)
      _ = 2 * Fintype.card V := by simp [mul_comm]
  have heq := A.sum_degrees_eq_twice_card_edges
  have hm : A.edgeFinset.card ≤ Fintype.card V := by omega
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists A he
  have hb := cycle_decomposition_three_mul_card_le_edges A D hc hd
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hm hb
  rw [hcard,hval] at hb
  have hv : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  omega

/-- The loss at the apex is at least one sixth of the base order. This can
be large, despite the base graph having degree at most three. -/
lemma cone_loss_lower (H : SimpleGraph V) (hn : Even (Fintype.card V))
    (hodd : ∀ v, Odd (H.degree v)) (hdeg : ∀ v, H.degree v ≤ 3) :
    Fintype.card V ≤ 6 * (CycleEnvelope.envelope (fullCone H) -
      CycleEnvelope.envelope ((fullCone H).deleteIncidenceSet none)) := by
  have hh := apex_envelope_lower H (cone_even_of_odd H hn hodd)
  have hl := deleted_envelope_upper H hdeg
  omega

/-- A Hamilton path in the base extends to a longest path starting at the
apex. No property of a minimum cycle partition is inferred from this. -/
lemma apex_longest_path (H : SimpleGraph V) {a b : V} (p : H.Walk a b)
    (hp : p.IsPath) (hlen : p.length + 1 = Fintype.card V) :
    ∃ q : (fullCone H).Walk none (some b), q.IsPath ∧
      ∀ x y (r : (fullCone H).Walk x y), r.IsPath → r.length ≤ q.length := by
  let q := (p.map (someEmbedding H Set.univ).toHom).cons
    (show (fullCone H).Adj none (some a) from Set.mem_univ a)
  have hp' : (p.map (someEmbedding H Set.univ).toHom).IsPath :=
    Walk.map_isPath_of_injective (someEmbedding H Set.univ).injective hp
  have hq : q.IsPath := by
    apply hp'.cons
    simp only [Walk.support_map, List.mem_map]
    rintro ⟨x,_,hx⟩
    change some x = (none : Option V) at hx
    cases hx
  refine ⟨q,hq,?_⟩
  intro x y r hr
  have hh := hr.length_lt
  simp only [Fintype.card_option] at hh
  have heq : q.length = p.length + 1 := by simp [q]
  omega

end Erdos184.ConeEnvelopeLoss
