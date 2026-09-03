import Submission.CycleEnvelope

/-!
A conditional reduction using the actual vertex-deletion loss of the monotone
cycle envelope. A universal bound on that loss is NOT proved here.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleEnvelope
open CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]

/-- Isolating a supported vertex removes at least one supported vertex. -/
lemma support_delete_vertex_card (G : SimpleGraph V) (v : V) (hv : v ∈ G.support) :
    (G.deleteIncidenceSet v).support.ncard + 1 ≤ G.support.ncard := by
  have hsub := SimpleGraph.support_mono (G.deleteIncidenceSet_le v)
  have hn : v ∉ (G.deleteIncidenceSet v).support := by
    rintro ⟨w,hw⟩
    exact (deleteIncidenceSet_adj.mp hw).2.1 rfl
  have hne : (G.deleteIncidenceSet v).support ≠ G.support := by
    intro h
    exact hn (h.symm ▸ hv)
  have hlt := Set.ncard_lt_ncard (ht := Set.toFinite _)
    (Set.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
  omega

/-- A degree bound is one way, but not a necessary premise of the reduction,
to control envelope loss when isolating a vertex. -/
lemma vertex_loss_le_of_degree_le (G : SimpleGraph V) (v : V) (C : ℕ)
    (hv : G.degree v ≤ 2*C) :
    envelope G ≤ envelope (G.deleteIncidenceSet v) + C := by
  have hh := delete_vertex_degree_cost G v
  omega

/-- Only critical subgraphs need the bounded vertex-loss property. In the
induction the vertex-deleted graph can be odd and need not be critical. -/
lemma envelope_bound_of_critical_vertex_loss (G : SimpleGraph V) (C : ℕ)
    (hloss : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k → IsCountCritical k H →
      ∃ v ∈ H.support, envelope H ≤ envelope (H.deleteIncidenceSet v) + C) :
    envelope G ≤ C * G.support.ncard := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hz : envelope G = 0
    · omega
    obtain ⟨H,hHG,hH⟩ := critical_kernel G (Nat.pos_of_ne_zero hz)
    obtain ⟨v,hv,hstep⟩ := hloss H hHG _ (Nat.pos_of_ne_zero hz) hH
    have hsupport := support_delete_vertex_card H v hv
    have hSG := Set.ncard_le_ncard (SimpleGraph.support_mono hHG)
    have hlt : (H.deleteIncidenceSet v).support.ncard < n := by omega
    have hb := ih _ hlt (H.deleteIncidenceSet v) (by
      intro A hAR k hk hA
      exact hloss A (hAR.trans ((H.deleteIncidenceSet_le v).trans hHG)) k hk hA) rfl
    have hmul := Nat.mul_le_mul_left C
      (show (H.deleteIncidenceSet v).support.ncard + 1 ≤ n by omega)
    rw [Nat.mul_add,Nat.mul_one] at hmul
    rw [critical_envelope hH] at hstep
    omega

lemma envelope_bound_of_critical_low_degree (G : SimpleGraph V) (C : ℕ)
    (hlow : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k → IsCountCritical k H →
      ∃ v ∈ H.support, H.degree v ≤ 2*C) :
    envelope G ≤ C * G.support.ncard := by
  apply envelope_bound_of_critical_vertex_loss G C
  intro H hHG k hk hH
  obtain ⟨v,hv,hd⟩ := hlow H hHG k hk hH
  exact ⟨v,hv,vertex_loss_le_of_degree_le H v C hd⟩

/-- A minimum decomposition obeys the same bound under the local loss
hypothesis. No monotonicity of the minimum cycle count is used. -/
lemma decomposition_bound_of_critical_vertex_loss (G : SimpleGraph V) (C : ℕ)
    (he : ∀ v, Even (G.degree v))
    (hloss : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k → IsCountCritical k H →
      ∃ v ∈ H.support, envelope H ≤ envelope (H.deleteIncidenceSet v) + C) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ C * G.support.ncard := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G he
  refine ⟨D,hc,hd,?_⟩
  rw [hcard]
  exact (number_le_envelope le_rfl he).trans (envelope_bound_of_critical_vertex_loss G C hloss)

universe u
/-- A uniform bound on a favorable critical vertex's actual envelope loss
would settle the original conjecture. That assertion remains an explicit
unproved premise. -/
lemma conjecture_of_critical_vertex_loss (C : ℕ)
    (hloss : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      0 < k → IsCountCritical k G →
      ∃ v ∈ G.support, envelope G ≤ envelope (G.deleteIncidenceSet v) + C) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨C,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hb⟩ := decomposition_bound_of_critical_vertex_loss G C he
    (fun H _ k hk hH => hloss H k hk hH)
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  refine ⟨D,hc,hd,?_⟩
  exact_mod_cast hb.trans (Nat.mul_le_mul_left C hs)

lemma conjecture_of_critical_low_degree (C : ℕ)
    (hlow : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      0 < k → IsCountCritical k G →
      ∃ v ∈ G.support, G.degree v ≤ 2*C) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_of_critical_vertex_loss C
  intro V _ G k hk hG
  obtain ⟨v,hv,hd⟩ := hlow G k hk hG
  exact ⟨v,hv,vertex_loss_le_of_degree_le G v C hd⟩

end Erdos184.CycleEnvelope
