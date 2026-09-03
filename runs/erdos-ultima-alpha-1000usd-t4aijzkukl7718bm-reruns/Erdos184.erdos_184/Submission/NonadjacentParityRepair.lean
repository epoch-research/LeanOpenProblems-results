import Submission.FeedbackKernels
import Submission.ParityCompletion

/-!
Parity repair after deletion of a nonadjacent vertex, under explicit
connectivity of the graph away from the two vertices. This yields
one-slack critical descent in that restricted case only.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.NonadjacentParityRepair
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma degree_delete_of_nonadjacent (G : SimpleGraph V) (v w : V)
    (hvw : v ≠ w) (hn : ¬G.Adj v w) :
    (G.deleteIncidenceSet w).degree v = G.degree v := by
  have hN : (G.deleteIncidenceSet w).neighborSet v = G.neighborSet v := by
    ext x
    simp only [mem_neighborSet,deleteIncidenceSet_adj]
    exact ⟨And.left,fun hx => ⟨hx,hvw,fun hh => hn (hh ▸ hx)⟩⟩
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,hN]

lemma degree_delete_self (G : SimpleGraph V) (w : V) :
    (G.deleteIncidenceSet w).degree w = 0 := by
  apply ((G.deleteIncidenceSet w).degree_eq_zero_iff_notMem_support w).mpr
  rintro ⟨x,hx⟩
  exact (deleteIncidenceSet_adj.mp hx).2.1 rfl

/-- Preserve the degree at v while making w unsupported. The parity demand is
realized away from v and w by attaching auxiliary pendant edges, applying the
connected parity theorem, and observing that neither pendant edge is used. -/
lemma exists_even_avoiding_preserving (G : SimpleGraph V) (v w : V)
    (hvw : v ≠ w) (hn : ¬G.Adj v w) (hev : Even (G.degree v))
    (hconn : ∀ x y : V, x ≠ v → x ≠ w → y ≠ v → y ≠ w →
      ((G.deleteIncidenceSet v).deleteIncidenceSet w).Reachable x y) :
    ∃ A : SimpleGraph V, A ≤ G ∧ (∀ x, Even (A.degree x)) ∧
      A.degree v = G.degree v ∧ w ∉ A.support := by
  by_cases hz : G.degree v = 0
  · refine ⟨⊥,bot_le,?_,?_,?_⟩
    · intro x; simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]; simp
    · simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hz ⊢
      simpa using hz.symm
    · simp
  obtain ⟨a,hva⟩ := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hz)
  have hav : a ≠ v := hva.ne.symm
  have haw : a ≠ w := fun h => hn (h ▸ hva)
  let R := (G.deleteIncidenceSet v).deleteIncidenceSet w
  let B := G.deleteIncidenceSet w
  let T := (R ⊔ edge v a) ⊔ edge w a
  have hRT : R ≤ T := le_sup_left.trans le_sup_left
  have hTv : T.Adj v a := Or.inl (Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hva.ne⟩))
  have hTw : T.Adj w a := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,haw.symm⟩)
  have hTa (x : V) : T.Reachable x a := by
    by_cases hxv : x = v
    · subst x; exact hTv.reachable
    by_cases hxw : x = w
    · subst x; exact hTw.reachable
    exact (hconn x a hxv hxw hav haw).mono hRT
  haveI : Nonempty V := ⟨a⟩
  have hcT : T.Connected := ⟨fun x y => (hTa x).trans (hTa y).symm⟩
  have hTva (x : V) (hx : T.Adj v x) : x = a := by
    rcases hx with (hx | hx) | hx
    · exact False.elim ((deleteIncidenceSet_adj.mp (deleteIncidenceSet_adj.mp hx).1).2.1 rfl)
    · simp only [edge_adj] at hx
      rcases hx.1 with hh | hh
      · exact hh.2
      · exact False.elim (hav hh.1.symm)
    · simp only [edge_adj] at hx
      rcases hx.1 with hh | hh
      · exact False.elim (hvw hh.1)
      · exact False.elim (hav hh.1.symm)
  have hTwa (x : V) (hx : T.Adj w x) : x = a := by
    rcases hx with (hx | hx) | hx
    · exact False.elim ((deleteIncidenceSet_adj.mp hx).2.1 rfl)
    · simp only [edge_adj] at hx
      rcases hx.1 with hh | hh
      · exact False.elim (hvw hh.1.symm)
      · exact False.elim (haw hh.1.symm)
    · simp only [edge_adj] at hx
      rcases hx.1 with hh | hh
      · exact hh.2
      · exact False.elim (haw hh.1.symm)
  have hTv1 : T.degree v = 1 := degree_eq_one_iff_existsUnique_adj.mpr ⟨a,hTv,hTva⟩
  have hTw1 : T.degree w = 1 := degree_eq_one_iff_existsUnique_adj.mpr ⟨a,hTw,hTwa⟩
  have hBv : B.degree v = G.degree v := degree_delete_of_nonadjacent G v w hvw hn
  have hBw : B.degree w = 0 := degree_delete_self G w
  obtain ⟨X,hXT,hpar⟩ := ParityCompletion.exists_parity_subgraph T B hcT
  have hXvEven : Even (X.degree v) := ZMod.natCast_eq_zero_iff_even.mp (by
    have hp := hpar v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hp hBv hev ⊢
    rw [hp,hBv]; exact hev.natCast_zmod_two)
  have hXwEven : Even (X.degree w) := ZMod.natCast_eq_zero_iff_even.mp (by
    have hp := hpar w
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hp hBw ⊢
    rw [hp,hBw]; rfl)
  have hXv : X.degree v = 0 := by
    have hh := degree_le_of_le hXT (v := v)
    rw [hTv1] at hh
    rw [Nat.even_iff] at hXvEven
    omega
  have hXw : X.degree w = 0 := by
    have hh := degree_le_of_le hXT (v := w)
    rw [hTw1] at hh
    rw [Nat.even_iff] at hXwEven
    omega
  have hvX : v ∉ X.support := (X.degree_eq_zero_iff_notMem_support v).mp hXv
  have hwX : w ∉ X.support := (X.degree_eq_zero_iff_notMem_support w).mp hXw
  have hXR : X ≤ R := by
    intro x y hxy
    rcases hXT hxy with (hh | hh) | hh
    · exact hh
    · simp only [edge_adj] at hh
      rcases hh.1 with ⟨rfl,_⟩ | ⟨_,rfl⟩
      · exact False.elim (hvX ⟨y,hxy⟩)
      · exact False.elim (hvX ⟨x,hxy.symm⟩)
    · simp only [edge_adj] at hh
      rcases hh.1 with ⟨rfl,_⟩ | ⟨_,rfl⟩
      · exact False.elim (hwX ⟨y,hxy⟩)
      · exact False.elim (hwX ⟨x,hxy.symm⟩)
  have hRB : R ≤ B := by
    intro x y hxy
    have hh := deleteIncidenceSet_adj.mp hxy
    exact deleteIncidenceSet_adj.mpr ⟨(deleteIncidenceSet_adj.mp hh.1).1,hh.2⟩
  have hXB : X ≤ B := hXR.trans hRB
  let A := B \ X
  have hAe : ∀ x, Even (A.degree x) := by
    intro x
    have hd := degree_sdiff_of_le hXB x
    have hl := degree_le_of_le hXB (v := x)
    have hp := hpar x
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd hl hp ⊢
    change Even (Nat.card ((B \ X).neighborSet x))
    rw [hd]
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [Nat.cast_sub hl,hp,sub_self]
  have hAv : A.degree v = G.degree v := by
    have hh := degree_sdiff_of_le hXB v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hXv hBv ⊢
    change Nat.card ((B \ X).neighborSet v) = _
    omega
  have hwA : w ∉ A.support := by
    rintro ⟨x,hx⟩
    exact (deleteIncidenceSet_adj.mp hx.1).2.1 rfl
  refine ⟨A,sdiff_le.trans (G.deleteIncidenceSet_le w),?_,?_,hwA⟩
  · intro x
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hAe x
  · simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hAv

/-- The parity-repaired graph has a feedback kernel at the original half degree.
The graph G need not itself be critical. -/
lemma exists_avoiding_critical_kernel (G : SimpleGraph V) (v w : V) (r : ℕ)
    (hvw : v ≠ w) (hn : ¬G.Adj v w) (hd : G.degree v = 2*r)
    (hconn : ∀ x y : V, x ≠ v → x ≠ w → y ≠ v → y ≠ w →
      ((G.deleteIncidenceSet v).deleteIncidenceSet w).Reachable x y) :
    ∃ H : SimpleGraph V, H ≤ G ∧ CountCritical.IsCountCritical r H ∧
      H.degree v = G.degree v ∧ w ∉ H.support := by
  have hev : Even (G.degree v) := by rw [hd]; exact even_two_mul r
  obtain ⟨A,hAG,heA,hAv,hwA⟩ := exists_even_avoiding_preserving G v w hvw hn hev hconn
  obtain ⟨H,hHA,hHv,_,hcH⟩ := FeedbackKernels.exists_feedback_critical_kernel A heA v r
    (hAv.trans hd)
  exact ⟨H,hHA.trans hAG,hcH,hHv.trans hAv,fun hw => hwA (support_mono hHA hw)⟩

/-- A next-count kernel with strictly lower potential, in the one-slack case
under nonadjacency and connectivity away from v,w. This is not a universal
critical descent theorem. -/
lemma one_slack_descent {G : SimpleGraph V} {k : ℕ}
    (hG : CountCritical.IsCountCritical k G) (v w : V)
    (hvw : v ≠ w) (hn : ¬G.Adj v w) (hw : w ∈ G.support)
    (hd : G.degree v = 2*(k-1))
    (hconn : ∀ x y : V, x ≠ v → x ≠ w → y ≠ v → y ≠ w →
      ((G.deleteIncidenceSet v).deleteIncidenceSet w).Reachable x y) :
    ∃ H : SimpleGraph V, H ≤ G ∧ CountCritical.IsCountCritical (k-1) H ∧
      BlockRankPotential.potential H + 1 ≤ BlockRankPotential.potential G := by
  obtain ⟨H,hHG,hH,_,hwH⟩ := exists_avoiding_critical_kernel G v w (k-1) hvw hn hd hconn
  exact ⟨H,hHG,hH,BlockRankPotential.potential_drop_of_support_loss hHG hG.1 w hw hwH⟩

end Erdos184.NonadjacentParityRepair
