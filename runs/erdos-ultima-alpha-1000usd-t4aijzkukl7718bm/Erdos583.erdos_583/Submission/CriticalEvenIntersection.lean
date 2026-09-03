import Submission.CriticalFiveEvenClique

/-! Intersections of critical even-even nonedges at a sharp odd-order budget.
These are necessary conditions, not a proof of the full path bound. -/
namespace Erdos583CriticalEvenIntersectionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583CriticalFiveEvenCliqueDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma disjoint_critical_even_edges_seven_even
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1)
    {r x a b : V} (hrx : r ≠ x) (hab : a ≠ b)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x)))
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hcrx : EdgeCritical H p r x) (hcab : EdgeCritical H p a b) :
    7 ≤ evenCount H :=
  critical_even_edge_nonadjacent_remaining_seven_even T hp hn hrx hr hx hcrx
    har hax hbr hbx hab ha hb (critical_edge_missing T hp hcab)

lemma critical_five_even_edges_intersect
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b : V} (hrx : r ≠ x) (hab : a ≠ b)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x)))
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hcrx : EdgeCritical H p r x) (hcab : EdgeCritical H p a b) :
    a=r ∨ a=x ∨ b=r ∨ b=x := by
  by_contra h
  push_neg at h
  have hh := disjoint_critical_even_edges_seven_even T hp hn hrx hab
    h.1 h.2.1 h.2.2.1 h.2.2.2 hr hx ha hb hcrx hcab
  omega

omit [Fintype V] in
/-- A simple graph whose edges pairwise intersect is a star or has all its
edges supported on a single triangle. -/
lemma pairwise_intersecting_edges_star_or_triangle (K : SimpleGraph V)
    (hinter : ∀ {r x a b}, K.Adj r x → K.Adj a b → a=r ∨ a=x ∨ b=r ∨ b=x) :
    (∃ r : V, ∀ ⦃a b⦄, K.Adj a b → a=r ∨ b=r) ∨
      (∀ ⦃a b⦄, ¬K.Adj a b) ∨
      ∃ r x y : V, K.Adj r x ∧ K.Adj r y ∧ K.Adj x y ∧
        ∀ ⦃a b⦄, K.Adj a b →
          (a=r ∨ a=x ∨ a=y) ∧ (b=r ∨ b=x ∨ b=y) := by
  classical
  by_cases he : ∃ r x, K.Adj r x
  · obtain ⟨r,x,hrx⟩ := he
    by_cases hr : ∀ ⦃a b⦄, K.Adj a b → a=r ∨ b=r
    · exact Or.inl ⟨r,hr⟩
    push_neg at hr
    obtain ⟨a,b,hab,har,hbr⟩ := hr
    have habx : a=x ∨ b=x := by
      have hh := hinter hrx hab
      tauto
    obtain ⟨y,hxy,hyr⟩ : ∃ y, K.Adj x y ∧ y ≠ r := by
      rcases habx with hax|hbx
      · exact ⟨b,hax ▸ hab,hbr⟩
      · exact ⟨a,hbx ▸ hab.symm,har⟩
    by_cases hx : ∀ ⦃a b⦄, K.Adj a b → a=x ∨ b=x
    · exact Or.inl ⟨x,hx⟩
    push_neg at hx
    obtain ⟨a,b,hab,hax,hbx⟩ := hx
    have habr : a=r ∨ b=r := by
      have hh := hinter hrx hab
      tauto
    have haby : a=y ∨ b=y := by
      have hh := hinter hxy hab
      tauto
    have hry : K.Adj r y := by
      rcases habr with har|hbr <;> rcases haby with hay|hby
      · exact (hyr (hay.symm.trans har)).elim
      · simpa only [har,hby] using hab
      · simpa only [hbr,hay] using hab.symm
      · exact (hyr (hby.symm.trans hbr)).elim
    refine Or.inr (Or.inr ⟨r,x,y,hrx,hry,hxy,?_⟩)
    intro a b hab
    have h1 := hinter hrx hab
    have h2 := hinter hry hab
    have h3 := hinter hxy hab
    constructor
    · by_contra ha
      have hb : b=r ∨ b=x := by tauto
      rcases hb with rfl|rfl <;>
        simp_all [hrx.ne,hrx.ne.symm,hry.ne,hry.ne.symm,hxy.ne]
    · by_contra hb
      have ha : a=r ∨ a=x := by tauto
      rcases ha with rfl|rfl <;>
        simp_all [hrx.ne,hrx.ne.symm,hry.ne,hry.ne.symm,hxy.ne]
  · exact Or.inr (Or.inl (by intro a b hab; exact he ⟨a,b,hab⟩))

/-- Critical even-even pairs, regarded as edges of an auxiliary graph. -/
def criticalEvenGraph (H : SimpleGraph V) (p : ℕ) : SimpleGraph V where
  Adj r x := r ≠ x ∧ Even (Nat.card (H.neighborSet r)) ∧
    Even (Nat.card (H.neighborSet x)) ∧ EdgeCritical H p r x
  symm := by
    rintro r x ⟨hne,hr,hx,hc⟩
    exact ⟨hne.symm,hx,hr,hc.symm⟩
  loopless := by intro r h; exact h.1 rfl

lemma critical_five_even_star_or_triangle
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5) :
    (∃ r : V, ∀ ⦃a b⦄, (criticalEvenGraph H p).Adj a b → a=r ∨ b=r) ∨
      (∀ ⦃a b⦄, ¬(criticalEvenGraph H p).Adj a b) ∨
      ∃ r x y : V, (criticalEvenGraph H p).Adj r x ∧
        (criticalEvenGraph H p).Adj r y ∧ (criticalEvenGraph H p).Adj x y ∧
        ∀ ⦃a b⦄, (criticalEvenGraph H p).Adj a b →
          (a=r ∨ a=x ∨ a=y) ∧ (b=r ∨ b=x ∨ b=y) := by
  apply pairwise_intersecting_edges_star_or_triangle
  intro r x a b hrx hab
  exact critical_five_even_edges_intersect T hp hn he hrx.1 hab.1
    hrx.2.1 hrx.2.2.1 hab.2.1 hab.2.2.1 hrx.2.2.2 hab.2.2.2

end Erdos583CriticalEvenIntersectionDevelopment
