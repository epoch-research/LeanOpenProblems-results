import Submission.HeterogeneousSelectionExplore
import Submission.LocalWindowExplore

/-! Several symmetric repair packets. Non-designated sums are required to be
Sidon across the whole collection, not separately in each packet. -/
namespace Erdos66MultiPacket
open Erdos66OriginRepair Erdos66LocalWindow
open scoped Classical
set_option maxHeartbeats 1200000

variable {ι : Type*} [DecidableEq ι]

/-- The two points of coordinate i are x_i and n_i-x_i. -/
def point (n x : ι → ℤ) (u : ι × Bool) : ℤ :=
  if u.2 then n u.1 - x u.1 else x u.1

def Designated (u v : ι × Bool) : Prop := u.1 = v.1 ∧ u.2 ≠ v.2

lemma point_designated (n x : ι → ℤ) {u v : ι × Bool} (h : Designated u v) :
    point n x u + point n x v = n u.1 := by
  obtain ⟨i, b⟩ := u
  obtain ⟨j, d⟩ := v
  obtain ⟨rfl, hbd⟩ := h
  cases b <;> cases d <;> simp_all [point]

/-- A point collision always has at most one bad value in either coordinate
that occurs in it. -/
lemma point_collision_fiber (n : ι → ℤ) (u v : ι × Bool) (huv : u ≠ v)
    (i : ι) (hi : i = u.1 ∨ i = v.1) :
    ∀ f : ι → ℤ, ∀ a b : ℤ,
      point n (Function.update f i a) u = point n (Function.update f i a) v →
      point n (Function.update f i b) u = point n (Function.update f i b) v → a = b := by
  obtain ⟨j, s⟩ := u
  obtain ⟨k, t⟩ := v
  dsimp only [Prod.fst, Prod.snd] at hi
  rcases hi with hi | hi
  all_goals
    subst i
    intro f a b ha hb
    by_cases hjk : j = k
    · subst k
      cases s <;> cases t
      all_goals first | exact (huv rfl).elim |
        (simp only [point, Bool.false_eq_true, if_false, if_true, Function.update_self] at ha hb; omega)
    · cases s <;> cases t <;>
        simp only [point, Bool.false_eq_true, if_false, if_true, Function.update_self,
          Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk)] at ha hb <;> omega

/-- For disjoint, non-designated pairs, every coordinate appearing in the
comparison has a nonzero coefficient. In particular, the largest-scale
coordinate can pay for this collision event. -/
lemma pair_collision_fiber (n : ι → ℤ) (u v w t : ι × Bool)
    (h₁ : ¬ Designated u v) (h₂ : ¬ Designated w t)
    (huw : u ≠ w) (hut : u ≠ t) (hvw : v ≠ w) (hvt : v ≠ t)
    (i : ι) (hi : i = u.1 ∨ i = v.1 ∨ i = w.1 ∨ i = t.1) :
    ∀ f : ι → ℤ, ∀ a b : ℤ,
      point n (Function.update f i a) u + point n (Function.update f i a) v =
        point n (Function.update f i a) w + point n (Function.update f i a) t →
      point n (Function.update f i b) u + point n (Function.update f i b) v =
        point n (Function.update f i b) w + point n (Function.update f i b) t → a = b := by
  obtain ⟨j, r⟩ := u
  obtain ⟨k, s⟩ := v
  obtain ⟨l, d⟩ := w
  obtain ⟨m, e⟩ := t
  dsimp only [Prod.fst, Prod.snd] at *
  intro f a b ha hb
  cases r <;> cases s <;> cases d <;> cases e <;>
    by_cases hj : j = i <;> by_cases hk : k = i <;>
    by_cases hl : l = i <;> by_cases hm : m = i <;>
    subst_vars <;> simp_all [point, Designated, Function.update_of_ne] <;> first | omega | tauto

variable [Fintype ι]

noncomputable def packet (n x : ι → ℤ) : Finset ℤ := Finset.univ.image (point n x)

/-- Once points are distinct, disjoint-pair collision avoidance implies the
usual uniqueness of all non-designated unordered pairs. -/
lemma non_designated_unique (n x : ι → ℤ) (hinj : Function.Injective (point n x))
    (havoid : ∀ u v w t : ι × Bool, ¬ Designated u v → ¬ Designated w t →
      u ≠ w → u ≠ t → v ≠ w → v ≠ t →
      point n x u + point n x v ≠ point n x w + point n x t)
    (u v w t : ι × Bool) (h₁ : ¬ Designated u v) (h₂ : ¬ Designated w t)
    (he : point n x u + point n x v = point n x w + point n x t) :
    (u = w ∧ v = t) ∨ (u = t ∧ v = w) := by
  by_cases huw : u = w
  · subst w
    exact Or.inl ⟨rfl, hinj (add_left_cancel he)⟩
  by_cases hut : u = t
  · subst t
    exact Or.inr ⟨rfl, hinj (by linarith)⟩
  by_cases hvw : v = w
  · subst w
    exact Or.inr ⟨hinj (by linarith), rfl⟩
  by_cases hvt : v = t
  · subst t
    exact Or.inl ⟨hinj (by linarith), rfl⟩
  exact (havoid u v w t h₁ h₂ huw hut hvw hvt he).elim

noncomputable def pairLabels (n x : ι → ℤ) (z : ℤ) : Finset ((ι × Bool) × (ι × Bool)) :=
  Finset.univ.filter (fun p ↦ point n x p.1 + point n x p.2 = z)

lemma pairLabels_card (n x : ι → ℤ) (hinj : Function.Injective (point n x)) (z : ℤ) :
    (pairLabels n x z).card = pairCount (packet n x) (packet n x) z := by
  rw [pairCount_eq_product_filter_card]
  apply Finset.card_bij (fun p _ ↦ (point n x p.1, point n x p.2))
  · intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
      (Finset.mem_filter.mp hp).2⟩
    · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩
  · intro p hp q hq he
    exact Prod.ext (hinj (congrArg Prod.fst he)) (hinj (congrArg Prod.snd he))
  · intro p hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp ha
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hb
    refine ⟨(u,v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext hu hv⟩
    simpa only [hu, hv] using hs

lemma designated_card (n x : ι → ℤ) (z : ℤ) :
    ((pairLabels n x z).filter (fun p ↦ Designated p.1 p.2)).card =
      2 * (Finset.univ.filter (fun i ↦ n i = z)).card := by
  let D := (Finset.univ.filter (fun i ↦ n i = z)).product (Finset.univ : Finset Bool)
  have he : D.card = ((pairLabels n x z).filter (fun p ↦ Designated p.1 p.2)).card := by
    apply Finset.card_bij (fun p _ ↦ ((p.1,p.2),(p.1,!p.2)))
    · intro p hp
      obtain ⟨hp, _⟩ := Finset.mem_product.mp hp
      have hn := (Finset.mem_filter.mp hp).2
      have hd : Designated (p.1,p.2) (p.1,!p.2) := by
        cases h : p.2 <;> simp [Designated, h]
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (point_designated n x hd).trans hn⟩, hd⟩
    · intro p hp q hq he
      exact congrArg Prod.fst he
    · intro p hp
      obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
      have hs := (Finset.mem_filter.mp hp).2
      have hn : n p.1.1 = z := (point_designated n x hd).symm.trans hs
      refine ⟨p.1, Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, Finset.mem_univ _⟩, ?_⟩
      obtain ⟨⟨i,b⟩,⟨j,d⟩⟩ := p
      change i = j ∧ b ≠ d at hd
      obtain ⟨rfl, hbd⟩ := hd
      cases b <;> cases d <;> simp_all
  rw [← he]
  simp [D, Finset.product_eq_sprod, Finset.card_product, Nat.mul_comm]

/-- All the target spikes are accounted for by the prescribed centers;
there are at most two other ordered representations at any integer. -/
theorem packet_bound (n x : ι → ℤ) (hinj : Function.Injective (point n x))
    (hunique : ∀ u v w t : ι × Bool, ¬ Designated u v → ¬ Designated w t →
      point n x u + point n x v = point n x w + point n x t →
      (u = w ∧ v = t) ∨ (u = t ∧ v = w)) (z : ℤ) :
    2 * (Finset.univ.filter (fun i ↦ n i = z)).card ≤ pairCount (packet n x) (packet n x) z ∧
    pairCount (packet n x) (packet n x) z ≤
      2 * (Finset.univ.filter (fun i ↦ n i = z)).card + 2 := by
  let P := pairLabels n x z
  let Q := P.filter (fun p ↦ ¬ Designated p.1 p.2)
  have hQ : Q.card ≤ 2 := by
    by_cases hne : Q.Nonempty
    · obtain ⟨p, hp⟩ := hne
      have hp' := Finset.mem_filter.mp hp
      have hps := (Finset.mem_filter.mp hp'.1).2
      have hsub : Q ⊆ {p, (p.2,p.1)} := by
        intro q hq
        obtain ⟨hq, hqn⟩ := Finset.mem_filter.mp hq
        have hqs := (Finset.mem_filter.mp hq).2
        have hh := hunique q.1 q.2 p.1 p.2 hqn hp'.2 (hqs.trans hps.symm)
        rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h₁ h₂))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h₁ h₂)))
      exact (Finset.card_le_card hsub).trans (by
        calc
          _ ≤ ({(p.2,p.1)} : Finset ((ι × Bool) × (ι × Bool))).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have he := Finset.filter_card_add_filter_neg_card_eq_card (s := P)
    (p := fun p ↦ Designated p.1 p.2)
  have hd := designated_card n x z
  have hp := pairLabels_card n x hinj z
  change _ + Q.card = P.card at he
  change (P.filter _).card = _ at hd
  change P.card = _ at hp
  omega

end Erdos66MultiPacket
