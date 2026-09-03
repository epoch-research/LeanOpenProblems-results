import FormalConjecturesUtil

/-!
A limitation of a proposed acyclic two-terminal flow construction.
This file does not prove or disprove Erdos 184, or the general star-elimination
criterion. It only bounds the number of exhausted vertices for forward
orientations balanced away from two terminals, on a complete graph.
-/

open scoped Classical
namespace Erdos184.AcyclicStarObstruction

/-- All edges incident to this vertex of the complete graph are used. -/
def Exhausted {n : ℕ} (A : Fin n → Fin n → Prop) (v : Fin n) : Prop :=
  ∀ w, w ≠ v → A v w ∨ A w v

/-- Conservation at a nonterminal of a unit-edge directed flow. -/
def Balanced {n : ℕ} (A : Fin n → Fin n → Prop) (v : Fin n) : Prop :=
  (Finset.univ.filter (fun w => A w v)).card =
    (Finset.univ.filter (fun w => A v w)).card

lemma incoming_eq_Iio {n : ℕ} {A : Fin n → Fin n → Prop}
    (hf : ∀ a b, A a b → a < b) {v : Fin n} (hv : Exhausted A v) :
    Finset.univ.filter (fun w => A w v) = Finset.Iio v := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  constructor
  · exact hf w v
  · intro hw
    rcases hv w (ne_of_lt hw) with h | h
    · exact (lt_asymm hw (hf v w h)).elim
    · exact h

lemma outgoing_eq_Ioi {n : ℕ} {A : Fin n → Fin n → Prop}
    (hf : ∀ a b, A a b → a < b) {v : Fin n} (hv : Exhausted A v) :
    Finset.univ.filter (fun w => A v w) = Finset.Ioi v := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
  constructor
  · exact hf v w
  · intro hw
    rcases hv w (ne_of_gt hw) with h | h
    · exact h
    · exact (lt_asymm hw (hf w v h)).elim

/-- There is only one possible balanced exhausted vertex in a forward
orientation on `2*r+1` vertices. -/
lemma exhausted_balanced_eq_middle {r : ℕ} {A : Fin (2*r+1) → Fin (2*r+1) → Prop}
    (hf : ∀ a b, A a b → a < b) {v : Fin (2*r+1)}
    (hv : Exhausted A v) (hb : Balanced A v) : v.val = r := by
  unfold Balanced at hb
  rw [incoming_eq_Iio hf hv, outgoing_eq_Ioi hf hv, Fin.card_Iio, Fin.card_Ioi] at hb
  have hvlt := v.isLt
  omega

/-- Two exceptional terminals plus at most one balanced exhausted vertex. -/
lemma exhausted_card_le_three {r : ℕ} {A : Fin (2*r+1) → Fin (2*r+1) → Prop}
    (hf : ∀ a b, A a b → a < b) (s t : Fin (2*r+1))
    (hb : ∀ v, v ≠ s → v ≠ t → Balanced A v) :
    (Finset.univ.filter (Exhausted A)).card ≤ 3 := by
  let middle : Fin (2*r+1) := ⟨r, by omega⟩
  have hs : Finset.univ.filter (Exhausted A) ⊆ {s,t,middle} := by
    intro v hv
    have he := (Finset.mem_filter.mp hv).2
    by_cases hvs : v = s
    · simp [hvs]
    by_cases hvt : v = t
    · simp [hvt]
    have hvm : v = middle := Fin.ext (exhausted_balanced_eq_middle hf he (hb v hvs hvt))
    simp [hvm]
  have hc : ({s,t,middle} : Finset (Fin (2*r+1))).card ≤ 3 := by
    calc
      _ ≤ ({t,middle} : Finset (Fin (2*r+1))).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({middle} : Finset (Fin (2*r+1))).card + 1) + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  exact (Finset.card_le_card hs).trans hc

/-- This restricted construction cannot pay for `r` cycles by any one
constant times its number of exhausted vertices. This is NOT a negation
of the unrestricted star-elimination hypothesis. -/
theorem no_uniform_charge :
    ∀ C : ℕ, ∃ r : ℕ, 0 < r ∧
      ∀ (A : Fin (2*r+1) → Fin (2*r+1) → Prop) (s t : Fin (2*r+1)),
        (∀ a b, A a b → a < b) →
        (∀ v, v ≠ s → v ≠ t → Balanced A v) →
        C * (Finset.univ.filter (Exhausted A)).card < r := by
  intro C
  refine ⟨3*C+1, by omega, ?_⟩
  intro A s t hf hb
  have h := Nat.mul_le_mul_left C (exhausted_card_le_three hf s t hb)
  omega

/-- For the forward orientation of a subgraph of a complete graph,
exhaustion is exactly isolation after its deletion. -/
lemma exhausted_iff_isolated {n : ℕ} (F : SimpleGraph (Fin n)) (v : Fin n) :
    Exhausted (fun a b => F.Adj a b ∧ a < b) v ↔
      v ∉ ((⊤ : SimpleGraph (Fin n)) \ F).support := by
  simp only [SimpleGraph.mem_support, SimpleGraph.sdiff_adj, SimpleGraph.top_adj,
    not_exists, not_and, not_not]
  constructor
  · intro h w hw
    rcases h w hw.symm with h | h
    · exact h.1
    · exact h.1.symm
  · intro h w hw
    have ha : F.Adj v w := h w hw.symm
    rcases lt_or_gt_of_ne hw.symm with hlt | hgt
    · exact Or.inl ⟨ha, hlt⟩
    · exact Or.inr ⟨ha.symm, hgt⟩

lemma isolated_card_le_three {r : ℕ} (F : SimpleGraph (Fin (2*r+1)))
    (s t : Fin (2*r+1))
    (hb : ∀ v, v ≠ s → v ≠ t → Balanced (fun a b => F.Adj a b ∧ a < b) v) :
    (Finset.univ.filter (fun v => v ∉ ((⊤ : SimpleGraph (Fin (2*r+1))) \ F).support)).card
      ≤ 3 := by
  have heq : Exhausted (fun a b => F.Adj a b ∧ a < b) =
      (fun v => v ∉ ((⊤ : SimpleGraph (Fin (2*r+1))) \ F).support) := by
    funext v
    exact propext (exhausted_iff_isolated F v)
  simpa only [heq] using
    (exhausted_card_le_three (A := fun a b => F.Adj a b ∧ a < b)
      (fun _ _ h => h.2) s t hb)

/-- Graph formulation of the same restricted obstruction. It does not
assume, or negate, the existence of an unrestricted cycle packing. -/
theorem no_uniform_acyclic_flow_charge :
    ∀ C : ℕ, ∃ r : ℕ, 0 < r ∧
      ∀ (F : SimpleGraph (Fin (2*r+1))) (s t : Fin (2*r+1)),
        (∀ v, v ≠ s → v ≠ t → Balanced (fun a b => F.Adj a b ∧ a < b) v) →
        C * (Finset.univ.filter
          (fun v => v ∉ ((⊤ : SimpleGraph (Fin (2*r+1))) \ F).support)).card < r := by
  intro C
  refine ⟨3*C+1, by omega, ?_⟩
  intro F s t hb
  have h := Nat.mul_le_mul_left C (isolated_card_le_three F s t hb)
  omega

end Erdos184.AcyclicStarObstruction
