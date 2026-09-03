import FormalConjecturesUtil
import Submission.UpToCycles

/-! A five-coordinate incidence construction excluding eight-cycles. -/

open Filter SimpleGraph Asymptotics Finset

namespace Erdos713C8
open Finset

lemma four_step_moment_obstruction {F : Type*} [Field F] (a b x r : Fin 4 → F)
    (ha01 : a 0 ≠ a 1) (ha12 : a 1 ≠ a 2) (ha23 : a 2 ≠ a 3)
    (hr1 : r 1 ≠ 0) (hr2 : r 2 ≠ 0) (hrx : r 1 = x 2 - x 1)
    (hb0 : b 1 - b 0 = (a 1 - a 0) * x 1)
    (hb1 : b 2 - b 1 = (a 2 - a 1) * x 2)
    (hR0 : ∑ i, r i = 0) (hR1 : ∑ i, a i * r i = 0)
    (hR2 : ∑ i, a i ^ 2 * r i = 0) (hS0 : ∑ i, b i * r i = 0)
    (hS1 : ∑ i, a i * b i * r i = 0) : False := by
  simp only [Fin.sum_univ_four] at hR0 hR1 hR2 hS0 hS1
  let D := a 1 - a 0
  let E := b 1 - b 0
  have hProd : r 2 * (a 2 - a 3) *
      (D * (b 2 - b 0) - E * (a 2 - a 0)) = 0 := by
    dsimp [D, E]
    linear_combination
      (a 1 - a 0) * hS1 + (-(a 1 - a 0) * b 0 + (b 1 - b 0) * a 0) * hR1 -
      (b 1 - b 0) * hR2 - a 3 * (a 1 - a 0) * hS0 -
      a 3 * (-(a 1 - a 0) * b 0 + (b 1 - b 0) * a 0) * hR0 +
      a 3 * (b 1 - b 0) * hR1
  have hB2 : D * (b 2 - b 0) - E * (a 2 - a 0) = 0 :=
    (mul_eq_zero.mp hProd).resolve_left (mul_ne_zero hr2 (sub_ne_zero.mpr ha23))
  have hCross : (a 1 - a 0) * (a 2 - a 1) * r 1 = 0 := by
    rw [hrx]
    dsimp [D, E] at hB2
    linear_combination hB2 - (a 1 - a 0) * hb1 + (a 2 - a 1) * hb0
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ha01.symm)
    (sub_ne_zero.mpr ha12.symm)) hr1 hCross

abbrev Coordinates (F : Type*) := F × (Fin 4 → F)

def Incidence {F : Type*} [Field F] (p l : Coordinates F) : Prop :=
  p.2 0 + l.2 0 = l.1 * p.1 ∧
  p.2 1 + l.2 1 = l.2 0 * p.1 ∧
  p.2 2 + l.2 2 = l.1 * p.2 0 ∧
  p.2 3 + l.2 3 = l.1 * p.2 1

abbrev incidenceGraph (F : Type*) [Field F] := Erdos713C6.bipGraph (Incidence (F := F))

lemma point_eq_of_x_eq {F : Type*} [Field F] {p q l : Coordinates F}
    (hp : Incidence p l) (hq : Incidence q l) (h : p.1 = q.1) : p = q := by
  have hy : p.2 0 = q.2 0 := by
    have hh := hp.1
    rw [h] at hh
    linear_combination hh - hq.1
  have hz : p.2 1 = q.2 1 := by
    have hh := hp.2.1
    rw [h] at hh
    linear_combination hh - hq.2.1
  apply Prod.ext h
  funext j
  fin_cases j
  · exact hy
  · exact hz
  · change p.2 2 = q.2 2
    have hh := hp.2.2.1
    rw [hy] at hh
    linear_combination hh - hq.2.2.1
  · change p.2 3 = q.2 3
    have hh := hp.2.2.2
    rw [hz] at hh
    linear_combination hh - hq.2.2.2

lemma line_eq_of_slope_eq {F : Type*} [Field F] {p l m : Coordinates F}
    (hl : Incidence p l) (hm : Incidence p m) (h : l.1 = m.1) : l = m := by
  have hb : l.2 0 = m.2 0 := by
    have hh := hl.1
    rw [h] at hh
    linear_combination hh - hm.1
  apply Prod.ext h
  funext j
  fin_cases j
  · exact hb
  · change l.2 1 = m.2 1
    have hh := hl.2.1
    rw [hb] at hh
    linear_combination hh - hm.2.1
  · change l.2 2 = m.2 2
    have hh := hl.2.2.1
    rw [h] at hh
    linear_combination hh - hm.2.2.1
  · change l.2 3 = m.2 3
    have hh := hl.2.2.2
    rw [h] at hh
    linear_combination hh - hm.2.2.2

lemma sum_next_sub {F : Type*} [Field F] (x : Fin 4 → F) : ∑ i, (x (i + 1) - x i) = 0 := by
  rw [sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin 4)) x

lemma no_octagon {F : Type*} [Field F] (p l : Fin 4 → Coordinates F)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, Incidence (p i) (l i)) (hB : ∀ i, Incidence (p (i + 1)) (l i)) : False := by
  have hNe : ∀ i : Fin 4, i ≠ i + 1 := by decide
  let a : Fin 4 → F := fun i => (l i).1
  let b : Fin 4 → F := fun i => (l i).2 0
  let x : Fin 4 → F := fun i => (p i).1
  let r : Fin 4 → F := fun i => x (i + 1) - x i
  have hAdj : ∀ i, a i ≠ a (i + 1) := by
    intro i he
    exact hNe i (hl (line_eq_of_slope_eq (hB i) (hA (i + 1)) he))
  have hr : ∀ i, r i ≠ 0 := by
    intro i he
    have hx : (p i).1 = (p (i + 1)).1 := (sub_eq_zero.mp he).symm
    exact hNe i (hp (point_eq_of_x_eq (hA i) (hB i) hx))
  have hY (i : Fin 4) : a i * r i = (p (i + 1)).2 0 - (p i).2 0 := by
    dsimp only [a, r, x]
    linear_combination (hA i).1 - (hB i).1
  have hZ (i : Fin 4) : b i * r i = (p (i + 1)).2 1 - (p i).2 1 := by
    dsimp only [b, r, x]
    linear_combination (hA i).2.1 - (hB i).2.1
  have hW (i : Fin 4) : a i ^ 2 * r i = (p (i + 1)).2 2 - (p i).2 2 := by
    dsimp only [a]
    linear_combination (hA i).2.2.1 - (hB i).2.2.1 + (l i).1 * hY i
  have hT (i : Fin 4) : a i * b i * r i = (p (i + 1)).2 3 - (p i).2 3 := by
    dsimp only [a]
    linear_combination (hA i).2.2.2 - (hB i).2.2.2 + (l i).1 * hZ i
  have hStep (i : Fin 4) : b (i + 1) - b i = (a (i + 1) - a i) * x (i + 1) := by
    dsimp only [a, b, x]
    linear_combination (hA (i + 1)).1 - (hB i).1
  apply four_step_moment_obstruction a b x r (hAdj 0) (hAdj 1) (hAdj 2) (hr 1) (hr 2)
    rfl (hStep 0) (hStep 1) (sum_next_sub x)
  · simp_rw [hY]
    exact sum_next_sub (fun i => (p i).2 0)
  · simp_rw [hW]
    exact sum_next_sub (fun i => (p i).2 2)
  · simp_rw [hZ]
    exact sum_next_sub (fun i => (p i).2 1)
  · simp_rw [hT]
    exact sum_next_sub (fun i => (p i).2 3)

abbrev C8 := cycleGraph 8

open Erdos713C6

lemma free_of_no_octagon {P L : Type*} (R : P → L → Prop)
    (h : ∀ (a : Fin 4 → P) (b : Fin 4 → L), Function.Injective a → Function.Injective b →
      (∀ i, R (a i) (b i)) → (∀ i, R (a (i + 1)) (b i)) → False) :
    C8.Free (bipGraph R) := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show C8.Adj 0 1 by decide)
  have h12 := f.toHom.map_rel' (show C8.Adj 1 2 by decide)
  have h23 := f.toHom.map_rel' (show C8.Adj 2 3 by decide)
  have h34 := f.toHom.map_rel' (show C8.Adj 3 4 by decide)
  have h45 := f.toHom.map_rel' (show C8.Adj 4 5 by decide)
  have h56 := f.toHom.map_rel' (show C8.Adj 5 6 by decide)
  have h67 := f.toHom.map_rel' (show C8.Adj 6 7 by decide)
  have h70 := f.toHom.map_rel' (show C8.Adj 7 0 by decide)
  change (bipGraph R).Adj (f 0) (f 1) at h01
  change (bipGraph R).Adj (f 1) (f 2) at h12
  change (bipGraph R).Adj (f 2) (f 3) at h23
  change (bipGraph R).Adj (f 3) (f 4) at h34
  change (bipGraph R).Adj (f 4) (f 5) at h45
  change (bipGraph R).Adj (f 5) (f 6) at h56
  change (bipGraph R).Adj (f 6) (f 7) at h67
  change (bipGraph R).Adj (f 7) (f 0) at h70
  cases e0 : f 0 with
  | inl x0 =>
    rw [e0] at h01
    obtain ⟨y0, e1, hR0⟩ := right_of_adj_left h01
    rw [e1] at h12
    obtain ⟨x1, e2, hR1⟩ := left_of_adj_right h12
    rw [e2] at h23
    obtain ⟨y1, e3, hR2⟩ := right_of_adj_left h23
    rw [e3] at h34
    obtain ⟨x2, e4, hR3⟩ := left_of_adj_right h34
    rw [e4] at h45
    obtain ⟨y2, e5, hR4⟩ := right_of_adj_left h45
    rw [e5] at h56
    obtain ⟨x3, e6, hR5⟩ := left_of_adj_right h56
    rw [e6] at h67
    obtain ⟨y3, e7, hR6⟩ := right_of_adj_left h67
    have hR7 : R x0 y3 := by simpa only [e7, e0] using h70
    apply h ![x0, x1, x2, x3] ![y0, y1, y2, y3]
    · apply Erdos713C10.injective_of_map f f.injective Sum.inl _ ![0, 2, 4, 6] (by decide)
      intro i; fin_cases i <;> assumption
    · apply Erdos713C10.injective_of_map f f.injective Sum.inr _ ![1, 3, 5, 7] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  | inr y0 =>
    rw [e0] at h01
    obtain ⟨x0, e1, hR0⟩ := left_of_adj_right h01
    rw [e1] at h12
    obtain ⟨y1, e2, hR1⟩ := right_of_adj_left h12
    rw [e2] at h23
    obtain ⟨x1, e3, hR2⟩ := left_of_adj_right h23
    rw [e3] at h34
    obtain ⟨y2, e4, hR3⟩ := right_of_adj_left h34
    rw [e4] at h45
    obtain ⟨x2, e5, hR4⟩ := left_of_adj_right h45
    rw [e5] at h56
    obtain ⟨y3, e6, hR5⟩ := right_of_adj_left h56
    rw [e6] at h67
    obtain ⟨x3, e7, hR6⟩ := left_of_adj_right h67
    have hR7 : R x3 y0 := by simpa only [e7, e0] using h70
    apply h ![x0, x1, x2, x3] ![y1, y2, y3, y0]
    · apply Erdos713C10.injective_of_map f f.injective Sum.inl _ ![1, 3, 5, 7] (by decide)
      intro i; fin_cases i <;> assumption
    · apply Erdos713C10.injective_of_map f f.injective Sum.inr _ ![2, 4, 6, 0] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

lemma incidenceGraph_free (F : Type*) [Field F] : C8.Free (incidenceGraph F) :=
  free_of_no_octagon Incidence no_octagon

def leftNeighbors {F : Type*} [Field F] (p : Coordinates F) :
    F ↪ (incidenceGraph F).neighborSet (Sum.inl p) where
  toFun a := ⟨Sum.inr (a, ![a * p.1 - p.2 0,
      (a * p.1 - p.2 0) * p.1 - p.2 1, a * p.2 0 - p.2 2, a * p.2 1 - p.2 3]), by
    change Incidence p _
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp <;> ring⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Coordinates F => x.1)
      (fun x : Coordinates F => x.1) v.val) h

def rightNeighbors {F : Type*} [Field F] (l : Coordinates F) :
    F ↪ (incidenceGraph F).neighborSet (Sum.inr l) where
  toFun x := ⟨Sum.inl (x, ![l.1 * x - l.2 0, l.2 0 * x - l.2 1,
      l.1 * (l.1 * x - l.2 0) - l.2 2, l.1 * (l.2 0 * x - l.2 1) - l.2 3]), by
    change Incidence _ l
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp <;> ring⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Coordinates F => x.1)
      (fun x : Coordinates F => x.1) v.val) h

open scoped Classical in
lemma incidenceGraph_degree_lower (F : Type*) [Field F] [Fintype F]
    (v : Coordinates F ⊕ Coordinates F) : Fintype.card F ≤ (incidenceGraph F).degree v := by
  classical
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inl p => exact Fintype.card_le_of_embedding (leftNeighbors p)
  | inr l => exact Fintype.card_le_of_embedding (rightNeighbors l)

open scoped Classical in
lemma incidenceGraph_edge_lower (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 6 ≤ (incidenceGraph F).edgeFinset.card := by
  classical
  have hh : ∑ v : Coordinates F ⊕ Coordinates F, Fintype.card F ≤
      ∑ v : Coordinates F ⊕ Coordinates F, (incidenceGraph F).degree v :=
    sum_le_sum fun v _ => incidenceGraph_degree_lower F v
  rw [sum_degrees_eq_twice_card_edges] at hh
  simp only [sum_const, card_univ, Fintype.card_sum, Coordinates, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.nsmul_eq_mul] at hh
  nlinarith

lemma extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 6 ≤ extremalNumber (2 * p ^ 5) C8 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have he := incidenceGraph_edge_lower (ZMod p)
  have hExt := card_edgeFinset_le_extremalNumber (incidenceGraph_free (ZMod p))
  have hc : Fintype.card (Coordinates (ZMod p) ⊕ Coordinates (ZMod p)) = 2 * p ^ 5 := by
    simp only [Coordinates, Fintype.card_sum, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    ring
  rw [hc] at hExt
  rw [ZMod.card] at he
  exact he.trans hExt

lemma rate_lower_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : C8 ⊑ H) {a : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a)) :
    (6 : ℝ) / 5 ≤ a := by
  apply Erdos713C10.lower_exponent_of_prime_bound hO
  intro p hp
  exact (extremal_lower_prime p hp).trans hH.extremalNumber_le

lemma exponent_lower_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : C8 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (6 : ℝ) / 5 ≤ a :=
  rate_lower_of_containment hH ((isBigO_const_mul_right_iff hc).mp h.isBigO)

lemma exponent_bounds {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n C8 : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (6 : ℝ) / 5 ≤ a ∧ a ≤ (5 : ℝ) / 4 := by
  refine ⟨exponent_lower_of_containment (IsContained.refl _) hc h, ?_⟩
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using
    Erdos713EvenCycle.exponent_upper_of_containment (by decide : 2 ≤ 4)
      (show C8 ⊑ cycleGraph (2 * 4) from IsContained.refl _) hc h

#print axioms extremal_lower_prime
#print axioms exponent_bounds
end Erdos713C8
