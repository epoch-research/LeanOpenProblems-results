import FormalConjecturesUtil

/-! The six-cycle case: algebraic lower bounds and breadth-first-layer bounds. -/

open SimpleGraph Filter Asymptotics Finset

namespace Erdos713C6

abbrev C6 := cycleGraph 6

def bipGraph {P L : Type*} (R : P → L → Prop) : SimpleGraph (P ⊕ L) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr y => R x y
    | Sum.inr y, Sum.inl x => R x y
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro v; cases v <;> simp

theorem right_of_adj_left {P L : Type*} {R : P → L → Prop} {x : P} {v : P ⊕ L}
    (h : (bipGraph R).Adj (Sum.inl x) v) : ∃ y, v = Sum.inr y ∧ R x y := by
  cases v with
  | inl y => exact h.elim
  | inr y => exact ⟨y, rfl, h⟩

theorem left_of_adj_right {P L : Type*} {R : P → L → Prop} {y : L} {v : P ⊕ L}
    (h : (bipGraph R).Adj (Sum.inr y) v) : ∃ x, v = Sum.inl x ∧ R x y := by
  cases v with
  | inl x => exact ⟨x, rfl, h⟩
  | inr x => exact h.elim

theorem injective_triple_of_map {U V : Type*} (f : Fin 6 → V) (hf : Function.Injective f)
    (g : U → V) (x : Fin 3 → U) (k : Fin 3 → Fin 6) (hk : Function.Injective k)
    (he : ∀ i, f (k i) = g (x i)) : Function.Injective x := by
  intro i j hij
  apply hk
  apply hf
  rw [he i, he j, hij]

theorem free_of_no_hexagon {P L : Type*} (R : P → L → Prop)
    (h : ∀ (a : Fin 3 → P) (b : Fin 3 → L), Function.Injective a → Function.Injective b →
      (∀ i, R (a i) (b i)) → (∀ i, R (a (i + 1)) (b i)) → False) :
    C6.Free (bipGraph R) := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show C6.Adj 0 1 by decide)
  have h12 := f.toHom.map_rel' (show C6.Adj 1 2 by decide)
  have h23 := f.toHom.map_rel' (show C6.Adj 2 3 by decide)
  have h34 := f.toHom.map_rel' (show C6.Adj 3 4 by decide)
  have h45 := f.toHom.map_rel' (show C6.Adj 4 5 by decide)
  have h50 := f.toHom.map_rel' (show C6.Adj 5 0 by decide)
  change (bipGraph R).Adj (f 0) (f 1) at h01
  change (bipGraph R).Adj (f 1) (f 2) at h12
  change (bipGraph R).Adj (f 2) (f 3) at h23
  change (bipGraph R).Adj (f 3) (f 4) at h34
  change (bipGraph R).Adj (f 4) (f 5) at h45
  change (bipGraph R).Adj (f 5) (f 0) at h50
  cases e0 : f 0 with
  | inl x₀ =>
    rw [e0] at h01
    obtain ⟨y₀, e1, h00⟩ := right_of_adj_left h01
    rw [e1] at h12
    obtain ⟨x₁, e2, h10⟩ := left_of_adj_right h12
    rw [e2] at h23
    obtain ⟨y₁, e3, h11⟩ := right_of_adj_left h23
    rw [e3] at h34
    obtain ⟨x₂, e4, h21⟩ := left_of_adj_right h34
    rw [e4] at h45
    obtain ⟨y₂, e5, h22⟩ := right_of_adj_left h45
    have h02 : R x₀ y₂ := by simpa only [e5, e0] using h50
    apply h ![x₀, x₁, x₂] ![y₀, y₁, y₂]
    · apply injective_triple_of_map f f.injective Sum.inl _ ![0, 2, 4] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_triple_of_map f f.injective Sum.inr _ ![1, 3, 5] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  | inr y₀ =>
    rw [e0] at h01
    obtain ⟨x₀, e1, h00⟩ := left_of_adj_right h01
    rw [e1] at h12
    obtain ⟨y₁, e2, h01'⟩ := right_of_adj_left h12
    rw [e2] at h23
    obtain ⟨x₁, e3, h11⟩ := left_of_adj_right h23
    rw [e3] at h34
    obtain ⟨y₂, e4, h12'⟩ := right_of_adj_left h34
    rw [e4] at h45
    obtain ⟨x₂, e5, h22⟩ := left_of_adj_right h45
    have h20 : R x₂ y₀ := by simpa only [e5, e0] using h50
    apply h ![x₀, x₁, x₂] ![y₁, y₂, y₀]
    · apply injective_triple_of_map f f.injective Sum.inl _ ![1, 3, 5] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_triple_of_map f f.injective Sum.inr _ ![2, 4, 0] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

abbrev Triple (F : Type*) := F × F × F

def WengerRel {F : Type*} [Field F] (p l : Triple F) : Prop :=
  p.2.1 = l.1 * p.1 + l.2.1 ∧ p.2.2 = l.1 ^ 2 * p.1 + l.2.2

abbrev wengerGraph (F : Type*) [Field F] := bipGraph (WengerRel (F := F))

theorem point_eq_of_x_eq {F : Type*} [Field F] {p q l : Triple F}
    (hp : WengerRel p l) (hq : WengerRel q l) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  apply Prod.ext <;> dsimp
  · rw [hp.1, hq.1, h]
  · rw [hp.2, hq.2, h]

theorem line_eq_of_slope_eq {F : Type*} [Field F] {p l m : Triple F}
    (hl : WengerRel p l) (hm : WengerRel p m) (h : l.1 = m.1) : l = m := by
  apply Prod.ext h
  apply Prod.ext <;> dsimp
  · linear_combination hm.1 - hl.1 - p.1 * h
  · have ht := hl.2
    rw [h] at ht
    exact add_left_cancel (ht.symm.trans hm.2)

theorem wenger_no_hexagon {F : Type*} [Field F] (p l : Fin 3 → Triple F)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, WengerRel (p i) (l i)) (hB : ∀ i, WengerRel (p (i + 1)) (l i)) : False := by
  have h01 : (l 0).1 ≠ (l 1).1 := by
    intro h
    exact (show (0 : Fin 3) ≠ 1 by decide)
      (hl (line_eq_of_slope_eq (hB 0) (hA 1) h))
  have h02 : (l 0).1 ≠ (l 2).1 := by
    intro h
    exact (show (0 : Fin 3) ≠ 2 by decide)
      (hl (line_eq_of_slope_eq (hA 0) (hB 2) h))
  have hx01 : (p 0).1 ≠ (p 1).1 := by
    intro h
    exact (show (0 : Fin 3) ≠ 1 by decide)
      (hp (point_eq_of_x_eq (hA 0) (hB 0) h))
  have hb0 : WengerRel (p 1) (l 0) := hB 0
  have hb1 : WengerRel (p 2) (l 1) := hB 1
  have hb2 : WengerRel (p 0) (l 2) := hB 2
  have hy : (l 0).1 * ((p 0).1 - (p 1).1) +
      (l 1).1 * ((p 1).1 - (p 2).1) + (l 2).1 * ((p 2).1 - (p 0).1) = 0 := by
    linear_combination -(hA 0).1 + hb0.1 - (hA 1).1 + hb1.1 -
      (hA 2).1 + hb2.1
  have hz : (l 0).1 ^ 2 * ((p 0).1 - (p 1).1) +
      (l 1).1 ^ 2 * ((p 1).1 - (p 2).1) + (l 2).1 ^ 2 * ((p 2).1 - (p 0).1) = 0 := by
    linear_combination -(hA 0).2 + hb0.2 - (hA 1).2 + hb1.2 -
      (hA 2).2 + hb2.2
  have hprod : ((l 0).1 - (l 1).1) * ((l 0).1 - (l 2).1) *
      ((p 0).1 - (p 1).1) = 0 := by
    linear_combination hz - ((l 1).1 + (l 2).1) * hy
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h01) (sub_ne_zero.mpr h02))
    (sub_ne_zero.mpr hx01) hprod

theorem wengerGraph_free (F : Type*) [Field F] : C6.Free (wengerGraph F) :=
  free_of_no_hexagon WengerRel wenger_no_hexagon

def leftNeighbors {F : Type*} [Field F] (p : Triple F) :
    F ↪ (wengerGraph F).neighborSet (Sum.inl p) where
  toFun a := ⟨Sum.inr (a, p.2.1 - a * p.1, p.2.2 - a ^ 2 * p.1), by
    change WengerRel p _
    constructor <;> dsimp <;> ring⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Triple F => x.1)
      (fun x : Triple F => x.1) v.val) h

def rightNeighbors {F : Type*} [Field F] (l : Triple F) :
    F ↪ (wengerGraph F).neighborSet (Sum.inr l) where
  toFun x := ⟨Sum.inl (x, l.1 * x + l.2.1, l.1 ^ 2 * x + l.2.2), by
    change WengerRel _ l
    exact ⟨rfl, rfl⟩⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Triple F => x.1)
      (fun x : Triple F => x.1) v.val) h

open scoped Classical in
theorem wengerGraph_degree_lower (F : Type*) [Field F] [Fintype F]
    (v : Triple F ⊕ Triple F) : Fintype.card F ≤ (wengerGraph F).degree v := by
  classical
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inl p => exact Fintype.card_le_of_embedding (leftNeighbors p)
  | inr l => exact Fintype.card_le_of_embedding (rightNeighbors l)

open scoped Classical in
theorem wengerGraph_edge_lower (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 4 ≤ (wengerGraph F).edgeFinset.card := by
  classical
  have hh : ∑ v : Triple F ⊕ Triple F, Fintype.card F ≤
      ∑ v : Triple F ⊕ Triple F, (wengerGraph F).degree v :=
    sum_le_sum fun v _ => wengerGraph_degree_lower F v
  rw [sum_degrees_eq_twice_card_edges] at hh
  simp only [sum_const, card_univ, Fintype.card_sum, Triple, Fintype.card_prod,
    Nat.nsmul_eq_mul] at hh
  nlinarith

theorem extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 4 ≤ extremalNumber (2 * p ^ 3) C6 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have he := wengerGraph_edge_lower (ZMod p)
  have hExt := card_edgeFinset_le_extremalNumber (wengerGraph_free (ZMod p))
  have hc : Fintype.card (Triple (ZMod p) ⊕ Triple (ZMod p)) = 2 * p ^ 3 := by
    simp only [Triple, Fintype.card_sum, Fintype.card_prod, ZMod.card]
    ring
  rw [hc] at hExt
  rw [ZMod.card] at he
  exact he.trans hExt

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ}
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 4 ≤ f (2 * p ^ 3)) : (4 : ℝ) / 3 ≤ a := by
  by_contra ha
  have ha' : a < (4 : ℝ) / 3 := lt_of_not_ge ha
  obtain ⟨C, _, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 3) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro p
    have hp := Nat.le_self_pow (by decide : 3 ≠ 0) p
    change p ≤ 2 * p ^ 3
    omega
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (4 - 3 * a) ≤ C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 4 ≤ (f (2 * p ^ 3) : ℝ) := by exact_mod_cast hlow p hprime
    have hu : (f (2 * p ^ 3) : ℝ) ≤ C * (2 * (p : ℝ) ^ 3) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg (2 * p ^ 3)) a)] at hp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hp
    have he := hl.trans hu
    have hp3 : ((p : ℝ) ^ 3) ^ a = (p : ℝ) ^ (3 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hp0.le 3), hp3] at he
    rw [Real.rpow_sub hp0, div_le_iff₀ (Real.rpow_pos_of_pos hp0 (3 * a))]
    have hp4 : (p : ℝ) ^ (4 : ℝ) = (p : ℝ) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 4
    rw [hp4]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (4 - 3 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 4 - 3 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)

theorem exponent_lower_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : C6 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (4 : ℝ) / 3 ≤ a := by
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply lower_exponent_of_prime_bound hO
  intro p hp
  exact (extremal_lower_prime p hp).trans hH.extremalNumber_le

end Erdos713C6

#print axioms Erdos713C6.wengerGraph_free

#print axioms Erdos713C6.exponent_lower_of_containment
