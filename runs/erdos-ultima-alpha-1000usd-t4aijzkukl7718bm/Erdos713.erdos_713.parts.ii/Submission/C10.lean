import FormalConjecturesUtil
import Submission.Current

/-! A polynomial incidence construction excluding ten-cycles. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713C10
open Finset Erdos713C6

theorem singleton_colour {A : Type*} (a : Fin 5 → A)
    (ha : ∀ i, a i ≠ a (i + 1)) : ∃ i, ∀ j, a j = a i → j = i := by
  classical
  have h0 : a 0 ≠ a 1 := ha 0
  have h1 : a 1 ≠ a 2 := ha 1
  have h2 : a 2 ≠ a 3 := ha 2
  have h3 : a 3 ≠ a 4 := ha 3
  have h4 : a 4 ≠ a 0 := ha 4
  by_cases h02 : a 0 = a 2
  · by_cases h14 : a 1 = a 4
    · refine ⟨3, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨4, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  by_cases h03 : a 0 = a 3
  · by_cases h14 : a 1 = a 4
    · refine ⟨2, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨1, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  · refine ⟨0, ?_⟩
    intro j hj
    fin_cases j <;> simp_all

theorem weighted_eval_zero {I F : Type*} [Fintype I] [Field F] (a r : I → F) {m : ℕ}
    (hm : ∀ k < m, ∑ i, r i * a i ^ k = 0) (P : Polynomial F) (hP : P.natDegree < m) :
    ∑ i, r i * P.eval (a i) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range' hP, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro k hk
  calc
    ∑ i, r i * (P.coeff k * a i ^ k) = P.coeff k * ∑ i, r i * a i ^ k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hm k (mem_range.mp hk), mul_zero]

theorem singleton_moment_zero {I F : Type*} [Fintype I] [Field F] (a r : I → F)
    (hm : ∀ k < Fintype.card I, ∑ i, r i * a i ^ k = 0) (i : I)
    (hi : ∀ j, a j = a i → j = i) : r i = 0 := by
  classical
  let P : Polynomial F := ∏ j ∈ (univ.erase i), (Polynomial.X - Polynomial.C (a j))
  have hP : P.natDegree < Fintype.card I := by
    calc
      P.natDegree ≤ ∑ j ∈ univ.erase i, (Polynomial.X - Polynomial.C (a j)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ = Fintype.card I - 1 := by simp
      _ < Fintype.card I := Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨i⟩) (by decide)
  have hEval (j : I) (hj : j ≠ i) : P.eval (a j) = 0 := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply prod_eq_zero (mem_erase.mpr ⟨hj, mem_univ _⟩)
    exact sub_self _
  have hNonzero : P.eval (a i) ≠ 0 := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun hh => (mem_erase.mp hj).1 (hi j hh.symm))
  have hh := weighted_eval_zero a r hm P hP
  have hs : ∑ j, r j * P.eval (a j) = r i * P.eval (a i) := by
    apply sum_eq_single i
    · intro j _ hj
      rw [hEval j hj, mul_zero]
    · simp
  rw [hs] at hh
  exact (mul_eq_zero.mp hh).resolve_right hNonzero

abbrev Coordinates (F : Type*) := F × (Fin 4 → F)

def Incidence {F : Type*} [Field F] (p l : Coordinates F) : Prop :=
  ∀ j : Fin 4, p.2 j = l.1 ^ (j.val + 1) * p.1 + l.2 j

abbrev incidenceGraph (F : Type*) [Field F] := bipGraph (Incidence (F := F))

theorem point_eq_of_x_eq {F : Type*} [Field F] {p q l : Coordinates F}
    (hp : Incidence p l) (hq : Incidence q l) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  funext j
  rw [hp j, hq j, h]

theorem line_eq_of_slope_eq {F : Type*} [Field F] {p l m : Coordinates F}
    (hl : Incidence p l) (hm : Incidence p m) (h : l.1 = m.1) : l = m := by
  apply Prod.ext h
  funext j
  have hh := hl j
  rw [h] at hh
  exact add_left_cancel (hh.symm.trans (hm j))

theorem sum_next_sub {F : Type*} [Field F] (x : Fin 5 → F) : ∑ i, (x (i + 1) - x i) = 0 := by
  rw [sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin 5)) x

theorem no_decagon {F : Type*} [Field F] (p l : Fin 5 → Coordinates F)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, Incidence (p i) (l i)) (hB : ∀ i, Incidence (p (i + 1)) (l i)) : False := by
  have hNe : ∀ i : Fin 5, i ≠ i + 1 := by decide
  let a : Fin 5 → F := fun i => (l i).1
  let r : Fin 5 → F := fun i => (p (i + 1)).1 - (p i).1
  have hAdj : ∀ i, a i ≠ a (i + 1) := by
    intro i he
    exact hNe i (hl (line_eq_of_slope_eq (hB i) (hA (i + 1)) he))
  have hr : ∀ i, r i ≠ 0 := by
    intro i he
    have hx : (p i).1 = (p (i + 1)).1 := (sub_eq_zero.mp he).symm
    exact hNe i (hp (point_eq_of_x_eq (hA i) (hB i) hx))
  have hm : ∀ k < Fintype.card (Fin 5), ∑ i, r i * a i ^ k = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa only [pow_zero, mul_one, r] using sum_next_sub (fun i => (p i).1)
    have hk5 : k < 5 := by simpa using hk
    let j : Fin 4 := ⟨k - 1, by omega⟩
    have hj : j.val + 1 = k := by dsimp [j]; omega
    have hStep (i : Fin 5) : r i * a i ^ k = (p (i + 1)).2 j - (p i).2 j := by
      have hhA := hA i j
      have hhB := hB i j
      rw [hj] at hhA hhB
      dsimp only [r, a]
      linear_combination hhA - hhB
    simp_rw [hStep]
    exact sum_next_sub (fun i => (p i).2 j)
  obtain ⟨i, hi⟩ := singleton_colour a hAdj
  exact hr i (singleton_moment_zero a r hm i hi)

abbrev C10 := cycleGraph 10

theorem injective_of_map {I J U V : Type*} (f : J → V) (hf : Function.Injective f)
    (g : U → V) (x : I → U) (k : I → J) (hk : Function.Injective k)
    (he : ∀ i, f (k i) = g (x i)) : Function.Injective x := by
  intro i j hij
  apply hk
  apply hf
  rw [he i, he j, hij]

theorem free_of_no_decagon {P L : Type*} (R : P → L → Prop)
    (h : ∀ (a : Fin 5 → P) (b : Fin 5 → L), Function.Injective a → Function.Injective b →
      (∀ i, R (a i) (b i)) → (∀ i, R (a (i + 1)) (b i)) → False) :
    C10.Free (bipGraph R) := by
  rintro ⟨f⟩
  have h01 := f.toHom.map_rel' (show C10.Adj 0 1 by decide)
  have h12 := f.toHom.map_rel' (show C10.Adj 1 2 by decide)
  have h23 := f.toHom.map_rel' (show C10.Adj 2 3 by decide)
  have h34 := f.toHom.map_rel' (show C10.Adj 3 4 by decide)
  have h45 := f.toHom.map_rel' (show C10.Adj 4 5 by decide)
  have h56 := f.toHom.map_rel' (show C10.Adj 5 6 by decide)
  have h67 := f.toHom.map_rel' (show C10.Adj 6 7 by decide)
  have h78 := f.toHom.map_rel' (show C10.Adj 7 8 by decide)
  have h89 := f.toHom.map_rel' (show C10.Adj 8 9 by decide)
  have h90 := f.toHom.map_rel' (show C10.Adj 9 0 by decide)
  change (bipGraph R).Adj (f 0) (f 1) at h01
  change (bipGraph R).Adj (f 1) (f 2) at h12
  change (bipGraph R).Adj (f 2) (f 3) at h23
  change (bipGraph R).Adj (f 3) (f 4) at h34
  change (bipGraph R).Adj (f 4) (f 5) at h45
  change (bipGraph R).Adj (f 5) (f 6) at h56
  change (bipGraph R).Adj (f 6) (f 7) at h67
  change (bipGraph R).Adj (f 7) (f 8) at h78
  change (bipGraph R).Adj (f 8) (f 9) at h89
  change (bipGraph R).Adj (f 9) (f 0) at h90
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
    rw [e7] at h78
    obtain ⟨x4, e8, hR7⟩ := left_of_adj_right h78
    rw [e8] at h89
    obtain ⟨y4, e9, hR8⟩ := right_of_adj_left h89
    have hR9 : R x0 y4 := by simpa only [e9, e0] using h90
    apply h ![x0, x1, x2, x3, x4] ![y0, y1, y2, y3, y4]
    · apply injective_of_map f f.injective Sum.inl _ ![0, 2, 4, 6, 8] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_of_map f f.injective Sum.inr _ ![1, 3, 5, 7, 9] (by decide)
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
    rw [e7] at h78
    obtain ⟨y4, e8, hR7⟩ := right_of_adj_left h78
    rw [e8] at h89
    obtain ⟨x4, e9, hR8⟩ := left_of_adj_right h89
    have hR9 : R x4 y0 := by simpa only [e9, e0] using h90
    apply h ![x0, x1, x2, x3, x4] ![y1, y2, y3, y4, y0]
    · apply injective_of_map f f.injective Sum.inl _ ![1, 3, 5, 7, 9] (by decide)
      intro i; fin_cases i <;> assumption
    · apply injective_of_map f f.injective Sum.inr _ ![2, 4, 6, 8, 0] (by decide)
      intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

theorem incidenceGraph_free (F : Type*) [Field F] : C10.Free (incidenceGraph F) :=
  free_of_no_decagon Incidence no_decagon

def leftNeighbors {F : Type*} [Field F] (p : Coordinates F) :
    F ↪ (incidenceGraph F).neighborSet (Sum.inl p) where
  toFun a := ⟨Sum.inr (a, fun j => p.2 j - a ^ (j.val + 1) * p.1), by
    change Incidence p _
    intro j
    dsimp
    ring⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Coordinates F => x.1)
      (fun x : Coordinates F => x.1) v.val) h

def rightNeighbors {F : Type*} [Field F] (l : Coordinates F) :
    F ↪ (incidenceGraph F).neighborSet (Sum.inr l) where
  toFun x := ⟨Sum.inl (x, fun j => l.1 ^ (j.val + 1) * x + l.2 j), by
    change Incidence _ l
    intro j
    rfl⟩
  inj' := by
    intro a b h
    exact congrArg (fun v => Sum.elim (fun x : Coordinates F => x.1)
      (fun x : Coordinates F => x.1) v.val) h

open scoped Classical in
theorem incidenceGraph_degree_lower (F : Type*) [Field F] [Fintype F]
    (v : Coordinates F ⊕ Coordinates F) : Fintype.card F ≤ (incidenceGraph F).degree v := by
  classical
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inl p => exact Fintype.card_le_of_embedding (leftNeighbors p)
  | inr l => exact Fintype.card_le_of_embedding (rightNeighbors l)

open scoped Classical in
theorem incidenceGraph_edge_lower (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 6 ≤ (incidenceGraph F).edgeFinset.card := by
  classical
  have hh : ∑ v : Coordinates F ⊕ Coordinates F, Fintype.card F ≤
      ∑ v : Coordinates F ⊕ Coordinates F, (incidenceGraph F).degree v :=
    sum_le_sum fun v _ => incidenceGraph_degree_lower F v
  rw [sum_degrees_eq_twice_card_edges] at hh
  simp only [sum_const, card_univ, Fintype.card_sum, Coordinates, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.nsmul_eq_mul] at hh
  nlinarith

theorem extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p ^ 6 ≤ extremalNumber (2 * p ^ 5) C10 := by
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

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ}
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 6 ≤ f (2 * p ^ 5)) : (6 : ℝ) / 5 ≤ a := by
  by_contra ha
  have ha' : a < (6 : ℝ) / 5 := lt_of_not_ge ha
  obtain ⟨C, _, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 5) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro p
    have hp := Nat.le_self_pow (by decide : 5 ≠ 0) p
    change p ≤ 2 * p ^ 5
    omega
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (6 - 5 * a) ≤ C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 6 ≤ (f (2 * p ^ 5) : ℝ) := by exact_mod_cast hlow p hprime
    have hu : (f (2 * p ^ 5) : ℝ) ≤ C * (2 * (p : ℝ) ^ 5) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg (2 * p ^ 5)) a)] at hp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hp
    have he := hl.trans hu
    have hp3 : ((p : ℝ) ^ 5) ^ a = (p : ℝ) ^ (5 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hp0.le 5), hp3] at he
    rw [Real.rpow_sub hp0, div_le_iff₀ (Real.rpow_pos_of_pos hp0 (5 * a))]
    have hp4 : (p : ℝ) ^ (6 : ℝ) = (p : ℝ) ^ (6 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 6
    rw [hp4]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (6 - 5 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 6 - 5 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)

theorem exponent_lower_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : C10 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (6 : ℝ) / 5 ≤ a := by
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply lower_exponent_of_prime_bound hO
  intro p hp
  exact (extremal_lower_prime p hp).trans hH.extremalNumber_le


#print axioms extremal_lower_prime
#print axioms exponent_lower_of_containment
end Erdos713C10
