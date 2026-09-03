import FormalConjecturesUtil

/-!
# A finite-field lower bound for the C4 extremal number

The two vertex classes are points `(x,y)` and nonvertical lines `(a,b)`, with
incidence `y = a*x+b`. Over a finite field of cardinality `q`, this gives a
bipartite C4-free graph with `2*q^2` vertices and `q^3` edges.

The forbidden graph is the complete bipartite graph on `Fin 2 ⊕ Fin 2`.
Consequently `ex(2*p^2,C4) ≥ p^3` for every prime `p`. The infinitude of primes
then shows that any power-law upper bound for `ex(n,C4)` has exponent at least
`3/2`, in particular any positive power-law asymptotic has this property.

This file does not prove the matching upper bound or resolve the general
rational-exponent conjecture. All results here are independent of the other
submission files.
-/

open SimpleGraph
open scoped BigOperators

namespace Erdos713C4Lower

universe u

/-- The C4 forbidden graph, with two vertices in each of its two classes. -/
abbrev C4 : SimpleGraph (Fin 2 ⊕ Fin 2) := completeBipartiteGraph (Fin 2) (Fin 2)

/-- Left vertices are points; right vertices are slope-intercept pairs. -/
abbrev Vertex (K : Type u) := (K × K) ⊕ (K × K)

/-- Point-line incidence, with no vertical lines. -/
def incidenceGraph (K : Type u) [Field K] : SimpleGraph (Vertex K) where
  Adj
    | .inl P, .inr L => P.2 = L.1 * P.1 + L.2
    | .inr L, .inl P => P.2 = L.1 * P.1 + L.2
    | _, _ => False
  symm := by rintro (P | L) (Q | M) <;> simp
  loopless := by rintro (P | L) <;> simp

instance incidenceGraph_decidableAdj (K : Type u) [Field K] [DecidableEq K] :
    DecidableRel (incidenceGraph K).Adj := by
  rintro (P | L) (Q | M) <;> dsimp [incidenceGraph] <;> infer_instance

variable {K : Type u} [Field K]

@[simp] theorem incidenceGraph_adj_inl_inr (P L : K × K) :
    (incidenceGraph K).Adj (.inl P) (.inr L) ↔ P.2 = L.1 * P.1 + L.2 := Iff.rfl

@[simp] theorem incidenceGraph_adj_inr_inl (L P : K × K) :
    (incidenceGraph K).Adj (.inr L) (.inl P) ↔ P.2 = L.1 * P.1 + L.2 := Iff.rfl

@[simp] theorem incidenceGraph_not_adj_inl_inl (P Q : K × K) :
    ¬ (incidenceGraph K).Adj (.inl P) (.inl Q) := not_false

@[simp] theorem incidenceGraph_not_adj_inr_inr (L M : K × K) :
    ¬ (incidenceGraph K).Adj (.inr L) (.inr M) := not_false

/-- The displayed point and line classes are a bipartition. -/
theorem incidenceGraph_isBipartiteWith :
    (incidenceGraph K).IsBipartiteWith
      (Set.range (Sum.inl : K × K → Vertex K))
      (Set.range (Sum.inr : K × K → Vertex K)) where
  disjoint := by
    rw [Set.disjoint_left]
    rintro v ⟨P, rfl⟩ ⟨L, hL⟩
    cases hL
  mem_of_adj := by
    rintro (P | L) (Q | M) h <;> simp_all [incidenceGraph, Set.mem_range]

/-- The incidence graph is bipartite. -/
theorem incidenceGraph_isBipartite : (incidenceGraph K).IsBipartite :=
  incidenceGraph_isBipartiteWith.isBipartite

/-- Two distinct points cannot lie on two distinct nonvertical lines. -/
lemma incidence_rectangle {P Q L M : K × K}
    (hPL : P.2 = L.1 * P.1 + L.2) (hQL : Q.2 = L.1 * Q.1 + L.2)
    (hPM : P.2 = M.1 * P.1 + M.2) (hQM : Q.2 = M.1 * Q.1 + M.2) :
    P = Q ∨ L = M := by
  by_cases hPQ : P = Q
  · exact Or.inl hPQ
  right
  have hx : P.1 ≠ Q.1 := by
    intro hx
    apply hPQ
    apply Prod.ext hx
    calc
      P.2 = L.1 * P.1 + L.2 := hPL
      _ = L.1 * Q.1 + L.2 := by rw [hx]
      _ = Q.2 := hQL.symm
  have hprod : (L.1 - M.1) * (P.1 - Q.1) = 0 := by
    linear_combination -hPL + hQL + hPM - hQM
  have ha : L.1 = M.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hx))
  apply Prod.ext ha
  have hb := hPL.symm.trans hPM
  rw [ha] at hb
  exact add_left_cancel hb

/-- In either orientation of the bipartition, an adjacency rectangle repeats a vertex. -/
lemma eq_or_eq_of_rectangle {v w x y : Vertex K}
    (hvx : (incidenceGraph K).Adj v x) (hvy : (incidenceGraph K).Adj v y)
    (hwx : (incidenceGraph K).Adj w x) (hwy : (incidenceGraph K).Adj w y) :
    v = w ∨ x = y := by
  cases v <;> cases w <;> cases x <;> cases y <;>
    simp only [incidenceGraph] at hvx hvy hwx hwy <;> try contradiction
  · exact (incidence_rectangle hvx hwx hvy hwy).imp
      (congrArg Sum.inl) (congrArg Sum.inr)
  · rcases incidence_rectangle hvx hvy hwx hwy with h | h
    · exact Or.inr (congrArg Sum.inl h)
    · exact Or.inl (congrArg Sum.inr h)

/-- There is no injective graph homomorphism from C4 into the incidence graph. -/
theorem incidenceGraph_C4_free : C4.Free (incidenceGraph K) := by
  rintro ⟨f⟩
  have hAdj (i j : Fin 2) :
      (incidenceGraph K).Adj (f (.inl i)) (f (.inr j)) :=
    f.toHom.map_adj (by simp [C4, completeBipartiteGraph_adj])
  rcases eq_or_eq_of_rectangle (hAdj 0 0) (hAdj 0 1) (hAdj 1 0) (hAdj 1 1) with h | h
  · exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj (f.injective h))
  · exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inr.inj (f.injective h))

section Finite

variable [Fintype K]

omit [Field K] in
/-- There are `q^2` points and `q^2` nonvertical lines. -/
@[simp] theorem card_vertex : Fintype.card (Vertex K) = 2 * Fintype.card K ^ 2 := by
  simp [Vertex, pow_two, two_mul]

variable [DecidableEq K]

/-- Lines through a point are parametrized by their slopes. -/
theorem neighborFinset_inl (P : K × K) :
    (incidenceGraph K).neighborFinset (.inl P) =
      Finset.univ.image (fun a : K => (Sum.inr (a, P.2 - a * P.1) : Vertex K)) := by
  ext v
  cases v with
  | inl Q => simp [incidenceGraph]
  | inr L =>
    rcases L with ⟨a, b⟩
    simp only [mem_neighborFinset, incidenceGraph, Finset.mem_image,
      Finset.mem_univ, true_and, Sum.inr.injEq, Prod.mk.injEq, exists_eq_left]
    constructor <;> intro h <;> linear_combination h

/-- Points on a nonvertical line are parametrized by their first coordinates. -/
theorem neighborFinset_inr (L : K × K) :
    (incidenceGraph K).neighborFinset (.inr L) =
      Finset.univ.image (fun x : K => (Sum.inl (x, L.1 * x + L.2) : Vertex K)) := by
  ext v
  cases v with
  | inl P =>
    rcases P with ⟨x, y⟩
    simp [incidenceGraph, eq_comm]
  | inr M => simp [incidenceGraph]

@[simp] theorem degree_inl (P : K × K) :
    (incidenceGraph K).degree (.inl P) = Fintype.card K := by
  unfold SimpleGraph.degree
  rw [neighborFinset_inl, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro a b hab
    exact congrArg Prod.fst (Sum.inr.inj hab)

@[simp] theorem degree_inr (L : K × K) :
    (incidenceGraph K).degree (.inr L) = Fintype.card K := by
  unfold SimpleGraph.degree
  rw [neighborFinset_inr, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj hxy)

/-- The incidence graph over a field of cardinality `q` is `q`-regular. -/
@[simp] theorem incidenceGraph_degree (v : Vertex K) :
    (incidenceGraph K).degree v = Fintype.card K := by
  cases v <;> simp

/-- Exact edge count, obtained from the degree-sum formula. -/
@[simp] theorem card_edgeFinset :
    (incidenceGraph K).edgeFinset.card = Fintype.card K ^ 3 := by
  have h := (incidenceGraph K).sum_degrees_eq_twice_card_edges
  simp only [incidenceGraph_degree, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, card_vertex] at h
  have hpow : 2 * Fintype.card K ^ 2 * Fintype.card K = 2 * Fintype.card K ^ 3 := by ring
  rw [hpow] at h
  omega

end Finite

/-- The C4 extremal lower bound over any finite field. -/
theorem field_extremalNumber_lower (K : Type u) [Field K] [Fintype K] :
    Fintype.card K ^ 3 ≤ extremalNumber (2 * Fintype.card K ^ 2) C4 := by
  classical
  simpa only [card_edgeFinset, card_vertex] using
    (card_edgeFinset_le_extremalNumber (incidenceGraph_C4_free (K := K)))

/-- All parameters of the explicit construction over `ZMod p`, for prime `p`. -/
theorem prime_incidenceGraph_spec (p : ℕ) [Fact p.Prime] :
    (incidenceGraph (ZMod p)).IsBipartite ∧
      Fintype.card (Vertex (ZMod p)) = 2 * p ^ 2 ∧
      (incidenceGraph (ZMod p)).edgeFinset.card = p ^ 3 ∧
      C4.Free (incidenceGraph (ZMod p)) := by
  refine ⟨incidenceGraph_isBipartite, ?_, ?_, incidenceGraph_C4_free⟩
  · simp only [card_vertex, ZMod.card]
  · simp only [card_edgeFinset, ZMod.card]

/-- In particular, `ex(2*p^2,C4) ≥ p^3` for every prime `p`. -/
theorem prime_extremalNumber_lower (p : ℕ) (hp : p.Prime) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2) C4 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.card] using field_extremalNumber_lower (ZMod p)

open Filter Asymptotics

/-- An upper power-law bound for the C4 extremal function has exponent at least `3/2`.
Only the infinitude of primes is used; no bound on gaps between primes is needed. -/
theorem exponent_ge_three_halves_of_isBigO {a : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n C4 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a)) : (3 : ℝ) / 2 ≤ a := by
  by_contra ha
  have hd : 0 < 3 - 2 * a := by linarith [lt_of_not_ge ha]
  have hsize : Tendsto (fun p : ℕ => 2 * p ^ 2) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro p
    exact (Nat.le_self_pow (by decide : 2 ≠ 0) p).trans
      (Nat.le_mul_of_pos_left _ (by decide))
  obtain ⟨C, hC⟩ := isBigO_iff.mp (hO.comp_tendsto hsize)
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ (3 - 2 * a)) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hprimes : ∃ᶠ p : ℕ in atTop, p.Prime :=
    frequently_atTop.mpr Nat.exists_infinite_primes
  obtain ⟨p, hp, hCp, hlarge⟩ :=
    (hprimes.and_eventually (hC.and (ht.eventually_gt_atTop (C * (2 : ℝ) ^ a)))).exists
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hupper : (extremalNumber (2 * p ^ 2) C4 : ℝ) ≤
      C * (2 * (p : ℝ) ^ 2) ^ a := by
    simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * (p : ℝ) ^ 2 by positivity) a)] using hCp
  have hlower : (p : ℝ) ^ 3 ≤ (extremalNumber (2 * p ^ 2) C4 : ℝ) := by
    exact_mod_cast prime_extremalNumber_lower p hp
  have hbound : (p : ℝ) ^ 3 ≤ (C * (2 : ℝ) ^ a) * (p : ℝ) ^ (2 * a) := by
    calc
      (p : ℝ) ^ 3 ≤ C * (2 * (p : ℝ) ^ 2) ^ a := hlower.trans hupper
      _ = (C * (2 : ℝ) ^ a) * (p : ℝ) ^ (2 * a) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (p : ℝ)),
          ← Real.rpow_natCast_mul hp'.le 2 a]
        simp only [Nat.cast_ofNat, mul_assoc]
  have hratio : (p : ℝ) ^ (3 - 2 * a) ≤ C * (2 : ℝ) ^ a := by
    rw [Real.rpow_sub hp', Real.rpow_ofNat]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hp' (2 * a))).mpr hbound
  exact (not_lt_of_ge hratio) hlarge

/-- Consequently, a positive power-law asymptotic for `ex(n,C4)` has exponent at least `3/2`.
This is a lower bound on the exponent, not the full rational-exponent conjecture. -/
theorem exponent_ge_three_halves_of_equivalent {a c : ℝ} (hc : 0 < c)
    (heq : (fun n : ℕ => (extremalNumber n C4 : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : (3 : ℝ) / 2 ≤ a :=
  exponent_ge_three_halves_of_isBigO (heq.isTheta.of_const_mul_right hc.ne').1

end Erdos713C4Lower
