import Submission.FourthAverageDegree

/-! Transfer the fourth-case average-degree bound to actual extremal numbers. -/
noncomputable section
open Finset SimpleGraph Classical Filter
set_option maxHeartbeats 2000000
namespace Erdos714FourthUpper
open Erdos714Packing Erdos714FourthLocal

/-- The bipartite neighborhood double cover preserves the relevant freeness. -/
lemma neighborhood_incidence_free {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence (fun v => G.neighborFinset v)) := by
  exact (free_iff_common_card _ (by decide)).mpr (neighborhood_common_card G hfree)

/-- Natural fourth-root parameter form, with the factor of two for undirected edges. -/
theorem graph_bound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : Fintype.card V ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G) :
    2*G.edgeFinset.card ≤ (q^3+3*q^2+2)*Fintype.card V := by
  have h := average_degree_bound (fun v => G.neighborFinset v) q hq le_rfl
    (neighborhood_incidence_free G hfree)
  have hd (v : V) : dual (fun w => G.neighborFinset w) v = G.neighborFinset v := by
    ext w
    simp only [mem_dual, mem_neighborFinset, G.adj_comm]
  simp_rw [hd, card_neighborFinset_eq_degree] at h
  rwa [G.sum_degrees_eq_twice_card_edges] at h

/-- The same finite upper bound for the actual Mathlib extremal number. -/
theorem extremal_bound (n q : ℕ) (hq : n ≤ q^4) :
    2*extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) ≤
      (q^3+3*q^2+2)*n := by
  have hn : completeBipartiteGraph (Fin 4) (Fin 4) ≠ ⊥ := by
    intro h
    have he : (completeBipartiteGraph (Fin 4) (Fin 4)).Adj (.inl 0) (.inr 0) := by simp
    rw [h] at he
    exact he
  obtain ⟨G,inst,hG⟩ := exists_isExtremal_free (V := Fin n) hn
  have h := graph_bound G q (by simpa using hq) hG.prop
  rw [card_edgeFinset_of_isExtremal_free hG] at h
  simpa only [Fintype.card_fin] using h

/-- In particular the q⁴-order bound has leading coefficient one half. -/
theorem extremal_scaled_bound (q : ℕ) :
    2*extremalNumber (q^4) (completeBipartiteGraph (Fin 4) (Fin 4)) ≤
      q^7+3*q^6+2*q^4 := by
  have h := extremal_bound (q^4) q le_rfl
  (convert h using 1; ring)

/-- An explicit all-orders real bound; the error has strictly smaller exponent. -/
theorem extremal_real_bound (n : ℕ) :
    (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      (1/2 : ℝ)*(n : ℝ)^((7 : ℝ)/4) + 3*(n : ℝ)^((3 : ℝ)/2) +
      (9/2 : ℝ)*(n : ℝ)^((5 : ℝ)/4) + 3*(n : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let x : ℝ := (n : ℝ)^((1 : ℝ)/4)
  let q : ℕ := ⌈x⌉₊
  have hx : 0 ≤ x := Real.rpow_nonneg hn _
  have hpow (k : ℕ) : x^k = (n : ℝ)^((k : ℝ)/4) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hn]
    congr 1
    ring
  have hx4 : x^4 = (n : ℝ) := by simpa using hpow 4
  have hqx : x ≤ (q : ℝ) := Nat.le_ceil x
  have hq : n ≤ q^4 := by
    have h := pow_le_pow_left₀ hx hqx 4
    rw [hx4] at h
    exact_mod_cast h
  have hq' : (q : ℝ) ≤ x+1 := (Nat.ceil_lt_add_one hx).le
  have he : 2*(extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      ((q : ℝ)^3+3*(q : ℝ)^2+2)*(n : ℝ) := by exact_mod_cast extremal_bound n q hq
  have he' : 2*(extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      x^7+6*x^6+9*x^5+6*x^4 := by
    calc
      _ ≤ ((q : ℝ)^3+3*(q : ℝ)^2+2)*(n : ℝ) := he
      _ ≤ ((x+1)^3+3*(x+1)^2+2)*(n : ℝ) := by gcongr
      _ = _ := by rw [← hx4]; ring
  rw [hpow 7, hpow 6, hpow 5, hx4] at he'
  norm_num at he'
  linarith

/-- A two-term version retaining the leading constant one half. -/
theorem extremal_two_term_bound (n : ℕ) (hn : 1 ≤ n) :
    (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      (1/2 : ℝ)*(n : ℝ)^((7 : ℝ)/4) + (21/2 : ℝ)*(n : ℝ)^((3 : ℝ)/2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : (n : ℝ)^((5 : ℝ)/4) ≤ (n : ℝ)^((3 : ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  have h₂ : (n : ℝ) ≤ (n : ℝ)^((3 : ℝ)/2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (show (1 : ℝ) ≤ 3/2 by norm_num)
  have h := extremal_real_bound n
  linarith

/-- Any eventual lower-bound constant in the fourth instance is at most one half.
This restricts the constant only; it does not rule out a positive constant. -/
theorem lower_constant_le_half (c : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^((7 : ℝ)/4) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ)) :
    c ≤ 1/2 := by
  by_contra! hc
  have hd : 0 < 2*c-1 := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨q,hq⟩ := exists_nat_gt (max (N : ℝ) (max 1 (5/(2*c-1))))
  have hq1 : (1 : ℝ) < q := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hq)
  have hq0 : 0 < q := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hq1)
  have hqN : N ≤ q := by
    have hn : (N : ℝ) < q := (le_max_left _ _).trans_lt hq
    exact_mod_cast hn.le
  have hqL : 5/(2*c-1) < (q : ℝ) :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hq)
  have hnq : N ≤ q^4 := hqN.trans (by
    simpa only [pow_one] using pow_le_pow_right' (show 1 ≤ q by omega) (show 1 ≤ 4 by decide))
  have hlo := hN (q^4) hnq
  have hp : ((q^4 : ℕ) : ℝ)^((7 : ℝ)/4) = (q : ℝ)^7 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  rw [hp] at hlo
  have hup : 2*(extremalNumber (q^4) (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      (q : ℝ)^7+3*(q : ℝ)^6+2*(q : ℝ)^4 := by exact_mod_cast extremal_scaled_bound q
  have hpow : (q : ℝ)^4 ≤ (q : ℝ)^6 := pow_le_pow_right₀ hq1.le (by decide)
  have hmul : ((2*c-1)*(q : ℝ))*(q : ℝ)^6 ≤ 5*(q : ℝ)^6 := by
    have heq : (q : ℝ)^7 = (q : ℝ)*(q : ℝ)^6 := by ring
    nlinarith
  have hsmall := (mul_le_mul_iff_left₀ (pow_pos (show (0 : ℝ) < q by exact_mod_cast hq0) 6)).mp
    hmul
  have hlarge : 5 < (2*c-1)*(q : ℝ) := by
    have hh := (div_lt_iff₀ hd).mp hqL
    nlinarith
  linarith

#print axioms lower_constant_le_half
#print axioms extremal_real_bound
#print axioms extremal_two_term_bound
#print axioms neighborhood_incidence_free
#print axioms graph_bound
#print axioms extremal_bound
#print axioms extremal_scaled_bound
end Erdos714FourthUpper
