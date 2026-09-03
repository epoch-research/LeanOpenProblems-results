import FormalConjecturesUtil

/-! Exact parity and counting lemmas for a two-terminal profile obstruction.
The graph-family construction and the completeness of the finite pattern lists
are documented and independently checked externally. This module proves the
stated algebraic implications, not the full graph-family theorem, and does not
settle Erdős 184. -/
namespace Erdos184.BoundaryProfileObstruction
open scoped BigOperators

/-- Intersections with the four marked edge types of the nine possible
internal-spanning terminal paths in the checked block. -/
def pathZ : Fin 9 → ℕ := ![0, 2, 2, 2, 4, 4, 2, 2, 4]

/-- The three spanning cycles using both terminals. -/
def terminalZ : Fin 3 → ℕ := ![2, 2, 4]

/-- The two spanning cycles avoiding both terminals. -/
def internalZ : Fin 2 → ℕ := ![3, 3]

lemma pathZ_even (i : Fin 9) : Even (pathZ i) := by
  have h : ∀ i : Fin 9, Even (pathZ i) := by decide
  exact h i

lemma terminalZ_even (i : Fin 3) : Even (terminalZ i) := by
  have h : ∀ i : Fin 3, Even (terminalZ i) := by decide
  exact h i

/-- Any integral use of the path and two-terminal patterns, together with
exactly one internal pattern, has odd marked-edge incidence. It therefore
cannot cover the block's even total six. The path multiplicities are arbitrary. -/
theorem no_saturated_profile
    (a : Fin 9 → ℕ) (u : Fin 3 → ℕ) (v : Fin 2 → ℕ)
    (hv : ∑ i, v i = 1)
    (hcover : (∑ i, a i * pathZ i) + (∑ i, u i * terminalZ i) +
      (∑ i, v i * internalZ i) = 6) : False := by
  have hp : Even (∑ i, a i * pathZ i) :=
    Finset.even_sum _ (fun i _ => (pathZ_even i).mul_left (a i))
  have ht : Even (∑ i, u i * terminalZ i) :=
    Finset.even_sum _ (fun i _ => (terminalZ_even i).mul_left (u i))
  have he := hp.add ht
  have hi : (∑ i, v i * internalZ i) = 3 := by
    have hh : ∀ i : Fin 2, internalZ i = 3 := by decide
    simp only [hh, ← Finset.sum_mul, hv, one_mul]
  rw [hi] at hcover
  rw [Nat.even_iff] at he
  omega

/-- The exact integer lower bound in a serial chain. Here `q` is the number
of global pieces, `a` counts pieces using two closing branches, and `c i`
counts pieces internal to block `i`. The exceptional saturated profile is
excluded by `hsaturated`; its graph interpretation is separate. -/
theorem serial_integer_lower {t p q a : ℕ} (c : Fin t → ℕ)
    (ht : 1 ≤ t) (hclosing : q + 2*a = p)
    (hdegree : ∀ i, p + 2 ≤ q + c i)
    (hsaturated : q = p → ∀ i, 3 ≤ c i) :
    p + 3*t ≤ q + a + ∑ i, c i := by
  by_cases ha : a = 0
  · have hqp : q = p := by omega
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => hsaturated hqp i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id] at hs
    omega
  · have ha' : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdegree i)
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
    have h1 : t ≤ a*t := by simpa using Nat.mul_le_mul_right t ha'
    have h2 : a ≤ a*t := by simpa using Nat.mul_le_mul_left a ht
    nlinarith

/-- The corresponding real lower bound needs only the degree inequalities;
there is no parity obstruction for fractional coefficients. -/
theorem serial_fractional_lower {t : ℕ} {p q a : ℝ} (c : Fin t → ℝ)
    (ht : 1 ≤ t) (ha : 0 ≤ a) (hclosing : q + 2*a = p)
    (hdegree : ∀ i, p + 2 ≤ q + c i) :
    p + 2*(t : ℝ) ≤ q + a + ∑ i, c i := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdegree i)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : a ≤ (t : ℝ)*a := by
    simpa using mul_le_mul_of_nonneg_right ht' ha
  have h2 : 0 ≤ (t : ℝ)*a := mul_nonneg (Nat.cast_nonneg _) ha
  nlinarith

/-- The series/parallel resistance formula is less than `3/b`. For `b≥6`
it is strictly below one half, regardless of the chain length. -/
theorem root_weight_bounds {b t R : ℝ} (hb : 6 ≤ b) (ht : 0 < t) (hR : 0 < R) :
    0 < 3*t*R / (3 + b*t*R) ∧
    3*t*R / (3 + b*t*R) < 3/b ∧ 3/b ≤ 1/2 := by
  have hb' : 0 < b := by linarith
  have hden : 0 < 3 + b*t*R := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_lt_div_iff₀ hden hb').2
    nlinarith
  · apply (div_le_iff₀ hb').2
    linarith

end Erdos184.BoundaryProfileObstruction
