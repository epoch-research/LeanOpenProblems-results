import FormalConjecturesUtil

/-!
A uniform obstruction to square-weight cubic norm graphs in characteristic three.
All fields of order 3^m with m >= 3 are covered.
This does not prove or disprove Erdős Problem 714.
-/

open scoped BigOperators
open SimpleGraph Polynomial

namespace Erdos714CharThreeNorm

variable {F : Type*} [Field F] [CharP F 3]

/-- Coordinate norm in the algebra with basis `1, θ, θ²`, where `θ³=θ+d`. -/
def normForm (d : F) (v : F × F × F) : F :=
  v.1 ^ 3 + 2 * v.1 ^ 2 * v.2.2 + v.1 * v.2.2 ^ 2 - v.1 * v.2.1 ^ 2 +
    d * v.2.1 ^ 3 - d * v.2.1 * v.2.2 ^ 2 -
    3 * d * v.1 * v.2.1 * v.2.2 + d ^ 2 * v.2.2 ^ 3

/-- The displayed cubic really is the determinant of the multiplication matrix. -/
theorem normForm_eq_det (d : F) (v : F × F × F) :
    normForm d v = Matrix.det
      !![v.1, d*v.2.2, d*v.2.1;
         v.2.1, v.1+v.2.2, v.2.1+d*v.2.2;
         v.2.2, v.2.1, v.1+v.2.2] := by
  rw [Matrix.det_fin_three]
  change normForm d v =
    v.1 * (v.1 + v.2.2) * (v.1 + v.2.2) - v.1 * (v.2.1 + d*v.2.2) * v.2.1 -
    (d*v.2.2) * v.2.1 * (v.1+v.2.2) + (d*v.2.2) * (v.2.1+d*v.2.2) * v.2.2 +
    (d*v.2.1) * v.2.1 * v.2.1 - (d*v.2.1) * (v.1+v.2.2) * v.2.2
  unfold normForm
  ring

@[simp] theorem normForm_plane (d x y : F) :
    normForm d (x, y, 0) = x ^ 3 - x * y ^ 2 + d * y ^ 3 := by
  simp [normForm]

/-- On the plane used below the norm is the product over the three conjugates. -/
theorem normForm_plane_conjugates (d x y theta : F)
    (htheta : theta ^ 3 - theta = d) :
    normForm d (x, y, 0) =
      (x + y * theta) * (x + y * (theta + 1)) * (x + y * (theta - 1)) := by
  have hc := add_pow_char (x) (y * theta) 3
  simp only [mul_pow] at hc
  rw [normForm_plane]
  calc
    x ^ 3 - x * y ^ 2 + d * y ^ 3 =
        (x + y * theta) ^ 3 - y ^ 2 * (x + y * theta) := by
      rw [hc, ← htheta]
      ring
    _ = _ := by ring

/-- The weighted bipartite graph in these norm coordinates. -/
def graph (d : F) : SimpleGraph (Bool × ((F × F × F) × Fˣ)) where
  Adj u v := u.1 ≠ v.1 ∧ normForm d (u.2.1 + v.2.1) = (u.2.2 : F) * (v.2.2 : F)
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro u h; exact h.1 rfl

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have : (1 : F) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

/-- All fields admit the following explicit configuration, provided the weights are nonzero. -/
theorem graph_not_free (c : F) (hc : c ≠ 0) (hd : -c ^ 3 - c ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (-c ^ 3 - c)) := by
  let d := -c ^ 3 - c
  let D : Fˣ := Units.mk0 d hd
  let B : Fˣ := Units.mk0 (-c ^ 3) (neg_ne_zero.mpr (pow_ne_zero 3 hc))
  let L : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(false, (0, 0, 0), 1), (false, (1, 0, 0), 1),
      (false, (-1, 0, 0), 1), (false, (0, 1, 0), -1)]
  let R : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(true, (0, 1, 0), D), (true, (1, 1, 0), D),
      (true, (-1, 1, 0), D), (true, (c, -1, 0), B)]
  have hL : Function.Injective L := by
    intro i j hij
    have hp := congrArg (fun v : Bool × ((F × F × F) × Fˣ) => v.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [L, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg (fun v : Bool × ((F × F × F) × Fˣ) => v.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [R, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h6 : (6 : F) = 0 := by linear_combination 2 * h3
  have h8 : (8 : F) = -1 := by linear_combination 3 * h3
  have hleft : ∀ i, (L i).1 = false := by intro i; fin_cases i <;> rfl
  have hright : ∀ i, (R i).1 = true := by intro i; fin_cases i <;> rfl
  have hp : (c + 1) ^ 3 = c ^ 3 + 1 := by simpa using add_pow_char c (1 : F) 3
  have hm : (c - 1) ^ 3 = c ^ 3 - 1 := by simpa using sub_pow_char c (1 : F)
  have hE : ∀ i j, (graph d).Adj (L i) (R j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L, R, graph, normForm, D, B, d, hp, hm,
        show (-1 : F) + c = c - 1 by ring, show (1 : F) + c = c + 1 by ring] <;>
      ring_nf <;> simp [h2, h3, h6, h8] <;> ring
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => simp at hab
      | inr j => exact hE i j
    | inr i =>
      cases b with
      | inl j => exact (hE j i).symm
      | inr j => simp at hab
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hL hab)
      | inr j =>
        have h : (L i).1 = (R j).1 := congrArg Prod.fst hab
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
    | inr i =>
      cases b with
      | inl j =>
        have h : (L j).1 = (R i).1 := (congrArg Prod.fst hab).symm
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
      | inr j => exact congrArg Sum.inr (hR hab)

/-- The Artin–Schreier map is not onto a finite characteristic-three field. -/
theorem exists_outside_artinSchreier [Finite F] : ∃ c : F, ∀ x : F, x ^ 3 - x ≠ c := by
  classical
  have hn : ¬ Function.Surjective (fun x : F => x ^ 3 - x) := by
    intro hs
    have hi := Finite.injective_iff_surjective.mpr hs
    have he : (0 : F) = 1 := hi (by simp)
    exact zero_ne_one he
  simpa only [Function.Surjective, not_forall, not_exists] using hn

/-- The chosen parameter gives an irreducible cubic, not a split or degenerate norm form. -/
theorem parameter_irreducible (c : F) (hc : ∀ x : F, x ^ 3 - x ≠ c) :
    c ≠ 0 ∧ -c ^ 3 - c ≠ 0 ∧
      Irreducible ((X ^ 3 - X - C (-c ^ 3 - c)) : F[X]) := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hroot : ∀ x : F, x ^ 3 - x ≠ -c ^ 3 - c := by
    intro x hx
    apply hc (x + c)
    rw [add_pow_char x c 3]
    linear_combination hx - c * h3
  have hc0 : c ≠ 0 := by
    intro h
    exact hc 0 (by simp [h])
  have hd0 : -c ^ 3 - c ≠ 0 := by
    intro h
    exact hroot 0 (by simp [h])
  refine ⟨hc0, hd0, ?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X ^ 3 - X - C (-c ^ 3 - c)) : F[X]).natDegree = 3 := by
      compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    apply hroot x
    simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hx

/-- Every finite characteristic-three field has this cubic-norm K_{4,4} obstruction. -/
theorem finite_char_three_obstruction [Finite F] :
    ∃ d : F, Irreducible ((X ^ 3 - X - C d) : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph d) := by
  obtain ⟨c, hc⟩ := exists_outside_artinSchreier (F := F)
  obtain ⟨hc0, hd0, hirr⟩ := parameter_irreducible c hc
  exact ⟨-c ^ 3 - c, hirr, graph_not_free c hc0 hd0⟩

#print axioms normForm_eq_det
#print axioms normForm_plane_conjugates
#print axioms graph_not_free
#print axioms finite_char_three_obstruction

end Erdos714CharThreeNorm


namespace Erdos714CharThreeSquare

private lemma power_bounds (m i : ℕ) (hm : 3 ≤ m) (hi : i < m) :
    27 ≤ 3 ^ m ∧ 3 ^ i ≤ 3 ^ (m - 1) ∧ 3 ^ m = 3 * 3 ^ (m - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (n := 3) (i := 3) (by omega) hm
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · have he : m = (m - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ, mul_comm]

/-- The positive exponents in the character sum have no nontrivial zero frequency. -/
lemma not_dvd_positive (m i : ℕ) (hm : 3 ≤ m) (hi0 : 0 < i) (hi : i < m) :
    ¬ (3 ^ m - 1) ∣ (4 * 3 ^ i - 4) := by
  obtain ⟨hq, hpi, hpow⟩ := power_bounds m i hm hi
  have hi3 : 3 ≤ 3 ^ i := Nat.pow_le_pow_right (n := 3) (i := 1) (by omega) hi0
  have hpos : 0 < 4 * 3 ^ i - 4 := by omega
  have hlt : 4 * 3 ^ i - 4 < 2 * (3 ^ m - 1) := by omega
  rintro ⟨k, hk⟩
  have hk1 : k = 1 := by
    have : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    nlinarith
  rw [hk1, mul_one] at hk
  have he : 4 * 3 ^ i = 3 ^ m + 3 := by omega
  by_cases hi1 : i = 1
  · rw [hi1] at he
    norm_num at he
    omega
  · have hi2 : 2 ≤ i := by omega
    have h9i : 9 ∣ 3 ^ i := Nat.pow_dvd_pow 3 hi2
    have h9m : 9 ∣ 3 ^ m := Nat.pow_dvd_pow (m := 2) (n := m) 3 (by omega)
    have hmi := Nat.mod_eq_zero_of_dvd h9i
    have hmm := Nat.mod_eq_zero_of_dvd h9m
    omega

/-- The negative exponents also avoid zero frequency. -/
lemma not_dvd_negative (m i : ℕ) (hm : 3 ≤ m) (hi : i < m) :
    ¬ (3 ^ m - 1) ∣ (4 * 3 ^ i + 4) := by
  obtain ⟨hq, hpi, hpow⟩ := power_bounds m i hm hi
  have hlt : 4 * 3 ^ i + 4 < 2 * (3 ^ m - 1) := by omega
  rintro ⟨k, hk⟩
  have hk1 : k = 1 := by
    have : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    nlinarith
  rw [hk1, mul_one] at hk
  have he : 4 * 3 ^ i + 5 = 3 ^ m := by omega
  by_cases hi0 : i = 0
  · rw [hi0] at he
    norm_num at he
    omega
  · have h3i : 3 ∣ 3 ^ i := Nat.pow_dvd_pow 3 (by omega : 1 ≤ i)
    have h3m : 3 ∣ 3 ^ m := Nat.pow_dvd_pow 3 (by omega : 1 ≤ m)
    have hmi := Nat.mod_eq_zero_of_dvd h3i
    have hmm := Nat.mod_eq_zero_of_dvd h3m
    omega

open Classical

section Fields

variable {F : Type*} [Field F] [CharP F 3] [Fintype F]

/-- The finite-field trace, expressed in the field itself. -/
def traceSum (m : ℕ) (x : F) : F := ∑ i ∈ Finset.range m, x ^ (3 ^ i)

lemma traceSum_artinSchreier (m : ℕ) (hcard : Fintype.card F = 3 ^ m) (x : F) :
    traceSum m (x ^ 3 - x) = 0 := by
  unfold traceSum
  simp_rw [sub_pow_char_pow]
  have ht : ∀ i : ℕ, (x ^ 3) ^ (3 ^ i) = x ^ (3 ^ (i + 1)) := by
    intro i
    rw [← pow_mul, pow_succ']
  simp_rw [ht]
  rw [Finset.sum_range_sub (fun i : ℕ => x ^ (3 ^ i)) m]
  simpa only [pow_zero, pow_one, ← hcard, FiniteField.pow_card, sub_self]

lemma sum_inv_pow (n : ℕ) :
    ∑ t : Fˣ, ((t : F)⁻¹) ^ n = ∑ t : Fˣ, (t : F) ^ n := by
  apply Fintype.sum_equiv (Equiv.inv Fˣ)
  intro t
  simp

private lemma weighted_term (t : Fˣ) (i : ℕ) :
    ((t : F)⁻¹) ^ 4 *
      ((t : F) ^ (4 * 3 ^ i) + ((t : F)⁻¹) ^ (4 * 3 ^ i) + 1) =
      (t : F) ^ (4 * 3 ^ i - 4) + ((t : F)⁻¹) ^ (4 * 3 ^ i + 4) +
        ((t : F)⁻¹) ^ 4 := by
  have hi : 4 ≤ 4 * 3 ^ i := by
    have h := Nat.one_le_pow i 3 (by omega)
    omega
  rw [pow_sub₀ (t : F) (Units.ne_zero t) hi, pow_add, inv_pow]
  ring

/-- Extracting one multiplicative character proves that this trace is not identically zero. -/
theorem weighted_trace_sum (m : ℕ) (hm : 3 ≤ m) (hcard : Fintype.card F = 3 ^ m) :
    ∑ t : Fˣ, ((t : F)⁻¹) ^ 4 *
      traceSum m ((t : F) ^ 4 + ((t : F)⁻¹) ^ 4 + 1) = -1 := by
  classical
  have hconst : ∑ t : Fˣ, ((t : F)⁻¹) ^ 4 = 0 := by
    rw [sum_inv_pow, FiniteField.sum_pow_units, hcard, if_neg]
    have hq : 27 ≤ 3 ^ m := (power_bounds m 0 hm (by omega)).1
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpos : ∀ i ∈ Finset.range m,
      (∑ t : Fˣ, (t : F) ^ (4 * 3 ^ i - 4)) = if i = 0 then -1 else 0 := by
    intro i hi
    rw [FiniteField.sum_pow_units, hcard]
    by_cases hi0 : i = 0
    · simp [hi0]
    · rw [if_neg hi0, if_neg (not_dvd_positive m i hm (by omega)
        (Finset.mem_range.mp hi))]
  have hneg : ∀ i ∈ Finset.range m,
      (∑ t : Fˣ, ((t : F)⁻¹) ^ (4 * 3 ^ i + 4)) = 0 := by
    intro i hi
    rw [sum_inv_pow, FiniteField.sum_pow_units, hcard,
      if_neg (not_dvd_negative m i hm (Finset.mem_range.mp hi))]
  calc
    _ = ∑ t : Fˣ, ∑ i ∈ Finset.range m,
        ((t : F)⁻¹) ^ 4 * ((t : F) ^ (4 * 3 ^ i) +
          ((t : F)⁻¹) ^ (4 * 3 ^ i) + 1) := by
      simp only [traceSum, Finset.mul_sum, add_pow_char_pow, one_pow, ← pow_mul]
    _ = ∑ i ∈ Finset.range m, ∑ t : Fˣ,
        ((t : F) ^ (4 * 3 ^ i - 4) + ((t : F)⁻¹) ^ (4 * 3 ^ i + 4) +
          ((t : F)⁻¹) ^ 4) := by
      simp_rw [weighted_term]
      exact Finset.sum_comm
    _ = ∑ i ∈ Finset.range m, (if i = 0 then (-1 : F) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hpos i hi, hneg i hi, hconst]
      simp
    _ = -1 := by simp [show 0 < m by omega]

/-- The rational expression is outside the Artin–Schreier image for some nonzero t. -/
theorem exists_parameter (m : ℕ) (hm : 3 ≤ m) (hcard : Fintype.card F = 3 ^ m) :
    ∃ t : Fˣ, ∀ x : F,
      x ^ 3 - x ≠ (t : F) ^ 4 + ((t : F)⁻¹) ^ 4 + 1 := by
  classical
  by_contra! h
  have hz : ∀ t : Fˣ, traceSum m ((t : F) ^ 4 + ((t : F)⁻¹) ^ 4 + 1) = 0 := by
    intro t
    obtain ⟨x, hx⟩ := h t
    rw [← hx]
    exact traceSum_artinSchreier m hcard x
  have he := weighted_trace_sum m hm hcard
  simp only [hz, mul_zero, Finset.sum_const_zero] at he
  exact neg_ne_zero.mpr one_ne_zero he.symm

/-- Parameters with both square conditions and an irreducible Artin–Schreier cubic. -/
theorem exists_square_parameter (m : ℕ) (hm : 3 ≤ m) (hcard : Fintype.card F = 3 ^ m) :
    ∃ u : F, u ≠ 0 ∧ u + 1 ≠ 0 ∧ IsSquare u ∧ IsSquare (u + 1) ∧
      ∀ x : F, x ^ 3 - x ≠ u ^ 2 * (u + 1) := by
  obtain ⟨t, ht⟩ := exists_parameter m hm hcard
  let a : F := t
  let b : F := (t : F)⁻¹
  let u : F := (a - b) ^ 2
  have hab : a * b = 1 := mul_inv_cancel₀ (Units.ne_zero t)
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hu : u + 1 = (a + b) ^ 2 := by
    dsimp only [u]
    linear_combination -4 * hab - h3
  have hg : u ^ 2 + u = a ^ 4 + b ^ 4 + 1 := by
    dsimp only [u]
    linear_combination -2 * (2*a^2 - 3*a*b + 2*b^2 - 2) * hab +
      (1-a^2-b^2) * h3
  have hune : u ≠ 0 := by
    intro hz
    apply ht 0
    change (0 : F) ^ 3 - 0 = a ^ 4 + b ^ 4 + 1
    simpa [hz] using hg
  have hupne : u + 1 ≠ 0 := by
    intro hz
    have hneg : u = -1 := eq_neg_of_add_eq_zero_left hz
    apply ht 0
    change (0 : F) ^ 3 - 0 = a ^ 4 + b ^ 4 + 1
    simpa [hneg] using hg
  refine ⟨u, hune, hupne, ⟨a-b, by dsimp [u]; ring⟩,
    ⟨a+b, by rw [hu]; ring⟩, ?_⟩
  intro x hx
  apply ht (x - u)
  change (x - u) ^ 3 - (x - u) = a ^ 4 + b ^ 4 + 1
  rw [sub_pow_char]
  linear_combination hx + hg

end Fields

#print axioms exists_square_parameter
#print axioms exists_parameter

end Erdos714CharThreeSquare

namespace Erdos714CharThreeNorm

open Classical

variable {F : Type*} [Field F] [CharP F 3]

/-- The genuine restriction of the norm graph to square weights. -/
def squareGraph (d : F) := (graph d).induce {v | IsSquare (v.2.2 : F)}

set_option maxHeartbeats 3000000 in
/-- A parametric K_{4,4} with all eight weights nonzero squares. -/
theorem square_graph_not_free (u : F) (hu : u ≠ 0) (hu1 : u + 1 ≠ 0)
    (hsu : IsSquare u) (hsu1 : IsSquare (u + 1)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (squareGraph (u ^ 2 * (u + 1))) := by
  let d := u ^ 2 * (u + 1)
  let v := -(u + 1)
  let a := (u + 1) / u
  let b := u * (u + 1) ^ 2
  have hd : d ≠ 0 := mul_ne_zero (pow_ne_zero 2 hu) hu1
  have ha : a ≠ 0 := div_ne_zero hu1 hu
  have hb : b ≠ 0 := mul_ne_zero hu (pow_ne_zero 2 hu1)
  have hsa : IsSquare a := hsu1.div hsu
  have hsd : IsSquare d := (IsSquare.sq u).mul hsu1
  have hsb : IsSquare b := hsu.mul (IsSquare.sq (u+1))
  let A : Fˣ := Units.mk0 a ha
  let D : Fˣ := Units.mk0 d hd
  let B : Fˣ := Units.mk0 b hb
  let L : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(false, (0, 0, 0), 1), (false, (1, 0, 0), 1),
      (false, (-1, 0, 0), 1), (false, (v, 1, 0), A)]
  let R : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(true, (0, 1, 0), D), (true, (1, 1, 0), D),
      (true, (-1, 1, 0), D), (true, (v, -1, 0), B)]
  have hL : Function.Injective L := by
    intro i j hij
    have hp := congrArg (fun z : Bool × ((F × F × F) × Fˣ) => z.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [L, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg (fun z : Bool × ((F × F × F) × Fˣ) => z.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [R, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hleft : ∀ i, (L i).1 = false := by intro i; fin_cases i <;> rfl
  have hright : ∀ i, (R i).1 = true := by intro i; fin_cases i <;> rfl
  have hSL : ∀ i, IsSquare ((L i).2.2 : F) := by
    have hsq1 : IsSquare (1 : F) := ⟨1, by ring⟩
    intro i; fin_cases i <;> first | exact hsq1 | exact hsa
  have hSR : ∀ i, IsSquare ((R i).2.2 : F) := by
    intro i; fin_cases i <;> first | exact hsd | exact hsb
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h6 : (6 : F) = 0 := by linear_combination 2*h3
  have h8 : (8 : F) = -1 := by linear_combination 3*h3
  have hAD : a * d = b := by dsimp [a,d,b]; field_simp <;> ring
  have hAB : a * b = (u+1)^3 := by dsimp [a,b]; field_simp <;> ring
  have hV : v^3-v-d = b := by
    dsimp [v,d,b]
    linear_combination -u*(u+1)^2*h3
  have hv2 : v+v = u+1 := by dsimp [v]; linear_combination -(u+1)*h3
  have hp : (v+1)^3 = v^3+1 := by simpa using add_pow_char v (1:F) 3
  have hm : (v-1)^3 = v^3-1 := by simpa using sub_pow_char v (1:F)
  have hE : ∀ i j, (graph d).Adj (L i) (R j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L,R,graph,normForm,A,D,B,hAD,hAB,hv2,hp,hm,
        show (-1:F)+v = v-1 by ring, show (1:F)+v=v+1 by ring] <;>
      ring_nf <;> (try simp [h2,h3,h6,h8]) <;>
      (first | (linear_combination hV) | (linear_combination hV + (u+1)*h3) | ring)
  let LL (i : Fin 4) : {z : Bool × ((F × F × F) × Fˣ) | IsSquare (z.2.2 : F)} :=
    ⟨L i, hSL i⟩
  let RR (i : Fin 4) : {z : Bool × ((F × F × F) × Fˣ) | IsSquare (z.2.2 : F)} :=
    ⟨R i, hSR i⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim LL RR, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => simp at hxy
      | inr j => exact hE i j
    | inr i =>
      cases y with
      | inl j => exact (hE j i).symm
      | inr j => simp at hxy
  · intro x y hxy
    have hval := congrArg Subtype.val hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hL hval)
      | inr j =>
        have h : (L i).1 = (R j).1 := congrArg Prod.fst hval
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
    | inr i =>
      cases y with
      | inl j =>
        have h : (L j).1 = (R i).1 := (congrArg Prod.fst hval).symm
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
      | inr j => exact congrArg Sum.inr (hR hval)

/-- Square weights do not rescue the cubic norm construction over any field of order 3^m, m>=3. -/
theorem finite_square_obstruction [Fintype F] (m : ℕ) (hm : 3 ≤ m)
    (hcard : Fintype.card F = 3 ^ m) :
    ∃ d : F, Irreducible ((X ^ 3 - X - C d) : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (squareGraph d) := by
  obtain ⟨u, hu, hu1, hsu, hsu1, hroot⟩ :=
    Erdos714CharThreeSquare.exists_square_parameter m hm hcard
  refine ⟨u ^ 2 * (u+1), ?_, square_graph_not_free u hu hu1 hsu hsu1⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X ^ 3 - X - C (u ^ 2 * (u+1))) : F[X]).natDegree = 3 := by
      compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    apply hroot x
    simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hx

#print axioms square_graph_not_free
#print axioms finite_square_obstruction

end Erdos714CharThreeNorm
