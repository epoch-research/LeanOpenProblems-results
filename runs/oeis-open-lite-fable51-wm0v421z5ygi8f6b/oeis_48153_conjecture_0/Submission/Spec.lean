import FormalConjectures.Util.ProblemImports

open Finset

/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}$.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

section Schur1Sec

open Complex Finset Matrix

namespace GaussSchur

variable {N : ℕ} [NeZero N]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-- The DFT-type matrix. -/
noncomputable def A (m : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ := fun j k => ψ (m * j * k)

/-- Permutation matrix of negation. -/
noncomputable def P : Matrix (ZMod N) (ZMod N) ℂ := fun j k => if j + k = 0 then 1 else 0

lemma A_mul_A (u : (ZMod N)ˣ) : A (u : ZMod N) * A (u : ZMod N) = (N : ℂ) • P := by
  ext j k
  simp only [mul_apply, A, smul_apply, P, smul_eq_mul]
  have h : ∀ l, ψ (u * j * l) * ψ (u * l * k) = ψ (l * (u * (j + k))) := by
    intro l; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp_rw [h]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp only [ZMod.card, Units.mul_right_eq_zero]
  split_ifs <;> simp

lemma P_mul_P : (P : Matrix (ZMod N) (ZMod N) ℂ) * P = 1 := by
  ext j k
  simp only [mul_apply, P, one_apply]
  rw [Finset.sum_eq_single (-j)]
  · simp only [add_neg_cancel, if_true, one_mul]
    by_cases h : j = k
    · subst h; simp
    · have : ¬ (-j + k = 0) := fun h' => h (by linear_combination -h')
      simp [h, this]
  · intro l _ hl
    have : ¬ (j + l = 0) := fun h => hl (by linear_combination h)
    simp [this]
  · simp

lemma trace_A (m : ZMod N) : (A m).trace = ∑ j : ZMod N, ψ (m * j ^ 2) := by
  simp only [trace, Matrix.diag, A]
  congr 1; ext j; ring_nf

lemma isUnit_two (hN : Odd N) : IsUnit (2 : ZMod N) := by
  have : ((2 : ℕ) : ZMod N) = 2 := by norm_num
  rw [← this, ZMod.isUnit_iff_coprime]
  exact Nat.coprime_two_left.mpr hN

lemma trace_P (hN : Odd N) : (P : Matrix (ZMod N) (ZMod N) ℂ).trace = 1 := by
  simp only [trace, Matrix.diag]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp [P]
  · intro j _ hj
    have h2 := isUnit_two (N := N) hN
    have : ¬ (j + j = 0) := by
      intro h
      apply hj
      have : (2 : ZMod N) * j = 0 := by linear_combination h
      exact (h2.mul_right_eq_zero).mp this
    simp [P, this]
  · simp

lemma trace_A_mul_A (hN : Odd N) (u : (ZMod N)ˣ) :
    (A (u : ZMod N) * A (u : ZMod N)).trace = N := by
  rw [A_mul_A, trace_smul, trace_P hN, smul_eq_mul, mul_one]

lemma A_pow_four (u : (ZMod N)ˣ) :
    (A (u : ZMod N)) ^ 4 = ((N : ℂ) ^ 2) • (1 : Matrix (ZMod N) (ZMod N) ℂ) := by
  have h : (A (u : ZMod N)) ^ 4 = (A u * A u) * (A u * A u) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h, A_mul_A, smul_mul_smul_comm, P_mul_P, pow_two]

end GaussSchur

end Schur1Sec

section Schur2Sec

open Complex Finset Matrix

namespace GaussSchur

variable {N : ℕ} [NeZero N]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

lemma conj_stdAddChar (x : ZMod N) : (starRingEnd ℂ) (ψ x) = ψ (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
    AddChar.map_neg_eq_inv]

lemma g_mul_conj_g (hN : Odd N) (u : (ZMod N)ˣ) :
    (∑ j : ZMod N, ψ ((u : ZMod N) * j ^ 2)) * (starRingEnd ℂ) (∑ j : ZMod N, ψ ((u : ZMod N) * j ^ 2))
      = N := by
  rw [map_sum, Finset.sum_mul_sum]
  simp_rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
  -- ∑ j, ∑ k, ψ (u j² + -(u k²))
  have h1 : ∀ k : ZMod N, ∑ j : ZMod N, ψ ((u : ZMod N) * j ^ 2 + -((u : ZMod N) * k ^ 2))
      = ∑ j : ZMod N, ψ ((u : ZMod N) * j ^ 2) * ψ (k * (2 * (u : ZMod N) * j)) := by
    intro k
    refine (Fintype.sum_equiv (Equiv.addRight k) _ _ ?_).symm
    intro j
    rw [← AddChar.map_add_eq_mul]; congr 1
    simp only [Equiv.coe_addRight]; ring
  rw [Finset.sum_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp
  · intro j _ hj
    have h2 := isUnit_two (N := N) hN
    have : ¬ (2 * (u : ZMod N) * j = 0) := by
      intro h
      apply hj
      have hu : IsUnit (2 * (u : ZMod N)) := h2.mul u.isUnit
      exact (hu.mul_right_eq_zero).mp h
    simp [this]
  · simp

end GaussSchur

end Schur2Sec

section Schur3Sec

open Complex Finset Matrix

namespace GaussSchur

variable {N : ℕ} [NeZero N]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-- the equivalence `Fin N ≃ ZMod N` given by casting. -/
def finZMod : Fin N ≃ ZMod N where
  toFun i := ((i : ℕ) : ZMod N)
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv i := by
    ext; simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv x := by simp

lemma finZMod_apply (i : Fin N) : finZMod i = ((i : ℕ) : ZMod N) := rfl

lemma stdAddChar_mul_eq_pow (x : ZMod N) (i : Fin N) :
    ψ (x * finZMod i) = ψ x ^ (i : ℕ) := by
  rw [← AddChar.map_nsmul_eq_pow, finZMod_apply, nsmul_eq_mul, mul_comm]

lemma A_one_eq_reindex :
    A (1 : ZMod N) = Matrix.reindex finZMod finZMod (vandermonde fun i : Fin N => ψ (finZMod i)) := by
  ext j k
  simp only [A, reindex_apply, submatrix_apply, vandermonde_apply, one_mul]
  rw [← stdAddChar_mul_eq_pow]
  simp

lemma det_A_one :
    (A (1 : ZMod N)).det = ∏ i : Fin N, ∏ j ∈ Ioi i, (ψ (finZMod j) - ψ (finZMod i)) := by
  rw [A_one_eq_reindex, det_reindex_self, det_vandermonde]

lemma A_eq_submatrix (u : (ZMod N)ˣ) :
    A (u : ZMod N) = (A 1).submatrix (MulAction.toPerm u) id := by
  ext j k
  simp [A, MulAction.toPerm_apply, Units.smul_def]

lemma det_A (u : (ZMod N)ˣ) :
    (A (u : ZMod N)).det =
      ((Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod N)) : ℤ) : ℂ) * (A (1 : ZMod N)).det := by
  rw [A_eq_submatrix, det_permute]

end GaussSchur

end Schur3Sec

section Schur4Sec

open Complex Finset
open scoped Real

namespace GaussSchur

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- factorization of a difference of two roots of unity -/
lemma root_diff (i j : ℕ) :
    exp (2 * π * I * j / N) - exp (2 * π * I * i / N)
      = exp (π * I * (i + j) / N) * (2 * I * ((Real.sin (π * ((j : ℝ) - i) / N) : ℝ) : ℂ)) := by
  have h1 : (2 * π * I * j / N : ℂ) = π * I * (i + j) / N + I * (π * (j - i) / N) := by ring
  have h2 : (2 * π * I * i / N : ℂ) = π * I * (i + j) / N + -(I * (π * (j - i) / N)) := by ring
  rw [h1, h2, exp_add, exp_add, ← mul_sub]
  congr 1
  rw [Complex.ofReal_sin]
  push_cast
  rw [Complex.sin, mul_comm I (_ / _), neg_mul]
  ring_nf
  rw [I_sq]
  ring

omit [NeZero N] in
lemma sum_Ioi_card : ∑ i : Fin N, (Ioi i).card = N * (N - 1) / 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  rw [← Finset.sum_range_id]
  rw [← Finset.sum_range_reflect (fun i => i) N]

omit [NeZero N] in
/-- `S = ∑_{i<j} (i + j) = (N-1) * ∑ i`. -/
lemma sum_pairs : ∑ i : Fin N, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) = (N - 1) * (N * (N - 1) / 2) := by
  simp_rw [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin N, ∑ j ∈ Ioi i, (i : ℕ) = ∑ i : Fin N, (i : ℕ) * (N - 1 - i) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_const, Fin.card_Ioi, smul_eq_mul, mul_comm]
  have h2 : ∑ i : Fin N, ∑ j ∈ Ioi i, (j : ℕ) = ∑ j : Fin N, (j : ℕ) * (j : ℕ) := by
    rw [Finset.sum_comm' (s' := fun j => Iio j) (t' := univ)]
    · apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_const, Fin.card_Iio, smul_eq_mul, mul_comm]
    · intro i j; simp [Finset.mem_Ioi, Finset.mem_Iio]
  rw [h1, h2, ← Finset.sum_add_distrib]
  have h3 : ∀ i : Fin N, (i : ℕ) * (N - 1 - i) + (i : ℕ) * (i : ℕ) = (N - 1) * (i : ℕ) := by
    intro i
    have := i.isLt
    rw [← mul_add, Nat.sub_add_cancel (by omega), mul_comm]
  simp_rw [h3]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

end GaussSchur

end Schur4Sec

section Schur5Sec

open Complex Finset
open scoped Real

namespace GaussSchur

variable {N : ℕ} [NeZero N]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

lemma stdAddChar_finZMod (i : Fin N) : ψ (finZMod i) = exp (2 * π * I * i / N) := by
  rw [finZMod_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]

lemma sin_pos_of_lt (i j : Fin N) (hij : i < j) :
    0 < Real.sin (π * ((j : ℝ) - i) / N) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h1 : (i : ℝ) < j := by exact_mod_cast (Fin.lt_def.mp hij)
  have h2 : (j : ℝ) < N := by exact_mod_cast j.isLt
  have h3 : (0 : ℝ) ≤ i := by positivity
  apply Real.sin_pos_of_pos_of_lt_pi
  · have : 0 < (j : ℝ) - i := by linarith
    positivity
  · rw [mul_div_assoc]
    apply mul_lt_of_lt_one_right Real.pi_pos
    rw [div_lt_one hN]
    linarith

lemma exp_phase_eq_one (hN : Odd N) :
    exp (∑ i : Fin N, ∑ j ∈ Ioi i, (π * I * ((i : ℕ) + (j : ℕ)) / N : ℂ)) = 1 := by
  obtain ⟨h, hh⟩ := hN
  have e0 : ∑ i : Fin N, ∑ j ∈ Ioi i, (π * I * ((i : ℕ) + (j : ℕ)) / N : ℂ)
      = π * I / N * ((∑ i : Fin N, ∑ j ∈ Ioi i, ((i : ℕ) + (j : ℕ)) : ℕ) : ℂ) := by
    push_cast
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e1 : N * (N - 1) / 2 = N * h := by
    rw [hh, Nat.add_sub_cancel, show (2 * h + 1) * (2 * h) = ((2 * h + 1) * h) * 2 by ring,
      Nat.mul_div_cancel _ two_pos]
  have e2 : (N - 1) * (N * (N - 1) / 2) = N * (2 * h ^ 2) := by
    rw [e1, hh, Nat.add_sub_cancel]; ring
  rw [e0, sum_pairs, e2]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have : (π * I / N * ((N * (2 * h ^ 2) : ℕ) : ℂ)) = ((h ^ 2 : ℕ) : ℂ) * (2 * π * I) := by
    push_cast; field_simp
  rw [this, Complex.exp_nat_mul_two_pi_mul_I]

lemma det_A_one_phase (hN : Odd N) :
    ∃ r : ℝ, 0 < r ∧ (A (1 : ZMod N)).det = I ^ (N * (N - 1) / 2) * r := by
  refine ⟨2 ^ (N * (N - 1) / 2) * ∏ i : Fin N, ∏ j ∈ Ioi i, Real.sin (π * ((j : ℝ) - i) / N), ?_, ?_⟩
  · apply mul_pos (by positivity)
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro j hj
    exact sin_pos_of_lt i j (Finset.mem_Ioi.mp hj)
  rw [det_A_one]
  simp_rw [stdAddChar_finZMod, root_diff, Finset.prod_mul_distrib, ← Complex.exp_sum,
    Finset.prod_const, Finset.prod_pow_eq_pow_sum, sum_Ioi_card]
  rw [exp_phase_eq_one hN, one_mul]
  push_cast
  ring

end GaussSchur

end Schur5Sec

section Schur6Sec

open Polynomial Matrix

namespace GaussSchur

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma mapMatrix_charmatrix_comp (M : Matrix n n ℂ) (q : ℂ[X]) :
    (compRingHom q).mapMatrix (charmatrix M) = scalar n q - (C : ℂ →+* ℂ[X]).mapMatrix M := by
  ext i j
  by_cases h : i = j
  · subst h; simp [charmatrix_apply_eq]
  · simp [h]

lemma charpoly_comp (M : Matrix n n ℂ) (q : ℂ[X]) :
    M.charpoly.comp q = (scalar n q - (C : ℂ →+* ℂ[X]).mapMatrix M).det := by
  have : M.charpoly.comp q = compRingHom q M.charpoly := rfl
  rw [this, Matrix.charpoly, RingHom.map_det, mapMatrix_charmatrix_comp]

lemma charpoly_mul_self_comp (M : Matrix n n ℂ) :
    (M * M).charpoly.comp (X ^ 2) = (-1) ^ Fintype.card n * (M.charpoly * M.charpoly.comp (-X)) := by
  rw [charpoly_comp, charpoly_comp, map_mul, Matrix.charpoly]
  have hcomm : Commute (scalar n (X : ℂ[X])) ((C : ℂ →+* ℂ[X]).mapMatrix M) :=
    scalar_commute _ (fun r' => Commute.all _ _) _
  have e1 : scalar n (X ^ 2 : ℂ[X]) - (C : ℂ →+* ℂ[X]).mapMatrix M * (C : ℂ →+* ℂ[X]).mapMatrix M
      = charmatrix M * (scalar n X + (C : ℂ →+* ℂ[X]).mapMatrix M) := by
    rw [charmatrix, sub_mul, mul_add, mul_add, hcomm.eq, map_pow, pow_two]
    abel
  have e2 : scalar n (-X : ℂ[X]) - (C : ℂ →+* ℂ[X]).mapMatrix M
      = -(scalar n X + (C : ℂ →+* ℂ[X]).mapMatrix M) := by
    rw [map_neg]; abel
  rw [e1, det_mul, e2, det_neg, ← mul_assoc, mul_comm ((-1 : ℂ[X]) ^ _), mul_assoc,
    ← mul_assoc ((-1 : ℂ[X]) ^ _), ← pow_two, ← pow_mul, pow_mul', neg_one_sq, one_pow,
    one_mul]

lemma prod_X_sub_C_sq_comp (R : Multiset ℂ) :
    ((R.map (fun l => l ^ 2)).map (fun a => X - C a)).prod.comp (X ^ 2)
      = (-1) ^ Multiset.card R * ((R.map (fun a => X - C a)).prod
          * (R.map (fun a => X - C a)).prod.comp (-X)) := by
  rw [multiset_prod_comp, multiset_prod_comp, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  have : ∀ a : ℂ, (X - C (a ^ 2)).comp (X ^ 2) = (-1) * ((X - C a) * (X - C a).comp (-X)) := by
    intro a; simp only [sub_comp, X_comp, C_comp, map_pow, pow_comp]; ring
  simp only [Function.comp_def, this]
  rw [Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]

theorem charpoly_mul_self (M : Matrix n n ℂ) :
    (M * M).charpoly = ((M.charpoly.roots.map (fun l => l ^ 2)).map (fun a => X - C a)).prod := by
  apply expand_injective (R := ℂ) (n := 2) two_pos
  rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow, charpoly_mul_self_comp, prod_X_sub_C_sq_comp]
  have hs := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic M.charpoly_monic
  rw [← hs]
  congr 2
  rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim]

theorem trace_mul_self_eq_sum_sq_roots (M : Matrix n n ℂ) :
    (M * M).trace = (M.charpoly.roots.map (fun l => l ^ 2)).sum := by
  rw [trace_eq_sum_roots_charpoly, charpoly_mul_self, roots_multiset_prod_X_sub_C]

end GaussSchur

end Schur6Sec

section Schur7Sec

open Complex

namespace GaussSchur

lemma exists_counts (R : Multiset ℂ) (x₀ x₁ x₂ x₃ : ℂ)
    (h : ∀ l ∈ R, l = x₀ ∨ l = x₁ ∨ l = x₂ ∨ l = x₃) :
    ∃ a b c d : ℕ, a + b + c + d = Multiset.card R ∧
      (∀ f : ℂ → ℂ, (R.map f).sum = a * f x₀ + b * f x₁ + c * f x₂ + d * f x₃) ∧
      (∀ f : ℂ → ℂ, (R.map f).prod = f x₀ ^ a * f x₁ ^ b * f x₂ ^ c * f x₃ ^ d) := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨0, 0, 0, 0, by simp, by simp, by simp⟩
  | cons l R ih =>
    obtain ⟨a, b, c, d, h1, h2, h3⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have hl := h l (Multiset.mem_cons_self l R)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons, Multiset.card_cons]
    rcases hl with rfl | rfl | rfl | rfl
    · refine ⟨a + 1, b, c, d, by omega, fun f => ?_, fun f => ?_⟩
      · rw [h2]; push_cast; ring
      · rw [h3]; ring
    · refine ⟨a, b + 1, c, d, by omega, fun f => ?_, fun f => ?_⟩
      · rw [h2]; push_cast; ring
      · rw [h3]; ring
    · refine ⟨a, b, c + 1, d, by omega, fun f => ?_, fun f => ?_⟩
      · rw [h2]; push_cast; ring
      · rw [h3]; ring
    · refine ⟨a, b, c, d + 1, by omega, fun f => ?_, fun f => ?_⟩
      · rw [h2]; push_cast; ring
      · rw [h3]; ring

lemma I_pow_mod (m : ℕ) : I ^ m = I ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, I_pow_four, one_pow, one_mul]

lemma sq_add_sq_eq_one_cases (α β : ℤ) (h : α ^ 2 + β ^ 2 = 1) :
    (α = 1 ∧ β = 0) ∨ (α = -1 ∧ β = 0) ∨ (α = 0 ∧ β = 1) ∨ (α = 0 ∧ β = -1) := by
  have h1 : α ≤ 1 := by nlinarith [sq_nonneg β, sq_nonneg α]
  have h2 : -1 ≤ α := by nlinarith [sq_nonneg β, sq_nonneg α]
  have h3 : β ≤ 1 := by nlinarith [sq_nonneg β, sq_nonneg α]
  have h4 : -1 ≤ β := by nlinarith [sq_nonneg β, sq_nonneg α]
  interval_cases α <;> interval_cases β <;> simp_all

/-- The final arithmetic step of Schur's argument. -/
lemma final_arith (h a b c d : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (h1 : a + b + c + d = 2 * h + 1) (h2 : (a : ℤ) + b - c - d = 1)
    (h3 : ((a : ℤ) - b) ^ 2 + ((c : ℤ) - d) ^ 2 = 1)
    (h4 : I ^ (2 * b + c + 3 * d) = (σ : ℂ) * I ^ ((2 * h + 1) * h)) :
    (h % 2 = 0 → c = d ∧ (a : ℤ) - b = σ) ∧ (h % 2 = 1 → a = b ∧ (c : ℤ) - d = σ) := by
  rw [I_pow_mod (2 * b + c + 3 * d), I_pow_mod ((2 * h + 1) * h), Nat.mul_mod] at h4
  obtain ⟨w, hw, hw'⟩ : ∃ w, w < 4 ∧ h % 4 = w := ⟨h % 4, Nat.mod_lt _ (by norm_num), rfl⟩
  have hw2 : (2 * h + 1) % 4 = (2 * w + 1) % 4 := by omega
  rw [hw2, hw'] at h4
  rcases sq_add_sq_eq_one_cases _ _ h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
  rcases hσ with rfl | rfl <;>
  interval_cases w <;>
  · first
    | (rw [show (2 * b + c + 3 * d) % 4 = 0 by omega] at h4)
    | (rw [show (2 * b + c + 3 * d) % 4 = 1 by omega] at h4)
    | (rw [show (2 * b + c + 3 * d) % 4 = 2 by omega] at h4)
    | (rw [show (2 * b + c + 3 * d) % 4 = 3 by omega] at h4)
    (norm_num [Complex.ext_iff] at h4) <;> omega

end GaussSchur

end Schur7Sec

section Schur8Sec

open Complex Finset Matrix Polynomial

namespace GaussSchur

variable {N : ℕ} [NeZero N]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

lemma roots_pow_four (u : (ZMod N)ˣ) (l : ℂ) (hl : l ∈ (A (u : ZMod N)).charpoly.roots) :
    l ^ 4 = (N : ℂ) ^ 2 := by
  have h1 : l ∈ spectrum ℂ (A (u : ZMod N)) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hl
  have h2 := spectrum.subset_polynomial_aeval (A (u : ZMod N)) (X ^ 4 : ℂ[X]) ⟨l, h1, rfl⟩
  simp only [eval_pow, eval_X, map_pow, aeval_X] at h2
  rw [A_pow_four, ← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq] at h2
  exact h2

lemma root_cases (u : (ZMod N)ˣ) (l : ℂ) (hl : l ∈ (A (u : ZMod N)).charpoly.roots) :
    l = (Real.sqrt N : ℂ) ∨ l = -(Real.sqrt N : ℂ) ∨ l = I * (Real.sqrt N : ℂ) ∨
      l = -(I * (Real.sqrt N : ℂ)) := by
  have h4 := roots_pow_four u l hl
  have hs : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = N := by
    rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  set s : ℂ := ((Real.sqrt N : ℝ) : ℂ)
  have : (l - s) * (l + s) * ((l - I * s) * (l + I * s)) = 0 := by
    have : (l - s) * (l + s) * ((l - I * s) * (l + I * s)) = l ^ 4 - (s ^ 2) ^ 2 := by
      ring_nf; rw [I_sq]; ring
    rw [this, h4, hs]; ring
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · left; linear_combination h
    · right; left; linear_combination h
  · rcases mul_eq_zero.mp h with h | h
    · right; right; left; linear_combination h
    · right; right; right; linear_combination h

theorem gauss_sum_odd (hN : Odd N) (u : (ZMod N)ˣ) :
    ∑ j : ZMod N, ψ ((u : ZMod N) * j ^ 2) =
      ((Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod N)) : ℤ) : ℂ) *
        (if N % 4 = 1 then 1 else I) * (Real.sqrt N : ℂ) := by
  obtain ⟨h, hh⟩ := hN
  set M := A (u : ZMod N) with hM
  set R := M.charpoly.roots with hR
  set σ : ℤ := (Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod N)) : ℤ) with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod N))) with
      e | e <;> simp [hσdef, e]
  set g := ∑ j : ZMod N, ψ ((u : ZMod N) * j ^ 2) with hg
  have hsR : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  set s : ℂ := ((Real.sqrt N : ℝ) : ℂ) with hsdef
  have hs : s ^ 2 = N := by
    rw [hsdef, ← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  have hs0 : s ≠ 0 := by rw [hsdef]; exact_mod_cast hsR.ne'
  have hcard : Multiset.card R = N := by
    rw [hR, ← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim,
      ZMod.card]
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := exists_counts R s (-s) (I * s) (-(I * s)) (root_cases u)
  rw [hcard] at h1
  -- trace
  have hsum : g = a * s + b * (-s) + c * (I * s) + d * (-(I * s)) := by
    have := h2 id
    rw [Multiset.map_id, hR, ← trace_eq_sum_roots_charpoly, hM, trace_A] at this
    simpa using this
  -- trace of square
  have hsq : (N : ℂ) = (a + b - c - d) * N := by
    have := h2 (fun l => l ^ 2)
    rw [hR, ← trace_mul_self_eq_sum_sq_roots, hM, trace_A_mul_A ⟨h, hh⟩] at this
    simp only [mul_pow, I_sq, neg_sq] at this
    linear_combination this + ((a : ℂ) + b - c - d) * hs
  have h2' : (a : ℤ) + b - c - d = 1 := by
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have : ((a : ℤ) + b - c - d : ℂ) = 1 := by
      push_cast
      exact (mul_eq_right₀ hN0).mp hsq.symm
    exact_mod_cast this
  -- absolute value
  have h3' : ((a : ℤ) - b) ^ 2 + ((c : ℤ) - d) ^ 2 = 1 := by
    have e := g_mul_conj_g ⟨h, hh⟩ u
    rw [← hg, hsum] at e
    have hsr : (starRingEnd ℂ) s = s := by rw [hsdef, conj_ofReal]
    simp only [map_add, map_mul, map_neg, map_natCast, conj_I, hsr] at e
    have : ((((a : ℤ) - b) ^ 2 + ((c : ℤ) - d) ^ 2 : ℤ) : ℂ) * N = 1 * N := by
      push_cast
      linear_combination e - (((a : ℂ) - b) ^ 2 + ((c : ℂ) - d) ^ 2) * hs + ((c : ℂ) - d) ^ 2 * s ^ 2 * I_sq
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    exact_mod_cast mul_right_cancel₀ hN0 this
  -- determinant
  obtain ⟨r, hr, hdet⟩ := det_A_one_phase (N := N) ⟨h, hh⟩
  have hE : N * (N - 1) / 2 = (2 * h + 1) * h := by
    rw [hh, Nat.add_sub_cancel, show (2 * h + 1) * (2 * h) = ((2 * h + 1) * h) * 2 by ring,
      Nat.mul_div_cancel _ two_pos]
  have hprod : s ^ a * (-s) ^ b * (I * s) ^ c * (-(I * s)) ^ d = σ * (I ^ ((2 * h + 1) * h) * r) := by
    have := h3 id
    rw [Multiset.map_id, hR, ← det_eq_prod_roots_charpoly, hM, det_A, hdet, hE] at this
    simpa using this.symm
  have hprod' : s ^ N * I ^ (2 * b + c + 3 * d) = σ * (I ^ ((2 * h + 1) * h) * r) := by
    rw [← hprod, ← h1]
    have e1 : (-s) ^ b = s ^ b * I ^ (2 * b) := by
      rw [pow_mul, I_sq, neg_pow]; ring
    have e2 : (-(I * s)) ^ d = s ^ d * I ^ (3 * d) := by
      rw [pow_mul, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring, neg_pow, mul_pow]; ring
    rw [e1, e2, mul_pow]; ring
  have hr' : (r : ℂ) = s ^ N := by
    have := congrArg norm hprod'
    simp only [norm_mul, norm_pow, norm_I, one_pow, mul_one, norm_intCast, norm_real] at this
    rw [hsdef, norm_real, Real.norm_of_nonneg hsR.le, Real.norm_of_nonneg hr.le, one_mul] at this
    rw [hsdef, ← ofReal_pow, this]
    rcases hσ with e | e <;> simp [e]
  have h4 : I ^ (2 * b + c + 3 * d) = (σ : ℂ) * I ^ ((2 * h + 1) * h) := by
    have hsN : s ^ N ≠ 0 := pow_ne_zero _ hs0
    rw [hr'] at hprod'
    apply mul_left_cancel₀ hsN
    rw [hprod']; ring
  obtain ⟨k1, k2⟩ := final_arith h a b c d σ hσ (hh ▸ h1) h2' h3' h4
  rw [hsum]
  rcases Nat.even_or_odd h with he | ho
  · obtain ⟨hcd, hab⟩ := k1 (Nat.even_iff.mp he)
    have : N % 4 = 1 := by omega
    rw [if_pos this, hcd]
    have : ((a : ℤ) : ℂ) - b = σ := by exact_mod_cast hab
    push_cast at this
    linear_combination s * this
  · obtain ⟨hab, hcd⟩ := k2 (Nat.odd_iff.mp ho)
    have : ¬ N % 4 = 1 := by omega
    rw [if_neg this, hab]
    have : ((c : ℤ) : ℂ) - d = σ := by exact_mod_cast hcd
    push_cast at this
    linear_combination I * s * this

end GaussSchur

end Schur8Sec

section Gauss1Sec

open Complex Finset
open scoped Real

namespace GaussSum

/-- `e N a = exp(2πi a / N)` for naturals. -/
noncomputable def e (N a : ℕ) : ℂ := Complex.exp (2 * π * I * (a : ℂ) / (N : ℂ))

/-- The quadratic Gauss sum `∑_{k<N} exp(2πi m k² / N)`. -/
noncomputable def gsum (m N : ℕ) : ℂ := ∑ k ∈ range N, e N (m * k ^ 2)

lemma e_add (N a b : ℕ) : e N (a + b) = e N a * e N b := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma e_mul_add (N a b : ℕ) : e N (a + N * b) = e N a := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  unfold e
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (2 * π * I * ((a + N * b : ℕ) : ℂ) / N) = 2 * π * I * a / N + b * (2 * π * I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma e_mod (N a : ℕ) : e N (a % N) = e N a := by
  conv_rhs => rw [← Nat.mod_add_div a N]
  rw [e_mul_add]

lemma e_mul_left (N₁ N₂ a : ℕ) (h : 0 < N₂) : e (N₁ * N₂) (N₂ * a) = e N₁ a := by
  unfold e
  congr 1
  have : (N₂ : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  push_cast
  rcases Nat.eq_zero_or_pos N₁ with rfl | hN
  · simp
  have : (N₁ : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma e_mul_right (N₁ N₂ a : ℕ) (h : 0 < N₁) : e (N₁ * N₂) (N₁ * a) = e N₂ a := by
  rw [mul_comm N₁ N₂]; exact e_mul_left N₂ N₁ a h

lemma e_zero (N : ℕ) : e N 0 = 1 := by
  unfold e; simp

lemma e_self_mul (N a : ℕ) : e N (N * a) = 1 := by
  have := e_mul_add N 0 a
  rwa [zero_add, e_zero] at this

lemma e_sq_mod (N m a : ℕ) : e N (m * (a % N) ^ 2) = e N (m * a ^ 2) := by
  conv_rhs => rw [← Nat.mod_add_div a N]
  rw [show m * (a % N + N * (a / N)) ^ 2 = m * (a % N) ^ 2 + N * (m * (2 * (a % N) * (a / N) + N * (a / N) ^ 2)) by ring, e_mul_add]

/-- Chinese remainder theorem for quadratic Gauss sums. -/
theorem gsum_mul (m N₁ N₂ : ℕ) (h₁ : 0 < N₁) (h₂ : 0 < N₂) (hc : Nat.Coprime N₁ N₂) :
    gsum m (N₁ * N₂) = gsum (m * N₂) N₁ * gsum (m * N₁) N₂ := by
  unfold gsum
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  set g : ℕ × ℕ → ℕ := fun p => (N₂ * p.1 + N₁ * p.2) % (N₁ * N₂) with hg
  have hinj : Set.InjOn g ↑(range N₁ ×ˢ range N₂) := by
    rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hab
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at ha hb
    simp only [hg] at hab
    have hmod : N₂ * a₁ + N₁ * a₂ ≡ N₂ * b₁ + N₁ * b₂ [MOD N₁ * N₂] := hab
    have e1 : a₁ = b₁ := by
      have h := (Nat.ModEq.of_mul_right N₂ hmod)
      have k1 : N₂ * a₁ + N₁ * a₂ ≡ N₂ * a₁ [MOD N₁] := Nat.add_mul_mod_self_left _ _ _
      have k2 : N₂ * b₁ + N₁ * b₂ ≡ N₂ * b₁ [MOD N₁] := Nat.add_mul_mod_self_left _ _ _
      have h' : N₂ * a₁ ≡ N₂ * b₁ [MOD N₁] := k1.symm.trans (h.trans k2)
      have := Nat.ModEq.cancel_left_of_coprime hc h'
      exact Nat.ModEq.eq_of_lt_of_lt this ha.1 hb.1
    have e2 : a₂ = b₂ := by
      have h := (Nat.ModEq.of_mul_left N₁ hmod)
      have k1 : N₂ * a₁ + N₁ * a₂ ≡ N₁ * a₂ [MOD N₂] := by
        rw [add_comm]; exact Nat.add_mul_mod_self_left _ _ _
      have k2 : N₂ * b₁ + N₁ * b₂ ≡ N₁ * b₂ [MOD N₂] := by
        rw [add_comm]; exact Nat.add_mul_mod_self_left _ _ _
      have h' : N₁ * a₂ ≡ N₁ * b₂ [MOD N₂] := k1.symm.trans (h.trans k2)
      have := Nat.ModEq.cancel_left_of_coprime hc.symm h'
      exact Nat.ModEq.eq_of_lt_of_lt this ha.2 hb.2
    rw [e1, e2]
  have himg : (range N₁ ×ˢ range N₂).image g = range (N₁ * N₂) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [mem_range, hg]
      exact Nat.mod_lt _ (Nat.mul_pos h₁ h₂)
    · rw [card_range, card_image_of_injOn hinj, card_product, card_range, card_range]
  rw [← himg, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  rintro ⟨k₁, k₂⟩ _
  simp only [hg]
  rw [e_sq_mod]
  have : m * (N₂ * k₁ + N₁ * k₂) ^ 2 = N₂ * (m * N₂ * k₁ ^ 2) + N₁ * (m * N₁ * k₂ ^ 2)
      + (N₁ * N₂) * (2 * m * k₁ * k₂) := by ring
  rw [this, e_add, e_add, e_self_mul, mul_one, e_mul_left _ _ _ h₂, e_mul_right _ _ _ h₁]

end GaussSum

end Gauss1Sec

section Gauss2Sec

open Complex Finset
open scoped Real

namespace GaussSum

lemma e_two (m : ℕ) : e 2 m = (-1) ^ m := by
  unfold e
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1; ring

lemma e_four (m : ℕ) : e 4 m = I ^ m := by
  have : e 4 m = Complex.exp (m * (π / 2 * I)) := by unfold e; congr 1; ring
  rw [this, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]

lemma gsum_two (m : ℕ) : gsum m 2 = 1 + (-1) ^ m := by
  have h0 : e 2 (m * 0 ^ 2) = 1 := by rw [show m * 0 ^ 2 = 0 by ring, e_zero]
  have h1 : e 2 (m * 1 ^ 2) = (-1) ^ m := by rw [show m * 1 ^ 2 = m by ring, e_two]
  simp only [gsum, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1]
  ring

lemma gsum_four (m : ℕ) : gsum m 4 = 2 * (1 + I ^ m) := by
  have h0 : e 4 (m * 0 ^ 2) = 1 := by rw [show m * 0 ^ 2 = 0 by ring, e_zero]
  have h1 : e 4 (m * 1 ^ 2) = I ^ m := by rw [show m * 1 ^ 2 = m by ring, e_four]
  have h2 : e 4 (m * 2 ^ 2) = 1 := by rw [show m * 2 ^ 2 = 0 + 4 * m by ring, e_mul_add, e_zero]
  have h3 : e 4 (m * 3 ^ 2) = I ^ m := by
    rw [show m * 3 ^ 2 = m + 4 * (2 * m) by ring, e_mul_add, e_four]
  simp only [gsum, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3]
  ring

lemma gsum_eight (m : ℕ) : gsum m 8 = 2 + 4 * e 8 m + 2 * (-1) ^ m := by
  have h4 : e 8 (4 * m) = (-1) ^ m := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, e_mul_right _ _ _ (by norm_num), e_two]
  have k0 : e 8 (m * 0 ^ 2) = 1 := by rw [show m * 0 ^ 2 = 0 by ring, e_zero]
  have k1 : e 8 (m * 1 ^ 2) = e 8 m := by rw [show m * 1 ^ 2 = m by ring]
  have k2 : e 8 (m * 2 ^ 2) = (-1) ^ m := by rw [show m * 2 ^ 2 = 4 * m by ring, h4]
  have k3 : e 8 (m * 3 ^ 2) = e 8 m := by rw [show m * 3 ^ 2 = m + 8 * m by ring, e_mul_add]
  have k4 : e 8 (m * 4 ^ 2) = 1 := by rw [show m * 4 ^ 2 = 0 + 8 * (2 * m) by ring, e_mul_add, e_zero]
  have k5 : e 8 (m * 5 ^ 2) = e 8 m := by rw [show m * 5 ^ 2 = m + 8 * (3 * m) by ring, e_mul_add]
  have k6 : e 8 (m * 6 ^ 2) = (-1) ^ m := by
    rw [show m * 6 ^ 2 = 4 * m + 8 * (4 * m) by ring, e_mul_add, h4]
  have k7 : e 8 (m * 7 ^ 2) = e 8 m := by rw [show m * 7 ^ 2 = m + 8 * (6 * m) by ring, e_mul_add]
  simp only [gsum, Finset.sum_range_succ, Finset.sum_range_zero, k0, k1, k2, k3, k4, k5, k6, k7]
  ring

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ range (2 * n), f k = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    abel

lemma e_sq_add_self (N m j : ℕ) : e N (m * (N + j) ^ 2) = e N (m * j ^ 2) := by
  rw [show m * (N + j) ^ 2 = m * j ^ 2 + N * (m * (N + 2 * j)) by ring, e_mul_add]

/-- reduction for `16 ∣ N`. -/
theorem gsum_sixteen (m L : ℕ) (hm : Odd m) : gsum m (16 * L) = 2 * gsum m (4 * L) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [gsum]
  unfold gsum
  rw [show 16 * L = 2 * (8 * L) by ring, sum_range_two_mul, Finset.sum_add_distrib]
  -- even part
  have heven : ∑ j ∈ range (8 * L), e (2 * (8 * L)) (m * (2 * j) ^ 2)
      = 2 * ∑ k ∈ range (4 * L), e (4 * L) (m * k ^ 2) := by
    have : ∀ j, e (2 * (8 * L)) (m * (2 * j) ^ 2) = e (4 * L) (m * j ^ 2) := by
      intro j
      rw [show 2 * (8 * L) = 4 * L * 4 by ring, show m * (2 * j) ^ 2 = 4 * (m * j ^ 2) by ring,
        e_mul_left _ _ _ (by norm_num)]
    simp_rw [this]
    rw [show 8 * L = 4 * L + 4 * L by ring, Finset.sum_range_add]
    simp_rw [e_sq_add_self]
    ring
  -- odd part
  have hodd : ∑ j ∈ range (8 * L), e (2 * (8 * L)) (m * (2 * j + 1) ^ 2) = 0 := by
    set g : ℕ → ℂ := fun j => e (2 * (8 * L)) (m * (2 * j + 1) ^ 2) with hg
    have hshift : ∀ j, g (2 * L + j) = - g j := by
      intro j
      simp only [hg]
      rw [show m * (2 * (2 * L + j) + 1) ^ 2 = m * (2 * j + 1) ^ 2 + 2 * (8 * L) * (m * j + m * L)
          + 8 * L * m by ring, e_add, e_add, e_self_mul, mul_one,
        e_mul_left 2 (8 * L) m (by omega), e_two,
        hm.neg_one_pow]
      ring
    have hshift2 : ∀ j, g (4 * L + j) = g j := by
      intro j
      rw [show 4 * L + j = 2 * L + (2 * L + j) by ring, hshift, hshift, neg_neg]
    show ∑ j ∈ range (8 * L), g j = 0
    rw [show 8 * L = 4 * L + 4 * L by ring, Finset.sum_range_add]
    simp_rw [hshift2]
    rw [show 4 * L = 2 * L + 2 * L by ring, Finset.sum_range_add]
    simp_rw [hshift]
    rw [Finset.sum_neg_distrib]
    ring
  rw [heven, hodd, add_zero]

end GaussSum

end Gauss2Sec

section ZoloSec

open Finset

namespace Zolotarev

/-- The ℕ-level inversion product. -/
lemma sign_toPerm_eq_prod (t : ℕ) [NeZero t] (σ : Equiv.Perm (ZMod t)) :
    ((Equiv.Perm.sign σ : ℤˣ) : ℤ) =
      ∏ j ∈ range t, ∏ i ∈ range j,
        (if (σ (i : ZMod t)).val < (σ (j : ZMod t)).val then (1 : ℤ) else -1) := by
  rw [← Equiv.Perm.sign_permCongr (GaussSchur.finZMod (N := t)).symm σ,
    Equiv.Perm.sign_eq_prod_prod_Iio, Units.coe_prod]
  simp_rw [Units.coe_prod]
  rw [← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  have key : ∀ x : Fin t, ((GaussSchur.finZMod (N := t)).symm.permCongr σ x : Fin t) =
      ⟨(σ (x : ZMod t)).val, ZMod.val_lt _⟩ := by
    intro x; rfl
  rw [key, key]
  simp only [Fin.lt_def, Fin.valEmbedding_apply]
  split_ifs <;> simp

lemma prod_ite_neg_one (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∏ i ∈ s, (if P i then (1 : ℤ) else -1) = (-1) ^ (s.filter (fun i => ¬ P i)).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

lemma two_mul_mod (t x : ℕ) (hx : x < t) : (2 * x) % t = if 2 * x < t then 2 * x else 2 * x - t := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma card_filter_inv (h j : ℕ) (hj : j < 2 * h + 1) :
    ((range j).filter (fun i => ¬ ((2 * i) % (2 * h + 1) < (2 * j) % (2 * h + 1)))).card
      = if h < j then 2 * h + 1 - j else 0 := by
  split_ifs with hhj
  · have : (range j).filter (fun i => ¬ ((2 * i) % (2 * h + 1) < (2 * j) % (2 * h + 1)))
        = Ico (j - h) (h + 1) := by
      ext i
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨hi, hlt⟩
        rw [two_mul_mod _ _ (by omega), two_mul_mod _ _ hj] at hlt
        split_ifs at hlt <;> omega
      · rintro ⟨h1, h2⟩
        refine ⟨by omega, ?_⟩
        rw [two_mul_mod _ _ (by omega), two_mul_mod _ _ hj]
        split_ifs <;> omega
    rw [this, Nat.card_Ico]; omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    simp only [mem_range] at hi
    rw [two_mul_mod _ _ (by omega), two_mul_mod _ _ hj]
    split_ifs <;> omega

lemma sum_count (h : ℕ) :
    (∑ j ∈ range (2 * h + 1), if h < j then 2 * h + 1 - j else 0) * 2 = h * (h + 1) := by
  rw [show range (2 * h + 1) = range ((h + 1) + h) by congr 1; ring, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun j hj => by simp only [mem_range] at hj; rw [if_neg (by omega)]), zero_add]
  have : ∀ j ∈ range h, (if h < h + 1 + j then 2 * h + 1 - (h + 1 + j) else 0) = h - j := by
    intro j hj; simp only [mem_range] at hj; rw [if_pos (by omega)]; omega
  rw [Finset.sum_congr rfl this]
  clear this
  induction h with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_sub_cancel_left]
    have : ∀ j ∈ range n, n + 1 - j = (n - j) + 1 := by
      intro j hj; simp only [mem_range] at hj; omega
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, card_range, smul_eq_mul,
      mul_one, add_mul, add_mul, ih]
    ring

lemma neg_one_pow_count (h : ℕ) :
    ((-1 : ℤ) ^ (∑ j ∈ range (2 * h + 1), if h < j then 2 * h + 1 - j else 0))
      = ZMod.χ₈ ((2 * h + 1 : ℕ) : ZMod 8) := by
  set n := ∑ j ∈ range (2 * h + 1), if h < j then 2 * h + 1 - j else 0 with hn
  have h2 := sum_count h
  rw [← hn] at h2
  rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
  obtain ⟨v, hv⟩ : ∃ v, h = 4 * v ∨ h = 4 * v + 1 ∨ h = 4 * v + 2 ∨ h = 4 * v + 3 :=
    ⟨h / 4, by omega⟩
  rcases hv with rfl | rfl | rfl | rfl
  · rw [if_pos (by omega)]
    have : n = 2 * (v * (4 * v + 1)) := by nlinarith
    rw [this, pow_mul]; norm_num
  · rw [if_neg (by omega)]
    have : n = 2 * (v * (4 * v + 3)) + 1 := by nlinarith
    rw [this, pow_succ, pow_mul]; norm_num
  · rw [if_neg (by omega)]
    have : n = 2 * ((4 * v + 1) * (v + 1)) + 1 := by nlinarith
    rw [this, pow_succ, pow_mul]; norm_num
  · rw [if_pos (by omega)]
    have : n = 2 * ((4 * v + 3) * (v + 1)) := by nlinarith
    rw [this, pow_mul]; norm_num

/-- Zolotarev's lemma for `2`: the sign of multiplication by `2` on `ZMod t` (t odd) is `χ₈ t`. -/
theorem sign_mul_two (t : ℕ) [NeZero t] (ht : Odd t) (u : (ZMod t)ˣ) (hu : (u : ZMod t) = 2) :
    ((Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod t)) : ℤˣ) : ℤ)
      = ZMod.χ₈ (t : ZMod 8) := by
  obtain ⟨h, rfl⟩ := ht
  rw [sign_toPerm_eq_prod]
  have key : ∀ x : ℕ, ((MulAction.toPerm u : Equiv.Perm (ZMod (2 * h + 1))) (x : ZMod (2 * h + 1))).val
      = (2 * x) % (2 * h + 1) := by
    intro x
    rw [MulAction.toPerm_apply, Units.smul_def, hu, smul_eq_mul, ← ZMod.val_natCast]
    push_cast; rfl
  simp_rw [key, prod_ite_neg_one]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl (fun j hj => card_filter_inv h j (Finset.mem_range.mp hj))]
  exact neg_one_pow_count h

end Zolotarev

end ZoloSec

section Gauss3Sec

open Complex Finset
open scoped Real

namespace GaussSum

/-- The sign character of an odd modulus `t`: `m ↦ sign(x ↦ m x)`. -/
noncomputable def sgnChar (t : ℕ) [NeZero t] : DirichletCharacter ℂ t :=
  MulChar.ofUnitHom ((Units.map (Int.castRingHom ℂ).toMonoidHom).comp
    (Equiv.Perm.sign.comp (MulAction.toPermHom (ZMod t)ˣ (ZMod t))))

lemma sgnChar_coe (t : ℕ) [NeZero t] (u : (ZMod t)ˣ) :
    sgnChar t (u : ZMod t) =
      ((Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod t)) : ℤ) : ℂ) := by
  unfold sgnChar
  rw [MulChar.ofUnitHom_coe]
  simp only [MonoidHom.comp_apply, Units.coe_map]
  rfl

lemma sgnChar_coe_cases (t : ℕ) [NeZero t] (u : (ZMod t)ˣ) :
    sgnChar t (u : ZMod t) = 1 ∨ sgnChar t (u : ZMod t) = -1 := by
  rw [sgnChar_coe]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod t))) with h | h <;>
    simp [h]

lemma sgnChar_real (t : ℕ) [NeZero t] (a : ZMod t) : (sgnChar t a).im = 0 ∧ ‖sgnChar t a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rcases sgnChar_coe_cases t u with h | h <;> simp [h]
  · rw [MulChar.map_nonunit _ ha]; simp

lemma sgnChar_two (t : ℕ) [NeZero t] (ht : Odd t) :
    sgnChar t (2 : ZMod t) = ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℂ) := by
  have h2 : IsUnit (2 : ZMod t) := GaussSchur.isUnit_two ht
  obtain ⟨u, hu⟩ := h2
  rw [← hu, sgnChar_coe, Zolotarev.sign_mul_two t ht u hu]

/-- `gsum` as a sum over `ZMod N`. -/
lemma gsum_eq_sum_zmod (m N : ℕ) [NeZero N] :
    gsum m N = ∑ j : ZMod N, (ZMod.stdAddChar : AddChar (ZMod N) ℂ) ((m : ZMod N) * j ^ 2) := by
  unfold gsum
  rw [Finset.sum_range, ← Fintype.sum_equiv GaussSchur.finZMod _ _ (fun i => rfl)]
  apply Finset.sum_congr rfl
  intro i _
  rw [GaussSchur.finZMod_apply, ZMod.stdAddChar_apply]
  have : (m : ZMod N) * ((i : ℕ) : ZMod N) ^ 2 = ((m * (i : ℕ) ^ 2 : ℕ) : ZMod N) := by push_cast; ring
  rw [this, ZMod.toCircle_natCast]
  rfl

theorem gsum_odd (N : ℕ) [NeZero N] (hN : Odd N) (m : ℕ) (hm : Nat.Coprime m N) :
    gsum m N = sgnChar N m * (if N % 4 = 1 then 1 else I) * (Real.sqrt N : ℂ) := by
  rw [gsum_eq_sum_zmod]
  have hu : IsUnit (m : ZMod N) := (ZMod.isUnit_iff_coprime m N).mpr hm
  obtain ⟨u, hu⟩ := hu
  rw [← hu, GaussSchur.gauss_sum_odd hN u, sgnChar_coe]

end GaussSum

end Gauss3Sec

section Gauss4Sec

open Complex Finset
open scoped Real

namespace GaussSum

/-- complex-valued `χ₄`, `χ₈`, `χ₈'`. -/
noncomputable def χ₄C : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
noncomputable def χ₈C : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
noncomputable def χ₈'C : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

lemma χ₄C_apply (a : ZMod 4) : χ₄C a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl
lemma χ₈C_apply (a : ZMod 8) : χ₈C a = ((ZMod.χ₈ a : ℤ) : ℂ) := rfl
lemma χ₈'C_apply (a : ZMod 8) : χ₈'C a = ((ZMod.χ₈' a : ℤ) : ℂ) := rfl

lemma quadratic_real {n : ℕ} (χ : MulChar (ZMod n) ℤ) (hχ : χ.IsQuadratic) (a : ZMod n) :
    (((χ a : ℤ) : ℂ)).im = 0 ∧ ‖((χ a : ℤ) : ℂ)‖ ≤ 1 := by
  rcases hχ a with h | h | h <;> simp [h]

lemma χ₄C_real (a : ZMod 4) : (χ₄C a).im = 0 ∧ ‖χ₄C a‖ ≤ 1 :=
  quadratic_real _ ZMod.isQuadratic_χ₄ a
lemma χ₈C_real (a : ZMod 8) : (χ₈C a).im = 0 ∧ ‖χ₈C a‖ ≤ 1 :=
  quadratic_real _ ZMod.isQuadratic_χ₈ a
lemma χ₈'C_real (a : ZMod 8) : (χ₈'C a).im = 0 ∧ ‖χ₈'C a‖ ≤ 1 :=
  quadratic_real _ ZMod.isQuadratic_χ₈' a

/-- `I ^ x = χ₄(x) I` for odd `x`. -/
lemma I_pow_odd (x : ℕ) (hx : Odd x) : I ^ x = ((ZMod.χ₄ (x : ZMod 4) : ℤ) : ℂ) * I := by
  rw [GaussSchur.I_pow_mod, ZMod.χ₄_nat_eq_if_mod_four, if_neg (by rcases hx with ⟨k, rfl⟩; omega)]
  have : x % 4 = 1 ∨ x % 4 = 3 := by rcases hx with ⟨k, rfl⟩; omega
  rcases this with h | h <;> rw [h] <;> simp [pow_succ]

lemma e_eight_one : e 8 1 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I) := by
  have : e 8 1 = Complex.exp (((π / 4 : ℝ) : ℂ) * I) := by unfold e; congr 1; push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast; ring

lemma e_eight_pow (x : ℕ) : e 8 x = (e 8 1) ^ x := by
  unfold e
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `e 8 x` for odd `x`. -/
lemma e_eight_odd (x : ℕ) (hx : Odd x) :
    e 8 x = ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
      (((ZMod.χ₈ (x : ZMod 8) : ℤ) : ℂ) + I * ((ZMod.χ₈' (x : ZMod 8) : ℤ) : ℂ)) := by
  have h2 : e 8 2 = I := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, show (2 : ℕ) = 2 * 1 by norm_num,
      e_mul_left 4 2 1 (by norm_num), e_four, pow_one]
  have h4 : e 8 4 = -1 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, show (4 : ℕ) = 4 * 1 by norm_num,
      e_mul_left 2 4 1 (by norm_num), e_two, pow_one]
  have h3 : e 8 3 = e 8 1 * I := by rw [show (3 : ℕ) = 1 + 2 by norm_num, e_add, h2]
  have h5 : e 8 5 = - e 8 1 := by rw [show (5 : ℕ) = 1 + 4 by norm_num, e_add, h4]; ring
  have h7 : e 8 7 = - (e 8 1 * I) := by rw [show (7 : ℕ) = 3 + 4 by norm_num, e_add, h4, h3]; ring
  rw [← e_mod, ← ZMod.natCast_mod x 8]
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by rcases hx with ⟨k, rfl⟩; omega
  rcases this with h | h | h | h <;> rw [h]
  · rw [e_eight_one]; simp
  · rw [h3, e_eight_one, show ((3 : ℕ) : ZMod 8) = 3 by rfl,
      show ZMod.χ₈ (3 : ZMod 8) = -1 by decide, show ZMod.χ₈' (3 : ZMod 8) = 1 by decide]
    push_cast
    linear_combination ((Real.sqrt 2 : ℝ) : ℂ) / 2 * I_sq
  · rw [h5, e_eight_one, show ((5 : ℕ) : ZMod 8) = 5 by rfl,
      show ZMod.χ₈ (5 : ZMod 8) = -1 by decide, show ZMod.χ₈' (5 : ZMod 8) = -1 by decide]
    push_cast
    ring
  · rw [h7, e_eight_one, show ((7 : ℕ) : ZMod 8) = 7 by rfl,
      show ZMod.χ₈ (7 : ZMod 8) = 1 by decide, show ZMod.χ₈' (7 : ZMod 8) = -1 by decide]
    push_cast
    linear_combination -((Real.sqrt 2 : ℝ) : ℂ) / 2 * I_sq

end GaussSum

end Gauss4Sec

section Gauss5Sec

open Complex Finset
open scoped Real

namespace GaussSum

/-- Real-valued and bounded by `1`. -/
def RealBdd {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∀ a : ZMod N, (χ a).im = 0 ∧ ‖χ a‖ ≤ 1

lemma RealBdd.mul {N : ℕ} {χ χ' : DirichletCharacter ℂ N} (h : RealBdd χ) (h' : RealBdd χ') :
    RealBdd (χ * χ') := by
  intro a
  obtain ⟨h1, h2⟩ := h a
  obtain ⟨h1', h2'⟩ := h' a
  rw [MulChar.mul_apply]
  refine ⟨by rw [Complex.mul_im, h1, h1']; ring, ?_⟩
  rw [norm_mul]
  exact mul_le_one₀ h2 (norm_nonneg _) h2'

lemma RealBdd.one (N : ℕ) : RealBdd (1 : DirichletCharacter ℂ N) := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [MulChar.one_apply_coe]; simp
  · rw [MulChar.map_nonunit _ ha]; simp

lemma RealBdd.changeLevel {n m : ℕ} (h : n ∣ m) {χ : DirichletCharacter ℂ n} (hχ : RealBdd χ) :
    RealBdd (DirichletCharacter.changeLevel h χ) := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact hχ _
  · rw [MulChar.map_nonunit _ ha]; simp

lemma changeLevel_natCast {n m : ℕ} (h : n ∣ m) (χ : DirichletCharacter ℂ n) (k : ℕ)
    (hk : Nat.Coprime k m) :
    DirichletCharacter.changeLevel h χ (k : ZMod m) = χ (k : ZMod n) := by
  have hu : IsUnit (k : ZMod m) := (ZMod.isUnit_iff_coprime k m).mpr hk
  obtain ⟨u, hu⟩ := hu
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast h]

lemma sgnChar_real' (t : ℕ) [NeZero t] : RealBdd (sgnChar t) := sgnChar_real t

lemma χ₈_odd_sq (t : ℕ) (ht : Odd t) : ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℂ) ^ 2 = 1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by rcases ht with ⟨k, rfl⟩; omega)]
  split_ifs <;> simp

lemma sgnChar_four (t : ℕ) [NeZero t] (ht : Odd t) : sgnChar t (4 : ZMod t) = 1 := by
  rw [show (4 : ZMod t) = 2 * 2 by norm_num, map_mul, sgnChar_two t ht, ← pow_two, χ₈_odd_sq t ht]

lemma sgnChar_eight (t : ℕ) [NeZero t] (ht : Odd t) :
    sgnChar t (8 : ZMod t) = ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℂ) := by
  rw [show (8 : ZMod t) = 4 * 2 by norm_num, map_mul, sgnChar_four t ht, sgnChar_two t ht, one_mul]

lemma sgnChar_natCast_real (t : ℕ) [NeZero t] (m : ℕ) : ∃ r : ℝ, sgnChar t (m : ZMod t) = r := by
  by_cases hu : IsUnit (m : ZMod t)
  · obtain ⟨u, hu⟩ := hu
    rw [← hu]
    rcases sgnChar_coe_cases t u with h | h <;> rw [h]
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  · exact ⟨0, by rw [MulChar.map_nonunit _ hu]; simp⟩

lemma odd_of_coprime_two_mul {m k t : ℕ} (hk : 0 < k) (hm : Nat.Coprime m (2 ^ k * t)) : Odd m := by
  have : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self 2 hk.ne') t) hm
  exact Nat.coprime_two_right.mp this

lemma coprime_of_coprime_two_mul {m k t : ℕ} (hm : Nat.Coprime m (2 ^ k * t)) : Nat.Coprime m t :=
  Nat.Coprime.coprime_dvd_right (dvd_mul_left t _) hm

/-- The main structural theorem on the imaginary part of quadratic Gauss sums. -/
theorem gsum_im_structure (N : ℕ) (hN : 0 < N) :
    ∃ (c : ℝ) (χ : DirichletCharacter ℂ N), 0 ≤ c ∧ RealBdd χ ∧
      ∀ m : ℕ, Nat.Coprime m N → (((gsum m N).im : ℝ) : ℂ) = c * χ (m : ZMod N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  obtain ⟨k, t, ht, hNeq⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at ht)
  haveI : NeZero t := ⟨ht0.ne'⟩
  have hsqrt : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg _
  have h2t : Nat.Coprime 2 t := Nat.coprime_two_left.mpr ht
  rcases k with _ | _ | _ | _ | k
  · -- odd case
    have hN' : N = t := by simpa using hNeq
    clear hNeq
    subst N
    by_cases h4 : t % 4 = 1
    · refine ⟨0, sgnChar t, le_refl _, sgnChar_real' t, fun m hm => ?_⟩
      rw [gsum_odd t ht m hm, if_pos h4]
      obtain ⟨r, hr⟩ := sgnChar_natCast_real t m
      rw [hr]; simp
    · refine ⟨Real.sqrt t, sgnChar t, hsqrt, sgnChar_real' t, fun m hm => ?_⟩
      rw [gsum_odd t ht m hm, if_neg h4]
      obtain ⟨r, hr⟩ := sgnChar_natCast_real t m
      rw [hr]; simp [mul_comm]
  · -- N = 2 t
    have hN' : N = 2 ^ 1 * t := by simpa using hNeq
    clear hNeq
    subst N
    refine ⟨0, 1, le_refl _, RealBdd.one _, fun m hm => ?_⟩
    have hm2 : Odd m := odd_of_coprime_two_mul one_pos hm
    rw [pow_one, gsum_mul m 2 t two_pos ht0 h2t, gsum_two, (hm2.mul ht).neg_one_pow]
    simp
  · -- N = 4 t
    have hN' : N = 4 * t := by rw [hNeq]; norm_num
    clear hNeq
    subst N
    have h4t : Nat.Coprime 4 t := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.Coprime.pow_left 2 h2t
    have hdt : t ∣ 4 * t := dvd_mul_left _ _
    have hd4 : 4 ∣ 4 * t := dvd_mul_right _ _
    by_cases h4 : t % 4 = 1
    · refine ⟨2 * Real.sqrt t, DirichletCharacter.changeLevel hdt (sgnChar t) *
        DirichletCharacter.changeLevel hd4 χ₄C, by positivity,
        RealBdd.mul (RealBdd.changeLevel _ (sgnChar_real' t)) (RealBdd.changeLevel _ χ₄C_real),
        fun m hm => ?_⟩
      have hm2 : Odd m := odd_of_coprime_two_mul two_pos (by rwa [show (2:ℕ)^2 = 4 by norm_num])
      have hmt : Nat.Coprime (m * 4) t :=
        Nat.Coprime.mul_left (coprime_of_coprime_two_mul (k := 2) (by rwa [show (2:ℕ)^2 = 4 by norm_num])) h4t
      rw [gsum_mul m 4 t (by norm_num) ht0 h4t, gsum_four,
        gsum_odd t ht _ hmt, if_pos h4, I_pow_odd _ (hm2.mul ht), MulChar.mul_apply,
        changeLevel_natCast _ _ _ hm, changeLevel_natCast _ _ _ hm, χ₄C_apply]
      obtain ⟨r, hr⟩ := sgnChar_natCast_real t m
      have hs4 : sgnChar t ((m * 4 : ℕ) : ZMod t) = r := by
        push_cast; rw [map_mul, sgnChar_four t ht, hr, mul_one]
      have hχ₄ : ZMod.χ₄ ((m * t : ℕ) : ZMod 4) = ZMod.χ₄ (m : ZMod 4) := by
        push_cast; rw [map_mul, ZMod.χ₄_nat_eq_if_mod_four t, if_neg (by omega), if_pos h4, mul_one]
      rw [hs4, hr, hχ₄]
      have : ∀ z : ℤ, ((z : ℤ) : ℂ) = ((z : ℝ) : ℂ) := fun z => by simp
      rw [this]
      simp only [Complex.ext_iff, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
      constructor <;> ring
    · refine ⟨2 * Real.sqrt t, DirichletCharacter.changeLevel hdt (sgnChar t), by positivity,
        RealBdd.changeLevel _ (sgnChar_real' t), fun m hm => ?_⟩
      have hm2 : Odd m := odd_of_coprime_two_mul two_pos (by rwa [show (2:ℕ)^2 = 4 by norm_num])
      have hmt : Nat.Coprime (m * 4) t :=
        Nat.Coprime.mul_left (coprime_of_coprime_two_mul (k := 2) (by rwa [show (2:ℕ)^2 = 4 by norm_num])) h4t
      rw [gsum_mul m 4 t (by norm_num) ht0 h4t, gsum_four,
        gsum_odd t ht _ hmt, if_neg h4, I_pow_odd _ (hm2.mul ht), changeLevel_natCast _ _ _ hm]
      obtain ⟨r, hr⟩ := sgnChar_natCast_real t m
      have hs4 : sgnChar t ((m * 4 : ℕ) : ZMod t) = r := by
        push_cast; rw [map_mul, sgnChar_four t ht, hr, mul_one]
      rw [hs4, hr]
      have : ∀ z : ℤ, ((z : ℤ) : ℂ) = ((z : ℝ) : ℂ) := fun z => by simp
      rw [this]
      simp only [Complex.ext_iff, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
      constructor <;> ring
  · -- N = 8 t
    have hN' : N = 8 * t := by rw [hNeq]; norm_num
    clear hNeq
    subst N
    have h8t : Nat.Coprime 8 t := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.Coprime.pow_left 3 h2t
    have hdt : t ∣ 8 * t := dvd_mul_left _ _
    have hd8 : 8 ∣ 8 * t := dvd_mul_right _ _
    have hsq2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hχ8 : ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℂ) ^ 2 = 1 := χ₈_odd_sq t ht
    by_cases h4 : t % 4 = 1
    · refine ⟨2 * Real.sqrt 2 * Real.sqrt t, DirichletCharacter.changeLevel hdt (sgnChar t) *
        DirichletCharacter.changeLevel hd8 χ₈'C, by positivity,
        RealBdd.mul (RealBdd.changeLevel _ (sgnChar_real' t)) (RealBdd.changeLevel _ χ₈'C_real),
        fun m hm => ?_⟩
      have hm2 : Odd m := odd_of_coprime_two_mul (k := 3) (by norm_num) (by rwa [show (2:ℕ)^3 = 8 by norm_num])
      have hmt : Nat.Coprime (m * 8) t :=
        Nat.Coprime.mul_left (coprime_of_coprime_two_mul (k := 3) (by rwa [show (2:ℕ)^3 = 8 by norm_num])) h8t
      rw [gsum_mul m 8 t (by norm_num) ht0 h8t, gsum_eight,
        gsum_odd t ht _ hmt, if_pos h4, e_eight_odd _ (hm2.mul ht), (hm2.mul ht).neg_one_pow,
        MulChar.mul_apply, changeLevel_natCast _ _ _ hm, changeLevel_natCast _ _ _ hm, χ₈'C_apply]
      obtain ⟨r, hr⟩ := sgnChar_natCast_real t m
      have hs8 : sgnChar t ((m * 8 : ℕ) : ZMod t) = ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℂ) * r := by
        push_cast; rw [map_mul, sgnChar_eight t ht, hr, mul_comm]
      have hχ₈ : ZMod.χ₈ ((m * t : ℕ) : ZMod 8) = ZMod.χ₈ (m : ZMod 8) * ZMod.χ₈ (t : ZMod 8) := by
        push_cast; rw [map_mul]
      have hχ₈' : ZMod.χ₈' ((m * t : ℕ) : ZMod 8) = ZMod.χ₈' (m : ZMod 8) * ZMod.χ₈ (t : ZMod 8) := by
        push_cast; rw [map_mul]
        congr 1
        rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈'_nat_eq_if_mod_eight]
        have : t % 8 = 1 ∨ t % 8 = 5 := by omega
        rcases this with h | h <;> simp [h]
      rw [hs8, hr, hχ₈, hχ₈']
      have : ∀ z : ℤ, ((z : ℤ) : ℂ) = ((z : ℝ) : ℂ) := fun z => by simp
      have hχ8' : ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hχ8
      simp only [this, Int.cast_mul]
      simp only [Complex.ext_iff, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im]
      constructor
      · linear_combination (2 * Real.sqrt 2 * Real.sqrt t * r * (ZMod.χ₈' (m : ZMod 8) : ℝ)) * hχ8'
      · ring
    · refine ⟨2 * Real.sqrt 2 * Real.sqrt t, DirichletCharacter.changeLevel hdt (sgnChar t) *
        DirichletCharacter.changeLevel hd8 χ₈C, by positivity,
        RealBdd.mul (RealBdd.changeLevel _ (sgnChar_real' t)) (RealBdd.changeLevel _ χ₈C_real),
        fun m hm => ?_⟩
      have hm2 : Odd m := odd_of_coprime_two_mul (k := 3) (by norm_num) (by rwa [show (2:ℕ)^3 = 8 by norm_num])
      have hmt : Nat.Coprime (m * 8) t :=
        Nat.Coprime.mul_left (coprime_of_coprime_two_mul (k := 3) (by rwa [show (2:ℕ)^3 = 8 by norm_num])) h8t
      rw [gsum_mul m 8 t (by norm_num) ht0 h8t, gsum_eight,
        gsum_odd t ht _ hmt, if_neg h4, e_eight_odd _ (hm2.mul ht), (hm2.mul ht).neg_one_pow,
        MulChar.mul_apply, changeLevel_natCast _ _ _ hm, changeLevel_natCast _ _ _ hm, χ₈C_apply]
      obtain ⟨r, hr⟩ := sgnChar_natCast_real t m
      have hs8 : sgnChar t ((m * 8 : ℕ) : ZMod t) = ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℂ) * r := by
        push_cast; rw [map_mul, sgnChar_eight t ht, hr, mul_comm]
      have hχ₈ : ZMod.χ₈ ((m * t : ℕ) : ZMod 8) = ZMod.χ₈ (m : ZMod 8) * ZMod.χ₈ (t : ZMod 8) := by
        push_cast; rw [map_mul]
      have hχ₈' : ZMod.χ₈' ((m * t : ℕ) : ZMod 8) = ZMod.χ₈' (m : ZMod 8) * ZMod.χ₈' (t : ZMod 8) := by
        push_cast; rw [map_mul]
      rw [hs8, hr, hχ₈, hχ₈']
      have : ∀ z : ℤ, ((z : ℤ) : ℂ) = ((z : ℝ) : ℂ) := fun z => by simp
      have hχ8' : ((ZMod.χ₈ (t : ZMod 8) : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hχ8
      simp only [this, Int.cast_mul]
      simp only [Complex.ext_iff, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im]
      constructor
      · linear_combination (2 * Real.sqrt 2 * Real.sqrt t * r * (ZMod.χ₈ (m : ZMod 8) : ℝ)) * hχ8'
      · ring
  · -- 16 ∣ N
    have hN' : N = 16 * (2 ^ k * t) := by rw [hNeq]; ring
    clear hNeq
    subst N
    have hlt : 4 * (2 ^ k * t) < 16 * (2 ^ k * t) := by
      have : 0 < 2 ^ k * t := by positivity
      omega
    obtain ⟨c, χ, hc, hχ, hval⟩ := ih (4 * (2 ^ k * t)) hlt (by positivity)
    have hdvd : 4 * (2 ^ k * t) ∣ 16 * (2 ^ k * t) :=
      Nat.mul_dvd_mul_right (by norm_num) _
    refine ⟨2 * c, DirichletCharacter.changeLevel hdvd χ, by positivity, RealBdd.changeLevel _ hχ,
      fun m hm => ?_⟩
    have hm2 : Odd m := by
      have : Nat.Coprime m 2 :=
        Nat.Coprime.coprime_dvd_right (Dvd.dvd.mul_right (by norm_num) _) hm
      exact Nat.coprime_two_right.mp this
    have hm' : Nat.Coprime m (4 * (2 ^ k * t)) := Nat.Coprime.coprime_dvd_right hdvd hm
    rw [gsum_sixteen m _ hm2, changeLevel_natCast _ _ _ hm]
    have := hval m hm'
    rw [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    rw [this]; ring

end GaussSum

end Gauss5Sec

section HurwitzSec

open Complex Finset Filter Topology
open scoped Real

namespace HurwitzOne

/-- Bernoulli-type bound for differences of powers. -/
lemma rpow_neg_sub_le (u v s : ℝ) (hu : 0 < u) (huv : u ≤ v) (hs : 1 ≤ s) :
    u ^ (-s) - v ^ (-s) ≤ s * (v - u) * u ^ (-s - 1) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hr : -1 ≤ u / v - 1 := by
    have : 0 ≤ u / v := by positivity
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hr hs
  rw [add_sub_cancel] at hb
  -- (u/v)^s ≥ 1 + s (u/v - 1)
  have h1 : v ^ (-s) = u ^ (-s) * (u / v) ^ s := by
    rw [Real.div_rpow hu.le hv.le, Real.rpow_neg hu.le, Real.rpow_neg hv.le]
    field_simp
  rw [h1]
  have hus : 0 < u ^ (-s) := Real.rpow_pos_of_pos hu _
  have h2 : u ^ (-s) - u ^ (-s) * (u / v) ^ s ≤ u ^ (-s) * (s * (1 - u / v)) := by
    nlinarith
  have h3 : u ^ (-s) * (s * (1 - u / v)) ≤ s * (v - u) * u ^ (-s - 1) := by
    rw [Real.rpow_sub hu, Real.rpow_one, show 1 - u / v = (v - u) / v by field_simp]
    rw [show u ^ (-s) * (s * ((v - u) / v)) = s * (v - u) * (u ^ (-s) / v) by ring]
    apply mul_le_mul_of_nonneg_left _ (by nlinarith)
    rw [div_le_div_iff₀ hv hu]
    nlinarith
  linarith

/-- Symmetric version. -/
lemma abs_rpow_neg_sub_le (u v s : ℝ) (hu : 0 < u) (hv : 0 < v) (hs : 1 ≤ s) :
    |u ^ (-s) - v ^ (-s)| ≤ s * |v - u| * (min u v) ^ (-s - 1) := by
  rcases le_total u v with h | h
  · have h1 : (0 : ℝ) ≤ v - u := sub_nonneg.mpr h
    have h2 : (0 : ℝ) ≤ u ^ (-s) - v ^ (-s) := by
      rw [sub_nonneg]; exact Real.rpow_le_rpow_of_nonpos hu h (by linarith)
    rw [min_eq_left h, abs_of_nonneg h1, abs_of_nonneg h2]
    exact rpow_neg_sub_le u v s hu h hs
  · have h1 : v - u ≤ (0 : ℝ) := sub_nonpos.mpr h
    have h2 : u ^ (-s) - v ^ (-s) ≤ (0 : ℝ) := by
      rw [sub_nonpos]; exact Real.rpow_le_rpow_of_nonpos hv h (by linarith)
    rw [min_eq_right h, abs_of_nonpos h1, abs_of_nonpos h2]
    have := rpow_neg_sub_le v u s hv h hs
    linarith

/-- The paired term. -/
noncomputable def F (a s : ℝ) (n : ℕ) : ℝ := ((n + a) ^ (-s) - (n + 1 - a) ^ (-s)) / 2

lemma F_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (s : ℝ) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (n : ℕ) :
    |F a s n| ≤ (min a (1 - a)) ^ (-3 : ℝ) * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  set δ := min a (1 - a) with hδ
  have hδ0 : 0 < δ := lt_min ha0 (by linarith)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) ha1.le
  have hu : 0 < (n : ℝ) + a := by positivity
  have hv : 0 < (n : ℝ) + 1 - a := by linarith
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hmin : δ * (n + 1) ≤ min ((n : ℝ) + a) (n + 1 - a) := by
    apply le_min
    · have : δ ≤ a := min_le_left _ _
      nlinarith
    · have : δ ≤ 1 - a := min_le_right _ _
      nlinarith
  have hminpos : 0 < min ((n : ℝ) + a) (n + 1 - a) := lt_min hu hv
  unfold F
  rw [abs_div, abs_two, div_le_iff₀ (by norm_num)]
  calc |((n : ℝ) + a) ^ (-s) - (n + 1 - a) ^ (-s)|
      ≤ s * |(n + 1 - a) - (n + a)| * (min ((n : ℝ) + a) (n + 1 - a)) ^ (-s - 1) :=
        abs_rpow_neg_sub_le _ _ s hu hv hs1
    _ ≤ 2 * 1 * (δ * (n + 1)) ^ (-s - 1) := by
        apply mul_le_mul
        · apply mul_le_mul hs2 _ (abs_nonneg _) (by norm_num)
          rw [show (n : ℝ) + 1 - a - (n + a) = 1 - 2 * a by ring, abs_le]
          constructor <;> linarith
        · exact Real.rpow_le_rpow_of_nonpos (by positivity) hmin (by linarith)
        · positivity
        · positivity
    _ = 2 * (δ ^ (-s - 1) * ((n : ℝ) + 1) ^ (-s - 1)) := by
        rw [Real.mul_rpow hδ0.le hn1.le]; ring
    _ ≤ 2 * (δ ^ (-3 : ℝ) * ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        · positivity
        · positivity
    _ = δ ^ (-3 : ℝ) * ((n : ℝ) + 1) ^ (-2 : ℝ) * 2 := by ring

lemma summable_bound (δ : ℝ) :
    Summable (fun n : ℕ => δ ^ (-3 : ℝ) * ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
  apply Summable.mul_left
  have := (Real.summable_nat_rpow_inv (p := 2)).mpr one_lt_two
  rw [← summable_nat_add_iff 1] at this
  refine this.congr fun n => ?_
  rw [Real.rpow_neg (by positivity)]
  push_cast; rfl

/-- The series representation for real `s > 1`. -/
lemma hurwitzZetaOdd_eq_tsum (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (s : ℝ) (hs : 1 < s) :
    HurwitzZeta.hurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) = ∑' n : ℕ, ((F a s n : ℝ) : ℂ) := by
  have h := (HurwitzZeta.hasSum_int_hurwitzZetaOdd a (s := (s : ℂ)) (by simpa using hs)).nat_add_neg_add_one
  rw [← h.tsum_eq]
  congr 1; ext n
  have hu : 0 < (n : ℝ) + a := by positivity
  have hv : 0 < (n : ℝ) + 1 - a := by linarith
  have e1 : (((n : ℤ) : ℝ) + a) = (n : ℝ) + a := by push_cast; rfl
  have e2 : (((-((n : ℤ) + 1)) : ℤ) : ℝ) + a = -((n : ℝ) + 1 - a) := by push_cast; ring
  rw [e1, e2, sign_pos hu, abs_of_pos hu, abs_neg, abs_of_pos hv, sign_neg (by linarith)]
  unfold F
  rw [Real.rpow_neg hu.le, Real.rpow_neg hv.le]
  push_cast
  rw [Complex.ofReal_cpow hu.le, Complex.ofReal_cpow hv.le]
  push_cast
  simp only [SignType.coe_one]
  ring

/-- Telescoping. -/
lemma hasSum_telescope (a : ℝ) (ha0 : 0 < a) :
    HasSum (fun n : ℕ => (1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + 1 + a))) (1 / (a : ℂ)) := by
  have : HasSum (fun n : ℕ => (1 / ((n : ℝ) + a) - 1 / ((n : ℝ) + 1 + a))) (1 / a) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hpart : ∀ N : ℕ, ∑ i ∈ range N, (1 / ((i : ℝ) + a) - 1 / ((i : ℝ) + 1 + a))
          = 1 / a - 1 / ((N : ℝ) + a) := by
        intro N
        have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + a)) N
        simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at this
        rw [← this]
      simp_rw [hpart]
      have h0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + a)) atTop (𝓝 0) := by
        have : Tendsto (fun N : ℕ => (N : ℝ) + a) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        exact tendsto_const_nhds.div_atTop this
      simpa using (tendsto_const_nhds (x := (1 / a : ℝ))).sub h0
    · intro n
      have h1 : 0 < (n : ℝ) + a := by positivity
      have h2 : (n : ℝ) + a ≤ n + 1 + a := by linarith
      have := one_div_le_one_div_of_le h1 h2
      linarith
  have := (Complex.hasSum_ofReal.mpr this)
  push_cast at this
  exact this

lemma hasSum_cot (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HasSum (fun n : ℕ => (1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + 1 - a))) (π * Complex.cot (π * a)) := by
  have hz : (a : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have : (k : ℝ) = a := by exact_mod_cast hk
    have h1 : (0 : ℝ) < k := by rw [this]; exact ha0
    have h2 : (k : ℝ) < 1 := by rw [this]; exact ha1
    have : (0 : ℤ) < k := by exact_mod_cast h1
    have : k < (1 : ℤ) := by exact_mod_cast h2
    omega
  have h1 : HasSum (fun n : ℕ => (1 / ((a : ℂ) - (n + 1)) + 1 / ((a : ℂ) + (n + 1))))
      (π * Complex.cot (π * a) - 1 / a) := by
    rw [cot_series_rep' hz]
    exact (Summable_cotTerm hz).hasSum
  have h2 := hasSum_telescope a ha0
  have := h1.add h2
  rw [sub_add_cancel] at this
  refine this.congr_fun fun n => ?_
  have hu : ((n : ℂ) + a) ≠ 0 := by
    have : (0 : ℝ) < n + a := by positivity
    exact_mod_cast this.ne'
  have hv : ((n : ℂ) + 1 - a) ≠ 0 := by
    have : (0 : ℝ) < n + 1 - a := by linarith
    exact_mod_cast this.ne'
  have hw : ((n : ℂ) + 1 + a) ≠ 0 := by
    have : (0 : ℝ) < n + 1 + a := by positivity
    exact_mod_cast this.ne'
  have hv' : ((a : ℂ) - (n + 1)) ≠ 0 := by
    intro h; apply hv; linear_combination -h
  have hw' : ((a : ℂ) + (n + 1)) ≠ 0 := by
    intro h; apply hw; linear_combination h
  field_simp
  ring

/-- Main result: `hurwitzZetaOdd a 1 = (π/2) cot(π a)` for `0 < a < 1`. -/
theorem hurwitzZetaOdd_one (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HurwitzZeta.hurwitzZetaOdd (a : UnitAddCircle) 1 = π / 2 * Complex.cot (π * a) := by
  set δ := min a (1 - a) with hδ
  have hδ0 : 0 < δ := lt_min ha0 (by linarith)
  -- limit of the series
  have hlim : Tendsto (fun s : ℝ => ∑' n : ℕ, ((F a s n : ℝ) : ℂ)) (𝓝[>] 1)
      (𝓝 (∑' n : ℕ, ((F a 1 n : ℝ) : ℂ))) := by
    apply tendsto_tsum_of_dominated_convergence (summable_bound δ)
    · intro n
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply Continuous.tendsto
      have hu : (n : ℝ) + a ≠ 0 := by positivity
      have hv : (n : ℝ) + 1 - a ≠ 0 := by
        have : (0 : ℝ) < n + 1 - a := by linarith
        exact this.ne'
      apply Complex.continuous_ofReal.comp
      unfold F
      apply Continuous.div_const
      apply Continuous.sub
      · exact (Real.continuous_const_rpow hu).comp continuous_neg
      · exact (Real.continuous_const_rpow hv).comp continuous_neg
    · filter_upwards [Ioo_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with s hs n
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact F_bound a ha0 ha1 s hs.1.le hs.2.le n
  -- the limit of hurwitzZetaOdd
  have hcont : Tendsto (fun s : ℝ => HurwitzZeta.hurwitzZetaOdd (a : UnitAddCircle) (s : ℂ)) (𝓝[>] 1)
      (𝓝 (HurwitzZeta.hurwitzZetaOdd (a : UnitAddCircle) 1)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have := ((HurwitzZeta.differentiable_hurwitzZetaOdd (a : UnitAddCircle)).continuous.comp
      Complex.continuous_ofReal).tendsto 1
    simpa using this
  have heq : (fun s : ℝ => HurwitzZeta.hurwitzZetaOdd (a : UnitAddCircle) (s : ℂ)) =ᶠ[𝓝[>] 1]
      (fun s : ℝ => ∑' n : ℕ, ((F a s n : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hurwitzZetaOdd_eq_tsum a ha0 ha1 s hs
  have h1 := tendsto_nhds_unique (hcont.congr' heq) hlim
  rw [h1]
  -- evaluate the series at s = 1
  have h2 := (hasSum_cot a ha0 ha1).div_const 2
  rw [show (π / 2 * Complex.cot (π * a) : ℂ) = π * Complex.cot (π * a) / 2 by ring, ← h2.tsum_eq]
  congr 1; ext n
  unfold F
  have hu : 0 ≤ (n : ℝ) + a := by positivity
  have hv : 0 ≤ (n : ℝ) + 1 - a := by linarith
  rw [Real.rpow_neg_one, Real.rpow_neg_one]
  push_cast
  ring

end HurwitzOne

end HurwitzSec

section TrigSec

open Complex Finset
open scoped Real

namespace TrigId

/-- The basic Fejér-type identity. -/
lemma sin_mul_cos_eq (φ : ℝ) (x : ℕ) :
    Real.sin (2 * x * φ) * Real.cos φ =
      Real.sin φ * (2 * ∑ j ∈ range x, Real.cos (2 * j * φ) - 1 + Real.cos (2 * x * φ)) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have e1 : 2 * ((x : ℝ) + 1) * φ = 2 * x * φ + 2 * φ := by ring
    rw [e1, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq φ
    linear_combination ih + (2 * Real.cos φ * Real.sin (2 * x * φ)) * this

/-- `∑_{m<n} cos(2π j m / n) = 0` for `0 < j < n`. -/
lemma sum_cos_eq_zero (n j : ℕ) (hj0 : 0 < j) (hjn : j < n) :
    ∑ m ∈ range n, Real.cos (2 * π * j * m / n) = 0 := by
  have hn : n ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp n hn
  set ζ := Complex.exp (2 * π * I / n) with hζdef
  have hne : ζ ^ j ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hj0.ne' hjn
  have hsum : ∑ m ∈ range n, (ζ ^ j) ^ m = 0 := by
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]
  have : ∀ m : ℕ, Real.cos (2 * π * j * m / n) = ((ζ ^ j) ^ m).re := by
    intro m
    rw [hζdef, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  simp_rw [this]
  rw [← Complex.re_sum, hsum, Complex.zero_re]

/-- The key finite identity: `∑_{m<n} sin(2π m x / n) cot(π m / n) = n - 2x` for `0 < x < n`. -/
theorem sum_sin_cot (n x : ℕ) (hx0 : 0 < x) (hxn : x < n) :
    ∑ m ∈ range n, Real.sin (2 * π * m * x / n) * Real.cot (π * m / n) = n - 2 * x := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hxn)
  -- termwise identity for 1 ≤ m < n
  have hterm : ∀ m ∈ range n, m ≠ 0 →
      Real.sin (2 * π * m * x / n) * Real.cot (π * m / n) =
        2 * ∑ j ∈ range x, Real.cos (2 * π * j * m / n) - 1 + Real.cos (2 * π * x * m / n) := by
    intro m hm hm0
    simp only [mem_range] at hm
    set φ := π * m / n with hφ
    have hφ0 : 0 < φ := by
      have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
      positivity
    have hφπ : φ < π := by
      rw [hφ, div_lt_iff₀ hn]
      have : (m : ℝ) < n := by exact_mod_cast hm
      nlinarith [Real.pi_pos]
    have hsin : Real.sin φ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ).ne'
    have key := sin_mul_cos_eq φ x
    rw [Real.cot_eq_cos_div_sin]
    have e1 : 2 * π * m * x / n = 2 * x * φ := by rw [hφ]; ring
    have e2 : ∀ j : ℕ, 2 * π * j * m / n = 2 * j * φ := by intro j; rw [hφ]; ring
    simp_rw [e1, e2]
    rw [mul_div_assoc', div_eq_iff hsin, key]
    ring
  -- the m = 0 term vanishes
  have h0 : Real.sin (2 * π * (0 : ℕ) * x / n) * Real.cot (π * (0 : ℕ) / n) = 0 := by simp
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', h0, add_zero]
  rw [Finset.sum_congr rfl (fun m hm => hterm (m + 1) (by simp at hm ⊢; omega) (Nat.succ_ne_zero m))]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, card_range, ← Finset.mul_sum,
    Finset.sum_comm]
  -- inner sums
  have hC : ∀ j : ℕ, 0 < j → j < n' + 1 →
      ∑ m ∈ range n', Real.cos (2 * π * j * ((m + 1 : ℕ) : ℝ) / (n' + 1 : ℕ)) = -1 := by
    intro j hj0 hjn
    have := sum_cos_eq_zero (n' + 1) j hj0 hjn
    rw [Finset.sum_range_succ'] at this
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero] at this
    push_cast at this ⊢
    linarith
  have hCx := hC x hx0 hxn
  have hC0 : ∑ m ∈ range n', Real.cos (2 * π * ((0 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) / (n' + 1 : ℕ)) = n' := by
    simp
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  rw [Finset.sum_range_succ', hC0]
  rw [Finset.sum_congr rfl (fun j hj => hC (j + 1) (Nat.succ_pos j) (by simp at hj; omega))]
  rw [Finset.sum_const, card_range]
  push_cast at hCx ⊢
  rw [hCx]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  ring

end TrigId

end TrigSec

section LPosSec

open Complex Finset
open scoped Real LSeries.notation

namespace GaussSum

/-- Positivity of `L(χ, s)` for real `s > 1` and a real-valued character. -/
theorem LSeries_char_pos {N : ℕ} (χ : DirichletCharacter ℂ N) (hχ : RealBdd χ) (s : ℝ)
    (hs : 1 < s) : ∃ r : ℝ, 0 < r ∧ LSeries (↗χ) (s : ℂ) = r := by
  have h := DirichletCharacter.LSeries_eulerProduct_exp_log χ (s := (s : ℂ)) (by simpa using hs)
  -- each term is real
  have hterm : ∀ p : Nat.Primes, -Complex.log (1 - χ (p : ℕ) * (p : ℂ) ^ (-(s : ℂ)))
      = ((-Real.log (1 - (χ (p : ℕ)).re * ((p : ℕ) : ℝ) ^ (-s)) : ℝ) : ℂ) := by
    intro p
    have hp : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
    have hpow : ((p : ℕ) : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    have hpow0 : 0 < ((p : ℕ) : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
    obtain ⟨him, hnorm⟩ := hχ ((p : ℕ) : ZMod N)
    have hre : |(χ (p : ℕ)).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) hnorm
    have hpos : 0 < 1 - (χ (p : ℕ)).re * ((p : ℕ) : ℝ) ^ (-s) := by
      have : |(χ (p : ℕ)).re * ((p : ℕ) : ℝ) ^ (-s)| < 1 := by
        rw [abs_mul, abs_of_pos hpow0]
        calc |(χ (p : ℕ)).re| * ((p : ℕ) : ℝ) ^ (-s) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s) :=
              mul_le_mul_of_nonneg_right hre hpow0.le
          _ < 1 := by linarith
      have := (abs_lt.mp this).2
      linarith
    have hχp : χ (p : ℕ) = ((χ (p : ℕ)).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hcpow : (p : ℂ) ^ (-(s : ℂ)) = ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast; rfl
    rw [hχp, hcpow, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log hpos.le, Complex.ofReal_neg, Complex.ofReal_re]
  simp_rw [hterm] at h
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp] at h
  exact ⟨_, Real.exp_pos _, h.symm⟩

/-- `gsum (d m) (d N) = d gsum m N`. -/
lemma gsum_mul_left (d m N : ℕ) (hd : 0 < d) : gsum (d * m) (d * N) = d * gsum m N := by
  unfold gsum
  have h1 : ∀ k, e (d * N) (d * m * k ^ 2) = e N (m * k ^ 2) := by
    intro k
    rw [mul_assoc, e_mul_right _ _ _ hd]
  simp_rw [h1]
  clear h1
  induction d with
  | zero => simp at hd
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd'
    · simp
    · rw [add_mul, one_mul, Finset.sum_range_add, ih hd']
      have : ∀ k, e N (m * (d * N + k) ^ 2) = e N (m * k ^ 2) := by
        intro k
        rw [show m * (d * N + k) ^ 2 = m * k ^ 2 + N * (m * (d * d * N + 2 * d * k)) by ring, e_mul_add]
      simp_rw [this]
      push_cast; ring

lemma norm_gsum_le (m N : ℕ) : ‖gsum m N‖ ≤ N := by
  unfold gsum
  calc ‖∑ k ∈ range N, e N (m * k ^ 2)‖ ≤ ∑ k ∈ range N, ‖e N (m * k ^ 2)‖ := norm_sum_le _ _
    _ = N := by
      have : ∀ k, ‖e N (m * k ^ 2)‖ = 1 := by
        intro k; unfold e
        rw [show (2 * π * I * ((m * k ^ 2 : ℕ) : ℂ) / N) = ((2 * π * (m * k ^ 2 : ℕ) / N : ℝ) : ℂ) * I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
      simp [this]

/-- The periodic function `Φ`. -/
noncomputable def Φ (n : ℕ) (m : ℕ) : ℂ := ((gsum m n).im : ℂ)

lemma Φ_bound (n m : ℕ) : ‖Φ n m‖ ≤ n := by
  unfold Φ
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (Complex.abs_im_le_norm _) (norm_gsum_le m n)

/-- The gcd-piece. -/
noncomputable def Φd (n d : ℕ) (m : ℕ) : ℂ := if Nat.gcd m n = d then Φ n m else 0

lemma Φ_eq_sum_Φd (n : ℕ) (hn : 0 < n) : Φ n = ∑ d ∈ n.divisors, Φd n d := by
  ext m
  simp only [Finset.sum_apply, Φd]
  rw [Finset.sum_ite_eq n.divisors (Nat.gcd m n) (fun _ => Φ n m)]
  rw [if_pos (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hn.ne'⟩)]

lemma Φd_bound (n d m : ℕ) : ‖Φd n d m‖ ≤ n := by
  unfold Φd; split_ifs
  · exact Φ_bound n m
  · simp

/-- Summing nonneg reals in `ℂ`. -/
lemma sum_ofReal_nonneg {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ S, ∃ r : ℝ, 0 ≤ r ∧ f i = r) : ∃ r : ℝ, 0 ≤ r ∧ ∑ i ∈ S, f i = r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, le_refl _, by simp⟩
  | insert a S ha ih =>
    obtain ⟨r, hr, hfr⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨r', hr', hfr'⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨r + r', by positivity, ?_⟩
    rw [Finset.sum_insert ha, hfr, hfr']; push_cast; rfl

/-- The L-series of one gcd-piece is a nonnegative real. -/
lemma LSeries_Φd_nonneg (n d : ℕ) (hn : 0 < n) (hd : d ∈ n.divisors) (s : ℝ) (hs : 1 < s) :
    ∃ r : ℝ, 0 ≤ r ∧ LSeries (Φd n d) (s : ℂ) = r := by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hd
  obtain ⟨N', rfl⟩ := hdn
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hN0 : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨c, χ, hc, hχ, hval⟩ := gsum_im_structure N' hN0
  obtain ⟨r, hr, hL⟩ := LSeries_char_pos χ hχ s hs
  -- reindex
  have hinj : Function.Injective (fun m' : ℕ => d * m') := fun a b h => by
    simpa [hd0.ne'] using h
  have hsupp : Function.support (LSeries.term (Φd (d * N') d) (s : ℂ)) ⊆ Set.range (fun m' : ℕ => d * m') := by
    intro m hm
    rw [Function.mem_support] at hm
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    rw [LSeries.term_of_ne_zero hm0] at hm
    have : Φd (d * N') d m ≠ 0 := by
      intro h; apply hm; rw [h, zero_div]
    unfold Φd at this
    split_ifs at this with hg
    · exact ⟨m / d, by
        have : d ∣ m := hg ▸ Nat.gcd_dvd_left m (d * N')
        exact Nat.mul_div_cancel' this⟩
    · exact absurd rfl this
  unfold LSeries
  rw [← hinj.tsum_eq hsupp]
  -- the term formula
  set K : ℝ := (d : ℝ) * ((d : ℝ) ^ s)⁻¹ with hK
  have hKpos : 0 < K := by positivity
  have hterm : ∀ m' : ℕ, LSeries.term (Φd (d * N') d) (s : ℂ) (d * m')
      = (K : ℂ) * c * LSeries.term (↗χ) (s : ℂ) m' := by
    intro m'
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · simp
    have hdm : d * m' ≠ 0 := by positivity
    rw [LSeries.term_of_ne_zero hdm, LSeries.term_of_ne_zero hm'.ne']
    have hΦ : Φd (d * N') d (d * m') = d * c * χ (m' : ZMod N') := by
      unfold Φd
      rw [Nat.gcd_mul_left]
      by_cases hcop : Nat.Coprime m' N'
      · rw [if_pos (by rw [hcop, mul_one]), Φ, gsum_mul_left d m' N' hd0]
        rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
        push_cast
        rw [hval m' hcop]; ring
      · rw [if_neg (by
          intro h
          have : Nat.gcd m' N' = 1 := by
            have := Nat.eq_of_mul_eq_mul_left hd0 (h.trans (mul_one d).symm)
            exact this
          exact hcop this)]
        rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
        simp
    rw [hΦ]
    have hcast : ((d * m' : ℕ) : ℂ) ^ (s : ℂ) = (d : ℂ) ^ (s : ℂ) * (m' : ℂ) ^ (s : ℂ) := by
      push_cast
      rw [← Complex.ofReal_natCast d, ← Complex.ofReal_natCast m',
        Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    rw [hcast]
    have hds : (d : ℂ) ^ (s : ℂ) = (((d : ℝ) ^ s : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
    have hd1 : (d : ℂ) ^ (s : ℂ) ≠ 0 := by
      rw [hds]; exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hd0) s).ne'
    have hm1 : (m' : ℂ) ^ (s : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (m' : ℝ) ^ s := Real.rpow_pos_of_pos (by exact_mod_cast hm') s
      rw [show (m' : ℂ) = ((m' : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity)]
      exact_mod_cast this.ne'
    rw [hK, hds]
    push_cast
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left]
  refine ⟨K * c * r, by positivity, ?_⟩
  unfold LSeries at hL
  rw [hL]; push_cast; ring

/-- `LSeries Φ s` is a nonnegative real for real `s > 1`. -/
theorem LSeries_Φ_nonneg (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 1 < s) :
    ∃ r : ℝ, 0 ≤ r ∧ LSeries (Φ n) (s : ℂ) = r := by
  rw [Φ_eq_sum_Φd n hn, LSeries_sum (fun d _ =>
    LSeriesSummable_of_bounded_of_one_lt_real (fun m _ => Φd_bound n d m) hs)]
  exact sum_ofReal_nonneg _ _ (fun d hd => LSeries_Φd_nonneg n d hn hd s hs)

end GaussSum

end LPosSec

section FinalSec

open Complex Finset Filter Topology
open scoped Real

namespace GaussSum

variable {n : ℕ} [NeZero n]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod n) ℂ)

/-- The odd periodic function. -/
noncomputable def Φ' (n : ℕ) [NeZero n] : ZMod n → ℂ :=
  fun j => ∑ k : ZMod n, (((ZMod.stdAddChar : AddChar (ZMod n) ℂ) (j * k ^ 2)).im : ℂ)

lemma Φ'_odd : (Φ' n).Odd := by
  intro j
  unfold Φ'
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_mul, ← GaussSchur.conj_stdAddChar, Complex.conj_im]
  push_cast; ring

lemma Φ'_sum_zero : ∑ j : ZMod n, Φ' n j = 0 := by
  have h := Φ'_odd (n := n)
  have : ∑ j : ZMod n, Φ' n j = ∑ j : ZMod n, Φ' n (-j) :=
    (Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by simp)).symm
  have h2 : ∑ j : ZMod n, Φ' n (-j) = -∑ j : ZMod n, Φ' n j := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun j _ => h j)
  linear_combination (this + h2) / 2

lemma Φ'_natCast (m : ℕ) : Φ' n (m : ZMod n) = Φ n m := by
  unfold Φ' Φ
  rw [gsum_eq_sum_zmod, Complex.im_sum]
  push_cast
  rfl

lemma Φ'_zero : Φ' n 0 = 0 := by
  have := Φ'_natCast (n := n) 0
  rw [Nat.cast_zero] at this
  rw [this]; unfold Φ; simp [gsum, e_zero]

/-- `LFunction Φ' 1` is a nonnegative real. -/
theorem LFunction_one_nonneg : ∃ r : ℝ, 0 ≤ r ∧ ZMod.LFunction (Φ' n) 1 = r := by
  have hn : 0 < n := NeZero.pos n
  have hcont : Tendsto (fun s : ℝ => ZMod.LFunction (Φ' n) (s : ℂ)) (𝓝[>] 1)
      (𝓝 (ZMod.LFunction (Φ' n) 1)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have := ((ZMod.differentiable_LFunction_of_sum_zero (Φ'_sum_zero (n := n))).continuous.comp
      Complex.continuous_ofReal).tendsto 1
    simpa using this
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.re ∧ z.im = 0} := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const Complex.continuous_re
    · exact isClosed_eq Complex.continuous_im continuous_const
  have hmem : ZMod.LFunction (Φ' n) 1 ∈ {z : ℂ | 0 ≤ z.re ∧ z.im = 0} := by
    apply hclosed.mem_of_tendsto hcont
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (1 : ℝ) < s := hs
    rw [ZMod.LFunction_eq_LSeries _ (by simpa using hs')]
    have : (fun m : ℕ => Φ' n (m : ZMod n)) = Φ n := funext Φ'_natCast
    rw [this]
    obtain ⟨r, hr, hL⟩ := LSeries_Φ_nonneg n hn s hs'
    rw [hL]; simp [hr]
  refine ⟨(ZMod.LFunction (Φ' n) 1).re, hmem.1, ?_⟩
  apply Complex.ext <;> simp [hmem.2]

/-- Express `LFunction Φ' 1` through cotangents. -/
theorem LFunction_one_eq :
    ZMod.LFunction (Φ' n) 1 =
      (n : ℂ)⁻¹ * (π / 2) * ∑ m ∈ range n, Φ n m * (Real.cot (π * m / n) : ℂ) := by
  rw [ZMod.LFunction_def_odd Φ'_odd, cpow_neg_one]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_range, ← Fintype.sum_equiv GaussSchur.finZMod _ _ (fun i => rfl)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : ℕ) = 0
  · have : GaussSchur.finZMod i = 0 := by
      rw [GaussSchur.finZMod_apply, hi]; simp
    rw [this, Φ'_zero, zero_mul, ← Φ'_natCast, hi]
    simp [Φ'_zero]
  · have hval : (GaussSchur.finZMod i).val = i := by
      rw [GaussSchur.finZMod_apply, ZMod.val_natCast_of_lt i.isLt]
    rw [ZMod.toAddCircle_apply, hval, GaussSchur.finZMod_apply, Φ'_natCast]
    have hpos : (0 : ℝ) < (i : ℕ) / n := by
      have : (0 : ℝ) < (i : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hi
      have : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
      positivity
    have hlt : ((i : ℕ) : ℝ) / n < 1 := by
      rw [div_lt_one (by exact_mod_cast NeZero.pos n)]
      exact_mod_cast i.isLt
    rw [HurwitzOne.hurwitzZetaOdd_one _ hpos hlt]
    have : (π * ((i : ℕ) : ℝ) / n : ℝ) = π * (((i : ℕ) : ℝ) / n) := by ring
    rw [this, Complex.ofReal_cot]
    push_cast
    ring

/-- The sawtooth. -/
noncomputable def saw (n x : ℕ) : ℝ := if n ∣ x then 0 else ((x % n : ℕ) : ℝ) / n - 1 / 2

omit [NeZero n] in
lemma im_gsum (m : ℕ) : (gsum m n).im = ∑ k ∈ range n, Real.sin (2 * π * m * (k ^ 2 : ℕ) / n) := by
  unfold gsum
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold e
  rw [show (2 * π * I * ((m * k ^ 2 : ℕ) : ℂ) / n) = ((2 * π * m * (k ^ 2 : ℕ) / n : ℝ) : ℂ) * I by
    push_cast; ring, Complex.exp_ofReal_mul_I_im]

lemma saw_eq (k : ℕ) :
    saw n (k ^ 2) = -(1 / (2 * n)) *
      ∑ m ∈ range n, Real.sin (2 * π * m * (k ^ 2 : ℕ) / n) * Real.cot (π * m / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  set x := k ^ 2 % n with hx
  have hper : ∀ m : ℕ, Real.sin (2 * π * m * (k ^ 2 : ℕ) / n) = Real.sin (2 * π * m * x / n) := by
    intro m
    have : (2 * π * m * (k ^ 2 : ℕ) / n : ℝ) = 2 * π * m * x / n + ((m * (k ^ 2 / n) : ℕ) : ℝ) * (2 * π) := by
      conv_lhs => rw [← Nat.mod_add_div (k ^ 2) n]
      push_cast
      field_simp
      ring
    rw [this, Real.sin_add_nat_mul_two_pi]
  simp_rw [hper]
  unfold saw
  by_cases hdvd : n ∣ k ^ 2
  · rw [if_pos hdvd]
    have : x = 0 := by rw [hx]; exact Nat.mod_eq_zero_of_dvd hdvd
    rw [this]; simp
  · rw [if_neg hdvd]
    have hx0 : 0 < x := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
    have hxn : x < n := Nat.mod_lt _ (NeZero.pos n)
    rw [TrigId.sum_sin_cot n x hx0 hxn]
    field_simp
    ring

/-- The key inequality: `∑ saw(k²) ≤ 0`. -/
theorem sum_saw_nonpos : ∑ k ∈ range n, saw n (k ^ 2) ≤ 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  simp_rw [saw_eq]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hΦ : ∀ m ∈ range n, ∑ k ∈ range n, Real.sin (2 * π * m * (k ^ 2 : ℕ) / n) * Real.cot (π * m / n)
      = (gsum m n).im * Real.cot (π * m / n) := by
    intro m _
    rw [im_gsum, Finset.sum_mul]
  rw [Finset.sum_congr rfl hΦ]
  -- relate to LFunction
  obtain ⟨r, hr, hL⟩ := LFunction_one_nonneg (n := n)
  have key : (∑ m ∈ range n, (gsum m n).im * Real.cot (π * m / n) : ℝ) = 2 * n / π * r := by
    have h1 := LFunction_one_eq (n := n)
    rw [hL] at h1
    have h2 : ((∑ m ∈ range n, (gsum m n).im * Real.cot (π * m / n) : ℝ) : ℂ)
        = ∑ m ∈ range n, Φ n m * (Real.cot (π * m / n) : ℂ) := by
      push_cast; rfl
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have : ((2 * n / π * r : ℝ) : ℂ) = ∑ m ∈ range n, Φ n m * (Real.cot (π * m / n) : ℂ) := by
      have e : ((2 * n / π * r : ℝ) : ℂ) = 2 * (n : ℂ) / (π : ℂ) * (r : ℂ) := by push_cast; rfl
      rw [e, h1]; field_simp
    exact_mod_cast (h2.trans this.symm)
  rw [key]
  have : 0 ≤ 2 * n / π * r := by positivity
  have h3 : 0 ≤ 1 / (2 * (n : ℝ)) := by positivity
  nlinarith [this, h3]

end GaussSum

end FinalSec

section MainSec

open Finset
open scoped Real


namespace GaussSum

lemma mod_eq_saw (n : ℕ) [NeZero n] (k : ℕ) :
    ((k ^ 2 % n : ℕ) : ℝ) = n * saw n (k ^ 2) + (if n ∣ k ^ 2 then 0 else (n : ℝ) / 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  unfold saw
  split_ifs with h
  · rw [Nat.mod_eq_zero_of_dvd h]; simp
  · field_simp; ring

lemma sum_ite_le (n : ℕ) [NeZero n] :
    ∑ k ∈ range n, (if n ∣ k ^ 2 then (0 : ℝ) else (n : ℝ) / 2) ≤ (n - 1) * ((n : ℝ) / 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  calc ∑ k ∈ range n, (if n ∣ k ^ 2 then (0 : ℝ) else (n : ℝ) / 2)
      ≤ ∑ k ∈ range n, (if k = 0 then (0 : ℝ) else (n : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k = 0
        · subst hk; simp
        · rw [if_neg hk]; split_ifs <;> linarith
    _ = (n - 1) * ((n : ℝ) / 2) := by
        obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
        rw [hn', Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, if_true, add_zero, Finset.sum_const, card_range,
          nsmul_eq_mul]
        push_cast; ring

theorem A048153_le (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ n * (n - 1) / 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have hreal : ((A048153 n : ℕ) : ℝ) ≤ n * (n - 1) / 2 := by
    unfold A048153
    push_cast
    simp_rw [mod_eq_saw n]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := sum_saw_nonpos (n := n)
    have h2 := sum_ite_le n
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have h2 : (A048153 n : ℝ) * 2 ≤ n * (n - 1) := by linarith
  have h3 : A048153 n * 2 ≤ n * (n - 1) := by
    have : ((A048153 n * 2 : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub h]; linarith
    exact_mod_cast this
  omega

end GaussSum

end MainSec

/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  have h1 := GaussSum.A048153_le n h
  have h2 : n * (n - 1) ≤ n ^ 2 - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 = (m + 1) * m + (m + 1) := by ring
    omega
  exact le_trans h1 (Nat.div_le_div_right h2)

theorem oeis_48153_conjecture_0.disproof : ¬ (type_of% @oeis_48153_conjecture_0) := sorry
