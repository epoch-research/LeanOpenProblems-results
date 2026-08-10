import FormalConjectures.Util.ProblemImports
open Nat Finset Matrix
open scoped Matrix

namespace BridgeDev

variable {N : ℕ}

theorem permanent_diagonal_mul (d : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.diagonal d * A).permanent = (∏ i, d i) * A.permanent := by
  simp only [Matrix.permanent]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have h1 : ∀ i, (Matrix.diagonal d * A) (σ i) i = d (σ i) * A (σ i) i := by
    intro i; rw [Matrix.mul_apply]; simp [Matrix.diagonal]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ d]

theorem det_diagonal_mul (d : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.diagonal d * A).det = (∏ i, d i) * A.det := by
  rw [Matrix.det_mul, Matrix.det_diagonal]

-- Permanent cofactor (Laplace) expansion along column 0, analog of det_succ_column_zero.
theorem permanent_succ_column_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    A.permanent = ∑ i : Fin n.succ,
      A i 0 * (A.submatrix (fun j => Equiv.swap 0 i (Fin.succ j)) Fin.succ).permanent := by
  simp only [Matrix.permanent]
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    of_apply]

-- Permanent Laplace expansion along row 0 (transpose of column version).
theorem permanent_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    A.permanent = ∑ j : Fin n.succ,
      A 0 j * (A.submatrix Fin.succ (fun k => Equiv.swap 0 j (Fin.succ k))).permanent := by
  rw [← Matrix.permanent_transpose A, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.permanent_transpose]
  congr 1

-- Pairing recursion: for a matrix with zero diagonal, expanding along column 0 then
-- locating row 0 in each minor. Structural step toward per(G)=(-1)^n det(G).
-- We work toward: per G = ∑_{a≠0} G 0 a * G a 0 * per(delete {0,a}) + (offdiagonal which vanishes).

-- The embedding deleting elements 0 and (a.succ) from Fin (n+2): j ↦ (a.succAbove j).succ
def delZeroSucc {n : ℕ} (a : Fin (n+1)) : Fin n → Fin (n+2) := fun j => (a.succAbove j).succ

theorem delZeroSucc_inj {n : ℕ} (a : Fin (n+1)) : Function.Injective (delZeroSucc a) := by
  intro x y h
  simp only [delZeroSucc] at h
  exact a.succAbove_right_injective (Fin.succ_injective _ h)

theorem delZeroSucc_ne_zero {n : ℕ} (a : Fin (n+1)) (j : Fin n) : delZeroSucc a j ≠ 0 := by
  simp [delZeroSucc, Fin.succ_ne_zero]

section DecomposeOption
variable {α : Type*} [Fintype α] [DecidableEq α]

-- Permanent expanded via the insertion bijection decomposeOption.
theorem permanent_decomposeOption (G : Matrix (Option α) (Option α) ℂ) :
    G.permanent = ∑ p : Option α × Equiv.Perm α,
      ∏ i, G (Equiv.Perm.decomposeOption.symm p i) i := by
  rw [Matrix.permanent, Finset.univ_perm_option, Finset.sum_map]
  rfl

-- The product for the σ = decomposeOption.symm (some a₀, τ) summand: element `none` (the special
-- point) pairs with `some a₀` on one side and `some (τ.symm a₀)` on the other.
theorem prod_decomposeOption_some (G : Matrix (Option α) (Option α) ℂ) (a₀ : α)
    (τ : Equiv.Perm α) :
    (∏ i, G (Equiv.Perm.decomposeOption.symm (some a₀, τ) i) i)
      = G (some a₀) none * G none (some (τ.symm a₀))
        * ∏ x ∈ univ.erase (τ.symm a₀), G (some (τ x)) (some x) := by
  rw [Fintype.prod_option]
  have hnone : Equiv.Perm.decomposeOption.symm (some a₀, τ) none = some a₀ := by
    simp [Equiv.Perm.decomposeOption]
  rw [hnone]
  have hsucc : ∀ x : α, Equiv.Perm.decomposeOption.symm (some a₀, τ) (some x)
      = Equiv.swap none (some a₀) (some (τ x)) := by
    intro x; simp [Equiv.Perm.decomposeOption]
  simp_rw [hsucc]
  rw [mul_assoc]
  congr 1
  have hx0 : (τ.symm a₀) ∈ (univ : Finset α) := mem_univ _
  rw [← Finset.mul_prod_erase univ _ hx0]
  congr 1
  · have : τ (τ.symm a₀) = a₀ := τ.apply_symm_apply a₀
    rw [this, Equiv.swap_apply_right]
  · refine Finset.prod_congr rfl (fun x hx => ?_)
    rw [Finset.mem_erase] at hx
    have hne : τ x ≠ a₀ := by
      intro h; apply hx.1; rw [← h]; exact (τ.symm_apply_apply x).symm
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hne])]

-- The a = none summand.
theorem prod_decomposeOption_none (G : Matrix (Option α) (Option α) ℂ) (τ : Equiv.Perm α) :
    (∏ i, G (Equiv.Perm.decomposeOption.symm (none, τ) i) i)
      = G none none * ∏ x, G (some (τ x)) (some x) := by
  rw [Fintype.prod_option]
  simp [Equiv.Perm.decomposeOption]

-- The permanent of the principal minor obtained by deleting index `b` equals the sum over
-- permutations of `α` fixing `b` of the product over the remaining indices.
theorem permanent_minor_eq_sum_fix (D : Matrix α α ℂ) (b : α) :
    (D.submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).permanent
      = ∑ τ ∈ univ.filter (fun τ : Equiv.Perm α => τ b = b),
          ∏ x ∈ univ.erase b, D (τ x) x := by
  rw [Matrix.permanent]
  apply Finset.sum_bij (fun (g : Equiv.Perm {x // x ≠ b}) _ => Equiv.Perm.ofSubtype g)
  · intro g _
    rw [Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp)
  · intro g1 _ g2 _ h
    exact Equiv.Perm.ofSubtype_injective h
  · intro τ hτ
    rw [Finset.mem_filter] at hτ
    have hpres : ∀ x, (τ x ≠ b) ↔ (x ≠ b) := by
      intro x
      constructor
      · intro hx hxb; apply hx; rw [hxb]; exact hτ.2
      · intro hx hτx; apply hx; have := τ.injective (a₁ := x) (a₂ := b); apply this; rw [hτx, hτ.2]
    refine ⟨τ.subtypePerm hpres, mem_univ _, ?_⟩
    apply Equiv.Perm.ext
    intro x
    by_cases hx : x = b
    · rw [hx, Equiv.Perm.ofSubtype_subtypePerm_of_not_mem (p := fun y => y ≠ b) (g := τ) hpres
          (by simp)]
      exact hτ.2.symm
    · rw [Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun y => y ≠ b) (g := τ) hpres hx]
  · intro g _
    simp only [Matrix.submatrix_apply]
    rw [Finset.prod_subtype (p := fun x => x ≠ b) (univ.erase b)
          (fun x => by simp [Finset.mem_erase])
          (fun x => D (Equiv.Perm.ofSubtype g x) x)]
    refine Finset.prod_congr rfl (fun y _ => ?_)
    rw [Equiv.Perm.ofSubtype_apply_of_mem g y.2]

-- Step 1 toward the pairing recursion: rewrite the permanent of a matrix with `G none none = 0`
-- as a double sum over `τ : Perm α` and `b : α`.
theorem permanent_eq_sum_tau_b (G : Matrix (Option α) (Option α) ℂ)
    (hnn : G none none = 0) :
    G.permanent = ∑ τ : Equiv.Perm α, ∑ b : α,
      G (some (τ b)) none * G none (some b)
        * ∏ x ∈ univ.erase b, G (some (τ x)) (some x) := by
  rw [permanent_decomposeOption, Fintype.sum_prod_type, Fintype.sum_option]
  have hnone : (∑ τ : Equiv.Perm α, ∏ i, G (Equiv.Perm.decomposeOption.symm (none, τ) i) i) = 0 := by
    apply Finset.sum_eq_zero
    intro τ _
    rw [prod_decomposeOption_none, hnn, zero_mul]
  rw [hnone, zero_add]
  simp_rw [prod_decomposeOption_some]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← Equiv.sum_comp τ (fun a₀ => G (some a₀) none * G none (some (τ.symm a₀))
        * ∏ x ∈ univ.erase (τ.symm a₀), G (some (τ x)) (some x))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Equiv.symm_apply_apply]

-- The permanent pairing recursion for a zero-diagonal, skew, three-term ("Cauchy-type") matrix.
theorem permanent_pairing (G : Matrix (Option α) (Option α) ℂ)
    (hnn : G none none = 0)
    (hsk : ∀ p : α, G (some p) none = - G none (some p))
    (h3 : ∀ p q : α, p ≠ q → G (some p) none * G none (some q)
            = G (some p) (some q) * (G (some p) none + G none (some q))) :
    G.permanent = ∑ b : α, G (some b) none * G none (some b) *
      ((G.submatrix some some).submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).permanent := by
  classical
  have step : G.permanent = ∑ τ : Equiv.Perm α,
      ((∑ b ∈ univ.filter (fun b => τ b = b),
          G (some (τ b)) none * G none (some b)
            * ∏ x ∈ univ.erase b, G (some (τ x)) (some x))
        + (∑ b ∈ univ.filter (fun b => ¬ τ b = b),
          G (some (τ b)) none * G none (some b)
            * ∏ x ∈ univ.erase b, G (some (τ x)) (some x))) := by
    rw [permanent_eq_sum_tau_b G hnn]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [step, Finset.sum_add_distrib]
  -- The `τ b ≠ b` part vanishes.
  have hzero : (∑ τ : Equiv.Perm α, ∑ b ∈ univ.filter (fun b => ¬ τ b = b),
      G (some (τ b)) none * G none (some b)
        * ∏ x ∈ univ.erase b, G (some (τ x)) (some x)) = 0 := by
    apply Finset.sum_eq_zero
    intro τ _
    have hterm : ∀ b ∈ univ.filter (fun b => ¬ τ b = b),
        G (some (τ b)) none * G none (some b)
          * ∏ x ∈ univ.erase b, G (some (τ x)) (some x)
        = (∏ x, G (some (τ x)) (some x)) * (G (some (τ b)) none + G none (some b)) := by
      intro b hb
      rw [Finset.mem_filter] at hb
      rw [h3 (τ b) b hb.2,
          ← Finset.mul_prod_erase univ (fun x => G (some (τ x)) (some x)) (mem_univ b)]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hfilt : (∑ b ∈ univ.filter (fun b => ¬ τ b = b),
        (G (some (τ b)) none + G none (some b)))
        = ∑ b : α, (G (some (τ b)) none + G none (some b)) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b _ hb
      simp only [Finset.mem_filter, mem_univ, true_and, not_not] at hb
      rw [hb, hsk b]; ring
    have hfull : (∑ b : α, (G (some (τ b)) none + G none (some b))) = 0 := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp τ (fun b => G (some b) none),
          ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro b _
      rw [hsk b]; ring
    rw [hfilt, hfull, mul_zero]
  rw [hzero, add_zero]
  -- The `τ b = b` part equals the right-hand side.
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (univ : Finset α)) => by
      rw [permanent_minor_eq_sum_fix (G.submatrix some some) b, Finset.mul_sum])]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun τ _ => ?_))
  by_cases hb : τ b = b
  · simp only [hb, Matrix.submatrix_apply]
  · simp only [if_neg hb]

/-! ### Determinant analogues -/

theorem sign_decomposeOption_symm_some (a₀ : α) (τ : Equiv.Perm α) :
    Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm (some a₀, τ))
      = - Equiv.Perm.sign τ := by
  have h : Equiv.Perm.decomposeOption.symm (some a₀, τ)
      = Equiv.swap none (some a₀) * τ.optionCongr := rfl
  rw [h, map_mul, Equiv.Perm.sign_swap (by simp), Equiv.optionCongr_sign]
  simp

theorem det_decomposeOption (G : Matrix (Option α) (Option α) ℂ) :
    G.det = ∑ p : Option α × Equiv.Perm α,
      Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm p)
        • ∏ i, G (Equiv.Perm.decomposeOption.symm p i) i := by
  rw [Matrix.det_apply, Finset.univ_perm_option, Finset.sum_map]
  rfl

theorem det_minor_eq_sum_fix (D : Matrix α α ℂ) (b : α) :
    (D.submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).det
      = ∑ τ ∈ univ.filter (fun τ : Equiv.Perm α => τ b = b),
          Equiv.Perm.sign τ • ∏ x ∈ univ.erase b, D (τ x) x := by
  rw [Matrix.det_apply]
  apply Finset.sum_bij (fun (g : Equiv.Perm {x // x ≠ b}) _ => Equiv.Perm.ofSubtype g)
  · intro g _
    rw [Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp)
  · intro g1 _ g2 _ h
    exact Equiv.Perm.ofSubtype_injective h
  · intro τ hτ
    rw [Finset.mem_filter] at hτ
    have hpres : ∀ x, (τ x ≠ b) ↔ (x ≠ b) := by
      intro x
      constructor
      · intro hx hxb; apply hx; rw [hxb]; exact hτ.2
      · intro hx hτx; apply hx; have := τ.injective (a₁ := x) (a₂ := b); apply this; rw [hτx, hτ.2]
    refine ⟨τ.subtypePerm hpres, mem_univ _, ?_⟩
    apply Equiv.Perm.ext
    intro x
    by_cases hx : x = b
    · rw [hx, Equiv.Perm.ofSubtype_subtypePerm_of_not_mem (p := fun y => y ≠ b) (g := τ) hpres
          (by simp)]
      exact hτ.2.symm
    · rw [Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun y => y ≠ b) (g := τ) hpres hx]
  · intro g _
    rw [Equiv.Perm.sign_ofSubtype]
    congr 1
    simp only [Matrix.submatrix_apply]
    rw [Finset.prod_subtype (p := fun x => x ≠ b) (univ.erase b)
          (fun x => by simp [Finset.mem_erase])
          (fun x => D (Equiv.Perm.ofSubtype g x) x)]
    refine Finset.prod_congr rfl (fun y _ => ?_)
    rw [Equiv.Perm.ofSubtype_apply_of_mem g y.2]

theorem neg_units_smul (u : ℤˣ) (x : ℂ) : (-u) • x = -(u • x) := by
  rw [Units.smul_def, Units.smul_def, Units.val_neg, neg_smul]

theorem det_eq_sum_tau_b (G : Matrix (Option α) (Option α) ℂ) (hnn : G none none = 0) :
    G.det = - ∑ τ : Equiv.Perm α, Equiv.Perm.sign τ • ∑ b : α,
      G (some (τ b)) none * G none (some b)
        * ∏ x ∈ univ.erase b, G (some (τ x)) (some x) := by
  rw [det_decomposeOption, Fintype.sum_prod_type, Fintype.sum_option]
  have hnone : (∑ τ : Equiv.Perm α,
      Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm (none, τ))
        • ∏ i, G (Equiv.Perm.decomposeOption.symm (none, τ) i) i) = 0 := by
    apply Finset.sum_eq_zero
    intro τ _
    rw [prod_decomposeOption_none, hnn, zero_mul, smul_zero]
  rw [hnone, zero_add]
  simp_rw [sign_decomposeOption_symm_some, prod_decomposeOption_some, neg_units_smul]
  rw [Finset.sum_comm]
  have hrhs : (- ∑ τ : Equiv.Perm α, Equiv.Perm.sign τ • ∑ b : α,
      G (some (τ b)) none * G none (some b) * ∏ x ∈ univ.erase b, G (some (τ x)) (some x))
      = ∑ τ : Equiv.Perm α, ∑ b : α,
        -(Equiv.Perm.sign τ • (G (some (τ b)) none * G none (some b)
          * ∏ x ∈ univ.erase b, G (some (τ x)) (some x))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  rw [hrhs]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← Equiv.sum_comp τ (fun a₀ => -(Equiv.Perm.sign τ • (G (some a₀) none * G none (some (τ.symm a₀))
        * ∏ x ∈ univ.erase (τ.symm a₀), G (some (τ x)) (some x))))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Equiv.symm_apply_apply]

-- The determinant pairing recursion (sign-flipped analogue of `permanent_pairing`).
theorem det_pairing (G : Matrix (Option α) (Option α) ℂ)
    (hnn : G none none = 0)
    (hsk : ∀ p : α, G (some p) none = - G none (some p))
    (h3 : ∀ p q : α, p ≠ q → G (some p) none * G none (some q)
            = G (some p) (some q) * (G (some p) none + G none (some q))) :
    G.det = - ∑ b : α, G (some b) none * G none (some b) *
      ((G.submatrix some some).submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).det := by
  classical
  rw [det_eq_sum_tau_b G hnn]
  have hcancel : ∀ τ : Equiv.Perm α,
      (∑ b ∈ univ.filter (fun b => ¬ τ b = b),
        G (some (τ b)) none * G none (some b)
          * ∏ x ∈ univ.erase b, G (some (τ x)) (some x)) = 0 := by
    intro τ
    have hterm : ∀ b ∈ univ.filter (fun b => ¬ τ b = b),
        G (some (τ b)) none * G none (some b) * ∏ x ∈ univ.erase b, G (some (τ x)) (some x)
        = (∏ x, G (some (τ x)) (some x)) * (G (some (τ b)) none + G none (some b)) := by
      intro b hb
      rw [Finset.mem_filter] at hb
      rw [h3 (τ b) b hb.2,
          ← Finset.mul_prod_erase univ (fun x => G (some (τ x)) (some x)) (mem_univ b)]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hfilt : (∑ b ∈ univ.filter (fun b => ¬ τ b = b),
        (G (some (τ b)) none + G none (some b)))
        = ∑ b : α, (G (some (τ b)) none + G none (some b)) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b _ hb
      simp only [Finset.mem_filter, mem_univ, true_and, not_not] at hb
      rw [hb, hsk b]; ring
    have hfull : (∑ b : α, (G (some (τ b)) none + G none (some b))) = 0 := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp τ (fun b => G (some b) none),
          ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro b _
      rw [hsk b]; ring
    rw [hfilt, hfull, mul_zero]
  have step : (∑ τ : Equiv.Perm α, Equiv.Perm.sign τ • ∑ b : α,
        G (some (τ b)) none * G none (some b) * ∏ x ∈ univ.erase b, G (some (τ x)) (some x))
      = ∑ τ : Equiv.Perm α, Equiv.Perm.sign τ • ∑ b ∈ univ.filter (fun b => τ b = b),
          G (some (τ b)) none * G none (some b) * ∏ x ∈ univ.erase b, G (some (τ x)) (some x) := by
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun b => τ b = b), hcancel τ, add_zero]
  rw [step]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (univ : Finset α)) => by
      rw [det_minor_eq_sum_fix (G.submatrix some some) b, Finset.mul_sum])]
  rw [neg_inj]
  simp_rw [Finset.smul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun τ _ => ?_))
  by_cases hb : τ b = b
  · simp only [hb, Matrix.submatrix_apply]
    rw [mul_smul_comm]
  · simp only [if_neg hb]

end DecomposeOption

theorem permanent_submatrix_equiv_self {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : n ≃ m) (A : Matrix m m ℂ) :
    (A.submatrix e e).permanent = A.permanent := by
  rw [Matrix.permanent, Matrix.permanent,
      ← Equiv.sum_comp (e.permCongr) (fun σ' : Equiv.Perm m => ∏ j, A (σ' j) j)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Equiv.prod_comp e (fun j => A ((e.permCongr σ) j) j)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [Matrix.submatrix_apply, Equiv.permCongr_apply]

-- For an even-sized, skew, three-term ("Cauchy-type") matrix, the permanent equals
-- `(-1)^m` times the determinant.
theorem permanent_eq_sign_det {m : ℕ} :
    ∀ {γ : Type} [Fintype γ] [DecidableEq γ] (M : Matrix γ γ ℂ),
      Fintype.card γ = 2 * m →
      (∀ i j, M i j = - M j i) →
      (∀ p q s, p ≠ s → s ≠ q → p ≠ q →
        M p s * M s q = M p q * (M p s + M s q)) →
      M.permanent = (-1) ^ m * M.det := by
  induction m with
  | zero =>
    intro γ _ _ M hcard _ _
    have hempty : IsEmpty γ := Fintype.card_eq_zero_iff.mp (by omega)
    rw [Matrix.permanent_isEmpty, Matrix.det_isEmpty]
    ring
  | succ m ih =>
    intro γ _ _ M hcard hskew h3
    have hne : Nonempty γ := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a⟩ := hne
    classical
    set e : Option {b : γ // b ≠ a} ≃ γ := Equiv.optionSubtypeNe a with he
    set M' : Matrix (Option {b : γ // b ≠ a}) (Option {b : γ // b ≠ a}) ℂ :=
      M.submatrix e e with hM'
    -- entries of M'
    have hM'some : ∀ (x y : {b : γ // b ≠ a}), M' (some x) (some y) = M x.1 y.1 := by
      intro x y; simp [hM', Matrix.submatrix_apply, he, Equiv.optionSubtypeNe_some]
    have hM'sn : ∀ (x : {b : γ // b ≠ a}), M' (some x) none = M x.1 a := by
      intro x; simp [hM', Matrix.submatrix_apply, he, Equiv.optionSubtypeNe_some,
        Equiv.optionSubtypeNe_none]
    have hM'ns : ∀ (x : {b : γ // b ≠ a}), M' none (some x) = M a x.1 := by
      intro x; simp [hM', Matrix.submatrix_apply, he, Equiv.optionSubtypeNe_some,
        Equiv.optionSubtypeNe_none]
    -- hypotheses for M'
    have hnn' : M' none none = 0 := by
      have : M' none none = M a a := by simp [hM', Matrix.submatrix_apply, he, Equiv.optionSubtypeNe_none]
      rw [this]; linear_combination (1/2 : ℂ) * hskew a a
    have hsk' : ∀ p : {b : γ // b ≠ a}, M' (some p) none = - M' none (some p) := by
      intro p; rw [hM'sn, hM'ns, hskew p.1 a]
    have h3' : ∀ p q : {b : γ // b ≠ a}, p ≠ q →
        M' (some p) none * M' none (some q)
          = M' (some p) (some q) * (M' (some p) none + M' none (some q)) := by
      intro p q hpq
      rw [hM'sn, hM'ns, hM'some]
      exact h3 p.1 q.1 a p.2 (fun h => q.2 h.symm) (fun h => hpq (Subtype.ext h))
    -- relate per/det of M to M'
    have hperM : M.permanent = M'.permanent := (permanent_submatrix_equiv_self e M).symm
    have hdetM : M.det = M'.det := (Matrix.det_submatrix_equiv_self e M).symm
    -- card of minors
    have hcardminor : ∀ b : {b : γ // b ≠ a},
        Fintype.card {x : {b : γ // b ≠ a} // x ≠ b} = 2 * m := by
      intro b
      have h1 : Fintype.card (Option {b : γ // b ≠ a}) = Fintype.card γ := Fintype.card_congr e
      have h2 : Fintype.card (Option {x : {b : γ // b ≠ a} // x ≠ b})
          = Fintype.card {b : γ // b ≠ a} := Fintype.card_congr (Equiv.optionSubtypeNe b)
      rw [Fintype.card_option] at h1 h2
      omega
    -- the minor matrices satisfy the hypotheses, so the IH applies
    rw [hperM, hdetM, permanent_pairing M' hnn' hsk' h3', det_pairing M' hnn' hsk' h3']
    have hIH : ∀ b : {b : γ // b ≠ a},
        ((M'.submatrix some some).submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).permanent
          = (-1) ^ m *
            ((M'.submatrix some some).submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).det := by
      intro b
      apply ih _ (hcardminor b)
      · intro i j
        simp only [Matrix.submatrix_apply, hM'some]
        exact hskew _ _
      · intro p q s hps hsq hpq
        simp only [Matrix.submatrix_apply, hM'some]
        refine h3 p.1.1 q.1.1 s.1.1 ?_ ?_ ?_
        · exact fun h => hps (Subtype.ext (Subtype.ext h))
        · exact fun h => hsq (Subtype.ext (Subtype.ext h))
        · exact fun h => hpq (Subtype.ext (Subtype.ext h))
    have hsum : (∑ b : {b : γ // b ≠ a}, M' (some b) none * M' none (some b) *
          ((M'.submatrix some some).submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).permanent)
        = (-1) ^ m * ∑ b : {b : γ // b ≠ a}, M' (some b) none * M' none (some b) *
            ((M'.submatrix some some).submatrix (fun y : {x // x ≠ b} => y.1) (fun y => y.1)).det := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hIH b]; ring
    rw [hsum, pow_succ]
    ring

-- A Cauchy matrix `M i j = 1/(f i - f j)` (off-diagonal), `0` on the diagonal, with `f` injective,
-- satisfies the skew and three-term hypotheses, hence `per = (-1)^m det`.
theorem permanent_cauchy_eq_sign_det {γ : Type} [Fintype γ] [DecidableEq γ] {m : ℕ}
    (hcard : Fintype.card γ = 2 * m) (f : γ → ℂ) (hf : Function.Injective f)
    (M : Matrix γ γ ℂ) (hMd : ∀ i, M i i = 0)
    (hM : ∀ i j, i ≠ j → M i j = 1 / (f i - f j)) :
    M.permanent = (-1) ^ m * M.det := by
  apply permanent_eq_sign_det M hcard
  · intro i j
    rcases eq_or_ne i j with h | h
    · subst h; rw [hMd i]; ring
    · rw [hM i j h, hM j i h.symm]
      have hij : f i - f j ≠ 0 := sub_ne_zero.mpr (fun e => h (hf e))
      have hji : f j - f i ≠ 0 := sub_ne_zero.mpr (fun e => h.symm (hf e))
      field_simp
      ring
  · intro p q s hps hsq hpq
    rw [hM p s hps, hM s q hsq, hM p q hpq]
    have h1 : f p - f s ≠ 0 := sub_ne_zero.mpr (fun e => hps (hf e))
    have h2 : f s - f q ≠ 0 := sub_ne_zero.mpr (fun e => hsq (hf e))
    have h3 : f p - f q ≠ 0 := sub_ne_zero.mpr (fun e => hpq (hf e))
    field_simp
    ring

-- An odd-sized skew matrix has permanent zero. (This is why the "bridge" identity
-- `per(M) = per(W)` only holds in even size: in odd size `per(W) = 0` while `per(M) ≠ 0`.)
theorem permanent_skew_odd_eq_zero {γ : Type*} [Fintype γ] [DecidableEq γ]
    (M : Matrix γ γ ℂ) (hskew : ∀ i j, M i j = - M j i) (hodd : Odd (Fintype.card γ)) :
    M.permanent = 0 := by
  have h1 : Mᵀ = (-1 : ℂ) • M := by
    ext i j; simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, neg_one_mul]
    exact hskew j i
  have h2 : M.permanent = (-1 : ℂ) ^ (Fintype.card γ) * M.permanent := by
    conv_lhs => rw [← Matrix.permanent_transpose M, h1, Matrix.permanent_smul]
  rw [hodd.neg_one_pow] at h2
  linear_combination h2 / 2

-- The analogous determinant fact for completeness: odd-sized skew matrices have determinant zero.
theorem det_skew_odd_eq_zero {γ : Type*} [Fintype γ] [DecidableEq γ]
    (M : Matrix γ γ ℂ) (hskew : ∀ i j, M i j = - M j i) (hodd : Odd (Fintype.card γ)) :
    M.det = 0 := by
  have h1 : Mᵀ = (-1 : ℂ) • M := by
    ext i j; simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, neg_one_mul]
    exact hskew j i
  have h2 : M.det = (-1 : ℂ) ^ (Fintype.card γ) * M.det := by
    conv_lhs => rw [← Matrix.det_transpose M, h1, Matrix.det_smul]
  rw [hodd.neg_one_pow] at h2
  linear_combination h2 / 2

-- Specialization to the roots-of-unity Cauchy matrix `G_{ij} = 1/(ζ^i - ζ^j)` underlying the
-- conjecture: `per G = (-1)^n det G`. (This is the middle step `per(W)=(-1)^n det(W)` after the
-- diagonal scaling `W = diag(-2ζ^i)·G`; the outstanding gaps are the exponential-formula "bridge"
-- `per(M_spec)=per(W)` and the circulant evaluation `det(W)=(-1)^n a n`.)
theorem cauchy_roots_eq_sign_det {n : ℕ} (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n))
    (G : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hGd : ∀ i, G i i = 0)
    (hG : ∀ i j, i ≠ j → G i j = 1 / (ζ ^ (i : ℕ) - ζ ^ (j : ℕ))) :
    G.permanent = (-1) ^ n * G.det := by
  have hinj : Function.Injective (fun i : Fin (2 * n) => ζ ^ (i : ℕ)) := by
    intro i j h
    exact Fin.val_injective (hζ.pow_inj i.isLt j.isLt h)
  have hcard : Fintype.card (Fin (2 * n)) = 2 * n := by simp
  exact permanent_cauchy_eq_sign_det hcard (fun i => ζ ^ (i : ℕ)) hinj G hGd hG

-- `per = (-1)^n det` is preserved under left multiplication by a diagonal matrix. Applied with
-- `d i = -2ζ^i`, `G_{ij}=1/(ζ^i-ζ^j)`, and the previous corollary, this yields the full middle
-- step `per(W) = (-1)^n det(W)` for `W = diag(-2ζ^i)·G`.
theorem permanent_eq_sign_det_of_diagMul {n : ℕ} (d : Fin (2 * n) → ℂ)
    (G : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (hG : G.permanent = (-1) ^ n * G.det) :
    (Matrix.diagonal d * G).permanent = (-1) ^ n * (Matrix.diagonal d * G).det := by
  rw [permanent_diagonal_mul, det_diagonal_mul, hG]; ring

-- Concretely: the matrix `W_{ij} = -2ζ^i/(ζ^i - ζ^j)` (off-diagonal), `0` on the diagonal,
-- satisfies `per(W) = (-1)^n det(W)`, for any primitive `2n`-th root `ζ`.
theorem W_eq_sign_det {n : ℕ} (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n))
    (W : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hWd : ∀ i, W i i = 0)
    (hW : ∀ i j, i ≠ j → W i j = (-2 * ζ ^ (i : ℕ)) / (ζ ^ (i : ℕ) - ζ ^ (j : ℕ))) :
    W.permanent = (-1) ^ n * W.det := by
  classical
  -- W = diagonal (fun i => -2 ζ^i) * G with G_{ij} = 1/(ζ^i - ζ^j)
  set G : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
    fun i j => if i = j then 0 else 1 / (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) with hGdef
  have hGd : ∀ i, G i i = 0 := by intro i; simp [hGdef]
  have hGoff : ∀ i j, i ≠ j → G i j = 1 / (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) := by
    intro i j h; simp [hGdef, h]
  have hWG : W = Matrix.diagonal (fun i : Fin (2 * n) => -2 * ζ ^ (i : ℕ)) * G := by
    ext i j
    rw [Matrix.mul_apply]
    rcases eq_or_ne i j with h | h
    · subst h
      rw [hWd i, Fintype.sum_eq_single i, Matrix.diagonal_apply_eq, hGd i, mul_zero]
      intro k hk; rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]
    · rw [hW i j h, Fintype.sum_eq_single i, Matrix.diagonal_apply_eq, hGoff i j h]
      · ring
      · intro k hk; rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]
  rw [hWG]
  exact permanent_eq_sign_det_of_diagMul _ G (cauchy_roots_eq_sign_det ζ hζ G hGd hGoff)

-- Consequence: `per(W)` equals the target value `A` as soon as `det(W) = (-1)^n A`. This isolates
-- the *only* remaining gap for `per(W) = a n` to the circulant determinant computation
-- `det(W) = (-1)^n a n`.
theorem W_perm_of_det {n : ℕ} (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n))
    (W : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hWd : ∀ i, W i i = 0)
    (hW : ∀ i j, i ≠ j → W i j = (-2 * ζ ^ (i : ℕ)) / (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)))
    (A : ℂ) (hdet : W.det = (-1) ^ n * A) :
    W.permanent = A := by
  have h : ((-1 : ℂ)) ^ n * ((-1) ^ n) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n, rfl⟩
  rw [W_eq_sign_det ζ hζ W hWd hW, hdet, ← mul_assoc, h, one_mul]

-- Capstone assembly: the conjecture's permanent equals the target value `A`, given exactly the two
-- remaining lemmas — the bridge `per(M_spec) = per(W)` and the circulant determinant
-- `det(W) = (-1)^n A`. Everything else is discharged by the verified development above.
theorem spec_reduction {n : ℕ} (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n))
    (Mspec W : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hWd : ∀ i, W i i = 0)
    (hW : ∀ i j, i ≠ j → W i j = (-2 * ζ ^ (i : ℕ)) / (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)))
    (A : ℂ)
    (hbridge : Mspec.permanent = W.permanent)
    (hdet : W.det = (-1) ^ n * A) :
    Mspec.permanent = A := by
  rw [hbridge]
  exact W_perm_of_det ζ hζ W hWd hW A hdet

end BridgeDev
