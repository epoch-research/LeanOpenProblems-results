import FormalConjecturesUtil

/-! Fixed-parity polynomial outputs cannot exploit multiplicity in joint
fibers of diagonal quadratic forms. This is a construction obstruction,
not a bound for unrestricted quartic representations. -/
namespace Erdos322Research.JointQuadraticParityRigidity
noncomputable section
open Finset
set_option Elab.async false
set_option maxHeartbeats 0

/-- A sum of squares of real polynomials can be constant only when every
polynomial is constant. -/
lemma polynomial_constant_square_norm {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℝ) (c : ℝ)
    (h : ∑ i, P i ^ 2 = Polynomial.C c) :
    ∀ i, P i = Polynomial.C ((P i).coeff 0) := by
  classical
  intro i
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hn
  let D := Finset.univ.sup (fun j ↦ (P j).natDegree)
  have hDi : (P i).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (P j).natDegree)
    (Finset.mem_univ i)
  have hDpos : 0 < D := by omega
  have hD (j : ι) : (P j).natDegree ≤ D :=
    Finset.le_sup (f := fun j ↦ (P j).natDegree) (Finset.mem_univ j)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨i⟩) (fun j ↦ (P j).natDegree)
  change D = (P j).natDegree at hj
  have hp : P j ≠ 0 := by
    intro hz
    simp [hz] at hj
    omega
  have hc : (P j).coeff D ≠ 0 := by
    rw [hj, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have he : (∑ j, P j ^ 2).coeff (2 * D) = ∑ j, (P j).coeff D ^ 2 := by
    simp only [Polynomial.finset_sum_coeff]
    exact Finset.sum_congr rfl (fun j _ ↦ Polynomial.coeff_pow_of_natDegree_le (hD j))
  have hs : (∑ j, (P j).coeff D ^ 2) = 0 := by
    rw [← he, h]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using (show 0 < 2 * D by omega))
  have hj0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg ((P j).coeff D))).mp hs
  exact hc (sq_eq_zero_iff.mp (hj0 j (Finset.mem_univ j)))

/-- Positivity along affine lines makes the individual polynomial coordinates
constant on any linear fiber on which their square norm is constant. -/
lemma linear_fiber_square_norm {σ τ ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ))
    (h : ∀ x y, L x = L y →
      ∑ i, (MvPolynomial.eval x (P i)) ^ 2 = ∑ i, (MvPolynomial.eval y (P i)) ^ 2)
    (x y : σ → ℝ) (hxy : L x = L y) (i : ι) :
    MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  let E : MvPolynomial σ ℝ →+* Polynomial ℝ :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun j ↦ Polynomial.C (x j) + Polynomial.C (y j - x j) * Polynomial.X)
  have hev (p : MvPolynomial σ ℝ) (t : ℝ) :
      (E p).eval t = MvPolynomial.eval (x + t • (y - x)) p := by
    have he : (Polynomial.evalRingHom t).comp E =
        MvPolynomial.eval (x + t • (y - x)) := by
      apply MvPolynomial.ringHom_ext <;> intro j <;> simp [E, mul_comm]
    exact congrArg (fun f : MvPolynomial σ ℝ →+* ℝ ↦ f p) he
  have hline (t : ℝ) : L (x + t • (y - x)) = L x := by
    rw [map_add, map_smul, map_sub, hxy, sub_self, smul_zero, add_zero]
  have hn : ∑ j, E (P j) ^ 2 = Polynomial.C (∑ j, (MvPolynomial.eval x (P j)) ^ 2) := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow, Polynomial.eval_C, hev]
    exact h _ _ (hline t)
  have hc := polynomial_constant_square_norm (fun j ↦ E (P j)) _ hn i
  have h0 := congrArg (Polynomial.evalRingHom (0 : ℝ)) hc
  have h1 := congrArg (Polynomial.evalRingHom (1 : ℝ)) hc
  simp only [Polynomial.coe_evalRingHom, hev, zero_smul, one_smul, add_zero,
    add_sub_cancel, Polynomial.eval_C] at h0 h1
  exact h0.trans h1.symm

/-- The linear map on squared coordinates associated with a list of diagonal
quadratic forms. -/
def labels {σ τ : Type*} [Fintype σ] (a : τ → σ → ℝ) :
    (σ → ℝ) →ₗ[ℝ] (τ → ℝ) where
  toFun z j := ∑ k, a j k * z k
  map_add' := by intros; funext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intros
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring

lemma labels_apply {σ τ : Type*} [Fintype σ] (a : τ → σ → ℝ)
    (z : σ → ℝ) (j : τ) : labels a z j = ∑ k, a j k * z k := rfl

private def labelSubst {σ τ : Type*} [Fintype σ] (a : τ → σ → ℝ) :
    MvPolynomial τ ℝ →+* MvPolynomial σ ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j ↦ ∑ k, MvPolynomial.C (a j k) * MvPolynomial.X k)

private lemma labelSubst_eval {σ τ : Type*} [Fintype σ]
    (a : τ → σ → ℝ) (H : MvPolynomial τ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval z (labelSubst a H) = MvPolynomial.eval (labels a z) H := by
  have he : (MvPolynomial.eval z).comp (labelSubst a) = MvPolynomial.eval (labels a z) := by
    apply MvPolynomial.ringHom_ext <;> intro j <;> simp [labelSubst, labels_apply]
  exact congrArg (fun f : MvPolynomial τ ℝ →+* ℝ ↦ f H) he

/-- An identity on squares extends to every real value of the squared
coordinates. The nonnegative orthant is polynomially Zariski dense. -/
lemma square_substitution_square_norm {σ τ ι : Type*} [Fintype σ] [Fintype ι]
    (a : τ → σ → ℝ) (P : ι → MvPolynomial σ ℝ) (H : MvPolynomial τ ℝ)
    (h : ∀ x : σ → ℝ, (∀ j, 0 ≤ x j) →
      ∑ i, (MvPolynomial.eval (fun j ↦ x j ^ 2) (P i)) ^ 2 =
        MvPolynomial.eval (labels a (fun j ↦ x j ^ 2)) H) :
    ∀ z : σ → ℝ, ∑ i, (MvPolynomial.eval z (P i)) ^ 2 =
      MvPolynomial.eval (labels a z) H := by
  have hp : (∑ i, P i ^ 2) = labelSubst a H := by
    apply MvPolynomial.funext_set (fun _ ↦ Set.Ici (0 : ℝ))
      (fun _ ↦ Set.Ici_infinite (0 : ℝ))
    intro z hz
    have hz0 (j : σ) : 0 ≤ z j := hz j (Set.mem_univ j)
    have heq : (fun j ↦ (Real.sqrt (z j)) ^ 2) = z := by
      funext j
      exact Real.sq_sqrt (hz0 j)
    have hh := h (fun j ↦ Real.sqrt (z j)) (fun j ↦ Real.sqrt_nonneg (z j))
    rw [heq] at hh
    simpa only [map_sum, map_pow, labelSubst_eval] using hh
  intro z
  have hh := congrArg (MvPolynomial.eval z) hp
  simpa only [map_sum, map_pow, labelSubst_eval] using hh

/-- A polynomial square norm depending on any finite list of diagonal
quadratic labels forces its contracted coordinates to be constant on fibers. -/
theorem contracted_square_norm_fiber {σ τ ι : Type*} [Fintype σ] [Fintype ι]
    (a : τ → σ → ℝ) (P : ι → MvPolynomial σ ℝ) (H : MvPolynomial τ ℝ)
    (h : ∀ x : σ → ℝ, (∀ j, 0 ≤ x j) →
      ∑ i, (MvPolynomial.eval (fun j ↦ x j ^ 2) (P i)) ^ 2 =
        MvPolynomial.eval (labels a (fun j ↦ x j ^ 2)) H)
    (x y : σ → ℝ) (hxy : labels a x = labels a y) (i : ι) :
    MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  have hh := square_substitution_square_norm a P H h
  exact linear_fiber_square_norm P (labels a)
    (fun x y he ↦ by rw [hh, hh, he]) x y hxy i

/-- A monomial times a polynomial in the coordinate squares includes every
polynomial with a fixed parity in each variable. -/
def parityOutput {σ : Type*} [Fintype σ] (e : σ → ℕ)
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) : ℝ :=
  (∏ j, x j ^ e j) * MvPolynomial.eval (fun j ↦ x j ^ 2) P

private def squareContract {σ : Type*} [Fintype σ] (e : σ → ℕ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  (∏ j, MvPolynomial.X j ^ e j) * P ^ 2

private lemma squareContract_eval {σ : Type*} [Fintype σ] (e : σ → ℕ)
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval (fun j ↦ x j ^ 2) (squareContract e P) =
      parityOutput e P x ^ 2 := by
  simp only [squareContract, map_mul, map_prod, map_pow, MvPolynomial.eval_X,
    parityOutput, mul_pow]
  congr 1
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Fixed-parity quartic outputs have the same squares on each joint
quadratic fiber, with no degree restriction and no positivity assumptions
on the quadratic labels. -/
theorem parity_output_squares_constant {σ τ ι : Type*} [Fintype σ] [Fintype ι]
    (a : τ → σ → ℝ) (e : ι → σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (H : MvPolynomial τ ℝ)
    (h : ∀ x : σ → ℝ, (∀ j, 0 ≤ x j) → ∑ i, parityOutput (e i) (P i) x ^ 4 =
      MvPolynomial.eval (labels a (fun j ↦ x j ^ 2)) H)
    (x y : σ → ℝ)
    (hxy : labels a (fun j ↦ x j ^ 2) = labels a (fun j ↦ y j ^ 2)) (i : ι) :
    parityOutput (e i) (P i) x ^ 2 = parityOutput (e i) (P i) y ^ 2 := by
  have hn (z : σ → ℝ) (hz : ∀ j, 0 ≤ z j) :
      ∑ i, (MvPolynomial.eval (fun j ↦ z j ^ 2) (squareContract (e i) (P i))) ^ 2 =
        MvPolynomial.eval (labels a (fun j ↦ z j ^ 2)) H := by
    simp only [squareContract_eval, ← pow_mul]
    exact h z hz
  have hh := contracted_square_norm_fiber a (fun i ↦ squareContract (e i) (P i)) H hn
    (fun j ↦ x j ^ 2) (fun j ↦ y j ^ 2) hxy i
  simpa only [squareContract_eval] using hh

/-- Nonnegative outputs, as required for the conjecture's representations,
are completely determined by the joint labels in this fixed-parity class. -/
theorem nonnegative_parity_outputs_constant {σ τ ι : Type*} [Fintype σ] [Fintype ι]
    (a : τ → σ → ℝ) (e : ι → σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (H : MvPolynomial τ ℝ)
    (h : ∀ x : σ → ℝ, (∀ j, 0 ≤ x j) → ∑ i, parityOutput (e i) (P i) x ^ 4 =
      MvPolynomial.eval (labels a (fun j ↦ x j ^ 2)) H)
    (x y : σ → ℝ)
    (hxy : labels a (fun j ↦ x j ^ 2) = labels a (fun j ↦ y j ^ 2)) (i : ι)
    (hx : 0 ≤ parityOutput (e i) (P i) x) (hy : 0 ≤ parityOutput (e i) (P i) y) :
    parityOutput (e i) (P i) x = parityOutput (e i) (P i) y := by
  exact (sq_eq_sq₀ hx hy).mp (parity_output_squares_constant a e P H h x y hxy i)

/-- Allowing signed outputs leaves at most one choice of sign in each
coordinate on a fixed joint fiber. -/
theorem parity_image_fixed_fiber_card_le {σ τ ι : Type*}
    [Fintype σ] [Fintype ι]
    (a : τ → σ → ℝ) (e : ι → σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (H : MvPolynomial τ ℝ)
    (h : ∀ x : σ → ℝ, (∀ j, 0 ≤ x j) → ∑ i, parityOutput (e i) (P i) x ^ 4 =
      MvPolynomial.eval (labels a (fun j ↦ x j ^ 2)) H)
    (S : Finset (σ → ℝ)) (N : τ → ℝ)
    (hS : ∀ x ∈ S, labels a (fun j ↦ x j ^ 2) = N) :
    (S.image (fun x i ↦ parityOutput (e i) (P i) x)).card ≤ 2 ^ Fintype.card ι := by
  classical
  obtain rfl | ⟨x₀, hx₀⟩ := S.eq_empty_or_nonempty
  · simp
  let v : ι → ℝ := fun i ↦ parityOutput (e i) (P i) x₀
  let f : (ι → Bool) → (ι → ℝ) := fun b i ↦ if b i then v i else -v i
  have hsub : S.image (fun x i ↦ parityOutput (e i) (P i) x) ⊆
      (Finset.univ : Finset (ι → Bool)).image f := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    let b : ι → Bool := fun i ↦ decide (parityOutput (e i) (P i) x = v i)
    refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
    funext i
    have hh := parity_output_squares_constant a e P H h x x₀
      ((hS x hx).trans (hS x₀ hx₀).symm) i
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with hp | hp
    · simp [f, b, v, hp]
    · by_cases he : parityOutput (e i) (P i) x = v i
      · simp [f, b, he]
      · simp only [f, b, decide_eq_true_eq, if_neg he]
        exact hp.symm
  exact (Finset.card_le_card hsub).trans (by simpa using
    (Finset.card_image_le (s := (Finset.univ : Finset (ι → Bool))) (f := f)))

/-- The source multiplicity cannot produce distinct nonnegative outputs
within a fixed joint quadratic fiber in this class. -/
theorem nonnegative_parity_image_card_le_one {σ τ ι : Type*}
    [Fintype σ] [Fintype ι]
    (a : τ → σ → ℝ) (e : ι → σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (H : MvPolynomial τ ℝ)
    (h : ∀ x : σ → ℝ, (∀ j, 0 ≤ x j) → ∑ i, parityOutput (e i) (P i) x ^ 4 =
      MvPolynomial.eval (labels a (fun j ↦ x j ^ 2)) H)
    (S : Finset (σ → ℝ)) (N : τ → ℝ)
    (hS : ∀ x ∈ S, labels a (fun j ↦ x j ^ 2) = N)
    (hpos : ∀ x ∈ S, ∀ i, 0 ≤ parityOutput (e i) (P i) x) :
    (S.image (fun x i ↦ parityOutput (e i) (P i) x)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro v hv w hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
  funext i
  exact nonnegative_parity_outputs_constant a e P H h x y
    ((hS x hx).trans (hS y hy).symm) i (hpos x hx i) (hpos y hy i)

end
end Erdos322Research.JointQuadraticParityRigidity
