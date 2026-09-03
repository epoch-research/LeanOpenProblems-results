import Submission.ExceptionalQuintic

/-!
Positive local recovery and ray bounds for a quadratic/quartic incidence law.
They are not a proof of graph freeness: dependent non-collinear rows are not
covered. In particular this file does not settle Erdős 714.
-/

open Polynomial

namespace Erdos714QuadraticRecovery

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

lemma pencil_value (Q : QuadraticForm F V) (A B : V) (t : F) :
    Q (t • A+B) = Q A*t^2 + QuadraticMap.polar Q A B*t + Q B := by
  rw [QuadraticMap.map_add Q (t • A) B, Q.map_smul, QuadraticMap.polar_smul_left]
  simp only [smul_eq_mul]
  ring

noncomputable def cubic (Q : QuadraticForm F V) (A B : V) : F[X] :=
  C (Q A)*X^3 + C (QuadraticMap.polar Q A B)*X^2 + C (Q B)*X - 1

lemma eval_cubic (Q : QuadraticForm F V) (A B : V) (t : F) :
    (cubic Q A B).eval t = t*Q (t • A+B)-1 := by
  simp [cubic, pencil_value]
  ring

lemma cubic_ne_zero (Q : QuadraticForm F V) (A B : V) : cubic Q A B ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (0 : F)) h
  simpa [cubic] using he

lemma cubic_degree (Q : QuadraticForm F V) (A B : V) :
    (cubic Q A B).natDegree ≤ 3 := by
  unfold cubic
  compute_degree!

lemma value_is_root (Q : QuadraticForm F V) (A B H : V) (hD : Q H ≠ 0)
    (hH : H = (Q H)^2 • A + Q H • B) : (cubic Q A B).eval (Q H) = 0 := by
  have hp : H = Q H • (Q H • A+B) := by
    calc
      H = (Q H)^2 • A + Q H • B := hH
      _ = Q H • (Q H • A+B) := by simp only [smul_add, smul_smul, pow_two]
  have hd : (Q H)^2 * Q (Q H • A+B) = Q H := by
    calc
      (Q H)^2 * Q (Q H • A+B) = Q (Q H • (Q H • A+B)) := by
        rw [Q.map_smul, smul_eq_mul, pow_two]
      _ = Q H := congrArg Q hp.symm
  apply (mul_eq_zero.mp (show Q H * (cubic Q A B).eval (Q H) = 0 from ?_)).resolve_left hD
  rw [eval_cubic]
  linear_combination hd

/-- The determinant argument works for an arbitrary quadratic form. -/
theorem solution_card_le_three (Q : QuadraticForm F V)
    (e : V ≃ₗ[F] (Fin 4 → F)) (u v : Fin 4 → F) (S : Finset V)
    (hS : ∀ H ∈ S, Q H ≠ 0 ∧ e H = (Q H)^2 • u + Q H • v) : S.card ≤ 3 := by
  classical
  let A := e.symm u
  let B := e.symm v
  have hrec (H : V) (hH : H ∈ S) : H = (Q H)^2 • A + Q H • B := by
    calc
      H = e.symm (e H) := (e.symm_apply_apply H).symm
      _ = (Q H)^2 • A + Q H • B := by rw [(hS H hH).2, map_add, map_smul, map_smul]
  have hi : Set.InjOn Q (S : Set V) := by
    intro H hH J hJ hval
    rw [hrec H hH, hrec J hJ, hval]
  have hsub : S.image Q ⊆ (cubic Q A B).roots.toFinset := by
    intro t ht
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (cubic_ne_zero Q A B)]
    exact value_is_root Q A B H (hS H hH).1 (hrec H hH)
  calc
    S.card = (S.image Q).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ (cubic Q A B).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (cubic Q A B).roots.card := Multiset.toFinset_card_le _
    _ ≤ (cubic Q A B).natDegree := Polynomial.card_roots' _
    _ ≤ 3 := cubic_degree Q A B

/-- Asymmetric law used in the investigated quadratic/quartic model. -/
def relation (Q : QuadraticForm F V) (N : V → F)
    (B : V →ₗ[F] V →ₗ[F] F) (x y : V) : Prop :=
  B x y = (Q x)^2*(Q y)^2 + Q x*N x*Q y

/-- Independent row constraints suffice, regardless of the quartic function. -/
theorem independent_common_bound (Q : QuadraticForm F V) (N : V → F)
    (B : V →ₗ[F] V →ₗ[F] F) (R : Fin 4 → V)
    (e : V ≃ₗ[F] (Fin 4 → F)) (he : ∀ y i, e y i = B (R i) y)
    (S : Finset V) (hS : ∀ y ∈ S, Q y ≠ 0 ∧ ∀ i, relation Q N B (R i) y) :
    S.card ≤ 3 := by
  apply solution_card_le_three Q e (fun i => (Q (R i))^2)
    (fun i => Q (R i)*N (R i)) S
  intro y hy
  refine ⟨(hS y hy).1, ?_⟩
  ext i
  rw [he]
  change B (R i) y = (Q y)^2*(Q (R i))^2+Q y*(Q (R i)*N (R i))
  rw [(hS y hy).2 i]
  ring

end Erdos714QuadraticRecovery

namespace Erdos714QuadraticRays

variable {F : Type*} [Field F] [CharP F 3]

/-- A nonzero square coefficient makes this additive cubic injective
when minus one is nonsquare. No order on the field is being used. -/
theorem cubic_injective (hns : ¬ IsSquare (-1 : F)) (a : F)
    (ha : a ≠ 0) (hsa : IsSquare a) : Function.Injective (fun t : F => t^3+a*t) := by
  intro x y hxy
  have hd : (x-y)*((x-y)^2+a) = 0 := by
    have hp := sub_pow_char x y
    linear_combination hxy + hp
  rcases mul_eq_zero.mp hd with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hs : IsSquare (-a) := ⟨x-y, by linear_combination -h⟩
    have hdiv := hs.div hsa
    apply hns
    simpa only [neg_div, div_self ha] using hdiv

lemma scale_factor (A N D t : F) (hA : A ≠ 0) (hD : D ≠ 0) :
    A^2*(t^2*D)^2+A*N*(t^2*D) =
      t*((A^2*D^2)*(t^3+(N/(A*D))*t)) := by
  field_simp

lemma scale_equation_iff (A N D L t : F) (hA : A ≠ 0) (hD : D ≠ 0) (ht : t ≠ 0) :
    (t*L = A^2*(t^2*D)^2+A*N*(t^2*D)) ↔
      t^3+(N/(A*D))*t = L/(A^2*D^2) := by
  have hc : A^2*D^2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hD)
  rw [scale_factor A N D t hA hD]
  constructor
  · intro h
    apply (eq_div_iff hc).mpr
    simpa only [mul_comm] using (mul_left_cancel₀ ht h).symm
  · intro h
    congr 1
    simpa only [mul_comm] using ((eq_div_iff hc).mp h).symm

/-- Exactly one nonzero scalar solves the column-ray equation. -/
theorem unique_column_scale [Finite F] (hns : ¬ IsSquare (-1 : F))
    (A N D L : F) (hA : A ≠ 0) (hN : N ≠ 0) (hD : D ≠ 0) (hL : L ≠ 0)
    (hsA : IsSquare A) (hsN : IsSquare N) (hsD : IsSquare D) :
    ∃! t : F, t ≠ 0 ∧ t*L = A^2*(t^2*D)^2+A*N*(t^2*D) := by
  let a := N/(A*D)
  let b := L/(A^2*D^2)
  have ha : a ≠ 0 := div_ne_zero hN (mul_ne_zero hA hD)
  have hb : b ≠ 0 := div_ne_zero hL (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hD))
  have hi := cubic_injective hns a ha (hsN.div (hsA.mul hsD))
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hi) b
  have ht0 : t ≠ 0 := by
    intro h
    apply hb
    simpa [h] using ht.symm
  refine ⟨t, ⟨ht0, (scale_equation_iff A N D L t hA hD ht0).mpr ht⟩, ?_⟩
  intro s hs
  exact hi (((scale_equation_iff A N D L s hA hD hs.1).mp hs.2).trans ht.symm)

/-- The row-ray equation is exactly an exceptional quintic after dividing
by its explicitly nonzero leading coefficient and nonzero scalar. -/
theorem row_scale_bound (hns : ¬ IsSquare (-1 : F))
    (A N D L : F) (hA : A ≠ 0) (hN : N ≠ 0) (hD : D ≠ 0) (T : Finset F)
    (hT : ∀ t ∈ T, t ≠ 0 ∧ t*L = (t^2*A)^2*D^2+(t^2*A)*(t^4*N)*D) :
    T.card ≤ 3 := by
  apply Erdos714Exceptional.finite_root_bound (A*D/N) (-L/(A*N*D)) hns T
  intro t ht
  obtain ⟨ht0, he⟩ := hT t ht
  have hc : A*N*D ≠ 0 := mul_ne_zero (mul_ne_zero hA hN) hD
  have hp : (t*(A*N*D)) * (t^5+(A*D/N)*t^3+(-L/(A*N*D))) = 0 := by
    calc
      _ = t*(A*N*D*t^5+A^2*D^2*t^3-L) := by field_simp <;> ring
      _ = 0 := by linear_combination -he
  exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero ht0 hc)

section GraphRays

open Erdos714QuadraticRecovery

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The unique scaling statement for the actual bilinear incidence relation. -/
theorem column_ray_exists_unique [Finite F]
    (hns : ¬ IsSquare (-1 : F)) (Q : QuadraticForm F V) (N : V → F)
    (B : V →ₗ[F] V →ₗ[F] F) (x y : V)
    (hx : Q x ≠ 0) (hNx : N x ≠ 0) (hy : Q y ≠ 0) (hB : B x y ≠ 0)
    (hsx : IsSquare (Q x)) (hsNx : IsSquare (N x)) (hsy : IsSquare (Q y)) :
    ∃! t : F, t ≠ 0 ∧ relation Q N B x (t • y) := by
  simpa only [relation, map_smul, Q.map_smul, smul_eq_mul, ← pow_two] using
    unique_column_scale hns (Q x) (N x) (Q y) (B x y) hx hNx hy hB hsx hsNx hsy

/-- Four distinct nonzero scalar multiples of one row cannot have a common
neighbor under the stated homogeneous quartic and nonzero hypotheses. -/
theorem row_ray_card_bound
    (hns : ¬ IsSquare (-1 : F)) (Q : QuadraticForm F V) (N : V → F)
    (hN : ∀ (t : F) (x : V), N (t • x) = t^4*N x)
    (B : V →ₗ[F] V →ₗ[F] F) (x y : V)
    (hx : Q x ≠ 0) (hNx : N x ≠ 0) (hy : Q y ≠ 0) (T : Finset F)
    (hT : ∀ t ∈ T, t ≠ 0 ∧ relation Q N B (t • x) y) : T.card ≤ 3 := by
  apply row_scale_bound hns (Q x) (N x) (Q y) (B x y) hx hNx hy T
  intro t ht
  obtain ⟨ht0, he⟩ := hT t ht
  refine ⟨ht0, ?_⟩
  simpa only [relation, LinearMap.map_smul₂, Q.map_smul, smul_eq_mul, hN, ← pow_two] using he

end GraphRays

#print axioms cubic_injective
#print axioms unique_column_scale
#print axioms row_scale_bound
#print axioms column_ray_exists_unique
#print axioms row_ray_card_bound

end Erdos714QuadraticRays

#print axioms Erdos714QuadraticRecovery.solution_card_le_three
#print axioms Erdos714QuadraticRecovery.independent_common_bound
