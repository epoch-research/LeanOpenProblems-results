import FormalConjecturesUtil

/-! An obstruction to a weighted degree-six construction for sums of fifth
powers. This concerns one family of polynomial identities, not the full
representation count in Erdős 322. -/
namespace Erdos322Research.QuinticWeightedPair

open Finset Polynomial
noncomputable section
set_option Elab.async false

private def core (P D Z : ℝ) : ℝ :=
  4 * (P^2-D^2) * (Z*(Z+2*D)) + 4*(3*D^2-P^2)*(D*Z) - (P^2-D^2)^2

private lemma core_negative (P D Z : ℝ) (hP : 0 < P^2-D^2)
    (hZ : Z*(Z+2*D) < 0) : core P D Z < 0 := by
  have hfirst : 4*(P^2-D^2)*(Z*(Z+2*D)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hZ
  have hDZ : D*Z < 0 := by nlinarith [sq_nonneg Z]
  have hDZ' : 0 < D*(Z+2*D) := by nlinarith [sq_nonneg (Z+2*D)]
  by_cases hK : 0 ≤ 3*D^2-P^2
  · have hsecond : 4*(3*D^2-P^2)*(D*Z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hDZ.le
    dsimp only [core]
    linarith [sq_nonneg (P^2-D^2)]
  · have hK' : 3*D^2-P^2 < 0 := lt_of_not_ge hK
    have hsecond : 4*(3*D^2-P^2)*(D*(Z+2*D)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hDZ'
    have he : core P D Z = 4*(P^2-D^2)*(Z*(Z+2*D)) +
        4*(3*D^2-P^2)*(D*(Z+2*D)) - (5*D^2-P^2)^2 := by
      dsimp [core]
      ring
    rw [he]
    linarith [sq_nonneg (5*D^2-P^2)]

private def pair2 (A x y u : ℝ) : ℝ :=
  2*u*A^2*(x^3+y^3)+A*(x^4-y^4)
private def pair3 (A x y u : ℝ) : ℝ :=
  u*A^3*(x^2-y^2)+A^2*(x^3+y^3)
private def pair4 (A x y u : ℝ) : ℝ :=
  u*A^4*(x+y)+2*A^3*(x^2-y^2)

private lemma determinant_identity (A x y u : ℝ) :
    8*(pair2 A x y u * pair4 A x y u - 2*(pair3 A x y u)^2) =
      A^4*(x+y)^2*core (x+y) (x-y) (A*u) := by
  dsimp [pair2, pair3, pair4, core]
  ring

private lemma weighted_cauchy {ι : Type*} [Fintype ι] (l d : ι → ℝ)
    (hl : ∀ i, 0 < l i) :
    (∑ i, l i^2*d i^3)^2 ≤ (∑ i, l i^3*d i^2)*(∑ i, l i*d i^4) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun i _ => mul_nonneg (pow_nonneg (hl i).le _) (sq_nonneg _))
    (fun i _ => mul_nonneg (hl i).le (by positivity))
    (fun i _ => by ring)

private lemma slopes_zero_of_fourth_nonpos {ι : Type*} [Fintype ι]
    (l d : ι → ℝ) (hl : ∀ i, 0 < l i)
    (h : (∑ i, l i*d i^4) ≤ 0) : ∀ i, d i = 0 := by
  intro i
  have ht : l i*d i^4 ≤ 0 := (Finset.single_le_sum
    (f := fun j => l j*d j^4)
    (fun j _ => mul_nonneg (hl j).le (by positivity)) (Finset.mem_univ i)).trans h
  have hd : d i^4 ≤ 0 := (mul_le_mul_iff_right₀ (hl i)).mp (by simpa using ht)
  exact eq_zero_of_pow_eq_zero (le_antisymm hd (by positivity))

/-- The four highest nonconstant moment constraints are incompatible with
positivity, when the two degree-six leading coefficients do not vanish. -/
theorem no_positive_moments {ι : Type*} [Fintype ι]
    (l d : ι → ℝ) (A x y u : ℝ)
    (hl : ∀ i, 0 < l i) (hA : A ≠ 0) (hx : 0 < x) (hy : 0 < y) (hu : 0 < u)
    (h2 : pair2 A x y u + 2*(∑ i, l i^3*d i^2) = 0)
    (h3 : pair3 A x y u + (∑ i, l i^2*d i^3) = 0)
    (h4 : pair4 A x y u + (∑ i, l i*d i^4) = 0)
    (h5 : 5*A^4*(x+y) + (∑ i, d i^5) = 0) : False := by
  have hA2 : 0 < A^2 := sq_pos_of_ne_zero hA
  have hA4 : 0 < A^4 := by positivity
  have hP : 0 < x+y := by positivity
  have hS4 : 0 < ∑ i, l i*d i^4 := by
    by_contra hn
    have hd := slopes_zero_of_fourth_nonpos l d hl (le_of_not_gt hn)
    simp only [hd, zero_pow (by decide : 5 ≠ 0), sum_const_zero, add_zero] at h5
    have hp : 0 < 5*A^4*(x+y) := by positivity
    linarith
  have hpair4 : pair4 A x y u < 0 := by linarith
  have hmul : (A^2*(x+y))*((A*u)*(A*u+2*(x-y))) < 0 := by
    have he : (A^2*(x+y))*((A*u)*(A*u+2*(x-y))) = pair4 A x y u*u := by
      dsimp [pair4]
      ring
    rw [he]
    exact mul_neg_of_neg_of_pos hpair4 hu
  have hZ : (A*u)*(A*u+2*(x-y)) < 0 := by
    exact (mul_lt_mul_iff_right₀ (mul_pos hA2 hP)).mp (by simpa using hmul)
  have hcore := core_negative (x+y) (x-y) (A*u)
    (by nlinarith [mul_pos hx hy]) hZ
  have hneg : A^4*(x+y)^2*core (x+y) (x-y) (A*u) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hcore
  rw [← determinant_identity] at hneg
  have hCS := weighted_cauchy l d hl
  have he2 : (∑ i, l i^3*d i^2) = -(pair2 A x y u)/2 := by linarith
  have he3 : (∑ i, l i^2*d i^3) = -(pair3 A x y u) := by linarith
  have he4 : (∑ i, l i*d i^4) = -(pair4 A x y u) := by linarith
  rw [he2, he3, he4] at hCS
  nlinarith only [hCS, hneg]

private def affine (a b : ℝ) : ℝ[X] := C a*X+C b

private lemma affine_expansion (a b : ℝ) :
    affine a b^5 = C (b^5)+C (5*a*b^4)*X+C (10*a^2*b^3)*X^2+
      C (10*a^3*b^2)*X^3+C (5*a^4*b)*X^4+C (a^5)*X^5 := by
  simp only [affine, map_mul, map_pow, map_ofNat]
  ring

private lemma affine_coeff (a b : ℝ) (j : Fin 6) :
    (affine a b^5).coeff j =
      ![b^5, 5*a*b^4, 10*a^2*b^3, 10*a^3*b^2, 5*a^4*b, a^5] j := by
  rw [affine_expansion]
  fin_cases j <;>
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] <;> norm_num

/-- A translated version of the weighted family, centered at the parameter
where positivity will be tested. -/
def localModel {ι : Type*} [Fintype ι] (A x y u : ℝ) (l d : ι → ℝ) : ℝ[X] :=
  (X+C u)*((affine A x)^5+(affine (-A) y)^5)+∑ i, (affine (d i) (l i))^5

private lemma local_coeff {ι : Type*} [Fintype ι]
    (A x y u : ℝ) (l d : ι → ℝ) (j : ℕ) :
    (localModel A x y u l d).coeff (j+1) =
      (affine A x^5).coeff j+(affine (-A) y^5).coeff j+
      u*((affine A x^5).coeff (j+1)+(affine (-A) y^5).coeff (j+1))+
      ∑ i, (affine (d i) (l i)^5).coeff (j+1) := by
  simp only [localModel, add_mul, mul_add, coeff_add, finset_sum_coeff,
    coeff_X_mul, coeff_C_mul]
  ring

private lemma local_relations {ι : Type*} [Fintype ι]
    (A x y u N : ℝ) (l d : ι → ℝ) (he : localModel A x y u l d = C N) :
    (x^5+y^5+5*u*A*(x^4-y^4)+5*(∑ i, l i^4*d i)=0) ∧
    (pair2 A x y u+2*(∑ i, l i^3*d i^2)=0) ∧
    (pair3 A x y u+(∑ i, l i^2*d i^3)=0) ∧
    (pair4 A x y u+(∑ i, l i*d i^4)=0) ∧
    (5*A^4*(x+y)+(∑ i, d i^5)=0) := by
  have hc0 (a b : ℝ) : (affine a b^5).coeff 0=b^5 := affine_coeff a b 0
  have hc1 (a b : ℝ) : (affine a b^5).coeff 1=5*a*b^4 := affine_coeff a b 1
  have hc2 (a b : ℝ) : (affine a b^5).coeff 2=10*a^2*b^3 := affine_coeff a b 2
  have hc3 (a b : ℝ) : (affine a b^5).coeff 3=10*a^3*b^2 := affine_coeff a b 3
  have hc4 (a b : ℝ) : (affine a b^5).coeff 4=5*a^4*b := affine_coeff a b 4
  have hc5 (a b : ℝ) : (affine a b^5).coeff 5=a^5 := affine_coeff a b 5
  have h1 := congrArg (fun p : ℝ[X] => p.coeff (0+1)) he
  have h2 := congrArg (fun p : ℝ[X] => p.coeff (1+1)) he
  have h3 := congrArg (fun p : ℝ[X] => p.coeff (2+1)) he
  have h4 := congrArg (fun p : ℝ[X] => p.coeff (3+1)) he
  have h5 := congrArg (fun p : ℝ[X] => p.coeff (4+1)) he
  simp only [local_coeff, hc0, hc1, hc2, hc3, hc4, hc5, coeff_C,
    show (0+1 : ℕ) ≠ 0 by decide, show (1+1 : ℕ) ≠ 0 by decide,
    show (2+1 : ℕ) ≠ 0 by decide, show (3+1 : ℕ) ≠ 0 by decide,
    show (4+1 : ℕ) ≠ 0 by decide, if_false] at h1 h2 h3 h4 h5
  have hs1 : (∑ i, 5*d i*l i^4)=5*(∑ i, l i^4*d i) := by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
  have hs2 : (∑ i, 10*(d i)^2*(l i)^3)=10*(∑ i, l i^3*d i^2) := by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
  have hs3 : (∑ i, 10*(d i)^3*(l i)^2)=10*(∑ i, l i^2*d i^3) := by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
  have hs4 : (∑ i, 5*(d i)^4*l i)=5*(∑ i, l i*d i^4) := by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
  rw [hs1] at h1
  rw [hs2] at h2
  rw [hs3] at h3
  rw [hs4] at h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [h1]
  · dsimp [pair2]; nlinarith only [h2]
  · dsimp [pair3]; nlinarith only [h3]
  · dsimp [pair4]; nlinarith only [h4]
  · nlinarith only [h5]

/-- No constant polynomial of this weighted form passes through a point
where `u`, both paired factors, and every other coordinate are positive.
The number of other coordinates is arbitrary. -/
theorem no_positive_local_identity {ι : Type*} [Fintype ι]
    (A x y u N : ℝ) (l d : ι → ℝ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hl : ∀ i, 0 < l i) :
    localModel A x y u l d ≠ C N := by
  intro he
  obtain ⟨h1,h2,h3,h4,h5⟩ := local_relations A x y u N l d he
  by_cases hA : A = 0
  · subst A
    have hS : (∑ i, l i^3*d i^2) ≤ 0 := by
      simp only [pair2, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
        zero_add] at h2
      linarith
    have hd (i : ι) : d i = 0 := by
      have ht : l i^3*d i^2 ≤ 0 := (Finset.single_le_sum
        (f := fun j => l j^3*d j^2)
        (fun j _ => mul_nonneg (pow_nonneg (hl j).le _) (sq_nonneg _))
        (Finset.mem_univ i)).trans hS
      have hi : d i^2 ≤ 0 := (mul_le_mul_iff_right₀ (pow_pos (hl i) 3)).mp
        (by simpa using ht)
      exact eq_zero_of_pow_eq_zero (le_antisymm hi (sq_nonneg _))
    simp only [hd, mul_zero, sum_const_zero, add_zero] at h1
    have hx5 : 0 < x^5 := pow_pos hx _
    have hy5 : 0 < y^5 := pow_pos hy _
    linarith
  · exact no_positive_moments l d A x y u hl hA hx hy hu h2 h3 h4 h5

/-- The same obstruction in the unshifted weighted variable. -/
theorem no_positive_weighted_identity {ι : Type*} [Fintype ι]
    (A B E u N : ℝ) (c d : ι → ℝ)
    (hu : 0 < u) (hx : 0 < A*u+B) (hy : 0 < -A*u+E)
    (hl : ∀ i, 0 < c i+d i*u) :
    ¬ (∀ v : ℝ, v*((A*v+B)^5+(-A*v+E)^5)+∑ i, (c i+d i*v)^5=N) := by
  intro h
  apply no_positive_local_identity A (A*u+B) (-A*u+E) u N
    (fun i => c i+d i*u) d hx hy hu hl
  apply Polynomial.funext
  intro z
  simp only [localModel, affine, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_finset_sum]
  have hs (i : ι) : d i*z+(c i+d i*u)=c i+d i*(z+u) := by ring
  simp_rw [hs]
  have hx' : A*z+(A*u+B)=A*(z+u)+B := by ring
  have hy' : -A*z+(-A*u+E)=-A*(z+u)+E := by ring
  rw [hx', hy']
  exact h (z+u)

private lemma weighted_eval {ι : Type*} [Fintype ι]
    (A B E : ℝ) (c d : ι → ℝ) (v : ℝ) :
    (localModel A B E 0 c d).eval v =
      v*((A*v+B)^5+(-A*v+E)^5)+∑ i, (c i+d i*v)^5 := by
  simp [localModel, affine, eval_finset_sum, add_comm]

private lemma weighted_identity_of_original {ι : Type*} [Fintype ι]
    (A B E N : ℝ) (c d : ι → ℝ)
    (h : ∀ t : ℝ, (t*(A*t^5+B))^5+(t*(-A*t^5+E))^5+
      ∑ i, (c i+d i*t^5)^5=N) :
    ∀ v : ℝ, v*((A*v+B)^5+(-A*v+E)^5)+∑ i, (c i+d i*v)^5=N := by
  have hi : Function.Injective (fun m : ℕ => (m : ℝ)^5) := by
    intro a b hab
    change (a : ℝ)^5=(b : ℝ)^5 at hab
    have hn : a^5=b^5 := by exact_mod_cast hab
    exact Nat.pow_left_injective (by decide : 5 ≠ 0) hn
  have he : localModel A B E 0 c d = C N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hi).mono
    rintro v ⟨m, rfl⟩
    simp only [Set.mem_setOf_eq, weighted_eval, eval_C]
    have hm := h (m : ℝ)
    simp only [mul_pow] at hm
    simpa only [mul_add] using hm
  intro v
  have hv := congrArg (fun p : ℝ[X] => p.eval v) he
  simpa only [weighted_eval, eval_C] using hv

private theorem no_positive_original_parameter {ι : Type*} [Fintype ι]
    (A B E N t : ℝ) (c d : ι → ℝ) (ht : 0 < t)
    (hx : 0 < t*(A*t^5+B)) (hy : 0 < t*(-A*t^5+E))
    (hl : ∀ i, 0 < c i+d i*t^5) :
    ¬ (∀ s : ℝ, (s*(A*s^5+B))^5+(s*(-A*s^5+E))^5+
      ∑ i, (c i+d i*s^5)^5=N) := by
  intro h
  apply no_positive_weighted_identity A B E (t^5) N c d (pow_pos ht _)
    ((mul_lt_mul_iff_right₀ ht).mp (by simpa using hx))
    ((mul_lt_mul_iff_right₀ ht).mp (by simpa using hy)) hl
  exact weighted_identity_of_original A B E N c d h

/-- The entire opposite-leading weighted `(6,6,5,...)` family has no
constant fifth-power identity passing through an all-positive real point.
This includes zero leading coefficients, all signs of the parameter, and
any finite number of remaining binomial coordinates. It does not classify
unweighted degree-six curves or arbitrary quintic representations. -/
theorem no_all_positive_original_identity {ι : Type*} [Fintype ι]
    (A B E N t : ℝ) (c d : ι → ℝ)
    (hx : 0 < t*(A*t^5+B)) (hy : 0 < t*(-A*t^5+E))
    (hl : ∀ i, 0 < c i+d i*t^5) :
    ¬ (∀ s : ℝ, (s*(A*s^5+B))^5+(s*(-A*s^5+E))^5+
      ∑ i, (c i+d i*s^5)^5=N) := by
  intro h
  rcases lt_trichotomy t 0 with ht | ht | ht
  · apply no_positive_original_parameter A (-B) (-E) N (-t) c (fun i => -d i)
      (by linarith)
    · convert hx using 1; ring
    · convert hy using 1; ring
    · intro i
      convert hl i using 1; ring
    · intro s
      have hs := h (-s)
      have hleft : (s*(A*s^5+-B))^5=((-s)*(A*(-s)^5+B))^5 := by ring
      have hright : (s*(-A*s^5+-E))^5=((-s)*(-A*(-s)^5+E))^5 := by ring
      have hrest (i : ι) : (c i+-d i*s^5)^5=(c i+d i*(-s)^5)^5 := by ring
      simpa only [hleft, hright, hrest] using hs
  · subst t
    simp at hx
  · exact no_positive_original_parameter A B E N t c d ht hx hy hl h

end
end Erdos322Research.QuinticWeightedPair
