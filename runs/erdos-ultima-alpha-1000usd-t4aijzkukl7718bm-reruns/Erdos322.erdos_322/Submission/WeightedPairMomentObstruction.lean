import FormalConjecturesUtil

/-! A weighted-Cauchy obstruction to a family of polynomial constructions.
This is not an upper bound on unrestricted representation counts. -/
namespace Erdos322Research.WeightedPairMomentObstruction

open Finset Polynomial
noncomputable section
set_option Elab.async false

/-- Consecutive weighted moments satisfy a Cauchy inequality. -/
lemma moment_cauchy {ι : Type*} [Fintype ι] (m : ℕ) (w l d : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hl : ∀ i, 0 ≤ l i) :
    (∑ i, w i*l i^(m+2)*d i^3)^2 ≤
      (∑ i, w i*l i^(m+3)*d i^2)*(∑ i, w i*l i^(m+1)*d i^4) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i) (pow_nonneg (hl i) _)) (sq_nonneg _)
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i) (pow_nonneg (hl i) _)) (by positivity)
  · intro i _
    simp only [pow_add]
    ring

private lemma determinant_gap (m : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < (x^(m+3)+y^(m+3))^2 -
      (y^(m+4)-x^(m+4))*(y^(m+2)-x^(m+2)) := by
  have he : (x^(m+3)+y^(m+3))^2 -
      (y^(m+4)-x^(m+4))*(y^(m+2)-x^(m+2)) =
      (x*y)^(m+2)*(x+y)^2 := by
    simp only [pow_add, mul_pow]
    ring
  rw [he]
  positivity

/-- The three normalized coefficient equations cannot be moments of a
positive measure. No fifth or higher moment equation is needed. -/
theorem no_positive_three_moments (m : ℕ) (A x y T2 T3 T4 : ℝ)
    (hA : A ≠ 0) (hx : 0 < x) (hy : 0 < y)
    (hCS : T3^2 ≤ T2*T4)
    (h2 : ((m : ℝ)+4)*T2 = 2*A*(y^(m+4)-x^(m+4)))
    (h3 : ((m : ℝ)+3)*T3 = -3*A^2*(x^(m+3)+y^(m+3)))
    (h4 : ((m : ℝ)+2)*T4 = 4*A^3*(y^(m+2)-x^(m+2))) : False := by
  let r : ℝ := (m : ℝ)+3
  let S : ℝ := x^(m+3)+y^(m+3)
  let L : ℝ := y^(m+4)-x^(m+4)
  let R : ℝ := y^(m+2)-x^(m+2)
  have hr : 3 ≤ r := by dsimp [r]; have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hr2 : 9 ≤ r^2 := by nlinarith [sq_nonneg (r-3)]
  have hA4 : 0 < A^4 := pow_pos (sq_pos_of_ne_zero hA) 2 |>.trans_eq (by ring)
  have hgap : 0 < S^2-L*R := determinant_gap m x y hx hy
  have he24 : (r^2-1)*(T2*T4)=8*A^4*(L*R) := by
    calc
      (r^2-1)*(T2*T4) = (((m : ℝ)+4)*T2)*(((m : ℝ)+2)*T4) := by dsimp [r]; ring
      _ = 8*A^4*(L*R) := by rw [h2,h4]; dsimp [L,R]; ring
  have he3 : r^2*T3^2=9*A^4*S^2 := by
    calc
      r^2*T3^2=(((m : ℝ)+3)*T3)^2 := by dsimp [r]; ring
      _ = 9*A^4*S^2 := by rw [h3]; dsimp [S]; ring
  have hcoef : 0 ≤ (r^2-1)*r^2 := mul_nonneg (by linarith) (sq_nonneg r)
  have hle := mul_le_mul_of_nonneg_left hCS hcoef
  have hl : (r^2-1)*r^2*T3^2=(r^2-1)*(r^2*T3^2) := by ring
  have hrr : (r^2-1)*r^2*(T2*T4)=r^2*((r^2-1)*(T2*T4)) := by ring
  rw [hl,hrr,he24,he3] at hle
  have hpos : 0 < A^4*((r^2-9)*S^2+8*r^2*(S^2-L*R)) := by
    apply mul_pos hA4
    have hfirst : 0 ≤ (r^2-9)*S^2 := mul_nonneg (by nlinarith) (sq_nonneg S)
    have hsecond : 0 < 8*r^2*(S^2-L*R) := mul_pos (by nlinarith) hgap
    linarith
  nlinarith only [hle,hpos]

/-- The moments include the two paired coordinates with weight `u`. -/
def combinedMoment {ι : Type*} [Fintype ι] (k j : ℕ)
    (A x y u : ℝ) (l d : ι → ℝ) : ℝ :=
  u*(x^(k-j)*A^j+y^(k-j)*(-A)^j)+∑ i, l i^(k-j)*d i^j

lemma combined_cauchy {ι : Type*} [Fintype ι] (m : ℕ)
    (A x y u : ℝ) (l d : ι → ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hl : ∀ i, 0 ≤ l i) :
    (combinedMoment (m+5) 3 A x y u l d)^2 ≤
      combinedMoment (m+5) 2 A x y u l d *
        combinedMoment (m+5) 4 A x y u l d := by
  let w' : Option (Option ι) → ℝ := Option.elim' u (Option.elim' u (fun _ => 1))
  let l' : Option (Option ι) → ℝ := Option.elim' x (Option.elim' y l)
  let d' : Option (Option ι) → ℝ := Option.elim' A (Option.elim' (-A) d)
  have hw' : ∀ i, 0 ≤ w' i := by
    rintro (_ | (_ | i)) <;> simp [w',hu]
  have hl' : ∀ i, 0 ≤ l' i := by
    rintro (_ | (_ | i)) <;> simp [l',hx,hy,hl]
  have h := moment_cauchy m w' l' d' hw' hl'
  simp only [Fintype.sum_option, w', l', d', Option.elim'_none, Option.elim'_some,
    one_mul] at h
  convert h using 1 <;> simp only [combinedMoment,
    show m+5-2=m+3 by omega, show m+5-3=m+2 by omega,
    show m+5-4=m+1 by omega] <;> ring

private def affine (a b : ℝ) : ℝ[X] := C a*X+C b

private lemma affine_coeff (a b : ℝ) (k j : ℕ) :
    (affine a b^k).coeff j = (k.choose j : ℝ)*(b^(k-j)*a^j) := by
  have he : affine a b^k = ((X+C b)^k).comp (C a*X) := by
    simp only [affine, pow_comp, add_comp, X_comp, C_comp]
  rw [he, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  ring

/-- The weighted identity after translating the parameter to a positive point. -/
def localModel {ι : Type*} [Fintype ι] (k : ℕ)
    (A x y u : ℝ) (l d : ι → ℝ) : ℝ[X] :=
  (X+C u)*((affine A x)^k+(affine (-A) y)^k)+∑ i, (affine (d i) (l i))^k

private lemma local_coeff {ι : Type*} [Fintype ι] (k j : ℕ)
    (A x y u : ℝ) (l d : ι → ℝ) :
    (localModel k A x y u l d).coeff (j+1) =
      (k.choose j : ℝ)*(x^(k-j)*A^j+y^(k-j)*(-A)^j)+
      (k.choose (j+1) : ℝ)*combinedMoment k (j+1) A x y u l d := by
  simp only [localModel, add_mul, mul_add, coeff_add, finset_sum_coeff,
    coeff_X_mul, coeff_C_mul, affine_coeff, combinedMoment]
  rw [← Finset.mul_sum]
  ring

/-- Normalization of the coefficient equations using consecutive binomial
coefficients. -/
lemma local_coefficient_relation {ι : Type*} [Fintype ι] (k j : ℕ)
    (hjk : j+1 ≤ k) (A x y u N : ℝ) (l d : ι → ℝ)
    (he : localModel k A x y u l d = C N) :
    (k-j : ℕ)*combinedMoment k (j+1) A x y u l d+
      (j+1 : ℕ)*(x^(k-j)*A^j+y^(k-j)*(-A)^j)=0 := by
  have h := congrArg (fun p : ℝ[X] => p.coeff (j+1)) he
  dsimp only at h
  rw [local_coeff] at h
  simp only [coeff_C, Nat.add_one_ne_zero, if_false] at h
  have hb : (k.choose j : ℝ)*(k-j : ℕ) = (j+1 : ℕ)*(k.choose (j+1) : ℝ) := by
    exact_mod_cast (Nat.choose_succ_right_eq k j).symm.trans (Nat.mul_comm _ _)
  have hpos : 0 < (k.choose (j+1) : ℝ) := by exact_mod_cast Nat.choose_pos hjk
  apply (mul_eq_zero.mp (show (k.choose (j+1) : ℝ)*
      ((k-j : ℕ)*combinedMoment k (j+1) A x y u l d+
      (j+1 : ℕ)*(x^(k-j)*A^j+y^(k-j)*(-A)^j))=0 from ?_)).resolve_left (ne_of_gt hpos)
  calc
    _ = (k-j : ℕ)*((k.choose j : ℝ)*(x^(k-j)*A^j+y^(k-j)*(-A)^j)+
        (k.choose (j+1) : ℝ)*combinedMoment k (j+1) A x y u l d) := by
      have hbp := congrArg (fun z : ℝ => z*(x^(k-j)*A^j+y^(k-j)*(-A)^j)) hb
      nlinarith only [hbp]
    _ = 0 := by rw [h]; ring

/-- For every exponent at least five, this weighted family cannot be constant
at a point where all coordinates are positive and the weight is nonnegative.
The family may have arbitrarily many affine remaining coordinates. -/
theorem no_positive_local_identity {ι : Type*} [Fintype ι] (m : ℕ)
    (A x y u N : ℝ) (l d : ι → ℝ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 ≤ u) (hl : ∀ i, 0 < l i) :
    localModel (m+5) A x y u l d ≠ C N := by
  intro he
  have h2 := local_coefficient_relation (m+5) 1 (by omega) A x y u N l d he
  have h3 := local_coefficient_relation (m+5) 2 (by omega) A x y u N l d he
  have h4 := local_coefficient_relation (m+5) 3 (by omega) A x y u N l d he
  norm_num [show m+5-1=m+4 by omega] at h2
  norm_num [show m+5-2=m+3 by omega] at h3
  norm_num [show m+5-3=m+2 by omega] at h4
  by_cases hA : A=0
  · subst A
    have hS : (∑ i, l i^(m+3)*d i^2)=0 := by
      simp only [combinedMoment, show m+5-2=m+3 by omega, neg_zero,
        zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add] at h2
      exact (mul_eq_zero.mp h2).resolve_left (by positivity)
    have hd (i : ι) : d i=0 := by
      have hterm := Finset.single_le_sum (f := fun i => l i^(m+3)*d i^2)
        (fun i _ => mul_nonneg (pow_nonneg (hl i).le _) (sq_nonneg _))
        (Finset.mem_univ i)
      rw [hS] at hterm
      have hpow : d i^2 ≤ 0 := (mul_le_mul_iff_right₀ (pow_pos (hl i) (m+3))).mp
        (by simpa using hterm)
      exact eq_zero_of_pow_eq_zero (le_antisymm hpow (sq_nonneg _))
    have h1 := local_coefficient_relation (m+5) 0 (by omega) 0 x y u N l d he
    simp only [combinedMoment, hd, Nat.sub_zero, pow_zero, pow_one, neg_zero,
      mul_zero, zero_add, add_zero, mul_one, sum_const_zero, Nat.cast_one,
      one_mul] at h1
    have hpos : 0 < x^(m+5)+y^(m+5) := by positivity
    linarith
  · apply no_positive_three_moments m A x y
      (combinedMoment (m+5) 2 A x y u l d)
      (combinedMoment (m+5) 3 A x y u l d)
      (combinedMoment (m+5) 4 A x y u l d) hA hx hy
      (combined_cauchy m A x y u l d hx.le hy.le hu (fun i => (hl i).le))
    · nlinarith only [h2]
    · nlinarith only [h3]
    · nlinarith only [h4]

/-- The same statement without translating the weighted variable. -/
theorem no_positive_weighted_identity {ι : Type*} [Fintype ι] (k : ℕ) (hk : 5 ≤ k)
    (A B E u N : ℝ) (c d : ι → ℝ)
    (hu : 0 ≤ u) (hx : 0 < A*u+B) (hy : 0 < -A*u+E)
    (hl : ∀ i, 0 < c i+d i*u) :
    ¬ (∀ v : ℝ, v*((A*v+B)^k+(-A*v+E)^k)+∑ i, (c i+d i*v)^k=N) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 5 m]
  intro h
  apply no_positive_local_identity m A (A*u+B) (-A*u+E) u N
    (fun i => c i+d i*u) d hx hy hu hl
  apply Polynomial.funext
  intro z
  simp only [localModel, affine, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_finset_sum]
  have hs (i : ι) : d i*z+(c i+d i*u)=c i+d i*(z+u) := by ring
  simp_rw [hs]
  have hx' : A*z+(A*u+B)=A*(z+u)+B := by ring
  have hy' : -A*z+(-A*u+E)=-A*(z+u)+E := by ring
  rw [hx',hy']
  exact h (z+u)

private lemma weighted_eval {ι : Type*} [Fintype ι] (k : ℕ)
    (A B E : ℝ) (c d : ι → ℝ) (v : ℝ) :
    (localModel k A B E 0 c d).eval v =
      v*((A*v+B)^k+(-A*v+E)^k)+∑ i, (c i+d i*v)^k := by
  simp [localModel, affine, eval_finset_sum, add_comm]

private lemma weighted_identity_of_original {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : k ≠ 0) (A B E N : ℝ) (c d : ι → ℝ)
    (h : ∀ t : ℝ, (t*(A*t^k+B))^k+(t*(-A*t^k+E))^k+
      ∑ i, (c i+d i*t^k)^k=N) :
    ∀ v : ℝ, v*((A*v+B)^k+(-A*v+E)^k)+∑ i, (c i+d i*v)^k=N := by
  have hi : Function.Injective (fun m : ℕ => (m : ℝ)^k) := by
    intro a b hab
    change (a : ℝ)^k=(b : ℝ)^k at hab
    have hn : a^k=b^k := by exact_mod_cast hab
    exact Nat.pow_left_injective hk hn
  have he : localModel k A B E 0 c d = C N := by
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
    (k : ℕ) (hk : 5 ≤ k) (A B E N t : ℝ) (c d : ι → ℝ) (ht : 0 < t)
    (hx : 0 < t*(A*t^k+B)) (hy : 0 < t*(-A*t^k+E))
    (hl : ∀ i, 0 < c i+d i*t^k) :
    ¬ (∀ s : ℝ, (s*(A*s^k+B))^k+(s*(-A*s^k+E))^k+
      ∑ i, (c i+d i*s^k)^k=N) := by
  intro h
  apply no_positive_weighted_identity k hk A B E (t^k) N c d (pow_pos ht _).le
    ((mul_lt_mul_iff_right₀ ht).mp (by simpa using hx))
    ((mul_lt_mul_iff_right₀ ht).mp (by simpa using hy)) hl
  exact weighted_identity_of_original k (by omega) A B E N c d h

/-- For every `k ≥ 5`, the opposite-leading weighted `(k+1,k+1,k,...)`
family admits no constant identity passing through an all-positive real
point. This includes zero leading coefficients, either sign of the parameter,
and any finite number of remaining binomial coordinates. -/
theorem no_all_positive_original_identity {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 5 ≤ k) (A B E N t : ℝ) (c d : ι → ℝ)
    (hx : 0 < t*(A*t^k+B)) (hy : 0 < t*(-A*t^k+E))
    (hl : ∀ i, 0 < c i+d i*t^k) :
    ¬ (∀ s : ℝ, (s*(A*s^k+B))^k+(s*(-A*s^k+E))^k+
      ∑ i, (c i+d i*s^k)^k=N) := by
  intro h
  rcases lt_trichotomy t 0 with ht | ht | ht
  · let A' : ℝ := -((-1)^k*A)
    let d' : ι → ℝ := fun i => (-1)^k*d i
    have hleft (s : ℝ) : s*(A'*s^k+-B)=(-s)*(A*(-s)^k+B) := by
      dsimp [A']; rw [neg_pow]; ring
    have hright (s : ℝ) : s*(-A'*s^k+-E)=(-s)*(-A*(-s)^k+E) := by
      dsimp [A']; rw [neg_pow]; ring
    have hrest (s : ℝ) (i : ι) : c i+d' i*s^k=c i+d i*(-s)^k := by
      dsimp [d']; rw [neg_pow]; ring
    apply no_positive_original_parameter k hk A' (-B) (-E) N (-t) c d'
      (by linarith)
    · simpa only [hleft,neg_neg] using hx
    · simpa only [hright,neg_neg] using hy
    · intro i
      simpa only [hrest,neg_neg] using hl i
    · intro s
      simpa only [hleft,hright,hrest] using h (-s)
  · subst t
    simp at hx
  · exact no_positive_original_parameter k hk A B E N t c d ht hx hy hl h

end
end Erdos322Research.WeightedPairMomentObstruction
