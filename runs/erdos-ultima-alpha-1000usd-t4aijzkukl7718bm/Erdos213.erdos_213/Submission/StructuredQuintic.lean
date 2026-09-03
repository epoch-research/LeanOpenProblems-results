import FormalConjecturesUtil

/-! Exact square classification for one structured quintic chart.
This is not a classification of quintics or rational-distance configurations.
The coordinate is x=t+1 relative to the heptad parameter t. -/
namespace Erdos213.StructuredQuintic
open Polynomial
set_option maxHeartbeats 4000000

private def F (a c : ℚ) : ℚ := -3*a^2+a*c+5*a+c-4
private def G (a c : ℚ) : ℚ :=
  -2*a^5+2*a^4*c+8*a^4-8*a^3*c-12*a^3-2*a^2*c^2+16*a^2*c+
    6*a^2+5*a*c^2-18*a*c+3*a+c^3-6*c^2+11*c-4

/-- The two residual coefficient equations have one solution away from the
specified boundary. The proof uses an explicit polynomial elimination identity. -/
theorem coefficient_elimination {a c : ℚ} (hac : a ≠ c) (hc : c ≠ 1)
    (hF : (a-1)*F a c = 0) (hG : G a c = 0) : a = 1/2 ∧ c = 3/2 := by
  have ha : a ≠ 1 := by
    intro he
    subst a
    have hz : (c-1)^3 = 0 := by dsimp [G] at hG; linear_combination hG
    exact hc (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz))
  have hf : F a c = 0 := (mul_eq_zero.mp hF).resolve_left (sub_ne_zero.mpr ha)
  have hh : 2*(a-2)^2*(a-1)^5*(2*a-1) = 0 := by
    dsimp [F] at hf
    dsimp [G] at hG
    linear_combination (a+1)^3*hG -
      (2*a^6-10*a^5-2*a^4*c+30*a^4+4*a^3*c-50*a^3+a^2*c^2+39*a^2+
       2*a*c^2-8*a*c-10*a+c^2-2*c+3)*hf
  have ha2 : a ≠ 2 := by
    intro he
    subst a
    have hec : c = 2 := by dsimp [F] at hf; linarith only [hf]
    exact hac hec.symm
  have hn : 2*(a-2)^2*(a-1)^5 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr ha2)))
      (pow_ne_zero _ (sub_ne_zero.mpr ha))
  have hz : 2*a-1 = 0 := (mul_eq_zero.mp hh).resolve_left hn
  have he : a = 1/2 := by linarith only [hz]
  refine ⟨he, ?_⟩
  rw [he] at hf
  dsimp [F] at hf
  linarith only [hf]

private def u (a c : ℚ) : ℚ := (a-c)^2-2*c+2
private def w (a c : ℚ) : ℚ := a^2-2*a-c^2+4*c-2
private def v (a c : ℚ) : ℚ := 2*a-2*c+1
private def b (a c : ℚ) : ℚ := -3*a^2+4*a*c+2*a-c^2-2
private def d (a c : ℚ) : ℚ :=
  -4*a^4+8*a^3*c+8*a^3-4*a^2*c^2-16*a^2*c-4*a^2+
    6*a*c^2+12*a*c-2*a+2*c^3-7*c^2+1

/-- Coefficient-level square-root classification, normalized at x=0. -/
lemma normalized_coefficients {a c B D : ℚ} (hac : a ≠ c) (hc : c ≠ 1)
    (h1 : 2*B*(c-1)^2 = -2*(c-1)^2*(2*u a c+w a c))
    (h2 : B^2+2*D*(c-1)^2 =
      2*(u a c)^2+4*(c-1)^2-(w a c)^2-2*(c-1)^2*v a c)
    (h3 : 2*D*B = -4*u a c-2*w a c*v a c)
    (h4 : D^2 = 2-(v a c)^2) : a = 1/2 ∧ c = 3/2 := by
  have hn : (c-1)^2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hc)
  have hB : B = b a c := by
    apply mul_right_cancel₀ hn
    dsimp [u,w,b] at *
    linear_combination h1 / 2
  subst B
  have hD : (c-1)^2*D = d a c := by
    dsimp [b,u,w,v,d] at *
    linear_combination h2 / 2
  have hF : 8*(a-c)^3*((a-1)*F a c) = 0 := by
    dsimp [b,u,w,v,d,F] at *
    linear_combination (norm := (dsimp [b]; ring)) -(c-1)^2*h3+2*(b a c)*hD
  have hG : 8*(a-c)^3*G a c = 0 := by
    dsimp [v,d,G] at *
    linear_combination (norm := (dsimp [d]; ring)) -(c-1)^4*h4+((c-1)^2*D+d a c)*hD
  have hnon : 8*(a-c)^3 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr hac))
  exact coefficient_elimination hac hc ((mul_eq_zero.mp hF).resolve_left hnon)
    ((mul_eq_zero.mp hG).resolve_left hnon)

/-- The shifted numerator and denominator in the structured conic chart. -/
noncomputable def U (a c : ℚ) : ℚ[X] := -X^2+C (u a c)*X-C ((c-1)^2)
noncomputable def W (a c : ℚ) : ℚ[X] := C (v a c)*X^2+C (w a c)*X+C ((c-1)^2)

private lemma quadratic_repr {p : ℚ[X]} (hp : p.natDegree ≤ 2) :
    p = C (p.coeff 2)*X^2+C (p.coeff 1)*X+C (p.coeff 0) := by
  calc
    p = ∑ i ∈ Finset.range 3, C (p.coeff i)*X^i :=
      p.as_sum_range_C_mul_X_pow' (show p.natDegree < 3 by omega)
    _ = _ := by
      simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,
        mul_one,pow_one]
      ring

private lemma square_expand (a b c : ℚ) :
    (C a*X^2+C b*X+C c : ℚ[X])^2 =
    C (a^2)*X^4+C (2*a*b)*X^3+C (b^2+2*a*c)*X^2+C (2*b*c)*X+C (c^2) := by
  simp only [map_add,map_mul,map_pow,map_ofNat]
  ring

/-- Exact square classification on this chart. This condition is necessary
for one additional generic heptad distance, not sufficient for all distances. -/
theorem residual_square_iff {a c : ℚ} (hac : a ≠ c) (hc : c ≠ 1) :
    IsSquare (2*(U a c)^2-(W a c)^2) ↔ a = 1/2 ∧ c = 3/2 := by
  constructor
  · rintro ⟨p,hp⟩
    rw [← pow_two] at hp
    have hd : p.natDegree ≤ 2 := by
      have he : (p^2).natDegree ≤ 4 := by rw [← hp]; unfold U W; compute_degree
      rw [natDegree_pow] at he
      omega
    rw [quadratic_repr hd,square_expand] at hp
    have hi : 2*(U a c)^2-(W a c)^2 =
        C (2-(v a c)^2)*X^4+C (-4*u a c-2*w a c*v a c)*X^3+
        C (2*(u a c)^2+4*(c-1)^2-(w a c)^2-2*(c-1)^2*v a c)*X^2+
        C (-2*(c-1)^2*(2*u a c+w a c))*X+C ((c-1)^4) := by
      unfold U W
      simp only [map_add,map_sub,map_neg,map_mul,map_pow,map_ofNat]
      ring
    rw [hi] at hp
    have h0 := congrArg (fun q : ℚ[X] => q.coeff 0) hp
    have h1 := congrArg (fun q : ℚ[X] => q.coeff 1) hp
    have h2 := congrArg (fun q : ℚ[X] => q.coeff 2) hp
    have h3 := congrArg (fun q : ℚ[X] => q.coeff 3) hp
    have h4 := congrArg (fun q : ℚ[X] => q.coeff 4) hp
    simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] at h0 h1 h2 h3 h4
    norm_num at h0 h1 h2 h3 h4
    have hp0 : p.coeff 0 = (c-1)^2 ∨ p.coeff 0 = -((c-1)^2) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith only [h0])
    rcases hp0 with hp0 | hp0
    · rw [hp0] at h1 h2
      refine normalized_coefficients hac hc (B := p.coeff 1) (D := p.coeff 2) ?_ ?_ ?_ ?_
      · linear_combination -h1
      · exact h2.symm
      · linear_combination -h3
      · exact h4.symm
    · rw [hp0] at h1 h2
      refine normalized_coefficients hac hc (B := -p.coeff 1) (D := -p.coeff 2) ?_ ?_ ?_ ?_
      · linear_combination -h1
      · linear_combination -h2
      · linear_combination -h3
      · simpa only [neg_sq] using h4.symm
  · rintro ⟨rfl,rfl⟩
    refine ⟨X^2+X-C (1/4 : ℚ), ?_⟩
    have hquarter : (4 : ℚ[X])*C (1/4 : ℚ) = 1 := by
      have hh := congrArg (C : ℚ → ℚ[X]) (show 4*(1/4 : ℚ) = 1 by norm_num)
      simpa only [map_mul,map_ofNat,map_one] using hh
    norm_num [U,W,u,w,v]
    linear_combination 2*X^2*hquarter

/-- The unsupported residual factor for the surviving candidate's distance
to the square anchor t². -/
noncomputable def obstruction : ℚ[X] :=
  16*X^4+32*X^3+40*X^2+56*X+25

/-- Opposite signs at 0 and -1 exclude every constant square class, with no
degree assumption on a proposed square root. -/
theorem obstruction_not_constant_square :
    ¬ ∃ (k : ℚ) (p : ℚ[X]), obstruction = C k*p^2 := by
  rintro ⟨k,p,hp⟩
  have h0 := congrArg (eval (0 : ℚ)) hp
  have h1 := congrArg (eval (-1 : ℚ)) hp
  norm_num [obstruction] at h0 h1
  have hk : 0 < k := by
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (sq_nonneg (p.eval 0))
    nlinarith only [h0,hh]
  have hh := mul_nonneg hk.le (sq_nonneg (p.eval (-1)))
  nlinarith only [h1,hh]

/-- None of the five finite supported roots can absorb an odd factor. -/
theorem obstruction_supported_nonzero {r : ℚ}
    (hr : r = -2 ∨ r = -1 ∨ r = -1/2 ∨ r = 0 ∨ r = 1) :
    obstruction.eval r ≠ 0 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num [obstruction]

/-- The first two identities certify the first three norm classes of the
candidate. The last exhibits the extra residual factor at the square anchor. -/
theorem candidate_identities :
    (X*(4*X^2+8*X+5)^2+(4*X^2+4*X-1)^2 : ℚ[X]) =
      (X+1)*(4*X^2+8*X+1)^2 ∧
    (2*(4*X^2+8*X+5)^2-(4*X^2+4*X-1)^2 : ℚ[X]) =
      (4*X^2+12*X+7)^2 ∧
    ((4*X^2+8*X+5)^2+X*(4*X^2+4*X-1)^2 : ℚ[X]) =
      (X+1)*obstruction := by
  dsimp [obstruction]
  constructor
  · ring
  constructor <;> ring

#print axioms coefficient_elimination
#print axioms normalized_coefficients
#print axioms residual_square_iff
#print axioms obstruction_not_constant_square
#print axioms obstruction_supported_nonzero
#print axioms candidate_identities
end Erdos213.StructuredQuintic
