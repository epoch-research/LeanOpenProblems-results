import FormalConjecturesUtil

/-!
The quartic-square pencil obtained from one fixed degree-three Mumford
representative. These are polynomial statements, not an identification of
arbitrary plane configurations with Jacobian fibers.
-/
namespace Erdos213.GenusThreeQuadraticFiber
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000

/-- Coefficients of the fixed pencil `H + 2c v - c² W`, with `W` monic cubic
and `H` having leading coefficient `delta`. The omitted constant coefficients
are irrelevant to the upper bound. -/
structure Pencil (K : Type*) where
  delta : K
  h3 : K
  h2 : K
  h1 : K
  w2 : K
  w1 : K
  v2 : K
  v1 : K

variable {K : Type*} [Field K]

def Pencil.E (p : Pencil K) (c : K) : K := p.h3 - c^2
def Pencil.F (p : Pencil K) (c : K) : K := p.h2 + 2*c*p.v2 - c^2*p.w2
def Pencil.G (p : Pencil K) (c : K) : K := p.h1 + 2*c*p.v1 - c^2*p.w1

def Pencil.Admissible (p : Pencil K) (c : K) : Prop :=
  ∃ b d : K, 2*p.delta*b = p.E c ∧
    p.delta*(b^2+2*d) = p.F c ∧ 2*p.delta*b*d = p.G c

/-- The coefficient-one compatibility condition is a monic sextic up to sign. -/
def Pencil.sextic (p : Pencil K) : K[X] :=
  -X^6 + C (3*p.h3-4*p.delta*p.w2)*X^4 + C (8*p.delta*p.v2)*X^3 +
  C (-3*p.h3^2+4*p.delta*p.h3*p.w2+4*p.delta*p.h2-8*p.delta^2*p.w1)*X^2 +
  C (-8*p.delta*p.h3*p.v2+16*p.delta^2*p.v1)*X +
  C (p.h3^3-4*p.delta*p.h3*p.h2+8*p.delta^2*p.h1)

lemma Pencil.sextic_eval (p : Pencil K) (c : K) :
    p.sextic.eval c = p.E c ^ 3 - 4*p.delta*p.E c*p.F c + 8*p.delta^2*p.G c := by
  simp only [Pencil.sextic, eval_add, eval_neg, eval_pow, eval_X, eval_mul, eval_C,
    Pencil.E, Pencil.F, Pencil.G]
  ring

lemma Pencil.admissible_isRoot (p : Pencil K) {c : K} (hc : p.Admissible c) :
    p.sextic.IsRoot c := by
  obtain ⟨b,d,hb,hd,hbd⟩ := hc
  rw [IsRoot.def, p.sextic_eval, ← hb, ← hd, ← hbd]
  ring

lemma Pencil.sextic_coeff_six (p : Pencil K) : p.sextic.coeff 6 = -1 := by
  simp only [Pencil.sextic, coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow,
    coeff_X, coeff_C]
  norm_num

lemma Pencil.sextic_ne_zero (p : Pencil K) : p.sextic ≠ 0 := by
  intro h
  have hh := p.sextic_coeff_six
  rw [h, coeff_zero] at hh
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) hh.symm

lemma Pencil.sextic_natDegree_le (p : Pencil K) : p.sextic.natDegree ≤ 6 := by
  unfold Pencil.sextic
  compute_degree

lemma Pencil.sextic_natDegree (p : Pencil K) : p.sextic.natDegree = 6 := by
  apply Nat.le_antisymm p.sextic_natDegree_le
  apply le_natDegree_of_ne_zero
  rw [p.sextic_coeff_six]
  exact neg_ne_zero.mpr one_ne_zero

lemma Pencil.admissible_finite (p : Pencil K) : {c | p.Admissible c}.Finite := by
  apply (p.sextic.finite_setOf_isRoot p.sextic_ne_zero).subset
  intro c hc
  exact p.admissible_isRoot hc

/-- At most six scalar parameters can satisfy the three necessary coefficient
conditions. The constant coefficient equation can only reduce this number. -/
theorem Pencil.admissible_ncard_le_six (p : Pencil K) :
    {c | p.Admissible c}.ncard ≤ 6 := by
  classical
  calc
    {c | p.Admissible c}.ncard ≤ (p.sextic.rootSet K).ncard := by
      apply Set.ncard_le_ncard (ht := p.sextic.rootSet_finite K)
      intro c hc
      exact (mem_rootSet_of_ne p.sextic_ne_zero).mpr (p.admissible_isRoot hc)
    _ ≤ p.sextic.natDegree := p.sextic.ncard_rootSet_le K
    _ = 6 := p.sextic_natDegree

lemma Pencil.coefficients_unique [CharZero K] (p : Pencil K) (hp : p.delta ≠ 0)
    {c b d b' d' : K}
    (hb : 2*p.delta*b = p.E c) (hd : p.delta*(b^2+2*d) = p.F c)
    (hb' : 2*p.delta*b' = p.E c) (hd' : p.delta*(b'^2+2*d') = p.F c) :
    b = b' ∧ d = d' := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  have he : b = b' := mul_left_cancel₀ (mul_ne_zero h2 hp) (hb.trans hb'.symm)
  refine ⟨he, ?_⟩
  subst b'
  have hh := mul_left_cancel₀ hp (hd.trans hd'.symm)
  have hz : 2*d = 2*d' := by linear_combination hh
  exact mul_left_cancel₀ h2 hz

/-- An actual polynomial identity in the fixed Mumford pencil implies the
three coefficient conditions used above. -/
lemma Pencil.admissible_of_identity (p : Pencil K)
    (h0 w0 v0 c b d : K)
    (h : C p.delta * (X^2 + C b*X + C d)^2 =
      (C p.delta*X^4+C p.h3*X^3+C p.h2*X^2+C p.h1*X+C h0) +
      C (2*c)*(C p.v2*X^2+C p.v1*X+C v0) -
      C (c^2)*(X^3+C p.w2*X^2+C p.w1*X+C w0)) : p.Admissible c := by
  have he : C p.delta * (X^2 + C b*X + C d)^2 =
      C p.delta*X^4 + C (2*p.delta*b)*X^3 + C (p.delta*(b^2+2*d))*X^2 +
        C (2*p.delta*b*d)*X + C (p.delta*d^2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [he] at h
  have h3 := congrArg (fun f : K[X] => f.coeff 3) h
  have h2 := congrArg (fun f : K[X] => f.coeff 2) h
  have h1 := congrArg (fun f : K[X] => f.coeff 1) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow,
    coeff_C, coeff_X, Nat.reduceEqDiff, if_false, if_true, mul_zero, add_zero,
    zero_add, mul_one] at h3 h2 h1
  refine ⟨b,d,?_,?_,?_⟩
  · simpa [Pencil.E] using h3
  · simpa [Pencil.F, mul_assoc] using h2
  · simpa [Pencil.G, mul_assoc] using h1

/-- The fixed reduced representative gives exactly the displayed pencil after
cancelling its nonzero first polynomial. This is only a polynomial normal-form
bridge; no theorem about arbitrary Jacobian points is assumed. -/
lemma reduction_identity {R : Type*} [CommRing R] [IsDomain R]
    (f W v H U V delta c : R) (hW : W ≠ 0)
    (hf : f=v^2+W*H) (hr : f=V^2+delta*W*U^2) (hv : V=c*W-v) :
    delta*U^2=H+2*c*v-c^2*W := by
  apply mul_left_cancel₀ hW
  rw [hv] at hr
  linear_combination hf-hr

/-- The square lift used before reduction in a hyperelliptic doubling. -/
lemma square_lift_identity {R : Type*} [CommRing R] (f u v w h k : R)
    (hf : f-v^2=u*h) (hk : 2*v*w=h+u*k) :
    f-(v+u*w)^2 = -u^2*(k+w^2) := by
  linear_combination hf - u*hk

/-- A weighted Heron identity for three values of a quadratic square pencil.
It is valid in every commutative ring, with no division. -/
lemma weighted_heron {R : Type*} [CommRing R]
    (delta a b H v W u t w : R)
    (h1 : delta*u^2=H)
    (h2 : delta*t^2=H+2*b*v-b^2*W)
    (h3 : delta*w^2=H+2*(a+b)*v-(a+b)^2*W) :
    delta^2 * ((a*u+b*w+(a+b)*t)*(a*u+b*w-(a+b)*t)*
      (a*u-b*w+(a+b)*t)*(-a*u+b*w+(a+b)*t)) +
      4*a^2*b^2*(a+b)^2*(v^2+W*H) = 0 := by
  linear_combination
    (2*a^2*b^2*(delta*w^2)+2*a^2*(a+b)^2*(delta*t^2)-a^4*(delta*u^2+H))*h1 +
    (2*a^2*(a+b)^2*H+2*b^2*(a+b)^2*(delta*w^2)-
      (a+b)^4*(delta*t^2+(H+2*b*v-b^2*W)))*h2 +
    (2*a^2*b^2*H+2*b^2*(a+b)^2*(H+2*b*v-b^2*W)-
      b^4*(delta*w^2+(H+2*(a+b)*v-(a+b)^2*W)))*h3

/-- A nonzero split real branch polynomial cannot admit three ordered pencil
values represented by everywhere-positive quadratics. Only the coefficient
of degree two is needed to ensure the positive factor is nonconstant. -/
theorem no_three_positive_squares (delta a b : ℝ) (ha : 0<a) (hb : 0<b)
    (H v W U1 U2 U3 : ℝ[X])
    (hf : (v^2+W*H).Splits) (hf0 : v^2+W*H ≠ 0)
    (hc1 : U1.coeff 2=1) (hc2 : U2.coeff 2=1) (hc3 : U3.coeff 2=1)
    (hp1 : ∀ x : ℝ, 0<U1.eval x) (hp2 : ∀ x : ℝ, 0<U2.eval x)
    (hp3 : ∀ x : ℝ, 0<U3.eval x)
    (h1 : C delta*U1^2=H)
    (h2 : C delta*U2^2=H+C (2*b)*v-C (b^2)*W)
    (h3 : C delta*U3^2=H+C (2*(a+b))*v-C ((a+b)^2)*W) : False := by
  let Q : ℝ[X] := C a*U1+C b*U3+C (a+b)*U2
  let T : ℝ[X] := (C a*U1+C b*U3-C (a+b)*U2)*
    (C a*U1-C b*U3+C (a+b)*U2)*(-C a*U1+C b*U3+C (a+b)*U2)
  have hid := weighted_heron (C delta) (C a) (C b) H v W U1 U2 U3 h1
    (by simpa only [map_mul, map_ofNat, map_pow] using h2)
    (by simpa only [map_mul, map_ofNat, map_pow, map_add] using h3)
  have heq : C (4*a^2*b^2*(a+b)^2)*(v^2+W*H) = Q*(-C (delta^2)*T) := by
    dsimp [Q,T]
    simp only [map_mul, map_pow, map_add, map_ofNat]
    linear_combination hid
  have hk : (4*a^2*b^2*(a+b)^2 : ℝ) ≠ 0 := by positivity
  have hs : Q.Splits := (hf.C_mul (4*a^2*b^2*(a+b)^2)).of_dvd
    (mul_ne_zero (by simpa only [ne_eq, C_eq_zero] using hk) hf0) ⟨-C (delta^2)*T,heq⟩
  have hcoeff : Q.coeff 2 = 2*(a+b) := by
    dsimp [Q]
    simp only [coeff_add, coeff_C_mul, hc1, hc2, hc3, mul_one]
    ring
  have hn : 2 ≤ Q.natDegree := le_natDegree_of_ne_zero (by rw [hcoeff]; positivity)
  have hd : Q.degree ≠ 0 := degree_ne_of_natDegree_ne (show Q.natDegree ≠ 0 by omega)
  obtain ⟨x,hx⟩ := hs.exists_eval_eq_zero hd
  have hpos : 0<Q.eval x := by
    dsimp [Q]
    simp only [eval_add, eval_mul, eval_C]
    exact add_pos (add_pos (mul_pos ha (hp1 x)) (mul_pos hb (hp3 x)))
      (mul_pos (add_pos ha hb) (hp2 x))
  rw [hx] at hpos
  exact lt_irrefl 0 hpos

def positiveParams (delta : ℝ) (H v W : ℝ[X]) : Set ℝ :=
  {c | ∃ U : ℝ[X], U.coeff 2=1 ∧ (∀ x : ℝ, 0<U.eval x) ∧
    C delta*U^2=H+C (2*c)*v-C (c^2)*W}

lemma positiveParams_no_ordered_triple (delta : ℝ) (H v W : ℝ[X])
    (hf : (v^2+W*H).Splits) (hf0 : v^2+W*H ≠ 0)
    {c1 c2 c3 : ℝ} (h12 : c1<c2) (h23 : c2<c3)
    (h1 : c1 ∈ positiveParams delta H v W)
    (h2 : c2 ∈ positiveParams delta H v W)
    (h3 : c3 ∈ positiveParams delta H v W) : False := by
  obtain ⟨U1,hc1,hp1,hu1⟩ := h1
  obtain ⟨U2,hc2,hp2,hu2⟩ := h2
  obtain ⟨U3,hc3,hp3,hu3⟩ := h3
  let H' := H+C (2*c1)*v-C (c1^2)*W
  let v' := v-C c1*W
  have he : v'^2+W*H'=v^2+W*H := by
    dsimp [v',H']
    simp only [map_mul, map_pow, map_ofNat]
    ring
  apply no_three_positive_squares delta (c3-c2) (c2-c1)
    (sub_pos.mpr h23) (sub_pos.mpr h12) H' v' W U1 U2 U3
    (he ▸ hf) (he ▸ hf0) hc1 hc2 hc3 hp1 hp2 hp3 hu1
  · convert hu2 using 1
    dsimp [H',v']
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  · convert hu3 using 1
    dsimp [H',v']
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring

/-- Finiteness and the two-parameter bound include all real parameters, with
no rational-height or denominator restriction. -/
theorem positiveParams_finite_and_ncard_le_two (delta : ℝ) (H v W : ℝ[X])
    (hf : (v^2+W*H).Splits) (hf0 : v^2+W*H ≠ 0) :
    (positiveParams delta H v W).Finite ∧ (positiveParams delta H v W).ncard ≤ 2 := by
  classical
  let S := positiveParams delta H v W
  have htr : ∀ {c1 c2 c3 : ℝ}, c1<c2 → c2<c3 → c1∈S → c2∈S → c3∈S → False :=
    fun h12 h23 h1 h2 h3 =>
      positiveParams_no_ordered_triple delta H v W hf hf0 h12 h23 h1 h2 h3
  have hpair : ∀ a ∈ S, ∀ b ∈ S, a<b → S ⊆ ({a,b} : Set ℝ) := by
    intro a ha b hb hab c hc
    by_cases hca : c=a
    · simp [hca]
    by_cases hcb : c=b
    · simp [hcb]
    exfalso
    rcases lt_or_gt_of_ne hca with hca | hac
    · exact htr hca hab hc ha hb
    · rcases lt_or_gt_of_ne hcb with hcb | hbc
      · exact htr hac hcb ha hc hb
      · exact htr hab hbc ha hb hc
  by_cases hs : S.Subsingleton
  · exact ⟨hs.finite, (Set.ncard_le_one_iff hs.finite).mpr (fun ha hb => hs ha hb) |>.trans (by omega)⟩
  · obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hs
    have hex : ∃ a b : ℝ, a ≠ b ∧ S ⊆ ({a,b} : Set ℝ) := by
      rcases lt_or_gt_of_ne hab with hab | hba
      · exact ⟨a,b,ne_of_lt hab,hpair a ha b hb hab⟩
      · exact ⟨b,a,ne_of_lt hba,hpair b hb a ha hba⟩
    obtain ⟨a,b,hab,hsub⟩ := hex
    have hfin : ({a,b} : Set ℝ).Finite := Set.toFinite _
    refine ⟨hfin.subset hsub, ?_⟩
    exact (Set.ncard_le_ncard hsub hfin).trans_eq (Set.ncard_pair hab)

def negativeDiscriminantParams (delta : ℝ) (H v W : ℝ[X]) : Set ℝ :=
  {c | ∃ b d : ℝ, b^2<4*d ∧
    C delta*(X^2+C b*X+C d)^2=H+C (2*c)*v-C (c^2)*W}

lemma negativeDiscriminantParams_subset (delta : ℝ) (H v W : ℝ[X]) :
    negativeDiscriminantParams delta H v W ⊆ positiveParams delta H v W := by
  rintro c ⟨b,d,hbd,he⟩
  refine ⟨X^2+C b*X+C d,?_,?_,he⟩
  · simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    norm_num
  · intro x
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
    nlinarith [sq_nonneg (2*x+b)]

/-- In particular, at most two parameters have monic quadratic representatives
with negative discriminant when the nonzero branch polynomial splits over R. -/
theorem negativeDiscriminantParams_finite_and_ncard_le_two
    (delta : ℝ) (H v W : ℝ[X])
    (hf : (v^2+W*H).Splits) (hf0 : v^2+W*H ≠ 0) :
    (negativeDiscriminantParams delta H v W).Finite ∧
    (negativeDiscriminantParams delta H v W).ncard ≤ 2 := by
  obtain ⟨hfin,hcard⟩ := positiveParams_finite_and_ncard_le_two delta H v W hf hf0
  have hsub := negativeDiscriminantParams_subset delta H v W
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

#print axioms Pencil.admissible_ncard_le_six
#print axioms Pencil.admissible_of_identity
#print axioms Pencil.coefficients_unique
#print axioms square_lift_identity
#print axioms reduction_identity
#print axioms weighted_heron
#print axioms no_three_positive_squares
#print axioms positiveParams_finite_and_ncard_le_two
#print axioms negativeDiscriminantParams_finite_and_ncard_le_two
end
end Erdos213.GenusThreeQuadraticFiber
