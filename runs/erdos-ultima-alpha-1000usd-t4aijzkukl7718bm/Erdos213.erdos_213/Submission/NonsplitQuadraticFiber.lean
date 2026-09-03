import Submission.GenusThreeQuadraticFiber

/-! A three-parameter bound for quadratic square pencils whose nonzero
branch polynomial has at most one nonsplit quadratic factor. This concerns
one fixed pencil, not arbitrary rational-distance configurations. -/
namespace Erdos213.NonsplitQuadraticFiber
open Polynomial GenusThreeQuadraticFiber
noncomputable section
set_option maxHeartbeats 3000000

lemma positive_quadratic_factor_unique (Q q P : ℝ[X])
    (hQ : Q.natDegree=2) (hq : q.natDegree=2) (hqm : q.Monic)
    (hP : P.Splits) (hP0 : P≠0) (hpos : ∀ x : ℝ, 0<Q.eval x)
    (hdvd : Q ∣ q*P) : Q=C (Q.coeff 2)*q := by
  have hirr : Irreducible Q := irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hQ]; decide) (fun x hx => (ne_of_gt (hpos x)) hx)
  have hQq : Q ∣ q := by
    rcases hirr.prime.dvd_mul.mp hdvd with hh | hh
    · exact hh
    · have hsplit := hP.of_dvd hP0 hh
      obtain ⟨x,hx⟩ := hsplit.exists_eval_eq_zero
        (degree_ne_of_natDegree_ne (by omega : Q.natDegree≠0))
      exact False.elim ((ne_of_gt (hpos x)) hx)
  have hLC : Q.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have htarget : Q=C Q.leadingCoeff*q := by
    apply eq_of_dvd_of_natDegree_le_of_leadingCoeff
      (dvd_mul_of_dvd_right hQq (C Q.leadingCoeff))
    · rw [natDegree_C_mul hLC,hq,hQ]
    · simp [leadingCoeff_mul,hqm.leadingCoeff]
  simpa only [leadingCoeff,hQ] using htarget

lemma heron_factor_dvd (delta a b : ℝ) (ha : 0<a) (hb : 0<b)
    (H v W U1 U2 U3 : ℝ[X])
    (h1 : C delta*U1^2=H)
    (h2 : C delta*U2^2=H+C (2*b)*v-C (b^2)*W)
    (h3 : C delta*U3^2=H+C (2*(a+b))*v-C ((a+b)^2)*W) :
    C a*U1+C b*U3+C (a+b)*U2 ∣ v^2+W*H := by
  let Q := C a*U1+C b*U3+C (a+b)*U2
  let T := (C a*U1+C b*U3-C (a+b)*U2)*
    (C a*U1-C b*U3+C (a+b)*U2)*(-C a*U1+C b*U3+C (a+b)*U2)
  have hid := weighted_heron (C delta) (C a) (C b) H v W U1 U2 U3 h1
    (by simpa only [map_mul,map_ofNat,map_pow] using h2)
    (by simpa only [map_mul,map_ofNat,map_pow,map_add] using h3)
  have heq : C (4*a^2*b^2*(a+b)^2)*(v^2+W*H)=Q*(-C (delta^2)*T) := by
    dsimp [Q,T]
    simp only [map_mul,map_pow,map_add,map_ofNat]
    linear_combination hid
  have hk : 4*a^2*b^2*(a+b)^2≠0 := by positivity
  exact (dvd_C_mul hk).mp ⟨-C (delta^2)*T,heq⟩

def quad (b d : ℝ) : ℝ[X] := X^2+C b*X+C d

lemma quad_positive {b d : ℝ} (h : b^2<4*d) :
    ∀ x : ℝ, 0<(quad b d).eval x := by
  intro x
  simp only [quad,eval_add,eval_pow,eval_X,eval_mul,eval_C]
  nlinarith [sq_nonneg (2*x+b)]

lemma quad_coeff_two (b d : ℝ) : (quad b d).coeff 2=1 := by
  simp [quad]

lemma heron_factor_coeff_one (delta a b : ℝ) (ha : 0<a) (hb : 0<b)
    (H v W q P : ℝ[X]) (hq : q.natDegree=2) (hqm : q.Monic)
    (hP : P.Splits) (hP0 : P≠0) (hf : v^2+W*H=q*P)
    (b1 d1 b2 d2 b3 d3 : ℝ)
    (hp1 : b1^2<4*d1) (hp2 : b2^2<4*d2) (hp3 : b3^2<4*d3)
    (h1 : C delta*(quad b1 d1)^2=H)
    (h2 : C delta*(quad b2 d2)^2=H+C (2*b)*v-C (b^2)*W)
    (h3 : C delta*(quad b3 d3)^2=H+C (2*(a+b))*v-C ((a+b)^2)*W) :
    a*b1+b*b3+(a+b)*b2=2*(a+b)*q.coeff 1 := by
  let Q := C a*quad b1 d1+C b*quad b3 d3+C (a+b)*quad b2 d2
  have hcoeff : Q.coeff 2=2*(a+b) := by
    dsimp [Q]
    simp only [coeff_add,coeff_C_mul,quad_coeff_two,mul_one]
    ring
  have hQdeg : Q.natDegree=2 := by
    apply Nat.le_antisymm
    · dsimp [Q,quad]; compute_degree
    · apply le_natDegree_of_ne_zero
      rw [hcoeff]
      positivity
  have he := positive_quadratic_factor_unique Q q P hQdeg hq hqm hP hP0
    (fun x => by
      dsimp [Q]
      simp only [eval_add,eval_mul,eval_C]
      exact add_pos (add_pos (mul_pos ha (quad_positive hp1 x))
        (mul_pos hb (quad_positive hp3 x)))
        (mul_pos (add_pos ha hb) (quad_positive hp2 x)))
    (hf ▸ heron_factor_dvd delta a b ha hb H v W _ _ _ h1 h2 h3)
  have he1 := congrArg (fun f : ℝ[X] => f.coeff 1) he
  rw [hcoeff] at he1
  simpa only [Q,quad,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,
    Nat.reduceEqDiff,if_false,if_true,mul_zero,mul_one,zero_add,add_zero] using he1

lemma parameter_relation (delta a b h v q beta0 beta1 beta2 : ℝ)
    (hab : a+b≠0)
    (h0 : 2*delta*beta0=h)
    (h1 : 2*delta*beta1=h+2*b*v-b^2)
    (h2 : 2*delta*beta2=h+2*(a+b)*v-(a+b)^2)
    (hQ : a*beta0+b*beta2+(a+b)*beta1=2*(a+b)*q) :
    2*h+4*b*v-b*(a+2*b)=4*delta*q := by
  have hh : (a+b)*(2*h+4*b*v-b*(a+2*b)-4*delta*q)=0 := by
    linear_combination -a*h0-b*h2-(a+b)*h1+2*delta*hQ
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hab)

lemma quad_square_coeff_three (delta beta d : ℝ) :
    (C delta*(quad beta d)^2).coeff 3=2*delta*beta := by
  have he : C delta*(quad beta d)^2 =
      C delta*X^4+C (2*delta*beta)*X^3+C (delta*(beta^2+2*d))*X^2+
        C (2*delta*beta*d)*X+C (delta*d^2) := by
    simp only [quad,map_mul,map_add,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,
    Nat.reduceEqDiff,if_false,if_true,mul_zero,mul_one,zero_add,add_zero]

lemma no_four_normalized (delta a b d : ℝ) (ha : 0<a) (hb : 0<b) (had : a<d)
    (H v W q P : ℝ[X]) (hW : W.coeff 3=1)
    (hq : q.natDegree=2) (hqm : q.Monic)
    (hP : P.Splits) (hP0 : P≠0) (hf : v^2+W*H=q*P)
    (b1 d1 b2 d2 b3 d3 b4 d4 : ℝ)
    (hp1 : b1^2<4*d1) (hp2 : b2^2<4*d2)
    (hp3 : b3^2<4*d3) (hp4 : b4^2<4*d4)
    (h1 : C delta*(quad b1 d1)^2=H)
    (h2 : C delta*(quad b2 d2)^2=H+C (2*b)*v-C (b^2)*W)
    (h3 : C delta*(quad b3 d3)^2=H+C (2*(a+b))*v-C ((a+b)^2)*W)
    (h4 : C delta*(quad b4 d4)^2=H+C (2*(d+b))*v-C ((d+b)^2)*W) : False := by
  have hd : 0<d := ha.trans had
  have hQ3 := heron_factor_coeff_one delta a b ha hb H v W q P hq hqm hP hP0 hf
    b1 d1 b2 d2 b3 d3 hp1 hp2 hp3 h1 h2 h3
  have hQ4 := heron_factor_coeff_one delta d b hd hb H v W q P hq hqm hP hP0 hf
    b1 d1 b2 d2 b4 d4 hp1 hp2 hp4 h1 h2 h4
  have he1 := congrArg (fun f : ℝ[X] => f.coeff 3) h1
  have he2 := congrArg (fun f : ℝ[X] => f.coeff 3) h2
  have he3 := congrArg (fun f : ℝ[X] => f.coeff 3) h3
  have he4 := congrArg (fun f : ℝ[X] => f.coeff 3) h4
  dsimp only at he1 he2 he3 he4
  rw [quad_square_coeff_three] at he1 he2 he3 he4
  simp only [coeff_sub,coeff_add,coeff_C_mul,hW,mul_one] at he2 he3 he4
  have hrel3 := parameter_relation delta a b (H.coeff 3) (v.coeff 3) (q.coeff 1)
    b1 b2 b3 (ne_of_gt (add_pos ha hb)) he1 he2 he3 hQ3
  have hrel4 := parameter_relation delta d b (H.coeff 3) (v.coeff 3) (q.coeff 1)
    b1 b2 b4 (ne_of_gt (add_pos hd hb)) he1 he2 he4 hQ4
  nlinarith [mul_pos hb (sub_pos.mpr had)]

lemma no_ordered_quadruple (delta : ℝ) (H v W q P : ℝ[X])
    (hW : W.coeff 3=1) (hq : q.natDegree=2) (hqm : q.Monic)
    (hP : P.Splits) (hP0 : P≠0) (hf : v^2+W*H=q*P)
    {c1 c2 c3 c4 : ℝ} (h12 : c1<c2) (h23 : c2<c3) (h34 : c3<c4)
    (h1 : c1 ∈ negativeDiscriminantParams delta H v W)
    (h2 : c2 ∈ negativeDiscriminantParams delta H v W)
    (h3 : c3 ∈ negativeDiscriminantParams delta H v W)
    (h4 : c4 ∈ negativeDiscriminantParams delta H v W) : False := by
  obtain ⟨b1,d1,hp1,hu1⟩ := h1
  obtain ⟨b2,d2,hp2,hu2⟩ := h2
  obtain ⟨b3,d3,hp3,hu3⟩ := h3
  obtain ⟨b4,d4,hp4,hu4⟩ := h4
  let H' := H+C (2*c1)*v-C (c1^2)*W
  let v' := v-C c1*W
  have he : v'^2+W*H'=v^2+W*H := by
    dsimp [v',H']
    simp only [map_mul,map_pow,map_ofNat]
    ring
  apply no_four_normalized delta (c3-c2) (c2-c1) (c4-c2)
    (sub_pos.mpr h23) (sub_pos.mpr h12) (by linarith)
    H' v' W q P hW hq hqm hP hP0 (he.trans hf)
    b1 d1 b2 d2 b3 d3 b4 d4 hp1 hp2 hp3 hp4 hu1
  · convert hu2 using 1
    dsimp [H',v']
    simp only [map_sub,map_mul,map_pow,map_ofNat]
    ring
  · convert hu3 using 1
    dsimp [H',v']
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat]
    ring
  · convert hu4 using 1
    dsimp [H',v']
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat]
    ring

/-- The fixed-pencil bound is three when the branch polynomial has a
monic quadratic factor and all remaining factors split over the reals. -/
theorem negativeParams_finite_and_ncard_le_three (delta : ℝ) (H v W q P : ℝ[X])
    (hW : W.coeff 3=1) (hq : q.natDegree=2) (hqm : q.Monic)
    (hP : P.Splits) (hP0 : P≠0) (hf : v^2+W*H=q*P) :
    (negativeDiscriminantParams delta H v W).Finite ∧
      (negativeDiscriminantParams delta H v W).ncard≤3 := by
  classical
  let S := negativeDiscriminantParams delta H v W
  have hb : ∀ T : Finset ℝ, (T : Set ℝ) ⊆ S → T.card≤3 := by
    intro T hT
    by_contra hcard
    have hfour : 4≤T.card := by omega
    let e := T.orderEmbOfCardLe hfour
    have hm (i : Fin 4) : e i∈S := hT (T.orderEmbOfCardLe_mem hfour i)
    exact no_ordered_quadruple delta H v W q P hW hq hqm hP hP0 hf
      (e.strictMono (by decide : (0 : Fin 4)<1))
      (e.strictMono (by decide : (1 : Fin 4)<2))
      (e.strictMono (by decide : (2 : Fin 4)<3)) (hm 0) (hm 1) (hm 2) (hm 3)
  have hfin : S.Finite := by
    by_contra hi
    obtain ⟨T,hT,hcard⟩ := Set.Infinite.exists_subset_card_eq hi 4
    have hh := hb T hT
    omega
  refine ⟨hfin,?_⟩
  change S.ncard≤3
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact hb hfin.toFinset (by simp)

def oldBranch : ℝ[X] := X*(X^2-1)*(X^2-9)*(X^2+3)

/-- This includes every nonzero real twist of the old nonsplit degree-seven
model. It bounds one quadratic pencil, not all its rational points. -/
theorem oldBranch_bound (delta k : ℝ) (H v W : ℝ[X]) (hk : k≠0)
    (hW : W.coeff 3=1) (hf : v^2+W*H=C k*oldBranch) :
    (negativeDiscriminantParams delta H v W).Finite ∧
      (negativeDiscriminantParams delta H v W).ncard≤3 := by
  let G : ℝ[X] := X*(X-C 1)*(X+C 1)*(X-C 3)*(X+C 3)
  have hGm : G.Monic :=
    ((((monic_X.mul (monic_X_sub_C 1)).mul (monic_X_add_C 1)).mul
      (monic_X_sub_C 3)).mul (monic_X_add_C 3))
  have hGs : G.Splits :=
    ((((Splits.X.mul (Splits.X_sub_C 1)).mul (Splits.X_add_C 1)).mul
      (Splits.X_sub_C 3)).mul (Splits.X_add_C 3))
  apply negativeParams_finite_and_ncard_le_three delta H v W (X^2+C 3) (C k*G)
    hW (by compute_degree; norm_num) (monic_X_pow_add_C _ (by decide)) (hGs.C_mul k)
    (mul_ne_zero (by simpa using hk) hGm.ne_zero)
  rw [hf]
  dsimp [G,oldBranch]
  norm_num only [map_ofNat,map_one]
  ring

def controlH : ℝ[X] := C (-3/4)*X^4+C (13/4)*X^3-C (115/12)*X^2+
  C (79/4)*X-C (147/4)
def controlV : ℝ[X] := -C (35/6)*X^2+C 7*X-C 21
def controlW : ℝ[X] := X^3+C (13/3)*X^2-X+C 12

lemma control_branch : controlV^2+controlW*controlH=C (-3/4)*oldBranch := by
  apply Polynomial.funext
  intro x
  simp only [controlV,controlW,controlH,oldBranch,eval_add,eval_sub,eval_neg,
    eval_mul,eval_pow,eval_X,eval_C,eval_one,eval_ofNat]
  ring

lemma control_three :
    (-5/2 : ℝ)∈negativeDiscriminantParams (-3/4) controlH controlV controlW ∧
    (-3/2 : ℝ)∈negativeDiscriminantParams (-3/4) controlH controlV controlW ∧
    (1/2 : ℝ)∈negativeDiscriminantParams (-3/4) controlH controlV controlW := by
  refine ⟨⟨2,3,by norm_num,?_⟩,⟨-2/3,1,by norm_num,?_⟩,⟨-2,9,by norm_num,?_⟩⟩
  all_goals apply Polynomial.funext; intro x
  all_goals simp only [controlH,controlV,controlW,eval_add,eval_sub,eval_neg,
    eval_mul,eval_pow,eval_X,eval_C]
  all_goals ring

/-- Three really occur: the nonsplit bound must not be replaced by the
previous split-branch bound of two. No metric conclusion is asserted. -/
lemma control_ncard_eq_three :
    (negativeDiscriminantParams (-3/4) controlH controlV controlW).ncard=3 := by
  have hh := oldBranch_bound (-3/4) (-3/4) controlH controlV controlW
    (by norm_num) (by simp [controlW,coeff_X]) control_branch
  apply Nat.le_antisymm hh.2
  have hl : 2 < (negativeDiscriminantParams (-3/4) controlH controlV controlW).ncard := by
    apply (Set.two_lt_ncard_iff hh.1).mpr
    exact ⟨-5/2,-3/2,1/2,control_three.1,control_three.2.1,control_three.2.2,
      by norm_num,by norm_num,by norm_num⟩
  omega

#print axioms negativeParams_finite_and_ncard_le_three
#print axioms oldBranch_bound
#print axioms control_ncard_eq_three
#print axioms no_ordered_quadruple
#print axioms positive_quadratic_factor_unique
#print axioms heron_factor_coeff_one
#print axioms parameter_relation
end
end Erdos213.NonsplitQuadraticFiber
