import FormalConjecturesUtil

/-! Four real fourth powers of ternary linear forms cannot have a positive
quadratic factor. This file first treats two diagonal positive factors. -/
namespace Erdos322Research.PositiveQuadraticFactor
noncomputable section
open Finset
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

private def testPoints : Fin 15 → Fin 3 → ℝ :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![1, 1, 0],
    ![1, -1, 0],
    ![2, 1, 0],
    ![1, 0, 1],
    ![1, 0, -1],
    ![2, 0, 1],
    ![0, 1, 1],
    ![0, 1, -1],
    ![0, 2, 1],
    ![1, 1, 1],
    ![1, 1, -1],
    ![1, -1, 1]]

private def weights (q : Fin 6 → ℝ) : Fin 15 → ℝ :=
  ![12*q 0^2 - 4*q 0*q 1 - 4*q 0*q 2 - 12*q 0*q 3 - 12*q 0*q 4 - 2*q 0*q 5 + 12*q 1*q 3 + 2*q 1*q 4 + 2*q 2*q 3 + 12*q 2*q 4 - 2*q 3^2 - 2*q 3*q 4 + 2*q 3*q 5 - 2*q 4^2 + 2*q 4*q 5,
    -4*q 0*q 1 + 3*q 0*q 3 - 2*q 0*q 5 + 12*q 1^2 - 4*q 1*q 2 - 3*q 1*q 3 + 2*q 1*q 4 - 12*q 1*q 5 + 2*q 2*q 3 + 12*q 2*q 5 - 2*q 3^2 - 2*q 3*q 4 + 2*q 3*q 5 + 2*q 4*q 5 - 2*q 5^2,
    -4*q 0*q 2 + 3*q 0*q 4 - 2*q 0*q 5 - 4*q 1*q 2 + 2*q 1*q 4 + 3*q 1*q 5 + 12*q 2^2 + 2*q 2*q 3 - 3*q 2*q 4 - 3*q 2*q 5 - 2*q 3*q 4 + 2*q 3*q 5 - 2*q 4^2 + 2*q 4*q 5 - 2*q 5^2,
    2*q 0*q 1 - 3*q 0*q 3 + q 0*q 5 + 6*q 1*q 3 - q 1*q 4 - 2*q 2*q 3 + q 3^2 + q 3*q 4 - q 3*q 5 - 2*q 4*q 5,
    2*q 0*q 1 - q 0*q 3 + q 0*q 5 - 2*q 1*q 3 - q 1*q 4 + q 3^2 + q 3*q 4 - q 3*q 5,
    q 0*q 3 - q 1*q 3,
    2*q 0*q 2 - 3*q 0*q 4 + q 0*q 5 - 2*q 1*q 4 - q 2*q 3 + 6*q 2*q 4 + q 3*q 4 - 2*q 3*q 5 + q 4^2 - q 4*q 5,
    2*q 0*q 2 - q 0*q 4 + q 0*q 5 - q 2*q 3 - 2*q 2*q 4 + q 3*q 4 + q 4^2 - q 4*q 5,
    q 0*q 4 - q 2*q 4,
    2*q 1*q 2 - q 1*q 4 - 3*q 1*q 5 - q 2*q 3 + 6*q 2*q 5 - q 3*q 5 - q 4*q 5 + q 5^2,
    2*q 0*q 5 + 2*q 1*q 2 - q 1*q 4 - q 1*q 5 - q 2*q 3 - 2*q 2*q 5 + 2*q 3*q 4 - q 3*q 5 - q 4*q 5 + q 5^2,
    q 1*q 5 - q 2*q 5,
    q 1*q 4 + q 2*q 3 + q 3*q 5 + q 4*q 5,
    -q 0*q 5 + q 2*q 3 - q 3*q 4 + q 4*q 5,
    -q 0*q 5 + q 1*q 4 - q 3*q 4 + q 3*q 5]

private def quadraticEval (a : Fin 3 → ℝ) (q : Fin 6 → ℝ) : ℝ :=
  q 0*a 0^2 + q 1*a 1^2 + q 2*a 2^2 + q 3*a 0*a 1 + q 4*a 0*a 2 + q 5*a 1*a 2

private def positiveForm (q : Fin 6 → ℝ) : ℝ :=
  2*((q 0)^2+(q 1)^2+(q 2)^2)+(q 0+q 1+q 2)^2+(q 3)^2+(q 4)^2+(q 5)^2

private theorem quartic_polarization (a : Fin 3 → ℝ) (q : Fin 6 → ℝ) :
    12 * quadraticEval a q ^ 2 =
      ∑ j, weights q j * (∑ k, a k * testPoints j k)^4 := by
  norm_num [quadraticEval, weights, testPoints, Fin.sum_univ_succ]
  ring


private def gram (a b c : ℝ) (q : Fin 6 → ℝ) : ℝ :=
  12*(a*q 0^2+b*q 1^2+c*q 2^2) +
  4*((a+b)*q 0*q 1+(a+c)*q 0*q 2+(b+c)*q 1*q 2) +
  2*((a+b)*q 3^2+(a+c)*q 4^2+(b+c)*q 5^2)

private theorem weights_diagonal (a b c : ℝ) (q : Fin 6 → ℝ) :
    ∑ j, weights q j * ((∑ k, testPoints j k^2)*
      (a*testPoints j 0^2+b*testPoints j 1^2+c*testPoints j 2^2)) = gram a b c q := by
  norm_num [gram, weights, testPoints, Fin.sum_univ_succ]
  dsimp
  ring

private theorem gram_identity (v : Fin 4 → Fin 3 → ℝ) (a b c : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (∑ j, v i j*x j)^4 =
      (∑ j, x j^2)*(a*x 0^2+b*x 1^2+c*x 2^2)) (q : Fin 6 → ℝ) :
    12*(∑ i, quadraticEval (v i) q^2)=gram a b c q := by
  calc
    12*(∑ i, quadraticEval (v i) q^2) =
        ∑ i, ∑ j, weights q j*(∑ k, v i k*testPoints j k)^4 := by
      rw [mul_sum]
      exact sum_congr rfl (fun i _ ↦ quartic_polarization (v i) q)
    _ = ∑ j, weights q j*(∑ i, (∑ k, v i k*testPoints j k)^4) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = gram a b c q := by simp_rw [h]; exact weights_diagonal a b c q

private theorem strict_gram_zero (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hd : (a+b)^2 < 36*a*b) (q : Fin 5 → ℝ)
    (hz : gram a b c ![q 0,q 1,0,q 2,q 3,q 4]=0) : q=0 := by
  let D := 36*a*b-(a+b)^2
  have hD : 0<D := sub_pos.mpr hd
  have he : (6*a*q 0+(a+b)*q 1)^2+D*q 1^2+
      (6*a*(a+b))*q 2^2+(6*a*(a+c))*q 3^2+(6*a*(b+c))*q 4^2=0 := by
    dsimp only [D]
    dsimp [gram] at hz
    linear_combination 3*a*hz
  have hn0 := sq_nonneg (6*a*q 0+(a+b)*q 1)
  have hn1 := mul_nonneg hD.le (sq_nonneg (q 1))
  have hA : 0<6*a*(a+b) := by positivity
  have hB : 0<6*a*(a+c) := by positivity
  have hC : 0<6*a*(b+c) := by positivity
  have hn2 := mul_nonneg hA.le (sq_nonneg (q 2))
  have hn3 := mul_nonneg hB.le (sq_nonneg (q 3))
  have hn4 := mul_nonneg hC.le (sq_nonneg (q 4))
  have h1 : q 1=0 := by
    have hh : D*q 1^2=0 := by linarith only [he,hn0,hn1,hn2,hn3,hn4]
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left hD.ne')
  have h2 : q 2=0 := by
    have hh : (6*a*(a+b))*q 2^2=0 := by linarith only [he,hn0,hn1,hn2,hn3,hn4]
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left hA.ne')
  have h3 : q 3=0 := by
    have hh : (6*a*(a+c))*q 3^2=0 := by linarith only [he,hn0,hn1,hn2,hn3,hn4]
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left hB.ne')
  have h4 : q 4=0 := by
    have hh : (6*a*(b+c))*q 4^2=0 := by linarith only [he,hn0,hn1,hn2,hn3,hn4]
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left hC.ne')
  have h0 : q 0=0 := by
    have hh : (6*a*q 0+(a+b)*q 1)^2=0 := by linarith only [he,hn0,hn1,hn2,hn3,hn4]
    rw [h1,mul_zero,add_zero] at hh
    have hmul : 6*a*q 0=0 := eq_zero_of_pow_eq_zero hh
    exact (mul_eq_zero.mp hmul).resolve_left (by positivity)
  funext i
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

private theorem pair_relation (v : Fin 4 → Fin 3 → ℝ) (a b c : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (∑ j, v i j*x j)^4 =
      (∑ j, x j^2)*(a*x 0^2+b*x 1^2+c*x 2^2)) :
    (a+b)^2=36*a*b := by
  have hnonneg : 0≤gram a b c ![-(a+b),6*a,0,0,0,0] := by
    rw [← gram_identity v a b c h]
    positivity
  have hd : (a+b)^2≤36*a*b := by
    have hh : 0≤12*a*(36*a*b-(a+b)^2) := by
      convert hnonneg using 1
      dsimp [gram]
      ring
    have hD : 0≤36*a*b-(a+b)^2 := (mul_nonneg_iff_of_pos_left (by positivity : 0<12*a)).mp hh
    linarith
  by_contra hn
  have hstrict : (a+b)^2<36*a*b := lt_of_le_of_ne hd hn
  let L : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun q i ↦ quadraticEval (v i) ![q 0,q 1,0,q 2,q 3,q 4]
      map_add' := by intro q r; funext i; simp [quadraticEval]; ring
      map_smul' := by intro t q; funext i; simp [quadraticEval]; ring }
  have hL : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro q hq
    apply strict_gram_zero a b c ha hb hc hstrict q
    rw [← gram_identity v a b c h]
    have hh (i) : quadraticEval (v i) ![q 0,q 1,0,q 2,q 3,q 4]=0 := congrFun hq i
    simp only [hh,zero_pow (by decide : 2≠0),sum_const_zero,mul_zero]
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  norm_num at hdim

/-- Four real fourth powers cannot equal the product of a Euclidean ternary
norm and another positive diagonal ternary quadratic form. -/
theorem no_positive_diagonal_factor (v : Fin 4 → Fin 3 → ℝ) (a b c : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    ¬ (∀ x : Fin 3 → ℝ, ∑ i, (∑ j, v i j*x j)^4 =
      (∑ j, x j^2)*(a*x 0^2+b*x 1^2+c*x 2^2)) := by
  intro h
  have hab := pair_relation v a b c ha hb hc h
  have hac : (a+c)^2=36*a*c := by
    apply pair_relation (fun i ↦ ![v i 0,v i 2,v i 1]) a c b ha hc hb
    intro x
    have hh := h ![x 0,x 2,x 1]
    simp only [Fin.sum_univ_three] at hh ⊢
    dsimp at hh ⊢
    convert hh using 1
    · apply sum_congr rfl
      intro i _
      ring
    · ring
  have hbc : (b+c)^2=36*b*c := by
    apply pair_relation (fun i ↦ ![v i 1,v i 2,v i 0]) b c a hb hc ha
    intro x
    have hh := h ![x 2,x 0,x 1]
    simp only [Fin.sum_univ_three] at hh ⊢
    dsimp at hh ⊢
    convert hh using 1
    · apply sum_congr rfl
      intro i _
      ring
    · ring
  have habn : a≠b := by intro he; rw [he] at hab; nlinarith
  have hacn : a≠c := by intro he; rw [he] at hac; nlinarith
  have hbcn : b≠c := by intro he; rw [he] at hbc; nlinarith
  have h1 : b+c=34*a := by
    have he : (b-c)*(b+c-34*a)=0 := by nlinarith only [hab,hac]
    have := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hbcn)
    linarith
  have h2 : a+c=34*b := by
    have he : (a-c)*(a+c-34*b)=0 := by nlinarith only [hab,hbc]
    have := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hacn)
    linarith
  have h3 : a+b=34*c := by
    have he : (a-b)*(a+b-34*c)=0 := by nlinarith only [hac,hbc]
    have := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr habn)
    linarith
  linarith

private theorem coord_zero (v : Fin 4 → Fin 3 → ℝ) (j : Fin 3)
    (hz : ∑ i, (v i j)^4 = 0) (i : Fin 4) : v i j = 0 := by
  apply eq_zero_of_pow_eq_zero
  exact (sum_eq_zero_iff_of_nonneg (fun i _ ↦ by positivity)).mp hz i (mem_univ i)

private theorem factor_first_zero (v : Fin 4 → Fin 3 → ℝ) (b c : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (∑ j, v i j*x j)^4 =
      (∑ j, x j^2)*(0*x 0^2+b*x 1^2+c*x 2^2)) : v=0 := by
  have h0 := h ![1,0,0]
  have h1 := h ![0,1,0]
  have h2 := h ![0,0,1]
  have h01 := h ![1,1,0]
  have h02 := h ![1,0,1]
  simp only [Fin.sum_univ_three] at h0 h1 h2 h01 h02
  dsimp at h0 h1 h2 h01 h02
  norm_num at h0 h1 h2 h01 h02
  have hv0 (i) : v i 0=0 := coord_zero v 0 h0 i
  simp only [hv0,zero_add] at h01 h02
  have hb : b=0 := by linarith only [h1,h01]
  have hc : c=0 := by linarith only [h2,h02]
  rw [hb] at h1
  rw [hc] at h2
  funext i j
  fin_cases j
  · exact hv0 i
  · exact coord_zero v 1 h1 i
  · exact coord_zero v 2 h2 i

/-- Even a semidefinite diagonal factor is impossible unless all four linear
forms vanish. The coefficients are not assumed nonnegative: the identity
itself forces their nonnegativity. -/
theorem diagonal_factor_is_zero (v : Fin 4 → Fin 3 → ℝ) (a b c : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (∑ j, v i j*x j)^4 =
      (∑ j, x j^2)*(a*x 0^2+b*x 1^2+c*x 2^2)) : v=0 := by
  have h0 := h ![1,0,0]
  have h1 := h ![0,1,0]
  have h2 := h ![0,0,1]
  simp only [Fin.sum_univ_three] at h0 h1 h2
  dsimp at h0 h1 h2
  norm_num at h0 h1 h2
  have ha : 0≤a := h0 ▸ (by positivity : 0≤∑ i, (v i 0)^4)
  have hb : 0≤b := h1 ▸ (by positivity : 0≤∑ i, (v i 1)^4)
  have hc : 0≤c := h2 ▸ (by positivity : 0≤∑ i, (v i 2)^4)
  by_cases haz : a=0
  · rw [haz] at h
    exact factor_first_zero v b c h
  by_cases hbz : b=0
  · have hh : (fun i ↦ ![v i 1,v i 0,v i 2]) = (0 : Fin 4 → Fin 3 → ℝ) := by
      apply factor_first_zero _ a c
      intro x
      have hx := h ![x 1,x 0,x 2]
      simp only [Fin.sum_univ_three] at hx ⊢
      dsimp at hx ⊢
      rw [hbz] at hx
      convert hx using 1
      · apply sum_congr rfl
        intro i _
        ring
      · ring
    funext i j
    fin_cases j
    · exact congrFun (congrFun hh i) 1
    · exact congrFun (congrFun hh i) 0
    · exact congrFun (congrFun hh i) 2
  by_cases hcz : c=0
  · have hh : (fun i ↦ ![v i 2,v i 1,v i 0]) = (0 : Fin 4 → Fin 3 → ℝ) := by
      apply factor_first_zero _ b a
      intro x
      have hx := h ![x 2,x 1,x 0]
      simp only [Fin.sum_univ_three] at hx ⊢
      dsimp at hx ⊢
      rw [hcz] at hx
      convert hx using 1
      · apply sum_congr rfl
        intro i _
        ring
      · ring
    funext i j
    fin_cases j
    · exact congrFun (congrFun hh i) 2
    · exact congrFun (congrFun hh i) 1
    · exact congrFun (congrFun hh i) 0
  exact False.elim (no_positive_diagonal_factor v a b c
    (lt_of_le_of_ne ha (Ne.symm haz)) (lt_of_le_of_ne hb (Ne.symm hbz))
    (lt_of_le_of_ne hc (Ne.symm hcz)) h)

end
end Erdos322Research.PositiveQuadraticFactor
