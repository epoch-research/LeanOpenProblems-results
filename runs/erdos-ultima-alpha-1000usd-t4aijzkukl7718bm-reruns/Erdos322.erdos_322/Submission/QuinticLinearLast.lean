import FormalConjecturesUtil

/-! An obstruction to the linear-midpoint cubic chart for five fifth powers
when the last coordinate has degree at most one. This is a restricted-family
result, not a proof or disproof of Erdős 322. -/
namespace Erdos322Research.QuinticLinearLast
noncomputable section
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private def cubic (a b c : ℝ) : ℝ[X] := X^3 + C a*X^2 + C b*X + C c

def core (a b c d e f U V : ℝ) : ℝ[X] :=
  5 * (X * cubic a b c ^ 4 + (1-X) * cubic d e f ^ 4) +
  10 * (C U * X^3 * cubic a b c ^ 2 + C V * (1-X)^3 * cubic d e f ^ 2) +
  C (U^2) * X^5 + C (V^2) * (1-X)^5

private def q12 (a b c d e f U V : ℝ) : ℝ :=
  20 * a - 20 * d + 5

private def q11 (a b c d e f U V : ℝ) : ℝ :=
  30 * a ^ 2 - 30 * d ^ 2 + 20 * b + 20 * d - 20 * e

private def q10 (a b c d e f U V : ℝ) : ℝ :=
  20 * a ^ 3 - 20 * d ^ 3 + 60 * a * b + 30 * d ^ 2 - 60 * d * e + 20 * c + 20 * e - 20 * f

private def q9 (a b c d e f U V : ℝ) : ℝ :=
  5 * a ^ 4 - 5 * d ^ 4 + 60 * a ^ 2 * b + 20 * d ^ 3 - 60 * d ^ 2 * e + 30 * b ^ 2 + 60 * a * c + 60 * d * e - 30 * e ^ 2 - 60 * d * f + 20 * f + 10 * U - 10 * V

private def q8 (a b c d e f U V : ℝ) : ℝ :=
  20 * a ^ 3 * b + 5 * d ^ 4 - 20 * d ^ 3 * e + 60 * a * b ^ 2 + 60 * a ^ 2 * c + 60 * d ^ 2 * e - 60 * d * e ^ 2 - 60 * d ^ 2 * f + 60 * b * c + 30 * e ^ 2 + 60 * d * f - 60 * e * f + 20 * a * U - 20 * d * V + 30 * V

private def q7 (a b c d e f U V : ℝ) : ℝ :=
  30 * a ^ 2 * b ^ 2 + 20 * a ^ 3 * c + 20 * d ^ 3 * e - 30 * d ^ 2 * e ^ 2 - 20 * d ^ 3 * f + 20 * b ^ 3 + 120 * a * b * c + 60 * d * e ^ 2 - 20 * e ^ 3 + 60 * d ^ 2 * f - 120 * d * e * f + 10 * a ^ 2 * U - 10 * d ^ 2 * V + 30 * c ^ 2 + 60 * e * f - 30 * f ^ 2 + 20 * b * U + 60 * d * V - 20 * e * V - 30 * V

private def q6 (a b c d e f U V : ℝ) : ℝ :=
  20 * a * b ^ 3 + 60 * a ^ 2 * b * c + 30 * d ^ 2 * e ^ 2 - 20 * d * e ^ 3 + 20 * d ^ 3 * f - 60 * d ^ 2 * e * f + 60 * b ^ 2 * c + 60 * a * c ^ 2 + 20 * e ^ 3 + 120 * d * e * f - 60 * e ^ 2 * f - 60 * d * f ^ 2 + 20 * a * b * U + 30 * d ^ 2 * V - 20 * d * e * V + 30 * f ^ 2 + 20 * c * U - 60 * d * V + 60 * e * V - 20 * f * V + 10 * V

private lemma coeff12 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 12 = q12 a b c d e f U V := by
  unfold core cubic q12
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num

private lemma coeff11 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 11 = q11 a b c d e f U V := by
  unfold core cubic q11
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff10 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 10 = q10 a b c d e f U V := by
  unfold core cubic q10
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff9 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 9 = q9 a b c d e f U V := by
  unfold core cubic q9
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff8 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 8 = q8 a b c d e f U V := by
  unfold core cubic q8
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff7 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 7 = q7 a b c d e f U V := by
  unfold core cubic q7
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff6 (a b c d e f U V : ℝ) :
    (core a b c d e f U V).coeff 6 = q6 a b c d e f U V := by
  unfold core cubic q6
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_one, coeff_mul_ofNat]
  norm_num
  ring

private def aVal (h : ℝ) : ℝ := h-13/8
private def bVal (h v M : ℝ) : ℝ := 117/160-9*h/8-(128/5)*h*v-64*M
private def cVal (h v M : ℝ) : ℝ := 2*v-15*aVal h/32-5*bVal h v M/8-195/512
private def dVal (h : ℝ) : ℝ := aVal h+1/4
private def eVal (h v M : ℝ) : ℝ := bVal h v M+aVal h/4+5/32
private def fVal (h v M : ℝ) : ℝ := cVal h v M+bVal h v M/4+5*aVal h/32+15/128

private lemma positive_invariant (h v M : ℝ) :
    262144*(q6 (aVal h) (bVal h v M) (cVal h v M) (dVal h)
          (eVal h v M) (fVal h v M) (M-v/2) (M+v/2) -
      (2*h-7/2)*q7 (aVal h) (bVal h v M) (cVal h v M) (dVal h)
          (eVal h v M) (fVal h v M) (M-v/2) (M+v/2)) =
      (8192*h*v+20480*M)^2+6720*h^2+5242880*v^2+614400*M+429 := by
  dsimp [q6,q7,aVal,bVal,cVal,dVal,eVal,fVal]
  ring

private lemma high_coefficients_not_all_zero (a b c d e f U V : ℝ)
    (hUV : 0 ≤ U+V)
    (z12 : q12 a b c d e f U V = 0)
    (z11 : q11 a b c d e f U V = 0)
    (z10 : q10 a b c d e f U V = 0)
    (z9 : q9 a b c d e f U V = 0)
    (z8 : q8 a b c d e f U V = 0)
    (z7 : q7 a b c d e f U V = 0)
    (z6 : q6 a b c d e f U V = 0) : False := by
  have hd : d=a+1/4 := by dsimp [q12] at z12; linarith only [z12]
  have he : e=b+a/4+5/32 := by
    rw [hd] at z11
    dsimp [q11] at z11
    nlinarith only [z11]
  have hf : f=c+b/4+5*a/32+15/128 := by
    rw [hd,he] at z10
    dsimp [q10] at z10
    nlinarith only [z10]
  let h := a+13/8
  let v := V-U
  let M := (U+V)/2
  have ha : a=aVal h := by dsimp [aVal,h]; ring
  have hc : c=2*v-15*a/32-5*b/8-195/512 := by
    rw [hd,he,hf] at z9
    dsimp [q9] at z9
    dsimp [v]
    nlinarith only [z9]
  have hb : b=bVal h v M := by
    rw [hd,he,hf,hc] at z8
    dsimp [q8] at z8
    dsimp [bVal,h,v,M]
    dsimp [v] at z8
    nlinarith only [z8]
  have hc' : c=cVal h v M := by rw [hc,ha,hb]; rfl
  have hd' : d=dVal h := by rw [hd,ha]; rfl
  have he' : e=eVal h v M := by rw [he,ha,hb]; rfl
  have hf' : f=fVal h v M := by rw [hf,ha,hb,hc']; rfl
  have hU : U=M-v/2 := by dsimp [M,v]; ring
  have hV : V=M+v/2 := by dsimp [M,v]; ring
  rw [ha,hb,hc',hd',he',hf',hU,hV] at z6 z7
  have hi := positive_invariant h v M
  rw [z6,z7] at hi
  have hM : 0 ≤ M := div_nonneg hUV (by norm_num)
  nlinarith only [hi, sq_nonneg (8192*h*v+20480*M), sq_nonneg h, sq_nonneg v, hM]

/-- The first four contributions in this normalized chart cannot have degree
at most five. The assumption is weaker than the two weights being nonnegative. -/
theorem core_degree_at_least_six (a b c d e f U V : ℝ) (hUV : 0 ≤ U+V) :
    6 ≤ (core a b c d e f U V).natDegree := by
  by_contra hn
  have hz (i : ℕ) (hi : 6 ≤ i) : (core a b c d e f U V).coeff i = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  apply high_coefficients_not_all_zero a b c d e f U V hUV
  · simpa only [coeff12] using hz 12 (by omega)
  · simpa only [coeff11] using hz 11 (by omega)
  · simpa only [coeff10] using hz 10 (by omega)
  · simpa only [coeff9] using hz 9 (by omega)
  · simpa only [coeff8] using hz 8 (by omega)
  · simpa only [coeff7] using hz 7 (by omega)
  · simpa only [coeff6] using hz 6 (by omega)

/-- Adding a polynomial of degree at most five cannot cancel this core. -/
theorem no_constant_low_degree_tail (a b c d e f U V k N : ℝ)
    (hUV : 0 ≤ U+V) (hk : k ≠ 0) (p : ℝ[X]) (hp : p.natDegree ≤ 5) :
    C k * core a b c d e f U V + p ≠ C N := by
  intro he
  have hdeg : (core a b c d e f U V).natDegree ≤ 5 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hpi : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hni : i ≠ 0 := by omega
    have he' := congrArg (fun p : ℝ[X] ↦ p.coeff i) he
    simp only [coeff_add,coeff_C_mul,hpi,add_zero,coeff_C,if_neg hni] at he'
    exact (mul_eq_zero.mp he').resolve_left hk
  have := core_degree_at_least_six a b c d e f U V hUV
  omega

/-- The normalized linear-midpoint cubic chart. The second pair has an
arbitrary nonzero leading ratio, and the last coordinate is linear. -/
def coordinates (a b c d e f q r v w t : ℝ) : Fin 5 → ℝ :=
  let A := t^3+a*t^2+b*t+c
  let D := r*(t^3+d*t^2+e*t+f)
  ![A+q*t,-A+q*t,D+q/r^4*(1-t),-D+q/r^4*(1-t),v*t+w]

private lemma coordinates_sum (a b c d e f q r v w t : ℝ) (hr : r ≠ 0) :
    ∑ i, coordinates a b c d e f q r v w t i ^ 5 =
      2*q*(core a b c d e f (q^2) ((q/r^5)^2)).eval t+(v*t+w)^5 := by
  simp [coordinates,Fin.sum_univ_succ,core,cubic]
  field_simp
  ring

/-- There is no real constant-sum identity anywhere in this normalized chart,
including the unequal-leading case. This is not an unrestricted count bound. -/
theorem no_constant_sum (a b c d e f q r v w N : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    ¬ ∀ t : ℝ, ∑ i, coordinates a b c d e f q r v w t i ^ 5 = N := by
  intro he
  have hp : C (2*q)*core a b c d e f (q^2) ((q/r^5)^2) +
      (C v*X+C w)^5 = C N := by
    apply Polynomial.funext
    intro t
    have h := he t
    rw [coordinates_sum a b c d e f q r v w t hr] at h
    simpa only [eval_add,eval_mul,eval_C,eval_pow,eval_X] using h
  exact no_constant_low_degree_tail a b c d e f (q^2) ((q/r^5)^2) (2*q) N
    (add_nonneg (sq_nonneg q) (sq_nonneg (q/r^5)))
    (mul_ne_zero (by norm_num) hq) ((C v*X+C w)^5) (by compute_degree!) hp

/-- The same chart before normalizing the separation of the two zero
midpoints. -/
def generalCoordinates (a b c d e f q r v w H t : ℝ) : Fin 5 → ℝ :=
  let A := t^3+a*t^2+b*t+c
  let D := r*(t^3+d*t^2+e*t+f)
  ![A+q*t,-A+q*t,D+q/r^4*(H-t),-D+q/r^4*(H-t),v*t+w]

private lemma normalize_coordinates (a b c d e f q r v w H t : ℝ)
    (hH : H ≠ 0) (i : Fin 5) :
    generalCoordinates a b c d e f q r v w H (H*t) i =
      H^3*coordinates (a/H) (b/H^2) (c/H^3) (d/H) (e/H^2) (f/H^3)
        (q/H^2) r (v/H^2) (w/H^3) t i := by
  fin_cases i <;> simp [generalCoordinates,coordinates]
  all_goals field_simp

/-- The arbitrary-separation chart has no constant sum when both midpoint
slopes, the leading ratio, and the separation are nonzero. -/
theorem no_constant_sum_general (a b c d e f q r v w H N : ℝ)
    (hq : q ≠ 0) (hr : r ≠ 0) (hH : H ≠ 0) :
    ¬ ∀ t : ℝ, ∑ i, generalCoordinates a b c d e f q r v w H t i ^ 5 = N := by
  intro he
  apply no_constant_sum (a/H) (b/H^2) (c/H^3) (d/H) (e/H^2) (f/H^3)
    (q/H^2) r (v/H^2) (w/H^3) (N/H^15) (div_ne_zero hq (pow_ne_zero _ hH)) hr
  intro t
  have h := he (H*t)
  simp only [normalize_coordinates a b c d e f q r v w H t hH,mul_pow,
    ← Finset.mul_sum,← pow_mul] at h
  exact (eq_div_iff (pow_ne_zero _ hH)).mpr (by nlinarith only [h])

/-- Even the degenerate cases of the arbitrary-separation chart cannot give
a constant identity passing through an all-positive point. -/
theorem no_positive_constant_sum (a b c d e f q r v w H N t : ℝ)
    (he : ∀ s : ℝ, ∑ i, generalCoordinates a b c d e f q r v w H s i ^ 5 = N) :
    ¬ ∀ i, 0 < generalCoordinates a b c d e f q r v w H t i := by
  intro hp
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  simp [generalCoordinates] at h0 h1 h2 h3
  have hqt : 0 < q*t := by linarith only [h0,h1]
  have hqt' : 0 < q/r^4*(H-t) := by linarith only [h2,h3]
  have hq : q ≠ 0 := by intro hq; rw [hq,zero_mul] at hqt; exact lt_irrefl _ hqt
  have hr : r ≠ 0 := by intro hr; simp [hr] at hqt'
  have hH : H ≠ 0 := by
    intro hH
    have heq : (q/r^4*(H-t))*r^4=-(q*t) := by rw [hH]; field_simp; ring
    have hnonneg : 0 ≤ r^4 := by positivity
    have hh := mul_nonneg hqt'.le hnonneg
    rw [heq] at hh
    linarith only [hh,hqt]
  exact no_constant_sum_general a b c d e f q r v w H N hq hr hH he

end
end Erdos322Research.QuinticLinearLast
