import FormalConjecturesUtil

/-!
Quadratic four-cube families with adjacent-gap ratio arbitrarily close to one.
The parameter `k` selects the family; `u,v` are its homogeneous parameters.
This is an auxiliary family construction, not a density result.
-/
namespace Erdos1206.NearUnitConicFamily

section Formulas
variable {R : Type*} [CommRing R]

def norm (m : R) : R := 3*m^2-9*m+7
def den (s t : R) : R := s^2+3*t^2
def U (m s t : R) : R := (m-2)*s^2-(6*m-8)*s*t-3*(m-2)*t^2
def V (m s t : R) : R := (m-1)*s^2+(6*m-10)*s*t-3*(m-1)*t^2

def A (m s t : R) : R := norm m^2*den s t+9*m^3*U m s t
def B (m s t : R) : R := norm m^2*den s t+9*m^3*V m s t
def C (m s t : R) : R := 9*m^4*den s t+3*m*norm m*U m s t
def D (m s t : R) : R := 9*m^4*den s t+3*m*norm m*V m s t

lemma rotation_norm (m s t : R) :
    U m s t^2+U m s t*V m s t+V m s t^2=norm m*(den s t)^2 := by
  dsimp [U,V,norm,den]
  ring

lemma identity (m s t : R) : A m s t^3+D m s t^3=B m s t^3+C m s t^3 := by
  dsimp [A,B,C,D,U,V,norm,den]
  ring

lemma gaps (m s t : R) :
    B m s t-A m s t=9*m^3*(V m s t-U m s t) ∧
    D m s t-C m s t=3*m*norm m*(V m s t-U m s t) := by
  dsimp [A,B,C,D]
  constructor <;> ring

lemma gap_relation (m s t : R) :
    norm m*(B m s t-A m s t)=3*m^2*(D m s t-C m s t) := by
  rw [(gaps m s t).1,(gaps m s t).2]
  ring

lemma homogeneous (m s t r : R) :
    A m (r*s) (r*t)=r^2*A m s t ∧ B m (r*s) (r*t)=r^2*B m s t ∧
    C m (r*s) (r*t)=r^2*C m s t ∧ D m (r*s) (r*t)=r^2*D m s t := by
  dsimp [A,B,C,D,U,V,den]
  constructor; ring
  constructor; ring
  constructor <;> ring
end Formulas

private lemma shifted_order (k u v : ℝ) (hk : 0 ≤ k) (hu : 0 ≤ u) (hv : 0 < v) :
    0 < A (k+12) (u+12*(k+12)*v) v ∧
    A (k+12) (u+12*(k+12)*v) v < B (k+12) (u+12*(k+12)*v) v ∧
    B (k+12) (u+12*(k+12)*v) v < C (k+12) (u+12*(k+12)*v) v ∧
    C (k+12) (u+12*(k+12)*v) v < D (k+12) (u+12*(k+12)*v) v := by
  have hA : 0 < A (k+12) (u+12*(k+12)*v) v := by
    dsimp [A,U,norm,den]
    ring_nf
    positivity
  have hAB : 0 < B (k+12) (u+12*(k+12)*v) v-A (k+12) (u+12*(k+12)*v) v := by
    dsimp [A,B,U,V,norm,den]
    ring_nf
    positivity
  have hBC : 0 < C (k+12) (u+12*(k+12)*v) v-B (k+12) (u+12*(k+12)*v) v := by
    dsimp [B,C,U,V,norm,den]
    ring_nf
    positivity
  have hCD : 0 < D (k+12) (u+12*(k+12)*v) v-C (k+12) (u+12*(k+12)*v) v := by
    dsimp [C,D,U,V,norm,den]
    ring_nf
    positivity
  exact ⟨hA,sub_pos.mp hAB,sub_pos.mp hBC,sub_pos.mp hCD⟩

/-- Real-valued version with a lower bound on the parameter ratio. -/
lemma ordered_real {m s t : ℝ} (hm : 12 ≤ m) (ht : 0<t) (hs : 12*m*t ≤ s) :
    0<A m s t ∧ A m s t<B m s t ∧ B m s t<C m s t ∧ C m s t<D m s t := by
  have h := shifted_order (m-12) (s-12*m*t) t (by linarith) (by linarith) ht
  simpa only [sub_add_cancel] using h

/-- Positive order is uniform over this full positive quadrant of homogeneous
parameters. -/
theorem ordered (k u v : ℕ) (hv : 0 < v) :
    0 < A ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v ∧
    A ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v <
      B ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v ∧
    B ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v <
      C ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v ∧
    C ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v <
      D ((k:ℤ)+12) ((u:ℤ)+12*((k:ℤ)+12)*v) v := by
  have hh := shifted_order (k:ℝ) (u:ℝ) (v:ℝ) (by positivity) (by positivity)
    (by exact_mod_cast hv)
  simp only [A,B,C,D,U,V,norm,den] at hh ⊢
  exact_mod_cast hh

lemma norm_pos {m : ℚ} (hm : 12 ≤ m) : 0 < norm m := by
  dsimp [norm]
  nlinarith

lemma norm_lt {m : ℚ} (hm : 12 ≤ m) : norm m < 3*m^2 := by
  dsimp [norm]
  linarith

/-- A projective image under the first three coordinate forms determines the
parameter ratio. The fourth coordinate is not needed. -/
theorem projective_parameter {m s t s' t' r r' : ℚ} (hm : 12 ≤ m)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hA : r*A m s t=r'*A m s' t') (hB : r*B m s t=r'*B m s' t')
    (hC : r*C m s t=r'*C m s' t') : s*t'=s'*t := by
  have hm0 : m ≠ 0 := by linarith
  have hn0 := (norm_pos hm).ne'
  have hcoef : norm m^3 ≠ 27*m^6 := by
    have hh := (by decide : Odd (3:ℕ)).strictMono_pow (norm_lt hm)
    have heq : (3*m^2)^3=27*m^6 := by ring
    dsimp only at hh
    rw [heq] at hh
    exact hh.ne
  have hden : r*den s t=r'*den s' t' := by
    have he : (norm m^3-27*m^6)*(r*den s t-r'*den s' t')=0 := by
      dsimp [A,C] at hA hC
      linear_combination norm m*hA-3*m^2*hC
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hcoef))
  have hU : r*U m s t=r'*U m s' t' := by
    have he : (9*m^3)*(r*U m s t-r'*U m s' t')=0 := by
      dsimp [A] at hA
      linear_combination hA-norm m^2*hden
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by positivity))
  have hV : r*V m s t=r'*V m s' t' := by
    have he : (9*m^3)*(r*V m s t-r'*V m s' t')=0 := by
      dsimp [B] at hB
      linear_combination hB-norm m^2*hden
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by positivity))
  have hst : r*s*t=r'*s'*t' := by
    have he : (24*norm m)*(r*s*t-r'*s'*t')=0 := by
      dsimp [U,V] at hU hV
      dsimp [norm]
      linear_combination (6-6*m)*hU+(6*m-12)*hV
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hn0))
  have ht2 : r*t^2=r'*t'^2 := by
    have he : (24*norm m)*(r*t^2-r'*t'^2)=0 := by
      dsimp [U,V] at hU hV
      dsimp [den] at hden
      dsimp [norm]
      linear_combination (12*m^2-36*m+28)*hden+(10-6*m)*hU+(8-6*m)*hV
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hn0))
  have he : (r*t)*(s*t'-s'*t)=0 := by linear_combination t'*hst-s'*ht2
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero hr ht))

/-- Every family indexed by `12*H` lies entirely below the compact gap cutoff
`1+1/H`, uniformly over its positive homogeneous parameters. -/
theorem outside_compact_gap (H u v : ℕ) (hv : 0 < v) :
    let m : ℤ := 12*H+12
    let s : ℤ := u+12*m*v
    (H:ℤ)*(B m s v-A m s v) < (H+1)*(D m s v-C m s v) := by
  dsimp only
  let m : ℤ := 12*H+12
  let s : ℤ := u+12*m*v
  have hm : 0 < m := by dsimp [m]; omega
  have hord := ordered (12*H) u v hv
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hord
  change 0 < A m s v ∧ A m s v < B m s v ∧ B m s v < C m s v ∧ C m s v < D m s v at hord
  have hg : 0 < V m s v-U m s v := by
    have hh := sub_pos.mpr hord.2.1
    rw [(gaps m s v).1] at hh
    exact pos_of_mul_pos_right hh (by positivity)
  change (H:ℤ)*(B m s v-A m s v) < (H+1)*(D m s v-C m s v)
  rw [(gaps m s v).1,(gaps m s v).2]
  have hcoef : (H:ℤ)*3*m^2 < (H+1)*norm m := by
    dsimp [m,norm]
    nlinarith
  have hh := mul_lt_mul_of_pos_right hcoef (mul_pos (show (0:ℤ)<3*m by positivity) hg)
  nlinarith only [hh]

#print axioms ordered
#print axioms projective_parameter
#print axioms outside_compact_gap
end Erdos1206.NearUnitConicFamily
