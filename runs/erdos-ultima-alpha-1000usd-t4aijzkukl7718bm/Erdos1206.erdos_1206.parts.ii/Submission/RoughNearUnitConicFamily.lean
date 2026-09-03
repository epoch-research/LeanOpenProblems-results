import Submission.NearUnitConicFamily

/-! A two-constant extension of the near-unit conic family, with a free
congruence parameter. This is an auxiliary arithmetic construction. -/
namespace Erdos1206.RoughNearUnitConicFamily

section Formulas
variable {R : Type*} [CommRing R]
def norm (m L : R) : R := 3*m^2-9*m*L+7*L^2
def den (s t : R) : R := s^2+3*t^2
def U (m L s t : R) : R := (m-2*L)*s^2-(6*m-8*L)*s*t-3*(m-2*L)*t^2
def V (m L s t : R) : R := (m-L)*s^2+(6*m-10*L)*s*t-3*(m-L)*t^2
def A (m L s t : R) : R := norm m L^2*den s t+9*m^3*U m L s t
def B (m L s t : R) : R := norm m L^2*den s t+9*m^3*V m L s t
def C (m L s t : R) : R := 9*m^4*den s t+3*m*norm m L*U m L s t
def D (m L s t : R) : R := 9*m^4*den s t+3*m*norm m L*V m L s t

lemma identity (m L s t : R) : A m L s t^3+D m L s t^3=B m L s t^3+C m L s t^3 := by
  dsimp [A,B,C,D,U,V,norm,den]
  ring
lemma gaps (m L s t : R) :
    B m L s t-A m L s t=9*m^3*(V m L s t-U m L s t) ∧
    D m L s t-C m L s t=3*m*norm m L*(V m L s t-U m L s t) := by
  dsimp [A,B,C,D]
  constructor <;> ring
end Formulas

lemma scaled {R : Type*} [Field R] (m L s t : R) (hL : L ≠ 0) :
    A m L s t=L^4*NearUnitConicFamily.A (m/L) s t ∧
    B m L s t=L^4*NearUnitConicFamily.B (m/L) s t ∧
    C m L s t=L^4*NearUnitConicFamily.C (m/L) s t ∧
    D m L s t=L^4*NearUnitConicFamily.D (m/L) s t := by
  dsimp [A,B,C,D,U,V,norm,den,NearUnitConicFamily.A,NearUnitConicFamily.B,
    NearUnitConicFamily.C,NearUnitConicFamily.D,NearUnitConicFamily.U,
    NearUnitConicFamily.V,NearUnitConicFamily.norm,NearUnitConicFamily.den]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor <;> field_simp

lemma ordered_real {m L u t : ℝ} (hL : 1 ≤ L) (hm : 12*L ≤ m)
    (hu : 0≤u) (ht : 0<t) :
    0<A m L (u+12*m*t) t ∧ A m L (u+12*m*t) t<B m L (u+12*m*t) t ∧
    B m L (u+12*m*t) t<C m L (u+12*m*t) t ∧ C m L (u+12*m*t) t<D m L (u+12*m*t) t := by
  have hL0 : 0<L := by linarith
  have hm0 : 0 < m := by linarith
  have hmd : 12 ≤ m/L := (le_div_iff₀ hL0).mpr hm
  have hdiv : m/L ≤ m := (div_le_iff₀ hL0).mpr (by nlinarith)
  have hs : 12*(m/L)*t ≤ u+12*m*t := by
    have hh := mul_le_mul_of_nonneg_right hdiv ht.le
    linarith
  have h := NearUnitConicFamily.ordered_real hmd ht hs
  obtain ⟨hA,hB,hC,hD⟩ := scaled m L (u+12*m*t) t hL0.ne'
  rw [hA,hB,hC,hD]
  have hp : 0<L^4 := pow_pos hL0 4
  exact ⟨mul_pos hp h.1,mul_lt_mul_of_pos_left h.2.1 hp,
    mul_lt_mul_of_pos_left h.2.2.1 hp,mul_lt_mul_of_pos_left h.2.2.2 hp⟩

lemma ordered_int {m L u t : ℤ} (hL : 1 ≤ L) (hm : 12*L ≤ m)
    (hu : 0≤u) (ht : 0<t) :
    0<A m L (u+12*m*t) t ∧ A m L (u+12*m*t) t<B m L (u+12*m*t) t ∧
    B m L (u+12*m*t) t<C m L (u+12*m*t) t ∧ C m L (u+12*m*t) t<D m L (u+12*m*t) t := by
  have h := ordered_real (m := (m:ℝ)) (L := (L:ℝ)) (u := (u:ℝ)) (t := (t:ℝ))
    (by exact_mod_cast hL) (by exact_mod_cast hm) (by exact_mod_cast hu) (by exact_mod_cast ht)
  simp only [A,B,C,D,U,V,norm,den] at h ⊢
  exact_mod_cast h

lemma projective_parameter {m L s t s' t' r r' : ℚ} (hL : 0<L) (hm : 12*L ≤ m)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hA : r*A m L s t=r'*A m L s' t') (hB : r*B m L s t=r'*B m L s' t')
    (hC : r*C m L s t=r'*C m L s' t') : s*t'=s'*t := by
  obtain ⟨ha,hb,hc,hd⟩ := scaled m L s t hL.ne'
  obtain ⟨ha',hb',hc',hd'⟩ := scaled m L s' t' hL.ne'
  rw [ha,ha'] at hA
  rw [hb,hb'] at hB
  rw [hc,hc'] at hC
  apply NearUnitConicFamily.projective_parameter (r' := r') ((le_div_iff₀ hL).mpr hm) hr ht
  · apply mul_left_cancel₀ (pow_ne_zero 4 hL.ne'); linear_combination hA
  · apply mul_left_cancel₀ (pow_ne_zero 4 hL.ne'); linear_combination hB
  · apply mul_left_cancel₀ (pow_ne_zero 4 hL.ne'); linear_combination hC

lemma outside_compact_gap (H L u t : ℕ) (hL : 0<L) (ht : 0<t) :
    let m : ℤ := 12*L*(H+1)+1
    let s : ℤ := u+12*m*t
    (H:ℤ)*(B m L s t-A m L s t) < (H+1)*(D m L s t-C m L s t) := by
  dsimp only
  let m : ℤ := 12*L*(H+1)+1
  let s : ℤ := u+12*m*t
  have hL0 : (0:ℤ)<L := by exact_mod_cast hL
  have hH0 : (0:ℤ)≤H := Nat.cast_nonneg H
  have hm : 12*(L:ℤ) ≤ m := by dsimp [m]; nlinarith
  have hm0 : 0 < m := by linarith
  have hord := ordered_int (m := m) (L := (L:ℤ)) (u := (u:ℤ)) (t := (t:ℤ))
    (by omega) hm (by positivity) (by exact_mod_cast ht)
  have hg : 0 < V m L s t-U m L s t := by
    have hh := sub_pos.mpr hord.2.1
    rw [(gaps m L s t).1] at hh
    exact pos_of_mul_pos_right hh (by positivity)
  change (H:ℤ)*(B m L s t-A m L s t) < (H+1)*(D m L s t-C m L s t)
  rw [(gaps m L s t).1,(gaps m L s t).2]
  have hcoef : (H:ℤ)*3*m^2 < (H+1)*norm m L := by
    apply sub_pos.mp
    dsimp [m,norm]
    ring_nf
    positivity
  have hh := mul_lt_mul_of_pos_right hcoef (mul_pos (show (0:ℤ)<3*m by positivity) hg)
  nlinarith only [hh]

/-- Choosing the constants and parameters near `(1,0,1,0)` modulo `18*Q`
makes all four raw coordinates equal to 18 modulo `18*Q`. -/
lemma eighteen_congruences (Q α β γ : ℕ) :
    let L : ℤ := 18*Q
    (L ∣ A (1+L*α) L (1+L*β) (L*γ)-18) ∧
    (L ∣ B (1+L*α) L (1+L*β) (L*γ)-18) ∧
    (L ∣ C (1+L*α) L (1+L*β) (L*γ)-18) ∧
    (L ∣ D (1+L*α) L (1+L*β) (L*γ)-18) := by
  dsimp only
  have hL : (18:ZMod (18*Q))*(Q:ZMod (18*Q))=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (ZMod.natCast_self (18*Q))
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (18*Q)).mp
    dsimp [A,B,C,D,U,V,norm,den]
    push_cast
    norm_num [hL]

#print axioms ordered_int
#print axioms projective_parameter
#print axioms outside_compact_gap
#print axioms eighteen_congruences
end Erdos1206.RoughNearUnitConicFamily
