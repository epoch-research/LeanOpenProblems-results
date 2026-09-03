import FormalConjecturesUtil

/-!
An obstruction for the equal-leading-coefficient branch of a reflection-symmetric
quartic-polynomial ansatz for five fifth powers. This does not bound arbitrary
representations and does not settle Erdős Problem 322.
-/

namespace Erdos322Research.QuinticQuartic

noncomputable section

private def qa (T : ℝ) : ℝ := 75*T^2-100*T+10300
private def qb (T : ℝ) : ℝ := 1680*T^3+9300*T^2+260880*T+949600
private def qc (T : ℝ) : ℝ :=
  21168*T^4+154224*T^3+2165664*T^2+11677824*T+21852608
private def discriminant (T : ℝ) : ℝ :=
  8820*T^6+16380*T^5+1242711*T^4+2370216*T^3+
    13472688*T^2-57694976*T-3531776

def obstruction (T K : ℝ) : ℝ := qa T * K^2 + qb T * K + qc T

private theorem qa_pos (T : ℝ) : 0 < qa T := by
  have he : 3 * qa T = 25 * (3*T-2)^2 + 30800 := by unfold qa; ring
  nlinarith [sq_nonneg (3*T-2)]

private theorem qb_pos {T : ℝ} (hT : -1 ≤ T) : 0 < qb T := by
  have hs : 0 ≤ T+1 := by linarith
  have he : qb T = 1680*(T+1)^3+4260*(T+1)^2+247320*(T+1)+696340 := by
    unfold qb; ring
  rw [he]
  positivity

private theorem qc_pos {T : ℝ} (hT : -1 ≤ T) : 0 < qc T := by
  have hs : 0 ≤ T+1 := by linarith
  have he : qc T = 21168*(T+1)^4+69552*(T+1)^3+
      1830000*(T+1)^2+7724496*(T+1)+12207392 := by
    unfold qc; ring
  rw [he]
  positivity

private theorem discriminant_pos {T : ℝ} (hT : T ≤ -1) : 0 < discriminant T := by
  have hs : 0 ≤ -T-1 := by linarith
  have he : discriminant T = 8820*(-T-1)^6+36540*(-T-1)^5+
      1293111*(-T-1)^4+2613228*(-T-1)^3+13786806*(-T-1)^2+
      82471568*(-T-1)+66500823 := by
    unfold discriminant; ring
  rw [he]
  positivity

theorem obstruction_pos (T K : ℝ) (hK : 0 ≤ K) : 0 < obstruction T K := by
  have ha := qa_pos T
  by_cases hT : -1 ≤ T
  · have hb := qb_pos hT
    have hc := qc_pos hT
    unfold obstruction
    positivity
  · have hp := discriminant_pos (le_of_lt (lt_of_not_ge hT))
    have he : 4 * qa T * obstruction T K =
        (2 * qa T * K + qb T)^2 + 400 * discriminant T := by
      unfold obstruction qa qb qc discriminant
      ring
    have hpos : 0 < 4 * qa T * obstruction T K := by
      rw [he]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4 * qa T)).mp hpos

def f3 (T H : ℝ) : ℝ :=
  10*H*(15*T^2*H^2+84*T^3-20*T*H^2+336*T^2-404*H^2-6384*T-13776)
def f4 (T H : ℝ) : ℝ :=
  -10*H*(15*T*H^2+168*T^2-10*H^2+612*T-1192)
def f5 (T H : ℝ) : ℝ := 10*H*(5*H^2+84*T+276)

theorem coefficient_invariant (T H : ℝ) :
    2*(f4 T H)^2-5*f3 T H*f5 T H = 100*H^2*obstruction T (H^2) := by
  unfold f3 f4 f5 obstruction qa qb qc
  ring

theorem coefficient_invariant_pos (T H : ℝ) (hH : H ≠ 0) :
    0 < 2*(f4 T H)^2-5*f3 T H*f5 T H := by
  rw [coefficient_invariant]
  have hsq : 0 < H^2 := sq_pos_of_ne_zero hH
  have hp := obstruction_pos T (H^2) (sq_nonneg H)
  positivity

theorem no_fifth_power_coefficients (T H h v : ℝ) (hH : H ≠ 0) :
    ¬ (f3 T H = 10*h*v^2 ∧ f4 T H = 5*h*v ∧ f5 T H = h) := by
  rintro ⟨h3, h4, h5⟩
  have hp := coefficient_invariant_pos T H hH
  rw [h3, h4, h5] at hp
  nlinarith

private theorem fifth_power_invariant (a0 a1 a2 a3 a4 a5 h v N : ℝ)
    (he : ∀ U : ℝ, a0+a1*U+a2*U^2+a3*U^3+a4*U^4+a5*U^5+h*(U+v)^5=N) :
    2*a4^2-5*a3*a5=0 := by
  let p : Polynomial ℝ := Polynomial.C a0 + Polynomial.C a1 * Polynomial.X +
    Polynomial.C a2 * Polynomial.X^2 + Polynomial.C a3 * Polynomial.X^3 +
    Polynomial.C a4 * Polynomial.X^4 + Polynomial.C a5 * Polynomial.X^5 +
    Polynomial.C h * (Polynomial.X + Polynomial.C v)^5
  have hp : p = Polynomial.C N := by
    apply Polynomial.funext
    intro U
    simpa [p] using he U
  have hexp : p =
      Polynomial.C (a0+h*v^5) + Polynomial.C (a1+5*h*v^4)*Polynomial.X +
      Polynomial.C (a2+10*h*v^3)*Polynomial.X^2 +
      Polynomial.C (a3+10*h*v^2)*Polynomial.X^3 +
      Polynomial.C (a4+5*h*v)*Polynomial.X^4 +
      Polynomial.C (a5+h)*Polynomial.X^5 := by
    simp only [p, map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [hexp] at hp
  have h3 := congrArg (fun q : Polynomial ℝ => q.coeff 3) hp
  have h4 := congrArg (fun q : Polynomial ℝ => q.coeff 4) hp
  have h5 := congrArg (fun q : Polynomial ℝ => q.coeff 5) hp
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X] at h3 h4 h5
  norm_num at h3 h4 h5
  have h3' : a3 = -(10*h*v^2) := by linarith
  have h4' : a4 = -(5*h*v) := by linarith
  have h5' : a5 = -h := by linarith
  rw [h3', h4', h5']
  ring

def f0 (T H : ℝ) : ℝ :=
  H/2*(5*T^2*H^4-210*T*H^4+1181*H^4-52920*T*H^2+546840*H^2+15558480)
def f1 (T H : ℝ) : ℝ :=
  -5*H*(T*H^4+462*T^2*H^2-21*H^4-2772*T*H^2-16422*H^2-222264*T-370440)
def f2 (T H : ℝ) : ℝ :=
  5/2*H*(-20*T^3*H^2+40*T^2*H^2+H^4+2540*T*H^2+21168*T^2-
    4304*H^2+63504*T-232848)

def centeredSum (T H U : ℝ) : ℝ :=
  let u := U-T+5
  let A := U-H/2
  let C := U+H/2
  let B := U^2-T*U+2*H-21
  let D := -U^2+T*U+2*H+21
  2*(B^5+D^5)+20*u*(A^2*B^3+C^2*D^3)+10*u^2*(A^4*B+C^4*D)

theorem centeredSum_expansion (T H U : ℝ) :
    centeredSum T H U = f0 T H+f1 T H*U+f2 T H*U^2+
      f3 T H*U^3+f4 T H*U^4+f5 T H*U^5 := by
  unfold centeredSum f0 f1 f2 f3 f4 f5
  ring

theorem no_centered_fifth_power_completion (T H h v N : ℝ) (hH : H ≠ 0) :
    ¬ (∀ U : ℝ, centeredSum T H U+h*(U+v)^5=N) := by
  intro he
  have hz := fifth_power_invariant (f0 T H) (f1 T H) (f2 T H)
    (f3 T H) (f4 T H) (f5 T H) h v N
    (fun U => by simpa only [centeredSum_expansion] using he U)
  exact (ne_of_gt (coefficient_invariant_pos T H hH)) hz

end

end Erdos322Research.QuinticQuartic
