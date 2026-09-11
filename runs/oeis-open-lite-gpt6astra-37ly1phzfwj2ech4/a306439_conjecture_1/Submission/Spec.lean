import FormalConjectures.Util.ProblemImports

/-
Proof outline.

We first prove a ternary representation theorem: every positive integer m
which is a nonzero quadratic nonresidue modulo 7 is represented by
(3 C² + 7 B² + 14 A²) / 8.  Auxiliary diagonal forms are constructed using
Dirichlet's theorem and quadratic reciprocity.  Integral lattice enlargement
and reduction identify a minimal-discriminant form with the required form;
all local arguments use primitive congruence solutions.

For n ≥ 4900, two suitable weighted sums s give two distinct nonnegative
pentagonal representations.  The remaining finite interval is verified by
explicit witnesses, and the counts through 41 are evaluated in a bounded
search.  All finite verifications below use kernel reduction (`decide`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000


/-! ### Ternary forms and reduction inequalities -/

namespace Aux306439

structure Form3 (R : Type*) where
  a : R
  b : R
  c : R
  d : R
  e : R
  f : R
  deriving DecidableEq

namespace Form3
variable {R : Type*} [CommRing R]
def eval (F : Form3 R) (x y z : R) : R :=
  F.a*x^2 + F.b*y^2 + F.c*z^2 + F.d*y*z + F.e*x*z + F.f*x*y

def disc (F : Form3 R) : R :=
  4*F.a*F.b*F.c + F.d*F.e*F.f - F.a*F.d^2 - F.b*F.e^2 - F.c*F.f^2

end Form3

-- The determinant inequality for reduced ternary forms, positive cross-product case.
lemma bound_pos (a b c u v w : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hu : 0 ≤ u) (hua : u ≤ a) (hv : 0 ≤ v) (hva : v ≤ a)
    (hw : 0 ≤ w) (hwb : w ≤ b) :
    a*w^2+b*v^2+c*u^2-u*v*w ≤ 2*a*b*c := by
  have hb : 0 ≤ b := le_trans ha hab
  have hc : 0 ≤ c := le_trans hb hbc
  have hvw : v*w ≤ a*b := mul_le_mul hva hwb hw ha
  have habc : a*b ≤ a*c := mul_le_mul_of_nonneg_left hbc ha
  have h₁ : c*u^2-u*v*w ≤ a*(c*a-v*w) := by
    have hsq : u^2 ≤ a*u := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq hc
    have hn := mul_le_mul_of_nonneg_right hua (show 0 ≤ c*a-v*w by nlinarith)
    nlinarith
  have h₂ : b*v^2-a*v*w ≤ a^2*(b-w) := by
    have hsq : v^2 ≤ a*v := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq hb
    have hn := mul_le_mul_of_nonneg_right hva (mul_nonneg ha (sub_nonneg.mpr hwb))
    nlinarith
  have h₃ : a*w^2+a^2*b-a^2*w ≤ a*b^2 := by
    have hsq : w^2 ≤ b*w := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq ha
    have hn := mul_le_mul_of_nonneg_right hwb (mul_nonneg ha (sub_nonneg.mpr hab))
    nlinarith
  have h₄ : a*b^2+c*a^2 ≤ 2*a*b*c := by
    have h₅ := mul_le_mul_of_nonneg_left hbc (show 0 ≤ a*b by positivity)
    have h₆ := mul_le_mul_of_nonneg_left hab (show 0 ≤ a*c by positivity)
    nlinarith
  nlinarith

lemma bound_neg_aux (a b u v w : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : 0 ≤ u) (hua : u ≤ a) (hv : 0 ≤ v) (hva : v ≤ a)
    (hw : 0 ≤ w) (hwb : w ≤ b) (hs : u+v+w ≤ a+b) :
    a*w^2+b*u^2+b*v^2+u*v*w ≤ a*b^2+b*a^2 := by
  have hb : 0 ≤ b := le_trans ha hab
  have huv : 0 ≤ u*v := mul_nonneg hu hv
  have hwb₂ : 0 ≤ 2*b-w := by omega
  have heq : b*u^2+b*v^2+u*v*w = b*(u+v)^2-(2*b-w)*(u*v) := by ring
  rw [show a*w^2+b*u^2+b*v^2+u*v*w = a*w^2 + (b*(u+v)^2-(2*b-w)*(u*v)) by ring]
  by_cases hs' : u+v ≤ a
  · have hsq : (u+v)^2 ≤ a^2 := by nlinarith
    have hwq : w^2 ≤ b^2 := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hsq hb
    have h₂ := mul_le_mul_of_nonneg_left hwq ha
    have h₃ := mul_nonneg hwb₂ huv
    nlinarith
  · have ht : a ≤ u+v := by omega
    have ht' : u+v-a ≤ a := by omega
    have hp : a*(u+v-a) ≤ u*v := by
      have := mul_nonneg (sub_nonneg.mpr hua) (sub_nonneg.mpr hva)
      nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hp hwb₂
    have h₂ : w^2+w*(u+v-a) ≤ b*(b-(u+v-a)) := by
      have h₃ := mul_le_mul_of_nonneg_left (show w+(u+v-a) ≤ b by omega) hw
      have h₄ := mul_le_mul_of_nonneg_left (show w ≤ b-(u+v-a) by omega) hb
      nlinarith
    have h₃ := mul_le_mul_of_nonneg_left h₂ ha
    have h₄ : (u+v-a)^2 ≤ a*(u+v-a) := by nlinarith
    have h₅ := mul_le_mul_of_nonneg_left h₄ hb
    nlinarith

lemma bound_neg (a b c u v w : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hu : 0 ≤ u) (hua : u ≤ a) (hv : 0 ≤ v) (hva : v ≤ a)
    (hw : 0 ≤ w) (hwb : w ≤ b) (hs : u+v+w ≤ a+b) :
    a*w^2+b*v^2+c*u^2+u*v*w ≤ 2*a*b*c := by
  have hb : 0 ≤ b := le_trans ha hab
  have h₁ := bound_neg_aux a b u v w ha hab hu hua hv hva hw hwb hs
  have h₂ : a^2*b ≤ a*b^2 := by
    have := mul_le_mul_of_nonneg_left hab (show 0 ≤ a*b by positivity)
    nlinarith
  have huq : u^2 ≤ a*b := by
    have h₃ : u^2 ≤ a^2 := by nlinarith
    have h₄ := mul_le_mul_of_nonneg_left hab ha
    nlinarith
  have h₃ := mul_le_mul_of_nonneg_left huq (sub_nonneg.mpr hbc)
  have h₄ := mul_nonneg (show 0 ≤ a*b by positivity) (sub_nonneg.mpr hbc)
  nlinarith

-- We can arrange the xz and xy coefficients to be nonnegative by sign changes.
def Reduced (F : Form3 ℤ) : Prop :=
  0 < F.a ∧ F.a ≤ F.b ∧ F.b ≤ F.c ∧
  0 ≤ F.e ∧ F.e ≤ F.a ∧ 0 ≤ F.f ∧ F.f ≤ F.a ∧
  -F.b ≤ F.d ∧ F.d ≤ F.b ∧ F.e + F.f - F.d ≤ F.a + F.b

lemma reduced_disc_bound (F : Form3 ℤ) (h : Reduced F) :
    2*F.a*F.b*F.c ≤ F.disc := by
  rcases h with ⟨ha, hab, hbc, he, hea, hf, hfa, hdb, hbd, ht⟩
  by_cases hd : 0 ≤ F.d
  · have := bound_pos F.a F.b F.c F.f F.e F.d (le_of_lt ha)
      hab hbc hf hfa he hea hd hbd
    dsimp [Form3.disc]
    nlinarith
  · have := bound_neg F.a F.b F.c F.f F.e (-F.d) (le_of_lt ha)
      hab hbc hf hfa he hea (by omega) (by omega) (by omega)
    dsimp [Form3.disc]
    nlinarith

def Nonres7 (n : ℤ) : Prop := n % 7 = 0 ∨ n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6

lemma reduced_classification (F : Form3 ℤ) (hr : Reduced F)
    (hdisc : F.disc = 3 ∨ F.disc = 147)
    (hmod : ∀ x y z : ℤ, Nonres7 (F.eval x y z)) :
    F = ⟨3,3,5,-2,2,1⟩ := by
  have hbound := reduced_disc_bound F hr
  rcases F with ⟨a,b,c,d,e,f⟩
  rcases hr with ⟨ha, hab, hbc, he, hea, hf, hfa, hdb, hbd, ht⟩
  simp only [Form3.a, Form3.b, Form3.c, Form3.d, Form3.e, Form3.f] at *
  have ha7 := hmod 1 0 0
  have hb7 := hmod 0 1 0
  have hc7 := hmod 0 0 1
  norm_num [Form3.eval] at ha7 hb7 hc7
  have hle : 2*a*b*c ≤ 147 := by omega
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hab' : a^2 ≤ a*b := by nlinarith
  have hbc' : a*b ≤ b*c := by nlinarith
  have ha4 : a ≤ 4 := by
    by_contra h
    have h₁ : 5 ≤ a := by omega
    have h₂ : 5 ≤ b := le_trans h₁ hab
    have h₃ : 5 ≤ c := le_trans h₂ hbc
    have h₄ : 25 ≤ a*b := by nlinarith
    nlinarith
  have ha3 : a = 3 := by
    interval_cases a <;> norm_num [Nonres7] at *
  subst a
  have hb4 : b ≤ 4 := by
    by_contra h
    have h₁ : 5 ≤ b := by omega
    have h₂ : 5 ≤ c := le_trans h₁ hbc
    nlinarith
  have hb3 : b = 3 := by
    interval_cases b <;> norm_num [Nonres7] at *
  subst b
  have hc8 : c ≤ 8 := by nlinarith
  have hf1 : f = 1 := by
    have h₁ := hmod 1 1 0
    have h₂ := hmod 1 2 0
    norm_num [Form3.eval] at h₁ h₂
    interval_cases f <;> norm_num [Nonres7] at *
  subst f
  have hd147 : Form3.disc (⟨3,3,c,d,e,1⟩ : Form3 ℤ) = 147 := by
    rcases hdisc with h | h
    · rw [h] at hbound
      nlinarith
    · exact h
  dsimp [Form3.disc] at hd147
  interval_cases c <;> interval_cases e <;> interval_cases d <;>
    norm_num at *

lemma normalized_to_diagonal (x y z : ℤ) :
    3*(-x+y+2*z)^2 + 7*(-x+y-2*z)^2 + 14*(-x-y)^2 =
      8*(Form3.eval (⟨3,3,5,-2,2,1⟩ : Form3 ℤ) x y z) := by
  simp only [Form3.eval]
  ring

end Aux306439

/-! ### Changes of basis -/

set_option maxHeartbeats 0

namespace Aux306439
namespace Form3
variable {R S : Type*} [CommRing R] [CommRing S]

def map (F : Form3 R) (g : R →+* S) : Form3 S :=
  ⟨g F.a, g F.b, g F.c, g F.d, g F.e, g F.f⟩

@[simp] lemma eval_map (F : Form3 R) (g : R →+* S) (x y z : R) :
    (F.map g).eval (g x) (g y) (g z) = g (F.eval x y z) := by
  simp [map, eval]

@[simp] lemma disc_map (F : Form3 R) (g : R →+* S) :
    (F.map g).disc = g F.disc := by
  simp [map, disc, map_ofNat]

def evalV (F : Form3 R) (v : Fin 3 → R) : R := F.eval (v 0) (v 1) (v 2)

def hessian (F : Form3 R) : Matrix (Fin 3) (Fin 3) R :=
  !![2*F.a, F.f, F.e; F.f, 2*F.b, F.d; F.e, F.d, 2*F.c]

lemma det_hessian (F : Form3 R) : F.hessian.det = 2*F.disc := by
  simp [hessian, Matrix.det_fin_three, disc]
  ring

lemma two_evalV (F : Form3 R) (v : Fin 3 → R) :
    2*F.evalV v = dotProduct v (F.hessian.mulVec v) := by
  simp [evalV, eval, hessian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

-- Changes of basis, using integer-valued coefficients rather than Gram half-coefficients.
def transform (F : Form3 R) (T : Matrix (Fin 3) (Fin 3) R) : Form3 R :=
  let a := F.evalV (T.transpose 0)
  let b := F.evalV (T.transpose 1)
  let c := F.evalV (T.transpose 2)
  ⟨a, b, c,
    F.evalV (T.transpose 1 + T.transpose 2)-b-c,
    F.evalV (T.transpose 0 + T.transpose 2)-a-c,
    F.evalV (T.transpose 0 + T.transpose 1)-a-b⟩

lemma evalV_transform (F : Form3 R) (T : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    (F.transform T).evalV v = F.evalV (T.mulVec v) := by
  simp [transform, evalV, eval, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

lemma hessian_transform (F : Form3 R) (T : Matrix (Fin 3) (Fin 3) R) :
    (F.transform T).hessian = T.transpose * F.hessian * T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transform, hessian, evalV, eval, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

lemma disc_transform (F : Form3 R) (T : Matrix (Fin 3) (Fin 3) R) :
    (F.transform T).disc = F.disc * T.det^2 := by
  simp [transform, evalV, eval, disc, Matrix.transpose_apply, Matrix.det_fin_three]
  ring

@[simp] lemma transform_one (F : Form3 R) : F.transform 1 = F := by
  cases F
  simp [transform, evalV, eval, Matrix.transpose_apply, Matrix.one_apply]
  refine ⟨?_, ?_, ?_⟩ <;> ring

lemma ext_evalV (F G : Form3 R) (h : ∀ v, F.evalV v = G.evalV v) : F = G := by
  have ha := h ![1,0,0]
  have hb := h ![0,1,0]
  have hc := h ![0,0,1]
  have hd := h ![0,1,1]
  have he := h ![1,0,1]
  have hf := h ![1,1,0]
  simp [evalV, eval] at ha hb hc hd he hf
  cases F; cases G
  simp_all

lemma transform_mul (F : Form3 R) (T U : Matrix (Fin 3) (Fin 3) R) :
    (F.transform T).transform U = F.transform (T*U) := by
  apply ext_evalV
  intro v
  simp only [evalV_transform, Matrix.mulVec_mulVec]

lemma transform_map (F : Form3 R) (T : Matrix (Fin 3) (Fin 3) R) (g : R →+* S) :
    (F.transform T).map g = (F.map g).transform (T.map g) := by
  cases F
  simp [map, transform, evalV, eval, Matrix.map_apply, Matrix.transpose_apply]

end Form3
end Aux306439

/-! ### Minimal admissible integral forms -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

def rat (F : Form3 ℤ) : Form3 ℚ := F.map (Int.castRingHom ℚ)

def Pos (F : Form3 ℚ) : Prop := ∀ v : Fin 3 → ℚ, v ≠ 0 → 0 < F.evalV v

def Rep (F : Form3 ℤ) (m : ℤ) : Prop := ∃ v : Fin 3 → ℤ, F.evalV v = m

def Admissible (G : Form3 ℚ) (m : ℤ) (F : Form3 ℤ) : Prop :=
  (∃ T : Matrix (Fin 3) (Fin 3) ℚ, T.det ≠ 0 ∧ F.rat = G.transform T) ∧ F.Rep m

lemma pos_transform {G : Form3 ℚ} (hG : G.Pos)
    {T : Matrix (Fin 3) (Fin 3) ℚ} (hT : T.det ≠ 0) : (G.transform T).Pos := by
  intro v hv
  rw [evalV_transform]
  apply hG
  intro h
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero hT h)

lemma admissible_pos {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hG : G.Pos) (hF : Admissible G m F) : F.rat.Pos := by
  obtain ⟨⟨T,hT,hFT⟩,hrep⟩ := hF
  rw [hFT]
  exact pos_transform hG hT

lemma admissible_disc_pos {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hG : 0 < G.disc) (hF : Admissible G m F) : 0 < F.disc := by
  obtain ⟨⟨T,hT,hF⟩,hrep⟩ := hF
  have h := congrArg disc hF
  rw [disc_transform] at h
  have hpos : 0 < G.disc*T.det^2 := mul_pos hG (sq_pos_of_ne_zero hT)
  rw [← h] at hpos
  simpa [rat] using hpos

lemma pos_diagonals {F : Form3 ℤ} (hF : F.rat.Pos) :
    0 < F.a ∧ 0 < F.b ∧ 0 < F.c := by
  have ha := hF ![1,0,0] (by decide)
  have hb := hF ![0,1,0] (by decide)
  have hc := hF ![0,0,1] (by decide)
  simp [rat, map, evalV, eval] at ha hb hc
  exact ⟨ha,hb,hc⟩

lemma rat_transform (F : Form3 ℤ) (T : Matrix (Fin 3) (Fin 3) ℤ) :
    (F.transform T).rat = F.rat.transform (T.map (Int.castRingHom ℚ)) :=
  transform_map F T _

lemma admissible_transform {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hF : Admissible G m F) (U V : Matrix (Fin 3) (Fin 3) ℤ) (hUV : U*V=1) :
    Admissible G m (F.transform U) := by
  obtain ⟨⟨T,hT,hFT⟩,v,hv⟩ := hF
  have hU : U.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hUV
  constructor
  · refine ⟨T * U.map (Int.castRingHom ℚ), ?_, ?_⟩
    · rw [Matrix.det_mul]
      apply mul_ne_zero hT
      simpa only [Matrix.det_fin_three, Matrix.map_apply, Int.cast_add, Int.cast_sub, Int.cast_mul]
        using (show (U.det : ℚ) ≠ 0 by exact_mod_cast hU)
    · rw [rat_transform, hFT, transform_mul]
  · refine ⟨V.mulVec v, ?_⟩
    rw [evalV_transform, Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
    exact hv

lemma disc_transform_unit (F : Form3 ℤ) (U V : Matrix (Fin 3) (Fin 3) ℤ)
    (hUV : U*V=1) : (F.transform U).disc = F.disc := by
  rw [disc_transform]
  have hu := Matrix.isUnit_det_of_right_inverse hUV
  rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]

end Form3

lemma minimize_nonneg {α : Type*} (P : α → Prop) (c : α → ℤ)
    (hne : ∃ x, P x) (hc : ∀ x, P x → 0 ≤ c x) :
    ∃ x, P x ∧ ∀ y, P y → c x ≤ c y := by
  classical
  let x := Function.argminOn (fun x => (c x).toNat) {x | P x} hne
  have hx : P x := Function.argminOn_mem _ _ _
  refine ⟨x,hx,?_⟩
  intro y hy
  have h := Function.not_lt_argminOn (fun x => (c x).toNat) {x | P x} hy hne
  have hxy : (c x).toNat ≤ (c y).toNat := by exact le_of_not_gt h
  have hx0 := hc x hx
  have hy0 := hc y hy
  omega

-- Successive integer minima are an elementary substitute for reduction theory.
def Optimal (G : Form3 ℚ) (m : ℤ) (F : Form3 ℤ) : Prop :=
  Form3.Admissible G m F ∧
  (∀ E, Form3.Admissible G m E → F.disc ≤ E.disc) ∧
  (∀ E, Form3.Admissible G m E → E.disc = F.disc → F.a ≤ E.a) ∧
  (∀ E, Form3.Admissible G m E → E.disc = F.disc → E.a = F.a → F.b ≤ E.b) ∧
  (∀ E, Form3.Admissible G m E → E.disc = F.disc → E.a = F.a → E.b = F.b → F.c ≤ E.c)

lemma optimal_exists {G : Form3 ℚ} {m : ℤ} (hG : G.Pos) (hD : 0 < G.disc)
    (hne : ∃ F, Form3.Admissible G m F) : ∃ F, Optimal G m F := by
  obtain ⟨F₀,hF₀,hmin₀⟩ := minimize_nonneg (Form3.Admissible G m) Form3.disc hne
    (fun F hF => le_of_lt (Form3.admissible_disc_pos hD hF))
  obtain ⟨F₁,⟨hF₁,hD₁⟩,hmin₁⟩ := minimize_nonneg
    (fun F => Form3.Admissible G m F ∧ F.disc = F₀.disc) Form3.a
    ⟨F₀,hF₀,rfl⟩ (fun F hF => le_of_lt (Form3.pos_diagonals
      (Form3.admissible_pos hG hF.1)).1)
  obtain ⟨F₂,⟨hF₂,hD₂,ha₂⟩,hmin₂⟩ := minimize_nonneg
    (fun F => Form3.Admissible G m F ∧ F.disc = F₀.disc ∧ F.a = F₁.a) Form3.b
    ⟨F₁,hF₁,hD₁,rfl⟩ (fun F hF => le_of_lt (Form3.pos_diagonals
      (Form3.admissible_pos hG hF.1)).2.1)
  obtain ⟨F₃,⟨hF₃,hD₃,ha₃,hb₃⟩,hmin₃⟩ := minimize_nonneg
    (fun F => Form3.Admissible G m F ∧ F.disc = F₀.disc ∧ F.a = F₁.a ∧ F.b = F₂.b)
    Form3.c ⟨F₂,hF₂,hD₂,ha₂,rfl⟩ (fun F hF => le_of_lt (Form3.pos_diagonals
      (Form3.admissible_pos hG hF.1)).2.2)
  refine ⟨F₃,hF₃,?_,?_,?_,?_⟩
  · intro E hE
    rw [hD₃]
    exact hmin₀ E hE
  · intro E hE hDE
    rw [ha₃]
    exact hmin₁ E ⟨hE,hDE.trans hD₃⟩
  · intro E hE hDE haE
    rw [hb₃]
    exact hmin₂ E ⟨hE,hDE.trans hD₃,haE.trans ha₃⟩
  · intro E hE hDE haE hbE
    exact hmin₃ E ⟨hE,hDE.trans hD₃,haE.trans ha₃,hbE.trans hb₃⟩

end Aux306439

/-! ### Reduction of minimal forms -/

set_option maxHeartbeats 0
namespace Aux306439
open Form3

lemma optimal_compare {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hF : Optimal G m F) (U V : Matrix (Fin 3) (Fin 3) ℤ) (hUV : U*V=1) :
    F.a ≤ (F.transform U).a ∧
    ((F.transform U).a = F.a → F.b ≤ (F.transform U).b) ∧
    ((F.transform U).a = F.a → (F.transform U).b = F.b → F.c ≤ (F.transform U).c) := by
  have hE := admissible_transform hF.1 U V hUV
  have hD := disc_transform_unit F U V hUV
  exact ⟨hF.2.2.1 _ hE hD, hF.2.2.2.1 _ hE hD, hF.2.2.2.2 _ hE hD⟩

lemma optimal_weak_reduced {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hG : G.Pos) (hF : Optimal G m F) :
    0 < F.a ∧ F.a ≤ F.b ∧ F.b ≤ F.c ∧
    -F.a ≤ F.e ∧ F.e ≤ F.a ∧ -F.a ≤ F.f ∧ F.f ≤ F.a ∧
    -F.b ≤ F.d ∧ F.d ≤ F.b ∧ F.e + F.f - F.d ≤ F.a + F.b := by
  have ha := (pos_diagonals (admissible_pos hG hF.1)).1
  have hab := (optimal_compare hF !![0,1,0;1,0,0;0,0,1]
    !![0,1,0;1,0,0;0,0,1] (by decide)).1
  have hbc := (optimal_compare hF !![1,0,0;0,0,1;0,1,0]
    !![1,0,0;0,0,1;0,1,0] (by decide)).2.1 (by simp [transform,evalV,eval])
  have hem := (optimal_compare hF !![1,0,1;0,1,0;0,0,1]
    !![1,0,-1;0,1,0;0,0,1] (by decide)).2.2
    (by simp [transform,evalV,eval]) (by simp [transform,evalV,eval])
  have hep := (optimal_compare hF !![1,0,-1;0,1,0;0,0,1]
    !![1,0,1;0,1,0;0,0,1] (by decide)).2.2
    (by simp [transform,evalV,eval]) (by simp [transform,evalV,eval])
  have hfm := (optimal_compare hF !![1,1,0;0,1,0;0,0,1]
    !![1,-1,0;0,1,0;0,0,1] (by decide)).2.1 (by simp [transform,evalV,eval])
  have hfp := (optimal_compare hF !![1,-1,0;0,1,0;0,0,1]
    !![1,1,0;0,1,0;0,0,1] (by decide)).2.1 (by simp [transform,evalV,eval])
  have hdm := (optimal_compare hF !![1,0,0;0,1,1;0,0,1]
    !![1,0,0;0,1,-1;0,0,1] (by decide)).2.2
    (by simp [transform,evalV,eval]) (by simp [transform,evalV,eval])
  have hdp := (optimal_compare hF !![1,0,0;0,1,-1;0,0,1]
    !![1,0,0;0,1,1;0,0,1] (by decide)).2.2
    (by simp [transform,evalV,eval]) (by simp [transform,evalV,eval])
  have ht := (optimal_compare hF !![1,0,-1;0,1,1;0,0,1]
    !![1,0,1;0,1,-1;0,0,1] (by decide)).2.2
    (by simp [transform,evalV,eval]) (by simp [transform,evalV,eval])
  simp [transform,evalV,eval] at hab hbc hem hep hfm hfp hdm hdp ht
  omega

lemma optimal_of_same_diagonal {G : Form3 ℚ} {m : ℤ} {F E : Form3 ℤ}
    (hF : Optimal G m F) (hE : Admissible G m E)
    (hD : E.disc = F.disc) (ha : E.a = F.a) (hb : E.b = F.b) (hc : E.c = F.c) :
    Optimal G m E := by
  refine ⟨hE,?_,?_,?_,?_⟩
  · simpa [hD] using hF.2.1
  · intro K hK hKD
    rw [ha]
    exact hF.2.2.1 K hK (hKD.trans hD)
  · intro K hK hKD hKa
    rw [hb]
    exact hF.2.2.2.1 K hK (hKD.trans hD) (hKa.trans ha)
  · intro K hK hKD hKa hKb
    rw [hc]
    exact hF.2.2.2.2 K hK (hKD.trans hD) (hKa.trans ha) (hKb.trans hb)

lemma sign_normalize {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hF : Optimal G m F) :
    ∃ E, Optimal G m E ∧ 0 ≤ E.e ∧ 0 ≤ E.f := by
  by_cases he : 0 ≤ F.e <;> by_cases hf : 0 ≤ F.f
  · exact ⟨F,hF,he,hf⟩
  · let U : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;0,-1,0;0,0,1]
    have hUU : U*U=1 := by decide
    refine ⟨F.transform U,?_,?_,?_⟩
    · exact optimal_of_same_diagonal hF (admissible_transform hF.1 U U hUU)
        (disc_transform_unit F U U hUU) (by simp [U,transform,evalV,eval])
        (by simp [U,transform,evalV,eval]) (by simp [U,transform,evalV,eval])
    · simp [U,transform,evalV,eval]
      omega
    · simp [U,transform,evalV,eval]
      omega
  · let U : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;0,1,0;0,0,-1]
    have hUU : U*U=1 := by decide
    refine ⟨F.transform U,?_,?_,?_⟩
    · exact optimal_of_same_diagonal hF (admissible_transform hF.1 U U hUU)
        (disc_transform_unit F U U hUU) (by simp [U,transform,evalV,eval])
        (by simp [U,transform,evalV,eval]) (by simp [U,transform,evalV,eval])
    · simp [U,transform,evalV,eval]
      omega
    · simp [U,transform,evalV,eval]
      omega
  · let U : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;0,-1,0;0,0,-1]
    have hUU : U*U=1 := by decide
    refine ⟨F.transform U,?_,?_,?_⟩
    · exact optimal_of_same_diagonal hF (admissible_transform hF.1 U U hUU)
        (disc_transform_unit F U U hUU) (by simp [U,transform,evalV,eval])
        (by simp [U,transform,evalV,eval]) (by simp [U,transform,evalV,eval])
    · simp [U,transform,evalV,eval]
      omega
    · simp [U,transform,evalV,eval]
      omega

lemma optimal_reduced_exists {G : Form3 ℚ} {m : ℤ} (hG : G.Pos) (hD : 0 < G.disc)
    (hne : ∃ F, Admissible G m F) : ∃ F, Optimal G m F ∧ Reduced F := by
  obtain ⟨F,hF⟩ := optimal_exists hG hD hne
  obtain ⟨E,hE,he,hf⟩ := sign_normalize hF
  obtain ⟨ha,hab,hbc,hem,hep,hfm,hfp,hdm,hdp,ht⟩ := optimal_weak_reduced hG hE
  exact ⟨E,hE,ha,hab,hbc,he,hep,hf,hfp,hdm,hdp,ht⟩

end Aux306439

/-! ### Integral overlattices -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma evalV_add {R : Type*} [CommRing R] (F : Form3 R) (v w : Fin 3 → R) :
    F.evalV (v+w) = F.evalV v + F.evalV w + dotProduct v (F.hessian.mulVec w) := by
  simp [evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

lemma evalV_smul {R : Type*} [CommRing R] (F : Form3 R) (r : R) (v : Fin 3 → R) :
    F.evalV (r • v) = r^2*F.evalV v := by
  simp [evalV,eval]
  ring

lemma admissible_change {G : Form3 ℚ} {m : ℤ} {F E : Form3 ℤ}
    (hF : Admissible G m F) (hE : E.Rep m) (U : Matrix (Fin 3) (Fin 3) ℚ)
    (hU : U.det ≠ 0) (heq : E.rat = F.rat.transform U) : Admissible G m E := by
  obtain ⟨⟨T,hT,hFT⟩,hrep⟩ := hF
  refine ⟨⟨T*U,?_,?_⟩,hE⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero hT hU
  · rw [heq,hFT,transform_mul]

lemma admissible_div_first {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hF : Admissible G m F) {p a e f : ℤ} (hp : p ≠ 0)
    (ha : F.a = p^2*a) (he : F.e = p*e) (hf : F.f = p*f) :
    Admissible G m (⟨a,F.b,F.c,F.d,e,f⟩ : Form3 ℤ) ∧
    F.disc = p^2*(⟨a,F.b,F.c,F.d,e,f⟩ : Form3 ℤ).disc := by
  let E : Form3 ℤ := ⟨a,F.b,F.c,F.d,e,f⟩
  have heval (x y z : ℤ) : E.eval (p*x) y z = F.eval x y z := by
    dsimp [E,eval]
    rw [ha,he,hf]
    ring
  have hrep : E.Rep m := by
    obtain ⟨v,hv⟩ := hF.2
    refine ⟨![p*v 0,v 1,v 2],?_⟩
    change E.eval (p*v 0) (v 1) (v 2) = m
    rw [heval]
    exact hv
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  let U : Matrix (Fin 3) (Fin 3) ℚ := !![1/(p:ℚ),0,0;0,1,0;0,0,1]
  have hU : U.det ≠ 0 := by simp [U,Matrix.det_fin_three,hpq]
  have heq : E.rat = F.rat.transform U := by
    apply ext_evalV
    intro v
    rw [evalV_transform]
    simp [E,U,rat,map,evalV,eval,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,ha,he,hf]
    field_simp
    <;> ring
  refine ⟨admissible_change hF hrep U hU heq,?_⟩
  dsimp [disc]
  rw [ha,he,hf]
  ring

lemma div_first_contradiction {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hD : 0 < G.disc) (hF : Admissible G m F)
    (hmin : ∀ E, Admissible G m E → F.disc ≤ E.disc)
    {p : ℤ} (hp : 1 < p) (ha : p^2 ∣ F.a) (he : p ∣ F.e) (hf : p ∣ F.f) : False := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨e,he⟩ := he
  obtain ⟨f,hf⟩ := hf
  obtain ⟨hE,heq⟩ := admissible_div_first hF (by omega : p ≠ 0) ha he hf
  have hpos := admissible_disc_pos hD hE
  have hle := hmin _ hE
  have hp2 : 1 < p^2 := by nlinarith
  have hm := mul_lt_mul_of_pos_right hp2 hpos
  nlinarith

-- Congruent vectors remain isotropic one power further if their gradient is divisible by p.
lemma iso_vector_adjust (F : Form3 ℤ) (p a : ℤ) (v w : Fin 3 → ℤ)
    (hQ : p^2 ∣ F.evalV v) (hH : ∀ i, p ∣ F.hessian.mulVec v i) :
    p^2 ∣ F.evalV (a • v + p • w) ∧
    ∀ i, p ∣ F.hessian.mulVec (a • v + p • w) i := by
  have hpol : p ∣ dotProduct w (F.hessian.mulVec v) := by
    apply Finset.dvd_sum
    intro i hi
    exact dvd_mul_of_dvd_right (hH i) (w i)
  have heq : F.evalV (a • v + p • w) =
      a^2*F.evalV v + p^2*F.evalV w + a*p*dotProduct w (F.hessian.mulVec v) := by
    simp [evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  constructor
  · rw [heq]
    apply dvd_add
    · exact dvd_add (dvd_mul_of_dvd_right hQ _) (dvd_mul_right _ _)
    · obtain ⟨b,hb⟩ := hpol
      rw [hb]
      exact ⟨a*b,by ring⟩
  · intro i
    have heq' : F.hessian.mulVec (a • v + p • w) i =
        a * F.hessian.mulVec v i + p * F.hessian.mulVec w i := by
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    rw [heq']
    exact dvd_add (dvd_mul_of_dvd_right (hH i) a) (dvd_mul_right _ _)

lemma bezout_prime {p : ℕ} (hp : p.Prime) {v : ℤ} (hv : ¬(p:ℤ) ∣ v) :
    ∃ a b : ℤ, a*v+b*(p:ℤ)=1 := by
  have hcop : Nat.Coprime v.natAbs p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    exact fun h => hv (Int.natCast_dvd.mpr h)
  have hi : IsCoprime v (p:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop)
  exact hi

lemma normalize_iso_vector (F : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (v : Fin 3 → ℤ) (j : Fin 3) (hv : ¬(p:ℤ) ∣ v j)
    (hQ : (p:ℤ)^2 ∣ F.evalV v) (hH : ∀ i, (p:ℤ) ∣ F.hessian.mulVec v i) :
    ∃ w : Fin 3 → ℤ, w j = 1 ∧ (p:ℤ)^2 ∣ F.evalV w ∧
      ∀ i, (p:ℤ) ∣ F.hessian.mulVec w i := by
  obtain ⟨a,b,hab⟩ := bezout_prime hp hv
  let w : Fin 3 → ℤ := a • v + (p:ℤ) • Pi.single j b
  have hwj : w j = 1 := by simpa [w,mul_comm] using hab
  have h := iso_vector_adjust F (p:ℤ) a v (Pi.single j b) hQ hH
  exact ⟨w,hwj,h.1,h.2⟩

-- Minimal discriminant forbids a primitive vector with a sufficiently divisible norm and gradient.
lemma no_isotropic_radical {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hD : 0 < G.disc) (hF : Admissible G m F)
    (hmin : ∀ E, Admissible G m E → F.disc ≤ E.disc)
    {p : ℕ} (hp : p.Prime) (v : Fin 3 → ℤ)
    (hprim : ∃ j, ¬(p:ℤ) ∣ v j)
    (hQ : (p:ℤ)^2 ∣ F.evalV v) (hH : ∀ i, (p:ℤ) ∣ F.hessian.mulVec v i) : False := by
  obtain ⟨j,hj⟩ := hprim
  obtain ⟨w,hwj,hwQ,hwH⟩ := normalize_iso_vector F hp v j hj hQ hH
  have hp' : 1 < (p:ℤ) := by exact_mod_cast hp.one_lt
  fin_cases j
  · change w 0 = 1 at hwj
    let U : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;w 1,1,0;w 2,0,1]
    let V : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;-w 1,1,0;-w 2,0,1]
    have hUV : U*V=1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U,V,Matrix.mul_apply,Fin.sum_univ_succ]
    have hE := admissible_transform hF U V hUV
    have hminE : ∀ E, Admissible G m E → (F.transform U).disc ≤ E.disc := by
      simpa only [disc_transform_unit F U V hUV] using hmin
    have hA : (F.transform U).a = F.evalV w := by
      simp [U,transform,evalV,eval,hwj]
    have hE' : (F.transform U).e = F.hessian.mulVec w 2 := by
      simp [U,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hwj]
      ring
    have hF' : (F.transform U).f = F.hessian.mulVec w 1 := by
      simp [U,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hwj]
      ring
    exact div_first_contradiction hD hE hminE hp' (hA ▸ hwQ)
      (hE' ▸ hwH 2) (hF' ▸ hwH 1)
  · change w 1 = 1 at hwj
    let U : Matrix (Fin 3) (Fin 3) ℤ := !![w 0,1,0;1,0,0;w 2,0,1]
    let V : Matrix (Fin 3) (Fin 3) ℤ := !![0,1,0;1,-w 0,0;0,-w 2,1]
    have hUV : U*V=1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U,V,Matrix.mul_apply,Fin.sum_univ_succ]
    have hE := admissible_transform hF U V hUV
    have hminE : ∀ E, Admissible G m E → (F.transform U).disc ≤ E.disc := by
      simpa only [disc_transform_unit F U V hUV] using hmin
    have hA : (F.transform U).a = F.evalV w := by
      simp [U,transform,evalV,eval,hwj]
    have hE' : (F.transform U).e = F.hessian.mulVec w 2 := by
      simp [U,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hwj]
      ring
    have hF' : (F.transform U).f = F.hessian.mulVec w 0 := by
      simp [U,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hwj]
      ring
    exact div_first_contradiction hD hE hminE hp' (hA ▸ hwQ)
      (hE' ▸ hwH 2) (hF' ▸ hwH 0)
  · change w 2 = 1 at hwj
    let U : Matrix (Fin 3) (Fin 3) ℤ := !![w 0,1,0;w 1,0,1;1,0,0]
    let V : Matrix (Fin 3) (Fin 3) ℤ := !![0,0,1;1,0,-w 0;0,1,-w 1]
    have hUV : U*V=1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U,V,Matrix.mul_apply,Fin.sum_univ_succ]
    have hE := admissible_transform hF U V hUV
    have hminE : ∀ E, Admissible G m E → (F.transform U).disc ≤ E.disc := by
      simpa only [disc_transform_unit F U V hUV] using hmin
    have hA : (F.transform U).a = F.evalV w := by
      simp [U,transform,evalV,eval,hwj]
    have hE' : (F.transform U).e = F.hessian.mulVec w 1 := by
      simp [U,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hwj]
      ring
    have hF' : (F.transform U).f = F.hessian.mulVec w 0 := by
      simp [U,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hwj]
      ring
    exact div_first_contradiction hD hE hminE hp' (hA ▸ hwQ)
      (hE' ▸ hwH 1) (hF' ▸ hwH 0)

end Form3
end Aux306439

/-! ### Discriminant bounds from local isotropy -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma hessian_map {R S : Type*} [CommRing R] [CommRing S]
    (F : Form3 R) (g : R →+* S) :
    (F.map g).hessian = F.hessian.map g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessian,map,Matrix.map_apply,map_ofNat]

lemma evalV_map {R S : Type*} [CommRing R] [CommRing S]
    (F : Form3 R) (g : R →+* S) (v : Fin 3 → R) :
    (F.map g).evalV (g ∘ v) = g (F.evalV v) := by
  simp [evalV,eval_map]

lemma mapVec_mulVec {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    g ∘ (M.mulVec v) = (M.map g).mulVec (g ∘ v) := by
  funext i
  exact g.map_mulVec M v i

lemma det_map_hom {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Matrix (Fin 3) (Fin 3) R) :
    (M.map g).det = g M.det := by
  exact (g.map_det M).symm

def vmod (p : ℕ) (v : Fin 3 → ℤ) : Fin 3 → ZMod p := (Int.castRingHom (ZMod p)) ∘ v

lemma primitive_iff_vmod {p : ℕ} {v : Fin 3 → ℤ} :
    (∃ i, ¬(p:ℤ) ∣ v i) ↔ vmod p v ≠ 0 := by
  constructor
  · rintro ⟨i,hi⟩ h
    have hz := congrFun h i
    exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  · intro h
    by_contra! h'
    apply h
    funext i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h' i)

lemma all_dvd_iff_vmod {p : ℕ} {v : Fin 3 → ℤ} :
    (∀ i, (p:ℤ) ∣ v i) ↔ vmod p v = 0 := by
  simpa only [not_exists, not_not] using (not_congr (primitive_iff_vmod (p := p) (v := v)))

lemma map_det_ne_zero {p : ℕ} {T : Matrix (Fin 3) (Fin 3) ℤ}
    (hT : ¬(p:ℤ) ∣ T.det) : (T.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
  rw [det_map_hom]
  exact fun h => hT ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

lemma transfer_isotropic_radical (F : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (T : Matrix (Fin 3) (Fin 3) ℤ) (hT : ¬(p:ℤ) ∣ T.det)
    (v : Fin 3 → ℤ) (hprim : ∃ i, ¬(p:ℤ) ∣ v i)
    (hQ : (p:ℤ)^2 ∣ (F.transform T).evalV v)
    (hH : ∀ i, (p:ℤ) ∣ (F.transform T).hessian.mulVec v i) :
    (∃ i, ¬(p:ℤ) ∣ T.mulVec v i) ∧ (p:ℤ)^2 ∣ F.evalV (T.mulVec v) ∧
    ∀ i, (p:ℤ) ∣ F.hessian.mulVec (T.mulVec v) i := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := Int.castRingHom (ZMod p)
  have hT' : (T.map g).det ≠ 0 := map_det_ne_zero hT
  have hv : vmod p v ≠ 0 := primitive_iff_vmod.mp hprim
  have hvT : vmod p (T.mulVec v) = (T.map g).mulVec (vmod p v) := mapVec_mulVec g T v
  refine ⟨?_,?_,?_⟩
  · apply primitive_iff_vmod.mpr
    rw [hvT]
    intro h
    exact hv (Matrix.eq_zero_of_mulVec_eq_zero hT' h)
  · simpa only [evalV_transform] using hQ
  · apply all_dvd_iff_vmod.mpr
    have h := all_dvd_iff_vmod.mp hH
    change g ∘ ((F.transform T).hessian.mulVec v) = 0 at h
    rw [mapVec_mulVec,hessian_transform,Matrix.map_mul,Matrix.map_mul] at h
    have htrans : (T.transpose.map g) = (T.map g).transpose := rfl
    rw [htrans,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec] at h
    have hTt : (T.map g).transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
    have h' := Matrix.eq_zero_of_mulVec_eq_zero hTt h
    change g ∘ (F.hessian.mulVec (T.mulVec v)) = 0
    rw [mapVec_mulVec,mapVec_mulVec]
    exact h'

-- An exact orthogonal-complement identity replaces all local lattice diagonalization.
lemma block_radical (F : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (ha : (p:ℤ) ∣ F.a) (hf : ¬(p:ℤ) ∣ F.f)
    (hD : (p:ℤ)^2 ∣ F.disc) :
    ∃ v : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ v i) ∧ (p:ℤ)^2 ∣ F.evalV v ∧
      ∀ i, (p:ℤ) ∣ F.hessian.mulVec v i := by
  let Δ := 4*F.a*F.b-F.f^2
  let v : Fin 3 → ℤ := ![F.f*F.d-2*F.b*F.e,F.f*F.e-2*F.a*F.d,Δ]
  have hΔ : ¬(p:ℤ) ∣ Δ := by
    intro h
    have hf2 : (p:ℤ) ∣ F.f^2 := by
      have h₁ : (p:ℤ) ∣ 4*F.a*F.b := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha 4) F.b
      have h₂ := dvd_sub h₁ h
      simpa [Δ] using h₂
    have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
    exact hf (hprime.dvd_of_dvd_pow hf2)
  have hq : F.evalV v = Δ*F.disc := by
    simp [v,Δ,evalV,eval,disc]
    ring
  have hh : F.hessian.mulVec v = ![0,0,2*F.disc] := by
    funext i
    fin_cases i <;> simp [v,Δ,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,disc] <;> ring
  refine ⟨v,⟨2,hΔ⟩,?_,?_⟩
  · rw [hq]
    exact dvd_mul_of_dvd_right hD Δ
  · rw [hh]
    intro i
    fin_cases i <;> simp
    exact dvd_mul_of_dvd_right (dvd_trans (dvd_pow_self (p:ℤ) (by decide : 2 ≠ 0)) hD) 2

lemma orth_pair_coordinate {K : Type*} [Field K] (x y : Fin 3 → K)
    (hx : x ≠ 0) (hxy : dotProduct x y = 0) (j : Fin 3) (hy : y j ≠ 0) :
    ∃ i, i ≠ j ∧ x i ≠ 0 := by
  by_contra! h
  have heq : dotProduct x y = x j*y j := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      rw [h i hij,zero_mul]
    · simp
  have hxj : x j = 0 := (mul_eq_zero.mp (heq.symm.trans hxy)).resolve_right hy
  apply hx
  funext i
  by_cases hij : i = j
  · simpa [hij] using hxj
  · exact h i hij

lemma local_basis (F : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (u : Fin 3 → ℤ) (hu : ∃ i, ¬(p:ℤ) ∣ u i)
    (hQ : (p:ℤ) ∣ F.evalV u) (j : Fin 3)
    (hgj : ¬(p:ℤ) ∣ F.hessian.mulVec u j) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℤ,
      ¬(p:ℤ) ∣ T.det ∧ (F.transform T).a = F.evalV u ∧
      ¬(p:ℤ) ∣ (F.transform T).f := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := Int.castRingHom (ZMod p)
  have hdot : dotProduct (vmod p u) (vmod p (F.hessian.mulVec u)) = 0 := by
    have h := congrArg g (two_evalV F u)
    have hQu : g (F.evalV u) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hQ
    simp only [map_mul,map_ofNat,hQu,mul_zero] at h
    have hd : g (dotProduct u (F.hessian.mulVec u)) =
        dotProduct (vmod p u) (vmod p (F.hessian.mulVec u)) := by
      simp [dotProduct,vmod,Fin.sum_univ_succ]
    exact hd.symm.trans h.symm
  have hj' : vmod p (F.hessian.mulVec u) j ≠ 0 := by
    intro h
    exact hgj ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  obtain ⟨i,hij,hui⟩ := orth_pair_coordinate (vmod p u) (vmod p (F.hessian.mulVec u))
    (primitive_iff_vmod.mp hu) hdot j hj'
  have hui' : ¬(p:ℤ) ∣ u i := by
    intro h
    exact hui ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · change ¬(p:ℤ) ∣ u 0 at hui'
    change ¬(p:ℤ) ∣ F.hessian.mulVec u 1 at hgj
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,0,0;u 1,1,0;u 2,0,1]
    refine ⟨T,?_,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hui'
    · simp [T,transform,evalV,eval]
    · have heq : (F.transform T).f = F.hessian.mulVec u 1 := by
        simp [T,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
      rwa [heq]
  · change ¬(p:ℤ) ∣ u 0 at hui'
    change ¬(p:ℤ) ∣ F.hessian.mulVec u 2 at hgj
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,0,0;u 1,0,1;u 2,1,0]
    refine ⟨T,?_,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hui'
    · simp [T,transform,evalV,eval]
    · have heq : (F.transform T).f = F.hessian.mulVec u 2 := by
        simp [T,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
      rwa [heq]
  · change ¬(p:ℤ) ∣ u 1 at hui'
    change ¬(p:ℤ) ∣ F.hessian.mulVec u 0 at hgj
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,1,0;u 1,0,0;u 2,0,1]
    refine ⟨T,?_,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hui'
    · simp [T,transform,evalV,eval]
    · have heq : (F.transform T).f = F.hessian.mulVec u 0 := by
        simp [T,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
      rwa [heq]
  · change ¬(p:ℤ) ∣ u 1 at hui'
    change ¬(p:ℤ) ∣ F.hessian.mulVec u 2 at hgj
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,0,1;u 1,0,0;u 2,1,0]
    refine ⟨T,?_,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hui'
    · simp [T,transform,evalV,eval]
    · have heq : (F.transform T).f = F.hessian.mulVec u 2 := by
        simp [T,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
      rwa [heq]
  · change ¬(p:ℤ) ∣ u 2 at hui'
    change ¬(p:ℤ) ∣ F.hessian.mulVec u 0 at hgj
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,1,0;u 1,0,1;u 2,0,0]
    refine ⟨T,?_,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hui'
    · simp [T,transform,evalV,eval]
    · have heq : (F.transform T).f = F.hessian.mulVec u 0 := by
        simp [T,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
      rwa [heq]
  · change ¬(p:ℤ) ∣ u 2 at hui'
    change ¬(p:ℤ) ∣ F.hessian.mulVec u 1 at hgj
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,0,1;u 1,1,0;u 2,0,0]
    refine ⟨T,?_,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hui'
    · simp [T,transform,evalV,eval]
    · have heq : (F.transform T).f = F.hessian.mulVec u 1 := by
        simp [T,transform,evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
      rwa [heq]

lemma disc_not_sq_of_isotropic {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hD : 0 < G.disc) (hF : Admissible G m F)
    (hmin : ∀ E, Admissible G m E → F.disc ≤ E.disc)
    {p : ℕ} (hp : p.Prime)
    (hiso : ∃ u : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ u i) ∧ (p:ℤ)^2 ∣ F.evalV u) :
    ¬(p:ℤ)^2 ∣ F.disc := by
  intro hFD
  obtain ⟨u,hu,hQu⟩ := hiso
  by_cases hHu : ∀ i, (p:ℤ) ∣ F.hessian.mulVec u i
  · exact no_isotropic_radical hD hF hmin hp u hu hQu hHu
  push_neg at hHu
  obtain ⟨j,hj⟩ := hHu
  have hQu' : (p:ℤ) ∣ F.evalV u :=
    dvd_trans (dvd_pow_self (p:ℤ) (by decide : 2 ≠ 0)) hQu
  obtain ⟨T,hT,ha,hf⟩ := local_basis F hp u hu hQu' j hj
  have hD' : (p:ℤ)^2 ∣ (F.transform T).disc := by
    rw [disc_transform]
    exact dvd_mul_of_dvd_left hFD _
  obtain ⟨v,hv,hQv,hHv⟩ := block_radical (F.transform T) hp (ha ▸ hQu') hf hD'
  obtain ⟨hw,hQw,hHw⟩ := transfer_isotropic_radical F hp T hT v hv hQv hHv
  exact no_isotropic_radical hD hF hmin hp (T.mulVec v) hw hQw hHw

end Form3
end Aux306439

/-! ### Quadratic forms over finite fields -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

def quadratic {R : Type*} [CommRing R] (F : Form3 R) : QuadraticForm R (Fin 3 → R) where
  toFun := F.evalV
  toFun_smul := by
    intro r v
    rw [evalV_smul]
    simp [pow_two]
  exists_companion' := ⟨Matrix.toBilin' F.hessian, by
    intro v w
    rw [Matrix.toBilin'_apply']
    exact evalV_add F v w⟩

lemma binary_rep_finite {K : Type*} [Field K] [Fintype K]
    (hcard : Fintype.card K % 2 = 1) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (c : K) : ∃ x y : K, a*x^2+b*y^2 = c := by
  open Polynomial in
  have hf : (C a * X^2 : K[X]).degree = 2 := degree_C_mul_X_pow 2 ha
  open Polynomial in
  have hg : (C b * X^2 - C c : K[X]).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt]
    · exact degree_C_mul_X_pow 2 hb
    · rw [degree_C_mul_X_pow 2 hb]
      exact lt_of_le_of_lt degree_C_le (by decide)
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨x,y,?_⟩
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_sub] at hxy
  linear_combination hxy

lemma ternary_isotropic_finite {K : Type*} [Field K] [Fintype K]
    [Invertible (2 : K)] (hcard : Fintype.card K % 2 = 1) (F : Form3 K) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ F.evalV v = 0 := by
  obtain ⟨w,⟨iso⟩⟩ : ∃ w : Fin 3 → K,
      QuadraticMap.Equivalent F.quadratic (QuadraticMap.weightedSumSquares K w) := by
    have h := F.quadratic.equivalent_weightedSumSquares
    have hd : Module.finrank K (Fin 3 → K) = 3 := by simp
    rw [hd] at h
    exact h
  have hex : ∃ v : Fin 3 → K, v ≠ 0 ∧ (QuadraticMap.weightedSumSquares K w) v = 0 := by
    by_cases h₀ : w 0 = 0
    · refine ⟨![1,0,0],?_,?_⟩
      · intro h
        have := congrFun h 0
        simpa using this
      · simp [QuadraticMap.weightedSumSquares_apply,Fin.sum_univ_succ,h₀]
    by_cases h₁ : w 1 = 0
    · refine ⟨![0,1,0],?_,?_⟩
      · intro h
        have := congrFun h 1
        simpa using this
      · simp [QuadraticMap.weightedSumSquares_apply,Fin.sum_univ_succ,h₁]
    obtain ⟨x,y,hxy⟩ := binary_rep_finite hcard h₀ h₁ (-w 2)
    refine ⟨![x,y,1],?_,?_⟩
    · intro h
      have := congrFun h 2
      simpa using this
    · simp [QuadraticMap.weightedSumSquares_apply,Fin.sum_univ_succ]
      linear_combination hxy
  obtain ⟨v,hv,hQ⟩ := hex
  refine ⟨iso.symm v,?_,?_⟩
  · intro h
    apply hv
    have h' := congrArg iso h
    simpa using h'
  · exact (iso.symm.map_app v).trans hQ

end Form3
end Aux306439

/-! ### The odd-prime discriminant bound -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma prime_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬(p:ℤ) ∣ 2 := by
  intro h
  have h' : p ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h' |>.resolve_left hp.ne_one)

lemma degenerate_binary_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (b c d : ℤ) (hδ : (p:ℤ) ∣ 4*b*c-d^2) :
    ∃ x y : ℤ, (¬(p:ℤ) ∣ x ∨ ¬(p:ℤ) ∣ y) ∧ (p:ℤ) ∣ b*x^2+c*y^2+d*x*y := by
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hb : (p:ℤ) ∣ b
  · have hd : (p:ℤ) ∣ d := by
      have h₁ : (p:ℤ) ∣ 4*b*c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb 4) c
      have h₂ : (p:ℤ) ∣ d^2 := by simpa using dvd_sub h₁ hδ
      exact hprime.dvd_of_dvd_pow h₂
    refine ⟨1,0,Or.inl ?_,?_⟩
    · exact hprime.not_dvd_one
    · simpa using hb
  · refine ⟨-d,2*b,Or.inr ?_,?_⟩
    · intro h
      rcases hprime.dvd_mul.mp h with h | h
      · exact prime_not_dvd_two hp hp2 h
      · exact hb h
    · convert dvd_mul_of_dvd_right hδ b using 1 <;> ring

lemma binary_cube_radical {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (b c d : ℤ) (hδ : (p:ℤ)^3 ∣ 4*b*c-d^2) :
    ∃ x y : ℤ, (¬(p:ℤ) ∣ x ∨ ¬(p:ℤ) ∣ y) ∧
      (p:ℤ)^2 ∣ b*x^2+c*y^2+d*x*y ∧
      (p:ℤ) ∣ 2*b*x+d*y ∧ (p:ℤ) ∣ d*x+2*c*y := by
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hδ₂ : (p:ℤ)^2 ∣ 4*b*c-d^2 :=
    dvd_trans (pow_dvd_pow (p:ℤ) (by decide : 2 ≤ 3)) hδ
  have hδ₁ : (p:ℤ) ∣ 4*b*c-d^2 :=
    dvd_trans (dvd_pow_self (p:ℤ) (by decide : 2 ≠ 0)) hδ₂
  by_cases hb : (p:ℤ) ∣ b
  · by_cases hc : (p:ℤ) ∣ c
    · have hd : (p:ℤ) ∣ d := by
        have h₁ : (p:ℤ) ∣ 4*b*c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb 4) c
        have h₂ : (p:ℤ) ∣ d^2 := by simpa using dvd_sub h₁ hδ₁
        exact hprime.dvd_of_dvd_pow h₂
      obtain ⟨B,rfl⟩ := hb
      obtain ⟨C,rfl⟩ := hc
      obtain ⟨D,rfl⟩ := hd
      have hδ' : (p:ℤ) ∣ 4*B*C-D^2 := by
        apply (mul_dvd_mul_iff_left (pow_ne_zero 2 hp0)).mp
        convert hδ using 1 <;> ring
      obtain ⟨x,y,hxy,hQ⟩ := degenerate_binary_zero hp hp2 B C D hδ'
      refine ⟨x,y,hxy,?_,?_,?_⟩
      · obtain ⟨k,hk⟩ := hQ
        refine ⟨k,?_⟩
        linear_combination (p:ℤ)*hk
      · exact ⟨2*B*x+D*y,by ring⟩
      · exact ⟨D*x+2*C*y,by ring⟩
    · refine ⟨2*c,-d,Or.inl ?_,?_,?_,?_⟩
      · intro h
        rcases hprime.dvd_mul.mp h with h | h
        · exact prime_not_dvd_two hp hp2 h
        · exact hc h
      · convert dvd_mul_of_dvd_right hδ₂ c using 1 <;> ring
      · convert hδ₁ using 1 <;> ring
      · convert dvd_zero (p:ℤ) using 1 <;> ring
  · refine ⟨-d,2*b,Or.inr ?_,?_,?_,?_⟩
    · intro h
      rcases hprime.dvd_mul.mp h with h | h
      · exact prime_not_dvd_two hp hp2 h
      · exact hb h
    · convert dvd_mul_of_dvd_right hδ₂ b using 1 <;> ring
    · convert dvd_zero (p:ℤ) using 1 <;> ring
    · convert hδ₁ using 1 <;> ring

def scale {R : Type*} [CommRing R] (F : Form3 R) (r : R) : Form3 R :=
  ⟨r*F.a,r*F.b,r*F.c,r*F.d,r*F.e,r*F.f⟩

lemma evalV_scale {R : Type*} [CommRing R] (F : Form3 R) (r : R) (v : Fin 3 → R) :
    (F.scale r).evalV v = r*F.evalV v := by
  simp [scale,evalV,eval]
  ring

lemma hessian_scale {R : Type*} [CommRing R] (F : Form3 R) (r : R) :
    (F.scale r).hessian = r • F.hessian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scale,hessian] <;> ring

lemma finite_isotropic_lift (F : Form3 ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ v : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ v i) ∧ (p:ℤ) ∣ F.evalV v := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    apply prime_not_dvd_two hp hp2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd 2 p]
    norm_cast
  letI := invertibleOfNonzero h2
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact hp.mod_two_eq_one_iff_ne_two.mpr hp2
  let g := Int.castRingHom (ZMod p)
  obtain ⟨v,hv,hq⟩ := ternary_isotropic_finite hcard (F.map g)
  choose w hw using fun i => ZMod.intCast_surjective (v i)
  have hwv : vmod p w = v := funext hw
  refine ⟨w,primitive_iff_vmod.mpr (hwv ▸ hv),?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change g (F.evalV w) = 0
  rw [← evalV_map]
  change (F.map g).evalV (vmod p w) = 0
  rw [hwv]
  exact hq

lemma scaled_radical (F : Form3 ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ v : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ v i) ∧ (p:ℤ)^2 ∣ (F.scale (p:ℤ)).evalV v ∧
      ∀ i, (p:ℤ) ∣ (F.scale (p:ℤ)).hessian.mulVec v i := by
  obtain ⟨v,hv,k,hk⟩ := finite_isotropic_lift F hp hp2
  refine ⟨v,hv,?_,?_⟩
  · rw [evalV_scale,hk]
    exact ⟨k,by ring⟩
  · intro i
    rw [hessian_scale,Matrix.smul_mulVec]
    exact dvd_mul_right _ _

lemma unit_first_cube_radical (F : Form3 ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : ¬(p:ℤ) ∣ F.a) (hD : (p:ℤ)^3 ∣ F.disc) :
    ∃ v : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ v i) ∧ (p:ℤ)^2 ∣ F.evalV v ∧
      ∀ i, (p:ℤ) ∣ F.hessian.mulVec v i := by
  let T : Matrix (Fin 3) (Fin 3) ℤ := !![1,-F.f,-F.e;0,2*F.a,0;0,0,2*F.a]
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2a : ¬(p:ℤ) ∣ 2*F.a := hprime.not_dvd_mul (prime_not_dvd_two hp hp2) ha
  have hT : ¬(p:ℤ) ∣ T.det := by
    have heq : T.det = (2*F.a)^2 := by simp [T,Matrix.det_fin_three]; ring
    rw [heq]
    exact fun h => h2a (hprime.dvd_of_dvd_pow h)
  let E := F.transform T
  have hea : E.a = F.a := by simp [E,T,transform,evalV,eval]
  have hee : E.e = 0 := by simp [E,T,transform,evalV,eval]; ring
  have hef : E.f = 0 := by simp [E,T,transform,evalV,eval]; ring
  have hDE : (p:ℤ)^3 ∣ E.disc := by
    rw [show E = F.transform T from rfl,disc_transform]
    exact dvd_mul_of_dvd_left hD _
  have hδ : (p:ℤ)^3 ∣ 4*E.b*E.c-E.d^2 := by
    apply hprime.pow_dvd_of_dvd_mul_left 3 (hea ▸ ha)
    convert hDE using 1
    simp [disc,hee,hef]
    ring
  obtain ⟨x,y,hxy,hq,hg₁,hg₂⟩ := binary_cube_radical hp hp2 E.b E.c E.d hδ
  have hv : ∃ i, ¬(p:ℤ) ∣ (![0,x,y] : Fin 3 → ℤ) i := by
    rcases hxy with hx | hy
    · exact ⟨1,hx⟩
    · exact ⟨2,hy⟩
  have hq' : (p:ℤ)^2 ∣ E.evalV ![0,x,y] := by simpa [evalV,eval] using hq
  have hh : ∀ i, (p:ℤ) ∣ E.hessian.mulVec ![0,x,y] i := by
    intro i
    fin_cases i
    · simp [hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hee,hef]
    · simpa [hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hg₁
    · simpa [hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hg₂
  exact ⟨T.mulVec ![0,x,y],transfer_isotropic_radical F hp T hT ![0,x,y] hv hq' hh⟩

lemma unit_norm_primitive (F : Form3 ℤ) {p : ℕ} (u : Fin 3 → ℤ)
    (hQ : ¬(p:ℤ) ∣ F.evalV u) : ∃ i, ¬(p:ℤ) ∣ u i := by
  by_contra! h
  have hz := all_dvd_iff_vmod.mp h
  let g := Int.castRingHom (ZMod p)
  have hcast : (F.map g).evalV (vmod p u) = g (F.evalV u) := evalV_map F g u
  rw [hz] at hcast
  simp [evalV,eval] at hcast
  exact hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa [evalV,eval] using hcast.symm))

lemma local_basis_primitive (F : Form3 ℤ) {p : ℕ} (u : Fin 3 → ℤ)
    (hu : ∃ i, ¬(p:ℤ) ∣ u i) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℤ, ¬(p:ℤ) ∣ T.det ∧ (F.transform T).a = F.evalV u := by
  obtain ⟨i,hi⟩ := hu
  fin_cases i
  · change ¬(p:ℤ) ∣ u 0 at hi
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,0,0;u 1,1,0;u 2,0,1]
    refine ⟨T,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hi
    · simp [T,transform,evalV,eval]
  · change ¬(p:ℤ) ∣ u 1 at hi
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,1,0;u 1,0,0;u 2,0,1]
    refine ⟨T,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hi
    · simp [T,transform,evalV,eval]
  · change ¬(p:ℤ) ∣ u 2 at hi
    let T : Matrix (Fin 3) (Fin 3) ℤ := !![u 0,1,0;u 1,0,1;u 2,0,0]
    refine ⟨T,?_,?_⟩
    · simpa [T,Matrix.det_fin_three] using hi
    · simp [T,transform,evalV,eval]

lemma all_norms_div_scale (F : Form3 ℤ) {p : ℤ} (h : ∀ v, p ∣ F.evalV v) :
    ∃ E : Form3 ℤ, F = E.scale p := by
  have ha : p ∣ F.a := by simpa [evalV,eval] using h ![1,0,0]
  have hb : p ∣ F.b := by simpa [evalV,eval] using h ![0,1,0]
  have hc : p ∣ F.c := by simpa [evalV,eval] using h ![0,0,1]
  have hd : p ∣ F.d := by
    have h' := dvd_sub (dvd_sub (h ![0,1,1]) hb) hc
    convert h' using 1 <;> simp [evalV,eval] <;> ring
  have he : p ∣ F.e := by
    have h' := dvd_sub (dvd_sub (h ![1,0,1]) ha) hc
    convert h' using 1 <;> simp [evalV,eval] <;> ring
  have hf : p ∣ F.f := by
    have h' := dvd_sub (dvd_sub (h ![1,1,0]) ha) hb
    convert h' using 1 <;> simp [evalV,eval] <;> ring
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  obtain ⟨c,hc⟩ := hc
  obtain ⟨d,hd⟩ := hd
  obtain ⟨e,he⟩ := he
  obtain ⟨f,hf⟩ := hf
  refine ⟨⟨a,b,c,d,e,f⟩,?_⟩
  cases F
  simp_all [scale]

lemma cube_radical (F : Form3 ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : (p:ℤ)^3 ∣ F.disc) :
    ∃ v : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ v i) ∧ (p:ℤ)^2 ∣ F.evalV v ∧
      ∀ i, (p:ℤ) ∣ F.hessian.mulVec v i := by
  by_cases h : ∀ v, (p:ℤ) ∣ F.evalV v
  · obtain ⟨E,rfl⟩ := all_norms_div_scale F h
    exact scaled_radical E hp hp2
  push_neg at h
  obtain ⟨u,hu⟩ := h
  obtain ⟨T,hT,ha⟩ := local_basis_primitive F u (unit_norm_primitive F u hu)
  have hDE : (p:ℤ)^3 ∣ (F.transform T).disc := by
    rw [disc_transform]
    exact dvd_mul_of_dvd_left hD _
  obtain ⟨v,hv,hQv,hHv⟩ := unit_first_cube_radical (F.transform T) hp hp2 (ha ▸ hu) hDE
  exact ⟨T.mulVec v,transfer_isotropic_radical F hp T hT v hv hQv hHv⟩

lemma disc_not_cube {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hD : 0 < G.disc) (hF : Admissible G m F)
    (hmin : ∀ E, Admissible G m E → F.disc ≤ E.disc)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬(p:ℤ)^3 ∣ F.disc := by
  intro hFD
  obtain ⟨v,hv,hQv,hHv⟩ := cube_radical F hp hp2 hFD
  exact no_isotropic_radical hD hF hmin hp v hv hQv hHv

end Form3
end Aux306439

/-! ### Classification and the conditional representation theorem -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma int_three_rat_sq (d : ℤ) (q : ℚ) (h : (d:ℚ) = 3*q^2) :
    ∃ k : ℤ, d = 3*k^2 := by
  have hs : IsSquare ((3*d : ℤ) : ℚ) := by
    refine ⟨3*q,?_⟩
    push_cast
    rw [h]
    ring
  obtain ⟨z,hz⟩ := Rat.isSquare_intCast_iff.mp hs
  have hprime : Prime (3:ℤ) := by norm_num
  have hdiv : (3:ℤ) ∣ z^2 := by
    rw [pow_two,← hz]
    exact dvd_mul_right _ _
  obtain ⟨k,hk⟩ := hprime.dvd_of_dvd_pow hdiv
  refine ⟨k,?_⟩
  rw [hk] at hz
  nlinarith

lemma admissible_disc_three_sq {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hG : ∃ q : ℚ, G.disc = 3*q^2) (hF : Admissible G m F) :
    ∃ k : ℤ, F.disc = 3*k^2 := by
  obtain ⟨q,hq⟩ := hG
  obtain ⟨⟨T,hT,hFT⟩,hrep⟩ := hF
  apply int_three_rat_sq F.disc (q*T.det)
  have h := congrArg disc hFT
  rw [disc_transform,hq] at h
  simp only [rat,disc_map,Int.coe_castRingHom] at h
  linear_combination h

def IsoMod (F : Form3 ℤ) (p k : ℕ) : Prop :=
  ∃ v : Fin 3 → ℤ, (∃ i, ¬(p:ℤ) ∣ v i) ∧ (p:ℤ)^k ∣ F.evalV v

def IsoAt (F : Form3 ℤ) (p : ℕ) : Prop := ∀ k, F.IsoMod p k

lemma disc_options {G : Form3 ℚ} {m : ℤ} {F : Form3 ℤ}
    (hD : 0 < G.disc) (hG : ∃ q : ℚ, G.disc = 3*q^2)
    (hF : Admissible G m F) (hmin : ∀ E, Admissible G m E → F.disc ≤ E.disc)
    (hiso : ∀ p : ℕ, p.Prime → p ≠ 7 → F.IsoMod p 2) :
    F.disc = 3 ∨ F.disc = 147 := by
  obtain ⟨k,hk⟩ := admissible_disc_three_sq hG hF
  let K := k.natAbs
  have hK : F.disc = 3*(K:ℤ)^2 := by simpa [K,Int.natCast_natAbs,sq_abs] using hk
  have hpos := admissible_disc_pos hD hF
  have hK0 : K ≠ 0 := by intro h; simp [h] at hK; omega
  have huniq : ∀ {p : ℕ}, p.Prime → p ∣ K → p = 7 := by
    intro p hp hpk
    by_contra hp7
    have hn := disc_not_sq_of_isotropic hD hF hmin hp (hiso p hp hp7)
    apply hn
    obtain ⟨t,ht⟩ := hpk
    refine ⟨3*(t:ℤ)^2,?_⟩
    rw [hK,ht]
    push_cast
    ring
  have hpower := Nat.eq_prime_pow_of_unique_prime_dvd hK0 huniq
  have hexp : K.primeFactorsList.length ≤ 1 := by
    by_contra h
    have hlen : 2 ≤ K.primeFactorsList.length := by omega
    have h49 : (7:ℤ)^2 ∣ (K:ℤ) := by
      exact_mod_cast (show 7^2 ∣ K by rw [hpower]; exact pow_dvd_pow 7 hlen)
    obtain ⟨t,ht⟩ := h49
    apply disc_not_cube hD hF hmin (by decide : Nat.Prime 7) (by decide)
    refine ⟨21*t^2,?_⟩
    rw [hK,ht]
    ring
  have hor : K.primeFactorsList.length = 0 ∨ K.primeFactorsList.length = 1 := by omega
  rcases hor with h | h
  · left
    have he : K = 1 := by simpa only [h,pow_zero] using hpower
    simpa only [he,Int.natCast_one,one_pow,mul_one] using hK
  · right
    have he : K = 7 := by simpa only [h,pow_one] using hpower
    norm_num [he] at hK ⊢
    exact hK

end Form3

-- All arithmetic content of the ternary theorem is reduced to local properties of an auxiliary form.
lemma ternary_from_auxiliary {G : Form3 ℚ} {m : ℤ}
    (hpos : G.Pos) (hD : 0 < G.disc) (hG : ∃ q : ℚ, G.disc = 3*q^2)
    (hne : ∃ F, Form3.Admissible G m F)
    (hiso : ∀ F, Form3.Admissible G m F → ∀ p : ℕ, p.Prime → p ≠ 7 → F.IsoMod p 2)
    (hmod : ∀ F, Form3.Admissible G m F → ∀ x y z : ℤ, Nonres7 (F.eval x y z)) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*m := by
  obtain ⟨F,hF,hr⟩ := optimal_reduced_exists hpos hD hne
  have hdisc := Form3.disc_options hD hG hF.1 hF.2.1 (hiso F hF.1)
  have heq := reduced_classification F hr hdisc (hmod F hF.1)
  obtain ⟨v,hv⟩ := hF.1.2
  rw [heq] at hv
  refine ⟨-v 0-v 1,-v 0+v 1-2*v 2,-v 0+v 1+2*v 2,?_⟩
  rw [normalized_to_diagonal]
  exact congrArg (8*·) hv

end Aux306439

/-! ### Local isotropy under rational equivalence -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma primitive_factor {p : ℕ} (hp : p.Prime) (w : Fin 3 → ℤ) (hw : w ≠ 0) :
    ∃ t : ℕ, ∃ v : Fin 3 → ℤ, w = (p:ℤ)^t • v ∧ ∃ i, ¬(p:ℤ) ∣ v i := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hne : ∃ i, w i ≠ 0 := by simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using hw
  obtain ⟨j,hj⟩ := hne
  have hex : ∃ t : ℕ, ¬∀ i, (p:ℤ)^(t+1) ∣ w i := by
    refine ⟨padicValInt p (w j),?_⟩
    intro h
    have h' := (padicValInt_dvd_iff _ _).mp (h j)
    omega
  let t := Nat.find hex
  have ht : ¬∀ i, (p:ℤ)^(t+1) ∣ w i := Nat.find_spec hex
  have hprev : ∀ i, (p:ℤ)^t ∣ w i := by
    cases ht' : t with
    | zero => simp
    | succ s =>
      have hmin := Nat.find_min hex (show s < Nat.find hex by omega)
      simpa only [not_not] using hmin
  choose v hv using hprev
  have hwv : w = (p:ℤ)^t • v := funext hv
  refine ⟨t,v,hwv,?_⟩
  by_contra! h
  apply ht
  intro i
  obtain ⟨r,hr⟩ := h i
  rw [hv i,hr]
  exact ⟨r,by ring⟩

lemma dvd_mulVec (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) (d : ℤ)
    (hv : ∀ i, d ∣ v i) : ∀ i, d ∣ M.mulVec v i := by
  intro i
  dsimp [Matrix.mulVec,dotProduct]
  apply Finset.dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_right (hv j) _

lemma primitive_factor_bound {p : ℕ} (hp : p.Prime)
    (U : Matrix (Fin 3) (Fin 3) ℤ) (hU : U.det ≠ 0)
    (v z : Fin 3 → ℤ) (hv : ∃ i, ¬(p:ℤ) ∣ v i) (t : ℕ)
    (hw : U.mulVec v = (p:ℤ)^t • z) : t ≤ padicValInt p U.det := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv : ∀ i, (p:ℤ)^t ∣ U.mulVec v i := by
    rw [hw]
    intro i
    exact dvd_mul_right _ _
  have hadj := dvd_mulVec U.adjugate (U.mulVec v) ((p:ℤ)^t) hdiv
  rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec] at hadj
  obtain ⟨i,hi⟩ := hv
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD : (p:ℤ)^t ∣ U.det := hprime.pow_dvd_of_dvd_mul_right t hi (hadj i)
  exact ((padicValInt_dvd_iff _ _).mp hD).resolve_left hU

lemma isoAt_of_intertwining (F G : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (hG : G.IsoAt p) (U : Matrix (Fin 3) (Fin 3) ℤ) (hU : U.det ≠ 0) (D : ℤ)
    (hnorm : ∀ v : Fin 3 → ℤ, F.evalV (U.mulVec v) = D^2*G.evalV v) : F.IsoAt p := by
  intro k
  obtain ⟨v,hv,hq⟩ := hG (k+2*padicValInt p U.det)
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨i,hi⟩ := hv
    exact hi (by simp [h])
  have hw0 : U.mulVec v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hU h)
  obtain ⟨t,z,hw,hz⟩ := primitive_factor hp (U.mulVec v) hw0
  have ht := primitive_factor_bound hp U hU v z hv t hw
  refine ⟨z,hz,?_⟩
  have hq' : (p:ℤ)^(k+2*t) ∣ F.evalV (U.mulVec v) := by
    rw [hnorm]
    exact dvd_mul_of_dvd_right
      (dvd_trans (pow_dvd_pow (p:ℤ) (by omega)) hq) _
  rw [hw,evalV_smul] at hq'
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he₁ : (p:ℤ)^(k+2*t) = (p:ℤ)^(2*t)*(p:ℤ)^k := by rw [← pow_add]; congr 1; omega
  have he₂ : ((p:ℤ)^t)^2 = (p:ℤ)^(2*t) := by rw [← pow_mul]; congr 1; omega
  rw [he₁,he₂] at hq'
  exact (mul_dvd_mul_iff_left (pow_ne_zero (2*t) hp0)).mp hq' 

lemma clear_matrix_denominators (T : Matrix (Fin 3) (Fin 3) ℚ) :
    ∃ D : ℤ, ∃ U : Matrix (Fin 3) (Fin 3) ℤ, D ≠ 0 ∧
      U.map (Int.castRingHom ℚ) = (D:ℚ) • T := by
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun ij : Fin 3 × Fin 3 => T ij.1 ij.2)
  choose u hu using hb
  refine ⟨b,fun i j => u (i,j),?_,?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp b.2
  · ext i j
    simpa [Algebra.smul_def] using hu (i,j)

lemma rational_intertwining {F G : Form3 ℤ} (T : Matrix (Fin 3) (Fin 3) ℚ)
    (hT : T.det ≠ 0) (hFT : F.rat = G.rat.transform T) :
    ∃ D : ℤ, ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det ≠ 0 ∧
      ∀ v : Fin 3 → ℤ, F.evalV (U.mulVec v) = D^2*G.evalV v := by
  obtain ⟨D,U,hD,hU⟩ := clear_matrix_denominators T⁻¹
  have hDq : (D:ℚ) ≠ 0 := by exact_mod_cast hD
  have hTi : T⁻¹.det ≠ 0 := by rw [Matrix.det_nonsing_inv]; simpa using hT
  have hUq : (U.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [hU,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hDq) hTi
  have hUi : U.det ≠ 0 := by
    rw [det_map_hom] at hUq
    change (U.det:ℚ) ≠ 0 at hUq
    exact_mod_cast hUq
  refine ⟨D,U,hUi,?_⟩
  intro v
  let g := Int.castRingHom ℚ
  have heq : T * (U.map g) = (D:ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    rw [hU,Matrix.mul_smul,Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT)]
  have heqv : T.mulVec ((U.map g).mulVec (g ∘ v)) = (D:ℚ) • (g ∘ v) := by
    rw [Matrix.mulVec_mulVec,heq,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hnorm : F.rat.evalV (g ∘ U.mulVec v) = (D:ℚ)^2 * G.rat.evalV (g ∘ v) := by
    rw [hFT,evalV_transform,mapVec_mulVec,heqv,evalV_smul]
  change (F.map g).evalV (g ∘ U.mulVec v) = (D:ℚ)^2*(G.map g).evalV (g ∘ v) at hnorm
  rw [evalV_map,evalV_map] at hnorm
  change (F.evalV (U.mulVec v):ℚ) = (D:ℚ)^2*(G.evalV v:ℚ) at hnorm
  exact_mod_cast hnorm

lemma isoAt_rational_equiv {F G : Form3 ℤ} {p : ℕ} (hp : p.Prime)
    (hG : G.IsoAt p) (T : Matrix (Fin 3) (Fin 3) ℚ)
    (hT : T.det ≠ 0) (hFT : F.rat = G.rat.transform T) : F.IsoAt p := by
  obtain ⟨D,U,hU,hnorm⟩ := rational_intertwining T hT hFT
  exact isoAt_of_intertwining F G hp hG U hU D hnorm

end Form3
end Aux306439

/-! ### Lifting congruence solutions -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma evalV_add_single (F : Form3 ℤ) (v : Fin 3 → ℤ) (j : Fin 3) (r : ℤ) :
    F.evalV (v + r • Pi.single j 1) = F.evalV v + r*F.hessian.mulVec v j +
      r^2*F.evalV (Pi.single j 1) := by
  fin_cases j <;> simp [evalV,eval,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Pi.single_apply] <;> ring

lemma hessian_add_single (F : Form3 ℤ) (v : Fin 3 → ℤ) (j : Fin 3) (r : ℤ) :
    F.hessian.mulVec (v + r • Pi.single j 1) j =
      F.hessian.mulVec v j + r*F.hessian j j := by
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_single]
  simp

lemma hensel_step (F : Form3 ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k)
    (v : Fin 3 → ℤ) (j : Fin 3) (hQ : (p:ℤ)^k ∣ F.evalV v)
    (hg : ¬(p:ℤ) ∣ F.hessian.mulVec v j) :
    ∃ w : Fin 3 → ℤ, (∀ i, i ≠ j → w i = v i) ∧
      (p:ℤ)^(k+1) ∣ F.evalV w ∧ ¬(p:ℤ) ∣ F.hessian.mulVec w j := by
  obtain ⟨q,hq⟩ := hQ
  obtain ⟨a,b,hab⟩ := bezout_prime hp hg
  let r : ℤ := -(p:ℤ)^k*a*q
  let w := v + r • Pi.single j 1
  have hpr : (p:ℤ) ∣ r := by
    dsimp [r]
    simpa only [pow_one] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_neg.mpr (pow_dvd_pow (p:ℤ) hk)) a) q
  refine ⟨w,?_,?_,?_⟩
  · intro i hij
    simp [w,Pi.single_apply,hij]
  · have hpp : (p:ℤ)^(k+1) ∣ r^2 := by
      have hexp : k+1 ≤ 2*k := by omega
      have hrq : r^2 = (p:ℤ)^(2*k)*(a*q)^2 := by
        simp [r,pow_mul]
        ring
      rw [hrq]
      exact dvd_mul_of_dvd_left (pow_dvd_pow (p:ℤ) hexp) _
    have hlin : F.evalV v + r*F.hessian.mulVec v j = (p:ℤ)^(k+1)*(q*b) := by
      rw [hq]
      dsimp [r]
      rw [pow_succ]
      linear_combination -(p:ℤ)^k*q*hab
    rw [show w = v + r • Pi.single j 1 from rfl,evalV_add_single,hlin]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hpp _)
  · intro h
    apply hg
    have hdiff := dvd_mul_of_dvd_left hpr (F.hessian j j)
    have h' := dvd_sub h hdiff
    rw [show w = v + r • Pi.single j 1 from rfl,hessian_add_single] at h'
    simpa using h'

lemma smooth_lift (F : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (v : Fin 3 → ℤ) (j : Fin 3) (hQ : (p:ℤ) ∣ F.evalV v)
    (hg : ¬(p:ℤ) ∣ F.hessian.mulVec v j) :
    ∀ k : ℕ, ∃ w : Fin 3 → ℤ, (∀ i, i ≠ j → w i = v i) ∧
      (p:ℤ)^k ∣ F.evalV w ∧ ¬(p:ℤ) ∣ F.hessian.mulVec w j := by
  have haux : ∀ k : ℕ, ∃ w : Fin 3 → ℤ, (∀ i, i ≠ j → w i = v i) ∧
      (p:ℤ)^(k+1) ∣ F.evalV w ∧ ¬(p:ℤ) ∣ F.hessian.mulVec w j := by
    intro k
    induction k with
    | zero => exact ⟨v,fun _ _ => rfl,by simpa using hQ,hg⟩
    | succ k ih =>
      obtain ⟨w,hw,hqw,hgw⟩ := ih
      obtain ⟨z,hz,hqz,hgz⟩ := hensel_step F hp (k+1) (by omega) w j hqw hgw
      exact ⟨z,fun i hi => (hz i hi).trans (hw i hi),hqz,hgz⟩
  intro k
  obtain ⟨w,hw,hqw,hgw⟩ := haux k
  exact ⟨w,hw,dvd_trans (pow_dvd_pow (p:ℤ) (by omega : k ≤ k+1)) hqw,hgw⟩

lemma isoAt_of_smooth (F : Form3 ℤ) {p : ℕ} (hp : p.Prime)
    (v : Fin 3 → ℤ) (j : Fin 3) (hQ : (p:ℤ) ∣ F.evalV v)
    (hg : ¬(p:ℤ) ∣ F.hessian.mulVec v j) : F.IsoAt p := by
  intro k
  obtain ⟨w,hw,hQw,hgw⟩ := smooth_lift F hp v j hQ hg k
  refine ⟨w,?_,hQw⟩
  by_contra! h
  exact hgw (dvd_mulVec F.hessian w (p:ℤ) h j)

lemma quadratic_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a b r : ℤ) (ha : ¬(p:ℤ) ∣ a) (hr : ¬(p:ℤ) ∣ r)
    (hQ : (p:ℤ) ∣ a*r^2+b) : ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ a*x^2+b := by
  let F : Form3 ℤ := ⟨a,b,0,0,0,0⟩
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hg : ¬(p:ℤ) ∣ F.hessian.mulVec ![r,1,0] 0 := by
    simpa [F,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using
      hprime.not_dvd_mul (hprime.not_dvd_mul (prime_not_dvd_two hp hp2) ha) hr
  have hQ' : (p:ℤ) ∣ F.evalV ![r,1,0] := by simpa [F,evalV,eval] using hQ
  intro k
  obtain ⟨v,hv,hq,hg'⟩ := smooth_lift F hp ![r,1,0] 0 hQ' hg k
  have h₁ : v 1 = 1 := hv 1 (by decide)
  have h₂ : v 2 = 0 := hv 2 (by decide)
  refine ⟨v 0,?_⟩
  simpa [F,evalV,eval,h₁,h₂] using hq

lemma isoAt_scale (F : Form3 ℤ) {p : ℕ} (hF : F.IsoAt p) (d : ℤ) :
    (F.scale d).IsoAt p := by
  intro k
  obtain ⟨v,hv,hq⟩ := hF k
  refine ⟨v,hv,?_⟩
  rw [evalV_scale]
  exact dvd_mul_of_dvd_right hq d

lemma diagonal_isoAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a b c : ℤ) (ha : ¬(p:ℤ) ∣ a) (hb : ¬(p:ℤ) ∣ b) (hc : ¬(p:ℤ) ∣ c) :
    (⟨a,b,c,0,0,0⟩ : Form3 ℤ).IsoAt p := by
  let F : Form3 ℤ := ⟨a,b,c,0,0,0⟩
  obtain ⟨v,⟨j,hj⟩,hq⟩ := finite_isotropic_lift F hp hp2
  apply isoAt_of_smooth F hp v j hq
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  fin_cases j
  · change ¬(p:ℤ) ∣ v 0 at hj
    simpa [F,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using
      hprime.not_dvd_mul (hprime.not_dvd_mul (prime_not_dvd_two hp hp2) ha) hj
  · change ¬(p:ℤ) ∣ v 1 at hj
    simpa [F,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using
      hprime.not_dvd_mul (hprime.not_dvd_mul (prime_not_dvd_two hp hp2) hb) hj
  · change ¬(p:ℤ) ∣ v 2 at hj
    simpa [F,hessian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using
      hprime.not_dvd_mul (hprime.not_dvd_mul (prime_not_dvd_two hp hp2) hc) hj

end Form3
end Aux306439

/-! ### Binary and ternary local constructions -/

set_option maxHeartbeats 0
namespace Aux306439
namespace Form3

lemma two_adic_square (b : ℤ) (hb : (8:ℤ) ∣ 1+b) :
    ∀ k : ℕ, ∃ x : ℤ, (2:ℤ)^k ∣ x^2+b := by
  have haux : ∀ n : ℕ, ∃ x : ℤ, (2:ℤ) ∣ x+1 ∧ (2:ℤ)^(n+3) ∣ x^2+b := by
    intro n
    induction n with
    | zero => exact ⟨1,by decide,by simpa using hb⟩
    | succ n ih =>
      obtain ⟨x,hx,q,hq⟩ := ih
      let y := x + (2:ℤ)^(n+2)*q
      refine ⟨y,?_,?_⟩
      · have h₁ : (2:ℤ) ∣ (2:ℤ)^(n+2)*q := by
          apply dvd_mul_of_dvd_left
          simpa using pow_dvd_pow (2:ℤ) (show 1 ≤ n+2 by omega)
        simpa [y,add_right_comm] using dvd_add hx h₁
      · have heq : y^2+b = (2:ℤ)^(n+3)*q*(x+1) + (2:ℤ)^(2*n+4)*q^2 := by
          dsimp [y]
          rw [show 2*n+4 = (n+2)*2 by omega,pow_mul]
          have he : (2:ℤ)^(n+3) = 2*(2:ℤ)^(n+2) := by
            rw [show n+3 = (n+2)+1 by omega,pow_succ]
            ring
          rw [he] at hq ⊢
          nlinarith [hq]
        rw [heq]
        apply dvd_add
        · obtain ⟨r,hr⟩ := hx
          rw [hr]
          refine ⟨q*r,?_⟩
          rw [show n+1+3 = (n+3)+1 by omega,pow_succ]
          ring
        · exact dvd_mul_of_dvd_left (pow_dvd_pow (2:ℤ) (by omega)) _
  intro k
  obtain ⟨x,hx,hq⟩ := haux k
  exact ⟨x,dvd_trans (pow_dvd_pow (2:ℤ) (by omega : k ≤ k+3)) hq⟩

lemma diagonal_pair13 (a b t : ℤ) {p : ℕ} (hp : p.Prime)
    (hroot : ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ x^2+t) :
    (⟨a,b,a*t,0,0,0⟩ : Form3 ℤ).IsoAt p := by
  intro k
  obtain ⟨x,hx⟩ := hroot k
  refine ⟨![x,0,1],⟨2,?_⟩,?_⟩
  · exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one
  · convert dvd_mul_of_dvd_right hx a using 1 <;> simp [evalV,eval] <;> ring

lemma diagonal_pair23 (a b t : ℤ) {p : ℕ} (hp : p.Prime)
    (hroot : ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ x^2+t) :
    (⟨a,b,b*t,0,0,0⟩ : Form3 ℤ).IsoAt p := by
  intro k
  obtain ⟨x,hx⟩ := hroot k
  refine ⟨![0,x,1],⟨2,?_⟩,?_⟩
  · exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one
  · convert dvd_mul_of_dvd_right hx b using 1 <;> simp [evalV,eval] <;> ring

lemma diagonal_pair23_three (a d m : ℤ) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hroot : ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ 3*x^2+9*m) :
    (⟨a,3*d,d*m,0,0,0⟩ : Form3 ℤ).IsoAt p := by
  intro k
  obtain ⟨x,hx⟩ := hroot k
  refine ⟨![0,x,3],⟨2,?_⟩,?_⟩
  · change ¬(p:ℤ) ∣ 3
    intro h
    have h' : p ∣ 3 := by exact_mod_cast h
    exact hp3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h' |>.resolve_left hp.ne_one)
  · convert dvd_mul_of_dvd_right hx d using 1 <;> simp [evalV,eval] <;> ring

lemma diagonal_pair12 (a b c : ℤ) {p : ℕ} (hp : p.Prime)
    (hroot : ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ a*x^2+b) :
    (⟨a,b,c,0,0,0⟩ : Form3 ℤ).IsoAt p := by
  intro k
  obtain ⟨x,hx⟩ := hroot k
  refine ⟨![x,1,0],⟨1,?_⟩,?_⟩
  · exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one
  · simpa [evalV,eval] using hx

end Form3
end Aux306439

/-! ### The obstruction at 7 and auxiliary diagonal forms -/

set_option maxHeartbeats 0
namespace Aux306439
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def NR7 (x : ZMod 7) : Prop := x = 0 ∨ x = 3 ∨ x = 5 ∨ x = 6

lemma nonres7_iff {n : ℤ} : Nonres7 n ↔ NR7 (n : ZMod 7) := by
  have h0 := ZMod.intCast_eq_intCast_iff' n 0 7
  have h3 := ZMod.intCast_eq_intCast_iff' n 3 7
  have h5 := ZMod.intCast_eq_intCast_iff' n 5 7
  have h6 := ZMod.intCast_eq_intCast_iff' n 6 7
  norm_num at h0 h3 h5 h6
  simp only [Nonres7,NR7,h0,h3,h5,h6,Int.dvd_iff_emod_eq_zero]

lemma nr7_div_sq : ∀ (m n d x : ZMod 7), NR7 m → d ≠ 0 → n*d^2 = m*x^2 → NR7 n := by
  unfold NR7
  decide

lemma nr7_binary1 : ∀ (m x y : ZMod 7), NR7 m → m ≠ 0 →
    x^2+3*m*y^2 = 0 → x = 0 ∧ y = 0 := by unfold NR7; decide

lemma nr7_binary3 : ∀ (m x y : ZMod 7), NR7 m → m ≠ 0 →
    3*x^2+m*y^2 = 0 → x = 0 ∧ y = 0 := by unfold NR7; decide

lemma nr7_times_three : ∀ (x : ZMod 7), x ≠ 0 → NR7 (3*x^2) ∧ 3*x^2 ≠ 0 := by unfold NR7; decide

lemma norm_nonres_den (m r a b : ℤ) (hm : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m)
    (hr7 : ¬(7:ℤ) ∣ r)
    (hbin : ∀ y z : ℤ, (7:ℤ) ∣ a*y^2+b*z^2 → (7:ℤ) ∣ y ∧ (7:ℤ) ∣ z)
    (n D X Y Z : ℤ) (hD : D ≠ 0)
    (heq : n*D^2 = m*X^2+7*r*(a*Y^2+b*Z^2)) : Nonres7 n := by
  have h7 : (7 : ZMod 7) = 0 := by decide
  have hm0 : (m : ZMod 7) ≠ 0 := by
    intro h
    exact hm7 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  induction D using (measure Int.natAbs).wf.induction generalizing X Y Z with
  | h D ih =>
    by_cases h7D : (7:ℤ) ∣ D
    · have hX : (7:ℤ) ∣ X := by
        have hd0 : (D : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h7D
        have h := congrArg (Int.castRingHom (ZMod 7)) heq
        norm_num [map_ofNat,hd0,h7] at h
        simp only [h7,zero_mul,add_zero] at h
        have hX0 : (X : ZMod 7)^2 = 0 := (mul_eq_zero.mp h.symm).resolve_left hm0
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (pow_eq_zero hX0)
      obtain ⟨d,hd⟩ := h7D
      obtain ⟨x,hx⟩ := hX
      have hbinary : (7:ℤ) ∣ a*Y^2+b*Z^2 := by
        have hmul : (7:ℤ) ∣ r*(a*Y^2+b*Z^2) := by
          refine ⟨n*d^2-m*x^2,?_⟩
          rw [hd,hx] at heq
          nlinarith [heq]
        exact ((show Prime (7:ℤ) by norm_num).dvd_mul.mp hmul).resolve_left hr7
      obtain ⟨hY,hZ⟩ := hbin Y Z hbinary
      obtain ⟨y,hy⟩ := hY
      obtain ⟨z,hz⟩ := hZ
      have hd0 : d ≠ 0 := by intro h; simp [h] at hd; exact hD hd
      have hlt : d.natAbs < D.natAbs := by
        rw [hd,Int.natAbs_mul]
        have hpos := Int.natAbs_pos.mpr hd0
        norm_num
        omega
      apply ih d hlt x y z hd0
      rw [hd,hx,hy,hz] at heq
      nlinarith [heq]
    · apply nonres7_iff.mpr
      apply nr7_div_sq (m:ZMod 7) (n:ZMod 7) (D:ZMod 7) (X:ZMod 7)
        (nonres7_iff.mp hm)
      · exact fun h => h7D ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
      · have h := congrArg (Int.castRingHom (ZMod 7)) heq
        norm_num [map_ofNat,h7] at h
        simp only [h7,zero_mul,add_zero] at h
        exact h

lemma binary1_anisotropic (m : ℤ) (hm : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m) :
    ∀ y z : ℤ, (7:ℤ) ∣ y^2+3*m*z^2 → (7:ℤ) ∣ y ∧ (7:ℤ) ∣ z := by
  intro y z h
  have hm0 : (m : ZMod 7) ≠ 0 := fun h => hm7 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  push_cast at h0
  have h' := nr7_binary1 (m:ZMod 7) (y:ZMod 7) (z:ZMod 7) (nonres7_iff.mp hm) hm0 h0
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'.2⟩

lemma binary3_anisotropic (m : ℤ) (hm : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m) :
    ∀ y z : ℤ, (7:ℤ) ∣ 3*y^2+m*z^2 → (7:ℤ) ∣ y ∧ (7:ℤ) ∣ z := by
  intro y z h
  have hm0 : (m : ZMod 7) ≠ 0 := fun h => hm7 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  push_cast at h0
  have h' := nr7_binary3 (m:ZMod 7) (y:ZMod 7) (z:ZMod 7) (nonres7_iff.mp hm) hm0 h0
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'.2⟩

namespace Form3

lemma norm_residues_admissible (G : Form3 ℤ) (m : ℤ)
    (hden : ∀ n D X Y Z : ℤ, D ≠ 0 → n*D^2 = G.eval X Y Z → Nonres7 n)
    (F : Form3 ℤ) (hF : Admissible G.rat m F) :
    ∀ x y z : ℤ, Nonres7 (F.eval x y z) := by
  obtain ⟨⟨T,hT,hFT⟩,hrep⟩ := hF
  obtain ⟨D,U,hD,hU⟩ := clear_matrix_denominators T
  intro x y z
  let v : Fin 3 → ℤ := ![x,y,z]
  let g := Int.castRingHom ℚ
  have hnorm : G.rat.evalV (g ∘ U.mulVec v) = (D:ℚ)^2 * F.rat.evalV (g ∘ v) := by
    rw [mapVec_mulVec,hU,Matrix.smul_mulVec,evalV_smul,hFT,evalV_transform]
  change (G.map g).evalV (g ∘ U.mulVec v) = (D:ℚ)^2*(F.map g).evalV (g ∘ v) at hnorm
  rw [evalV_map,evalV_map] at hnorm
  change (G.evalV (U.mulVec v):ℚ) = (D:ℚ)^2*(F.evalV v:ℚ) at hnorm
  have hn : G.evalV (U.mulVec v) = D^2*F.evalV v := by exact_mod_cast hnorm
  apply hden (F.eval x y z) D (U.mulVec v 0) (U.mulVec v 1) (U.mulVec v 2) hD
  change F.evalV v * D^2 = G.evalV (U.mulVec v)
  rw [hn]
  ring

def aux1 (m r : ℤ) : Form3 ℤ := ⟨m,7*r,21*m*r,0,0,0⟩
def aux3 (m r : ℤ) : Form3 ℤ := ⟨m,21*r,7*m*r,0,0,0⟩

lemma aux1_residues (m r n D X Y Z : ℤ) (hm : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m)
    (hr7 : ¬(7:ℤ) ∣ r) (hD : D ≠ 0) (hn : n*D^2 = (aux1 m r).eval X Y Z) : Nonres7 n := by
  apply norm_nonres_den m r 1 (3*m) hm hm7 hr7 (by simpa using binary1_anisotropic m hm hm7)
    n D X Y Z hD
  simp [aux1,eval] at hn
  linear_combination hn

lemma aux3_residues (m r n D X Y Z : ℤ) (hm : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m)
    (hr7 : ¬(7:ℤ) ∣ r) (hD : D ≠ 0) (hn : n*D^2 = (aux3 m r).eval X Y Z) : Nonres7 n := by
  apply norm_nonres_den m r 3 m hm hm7 hr7 (binary3_anisotropic m hm hm7)
    n D X Y Z hD
  simp [aux3,eval] at hn
  linear_combination hn

lemma diagonal_pos (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (⟨a,b,c,0,0,0⟩ : Form3 ℚ).Pos := by
  intro v hv
  have hne : ∃ i, v i ≠ 0 := by simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using hv
  obtain ⟨i,hi⟩ := hne
  have h₀ : 0 ≤ a*(v 0)^2 := mul_nonneg ha.le (sq_nonneg _)
  have h₁ : 0 ≤ b*(v 1)^2 := mul_nonneg hb.le (sq_nonneg _)
  have h₂ : 0 ≤ c*(v 2)^2 := mul_nonneg hc.le (sq_nonneg _)
  simp [evalV,eval]
  fin_cases i
  · change v 0 ≠ 0 at hi
    have := mul_pos ha (sq_pos_of_ne_zero hi)
    linarith
  · change v 1 ≠ 0 at hi
    have := mul_pos hb (sq_pos_of_ne_zero hi)
    linarith
  · change v 2 ≠ 0 at hi
    have := mul_pos hc (sq_pos_of_ne_zero hi)
    linarith

lemma self_admissible (F : Form3 ℤ) (m : ℤ) (hrep : F.Rep m) : Admissible F.rat m F := by
  refine ⟨⟨1,by simp,?_⟩,hrep⟩
  simp

lemma aux1_suffices (m r : ℤ) (hm : 0 < m) (hr : 0 < r)
    (hmres : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m) (hr7 : ¬(7:ℤ) ∣ r)
    (hiso : ∀ p : ℕ, p.Prime → p ≠ 7 → (aux1 m r).IsoAt p) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*m := by
  have hpos : (aux1 m r).rat.Pos := by
    apply diagonal_pos <;> simp [aux1,rat,map] <;> positivity
  have hD : 0 < (aux1 m r).rat.disc := by
    simp [aux1,rat,map,disc]
    positivity
  have hG : ∃ q : ℚ, (aux1 m r).rat.disc = 3*q^2 := by
    refine ⟨14*(m:ℚ)*r,?_⟩
    simp [aux1,rat,map,disc]
    ring
  apply ternary_from_auxiliary hpos hD hG
  · refine ⟨aux1 m r,self_admissible _ _ ?_⟩
    exact ⟨![1,0,0],by simp [aux1,evalV,eval]⟩
  · intro F hF p hp hp7
    obtain ⟨⟨T,hT,hFT⟩,hrep⟩ := hF
    exact isoAt_rational_equiv hp (hiso p hp hp7) T hT hFT 2
  · intro F hF
    exact norm_residues_admissible (aux1 m r) m
      (fun n D X Y Z hD hn => aux1_residues m r n D X Y Z hmres hm7 hr7 hD hn) F hF

lemma aux3_suffices (m r : ℤ) (hm : 0 < m) (hr : 0 < r)
    (hmres : Nonres7 m) (hm7 : ¬(7:ℤ) ∣ m) (hr7 : ¬(7:ℤ) ∣ r)
    (hiso : ∀ p : ℕ, p.Prime → p ≠ 7 → (aux3 m r).IsoAt p) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*m := by
  have hpos : (aux3 m r).rat.Pos := by
    apply diagonal_pos <;> simp [aux3,rat,map] <;> positivity
  have hD : 0 < (aux3 m r).rat.disc := by
    simp [aux3,rat,map,disc]
    positivity
  have hG : ∃ q : ℚ, (aux3 m r).rat.disc = 3*q^2 := by
    refine ⟨14*(m:ℚ)*r,?_⟩
    simp [aux3,rat,map,disc]
    ring
  apply ternary_from_auxiliary hpos hD hG
  · refine ⟨aux3 m r,self_admissible _ _ ?_⟩
    exact ⟨![1,0,0],by simp [aux3,evalV,eval]⟩
  · intro F hF p hp hp7
    obtain ⟨⟨T,hT,hFT⟩,hrep⟩ := hF
    exact isoAt_rational_equiv hp (hiso p hp hp7) T hT hFT 2
  · intro F hF
    exact norm_residues_admissible (aux3 m r) m
      (fun n D X Y Z hD hn => aux3_residues m r n D X Y Z hmres hm7 hr7 hD hn) F hF

end Form3
end Aux306439

/-! ### Auxiliary primes and quadratic reciprocity -/

set_option maxHeartbeats 0
namespace Aux306439
open scoped NumberTheorySymbols

lemma prime_two_congruences (s α c N : ℕ) (hs : 0 < s) (hs24 : Nat.Coprime 24 s)
    (hα : α.Coprime 24) (hc : c.Coprime s) :
    ∃ r : ℕ, N < r ∧ r.Prime ∧ r ≡ α [MOD 24] ∧ (r:ℤ) ≡ -(c:ℤ) [ZMOD (s:ℤ)] := by
  let β := (s-1)*c
  have hb : β.Coprime s := by
    apply Nat.Coprime.mul_left
    · exact (Nat.coprime_self_sub_left (by omega : 1 ≤ s)).mpr (Nat.coprime_one_left s)
    · exact hc
  let x := Nat.chineseRemainder hs24 α β
  have hx24 : (x:ℕ).Coprime 24 := by
    rw [Nat.coprime_iff_gcd_eq_one,x.2.1.gcd_eq]
    exact hα
  have hxs : (x:ℕ).Coprime s := by
    rw [Nat.coprime_iff_gcd_eq_one,x.2.2.gcd_eq]
    exact hb
  obtain ⟨r,hrN,hr,hrx⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (show 24*s ≠ 0 by omega) (hx24.mul_right hxs)
  have hr24 : r ≡ α [MOD 24] := (hrx.of_dvd (dvd_mul_right 24 s)).trans x.2.1
  have hrs : r ≡ β [MOD s] := (hrx.of_dvd (dvd_mul_left s 24)).trans x.2.2
  refine ⟨r,hrN,hr,hr24,?_⟩
  apply (Int.natCast_modEq_iff.mpr hrs).trans
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(c:ℤ),?_⟩
  dsimp [β]
  rw [Nat.cast_sub (by omega : 1 ≤ s)]
  push_cast
  ring

lemma neg_odd_reciprocity {a b : ℕ} (ha : a % 4 = 3) (hb : Odd b) :
    J(-(a:ℤ) | b) = J((b:ℤ) | a) := by
  rw [jacobiSym.neg _ hb]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hb) with hb1 | hb3
  · rw [ZMod.χ₄_nat_one_mod_four hb1,
      jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hb1]
    simp
  · rw [ZMod.χ₄_nat_three_mod_four hb3,
      jacobiSym.quadratic_reciprocity_three_mod_four ha hb3]
    ring

lemma symbol_swap21 {s r : ℕ} (hs : Odd s) (hr : r % 4 = 3)
    (hmod : (r:ℤ) ≡ -21 [ZMOD (s:ℤ)]) :
    J((s:ℤ) | r) = J((s:ℤ) | 3)*J((s:ℤ) | 7) := by
  rw [← neg_odd_reciprocity hr hs]
  have hn : (-(r:ℤ)) % (s:ℤ) = 21 % (s:ℤ) := by
    have h := hmod.neg
    norm_num at h
    exact h
  rw [jacobiSym.mod_left' hn]
  change J(((21:ℕ):ℤ) | s) = _
  rw [jacobiSym.quadratic_reciprocity_one_mod_four (by decide : 21 % 4 = 1) hs]
  exact jacobiSym.mul_right (s:ℤ) 3 7

lemma symbol_swap7 {s r : ℕ} (hs : Odd s) (hr : r % 4 = 1)
    (hmod : (r:ℤ) ≡ -7 [ZMOD (s:ℤ)]) : J((s:ℤ) | r) = J((s:ℤ) | 7) := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' hs hr]
  rw [jacobiSym.mod_left' hmod]
  exact neg_odd_reciprocity (by decide : 7 % 4 = 3) hs

lemma symbol_two_three_mod_eight {r : ℕ} (hr : r % 8 = 3) : J(2 | r) = -1 := by
  have ho : Odd r := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two ho,ZMod.χ₈_nat_eq_if_mod_eight]
  simp [hr,show r%2=1 by omega]

lemma symbol_two_one_mod_eight {r : ℕ} (hr : r % 8 = 1) : J(2 | r) = 1 := by
  have ho : Odd r := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two ho,ZMod.χ₈_nat_eq_if_mod_eight]
  simp [hr,show r%2=1 by omega]

lemma symbol_aux1 {s t r : ℕ} (hs : Odd s) (hs3 : ¬3 ∣ s) (ht : t = 1 ∨ t = 2)
    (hr8 : r % 8 = 3) (hr3 : (r:ℤ) ≡ -((t*s:ℕ):ℤ) [ZMOD 3])
    (hrs : (r:ℤ) ≡ -21 [ZMOD (s:ℤ)]) (hs7 : J((s:ℤ) | 7) = -1) :
    J(-3*((t*s:ℕ):ℤ) | r) = 1 := by
  have hr4 : r%4=3 := by omega
  have hrOdd : Odd r := Nat.odd_iff.mpr (by omega)
  have hsr : J((s:ℤ) | r) = -J((s:ℤ) | 3) := by rw [symbol_swap21 hs hr4 hrs,hs7]; ring
  have hneg3 : J(-3 | r) = J((r:ℤ) | 3) := neg_odd_reciprocity (by decide) hrOdd
  have hr3' : J((r:ℤ) | 3) = -J((t:ℤ) | 3)*J((s:ℤ) | 3) := by
    rw [jacobiSym.mod_left' hr3]
    push_cast
    rw [show -((t:ℤ)*(s:ℤ)) = (-1)*(t:ℤ)*(s:ℤ) by ring]
    rw [jacobiSym.mul_left,jacobiSym.mul_left]
    norm_num
  have htr : J((t:ℤ) | r) = J((t:ℤ) | 3) := by
    rcases ht with rfl | rfl
    · simp
    · norm_num only [Nat.cast_ofNat]
      rw [symbol_two_three_mod_eight hr8]
  have htq : J((t:ℤ) | 3)^2 = 1 := by rcases ht with rfl | rfl <;> norm_num
  have hsq : J((s:ℤ) | 3)^2 = 1 := by
    apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.prime_three.coprime_iff_not_dvd.mpr hs3).symm)
  rw [jacobiSym.mul_left,hneg3,hr3']
  push_cast
  rw [jacobiSym.mul_left,htr,hsr]
  calc
    _ = J((t:ℤ) | 3)^2 * J((s:ℤ) | 3)^2 := by ring
    _ = 1 := by rw [htq,hsq]; norm_num

lemma symbol_aux3 {s t r : ℕ} (hs : Odd s) (ht : t = 1 ∨ t = 2)
    (hr : r.Prime) (hr3 : r ≠ 3) (hr8 : r % 8 = 1)
    (hrs : (r:ℤ) ≡ -7 [ZMOD (s:ℤ)]) (hs7 : J((s:ℤ) | 7) = 1) :
    J(-3*((3*t*s:ℕ):ℤ) | r) = 1 := by
  have hr4 : r%4=1 := by omega
  have hrOdd : Odd r := Nat.odd_iff.mpr (by omega)
  have hsr : J((s:ℤ) | r) = 1 := by rw [symbol_swap7 hs hr4 hrs,hs7]
  have htr : J((t:ℤ) | r) = 1 := by
    rcases ht with rfl | rfl
    · simp
    · exact symbol_two_one_mod_eight hr8
  have hn1 : J(-1 | r) = 1 := by rw [jacobiSym.at_neg_one hrOdd,ZMod.χ₄_nat_one_mod_four hr4]
  have h3q : J((3:ℤ)^2 | r) = 1 := by
    apply jacobiSym.sq_one'
    change Int.gcd ((3:ℕ):ℤ) (r:ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact (hr.coprime_iff_not_dvd.mpr (fun h => hr3 ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hr.ne_one))).symm
  rw [show -3*((3*t*s:ℕ):ℤ) = (-1)*(3:ℤ)^2*(t:ℤ)*(s:ℤ) by push_cast; ring]
  rw [jacobiSym.mul_left,jacobiSym.mul_left,jacobiSym.mul_left,hn1,h3q,htr,hsr]
  norm_num

end Aux306439

/-! ### Extracting and lifting roots -/

set_option maxHeartbeats 0
namespace Aux306439
open scoped NumberTheorySymbols
namespace Form3

lemma symbol_root {p : ℕ} (hp : p.Prime) (b : ℤ) (hb : ¬(p:ℤ) ∣ b)
    (hJ : J(-b | p) = 1) : ∃ r : ℤ, ¬(p:ℤ) ∣ r ∧ (p:ℤ) ∣ r^2+b := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  push_cast at hx
  obtain ⟨r,hr⟩ := ZMod.intCast_surjective x
  have hq : (p:ℤ) ∣ r^2+b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hr]
    linear_combination -hx
  refine ⟨r,?_,hq⟩
  intro h
  have hpow : (p:ℤ) ∣ r^2 := dvd_pow h (by decide : 2 ≠ 0)
  exact hb (by simpa using dvd_sub hq hpow)

lemma roots_of_symbol {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (b : ℤ) (hb : ¬(p:ℤ) ∣ b) (hJ : J(-b | p) = 1) :
    ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ x^2+b := by
  obtain ⟨r,hr,hq⟩ := symbol_root hp b hb hJ
  simpa using quadratic_lift hp hp2 1 b r (Nat.prime_iff_prime_int.mp hp).not_dvd_one hr (by simpa using hq)

lemma roots_three_of_symbol {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (m : ℤ) (hm : ¬(p:ℤ) ∣ 3*m) (hJ : J(-3*m | p) = 1) :
    ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ 3*x^2+9*m := by
  have hJ' : J(-(3*m) | p) = 1 := by simpa only [neg_mul] using hJ
  obtain ⟨r,hr,hq⟩ := symbol_root hp (3*m) hm hJ'
  have h3 : ¬(p:ℤ) ∣ 3 := fun h => hm (dvd_mul_of_dvd_left h m)
  apply quadratic_lift hp hp2 3 (9*m) r h3 hr
  convert dvd_mul_of_dvd_right hq 3 using 1 <;> ring

lemma prime_not_dvd_prime_int {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬(p:ℤ) ∣ (q:ℤ) := by
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (Int.natCast_dvd_natCast.mp h))

lemma one_or_two_not_dvd {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t=1 ∨ t=2) :
    ¬(p:ℤ) ∣ (t:ℤ) := by
  rcases ht with rfl | rfl
  · exact_mod_cast hp.not_dvd_one
  · exact prime_not_dvd_prime_int hp Nat.prime_two hp2

lemma congruence_roots {p s r c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hps : p ∣ s)
    (hc : ¬(p:ℤ) ∣ (c:ℤ)) (hrs : (r:ℤ) ≡ -(c:ℤ) [ZMOD (s:ℤ)]) :
    ∀ k : ℕ, ∃ x : ℤ, (p:ℤ)^k ∣ x^2+(c:ℤ)*r := by
  have hmod := hrs.of_dvd (show (p:ℤ) ∣ (s:ℤ) by exact_mod_cast hps)
  have hsum : (p:ℤ) ∣ (c:ℤ)+(r:ℤ) := by
    have h := dvd_neg.mpr hmod.dvd
    simpa [add_comm] using h
  have hq : (p:ℤ) ∣ (c:ℤ)^2+(c:ℤ)*r := by
    convert dvd_mul_of_dvd_right hsum (c:ℤ) using 1 <;> ring
  simpa using quadratic_lift hp hp2 1 ((c:ℤ)*r) c
    (Nat.prime_iff_prime_int.mp hp).not_dvd_one hc (by simpa using hq)

end Form3
end Aux306439

/-! ### Local isotropy of the auxiliary forms -/

set_option maxHeartbeats 0
namespace Aux306439
open scoped NumberTheorySymbols
namespace Form3

lemma aux1_all_local (s t r : ℕ) (hs : 0 < s) (hs3 : ¬3 ∣ s) (ht : t=1 ∨ t=2)
    (hr : r.Prime) (hr7 : 7 < r) (hmr : t*s < r) (hr8 : r%8=3)
    (hr3 : (r:ℤ) ≡ -((t*s:ℕ):ℤ) [ZMOD 3])
    (hrs : (r:ℤ) ≡ -21 [ZMOD (s:ℤ)]) (hJ : J(-3*((t*s:ℕ):ℤ) | r) = 1) :
    ∀ p : ℕ, p.Prime → p ≠ 7 → (aux1 ((t*s:ℕ):ℤ) r).IsoAt p := by
  intro p hp hp7
  let m := t*s
  have hm : 0 < m := Nat.mul_pos (by omega) hs
  have h3m : ¬(3:ℤ) ∣ (m:ℤ) := by
    have hprime : Prime (3:ℤ) := by norm_num
    simpa [m] using hprime.not_dvd_mul (one_or_two_not_dvd Nat.prime_three (by decide) ht)
      (show ¬(3:ℤ) ∣ (s:ℤ) by exact_mod_cast hs3)
  by_cases hp2 : p = 2
  · subst p
    have hr8' : (r:ℤ)%8=3 := by exact_mod_cast hr8
    have h8 : (8:ℤ) ∣ 1+21*(r:ℤ) := Int.dvd_iff_emod_eq_zero.mpr (by omega)
    convert diagonal_pair13 (m:ℤ) (7*(r:ℤ)) (21*(r:ℤ)) Nat.prime_two
      (two_adic_square _ h8) using 1 <;> apply ext_evalV <;> intro v <;> simp only [aux1, aux3, m, evalV, eval, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  by_cases hp3 : p = 3
  · subst p
    have hq : (3:ℤ) ∣ (m:ℤ)+7*(r:ℤ) := by
      obtain ⟨u,hu⟩ := hr3.dvd
      refine ⟨2*(r:ℤ)-u,?_⟩
      change -(m:ℤ)-(r:ℤ)=3*u at hu
      linarith
    exact diagonal_pair12 _ _ _ Nat.prime_three
      (quadratic_lift Nat.prime_three (by decide) (m:ℤ) (7*(r:ℤ)) 1 h3m
        (by norm_num) (by simpa using hq))
  by_cases hpr : p = r
  · subst p
    have hrm : ¬(r:ℤ) ∣ (m:ℤ) := by exact_mod_cast (Nat.not_dvd_of_pos_of_lt hm hmr)
    have hr3' : ¬(r:ℤ) ∣ (3:ℤ) := by
      exact_mod_cast prime_not_dvd_prime_int hr Nat.prime_three (by omega)
    have hr3m : ¬(r:ℤ) ∣ 3*(m:ℤ) := (Nat.prime_iff_prime_int.mp hr).not_dvd_mul hr3' hrm
    have hJ' : J(-(3*(m:ℤ)) | r) = 1 := by simpa only [neg_mul] using hJ
    convert diagonal_pair23 (m:ℤ) (7*(r:ℤ)) (3*(m:ℤ)) hr
      (roots_of_symbol hr hp2 _ hr3m hJ') using 1 <;> apply ext_evalV <;> intro v <;> simp only [aux1, aux3, m, evalV, eval, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp3' : ¬(p:ℤ) ∣ (3:ℤ) := by exact_mod_cast prime_not_dvd_prime_int hp Nat.prime_three hp3
  have hp7' : ¬(p:ℤ) ∣ (7:ℤ) := by exact_mod_cast prime_not_dvd_prime_int hp (by decide : Nat.Prime 7) hp7
  have hp21 : ¬(p:ℤ) ∣ (21:ℤ) := by simpa using hprime.not_dvd_mul hp3' hp7'
  by_cases hps : p ∣ s
  · have hc : ¬(p:ℤ) ∣ ((21:ℕ):ℤ) := by exact_mod_cast hp21
    convert diagonal_pair13 (m:ℤ) (7*(r:ℤ)) (21*(r:ℤ)) hp
      (congruence_roots hp hp2 hps hc hrs) using 1 <;> apply ext_evalV <;> intro v <;> simp only [aux1, aux3, m, evalV, eval, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  have hpm : ¬(p:ℤ) ∣ (m:ℤ) := by
    simpa [m] using hprime.not_dvd_mul (one_or_two_not_dvd hp hp2 ht)
      (show ¬(p:ℤ) ∣ (s:ℤ) by exact_mod_cast hps)
  have hpr' : ¬(p:ℤ) ∣ (r:ℤ) := prime_not_dvd_prime_int hp hr hpr
  exact diagonal_isoAt hp hp2 _ _ _ hpm (hprime.not_dvd_mul hp7' hpr')
    (hprime.not_dvd_mul (hprime.not_dvd_mul hp21 hpm) hpr')

lemma aux3_all_local (s t r : ℕ) (hs : 0 < s) (hs3 : ¬3 ∣ s) (ht : t=1 ∨ t=2)
    (hr : r.Prime) (hr7 : 7 < r) (hmr : 3*t*s < r) (hr8 : r%8=1)
    (hrs : (r:ℤ) ≡ -7 [ZMOD (s:ℤ)]) (hJ : J(-3*((3*t*s:ℕ):ℤ) | r) = 1) :
    ∀ p : ℕ, p.Prime → p ≠ 7 → (aux3 ((3*t*s:ℕ):ℤ) r).IsoAt p := by
  intro p hp hp7
  let m := 3*t*s
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hs
  by_cases hp2 : p = 2
  · subst p
    have hr8' : (r:ℤ)%8=1 := by exact_mod_cast hr8
    have h8 : (8:ℤ) ∣ 1+7*(r:ℤ) := Int.dvd_iff_emod_eq_zero.mpr (by omega)
    convert diagonal_pair13 (m:ℤ) (21*(r:ℤ)) (7*(r:ℤ)) Nat.prime_two
      (two_adic_square _ h8) using 1 <;> apply ext_evalV <;> intro v <;> simp only [aux1, aux3, m, evalV, eval, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  by_cases hp3 : p = 3
  · subst p
    let E : Form3 ℤ := ⟨((t*s:ℕ):ℤ),7*(r:ℤ),7*((t*s:ℕ):ℤ)*(r:ℤ),0,0,0⟩
    have hprime : Prime (3:ℤ) := by norm_num
    have h3s : ¬(3:ℤ) ∣ (s:ℤ) := by exact_mod_cast hs3
    have h3ts : ¬(3:ℤ) ∣ ((t*s:ℕ):ℤ) := by
      simpa using hprime.not_dvd_mul (one_or_two_not_dvd Nat.prime_three (by decide) ht) h3s
    have h3r : ¬(3:ℤ) ∣ (r:ℤ) := by
      exact_mod_cast prime_not_dvd_prime_int Nat.prime_three hr (by omega)
    have h37 : ¬(3:ℤ) ∣ (7:ℤ) := by norm_num
    have hE : E.IsoAt 3 := diagonal_isoAt Nat.prime_three (by decide) _ _ _ h3ts
      (hprime.not_dvd_mul h37 h3r) (hprime.not_dvd_mul (hprime.not_dvd_mul h37 h3ts) h3r)
    have heq : aux3 ((3*t*s:ℕ):ℤ) r = E.scale 3 := by
      apply ext_evalV
      intro v
      simp [E,aux3,scale,evalV,eval]
      ring
    rw [heq]
    exact isoAt_scale E hE 3
  by_cases hpr : p = r
  · subst p
    have hrm : ¬(r:ℤ) ∣ (m:ℤ) := by exact_mod_cast (Nat.not_dvd_of_pos_of_lt hm hmr)
    have hr3' : ¬(r:ℤ) ∣ (3:ℤ) := by
      exact_mod_cast prime_not_dvd_prime_int hr Nat.prime_three (by omega)
    have hr3m : ¬(r:ℤ) ∣ 3*(m:ℤ) := (Nat.prime_iff_prime_int.mp hr).not_dvd_mul hr3' hrm
    convert diagonal_pair23_three (m:ℤ) (7*(r:ℤ)) (m:ℤ) hr (by omega)
      (roots_three_of_symbol hr hp2 _ hr3m hJ) using 1 <;> apply ext_evalV <;> intro v <;> simp only [aux1, aux3, m, evalV, eval, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp3' : ¬(p:ℤ) ∣ (3:ℤ) := by exact_mod_cast prime_not_dvd_prime_int hp Nat.prime_three hp3
  have hp7' : ¬(p:ℤ) ∣ (7:ℤ) := by exact_mod_cast prime_not_dvd_prime_int hp (by decide : Nat.Prime 7) hp7
  by_cases hps : p ∣ s
  · have hc : ¬(p:ℤ) ∣ ((7:ℕ):ℤ) := by exact_mod_cast hp7'
    convert diagonal_pair13 (m:ℤ) (21*(r:ℤ)) (7*(r:ℤ)) hp
      (congruence_roots hp hp2 hps hc hrs) using 1 <;> apply ext_evalV <;> intro v <;> simp only [aux1, aux3, m, evalV, eval, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  have hpm : ¬(p:ℤ) ∣ (m:ℤ) := by
    simpa [m] using hprime.not_dvd_mul
      (hprime.not_dvd_mul hp3' (one_or_two_not_dvd hp hp2 ht))
      (show ¬(p:ℤ) ∣ (s:ℤ) by exact_mod_cast hps)
  have hpr' : ¬(p:ℤ) ∣ (r:ℤ) := prime_not_dvd_prime_int hp hr hpr
  have hp21 : ¬(p:ℤ) ∣ (21:ℤ) := by simpa using hprime.not_dvd_mul hp3' hp7'
  exact diagonal_isoAt hp hp2 _ _ _ hpm (hprime.not_dvd_mul hp21 hpr')
    (hprime.not_dvd_mul (hprime.not_dvd_mul hp7' hpm) hpr')

end Form3
end Aux306439

/-! ### Construction of the auxiliary primes -/
set_option maxHeartbeats 0
namespace Aux306439
open scoped NumberTheorySymbols

lemma symbol7_nonres (m : ℤ) : J(m | 7) = -1 ↔ Nonres7 m ∧ ¬(7:ℤ) ∣ m := by
  rw [jacobiSym.mod_left m 7]
  unfold Nonres7
  rw [Int.dvd_iff_emod_eq_zero]
  have h0 := Int.emod_nonneg m (by norm_num : (7:ℤ) ≠ 0)
  have h7 := Int.emod_lt_of_pos m (by norm_num : (0:ℤ) < 7)
  interval_cases h : m % 7 <;> norm_num

lemma coprime24 {s : ℕ} (hs : Odd s) (hs3 : ¬3 ∣ s) : Nat.Coprime 24 s := by
  have h2 : Nat.Coprime 2 s := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    rw [Nat.dvd_iff_mod_eq_zero]; have := Nat.odd_iff.mp hs; omega)
  have h3 : Nat.Coprime 3 s := Nat.prime_three.coprime_iff_not_dvd.mpr hs3
  simpa using (h2.pow_left 3).mul_left h3

lemma ternary_case1 (s t : ℕ) (hs : 0 < s) (hso : Odd s) (hs3 : ¬3 ∣ s)
    (ht : t=1 ∨ t=2) (hJ : J(((t*s:ℕ):ℤ) | 7) = -1) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*((t*s:ℕ):ℤ) := by
  have hm := (symbol7_nonres ((t*s:ℕ):ℤ)).mp hJ
  have hs7 : ¬7 ∣ s := by
    intro h
    apply hm.2
    exact_mod_cast dvd_mul_of_dvd_right h t
  have hJs : J((s:ℤ) | 7) = -1 := by
    rcases ht with rfl | rfl
    · simpa using hJ
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left, show J(2 | 7)=1 by norm_num, one_mul] using hJ
  have hm3 : ¬3 ∣ t*s := Nat.prime_three.not_dvd_mul
    (by rcases ht with rfl | rfl <;> norm_num) hs3
  let α : ℕ := if (t*s)%3=1 then 11 else 19
  have hα : α.Coprime 24 := by dsimp [α]; split <;> norm_num
  have hc : Nat.Coprime 21 s := by
    simpa using (Nat.prime_three.coprime_iff_not_dvd.mpr hs3).mul_left
      ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr hs7)
  obtain ⟨r,hrN,hr,hr24,hrs⟩ := prime_two_congruences s α 21 (t*s+7) hs (coprime24 hso hs3) hα hc
  have hr8 : r%8=3 := by
    have h := hr24.of_dvd (by decide : 8 ∣ 24)
    change r%8=α%8 at h
    dsimp [α] at h
    split_ifs at h <;> norm_num at h <;> omega
  have hr3 : (r:ℤ) ≡ -((t*s:ℕ):ℤ) [ZMOD 3] := by
    have h := hr24.of_dvd (by decide : 3 ∣ 24)
    change r%3=α%3 at h
    have hm3' : (t*s)%3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hm3
    have hcst : ((t*s:ℕ):ℤ)%3 = ((t*s)%3:ℕ) := by omega
    have hrst : (r:ℤ)%3 = (r%3:ℕ) := by omega
    change (r:ℤ)%3 = (-((t*s:ℕ):ℤ))%3
    dsimp [α] at h
    split_ifs at h <;> norm_num at h <;> omega
  apply Form3.aux1_suffices _ (r:ℤ) (by exact_mod_cast Nat.mul_pos (by omega : 0<t) hs)
    (by exact_mod_cast hr.pos) hm.1 hm.2
    (Form3.prime_not_dvd_prime_int (p := 7) (by decide) hr (by omega))
  exact Form3.aux1_all_local s t r hs hs3 ht hr (by omega) (by omega) hr8 hr3 hrs
    (symbol_aux1 hso hs3 ht hr8 hr3 hrs hJs)

lemma ternary_case3 (s t : ℕ) (hs : 0 < s) (hso : Odd s) (hs3 : ¬3 ∣ s)
    (ht : t=1 ∨ t=2) (hJ : J(((3*t*s:ℕ):ℤ) | 7) = -1) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*((3*t*s:ℕ):ℤ) := by
  have hm := (symbol7_nonres ((3*t*s:ℕ):ℤ)).mp hJ
  have hs7 : ¬7 ∣ s := by
    intro h
    apply hm.2
    exact_mod_cast dvd_mul_of_dvd_right h (3*t)
  have hJs : J((s:ℤ) | 7) = 1 := by
    rcases ht with rfl | rfl <;>
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left] at hJ <;> linarith
  obtain ⟨r,hrN,hr,hr24,hrs⟩ := prime_two_congruences s 1 7 (3*t*s+7) hs
    (coprime24 hso hs3) (by norm_num) ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr hs7)
  have hr8 : r%8=1 := hr24.of_dvd (by decide : 8 ∣ 24)
  apply Form3.aux3_suffices _ (r:ℤ) (by exact_mod_cast Nat.mul_pos (Nat.mul_pos (by decide) (by omega : 0<t)) hs)
    (by exact_mod_cast hr.pos) hm.1 hm.2
    (Form3.prime_not_dvd_prime_int (p := 7) (by decide) hr (by omega))
  exact Form3.aux3_all_local s t r hs hs3 ht hr (by omega) (by omega) hr8 hrs
    (symbol_aux3 hso ht hr (by omega) hr8 hrs hJs)
end Aux306439

/-! ### The unconditional ternary representation theorem -/
set_option maxHeartbeats 0
namespace Aux306439
open scoped NumberTheorySymbols

lemma split_two {n : ℕ} (hn : 0 < n) (h4 : ¬4 ∣ n) :
    ∃ t s : ℕ, (t=1 ∨ t=2) ∧ 0<s ∧ Odd s ∧ n=t*s := by
  rw [Nat.dvd_iff_mod_eq_zero] at h4
  by_cases ho : n%2=1
  · exact ⟨1,n,Or.inl rfl,hn,Nat.odd_iff.mpr ho,by omega⟩
  · refine ⟨2,n/2,Or.inr rfl,by omega,Nat.odd_iff.mpr (by omega),by omega⟩

lemma ternary_no_squares (m : ℕ) (hm : 0 < m) (h4 : ¬4 ∣ m) (h9 : ¬9 ∣ m)
    (hJ : J((m:ℤ) | 7) = -1) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*(m:ℤ) := by
  by_cases h3 : 3 ∣ m
  · obtain ⟨u,hu⟩ := h3
    have hu0 : 0<u := by omega
    have hu4 : ¬4 ∣ u := fun h => h4 (hu ▸ dvd_mul_of_dvd_right h 3)
    have hu3 : ¬3 ∣ u := by
      rintro ⟨v,hv⟩
      apply h9
      refine ⟨v,?_⟩
      omega
    obtain ⟨t,s,ht,hs,hso,heq⟩ := split_two hu0 hu4
    have hmts : m=3*t*s := by rw [hu,heq]; ring
    have hs3 : ¬3 ∣ s := fun h => hu3 (heq ▸ dvd_mul_of_dvd_right h t)
    rw [hmts] at hJ ⊢
    exact ternary_case3 s t hs hso hs3 ht hJ
  · obtain ⟨t,s,ht,hs,hso,heq⟩ := split_two hm h4
    have hs3 : ¬3 ∣ s := fun h => h3 (heq ▸ dvd_mul_of_dvd_right h t)
    rw [heq] at hJ ⊢
    exact ternary_case1 s t hs hso hs3 ht hJ

lemma ternary_nat (m : ℕ) (hm : 0 < m) (hJ : J((m:ℤ) | 7) = -1) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*(m:ℤ) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h4 : 4 ∣ m
    · obtain ⟨u,hu⟩ := h4
      have hu0 : 0 < u := by omega
      have huJ : J((u:ℤ) | 7) = -1 := by
        rw [hu] at hJ
        simpa only [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left,
          show J(4 | 7) = 1 by norm_num, one_mul] using hJ
      obtain ⟨A,B,C,hrep⟩ := ih u (by omega) hu0 huJ
      refine ⟨2*A,2*B,2*C,?_⟩
      rw [hu]
      push_cast
      linear_combination 4*hrep
    by_cases h9 : 9 ∣ m
    · obtain ⟨u,hu⟩ := h9
      have hu0 : 0 < u := by omega
      have huJ : J((u:ℤ) | 7) = -1 := by
        rw [hu] at hJ
        simpa only [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left,
          show J(9 | 7) = 1 by norm_num, one_mul] using hJ
      obtain ⟨A,B,C,hrep⟩ := ih u (by omega) hu0 huJ
      refine ⟨3*A,3*B,3*C,?_⟩
      rw [hu]
      push_cast
      linear_combination 9*hrep
    exact ternary_no_squares m hm h4 h9 hJ

lemma ternary (m : ℤ) (hm : 0 < m) (hres : Nonres7 m) (h7 : ¬(7:ℤ) ∣ m) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2 = 8*m := by
  lift m to ℕ using hm.le
  exact ternary_nat m (by exact_mod_cast hm) ((symbol7_nonres _).mpr ⟨hres,h7⟩)
end Aux306439

/-! ### Congruence normalization and integral coordinates -/
set_option maxHeartbeats 0
namespace Aux306439

lemma mod_six (n s : ℤ) (h : (s-2*n)%3=0) : (6:ℤ) ∣ 14*n-7*s-3*s^2 := by
  rw [Int.dvd_iff_emod_eq_zero]
  have hs0 := Int.emod_nonneg s (by norm_num : (6:ℤ) ≠ 0)
  have hs6 := Int.emod_lt_of_pos s (by norm_num : (0:ℤ) < 6)
  have hn0 := Int.emod_nonneg n (by norm_num : (6:ℤ) ≠ 0)
  have hn6 := Int.emod_lt_of_pos n (by norm_num : (0:ℤ) < 6)
  have hs3 : s%3=(s%6)%3 := by omega
  have hn3 : n%3=(n%6)%3 := by omega
  have hsq : s^2 % 6 = (s%6)^2 % 6 := Int.ModEq.pow 2 (by simp [Int.ModEq])
  interval_cases hs' : s%6 <;> interval_cases hn' : n%6 <;> norm_num [hs'] at hsq <;> omega

lemma parity_norm (A B C : ℤ) (h : (3*C^2+7*B^2+14*A^2)%8=0) :
    (A-B)%2=0 ∧ ((C-B)%4=0 ∨ (C+B)%4=0) := by
  have hfin : ∀ a b c : Fin 8,
      (3*(c.val:ℤ)^2+7*(b.val:ℤ)^2+14*(a.val:ℤ)^2)%8=0 →
      ((a.val:ℤ)-(b.val:ℤ))%2=0 ∧
      (((c.val:ℤ)-(b.val:ℤ))%4=0 ∨ ((c.val:ℤ)+(b.val:ℤ))%4=0) := by decide
  let a : Fin 8 := ⟨(A%8).toNat, by omega⟩
  let b : Fin 8 := ⟨(B%8).toNat, by omega⟩
  let c : Fin 8 := ⟨(C%8).toNat, by omega⟩
  have ha : (a.val:ℤ)=A%8 := by dsimp [a]; omega
  have hb : (b.val:ℤ)=B%8 := by dsimp [b]; omega
  have hc : (c.val:ℤ)=C%8 := by dsimp [c]; omega
  have hh : (3*(c.val:ℤ)^2+7*(b.val:ℤ)^2+14*(a.val:ℤ)^2)%8=0 := by
    rw [ha,hb,hc]
    have he : (3*C^2+7*B^2+14*A^2) ≡ (3*(C%8)^2+7*(B%8)^2+14*(A%8)^2) [ZMOD 8] :=
      ((Int.ModEq.refl 3).mul (Int.ModEq.pow 2 (by simp [Int.ModEq]))).add
        ((Int.ModEq.refl 7).mul (Int.ModEq.pow 2 (by simp [Int.ModEq]))) |>.add
        ((Int.ModEq.refl 14).mul (Int.ModEq.pow 2 (by simp [Int.ModEq])))
    exact (show (3*(C%8)^2+7*(B%8)^2+14*(A%8)^2)%8 = (3*C^2+7*B^2+14*A^2)%8 from he.symm).trans h
  have := hfin a b c hh
  rw [ha,hb,hc] at this
  omega

lemma normalize_norm (n s m A B C : ℤ) (hm : 6*m=14*n-7*s-3*s^2)
    (hnorm : 3*C^2+7*B^2+14*A^2=8*m) :
    ∃ A B C : ℤ, 3*C^2+7*B^2+14*A^2=8*m ∧
      (7:ℤ) ∣ s-C ∧ (4:ℤ) ∣ C-B ∧ (2:ℤ) ∣ A-B := by
  have h7 : (7:ZMod 7)=0 := by decide
  have hms := congrArg (Int.castRingHom (ZMod 7)) hm
  have hns := congrArg (Int.castRingHom (ZMod 7)) hnorm
  norm_num [map_ofNat,h7] at hms hns
  simp only [h7,zero_mul,add_zero,zero_sub] at hms hns
  have heq : (C:ZMod 7)^2=(s:ZMod 7)^2 := by
    linear_combination (norm := skip) 5*hns + 2*hms
    ring_nf
    simp [show (14:ZMod 7)=0 by decide, show (28:ZMod 7)=0 by decide,
      show (70:ZMod 7)=0 by decide, h7]
  have hsign : (7:ℤ) ∣ s-C ∨ (7:ℤ) ∣ s-(-C) := by
    have hf : ∀ c s : ZMod 7, c^2=s^2 → s-c=0 ∨ s-(-c)=0 := by decide
    rcases hf (C:ZMod 7) (s:ZMod 7) heq with hh | hh
    · left; apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp; simpa using hh
    · right; apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp; simpa using hh
  obtain ⟨C',hC',h7C⟩ : ∃ C' : ℤ, C'^2=C^2 ∧ (7:ℤ) ∣ s-C' := by
    rcases hsign with h | h
    · exact ⟨C,rfl,h⟩
    · exact ⟨-C,by ring,h⟩
  have hnorm' : 3*C'^2+7*B^2+14*A^2=8*m := by rw [hC']; exact hnorm
  have hpar := parity_norm A B C' (by rw [hnorm']; omega)
  rw [← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_emod_eq_zero,
    ← Int.dvd_iff_emod_eq_zero] at hpar
  rcases hpar.2 with hB | hB
  · exact ⟨A,B,C',hnorm',h7C,hB,hpar.1⟩
  · refine ⟨A,-B,C',by nlinarith [hnorm'],h7C,by simpa using hB,?_⟩
    rw [Int.dvd_iff_emod_eq_zero]
    have := Int.dvd_iff_emod_eq_zero.mp hpar.1
    omega

lemma norm_to_coordinates (n s m A B C : ℤ) (hm : 6*m=14*n-7*s-3*s^2)
    (hnorm : 3*C^2+7*B^2+14*A^2=8*m)
    (h7 : (7:ℤ) ∣ s-C) (h4 : (4:ℤ) ∣ C-B) (h2 : (2:ℤ) ∣ A-B) :
    ∃ x y z w : ℤ, x+y+2*z+3*w=s ∧
      3*(x^2+y^2+2*z^2+3*w^2)+s=2*n := by
  obtain ⟨w,hw⟩ := h7
  obtain ⟨u,hu⟩ := h4
  obtain ⟨v,hv⟩ := h2
  refine ⟨v+B+u+w,-v+u+w,u+w,w,by linarith,?_⟩
  have hC : C=B+4*u := by linarith
  have hA : A=B+2*v := by linarith
  have hs : s=B+4*u+7*w := by linarith
  rw [hC,hA] at hnorm
  rw [hs] at hm ⊢
  nlinarith [hnorm,hm]
end Aux306439

-- The original counting definitions.
section

open Nat Finset Set

/--
The generalized pentagonal number $k(3k+1)/2$ for $k \ge 0$.
-/
noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/--
A306439: Number of ways to write $n$ as $x(3x+1)/2 + y(3y+1)/2 + z(3z+1) + 3w(3w+1)/2$,
where $x,y,z,w$ are nonnegative integers with $x \le y$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B

  -- The domain of search is (RangeB x RangeB) x (RangeB x RangeB).
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)

  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    -- The equation is P3(x) + P3(y) + 2*P3(z) + 3*P3(w) = n.
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card


end


/-! ### Nonnegative pentagonal representations -/
set_option maxHeartbeats 0
namespace Aux306439

lemma coords_nonneg (n s x y z w : ℤ) (hs : 0 ≤ s) (hsq : 4*n < s^2+2*s)
    (hsum : x+y+2*z+3*w=s) (hnorm : 3*(x^2+y^2+2*z^2+3*w^2)+s=2*n) :
    0≤x ∧ 0≤y ∧ 0≤z ∧ 0≤w := by
  let a := x^2+y^2+2*z^2+3*w^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsa : 6*a < s^2 := by dsimp [a]; linarith
  have hx : 0 ≤ x := by
    by_contra! h
    have hid : 6*(a-x^2)-(s-x)^2 = 2*(y-z)^2+3*(y-w)^2+6*(z-w)^2 := by rw [←hsum]; dsimp [a]; ring
    have hpos : 0 ≤ 2*(y-z)^2+3*(y-w)^2+6*(z-w)^2 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs h.le, sq_nonneg x]
  have hy : 0 ≤ y := by
    by_contra! h
    have hid : 6*(a-y^2)-(s-y)^2 = 2*(x-z)^2+3*(x-w)^2+6*(z-w)^2 := by rw [←hsum]; dsimp [a]; ring
    have hpos : 0 ≤ 2*(x-z)^2+3*(x-w)^2+6*(z-w)^2 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs h.le, sq_nonneg y]
  have hz : 0 ≤ z := by
    by_contra! h
    have hid : 5*(a-2*z^2)-(s-2*z)^2 = (x-y)^2+3*(x-w)^2+3*(y-w)^2 := by rw [←hsum]; dsimp [a]; ring
    have hpos : 0 ≤ (x-y)^2+3*(x-w)^2+3*(y-w)^2 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs h.le, sq_nonneg z]
  have hw : 0 ≤ w := by
    by_contra! h
    have hid : 4*(a-3*w^2)-(s-3*w)^2 = (x-y)^2+2*(x-z)^2+2*(y-z)^2 := by rw [←hsum]; dsimp [a]; ring
    have hpos : 0 ≤ (x-y)^2+2*(x-z)^2+2*(y-z)^2 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs h.le, sq_nonneg w]
  exact ⟨hx,hy,hz,hw⟩

lemma P3_twice (k : ℕ) : 2*P3 k = k*(3*k+1) := by
  unfold P3
  have h : 2 ∣ k*(3*k+1) := by
    have h' : 2 ∣ k*(k+1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
    convert dvd_add (dvd_mul_right 2 (k*k)) h' using 1 <;> ring
  omega

lemma coords_to_pent (n s : ℕ) (x y z w : ℤ) (hsum : x+y+2*z+3*w=(s:ℤ))
    (hnorm : 3*(x^2+y^2+2*z^2+3*w^2)+(s:ℤ)=2*(n:ℤ))
    (hpos : 0≤x ∧ 0≤y ∧ 0≤z ∧ 0≤w) :
    ∃ x y z w : ℕ, x≤y ∧ n=P3 x+P3 y+2*P3 z+3*P3 w ∧ x+y+2*z+3*w=s := by
  obtain ⟨hx,hy,hz,hw⟩ := hpos
  lift x to ℕ using hx
  lift y to ℕ using hy
  lift z to ℕ using hz
  lift w to ℕ using hw
  have heq : n=P3 x+P3 y+2*P3 z+3*P3 w := by
    have hx' := P3_twice x
    have hy' := P3_twice y
    have hz' := P3_twice z
    have hw' := P3_twice w
    have hsum' : x+y+2*z+3*w=s := by exact_mod_cast hsum
    have hnorm' : 3*(x^2+y^2+2*z^2+3*w^2)+s=2*n := by exact_mod_cast hnorm
    nlinarith
  have hsum' : x+y+2*z+3*w=s := by exact_mod_cast hsum
  by_cases hxy : x≤y
  · exact ⟨x,y,z,w,hxy,heq,hsum'⟩
  · exact ⟨y,x,z,w,by omega,by nlinarith [heq],by omega⟩

lemma pent_of_sum (n s : ℕ) (hs : 0 < s) (hc : ((s:ℤ)-2*(n:ℤ))%3=0)
    (h7 : ¬7 ∣ s) (hlo : 4*(n:ℤ)<(s:ℤ)^2+2*(s:ℤ))
    (hhi : 3*(s:ℤ)^2+7*(s:ℤ)<14*(n:ℤ)) :
    ∃ x y z w : ℕ, x≤y ∧ n=P3 x+P3 y+2*P3 z+3*P3 w ∧ x+y+2*z+3*w=s := by
  obtain ⟨m,hm⟩ := mod_six (n:ℤ) (s:ℤ) hc
  have hm0 : 0 < m := by omega
  have hs7 : (s:ZMod 7) ≠ 0 := by
    intro h
    exact h7 ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hmr : NR7 (m:ZMod 7) ∧ (m:ZMod 7) ≠ 0 := by
    have he := congrArg (Int.castRingHom (ZMod 7)) hm
    norm_num [map_ofNat] at he
    have hf : ∀ m s : ZMod 7, 14*(0:ZMod 7)-7*s-3*s^2=6*m → s≠0 → NR7 m ∧ m≠0 := by
      unfold NR7; decide
    apply hf (m:ZMod 7) (s:ZMod 7) _ hs7
    simpa [show (14:ZMod 7)=0 by decide, show (7:ZMod 7)=0 by decide] using he
  obtain ⟨A,B,C,hn⟩ := ternary m hm0 (nonres7_iff.mpr hmr.1)
    (fun h => hmr.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))
  obtain ⟨A,B,C,hn,hC,hB,hA⟩ := normalize_norm n s m A B C hm.symm hn
  obtain ⟨x,y,z,w,hsum,hnorm⟩ := norm_to_coordinates n s m A B C hm.symm hn hC hB hA
  exact coords_to_pent n s x y z w hsum hnorm
    (coords_nonneg n s x y z w (by omega) hlo hsum hnorm)
end Aux306439

/-! ### Two representations for large n -/
set_option maxHeartbeats 0
namespace Aux306439

lemma two_offsets (b n : ℕ) : ∃ i j : ℕ, i≤8 ∧ j≤8 ∧ i≠j ∧
    (((b+i:ℕ):ℤ)-2*(n:ℤ))%3=0 ∧ ¬7 ∣ b+i ∧
    (((b+j:ℕ):ℤ)-2*(n:ℤ))%3=0 ∧ ¬7 ∣ b+j := by
  have hf : ∀ b : Fin 21, ∀ n : Fin 3, ∃ i j : Fin 9, i≠j ∧
      (((b.val+i.val:ℕ):ℤ)-2*(n.val:ℤ))%3=0 ∧ (b.val+i.val)%7≠0 ∧
      (((b.val+j.val:ℕ):ℤ)-2*(n.val:ℤ))%3=0 ∧ (b.val+j.val)%7≠0 := by decide
  obtain ⟨i,j,hij,hi3,hi7,hj3,hj7⟩ := hf ⟨b%21,by omega⟩ ⟨n%3,by omega⟩
  have hiv := i.isLt
  have hjv := j.isLt
  have hijv : i.val≠j.val := fun h => hij (Fin.ext h)
  dsimp at hi3 hi7 hj3 hj7
  refine ⟨i.val,j.val,by omega,by omega,hijv,by omega,?_,by omega,?_⟩ <;>
    rw [Nat.dvd_iff_mod_eq_zero] <;> omega

lemma sqrt_bounds (n s : ℕ) (hn : 4900≤n) (hslo : 2*Nat.sqrt n+2≤s) (hshi : s≤2*Nat.sqrt n+10) :
    0<s ∧ 4*(n:ℤ)<(s:ℤ)^2+2*(s:ℤ) ∧ 3*(s:ℤ)^2+7*(s:ℤ)<14*(n:ℤ) := by
  let k := Nat.sqrt n
  have hklo : k*k≤n := Nat.sqrt_le n
  have hkhi : n<(k+1)*(k+1) := Nat.lt_succ_sqrt n
  have hk70 : 70≤k := by nlinarith
  have hkl : (k:ℤ)^2≤(n:ℤ) := by exact_mod_cast (show k^2≤n by nlinarith)
  have hkh : (n:ℤ)<((k:ℤ)+1)^2 := by exact_mod_cast (show n<(k+1)^2 by nlinarith)
  have hk : (70:ℤ)≤(k:ℤ) := by exact_mod_cast hk70
  have hl : 2*(k:ℤ)+2≤(s:ℤ) := by exact_mod_cast hslo
  have hh : (s:ℤ)≤2*(k:ℤ)+10 := by exact_mod_cast hshi
  refine ⟨by omega,?_,?_⟩
  · nlinarith [sq_nonneg ((s:ℤ)-(2*(k:ℤ)+2))]
  · have hsq : (s:ℤ)^2≤(2*(k:ℤ)+10)^2 := by nlinarith [sq_nonneg ((2*(k:ℤ)+10)-(s:ℤ))]
    nlinarith [sq_nonneg ((k:ℤ)-70)]

lemma two_large_reps (n : ℕ) (hn : 4900≤n) :
    ∃ x y z w x' y' z' w' : ℕ,
      x≤y ∧ n=P3 x+P3 y+2*P3 z+3*P3 w ∧
      x'≤y' ∧ n=P3 x'+P3 y'+2*P3 z'+3*P3 w' ∧
      ((x,y),(z,w)) ≠ ((x',y'),(z',w')) := by
  obtain ⟨i,j,hi,hj,hij,hi3,hi7,hj3,hj7⟩ := two_offsets (2*Nat.sqrt n+2) n
  have his := sqrt_bounds n (2*Nat.sqrt n+2+i) hn (by omega) (by omega)
  have hjs := sqrt_bounds n (2*Nat.sqrt n+2+j) hn (by omega) (by omega)
  obtain ⟨x,y,z,w,hxy,hnxy,hsxy⟩ := pent_of_sum n _ his.1 hi3 hi7 his.2.1 his.2.2
  obtain ⟨x',y',z',w',hxy',hnxy',hsxy'⟩ := pent_of_sum n _ hjs.1 hj3 hj7 hjs.2.1 hjs.2.2
  refine ⟨x,y,z,w,x',y',z',w',hxy,hnxy,hxy',hnxy',?_⟩
  intro h
  have hx := congrArg (fun p : (ℕ×ℕ)×(ℕ×ℕ) => p.1.1) h
  have hy := congrArg (fun p : (ℕ×ℕ)×(ℕ×ℕ) => p.1.2) h
  have hz := congrArg (fun p : (ℕ×ℕ)×(ℕ×ℕ) => p.2.1) h
  have hw := congrArg (fun p : (ℕ×ℕ)×(ℕ×ℕ) => p.2.2) h
  dsimp at hx hy hz hw
  omega
end Aux306439

/-! ### Counting representations and the small exceptional values -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Aux306439
open Finset

abbrev Tuple4 := (ℕ×ℕ)×(ℕ×ℕ)
def Good (n : ℕ) (p : Tuple4) : Prop := p.1.1≤p.1.2 ∧
  n=P3 p.1.1+P3 p.1.2+2*P3 p.2.1+3*P3 p.2.2
noncomputable instance goodDec (n : ℕ) (p : Tuple4) : Decidable (Good n p) := by unfold Good; infer_instance
noncomputable def repSet (n B : ℕ) : Finset Tuple4 :=
  (((range B).product (range B)).product ((range B).product (range B))).filter (Good n)

lemma le_P3 (k : ℕ) : k≤P3 k := by
  have := P3_twice k
  nlinarith

lemma good_bounds {n : ℕ} {p : Tuple4} (h : Good n p) :
    p.1.1≤n ∧ p.1.2≤n ∧ p.2.1≤n ∧ p.2.2≤n := by
  have := le_P3 p.1.1
  have := le_P3 p.1.2
  have := le_P3 p.2.1
  have := le_P3 p.2.2
  obtain ⟨hxy,heq⟩ := h
  omega

lemma mem_repSet {n B : ℕ} {p : Tuple4} : p ∈ repSet n B ↔
    p.1.1<B ∧ p.1.2<B ∧ p.2.1<B ∧ p.2.2<B ∧ Good n p := by
  have hprod {α β : Type} (s : Finset α) (t : Finset β) (p : α×β) :
      p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := Finset.mem_product
  simp only [repSet,Finset.mem_filter,hprod,Finset.mem_range]
  tauto

lemma mem_repSet_self {n : ℕ} {p : Tuple4} : p ∈ repSet n (n+1) ↔ Good n p := by
  rw [mem_repSet]
  constructor
  · tauto
  · intro h
    obtain ⟨h1,h2,h3,h4⟩ := good_bounds h
    exact ⟨by omega,by omega,by omega,by omega,h⟩

lemma two_good {n : ℕ} {p q : Tuple4} (hp : Good n p) (hq : Good n q) (hne : p≠q) : 2≤a n := by
  change 2≤(repSet n (n+1)).card
  have hsub : ({p,q} : Finset Tuple4) ⊆ repSet n (n+1) := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact mem_repSet_self.mpr (by assumption)
  have := card_le_card hsub
  simpa [hne] using this

lemma count_large (n : ℕ) (hn : 4900≤n) : 2≤a n := by
  obtain ⟨x,y,z,w,x',y',z',w',hxy,heq,hxy',heq',hne⟩ := two_large_reps n hn
  exact two_good ⟨hxy,heq⟩ ⟨hxy',heq'⟩ hne

lemma P3_small {k : ℕ} (hk : P3 k≤41) : k<6 := by
  have := P3_twice k
  nlinarith

lemma small_repSet (n : ℕ) (hn : n≤41) : a n=(repSet n 6).card := by
  change (repSet n (n+1)).card=(repSet n 6).card
  congr 1
  ext p
  rw [mem_repSet_self,mem_repSet]
  constructor
  · intro h
    have heq := h.2
    have h1 : P3 p.1.1≤41 := by omega
    have h2 : P3 p.1.2≤41 := by omega
    have h3 : P3 p.2.1≤41 := by omega
    have h4 : P3 p.2.2≤41 := by omega
    exact ⟨P3_small h1,P3_small h2,P3_small h3,P3_small h4,h⟩
  · tauto

lemma count_small : ∀ n : Fin 42,
    ((repSet n.val 6).card=1 ↔ n.val ∈ ({0,2,7,9,11,12,16,31,33,41} : Set ℕ)) ∧
    (5<n.val → 0<(repSet n.val 6).card) := by
  decide
end Aux306439

/-! ### Explicit certificates for 42 ≤ n < 4900 -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Aux306439

lemma cert_42 (n : ℕ) (hlo : 42≤n) (hhi : n<142) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(2,2)),((1,3),(1,2))),
    (((0,2),(3,1)),((2,3),(0,2))),
    (((0,5),(1,0)),((1,2),(2,2))),
    (((0,0),(0,3)),((0,3),(3,0))),
    (((0,4),(2,1)),((0,5),(0,1))),
    (((0,1),(0,3)),((0,4),(0,2))),
    (((1,4),(2,1)),((1,5),(0,1))),
    (((0,0),(1,3)),((1,1),(0,3))),
    (((0,3),(2,2)),((0,5),(1,1))),
    (((0,0),(3,2)),((0,1),(1,3))),
    (((0,0),(4,0)),((0,2),(0,3))),
    (((0,1),(3,2)),((1,1),(1,3))),
    (((0,1),(4,0)),((0,5),(2,0))),
    (((1,1),(3,2)),((3,3),(1,2))),
    (((0,2),(1,3)),((0,4),(3,0))),
    (((0,6),(0,0)),((2,3),(2,2))),
    (((0,0),(4,1)),((0,2),(3,2))),
    (((0,0),(2,3)),((0,2),(4,0))),
    (((0,1),(4,1)),((0,3),(0,3))),
    (((0,1),(2,3)),((0,4),(2,2))),
    (((0,4),(3,1)),((1,1),(4,1))),
    (((0,6),(0,1)),((1,1),(2,3))),
    (((0,3),(1,3)),((1,4),(3,1))),
    (((0,2),(4,1)),((0,5),(1,2))),
    (((0,2),(2,3)),((0,3),(3,2))),
    (((0,3),(4,0)),((0,6),(1,1))),
    (((1,2),(2,3)),((1,3),(3,2))),
    (((1,3),(4,0)),((1,6),(1,1))),
    (((0,5),(3,0)),((2,6),(0,1))),
    (((0,4),(0,3)),((0,6),(2,0))),
    (((1,5),(3,0)),((2,2),(4,1))),
    (((0,0),(4,2)),((0,3),(4,1))),
    (((0,3),(2,3)),((2,3),(4,0))),
    (((0,0),(3,3)),((0,1),(4,2))),
    (((0,5),(3,1)),((1,3),(2,3))),
    (((0,1),(3,3)),((0,4),(3,2))),
    (((0,0),(0,4)),((0,4),(4,0))),
    (((1,1),(3,3)),((1,4),(3,2))),
    (((0,0),(5,0)),((0,1),(0,4))),
    (((0,7),(1,0)),((2,3),(2,3))),
    (((0,0),(1,4)),((0,1),(5,0))),
    (((0,7),(0,1)),((1,7),(1,0))),
    (((0,1),(1,4)),((0,4),(4,1))),
    (((0,2),(0,4)),((0,4),(2,3))),
    (((0,0),(5,1)),((1,1),(1,4))),
    (((0,2),(5,0)),((0,6),(3,0))),
    (((0,1),(5,1)),((0,3),(4,2))),
    (((0,2),(1,4)),((0,5),(1,3))),
    (((0,3),(3,3)),((1,1),(5,1))),
    (((0,5),(3,2)),((0,7),(2,0))),
    (((0,0),(2,4)),((0,5),(4,0))),
    (((0,2),(5,1)),((0,3),(0,4))),
    (((0,1),(2,4)),((1,5),(4,0))),
    (((0,3),(5,0)),((1,2),(5,1))),
    (((1,1),(2,4)),((2,2),(1,4))),
    (((0,0),(4,3)),((0,3),(1,4))),
    (((0,5),(4,1)),((0,7),(0,2))),
    (((0,1),(4,3)),((0,2),(2,4))),
    (((0,8),(0,0)),((1,5),(4,1))),
    (((0,0),(5,2)),((0,3),(5,1))),
    (((0,6),(0,3)),((0,7),(1,2))),
    (((0,1),(5,2)),((1,3),(5,1))),
    (((0,2),(4,3)),((0,4),(0,4))),
    (((1,1),(5,2)),((2,5),(4,1))),
    (((0,4),(5,0)),((0,6),(1,3))),
    (((0,3),(2,4)),((0,7),(3,0))),
    (((0,0),(3,4)),((0,2),(5,2))),
    (((0,6),(4,0)),((1,3),(2,4))),
    (((0,1),(3,4)),((0,8),(1,1))),
    (((1,6),(4,0)),((2,2),(4,3))),
    (((0,3),(4,3)),((0,4),(5,1))),
    (((0,5),(4,2)),((0,7),(3,1))),
    (((0,0),(6,0)),((0,8),(2,0))),
    (((0,2),(3,4)),((0,5),(3,3))),
    (((0,1),(6,0)),((0,3),(5,2))),
    (((1,2),(3,4)),((1,5),(3,3))),
    (((0,4),(2,4)),((0,5),(0,4))),
    (((2,3),(4,3)),((2,4),(5,1))),
    (((0,0),(0,5)),((0,0),(6,1))),
    (((0,2),(6,0)),((0,8),(0,2))),
    (((0,1),(0,5)),((0,1),(6,1))),
    (((0,3),(3,4)),((0,4),(4,3))),
    (((0,0),(1,5)),((1,1),(0,5))),
    (((0,0),(5,3)),((0,8),(1,2))),
    (((0,1),(1,5)),((0,5),(5,1))),
    (((0,1),(5,3)),((0,2),(0,5))),
    (((0,7),(3,2)),((1,1),(1,5))),
    (((0,3),(6,0)),((0,7),(4,0))),
    (((0,0),(4,4)),((0,6),(4,2))),
    (((0,2),(1,5)),((1,3),(6,0))),
    (((0,1),(4,4)),((0,2),(5,3))),
    (((1,2),(1,5)),((2,5),(5,1))),
    (((0,0),(2,5)),((0,4),(3,4))),
    (((0,0),(6,2)),((0,3),(0,5))),
    (((0,1),(2,5)),((0,7),(2,3))),
    (((0,1),(6,2)),((0,2),(4,4))),
    (((1,1),(2,5)),((1,7),(2,3))),
    (((0,3),(1,5)),((0,6),(1,4))),
    (((0,3),(5,3)),((0,4),(6,0))),
    (((0,2),(2,5)),((0,5),(5,2)))]
  have hc : ∀ i : Fin 100, Good (42+i.val) (c i).1 ∧
      Good (42+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-42,by omega⟩
  have he : 42+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_142 (n : ℕ) (hlo : 142≤n) (hhi : n<242) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(6,2)),((1,3),(5,3))),
    (((0,6),(5,1)),((1,2),(2,5))),
    (((1,2),(6,2)),((2,2),(4,4))),
    (((0,3),(4,4)),((0,8),(0,3))),
    (((0,4),(0,5)),((0,4),(6,1))),
    (((0,9),(0,2)),((1,3),(4,4))),
    (((0,5),(3,4)),((1,4),(0,5))),
    (((0,3),(2,5)),((0,6),(2,4))),
    (((0,0),(3,5)),((0,3),(6,2))),
    (((0,4),(5,3)),((0,8),(3,2))),
    (((0,1),(3,5)),((0,7),(3,3))),
    (((1,4),(5,3)),((1,8),(3,2))),
    (((0,0),(7,0)),((0,5),(6,0))),
    (((0,7),(0,4)),((0,10),(0,0))),
    (((0,1),(7,0)),((0,4),(4,4))),
    (((0,2),(3,5)),((0,7),(5,0))),
    (((0,0),(5,4)),((0,6),(5,2))),
    (((0,0),(6,3)),((0,7),(1,4))),
    (((0,0),(7,1)),((0,1),(5,4))),
    (((0,1),(6,3)),((0,2),(7,0))),
    (((0,1),(7,1)),((0,9),(3,1))),
    (((0,7),(5,1)),((1,1),(6,3))),
    (((0,5),(1,5)),((1,1),(7,1))),
    (((0,2),(5,4)),((0,3),(3,5))),
    (((0,2),(6,3)),((1,5),(1,5))),
    (((0,2),(7,1)),((1,2),(5,4))),
    (((1,2),(6,3)),((2,2),(7,0))),
    (((0,3),(7,0)),((0,7),(2,4))),
    (((0,5),(4,4)),((2,7),(5,1))),
    (((0,0),(0,6)),((0,6),(6,0))),
    (((0,0),(4,5)),((1,5),(4,4))),
    (((0,1),(0,6)),((0,3),(5,4))),
    (((0,1),(4,5)),((0,3),(6,3))),
    (((0,0),(1,6)),((0,0),(7,2))),
    (((0,4),(3,5)),((0,10),(0,2))),
    (((0,1),(1,6)),((0,1),(7,2))),
    (((0,2),(0,6)),((0,7),(5,2))),
    (((0,2),(4,5)),((1,1),(1,6))),
    (((0,4),(7,0)),((0,8),(5,0))),
    (((0,6),(1,5)),((1,2),(4,5))),
    (((0,2),(1,6)),((0,2),(7,2))),
    (((1,6),(1,5)),((2,4),(3,5))),
    (((0,4),(5,4)),((0,9),(4,1))),
    (((0,0),(2,6)),((0,4),(6,3))),
    (((0,3),(0,6)),((0,4),(7,1))),
    (((0,1),(2,6)),((0,3),(4,5))),
    (((1,3),(0,6)),((1,4),(7,1))),
    (((1,1),(2,6)),((1,3),(4,5))),
    (((0,3),(1,6)),((0,3),(7,2))),
    (((0,6),(2,5)),((0,7),(6,0))),
    (((0,0),(6,4)),((0,2),(2,6))),
    (((0,11),(0,1)),((1,6),(2,5))),
    (((0,1),(6,4)),((0,5),(7,0))),
    (((1,11),(0,1)),((3,4),(7,0))),
    (((1,1),(6,4)),((1,5),(7,0))),
    (((0,4),(0,6)),((0,7),(0,5))),
    (((0,4),(4,5)),((0,5),(5,4))),
    (((0,0),(7,3)),((0,2),(6,4))),
    (((0,0),(5,5)),((0,0),(8,0))),
    (((0,0),(3,6)),((0,1),(7,3))),
    (((0,1),(5,5)),((0,1),(8,0))),
    (((0,1),(3,6)),((1,1),(7,3))),
    (((0,9),(0,4)),((0,10),(1,3))),
    (((1,1),(3,6)),((2,4),(4,5))),
    (((0,0),(8,1)),((0,2),(7,3))),
    (((0,2),(5,5)),((0,2),(8,0))),
    (((0,1),(8,1)),((0,2),(3,6))),
    (((1,2),(5,5)),((1,2),(8,0))),
    (((1,1),(8,1)),((1,2),(3,6))),
    (((0,4),(2,6)),((0,5),(0,6))),
    (((0,5),(4,5)),((0,7),(6,2))),
    (((0,2),(8,1)),((0,10),(4,1))),
    (((0,3),(7,3)),((0,8),(6,0))),
    (((0,3),(5,5)),((0,3),(8,0))),
    (((0,3),(3,6)),((0,6),(6,3))),
    (((0,6),(7,1)),((0,11),(3,0))),
    (((0,4),(6,4)),((0,9),(2,4))),
    (((1,6),(7,1)),((1,11),(3,0))),
    (((0,8),(0,5)),((0,8),(6,1))),
    (((0,0),(8,2)),((0,3),(8,1))),
    (((0,11),(2,2)),((0,12),(0,0))),
    (((0,0),(4,6)),((0,1),(8,2))),
    (((0,8),(1,5)),((1,11),(2,2))),
    (((0,1),(4,6)),((0,4),(7,3))),
    (((0,4),(5,5)),((0,4),(8,0))),
    (((0,4),(3,6)),((0,7),(3,5))),
    (((0,2),(8,2)),((0,6),(0,6))),
    (((0,6),(4,5)),((1,4),(3,6))),
    (((0,2),(4,6)),((0,8),(4,4))),
    (((0,0),(0,7)),((0,7),(7,0))),
    (((0,0),(7,4)),((0,4),(8,1))),
    (((0,1),(0,7)),((0,10),(0,4))),
    (((0,0),(6,5)),((0,1),(7,4))),
    (((0,0),(1,7)),((0,7),(5,4))),
    (((0,1),(6,5)),((0,3),(8,2))),
    (((0,1),(1,7)),((0,7),(7,1))),
    (((0,2),(0,7)),((0,3),(4,6))),
    (((0,2),(7,4)),((0,5),(7,3))),
    (((0,5),(5,5)),((0,5),(8,0))),
    (((0,2),(6,5)),((0,5),(3,6)))]
  have hc : ∀ i : Fin 100, Good (142+i.val) (c i).1 ∧
      Good (142+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-142,by omega⟩
  have he : 142+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_242 (n : ℕ) (hlo : 242≤n) (hhi : n<342) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(1,7)),((0,6),(2,6))),
    (((0,12),(0,2)),((1,2),(6,5))),
    (((1,2),(1,7)),((1,6),(2,6))),
    (((0,0),(2,7)),((0,0),(8,3))),
    (((0,3),(0,7)),((0,5),(8,1))),
    (((0,1),(2,7)),((0,1),(8,3))),
    (((0,7),(0,6)),((1,3),(0,7))),
    (((0,3),(6,5)),((0,4),(4,6))),
    (((0,3),(1,7)),((0,8),(3,5))),
    (((0,0),(5,6)),((0,9),(5,3))),
    (((0,0),(9,0)),((0,2),(2,7))),
    (((0,1),(5,6)),((1,9),(5,3))),
    (((0,1),(9,0)),((0,8),(7,0))),
    (((1,1),(5,6)),((2,7),(0,6))),
    (((0,6),(7,3)),((0,9),(4,4))),
    (((0,4),(0,7)),((0,6),(5,5))),
    (((0,0),(9,1)),((0,2),(5,6))),
    (((0,2),(9,0)),((0,8),(6,3))),
    (((0,1),(9,1)),((0,3),(2,7))),
    (((0,0),(3,7)),((0,4),(1,7))),
    (((0,7),(2,6)),((0,11),(3,3))),
    (((0,1),(3,7)),((0,5),(4,6))),
    (((0,13),(1,0)),((1,7),(2,6))),
    (((0,2),(9,1)),((0,11),(0,4))),
    (((0,3),(5,6)),((0,13),(0,1))),
    (((0,3),(9,0)),((0,11),(5,0))),
    (((0,2),(3,7)),((1,3),(5,6))),
    (((0,7),(6,4)),((0,10),(6,0))),
    (((0,13),(1,1)),((1,2),(3,7))),
    (((0,4),(2,7)),((0,4),(8,3))),
    (((0,5),(7,4)),((0,8),(4,5))),
    (((0,0),(9,2)),((0,3),(9,1))),
    (((0,0),(7,5)),((0,5),(6,5))),
    (((0,1),(9,2)),((0,5),(1,7))),
    (((0,1),(7,5)),((0,3),(3,7))),
    (((0,4),(5,6)),((0,7),(5,5))),
    (((0,0),(8,4)),((0,4),(9,0))),
    (((0,10),(1,5)),((0,11),(2,4))),
    (((0,1),(8,4)),((0,2),(9,2))),
    (((0,2),(7,5)),((0,12),(2,3))),
    (((1,1),(8,4)),((1,2),(9,2))),
    (((0,0),(4,7)),((0,7),(8,1))),
    (((0,4),(9,1)),((0,9),(5,4))),
    (((0,0),(6,6)),((0,1),(4,7))),
    (((0,9),(7,1)),((1,4),(9,1))),
    (((0,1),(6,6)),((0,4),(3,7))),
    (((0,3),(9,2)),((0,6),(0,7))),
    (((0,3),(7,5)),((0,6),(7,4))),
    (((0,2),(4,7)),((0,10),(6,2))),
    (((0,5),(5,6)),((0,6),(6,5))),
    (((0,2),(6,6)),((0,5),(9,0))),
    (((0,3),(8,4)),((1,5),(5,6))),
    (((1,2),(6,6)),((1,5),(9,0))),
    (((0,11),(3,4)),((0,12),(4,2))),
    (((0,13),(3,1)),((2,3),(7,5))),
    (((0,0),(9,3)),((0,9),(0,6))),
    (((0,3),(4,7)),((0,5),(9,1))),
    (((0,1),(9,3)),((0,4),(9,2))),
    (((0,0),(0,8)),((0,3),(6,6))),
    (((0,5),(3,7)),((0,8),(3,6))),
    (((0,1),(0,8)),((0,6),(2,7))),
    (((1,5),(3,7)),((1,8),(3,6))),
    (((0,0),(1,8)),((0,2),(9,3))),
    (((0,10),(3,5)),((0,13),(0,3))),
    (((0,1),(1,8)),((0,8),(8,1))),
    (((0,2),(0,8)),((0,11),(0,5))),
    (((0,6),(5,6)),((0,7),(0,7))),
    (((0,4),(4,7)),((0,6),(9,0))),
    (((0,0),(10,0)),((1,6),(5,6))),
    (((0,0),(5,7)),((0,2),(1,8))),
    (((0,1),(10,0)),((0,3),(9,3))),
    (((0,1),(5,7)),((0,5),(9,2))),
    (((0,0),(2,8)),((0,5),(7,5))),
    (((0,3),(0,8)),((0,6),(9,1))),
    (((0,0),(10,1)),((0,1),(2,8))),
    (((0,2),(10,0)),((0,11),(4,4))),
    (((0,1),(10,1)),((0,2),(5,7))),
    (((0,3),(1,8)),((0,12),(4,3))),
    (((0,0),(8,5)),((1,1),(10,1))),
    (((0,2),(2,8)),((0,8),(8,2))),
    (((0,1),(8,5)),((0,7),(2,7))),
    (((0,2),(10,1)),((0,4),(9,3))),
    (((1,1),(8,5)),((1,7),(2,7))),
    (((0,0),(7,6)),((0,3),(10,0))),
    (((0,3),(5,7)),((0,4),(0,8))),
    (((0,1),(7,6)),((0,2),(8,5))),
    (((0,7),(5,6)),((1,3),(5,7))),
    (((0,3),(2,8)),((0,7),(9,0))),
    (((0,0),(3,8)),((0,0),(9,4))),
    (((0,0),(10,2)),((0,3),(10,1))),
    (((0,1),(3,8)),((0,1),(9,4))),
    (((0,1),(10,2)),((0,13),(4,2))),
    (((0,8),(6,5)),((1,1),(3,8))),
    (((0,3),(8,5)),((0,6),(8,4))),
    (((0,4),(10,0)),((0,12),(6,0))),
    (((0,2),(3,8)),((0,2),(9,4))),
    (((0,2),(10,2)),((0,7),(3,7))),
    (((1,2),(3,8)),((1,2),(9,4))),
    (((0,3),(7,6)),((0,4),(2,8))),
    (((0,11),(7,0)),((2,8),(6,5)))]
  have hc : ∀ i : Fin 100, Good (242+i.val) (c i).1 ∧
      Good (242+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-242,by omega⟩
  have he : 242+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_342 (n : ℕ) (hlo : 342≤n) (hhi : n<442) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,4),(10,1)),((0,6),(6,6))),
    (((1,11),(7,0)),((2,4),(10,0))),
    (((0,5),(1,8)),((1,4),(10,1))),
    (((0,0),(6,7)),((0,3),(3,8))),
    (((0,3),(10,2)),((0,4),(8,5))),
    (((0,1),(6,7)),((0,9),(8,2))),
    (((1,3),(10,2)),((1,4),(8,5))),
    (((0,9),(4,6)),((0,15),(1,0))),
    (((0,5),(10,0)),((0,7),(9,2))),
    (((0,4),(7,6)),((0,5),(5,7))),
    (((0,0),(4,8)),((0,2),(6,7))),
    (((0,14),(4,0)),((1,4),(7,6))),
    (((0,1),(4,8)),((0,5),(2,8))),
    (((0,0),(10,3)),((0,7),(8,4))),
    (((0,4),(3,8)),((0,4),(9,4))),
    (((0,1),(10,3)),((0,4),(10,2))),
    (((0,8),(9,1)),((0,9),(7,4))),
    (((0,2),(4,8)),((0,11),(4,5))),
    (((0,3),(6,7)),((0,5),(8,5))),
    (((0,6),(1,8)),((0,8),(3,7))),
    (((0,2),(10,3)),((0,7),(6,6))),
    (((1,6),(1,8)),((1,8),(3,7))),
    (((1,2),(10,3)),((1,7),(6,6))),
    (((0,5),(7,6)),((0,15),(2,1))),
    (((0,15),(0,2)),((2,2),(4,8))),
    (((0,3),(4,8)),((0,6),(10,0))),
    (((0,6),(5,7)),((0,13),(3,4))),
    (((1,3),(4,8)),((1,6),(10,0))),
    (((0,3),(10,3)),((0,5),(3,8))),
    (((0,0),(8,6)),((0,4),(6,7))),
    (((0,0),(9,5)),((0,11),(2,6))),
    (((0,1),(8,6)),((0,6),(10,1))),
    (((0,0),(11,0)),((0,1),(9,5))),
    (((0,15),(3,0)),((1,1),(8,6))),
    (((0,1),(11,0)),((0,10),(8,2))),
    (((0,6),(8,5)),((0,7),(0,8))),
    (((0,0),(0,9)),((0,2),(8,6))),
    (((0,2),(9,5)),((0,11),(6,4))),
    (((0,0),(5,8)),((0,0),(11,1))),
    (((0,2),(11,0)),((0,4),(10,3))),
    (((0,0),(1,9)),((0,1),(5,8))),
    (((0,8),(4,7)),((0,14),(1,4))),
    (((0,1),(1,9)),((0,9),(9,1))),
    (((0,0),(7,7)),((0,2),(0,9))),
    (((0,3),(8,6)),((0,10),(0,7))),
    (((0,1),(7,7)),((0,2),(5,8))),
    (((0,0),(10,4)),((0,6),(10,2))),
    (((0,2),(1,9)),((0,3),(11,0))),
    (((0,1),(10,4)),((0,10),(1,7))),
    (((0,7),(2,8)),((1,2),(1,9))),
    (((0,0),(2,9)),((0,2),(7,7))),
    (((0,3),(0,9)),((0,7),(10,1))),
    (((0,1),(2,9)),((0,12),(4,5))),
    (((0,0),(11,2)),((0,2),(10,4))),
    (((0,15),(3,2)),((0,16),(1,0))),
    (((0,1),(11,2)),((0,3),(1,9))),
    (((0,4),(9,5)),((0,14),(4,3))),
    (((0,2),(2,9)),((0,9),(9,2))),
    (((0,3),(7,7)),((0,4),(11,0))),
    (((1,2),(2,9)),((1,9),(9,2))),
    (((0,2),(11,2)),((0,6),(6,7))),
    (((0,3),(10,4)),((0,15),(4,1))),
    (((0,4),(0,9)),((0,8),(1,8))),
    (((1,3),(10,4)),((1,15),(4,1))),
    (((0,4),(5,8)),((0,4),(11,1))),
    (((0,3),(2,9)),((0,7),(3,8))),
    (((0,0),(3,9)),((0,4),(1,9))),
    (((0,6),(4,8)),((0,9),(4,7))),
    (((0,1),(3,9)),((0,3),(11,2))),
    (((0,4),(7,7)),((0,5),(8,6))),
    (((0,5),(9,5)),((0,6),(10,3))),
    (((0,10),(9,1)),((0,16),(0,2))),
    (((0,0),(6,8)),((0,4),(10,4))),
    (((0,2),(3,9)),((0,14),(6,0))),
    (((0,1),(6,8)),((0,8),(10,1))),
    (((0,16),(1,2)),((1,2),(3,9))),
    (((0,4),(2,9)),((0,5),(0,9))),
    (((0,0),(11,3)),((0,11),(7,4))),
    (((0,5),(5,8)),((0,5),(11,1))),
    (((0,1),(11,3)),((0,2),(6,8))),
    (((0,5),(1,9)),((0,7),(6,7))),
    (((0,0),(9,6)),((0,3),(3,9))),
    (((1,5),(1,9)),((1,7),(6,7))),
    (((0,1),(9,6)),((0,5),(7,7))),
    (((0,2),(11,3)),((0,9),(0,8))),
    (((0,15),(1,4)),((0,16),(2,2))),
    (((0,5),(10,4)),((0,6),(8,6))),
    (((0,3),(6,8)),((0,6),(9,5))),
    (((0,0),(4,9)),((0,0),(10,5))),
    (((0,0),(8,7)),((0,6),(11,0))),
    (((0,1),(4,9)),((0,1),(10,5))),
    (((0,1),(8,7)),((0,10),(8,4))),
    (((0,3),(11,3)),((0,4),(3,9))),
    (((0,5),(11,2)),((0,6),(0,9))),
    (((0,9),(10,0)),((0,14),(6,2))),
    (((0,2),(4,9)),((0,2),(10,5))),
    (((0,2),(8,7)),((0,3),(9,6))),
    (((0,6),(1,9)),((0,11),(9,0))),
    (((0,4),(6,8)),((0,9),(2,8))),
    (((0,16),(1,3)),((1,6),(1,9)))]
  have hc : ∀ i : Fin 100, Good (342+i.val) (c i).1 ∧
      Good (342+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-342,by omega⟩
  have he : 342+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_442 (n : ℕ) (hlo : 442≤n) (hhi : n<542) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,6),(7,7)),((0,9),(10,1))),
    (((0,12),(8,2)),((0,16),(3,2))),
    (((0,0),(12,0)),((0,16),(4,0))),
    (((0,3),(4,9)),((0,3),(10,5))),
    (((0,1),(12,0)),((0,3),(8,7))),
    (((1,3),(4,9)),((1,3),(10,5))),
    (((0,5),(3,9)),((0,7),(8,6))),
    (((0,4),(9,6)),((0,6),(2,9))),
    (((0,0),(12,1)),((0,16),(4,1))),
    (((0,2),(12,0)),((0,7),(11,0))),
    (((0,0),(11,4)),((0,1),(12,1))),
    (((0,12),(0,7)),((0,15),(3,4))),
    (((0,0),(7,8)),((0,1),(11,4))),
    (((0,7),(0,9)),((0,8),(10,3))),
    (((0,1),(7,8)),((0,4),(4,9))),
    (((0,2),(12,1)),((0,4),(8,7))),
    (((0,0),(5,9)),((1,1),(7,8))),
    (((0,2),(11,4)),((0,3),(12,0))),
    (((0,1),(5,9)),((0,11),(9,2))),
    (((0,2),(7,8)),((0,11),(7,5))),
    (((0,7),(7,7)),((0,17),(2,1))),
    (((0,5),(9,6)),((0,17),(0,2))),
    (((1,7),(7,7)),((1,17),(2,1))),
    (((0,0),(0,10)),((0,0),(12,2))),
    (((0,10),(5,7)),((0,13),(8,1))),
    (((0,1),(0,10)),((0,1),(12,2))),
    (((1,10),(5,7)),((1,13),(8,1))),
    (((0,0),(1,10)),((0,3),(7,8))),
    (((0,4),(12,0)),((0,5),(4,9))),
    (((0,1),(1,10)),((0,5),(8,7))),
    (((0,2),(0,10)),((0,2),(12,2))),
    (((0,3),(5,9)),((0,12),(5,6))),
    (((0,8),(11,0)),((0,12),(9,0))),
    (((0,10),(8,5)),((0,15),(4,4))),
    (((0,2),(1,10)),((0,4),(12,1))),
    (((0,17),(2,2)),((1,10),(8,5))),
    (((0,4),(11,4)),((0,8),(0,9))),
    (((0,0),(2,10)),((0,15),(2,5))),
    (((0,3),(0,10)),((0,3),(12,2))),
    (((0,0),(10,6)),((0,1),(2,10))),
    (((0,8),(1,9)),((1,3),(0,10))),
    (((0,0),(9,7)),((0,1),(10,6))),
    (((0,3),(1,10)),((0,4),(5,9))),
    (((0,1),(9,7)),((0,7),(3,9))),
    (((0,2),(2,10)),((0,10),(10,2))),
    (((0,6),(4,9)),((0,6),(10,5))),
    (((0,2),(10,6)),((0,6),(8,7))),
    (((0,0),(12,3)),((0,16),(4,3))),
    (((0,2),(9,7)),((0,5),(12,1))),
    (((0,1),(12,3)),((0,4),(0,10))),
    (((0,0),(6,9)),((0,5),(11,4))),
    (((0,14),(6,4)),((0,16),(5,2))),
    (((0,0),(11,5)),((0,1),(6,9))),
    (((0,0),(3,10)),((0,4),(1,10))),
    (((0,1),(11,5)),((0,2),(12,3))),
    (((0,1),(3,10)),((0,9),(8,6))),
    (((0,3),(9,7)),((0,5),(5,9))),
    (((0,2),(6,9)),((0,15),(7,0))),
    (((0,0),(8,8)),((0,7),(9,6))),
    (((0,2),(11,5)),((0,6),(12,0))),
    (((0,1),(8,8)),((0,2),(3,10))),
    (((0,11),(10,1)),((0,15),(5,4))),
    (((0,3),(12,3)),((0,9),(0,9))),
    (((0,4),(2,10)),((0,5),(0,10))),
    (((0,9),(5,8)),((0,9),(11,1))),
    (((0,2),(8,8)),((0,3),(6,9))),
    (((0,7),(8,7)),((0,8),(3,9))),
    (((0,3),(11,5)),((0,4),(9,7))),
    (((0,3),(3,10)),((0,10),(10,3))),
    (((0,6),(7,8)),((0,9),(7,7))),
    (((0,11),(7,6)),((0,13),(9,0))),
    (((1,6),(7,8)),((1,9),(7,7))),
    (((0,8),(6,8)),((0,9),(10,4))),
    (((0,3),(8,8)),((0,4),(12,3))),
    (((0,15),(0,6)),((0,16),(1,5))),
    (((0,0),(4,10)),((0,11),(3,8))),
    (((0,4),(6,9)),((0,9),(2,9))),
    (((0,1),(4,10)),((0,5),(2,10))),
    (((0,0),(13,0)),((0,4),(11,5))),
    (((0,4),(3,10)),((0,5),(10,6))),
    (((0,0),(12,4)),((0,1),(13,0))),
    (((0,5),(9,7)),((0,8),(9,6))),
    (((0,1),(12,4)),((0,2),(4,10))),
    (((0,18),(3,0)),((1,5),(9,7))),
    (((0,0),(13,1)),((0,4),(8,8))),
    (((0,2),(13,0)),((0,7),(12,1))),
    (((0,1),(13,1)),((0,17),(5,1))),
    (((0,2),(12,4)),((0,5),(12,3))),
    (((0,8),(4,9)),((0,8),(10,5))),
    (((0,7),(7,8)),((0,8),(8,7))),
    (((0,0),(7,9)),((0,3),(4,10))),
    (((0,2),(13,1)),((0,10),(0,9))),
    (((0,1),(7,9)),((0,5),(11,5))),
    (((0,3),(13,0)),((0,5),(3,10))),
    (((0,6),(2,10)),((0,12),(2,8))),
    (((0,3),(12,4)),((0,10),(1,9))),
    (((0,6),(10,6)),((0,12),(10,1))),
    (((0,2),(7,9)),((0,11),(4,8))),
    (((0,5),(8,8)),((0,6),(9,7))),
    (((0,0),(10,7)),((0,0),(13,2)))]
  have hc : ∀ i : Fin 100, Good (442+i.val) (c i).1 ∧
      Good (442+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-442,by omega⟩
  have he : 442+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_542 (n : ℕ) (hlo : 542≤n) (hhi : n<642) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,7),(0,10)),((0,7),(12,2))),
    (((0,1),(10,7)),((0,1),(13,2))),
    (((0,8),(12,0)),((0,15),(7,3))),
    (((0,0),(5,10)),((0,0),(11,6))),
    (((0,4),(13,0)),((0,6),(12,3))),
    (((0,1),(5,10)),((0,1),(11,6))),
    (((0,2),(10,7)),((0,2),(13,2))),
    (((0,6),(6,9)),((0,9),(9,6))),
    (((0,8),(12,1)),((0,10),(11,2))),
    (((0,6),(11,5)),((0,15),(8,1))),
    (((0,0),(9,8)),((0,2),(5,10))),
    (((0,12),(10,2)),((0,14),(9,0))),
    (((0,1),(9,8)),((0,8),(7,8))),
    (((0,19),(1,0)),((1,12),(10,2))),
    (((0,3),(10,7)),((0,3),(13,2))),
    (((0,5),(4,10)),((0,6),(8,8))),
    (((0,4),(7,9)),((0,7),(10,6))),
    (((0,2),(9,8)),((0,11),(9,5))),
    (((0,3),(5,10)),((0,3),(11,6))),
    (((0,0),(0,11)),((0,11),(11,0))),
    (((0,5),(12,4)),((0,14),(3,7))),
    (((0,1),(0,11)),((0,10),(3,9))),
    (((0,0),(12,5)),((0,13),(1,8))),
    (((0,0),(1,11)),((0,0),(13,3))),
    (((0,1),(12,5)),((0,5),(13,1))),
    (((0,1),(1,11)),((0,1),(13,3))),
    (((0,2),(0,11)),((0,15),(4,6))),
    (((0,7),(6,9)),((0,8),(1,10))),
    (((0,9),(12,0)),((0,13),(10,0))),
    (((0,2),(12,5)),((0,4),(5,10))),
    (((0,2),(1,11)),((0,2),(13,3))),
    (((0,18),(0,4)),((1,2),(12,5))),
    (((0,6),(4,10)),((0,10),(11,3))),
    (((0,0),(2,11)),((0,11),(10,4))),
    (((0,3),(0,11)),((0,9),(12,1))),
    (((0,1),(2,11)),((0,6),(13,0))),
    (((0,0),(8,9)),((0,4),(9,8))),
    (((0,0),(6,10)),((0,3),(12,5))),
    (((0,1),(8,9)),((0,3),(1,11))),
    (((0,1),(6,10)),((0,5),(10,7))),
    (((0,2),(2,11)),((0,11),(11,2))),
    (((0,6),(13,1)),((0,8),(9,7))),
    (((0,9),(5,9)),((0,14),(4,7))),
    (((0,2),(8,9)),((0,5),(5,10))),
    (((0,2),(6,10)),((0,10),(8,7))),
    (((0,4),(0,11)),((0,18),(2,4))),
    (((1,2),(6,10)),((1,10),(8,7))),
    (((0,6),(7,9)),((0,8),(12,3))),
    (((0,3),(2,11)),((0,4),(12,5))),
    (((0,0),(3,11)),((0,4),(1,11))),
    (((0,5),(9,8)),((0,8),(6,9))),
    (((0,1),(3,11)),((0,3),(8,9))),
    (((0,3),(6,10)),((0,7),(4,10))),
    (((0,8),(3,10)),((0,9),(1,10))),
    (((0,12),(11,0)),((0,15),(5,6))),
    (((0,7),(13,0)),((0,15),(9,0))),
    (((0,0),(13,4)),((0,2),(3,11))),
    (((0,7),(12,4)),((0,10),(12,0))),
    (((0,1),(13,4)),((0,8),(8,8))),
    (((0,4),(2,11)),((0,5),(0,11))),
    (((0,0),(14,0)),((0,6),(5,10))),
    (((0,7),(13,1)),((0,15),(9,1))),
    (((0,1),(14,0)),((0,4),(8,9))),
    (((0,0),(11,7)),((0,2),(13,4))),
    (((0,3),(3,11)),((0,11),(11,3))),
    (((0,1),(11,7)),((0,9),(10,6))),
    (((0,0),(14,1)),((1,3),(3,11))),
    (((0,2),(14,0)),((0,6),(9,8))),
    (((0,0),(10,8)),((0,1),(14,1))),
    (((0,14),(10,0)),((1,2),(14,0))),
    (((0,1),(10,8)),((0,2),(11,7))),
    (((0,0),(4,11)),((0,3),(13,4))),
    (((0,12),(2,9)),((0,17),(4,5))),
    (((0,0),(12,6)),((0,1),(4,11))),
    (((0,20),(0,1)),((1,12),(2,9))),
    (((0,1),(12,6)),((0,2),(10,8))),
    (((0,5),(8,9)),((0,6),(0,11))),
    (((0,0),(7,10)),((0,5),(6,10))),
    (((0,2),(4,11)),((0,3),(11,7))),
    (((0,1),(7,10)),((0,6),(12,5))),
    (((0,2),(12,6)),((0,6),(1,11))),
    (((0,0),(14,2)),((0,3),(14,1))),
    (((0,4),(13,4)),((0,10),(1,10))),
    (((0,1),(14,2)),((0,3),(10,8))),
    (((0,2),(7,10)),((0,8),(13,1))),
    (((0,16),(1,7)),((0,17),(2,6))),
    (((0,3),(4,11)),((0,4),(14,0))),
    (((0,7),(9,8)),((0,18),(2,5))),
    (((0,0),(9,9)),((0,2),(14,2))),
    (((0,4),(11,7)),((0,5),(3,11))),
    (((0,1),(9,9)),((0,6),(2,11))),
    (((0,19),(1,4)),((1,4),(11,7))),
    (((0,3),(7,10)),((0,4),(14,1))),
    (((0,6),(8,9)),((0,20),(1,2))),
    (((0,4),(10,8)),((0,6),(6,10))),
    (((0,2),(9,9)),((0,11),(12,1))),
    (((0,3),(14,2)),((0,5),(13,4))),
    (((0,4),(4,11)),((0,11),(11,4))),
    (((0,0),(13,5)),((0,13),(5,8))),
    (((0,0),(5,11)),((0,4),(12,6)))]
  have hc : ∀ i : Fin 100, Good (542+i.val) (c i).1 ∧
      Good (542+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-542,by omega⟩
  have he : 542+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_642 (n : ℕ) (hlo : 642≤n) (hhi : n<742) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(13,5)),((0,5),(14,0))),
    (((0,1),(5,11)),((0,9),(4,10))),
    (((0,10),(12,3)),((0,16),(9,0))),
    (((0,3),(9,9)),((0,4),(7,10))),
    (((0,9),(13,0)),((0,14),(6,7))),
    (((0,0),(14,3)),((0,2),(13,5))),
    (((0,2),(5,11)),((0,5),(14,1))),
    (((0,1),(14,3)),((0,4),(14,2))),
    (((0,5),(10,8)),((0,10),(3,10))),
    (((1,1),(14,3)),((1,4),(14,2))),
    (((0,7),(2,11)),((0,8),(9,8))),
    (((0,5),(4,11)),((0,12),(8,7))),
    (((0,2),(14,3)),((0,18),(6,3))),
    (((0,3),(13,5)),((0,5),(12,6))),
    (((0,3),(5,11)),((0,4),(9,9))),
    (((1,3),(13,5)),((1,5),(12,6))),
    (((0,9),(7,9)),((1,3),(5,11))),
    (((0,5),(7,10)),((0,6),(14,0))),
    (((1,9),(7,9)),((2,5),(4,11))),
    (((0,8),(0,11)),((0,15),(10,1))),
    (((0,3),(14,3)),((0,6),(11,7))),
    (((0,5),(14,2)),((0,17),(8,2))),
    (((0,8),(12,5)),((1,3),(14,3))),
    (((0,0),(8,10)),((0,6),(14,1))),
    (((0,0),(0,12)),((0,4),(13,5))),
    (((0,1),(8,10)),((0,4),(5,11))),
    (((0,1),(0,12)),((0,7),(3,11))),
    (((0,20),(2,3)),((1,1),(8,10))),
    (((0,0),(1,12)),((0,5),(9,9))),
    (((0,9),(5,10)),((0,9),(11,6))),
    (((0,1),(1,12)),((0,2),(8,10))),
    (((0,2),(0,12)),((0,4),(14,3))),
    (((0,0),(11,8)),((0,12),(11,4))),
    (((0,0),(6,11)),((0,0),(12,7))),
    (((0,1),(11,8)),((0,6),(7,10))),
    (((0,1),(6,11)),((0,1),(12,7))),
    (((0,8),(8,9)),((0,9),(9,8))),
    (((0,7),(14,0)),((0,8),(6,10))),
    (((0,0),(2,12)),((0,0),(14,4))),
    (((0,2),(11,8)),((0,3),(0,12))),
    (((0,1),(2,12)),((0,1),(14,4))),
    (((0,13),(9,6)),((0,14),(1,9))),
    (((1,1),(2,12)),((1,1),(14,4))),
    (((0,3),(1,12)),((0,7),(14,1))),
    (((0,14),(7,7)),((0,19),(6,2))),
    (((0,2),(2,12)),((0,2),(14,4))),
    (((0,0),(10,9)),((0,20),(0,4))),
    (((0,3),(11,8)),((0,14),(10,4))),
    (((0,0),(15,0)),((0,1),(10,9))),
    (((0,0),(13,6)),((0,4),(8,10))),
    (((0,1),(15,0)),((0,4),(0,12))),
    (((0,1),(13,6)),((0,14),(2,9))),
    (((0,17),(9,0)),((0,18),(7,3))),
    (((0,2),(10,9)),((0,3),(2,12))),
    (((0,0),(3,12)),((0,0),(15,1))),
    (((0,2),(15,0)),((0,6),(13,5))),
    (((0,1),(3,12)),((0,1),(15,1))),
    (((1,2),(15,0)),((1,6),(13,5))),
    (((0,4),(11,8)),((0,7),(14,2))),
    (((0,4),(6,11)),((0,4),(12,7))),
    (((0,8),(14,0)),((0,16),(10,0))),
    (((0,2),(3,12)),((0,2),(15,1))),
    (((0,6),(14,3)),((0,9),(8,9))),
    (((0,3),(15,0)),((0,5),(8,10))),
    (((0,3),(13,6)),((0,4),(2,12))),
    (((0,7),(9,9)),((0,10),(9,8))),
    (((0,8),(14,1)),((0,16),(10,1))),
    (((0,11),(12,4)),((0,14),(3,9))),
    (((0,5),(1,12)),((0,8),(10,8))),
    (((0,0),(15,2)),((0,3),(3,12))),
    (((0,13),(11,4)),((0,16),(8,5))),
    (((0,1),(15,2)),((0,8),(4,11))),
    (((0,4),(10,9)),((0,5),(11,8))),
    (((0,0),(7,11)),((0,5),(6,11))),
    (((0,4),(15,0)),((0,10),(0,11))),
    (((0,0),(9,10)),((0,1),(7,11))),
    (((0,0),(4,12)),((0,2),(15,2))),
    (((0,1),(9,10)),((0,8),(7,10))),
    (((0,1),(4,12)),((0,5),(2,12))),
    (((0,21),(1,3)),((1,1),(9,10))),
    (((0,0),(14,5)),((0,2),(7,11))),
    (((0,6),(0,12)),((0,8),(14,2))),
    (((0,1),(14,5)),((0,2),(9,10))),
    (((0,2),(4,12)),((0,13),(0,10))),
    (((0,3),(15,2)),((0,18),(0,7))),
    (((0,6),(1,12)),((0,15),(1,9))),
    (((0,5),(10,9)),((0,9),(14,0))),
    (((0,2),(14,5)),((0,13),(1,10))),
    (((0,3),(7,11)),((0,5),(15,0))),
    (((0,5),(13,6)),((0,6),(11,8))),
    (((0,3),(9,10)),((0,6),(6,11))),
    (((0,3),(4,12)),((0,10),(8,9))),
    (((0,9),(14,1)),((0,10),(6,10))),
    (((0,0),(15,3)),((0,20),(5,3))),
    (((0,5),(3,12)),((0,5),(15,1))),
    (((0,1),(15,3)),((0,3),(14,5))),
    (((1,5),(3,12)),((1,5),(15,1))),
    (((0,9),(4,11)),((0,11),(9,8))),
    (((0,8),(13,5)),((0,15),(11,2))),
    (((0,4),(7,11)),((0,8),(5,11)))]
  have hc : ∀ i : Fin 100, Good (642+i.val) (c i).1 ∧
      Good (642+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-642,by omega⟩
  have he : 642+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_742 (n : ℕ) (hlo : 742≤n) (hhi : n<842) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(15,3)),((0,7),(8,10))),
    (((0,4),(9,10)),((0,7),(0,12))),
    (((0,0),(12,8)),((0,4),(4,12))),
    (((0,6),(10,9)),((0,9),(7,10))),
    (((0,0),(5,12)),((0,1),(12,8))),
    (((0,6),(15,0)),((0,7),(1,12))),
    (((0,1),(5,12)),((0,4),(14,5))),
    (((0,9),(14,2)),((0,13),(12,3))),
    (((0,3),(15,3)),((0,19),(7,3))),
    (((0,0),(13,7)),((0,2),(12,8))),
    (((0,0),(11,9)),((0,7),(6,11))),
    (((0,1),(13,7)),((0,2),(5,12))),
    (((0,1),(11,9)),((0,12),(7,9))),
    (((0,5),(7,11)),((0,13),(3,10))),
    (((0,9),(9,9)),((0,17),(2,8))),
    (((0,5),(9,10)),((0,7),(2,12))),
    (((0,2),(13,7)),((0,5),(4,12))),
    (((0,2),(11,9)),((0,3),(12,8))),
    (((0,10),(11,7)),((0,13),(8,8))),
    (((0,0),(8,11)),((0,3),(5,12))),
    (((0,5),(14,5)),((0,11),(2,11))),
    (((0,1),(8,11)),((0,10),(14,1))),
    (((0,15),(11,3)),((0,16),(9,5))),
    (((0,7),(10,9)),((0,8),(8,10))),
    (((0,3),(13,7)),((0,8),(0,12))),
    (((0,3),(11,9)),((0,7),(15,0))),
    (((0,0),(15,4)),((0,2),(8,11))),
    (((0,18),(7,5)),((0,20),(6,3))),
    (((0,1),(15,4)),((0,4),(12,8))),
    (((1,18),(7,5)),((1,20),(6,3))),
    (((0,4),(5,12)),((0,6),(7,11))),
    (((0,0),(14,6)),((0,7),(3,12))),
    (((0,6),(9,10)),((0,8),(11,8))),
    (((0,0),(10,10)),((0,1),(14,6))),
    (((0,3),(8,11)),((0,15),(8,7))),
    (((0,1),(10,10)),((0,4),(13,7))),
    (((0,4),(11,9)),((0,10),(14,2))),
    (((0,6),(14,5)),((1,1),(10,10))),
    (((0,0),(0,13)),((0,0),(6,12))),
    (((0,20),(0,6)),((1,6),(14,5))),
    (((0,1),(0,13)),((0,1),(6,12))),
    (((0,3),(15,4)),((0,12),(0,11))),
    (((0,0),(1,13)),((0,0),(16,0))),
    (((0,10),(9,9)),((0,11),(13,4))),
    (((0,1),(1,13)),((0,1),(16,0))),
    (((0,2),(0,13)),((0,2),(6,12))),
    (((0,3),(14,6)),((0,7),(15,2))),
    (((0,11),(14,0)),((0,15),(12,0))),
    (((0,0),(16,1)),((0,3),(10,10))),
    (((0,2),(1,13)),((0,2),(16,0))),
    (((0,1),(16,1)),((0,5),(11,9))),
    (((0,14),(6,9)),((1,2),(1,13))),
    (((0,0),(2,13)),((0,4),(15,4))),
    (((0,3),(0,13)),((0,3),(6,12))),
    (((0,1),(2,13)),((0,8),(3,12))),
    (((0,2),(16,1)),((0,11),(10,8))),
    (((1,1),(2,13)),((1,8),(3,12))),
    (((0,3),(1,13)),((0,3),(16,0))),
    (((0,9),(11,8)),((0,11),(4,11))),
    (((0,2),(2,13)),((0,4),(10,10))),
    (((0,10),(14,3)),((0,11),(12,6))),
    (((0,6),(5,12)),((0,15),(5,9))),
    (((1,10),(14,3)),((1,11),(12,6))),
    (((0,0),(16,2)),((0,3),(16,1))),
    (((0,4),(0,13)),((0,4),(6,12))),
    (((0,1),(16,2)),((0,21),(6,2))),
    (((0,5),(15,4)),((0,6),(13,7))),
    (((0,3),(2,13)),((0,6),(11,9))),
    (((0,0),(3,13)),((0,0),(15,5))),
    (((0,8),(15,2)),((0,16),(11,3))),
    (((0,1),(3,13)),((0,1),(15,5))),
    (((0,0),(9,11)),((0,5),(14,6))),
    (((0,9),(10,9)),((0,15),(1,10))),
    (((0,1),(9,11)),((0,5),(10,10))),
    (((0,4),(16,1)),((0,9),(15,0))),
    (((0,2),(3,13)),((0,2),(15,5))),
    (((0,6),(8,11)),((0,8),(4,12))),
    (((0,22),(1,4)),((0,23),(2,0))),
    (((0,0),(7,12)),((0,0),(13,8))),
    (((0,7),(12,8)),((0,10),(0,12))),
    (((0,0),(12,9)),((0,1),(7,12))),
    (((0,7),(5,12)),((0,14),(12,4))),
    (((0,1),(12,9)),((0,5),(1,13))),
    (((0,3),(3,13)),((0,3),(15,5))),
    (((0,15),(10,6)),((0,18),(10,2))),
    (((0,2),(7,12)),((0,2),(13,8))),
    (((0,3),(9,11)),((0,7),(13,7))),
    (((0,0),(16,3)),((0,2),(12,9))),
    (((0,5),(16,1)),((0,6),(14,6))),
    (((0,1),(16,3)),((0,4),(16,2))),
    (((0,0),(4,13)),((0,6),(10,10))),
    (((0,0),(14,7)),((0,14),(7,9))),
    (((0,1),(4,13)),((0,5),(2,13))),
    (((0,1),(14,7)),((0,3),(7,12))),
    (((0,2),(16,3)),((0,4),(3,13))),
    (((0,3),(12,9)),((0,6),(0,13))),
    (((0,7),(8,11)),((0,13),(8,9))),
    (((0,0),(11,10)),((0,2),(4,13))),
    (((0,2),(14,7)),((0,15),(3,10))),
    (((0,1),(11,10)),((0,6),(1,13)))]
  have hc : ∀ i : Fin 100, Good (742+i.val) (c i).1 ∧
      Good (742+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-742,by omega⟩
  have he : 742+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_842 (n : ℕ) (hlo : 842≤n) (hhi : n<942) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,14),(10,7)),((0,14),(13,2))),
    (((0,9),(9,10)),((0,10),(10,9))),
    (((0,3),(16,3)),((0,8),(12,8))),
    (((0,5),(16,2)),((0,7),(15,4))),
    (((0,2),(11,10)),((0,4),(7,12))),
    (((0,3),(4,13)),((0,6),(16,1))),
    (((0,3),(14,7)),((0,4),(12,9))),
    (((1,3),(4,13)),((1,6),(16,1))),
    (((0,5),(3,13)),((0,5),(15,5))),
    (((0,6),(2,13)),((0,8),(13,7))),
    (((0,7),(10,10)),((0,8),(11,9))),
    (((0,5),(9,11)),((0,11),(0,12))),
    (((0,3),(11,10)),((0,23),(1,3))),
    (((0,4),(16,3)),((0,19),(1,8))),
    (((0,17),(6,8)),((0,23),(3,2))),
    (((0,7),(0,13)),((0,7),(6,12))),
    (((0,4),(4,13)),((0,13),(13,4))),
    (((0,4),(14,7)),((1,7),(0,13))),
    (((0,0),(5,13)),((0,5),(7,12))),
    (((0,0),(15,6)),((0,7),(1,13))),
    (((0,0),(16,4)),((0,1),(5,13))),
    (((0,1),(15,6)),((0,12),(5,11))),
    (((0,1),(16,4)),((0,21),(6,4))),
    (((0,4),(11,10)),((0,13),(11,7))),
    (((0,0),(8,12)),((0,10),(15,2))),
    (((0,2),(5,13)),((0,6),(3,13))),
    (((0,1),(8,12)),((0,2),(15,6))),
    (((0,2),(16,4)),((0,5),(16,3))),
    (((0,6),(9,11)),((0,9),(12,8))),
    (((0,0),(10,11)),((0,7),(2,13))),
    (((0,5),(4,13)),((0,9),(5,12))),
    (((0,1),(10,11)),((0,2),(8,12))),
    (((1,5),(4,13)),((1,9),(5,12))),
    (((0,3),(5,13)),((0,8),(10,10))),
    (((0,3),(15,6)),((0,14),(2,11))),
    (((0,3),(16,4)),((0,6),(7,12))),
    (((0,2),(10,11)),((0,9),(11,9))),
    (((0,5),(11,10)),((0,6),(12,9))),
    (((0,8),(0,13)),((0,8),(6,12))),
    (((0,3),(8,12)),((0,16),(12,3))),
    (((0,7),(16,2)),((0,19),(10,2))),
    (((0,11),(3,12)),((0,11),(15,1))),
    (((0,0),(17,0)),((0,8),(1,13))),
    (((0,23),(5,0)),((1,11),(3,12))),
    (((0,1),(17,0)),((0,3),(10,11))),
    (((0,4),(15,6)),((0,7),(3,13))),
    (((0,4),(16,4)),((0,12),(0,12))),
    (((0,6),(4,13)),((1,4),(15,6))),
    (((0,0),(17,1)),((0,6),(14,7))),
    (((0,2),(17,0)),((0,22),(7,0))),
    (((0,1),(17,1)),((0,4),(8,12))),
    (((0,20),(4,7)),((0,21),(8,2))),
    (((0,0),(6,13)),((0,8),(2,13))),
    (((0,20),(6,6)),((0,21),(4,6))),
    (((0,1),(6,13)),((0,6),(11,10))),
    (((0,2),(17,1)),((0,4),(10,11))),
    (((0,0),(13,9)),((0,11),(15,2))),
    (((0,3),(17,0)),((0,7),(12,9))),
    (((0,1),(13,9)),((0,5),(5,13))),
    (((0,2),(6,13)),((0,5),(15,6))),
    (((0,0),(14,8)),((0,5),(16,4))),
    (((0,0),(0,14)),((0,14),(14,0))),
    (((0,0),(16,5)),((0,1),(14,8))),
    (((0,0),(17,2)),((0,1),(0,14))),
    (((0,1),(16,5)),((0,5),(8,12))),
    (((0,0),(1,14)),((0,1),(17,2))),
    (((0,22),(0,6)),((1,1),(16,5))),
    (((0,0),(12,10)),((0,1),(1,14))),
    (((0,2),(0,14)),((0,4),(17,0))),
    (((0,1),(12,10)),((0,2),(16,5))),
    (((0,2),(17,2)),((0,12),(15,0))),
    (((0,3),(13,9)),((0,8),(9,11))),
    (((0,2),(1,14)),((0,14),(4,11))),
    (((1,3),(13,9)),((1,8),(9,11))),
    (((0,2),(12,10)),((0,4),(17,1))),
    (((0,0),(2,14)),((0,3),(14,8))),
    (((0,0),(9,12)),((0,3),(0,14))),
    (((0,1),(2,14)),((0,3),(16,5))),
    (((0,1),(9,12)),((0,3),(17,2))),
    (((0,0),(15,7)),((0,17),(2,10))),
    (((0,3),(1,14)),((0,8),(12,9))),
    (((0,1),(15,7)),((0,6),(8,12))),
    (((0,2),(2,14)),((0,3),(12,10))),
    (((0,2),(9,12)),((0,13),(8,10))),
    (((0,13),(0,12)),((0,18),(8,7))),
    (((0,24),(3,2)),((1,2),(9,12))),
    (((0,2),(15,7)),((0,4),(14,8))),
    (((0,0),(17,3)),((0,4),(0,14))),
    (((0,4),(16,5)),((0,5),(17,1))),
    (((0,1),(17,3)),((0,4),(17,2))),
    (((0,3),(2,14)),((0,8),(4,13))),
    (((0,0),(3,14)),((0,3),(9,12))),
    (((0,0),(7,13)),((0,5),(6,13))),
    (((0,0),(11,11)),((0,1),(3,14))),
    (((0,1),(7,13)),((0,2),(17,3))),
    (((0,1),(11,11)),((0,7),(5,13))),
    (((0,5),(13,9)),((0,7),(15,6))),
    (((0,7),(16,4)),((0,8),(11,10))),
    (((0,2),(3,14)),((0,12),(4,12))),
    (((0,2),(7,13)),((0,6),(17,0)))]
  have hc : ∀ i : Fin 100, Good (842+i.val) (c i).1 ∧
      Good (842+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-842,by omega⟩
  have he : 842+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_942 (n : ℕ) (hlo : 942≤n) (hhi : n<1042) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(11,11)),((0,5),(14,8))),
    (((0,4),(2,14)),((0,5),(0,14))),
    (((0,3),(17,3)),((0,4),(9,12))),
    (((0,5),(17,2)),((0,10),(16,1))),
    (((0,9),(7,12)),((0,9),(13,8))),
    (((0,4),(15,7)),((0,5),(1,14))),
    (((0,3),(3,14)),((0,7),(10,11))),
    (((0,3),(7,13)),((0,5),(12,10))),
    (((0,3),(11,11)),((0,13),(15,0))),
    (((0,6),(6,13)),((0,13),(13,6))),
    (((1,3),(11,11)),((1,13),(15,0))),
    (((0,15),(14,1)),((0,16),(0,11))),
    (((0,24),(0,4)),((0,25),(1,0))),
    (((0,0),(4,14)),((0,0),(16,6))),
    (((0,13),(3,12)),((0,13),(15,1))),
    (((0,1),(4,14)),((0,1),(16,6))),
    (((0,5),(9,12)),((0,9),(4,13))),
    (((0,4),(3,14)),((0,6),(14,8))),
    (((0,4),(7,13)),((0,6),(0,14))),
    (((0,4),(11,11)),((0,5),(15,7))),
    (((0,0),(17,4)),((0,2),(4,14))),
    (((0,23),(5,4)),((1,4),(11,11))),
    (((0,1),(17,4)),((0,6),(1,14))),
    (((0,9),(11,10)),((0,10),(3,13))),
    (((0,6),(12,10)),((0,8),(8,12))),
    (((0,7),(17,1)),((0,11),(0,13))),
    (((0,10),(9,11)),((0,12),(5,12))),
    (((0,2),(17,4)),((0,5),(17,3))),
    (((0,3),(4,14)),((0,3),(16,6))),
    (((0,7),(6,13)),((0,8),(10,11))),
    (((0,21),(0,8)),((0,22),(1,7))),
    (((0,5),(3,14)),((0,12),(13,7))),
    (((0,5),(7,13)),((0,6),(2,14))),
    (((0,5),(11,11)),((0,6),(9,12))),
    (((0,0),(10,12)),((0,14),(6,11))),
    (((0,3),(17,4)),((0,10),(12,9))),
    (((0,1),(10,12)),((0,6),(15,7))),
    (((0,7),(14,8)),((1,3),(17,4))),
    (((0,0),(8,13)),((0,0),(14,9))),
    (((0,4),(4,14)),((0,4),(16,6))),
    (((0,1),(8,13)),((0,1),(14,9))),
    (((0,0),(5,14)),((0,2),(10,12))),
    (((0,7),(1,14)),((0,8),(17,0))),
    (((0,0),(13,10)),((0,1),(5,14))),
    (((0,6),(17,3)),((0,7),(12,10))),
    (((0,1),(13,10)),((0,2),(8,13))),
    (((0,4),(17,4)),((0,9),(16,4))),
    (((0,14),(10,9)),((0,18),(11,5))),
    (((0,0),(15,8)),((0,0),(18,0))),
    (((0,3),(10,12)),((0,6),(7,13))),
    (((0,1),(15,8)),((0,1),(18,0))),
    (((1,3),(10,12)),((1,6),(7,13))),
    (((0,7),(2,14)),((0,8),(6,13))),
    (((0,3),(8,13)),((0,3),(14,9))),
    (((0,0),(18,1)),((0,24),(0,5))),
    (((0,2),(15,8)),((0,2),(18,0))),
    (((0,1),(18,1)),((0,3),(5,14))),
    (((0,25),(1,3)),((1,2),(15,8))),
    (((0,3),(13,10)),((0,11),(9,11))),
    (((0,19),(12,1)),((0,24),(5,3))),
    (((0,4),(10,12)),((0,5),(17,4))),
    (((0,2),(18,1)),((0,8),(0,14))),
    (((0,0),(17,5)),((0,8),(16,5))),
    (((0,0),(12,11)),((0,3),(15,8))),
    (((0,1),(17,5)),((0,4),(8,13))),
    (((0,1),(12,11)),((0,8),(1,14))),
    (((0,25),(4,1)),((1,1),(17,5))),
    (((0,4),(5,14)),((0,8),(12,10))),
    (((0,7),(3,14)),((0,9),(17,0))),
    (((0,0),(18,2)),((0,2),(17,5))),
    (((0,2),(12,11)),((0,6),(4,14))),
    (((0,1),(18,2)),((1,2),(17,5))),
    (((1,2),(12,11)),((1,6),(4,14))),
    (((0,0),(16,7)),((0,10),(5,13))),
    (((0,4),(15,8)),((0,4),(18,0))),
    (((0,0),(6,14)),((0,1),(16,7))),
    (((0,2),(18,2)),((0,8),(9,12))),
    (((0,1),(6,14)),((0,3),(17,5))),
    (((0,3),(12,11)),((0,5),(8,13))),
    (((0,8),(15,7)),((0,10),(8,12))),
    (((0,2),(16,7)),((0,4),(18,1))),
    (((0,5),(5,14)),((0,14),(14,5))),
    (((0,2),(6,14)),((0,9),(13,9))),
    (((0,5),(13,10)),((0,15),(2,12))),
    (((0,3),(18,2)),((0,10),(10,11))),
    (((0,12),(16,2)),((0,18),(7,9))),
    (((0,9),(14,8)),((0,13),(15,4))),
    (((0,8),(17,3)),((0,9),(0,14))),
    (((0,3),(16,7)),((0,4),(17,5))),
    (((0,4),(12,11)),((0,9),(17,2))),
    (((0,0),(9,13)),((0,3),(6,14))),
    (((0,6),(10,12)),((0,8),(3,14))),
    (((0,1),(9,13)),((0,8),(7,13))),
    (((0,0),(0,15)),((0,0),(18,3))),
    (((0,5),(18,1)),((0,14),(15,3))),
    (((0,1),(0,15)),((0,1),(18,3))),
    (((1,5),(18,1)),((1,14),(15,3))),
    (((0,0),(1,15)),((0,2),(9,13))),
    (((0,0),(11,12)),((0,6),(5,14))),
    (((0,1),(1,15)),((0,4),(16,7)))]
  have hc : ∀ i : Fin 100, Good (942+i.val) (c i).1 ∧
      Good (942+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-942,by omega⟩
  have he : 942+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1042 (n : ℕ) (hlo : 1042≤n) (hhi : n<1142) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(11,12)),((0,2),(0,15))),
    (((0,4),(6,14)),((0,9),(2,14))),
    (((0,5),(17,5)),((0,9),(9,12))),
    (((0,5),(12,11)),((0,10),(17,1))),
    (((0,2),(1,15)),((0,19),(3,10))),
    (((0,2),(11,12)),((0,3),(9,13))),
    (((0,11),(15,6)),((0,22),(5,7))),
    (((0,0),(2,15)),((0,10),(6,13))),
    (((0,3),(0,15)),((0,3),(18,3))),
    (((0,1),(2,15)),((0,5),(18,2))),
    (((0,14),(13,7)),((0,17),(10,8))),
    (((0,6),(18,1)),((0,7),(10,12))),
    (((0,3),(1,15)),((0,12),(4,13))),
    (((0,0),(17,6)),((0,3),(11,12))),
    (((0,2),(2,15)),((0,15),(15,2))),
    (((0,0),(7,14)),((0,1),(17,6))),
    (((0,4),(9,13)),((0,10),(0,14))),
    (((0,1),(7,14)),((0,9),(3,14))),
    (((0,7),(5,14)),((0,9),(7,13))),
    (((0,4),(0,15)),((0,4),(18,3))),
    (((0,2),(17,6)),((0,6),(12,11))),
    (((0,15),(4,12)),((0,23),(9,1))),
    (((0,2),(7,14)),((0,3),(2,15))),
    (((0,0),(3,15)),((0,4),(1,15))),
    (((0,4),(11,12)),((0,16),(11,8))),
    (((0,0),(14,10)),((0,1),(3,15))),
    (((0,0),(15,9)),((0,0),(18,4))),
    (((0,1),(14,10)),((0,14),(15,4))),
    (((0,1),(15,9)),((0,1),(18,4))),
    (((0,11),(17,0)),((0,19),(13,0))),
    (((0,2),(3,15)),((0,3),(7,14))),
    (((0,7),(18,1)),((0,10),(9,12))),
    (((0,2),(14,10)),((0,6),(6,14))),
    (((0,2),(15,9)),((0,2),(18,4))),
    (((0,8),(10,12)),((0,10),(15,7))),
    (((0,11),(17,1)),((0,19),(13,1))),
    (((0,23),(9,2)),((0,26),(3,2))),
    (((0,5),(1,15)),((0,20),(1,10))),
    (((0,3),(3,15)),((0,5),(11,12))),
    (((0,0),(13,11)),((0,4),(17,6))),
    (((0,3),(14,10)),((0,7),(12,11))),
    (((0,1),(13,11)),((0,3),(15,9))),
    (((0,0),(16,8)),((0,10),(17,3))),
    (((0,8),(13,10)),((0,11),(13,9))),
    (((0,1),(16,8)),((0,18),(3,11))),
    (((0,0),(4,15)),((1,8),(13,10))),
    (((0,2),(13,11)),((0,7),(18,2))),
    (((0,1),(4,15)),((0,5),(2,15))),
    (((0,0),(10,13)),((0,8),(15,8))),
    (((0,2),(16,8)),((0,4),(3,15))),
    (((0,1),(10,13)),((0,6),(0,15))),
    (((0,4),(14,10)),((0,12),(10,11))),
    (((0,2),(4,15)),((0,4),(15,9))),
    (((0,5),(17,6)),((0,14),(2,13))),
    (((0,3),(13,11)),((0,6),(1,15))),
    (((0,2),(10,13)),((0,5),(7,14))),
    (((1,3),(13,11)),((1,6),(1,15))),
    (((0,3),(16,8)),((0,13),(11,10))),
    (((0,18),(11,7)),((0,25),(3,5))),
    (((1,3),(16,8)),((1,13),(11,10))),
    (((0,0),(19,0)),((0,3),(4,15))),
    (((0,0),(8,14)),((0,16),(15,2))),
    (((0,1),(19,0)),((0,8),(17,5))),
    (((0,1),(8,14)),((0,3),(10,13))),
    (((0,6),(2,15)),((0,9),(8,13))),
    (((0,4),(13,11)),((0,5),(14,10))),
    (((0,0),(19,1)),((0,5),(15,9))),
    (((0,2),(19,0)),((0,7),(9,13))),
    (((0,0),(12,12)),((0,0),(18,5))),
    (((0,8),(18,2)),((0,9),(13,10))),
    (((0,1),(12,12)),((0,1),(18,5))),
    (((0,4),(4,15)),((0,15),(15,4))),
    (((0,6),(7,14)),((0,14),(9,11))),
    (((0,0),(5,15)),((0,0),(17,7))),
    (((0,4),(10,13)),((0,7),(1,15))),
    (((0,1),(5,15)),((0,1),(17,7))),
    (((0,3),(8,14)),((0,15),(14,6))),
    (((0,22),(1,9)),((0,23),(2,8))),
    (((0,11),(3,14)),((0,12),(13,9))),
    (((0,5),(13,11)),((0,11),(7,13))),
    (((0,2),(5,15)),((0,2),(17,7))),
    (((0,0),(19,2)),((0,3),(19,1))),
    (((0,5),(16,8)),((0,6),(14,10))),
    (((0,1),(19,2)),((0,3),(12,12))),
    (((0,7),(2,15)),((0,12),(16,5))),
    (((0,5),(4,15)),((0,12),(17,2))),
    (((0,4),(19,0)),((0,24),(9,0))),
    (((0,4),(8,14)),((0,12),(1,14))),
    (((0,2),(19,2)),((0,3),(5,15))),
    (((0,9),(12,11)),((0,10),(10,12))),
    (((0,7),(17,6)),((0,8),(9,13))),
    (((0,14),(4,13)),((0,17),(13,6))),
    (((0,4),(19,1)),((0,7),(7,14))),
    (((0,8),(0,15)),((0,8),(18,3))),
    (((0,4),(12,12)),((0,4),(18,5))),
    (((0,9),(18,2)),((0,21),(0,10))),
    (((0,3),(19,2)),((0,6),(13,11))),
    (((0,8),(1,15)),((0,12),(2,14))),
    (((0,8),(11,12)),((0,10),(13,10))),
    (((0,4),(5,15)),((0,4),(17,7)))]
  have hc : ∀ i : Fin 100, Good (1042+i.val) (c i).1 ∧
      Good (1042+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1042,by omega⟩
  have he : 1042+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1142 (n : ℕ) (hlo : 1142≤n) (hhi : n<1242) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,5),(19,0)),((0,7),(3,15))),
    (((0,5),(8,14)),((0,9),(6,14))),
    (((0,6),(4,15)),((0,7),(14,10))),
    (((0,7),(15,9)),((0,7),(18,4))),
    (((1,6),(4,15)),((1,7),(14,10))),
    (((0,0),(19,3)),((0,6),(10,13))),
    (((0,5),(19,1)),((2,4),(5,15))),
    (((0,0),(6,15)),((0,1),(19,3))),
    (((0,5),(12,12)),((0,5),(18,5))),
    (((0,1),(6,15)),((0,10),(18,1))),
    (((0,26),(5,3)),((0,27),(0,3))),
    (((0,16),(8,11)),((0,17),(15,2))),
    (((0,0),(11,13)),((0,2),(19,3))),
    (((0,0),(9,14)),((0,0),(15,10))),
    (((0,1),(11,13)),((0,2),(6,15))),
    (((0,1),(9,14)),((0,1),(15,10))),
    (((0,7),(13,11)),((0,9),(9,13))),
    (((0,6),(19,0)),((0,10),(17,5))),
    (((0,6),(8,14)),((0,10),(12,11))),
    (((0,0),(18,6)),((0,2),(11,13))),
    (((0,0),(16,9)),((0,2),(9,14))),
    (((0,0),(14,11)),((0,1),(18,6))),
    (((0,1),(16,9)),((0,3),(6,15))),
    (((0,1),(14,11)),((0,6),(19,1))),
    (((0,9),(11,12)),((0,10),(18,2))),
    (((0,6),(12,12)),((0,6),(18,5))),
    (((0,2),(18,6)),((0,8),(15,9))),
    (((0,2),(16,9)),((0,3),(11,13))),
    (((0,2),(14,11)),((0,3),(9,14))),
    (((0,20),(0,11)),((0,25),(8,2))),
    (((0,6),(5,15)),((0,6),(17,7))),
    (((0,4),(19,3)),((0,24),(9,3))),
    (((0,15),(16,3)),((0,19),(14,2))),
    (((0,4),(6,15)),((0,9),(2,15))),
    (((0,0),(0,16)),((0,3),(18,6))),
    (((0,3),(16,9)),((0,11),(15,8))),
    (((0,1),(0,16)),((0,3),(14,11))),
    (((0,7),(19,0)),((0,23),(11,0))),
    (((0,0),(1,16)),((0,0),(19,4))),
    (((0,4),(9,14)),((0,4),(15,10))),
    (((0,1),(1,16)),((0,1),(19,4))),
    (((0,2),(0,16)),((0,9),(7,14))),
    (((0,0),(17,8)),((0,8),(16,8))),
    (((0,7),(19,1)),((0,14),(17,0))),
    (((0,0),(13,12)),((0,1),(17,8))),
    (((0,2),(1,16)),((0,2),(19,4))),
    (((0,1),(13,12)),((0,4),(16,9))),
    (((0,0),(7,15)),((0,4),(14,11))),
    (((0,0),(2,16)),((0,8),(10,13))),
    (((0,1),(7,15)),((0,2),(17,8))),
    (((0,1),(2,16)),((0,7),(5,15))),
    (((0,2),(13,12)),((0,9),(14,10))),
    (((0,5),(11,13)),((0,9),(15,9))),
    (((0,3),(1,16)),((0,3),(19,4))),
    (((0,2),(7,15)),((0,24),(8,5))),
    (((0,2),(2,16)),((0,16),(16,2))),
    (((0,11),(18,2)),((0,12),(10,12))),
    (((0,3),(17,8)),((0,14),(13,9))),
    (((0,7),(19,2)),((0,23),(11,2))),
    (((0,3),(13,12)),((0,5),(18,6))),
    (((0,4),(0,16)),((0,5),(16,9))),
    (((0,5),(14,11)),((0,8),(8,14))),
    (((0,3),(7,15)),((0,6),(19,3))),
    (((0,3),(2,16)),((0,12),(5,14))),
    (((0,0),(3,16)),((0,4),(1,16))),
    (((0,9),(13,11)),((0,12),(13,10))),
    (((0,1),(3,16)),((0,8),(19,1))),
    (((1,9),(13,11)),((1,12),(13,10))),
    (((0,4),(17,8)),((0,8),(12,12))),
    (((0,6),(11,13)),((0,15),(8,12))),
    (((0,4),(13,12)),((0,6),(9,14))),
    (((0,0),(10,14)),((0,2),(3,16))),
    (((0,16),(12,9)),((1,4),(13,12))),
    (((0,1),(10,14)),((0,4),(7,15))),
    (((0,4),(2,16)),((0,5),(0,16))),
    (((0,17),(10,10)),((0,18),(14,5))),
    (((0,6),(18,6)),((0,12),(18,1))),
    (((0,6),(16,9)),((0,11),(9,13))),
    (((0,0),(20,0)),((0,2),(10,14))),
    (((0,0),(18,7)),((0,3),(3,16))),
    (((0,0),(19,5)),((0,1),(20,0))),
    (((0,1),(18,7)),((0,8),(19,2))),
    (((0,0),(12,13)),((0,1),(19,5))),
    (((0,16),(14,7)),((0,19),(11,8))),
    (((0,0),(20,1)),((0,1),(12,13))),
    (((0,2),(20,0)),((0,11),(11,12))),
    (((0,0),(4,16)),((0,1),(20,1))),
    (((0,2),(19,5)),((0,5),(7,15))),
    (((0,1),(4,16)),((0,5),(2,16))),
    (((0,2),(12,13)),((0,7),(11,13))),
    (((0,4),(3,16)),((0,7),(9,14))),
    (((0,2),(20,1)),((0,6),(0,16))),
    (((0,9),(19,1)),((0,14),(3,14))),
    (((0,0),(8,15)),((0,2),(4,16))),
    (((0,3),(18,7)),((0,9),(12,12))),
    (((0,1),(8,15)),((0,3),(19,5))),
    (((0,7),(18,6)),((1,3),(18,7))),
    (((0,3),(12,13)),((0,4),(10,14))),
    (((0,7),(14,11)),((0,13),(8,13))),
    (((0,0),(20,2)),((0,3),(20,1)))]
  have hc : ∀ i : Fin 100, Good (1142+i.val) (c i).1 ∧
      Good (1142+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1142,by omega⟩
  have he : 1142+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1242 (n : ℕ) (hlo : 1242≤n) (hhi : n<1342) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(8,15)),((0,10),(4,15))),
    (((0,1),(20,2)),((0,3),(4,16))),
    (((0,11),(7,14)),((1,2),(8,15))),
    (((0,10),(10,13)),((0,13),(13,10))),
    (((0,4),(20,0)),((0,5),(3,16))),
    (((0,4),(18,7)),((0,6),(2,16))),
    (((0,2),(20,2)),((0,4),(19,5))),
    (((0,0),(16,10)),((0,8),(6,15))),
    (((0,3),(8,15)),((0,4),(12,13))),
    (((0,0),(15,11)),((0,1),(16,10))),
    (((0,4),(20,1)),((0,11),(3,15))),
    (((0,1),(15,11)),((0,5),(10,14))),
    (((0,4),(4,16)),((0,8),(11,13))),
    (((0,8),(9,14)),((0,8),(15,10))),
    (((0,0),(5,16)),((0,2),(16,10))),
    (((0,7),(1,16)),((0,7),(19,4))),
    (((0,1),(5,16)),((0,2),(15,11))),
    (((0,22),(12,4)),((0,23),(7,8))),
    (((0,5),(20,0)),((0,25),(10,0))),
    (((0,4),(8,15)),((0,5),(18,7))),
    (((0,0),(17,9)),((0,5),(19,5))),
    (((0,2),(5,16)),((0,6),(3,16))),
    (((0,1),(17,9)),((0,3),(16,10))),
    (((0,0),(20,3)),((0,10),(12,12))),
    (((0,3),(15,11)),((0,5),(20,1))),
    (((0,1),(20,3)),((0,4),(20,2))),
    (((0,0),(14,12)),((0,5),(4,16))),
    (((0,2),(17,9)),((0,19),(4,12))),
    (((0,1),(14,12)),((0,6),(10,14))),
    (((0,3),(5,16)),((0,11),(16,8))),
    (((0,2),(20,3)),((0,26),(2,7))),
    (((0,0),(19,6)),((0,9),(19,3))),
    (((0,11),(4,15)),((0,15),(17,3))),
    (((0,1),(19,6)),((0,2),(14,12))),
    (((0,8),(0,16)),((0,16),(17,0))),
    (((0,0),(11,14)),((0,3),(17,9))),
    (((0,6),(18,7)),((0,10),(19,2))),
    (((0,1),(11,14)),((0,6),(19,5))),
    (((0,2),(19,6)),((0,3),(20,3))),
    (((0,5),(20,2)),((0,6),(12,13))),
    (((0,4),(5,16)),((0,16),(17,1))),
    (((0,3),(14,12)),((0,6),(20,1))),
    (((0,2),(11,14)),((0,8),(17,8))),
    (((0,6),(4,16)),((0,18),(16,1))),
    (((0,8),(13,12)),((0,14),(13,10))),
    (((0,0),(9,15)),((0,9),(18,6))),
    (((0,3),(19,6)),((0,4),(17,9))),
    (((0,1),(9,15)),((0,5),(16,10))),
    (((0,0),(6,16)),((0,0),(18,8))),
    (((0,4),(20,3)),((0,5),(15,11))),
    (((0,1),(6,16)),((0,1),(18,8))),
    (((1,4),(20,3)),((1,5),(15,11))),
    (((0,2),(9,15)),((0,4),(14,12))),
    (((0,11),(19,1)),((0,13),(0,15))),
    (((0,5),(5,16)),((0,16),(16,5))),
    (((0,2),(6,16)),((0,2),(18,8))),
    (((0,0),(20,4)),((0,6),(20,2))),
    (((0,4),(19,6)),((0,7),(19,5))),
    (((0,0),(13,13)),((0,1),(20,4))),
    (((0,7),(12,13)),((0,16),(12,10))),
    (((0,1),(13,13)),((0,3),(9,15))),
    (((0,4),(11,14)),((0,7),(20,1))),
    (((0,10),(6,15)),((0,17),(16,4))),
    (((0,2),(20,4)),((0,3),(6,16))),
    (((0,6),(16,10)),((0,8),(3,16))),
    (((0,2),(13,13)),((0,15),(17,4))),
    (((0,5),(14,12)),((0,6),(15,11))),
    (((0,10),(11,13)),((0,12),(4,15))),
    (((0,9),(17,8)),((0,10),(9,14))),
    (((0,29),(2,2)),((1,10),(11,13))),
    (((0,7),(8,15)),((0,9),(13,12))),
    (((0,3),(20,4)),((0,4),(9,15))),
    (((0,28),(1,5)),((1,7),(8,15))),
    (((0,3),(13,13)),((0,9),(7,15))),
    (((0,4),(6,16)),((0,4),(18,8))),
    (((0,5),(11,14)),((0,10),(16,9))),
    (((0,7),(20,2)),((0,10),(14,11))),
    (((0,6),(17,9)),((0,19),(15,4))),
    (((0,8),(20,0)),((0,24),(12,0))),
    (((0,8),(18,7)),((0,15),(10,12))),
    (((0,6),(20,3)),((0,8),(19,5))),
    (((1,8),(18,7)),((1,15),(10,12))),
    (((0,4),(20,4)),((0,8),(12,13))),
    (((0,6),(14,12)),((0,12),(8,14))),
    (((0,0),(0,17)),((0,4),(13,13))),
    (((0,5),(9,15)),((0,13),(14,10))),
    (((0,1),(0,17)),((0,7),(15,11))),
    (((1,5),(9,15)),((1,13),(14,10))),
    (((0,0),(1,17)),((0,0),(7,16))),
    (((0,10),(0,16)),((0,19),(0,13))),
    (((0,1),(1,17)),((0,1),(7,16))),
    (((0,0),(19,7)),((0,2),(0,17))),
    (((0,6),(11,14)),((0,11),(19,3))),
    (((0,1),(19,7)),((0,8),(8,15))),
    (((0,11),(6,15)),((0,14),(0,15))),
    (((0,2),(1,17)),((0,2),(7,16))),
    (((0,5),(20,4)),((0,21),(0,12))),
    (((0,7),(17,9)),((0,9),(10,14))),
    (((0,0),(2,17)),((0,0),(20,5))),
    (((0,3),(0,17)),((0,8),(20,2)))]
  have hc : ∀ i : Fin 100, Good (1242+i.val) (c i).1 ∧
      Good (1242+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1242,by omega⟩
  have he : 1242+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1342 (n : ℕ) (hlo : 1342≤n) (hhi : n<1442) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(2,17)),((0,1),(20,5))),
    (((0,26),(10,1)),((1,3),(0,17))),
    (((0,0),(21,0)),((0,6),(9,15))),
    (((0,0),(10,15)),((0,0),(16,11))),
    (((0,1),(21,0)),((0,9),(20,0))),
    (((0,0),(12,14)),((0,1),(10,15))),
    (((0,3),(19,7)),((0,9),(19,5))),
    (((0,0),(17,10)),((0,1),(12,14))),
    (((0,0),(21,1)),((0,7),(19,6))),
    (((0,1),(17,10)),((0,2),(21,0))),
    (((0,1),(21,1)),((0,2),(10,15))),
    (((1,1),(17,10)),((1,2),(21,0))),
    (((0,2),(12,14)),((0,7),(11,14))),
    (((0,3),(2,17)),((0,3),(20,5))),
    (((0,0),(3,17)),((0,0),(15,12))),
    (((0,2),(21,1)),((0,6),(13,13))),
    (((0,1),(3,17)),((0,1),(15,12))),
    (((0,3),(21,0)),((0,4),(19,7))),
    (((0,3),(10,15)),((0,3),(16,11))),
    (((0,9),(8,15)),((0,10),(3,16))),
    (((0,3),(12,14)),((0,8),(17,9))),
    (((0,2),(3,17)),((0,2),(15,12))),
    (((0,3),(17,10)),((0,7),(9,15))),
    (((0,0),(21,2)),((0,3),(21,1))),
    (((0,4),(2,17)),((0,4),(20,5))),
    (((0,1),(21,2)),((0,7),(6,16))),
    (((0,0),(18,9)),((0,8),(14,12))),
    (((0,12),(19,3)),((0,14),(15,9))),
    (((0,1),(18,9)),((0,4),(21,0))),
    (((0,3),(3,17)),((0,3),(15,12))),
    (((0,2),(21,2)),((0,16),(8,13))),
    (((0,4),(12,14)),((0,5),(19,7))),
    (((1,2),(21,2)),((1,16),(8,13))),
    (((0,2),(18,9)),((0,4),(17,10))),
    (((0,0),(8,16)),((0,4),(21,1))),
    (((0,7),(13,13)),((0,8),(11,14))),
    (((0,0),(4,17)),((0,1),(8,16))),
    (((0,10),(12,13)),((0,18),(17,0))),
    (((0,1),(4,17)),((0,3),(21,2))),
    (((0,10),(20,1)),((0,25),(8,7))),
    (((0,0),(14,13)),((0,4),(3,17))),
    (((0,2),(8,16)),((0,3),(18,9))),
    (((0,1),(14,13)),((0,5),(21,0))),
    (((0,2),(4,17)),((0,5),(10,15))),
    (((0,30),(0,2)),((1,1),(14,13))),
    (((0,5),(12,14)),((0,6),(1,17))),
    (((0,9),(17,9)),((0,14),(4,15))),
    (((0,0),(21,3)),((0,2),(14,13))),
    (((0,5),(21,1)),((0,6),(19,7))),
    (((0,0),(20,6)),((0,1),(21,3))),
    (((0,27),(6,6)),((1,5),(21,1))),
    (((0,1),(20,6)),((0,3),(4,17))),
    (((0,4),(18,9)),((0,9),(14,12))),
    (((0,30),(3,0)),((1,1),(20,6))),
    (((0,2),(21,3)),((0,5),(3,17))),
    (((0,3),(14,13)),((0,6),(2,17))),
    (((0,2),(20,6)),((0,8),(20,4))),
    (((0,9),(19,6)),((0,18),(16,5))),
    (((0,8),(13,13)),((0,11),(10,14))),
    (((0,6),(21,0)),((0,26),(11,0))),
    (((0,0),(19,8)),((0,4),(8,16))),
    (((0,7),(0,17)),((0,9),(11,14))),
    (((0,1),(19,8)),((0,3),(21,3))),
    (((0,5),(21,2)),((0,26),(0,9))),
    (((0,0),(5,17)),((0,3),(20,6))),
    (((0,6),(21,1)),((0,7),(1,17))),
    (((0,1),(5,17)),((0,4),(14,13))),
    (((0,0),(11,15)),((0,2),(19,8))),
    (((0,7),(19,7)),((0,15),(3,15))),
    (((0,1),(11,15)),((0,10),(5,16))),
    (((0,12),(2,16)),((0,15),(14,10))),
    (((0,2),(5,17)),((0,6),(3,17))),
    (((0,13),(11,13)),((0,30),(1,3))),
    (((0,4),(21,3)),((0,11),(4,16))),
    (((0,2),(11,15)),((0,5),(8,16))),
    (((0,3),(19,8)),((0,4),(20,6))),
    (((0,5),(4,17)),((0,17),(10,12))),
    (((0,25),(1,10)),((0,26),(2,9))),
    (((0,10),(20,3)),((0,20),(3,13))),
    (((0,3),(5,17)),((0,7),(21,0))),
    (((0,0),(21,4)),((0,5),(14,13))),
    (((0,0),(13,14)),((0,10),(14,12))),
    (((0,1),(21,4)),((0,3),(11,15))),
    (((0,1),(13,14)),((0,6),(18,9))),
    (((0,7),(17,10)),((0,8),(0,17))),
    (((0,7),(21,1)),((0,16),(0,15))),
    (((0,0),(9,16)),((0,4),(19,8))),
    (((0,2),(21,4)),((0,5),(21,3))),
    (((0,1),(9,16)),((0,2),(13,14))),
    (((0,5),(20,6)),((0,16),(1,15))),
    (((0,4),(5,17)),((0,10),(11,14))),
    (((0,6),(8,16)),((0,7),(3,17))),
    (((0,29),(5,4)),((1,4),(5,17))),
    (((0,2),(9,16)),((0,4),(11,15))),
    (((0,11),(16,10)),((0,13),(0,16))),
    (((0,3),(21,4)),((0,24),(0,11))),
    (((0,3),(13,14)),((0,11),(15,11))),
    (((0,6),(14,13)),((0,20),(16,3))),
    (((0,0),(6,17)),((0,8),(2,17))),
    (((0,16),(2,15)),((0,19),(17,1)))]
  have hc : ∀ i : Fin 100, Good (1342+i.val) (c i).1 ∧
      Good (1342+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1342,by omega⟩
  have he : 1342+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1442 (n : ℕ) (hlo : 1442≤n) (hhi : n<1542) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(6,17)),((0,5),(19,8))),
    (((0,3),(9,16)),((0,11),(5,16))),
    (((0,8),(21,0)),((0,12),(19,5))),
    (((0,0),(17,11)),((0,7),(18,9))),
    (((0,5),(5,17)),((0,6),(21,3))),
    (((0,1),(17,11)),((0,2),(6,17))),
    (((0,4),(21,4)),((0,6),(20,6))),
    (((0,4),(13,14)),((0,5),(11,15))),
    (((0,0),(16,12)),((0,8),(21,1))),
    (((0,0),(20,7)),((0,24),(2,11))),
    (((0,1),(16,12)),((0,2),(17,11))),
    (((0,1),(20,7)),((0,7),(8,16))),
    (((0,4),(9,16)),((0,19),(0,14))),
    (((0,0),(18,10)),((0,3),(6,17))),
    (((0,8),(3,17)),((0,8),(15,12))),
    (((0,1),(18,10)),((0,2),(16,12))),
    (((0,2),(20,7)),((0,19),(1,14))),
    (((0,6),(19,8)),((0,7),(14,13))),
    (((0,3),(17,11)),((0,11),(19,6))),
    (((0,29),(2,6)),((0,31),(1,0))),
    (((0,2),(18,10)),((0,5),(21,4))),
    (((0,5),(13,14)),((0,6),(5,17))),
    (((0,0),(21,5)),((0,11),(11,14))),
    (((0,3),(16,12)),((0,8),(21,2))),
    (((0,1),(21,5)),((0,3),(20,7))),
    (((0,24),(3,11)),((0,25),(4,10))),
    (((0,5),(9,16)),((0,7),(20,6))),
    (((0,19),(9,12)),((1,24),(3,11))),
    (((0,0),(15,13)),((0,3),(18,10))),
    (((0,2),(21,5)),((0,4),(17,11))),
    (((0,1),(15,13)),((0,19),(15,7))),
    (((0,9),(12,14)),((0,12),(15,11))),
    (((0,0),(22,0)),((0,11),(9,15))),
    (((0,9),(17,10)),((0,18),(8,13))),
    (((0,1),(22,0)),((0,4),(16,12))),
    (((0,2),(15,13)),((0,4),(20,7))),
    (((0,8),(4,17)),((0,12),(5,16))),
    (((0,0),(12,15)),((0,3),(21,5))),
    (((0,0),(7,17)),((0,0),(19,9))),
    (((0,1),(12,15)),((0,2),(22,0))),
    (((0,1),(7,17)),((0,1),(19,9))),
    (((0,7),(5,17)),((0,22),(5,12))),
    (((0,12),(17,9)),((0,13),(12,13))),
    (((0,0),(0,18)),((0,3),(15,13))),
    (((0,0),(10,16)),((0,2),(12,15))),
    (((0,1),(0,18)),((0,2),(7,17))),
    (((0,1),(10,16)),((0,10),(19,7))),
    (((0,0),(1,18)),((0,3),(22,0))),
    (((0,4),(21,5)),((0,5),(16,12))),
    (((0,1),(1,18)),((0,5),(20,7))),
    (((0,2),(0,18)),((0,15),(19,3))),
    (((0,2),(10,16)),((0,23),(10,9))),
    (((0,3),(12,15)),((0,9),(18,9))),
    (((0,0),(22,2)),((0,3),(7,17))),
    (((0,2),(1,18)),((0,4),(15,13))),
    (((0,1),(22,2)),((0,6),(6,17))),
    (((0,22),(8,11)),((1,2),(1,18))),
    (((0,0),(2,18)),((0,7),(21,4))),
    (((0,3),(0,18)),((0,4),(22,0))),
    (((0,1),(2,18)),((0,3),(10,16))),
    (((0,2),(22,2)),((0,6),(17,11))),
    (((1,1),(2,18)),((1,3),(10,16))),
    (((0,3),(1,18)),((0,5),(21,5))),
    (((0,0),(14,14)),((0,4),(12,15))),
    (((0,2),(2,18)),((0,4),(7,17))),
    (((0,1),(14,14)),((0,6),(16,12))),
    (((0,6),(20,7)),((0,9),(14,13))),
    (((0,8),(11,15)),((0,12),(9,15))),
    (((0,3),(22,2)),((0,5),(15,13))),
    (((0,4),(0,18)),((0,10),(3,17))),
    (((0,2),(14,14)),((0,4),(10,16))),
    (((0,11),(0,17)),((0,19),(17,4))),
    (((0,3),(2,18)),((0,5),(22,0))),
    (((0,0),(3,18)),((0,0),(21,6))),
    (((0,13),(5,16)),((0,23),(15,2))),
    (((0,1),(3,18)),((0,1),(21,6))),
    (((1,13),(5,16)),((1,23),(15,2))),
    (((0,0),(22,3)),((0,5),(12,15))),
    (((0,0),(20,8)),((0,3),(14,14))),
    (((0,1),(22,3)),((0,4),(22,2))),
    (((0,1),(20,8)),((0,2),(3,18))),
    (((0,8),(13,14)),((0,10),(18,9))),
    (((0,30),(6,3)),((1,1),(20,8))),
    (((0,4),(2,18)),((0,5),(0,18))),
    (((0,0),(8,17)),((0,2),(22,3))),
    (((0,2),(20,8)),((0,6),(15,13))),
    (((0,1),(8,17)),((0,7),(20,7))),
    (((0,5),(1,18)),((0,14),(4,16))),
    (((0,3),(3,18)),((0,3),(21,6))),
    (((0,4),(14,14)),((0,6),(22,0))),
    (((0,7),(18,10)),((0,9),(5,17))),
    (((0,2),(8,17)),((0,10),(4,17))),
    (((0,3),(22,3)),((0,11),(12,14))),
    (((0,3),(20,8)),((0,5),(22,2))),
    (((0,6),(12,15)),((0,11),(17,10))),
    (((0,0),(4,18)),((0,6),(7,17))),
    (((0,21),(8,12)),((0,27),(8,7))),
    (((0,1),(4,18)),((0,5),(2,18))),
    (((0,8),(6,17)),((0,23),(15,3))),
    (((0,3),(8,17)),((0,4),(3,18)))]
  have hc : ∀ i : Fin 100, Good (1442+i.val) (c i).1 ∧
      Good (1442+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1442,by omega⟩
  have he : 1442+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1542 (n : ℕ) (hlo : 1542≤n) (hhi : n<1642) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,6),(0,18)),((0,14),(20,2))),
    (((0,6),(10,16)),((0,11),(3,17))),
    (((0,2),(4,18)),((0,10),(21,3))),
    (((0,4),(22,3)),((0,5),(14,14))),
    (((0,4),(20,8)),((0,6),(1,18))),
    (((0,7),(15,13)),((0,13),(9,15))),
    (((0,9),(21,4)),((0,12),(0,17))),
    (((0,9),(13,14)),((0,23),(12,8))),
    (((0,0),(11,16)),((0,0),(17,12))),
    (((0,0),(18,11)),((0,7),(22,0))),
    (((0,0),(22,4)),((0,1),(11,16))),
    (((0,1),(18,11)),((0,16),(18,6))),
    (((0,1),(22,4)),((0,9),(9,16))),
    (((0,0),(13,15)),((0,5),(3,18))),
    (((0,6),(2,18)),((0,7),(12,15))),
    (((0,1),(13,15)),((0,2),(11,16))),
    (((0,2),(18,11)),((0,13),(20,4))),
    (((0,2),(22,4)),((0,5),(22,3))),
    (((0,5),(20,8)),((0,13),(13,13))),
    (((0,10),(5,17)),((0,27),(7,8))),
    (((0,2),(13,15)),((0,6),(14,14))),
    (((0,4),(4,18)),((0,7),(10,16))),
    (((0,0),(16,13)),((0,8),(21,5))),
    (((0,0),(5,18)),((0,3),(11,16))),
    (((0,1),(16,13)),((0,3),(18,11))),
    (((0,0),(19,10)),((0,1),(5,18))),
    (((0,16),(0,16)),((0,19),(6,14))),
    (((0,1),(19,10)),((0,11),(14,13))),
    (((0,3),(13,15)),((0,8),(15,13))),
    (((0,2),(16,13)),((0,9),(17,11))),
    (((0,2),(5,18)),((0,6),(3,18))),
    (((0,15),(4,16)),((0,23),(15,4))),
    (((0,2),(19,10)),((0,8),(22,0))),
    (((0,0),(21,7)),((0,21),(0,14))),
    (((0,4),(11,16)),((0,4),(17,12))),
    (((0,1),(21,7)),((0,4),(18,11))),
    (((0,0),(9,17)),((0,4),(22,4))),
    (((0,3),(16,13)),((0,8),(12,15))),
    (((0,1),(9,17)),((0,3),(5,18))),
    (((0,4),(13,15)),((0,9),(18,10))),
    (((0,2),(21,7)),((0,3),(19,10))),
    (((0,6),(8,17)),((0,10),(9,16))),
    (((1,2),(21,7)),((1,3),(19,10))),
    (((0,2),(9,17)),((0,8),(0,18))),
    (((0,8),(10,16)),((0,13),(0,17))),
    (((0,12),(21,2)),((0,24),(15,2))),
    (((0,14),(9,15)),((0,26),(0,11))),
    (((0,8),(1,18)),((0,11),(19,8))),
    (((0,3),(21,7)),((0,4),(16,13))),
    (((0,4),(5,18)),((0,5),(18,11))),
    (((0,5),(22,4)),((0,7),(3,18))),
    (((0,0),(15,14)),((0,3),(9,17))),
    (((0,0),(22,5)),((0,6),(4,18))),
    (((0,1),(15,14)),((0,5),(13,15))),
    (((0,1),(22,5)),((0,7),(22,3))),
    (((0,7),(20,8)),((0,17),(9,14))),
    (((0,0),(20,9)),((0,12),(8,16))),
    (((0,0),(6,18)),((0,8),(2,18))),
    (((0,1),(20,9)),((0,2),(15,14))),
    (((0,1),(6,18)),((0,2),(22,5))),
    (((0,26),(2,11)),((0,27),(3,10))),
    (((0,7),(8,17)),((0,17),(18,6))),
    (((0,4),(9,17)),((0,5),(16,13))),
    (((0,2),(20,9)),((0,5),(5,18))),
    (((0,2),(6,18)),((0,9),(7,17))),
    (((0,5),(19,10)),((0,6),(11,16))),
    (((0,3),(15,14)),((0,6),(18,11))),
    (((0,3),(22,5)),((0,6),(22,4))),
    (((0,0),(23,0)),((0,10),(18,10))),
    (((0,9),(0,18)),((0,12),(21,3))),
    (((0,1),(23,0)),((0,6),(13,15))),
    (((0,3),(20,9)),((0,12),(20,6))),
    (((0,3),(6,18)),((0,7),(4,18))),
    (((0,5),(21,7)),((0,8),(3,18))),
    (((0,0),(23,1)),((0,13),(3,17))),
    (((0,2),(23,0)),((0,30),(9,0))),
    (((0,1),(23,1)),((0,5),(9,17))),
    (((0,4),(15,14)),((0,8),(22,3))),
    (((0,0),(12,16)),((0,4),(22,5))),
    (((0,6),(16,13)),((0,9),(22,2))),
    (((0,1),(12,16)),((0,6),(5,18))),
    (((0,2),(23,1)),((0,30),(9,1))),
    (((0,4),(20,9)),((0,6),(19,10))),
    (((0,3),(23,0)),((0,4),(6,18))),
    (((0,8),(8,17)),((0,17),(17,8))),
    (((0,2),(12,16)),((0,7),(11,16))),
    (((0,7),(18,11)),((0,12),(5,17))),
    (((0,7),(22,4)),((0,10),(22,0))),
    (((0,25),(2,12)),((0,25),(14,4))),
    (((0,0),(23,2)),((0,3),(23,1))),
    (((0,6),(21,7)),((0,7),(13,15))),
    (((0,1),(23,2)),((0,5),(15,14))),
    (((0,5),(22,5)),((0,10),(12,15))),
    (((0,3),(12,16)),((0,6),(9,17))),
    (((0,0),(10,17)),((0,4),(23,0))),
    (((0,0),(14,15)),((0,8),(4,18))),
    (((0,1),(10,17)),((0,2),(23,2))),
    (((0,0),(7,18)),((0,1),(14,15))),
    (((0,10),(0,18)),((0,22),(0,14))),
    (((0,1),(7,18)),((0,7),(16,13)))]
  have hc : ∀ i : Fin 100, Good (1542+i.val) (c i).1 ∧
      Good (1542+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1542,by omega⟩
  have he : 1542+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1642 (n : ℕ) (hlo : 1642≤n) (hhi : n<1742) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,4),(23,1)),((0,7),(5,18))),
    (((0,2),(10,17)),((0,15),(20,4))),
    (((0,0),(21,8)),((0,2),(14,15))),
    (((0,0),(22,6)),((0,9),(22,3))),
    (((0,1),(21,8)),((0,2),(7,18))),
    (((0,1),(22,6)),((0,29),(8,6))),
    (((0,14),(12,14)),((0,16),(5,16))),
    (((0,13),(21,3)),((0,18),(11,13))),
    (((0,5),(23,0)),((0,6),(15,14))),
    (((0,2),(21,8)),((0,3),(10,17))),
    (((0,2),(22,6)),((0,3),(14,15))),
    (((0,0),(0,19)),((0,19),(19,0))),
    (((0,3),(7,18)),((0,10),(2,18))),
    (((0,0),(23,3)),((0,1),(0,19))),
    (((0,0),(18,12)),((0,5),(23,1))),
    (((0,0),(1,19)),((0,1),(23,3))),
    (((0,1),(18,12)),((0,18),(14,11))),
    (((0,1),(1,19)),((0,3),(21,8))),
    (((0,2),(0,19)),((0,3),(22,6))),
    (((0,11),(22,0)),((0,19),(12,12))),
    (((0,2),(23,3)),((0,4),(10,17))),
    (((0,0),(19,11)),((0,2),(18,12))),
    (((0,0),(17,13)),((0,2),(1,19))),
    (((0,1),(19,11)),((0,4),(7,18))),
    (((0,1),(17,13)),((0,11),(12,15))),
    (((0,0),(2,19)),((0,6),(23,0))),
    (((0,3),(0,19)),((0,17),(20,1))),
    (((0,1),(2,19)),((0,13),(11,15))),
    (((0,2),(19,11)),((0,3),(23,3))),
    (((0,2),(17,13)),((0,3),(18,12))),
    (((0,3),(1,19)),((0,11),(0,18))),
    (((0,6),(23,1)),((0,11),(10,16))),
    (((0,2),(2,19)),((0,10),(22,3))),
    (((0,7),(20,9)),((0,8),(21,7))),
    (((0,5),(10,17)),((0,7),(6,18))),
    (((0,5),(14,15)),((0,6),(12,16))),
    (((0,3),(19,11)),((0,8),(9,17))),
    (((0,3),(17,13)),((0,4),(0,19))),
    (((0,31),(4,6)),((0,33),(3,0))),
    (((0,4),(23,3)),((0,9),(13,15))),
    (((0,3),(2,19)),((0,4),(18,12))),
    (((0,0),(3,19)),((0,4),(1,19))),
    (((0,5),(21,8)),((0,18),(7,15))),
    (((0,0),(8,18)),((0,0),(20,10))),
    (((0,11),(2,18)),((0,12),(21,5))),
    (((0,0),(16,14)),((0,1),(8,18))),
    (((0,0),(23,4)),((0,6),(23,2))),
    (((0,1),(16,14)),((0,4),(19,11))),
    (((0,1),(23,4)),((0,2),(3,19))),
    (((0,9),(5,18)),((0,17),(16,10))),
    (((0,2),(8,18)),((0,2),(20,10))),
    (((0,4),(2,19)),((0,5),(0,19))),
    (((0,2),(16,14)),((0,6),(14,15))),
    (((0,2),(23,4)),((0,5),(23,3))),
    (((0,0),(13,16)),((0,5),(18,12))),
    (((0,5),(1,19)),((0,7),(12,16))),
    (((0,1),(13,16)),((0,3),(3,19))),
    (((0,8),(6,18)),((0,22),(17,4))),
    (((0,0),(11,17)),((0,3),(8,18))),
    (((0,6),(21,8)),((0,9),(21,7))),
    (((0,1),(11,17)),((0,3),(16,14))),
    (((0,2),(13,16)),((0,3),(23,4))),
    (((0,5),(17,13)),((0,9),(9,17))),
    (((0,0),(4,19)),((0,0),(22,7))),
    (((0,10),(18,11)),((0,11),(22,3))),
    (((0,1),(4,19)),((0,1),(22,7))),
    (((0,7),(23,2)),((0,12),(10,16))),
    (((0,4),(3,19)),((0,23),(16,5))),
    (((0,6),(0,19)),((0,8),(23,0))),
    (((0,3),(13,16)),((0,4),(8,18))),
    (((0,2),(4,19)),((0,2),(22,7))),
    (((0,4),(16,14)),((0,6),(18,12))),
    (((0,4),(23,4)),((0,6),(1,19))),
    (((0,3),(11,17)),((0,13),(18,10))),
    (((0,7),(7,18)),((0,8),(23,1))),
    (((0,12),(22,2)),((0,18),(19,5))),
    (((0,16),(0,17)),((0,20),(19,1))),
    (((0,9),(15,14)),((0,10),(16,13))),
    (((0,3),(4,19)),((0,3),(22,7))),
    (((0,6),(17,13)),((0,7),(21,8))),
    (((0,0),(21,9)),((0,4),(13,16))),
    (((0,5),(3,19)),((0,14),(21,4))),
    (((0,1),(21,9)),((0,6),(2,19))),
    (((0,0),(15,15)),((0,5),(8,18))),
    (((0,4),(11,17)),((0,23),(15,7))),
    (((0,1),(15,15)),((0,5),(16,14))),
    (((0,5),(23,4)),((0,29),(11,4))),
    (((0,2),(21,9)),((0,14),(9,16))),
    (((0,0),(23,5)),((0,7),(0,19))),
    (((0,4),(4,19)),((0,4),(22,7))),
    (((0,1),(23,5)),((0,2),(15,15))),
    (((0,0),(5,19)),((0,7),(18,12))),
    (((0,7),(1,19)),((0,13),(22,0))),
    (((0,1),(5,19)),((0,19),(17,8))),
    (((0,5),(13,16)),((0,8),(10,17))),
    (((0,0),(9,18)),((0,2),(23,5))),
    (((0,11),(18,11)),((0,23),(3,14))),
    (((0,1),(9,18)),((0,8),(7,18))),
    (((0,2),(5,19)),((0,3),(15,15))),
    (((0,7),(17,13)),((0,12),(22,3)))]
  have hc : ∀ i : Fin 100, Good (1642+i.val) (c i).1 ∧
      Good (1642+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1642,by omega⟩
  have he : 1642+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1742 (n : ℕ) (hlo : 1742≤n) (hhi : n<1842) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,6),(8,18)),((0,6),(20,10))),
    (((0,30),(0,9)),((1,7),(17,13))),
    (((0,2),(9,18)),((0,6),(16,14))),
    (((0,3),(23,5)),((0,5),(4,19))),
    (((0,9),(12,16)),((0,13),(10,16))),
    (((0,15),(19,8)),((0,24),(10,11))),
    (((0,3),(5,19)),((0,4),(21,9))),
    (((0,10),(22,5)),((0,13),(1,18))),
    (((0,30),(7,7)),((1,3),(5,19))),
    (((0,4),(15,15)),((0,11),(16,13))),
    (((0,0),(24,0)),((0,3),(9,18))),
    (((0,6),(13,16)),((0,8),(0,19))),
    (((0,1),(24,0)),((0,10),(6,18))),
    (((0,8),(23,3)),((0,13),(22,2))),
    (((0,4),(23,5)),((0,8),(18,12))),
    (((0,6),(11,17)),((0,8),(1,19))),
    (((0,0),(24,1)),((0,32),(8,1))),
    (((0,2),(24,0)),((0,4),(5,19))),
    (((0,1),(24,1)),((0,7),(3,19))),
    (((0,31),(1,8)),((0,34),(1,1))),
    (((0,5),(21,9)),((0,6),(4,19))),
    (((0,4),(9,18)),((0,8),(19,11))),
    (((0,7),(16,14)),((0,8),(17,13))),
    (((0,2),(24,1)),((0,5),(15,15))),
    (((0,24),(17,1)),((1,7),(16,14))),
    (((0,0),(6,19)),((0,3),(24,0))),
    (((0,0),(19,12)),((0,15),(13,14))),
    (((0,1),(6,19)),((0,22),(9,13))),
    (((0,0),(12,17)),((0,0),(18,13))),
    (((0,9),(22,6)),((0,10),(23,1))),
    (((0,1),(12,17)),((0,1),(18,13))),
    (((0,0),(24,2)),((0,3),(24,1))),
    (((0,0),(22,8)),((0,2),(6,19))),
    (((0,1),(24,2)),((0,2),(19,12))),
    (((0,1),(22,8)),((0,22),(1,15))),
    (((0,2),(12,17)),((0,2),(18,13))),
    (((0,0),(14,16)),((0,4),(24,0))),
    (((0,6),(21,9)),((0,9),(0,19))),
    (((0,1),(14,16)),((0,2),(24,2))),
    (((0,0),(20,11)),((0,0),(23,6))),
    (((0,3),(6,19)),((0,6),(15,15))),
    (((0,1),(20,11)),((0,1),(23,6))),
    (((0,4),(24,1)),((0,30),(11,3))),
    (((0,2),(14,16)),((0,3),(12,17))),
    (((0,10),(23,2)),((0,11),(6,18))),
    (((0,0),(17,14)),((0,6),(23,5))),
    (((0,2),(20,11)),((0,2),(23,6))),
    (((0,1),(17,14)),((0,3),(22,8))),
    (((0,6),(5,19)),((0,9),(17,13))),
    (((0,10),(10,17)),((0,17),(17,10))),
    (((0,5),(24,0)),((0,10),(14,15))),
    (((0,3),(14,16)),((0,4),(6,19))),
    (((0,2),(17,14)),((0,4),(19,12))),
    (((0,0),(10,18)),((0,15),(16,12))),
    (((0,3),(20,11)),((0,3),(23,6))),
    (((0,0),(24,3)),((0,1),(10,18))),
    (((0,5),(24,1)),((0,16),(5,17))),
    (((0,1),(24,3)),((0,4),(24,2))),
    (((0,4),(22,8)),((0,8),(11,17))),
    (((0,16),(11,15)),((0,23),(18,1))),
    (((0,2),(10,18)),((0,3),(17,14))),
    (((0,11),(23,1)),((0,27),(3,12))),
    (((0,2),(24,3)),((0,4),(14,16))),
    (((0,8),(4,19)),((0,8),(22,7))),
    (((0,14),(14,14)),((1,2),(24,3))),
    (((0,0),(7,19)),((0,4),(20,11))),
    (((0,5),(19,12)),((0,10),(0,19))),
    (((0,0),(21,10)),((0,1),(7,19))),
    (((0,3),(10,18)),((0,5),(12,17))),
    (((0,1),(21,10)),((0,9),(8,18))),
    (((0,3),(24,3)),((0,10),(1,19))),
    (((0,4),(17,14)),((0,5),(24,2))),
    (((0,2),(7,19)),((0,5),(22,8))),
    (((0,6),(24,1)),((0,12),(15,14))),
    (((0,2),(21,10)),((0,12),(22,5))),
    (((0,26),(16,1)),((0,29),(10,7))),
    (((0,5),(14,16)),((0,10),(19,11))),
    (((0,0),(16,15)),((0,10),(17,13))),
    (((0,12),(20,9)),((0,14),(22,3))),
    (((0,1),(16,15)),((0,4),(10,18))),
    (((0,3),(7,19)),((0,8),(21,9))),
    (((0,4),(24,3)),((0,11),(10,17))),
    (((0,3),(21,10)),((0,6),(6,19))),
    (((0,6),(19,12)),((0,8),(15,15))),
    (((0,2),(16,15)),((0,9),(11,17))),
    (((0,5),(17,14)),((0,6),(12,17))),
    (((0,18),(19,7)),((0,19),(11,14))),
    (((0,7),(24,0)),((0,27),(14,5))),
    (((0,0),(0,20)),((0,0),(24,4))),
    (((0,6),(22,8)),((0,9),(4,19))),
    (((0,1),(0,20)),((0,1),(24,4))),
    (((0,4),(7,19)),((0,8),(5,19))),
    (((0,0),(1,20)),((0,3),(16,15))),
    (((0,4),(21,10)),((0,5),(10,18))),
    (((0,1),(1,20)),((0,20),(20,1))),
    (((0,2),(0,20)),((0,2),(24,4))),
    (((0,6),(20,11)),((0,6),(23,6))),
    (((0,18),(21,0)),((0,22),(19,0))),
    (((0,10),(8,18)),((0,10),(20,10))),
    (((0,0),(23,7)),((0,2),(1,20)))]
  have hc : ∀ i : Fin 100, Good (1742+i.val) (c i).1 ∧
      Good (1742+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1742,by omega⟩
  have he : 1742+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1842 (n : ℕ) (hlo : 1842≤n) (hhi : n<1942) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,10),(16,14)),((0,11),(23,3))),
    (((0,1),(23,7)),((0,10),(23,4))),
    (((0,0),(2,20)),((0,6),(17,14))),
    (((0,3),(0,20)),((0,3),(24,4))),
    (((0,0),(13,17)),((0,1),(2,20))),
    (((0,5),(7,19)),((0,7),(12,17))),
    (((0,1),(13,17)),((0,2),(23,7))),
    (((0,3),(1,20)),((0,5),(21,10))),
    (((0,7),(24,2)),((0,11),(19,11))),
    (((0,2),(2,20)),((0,7),(22,8))),
    (((0,0),(22,9)),((0,6),(10,18))),
    (((0,0),(8,19)),((0,2),(13,17))),
    (((0,1),(22,9)),((0,6),(24,3))),
    (((0,1),(8,19)),((0,7),(14,16))),
    (((0,3),(23,7)),((0,4),(0,20))),
    (((0,25),(1,14)),((0,30),(6,9))),
    (((0,7),(20,11)),((0,7),(23,6))),
    (((0,0),(11,18)),((0,2),(22,9))),
    (((0,0),(3,20)),((0,2),(8,19))),
    (((0,1),(11,18)),((0,3),(13,17))),
    (((0,1),(3,20)),((0,16),(15,13))),
    (((0,9),(9,18)),((0,18),(18,9))),
    (((0,6),(7,19)),((0,7),(17,14))),
    (((0,14),(16,13)),((0,15),(20,8))),
    (((0,0),(15,16)),((0,2),(11,18))),
    (((0,2),(3,20)),((0,3),(22,9))),
    (((0,1),(15,16)),((0,3),(8,19))),
    (((0,35),(2,0)),((1,2),(3,20))),
    (((0,4),(2,20)),((0,5),(0,20))),
    (((0,15),(8,17)),((0,16),(12,15))),
    (((0,0),(24,5)),((0,4),(13,17))),
    (((0,2),(15,16)),((0,8),(24,2))),
    (((0,1),(24,5)),((0,3),(11,18))),
    (((0,3),(3,20)),((0,11),(23,4))),
    (((0,6),(16,15)),((0,13),(23,1))),
    (((0,10),(21,9)),((0,12),(23,3))),
    (((0,4),(22,9)),((0,8),(14,16))),
    (((0,2),(24,5)),((0,4),(8,19))),
    (((0,10),(15,15)),((0,13),(12,16))),
    (((0,3),(15,16)),((0,5),(23,7))),
    (((0,0),(4,20)),((0,0),(19,13))),
    (((0,11),(13,16)),((0,20),(19,6))),
    (((0,1),(4,20)),((0,1),(19,13))),
    (((0,4),(11,18)),((0,10),(23,5))),
    (((0,0),(20,12)),((0,4),(3,20))),
    (((0,3),(24,5)),((0,6),(0,20))),
    (((0,1),(20,12)),((0,10),(5,19))),
    (((0,2),(4,20)),((0,2),(19,13))),
    (((0,35),(2,2)),((1,1),(20,12))),
    (((0,6),(1,20)),((0,13),(23,2))),
    (((0,4),(15,16)),((0,5),(22,9))),
    (((0,0),(18,14)),((0,2),(20,12))),
    (((0,9),(19,12)),((0,14),(15,14))),
    (((0,1),(18,14)),((0,8),(10,18))),
    (((0,7),(16,15)),((0,9),(12,17))),
    (((0,3),(4,20)),((0,3),(19,13))),
    (((0,4),(24,5)),((0,6),(23,7))),
    (((0,5),(11,18)),((0,9),(24,2))),
    (((0,0),(25,0)),((0,2),(18,14))),
    (((0,3),(20,12)),((0,6),(2,20))),
    (((0,1),(25,0)),((0,33),(9,0))),
    (((0,6),(13,17)),((1,3),(20,12))),
    (((0,9),(14,16)),((0,13),(21,8))),
    (((0,0),(9,19)),((0,0),(21,11))),
    (((0,0),(25,1)),((0,5),(15,16))),
    (((0,1),(9,19)),((0,1),(21,11))),
    (((0,1),(25,1)),((0,3),(18,14))),
    (((0,6),(22,9)),((0,8),(21,10))),
    (((0,0),(5,20)),((0,0),(23,8))),
    (((0,7),(1,20)),((0,14),(23,0))),
    (((0,1),(5,20)),((0,1),(23,8))),
    (((0,2),(25,1)),((0,9),(17,14))),
    (((0,35),(2,3)),((1,1),(5,20))),
    (((0,3),(25,0)),((0,13),(23,3))),
    (((0,6),(11,18)),((0,13),(18,12))),
    (((0,2),(5,20)),((0,2),(23,8))),
    (((0,7),(23,7)),((0,12),(13,16))),
    (((0,0),(17,15)),((0,4),(18,14))),
    (((0,3),(9,19)),((0,3),(21,11))),
    (((0,0),(25,2)),((0,1),(17,15))),
    (((0,5),(4,20)),((0,5),(19,13))),
    (((0,0),(24,6)),((0,1),(25,2))),
    (((0,11),(9,18)),((0,13),(17,13))),
    (((0,1),(24,6)),((0,3),(5,20))),
    (((0,2),(17,15)),((0,4),(25,0))),
    (((0,12),(4,19)),((0,12),(22,7))),
    (((0,0),(14,17)),((0,2),(25,2))),
    (((0,0),(12,18)),((0,6),(24,5))),
    (((0,1),(14,17)),((0,2),(24,6))),
    (((0,1),(12,18)),((0,4),(9,19))),
    (((0,4),(25,1)),((0,14),(23,2))),
    (((0,5),(18,14)),((0,9),(7,19))),
    (((0,3),(17,15)),((0,8),(1,20))),
    (((0,2),(14,17)),((0,9),(21,10))),
    (((0,2),(12,18)),((0,3),(25,2))),
    (((0,7),(3,20)),((0,14),(10,17))),
    (((0,3),(24,6)),((0,14),(14,15))),
    (((0,0),(22,10)),((0,6),(4,20))),
    (((0,5),(25,0)),((0,14),(7,18))),
    (((0,1),(22,10)),((0,8),(23,7)))]
  have hc : ∀ i : Fin 100, Good (1842+i.val) (c i).1 ∧
      Good (1842+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1842,by omega⟩
  have he : 1842+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_1942 (n : ℕ) (hlo : 1942≤n) (hhi : n<2042) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,10),(17,14)),((0,16),(11,16))),
    (((0,3),(14,17)),((0,6),(20,12))),
    (((0,0),(6,20)),((0,3),(12,18))),
    (((0,0),(25,3)),((0,4),(17,15))),
    (((0,1),(6,20)),((0,2),(22,10))),
    (((0,1),(25,3)),((0,4),(25,2))),
    (((0,13),(23,4)),((0,26),(15,7))),
    (((0,4),(24,6)),((0,7),(24,5))),
    (((0,5),(5,20)),((0,5),(23,8))),
    (((0,2),(6,20)),((0,28),(8,11))),
    (((0,2),(25,3)),((0,8),(22,9))),
    (((0,8),(8,19)),((0,19),(19,8))),
    (((0,3),(22,10)),((0,4),(14,17))),
    (((0,4),(12,18)),((0,11),(19,12))),
    (((0,9),(0,20)),((0,9),(24,4))),
    (((0,6),(25,0)),((0,11),(12,17))),
    (((0,14),(1,19)),((0,22),(18,7))),
    (((0,3),(6,20)),((0,5),(17,15))),
    (((0,0),(16,16)),((0,3),(25,3))),
    (((0,5),(25,2)),((0,11),(22,8))),
    (((0,1),(16,16)),((0,6),(9,19))),
    (((0,0),(10,19)),((0,5),(24,6))),
    (((0,10),(21,10)),((0,14),(19,11))),
    (((0,1),(10,19)),((0,4),(22,10))),
    (((0,8),(15,16)),((0,20),(3,17))),
    (((0,2),(16,16)),((0,6),(5,20))),
    (((0,5),(14,17)),((0,11),(20,11))),
    (((0,5),(12,18)),((0,18),(22,0))),
    (((0,2),(10,19)),((0,4),(6,20))),
    (((0,4),(25,3)),((0,32),(11,3))),
    (((0,8),(24,5)),((0,9),(13,17))),
    (((0,19),(21,4)),((0,27),(8,12))),
    (((0,10),(16,15)),((0,11),(17,14))),
    (((0,3),(16,16)),((0,18),(7,17))),
    (((0,6),(17,15)),((0,15),(23,2))),
    (((0,7),(25,0)),((0,31),(13,0))),
    (((0,0),(25,4)),((0,3),(10,19))),
    (((0,5),(22,10)),((0,9),(8,19))),
    (((0,1),(25,4)),((0,6),(24,6))),
    (((0,15),(10,17)),((0,18),(10,16))),
    (((0,7),(9,19)),((0,7),(21,11))),
    (((0,0),(24,7)),((0,7),(25,1))),
    (((0,0),(7,20)),((0,5),(6,20))),
    (((0,1),(24,7)),((0,2),(25,4))),
    (((0,1),(7,20)),((0,4),(16,16))),
    (((0,7),(5,20)),((0,7),(23,8))),
    (((0,0),(23,9)),((0,14),(16,14))),
    (((0,4),(10,19)),((0,10),(1,20))),
    (((0,1),(23,9)),((0,2),(24,7))),
    (((0,2),(7,20)),((0,16),(6,18))),
    (((0,9),(15,16)),((0,12),(12,17))),
    (((0,3),(25,4)),((0,8),(18,14))),
    (((0,11),(7,19)),((0,17),(22,4))),
    (((0,2),(23,9)),((0,12),(24,2))),
    (((0,6),(22,10)),((0,7),(17,15))),
    (((0,13),(9,18)),((0,14),(13,16))),
    (((0,3),(24,7)),((0,7),(25,2))),
    (((0,3),(7,20)),((0,10),(2,20))),
    (((0,0),(20,13)),((0,5),(16,16))),
    (((0,6),(6,20)),((0,10),(13,17))),
    (((0,1),(20,13)),((0,6),(25,3))),
    (((0,3),(23,9)),((0,5),(10,19))),
    (((0,4),(25,4)),((0,32),(11,4))),
    (((0,0),(13,18)),((0,0),(19,14))),
    (((0,7),(12,18)),((0,8),(25,1))),
    (((0,1),(13,18)),((0,1),(19,14))),
    (((0,9),(4,20)),((0,9),(19,13))),
    (((0,4),(24,7)),((0,12),(17,14))),
    (((0,0),(21,12)),((0,4),(7,20))),
    (((0,23),(3,16)),((0,27),(16,5))),
    (((0,1),(21,12)),((0,2),(13,18))),
    (((0,35),(5,4)),((0,36),(3,2))),
    (((0,4),(23,9)),((0,10),(11,18))),
    (((0,3),(20,13)),((0,10),(3,20))),
    (((0,0),(0,21)),((0,0),(15,17))),
    (((0,2),(21,12)),((0,6),(16,16))),
    (((0,1),(0,21)),((0,1),(15,17))),
    (((0,8),(17,15)),((0,9),(18,14))),
    (((0,0),(1,21)),((0,0),(25,5))),
    (((0,7),(6,20)),((0,8),(25,2))),
    (((0,1),(1,21)),((0,1),(25,5))),
    (((0,2),(0,21)),((0,2),(15,17))),
    (((0,5),(7,20)),((0,22),(9,15))),
    (((0,0),(18,15)),((0,3),(21,12))),
    (((0,4),(20,13)),((0,9),(25,0))),
    (((0,0),(11,19)),((0,1),(18,15))),
    (((0,5),(23,9)),((0,8),(14,17))),
    (((0,1),(11,19)),((0,8),(12,18))),
    (((0,0),(2,21)),((0,0),(8,20))),
    (((0,3),(0,21)),((0,3),(15,17))),
    (((0,1),(2,21)),((0,1),(8,20))),
    (((0,11),(13,17)),((0,13),(24,2))),
    (((0,2),(11,19)),((0,13),(22,8))),
    (((0,0),(22,11)),((0,3),(1,21))),
    (((0,4),(21,12)),((0,9),(5,20))),
    (((0,1),(22,11)),((0,2),(2,21))),
    (((0,13),(14,16)),((0,14),(9,18))),
    (((0,8),(22,10)),((0,11),(22,9))),
    (((0,3),(18,15)),((0,5),(20,13))),
    (((0,6),(7,20)),((0,10),(20,12)))]
  have hc : ∀ i : Fin 100, Good (1942+i.val) (c i).1 ∧
      Good (1942+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-1942,by omega⟩
  have he : 1942+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2042 (n : ℕ) (hlo : 2042≤n) (hhi : n<2142) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(22,11)),((0,3),(11,19))),
    (((1,6),(7,20)),((1,10),(20,12))),
    (((0,8),(6,20)),((0,26),(6,14))),
    (((0,3),(2,21)),((0,3),(8,20))),
    (((0,0),(3,21)),((0,4),(1,21))),
    (((0,9),(25,2)),((0,11),(3,20))),
    (((0,1),(3,21)),((0,10),(18,14))),
    (((0,9),(24,6)),((0,16),(1,19))),
    (((0,3),(22,11)),((0,5),(21,12))),
    (((0,4),(18,15)),((0,28),(15,6))),
    (((0,0),(24,8)),((0,12),(0,20))),
    (((0,2),(3,21)),((0,4),(11,19))),
    (((0,0),(26,0)),((0,1),(24,8))),
    (((0,7),(25,4)),((0,9),(12,18))),
    (((0,1),(26,0)),((0,4),(2,21))),
    (((0,6),(20,13)),((0,13),(24,3))),
    (((0,17),(23,1)),((0,25),(19,1))),
    (((0,2),(24,8)),((0,11),(24,5))),
    (((0,0),(17,16)),((0,0),(26,1))),
    (((0,2),(26,0)),((0,3),(3,21))),
    (((0,1),(17,16)),((0,1),(26,1))),
    (((0,8),(10,19)),((0,12),(23,7))),
    (((0,33),(6,8)),((1,1),(17,16))),
    (((0,5),(18,15)),((0,7),(23,9))),
    (((0,12),(2,20)),((0,19),(3,18))),
    (((0,2),(17,16)),((0,2),(26,1))),
    (((0,0),(4,21)),((0,12),(13,17))),
    (((0,3),(26,0)),((0,11),(4,20))),
    (((0,1),(4,21)),((0,5),(2,21))),
    (((0,0),(25,6)),((0,9),(25,3))),
    (((0,4),(3,21)),((0,31),(12,6))),
    (((0,1),(25,6)),((0,6),(0,21))),
    (((0,10),(17,15)),((0,12),(22,9))),
    (((0,0),(23,10)),((0,0),(26,2))),
    (((0,10),(25,2)),((0,26),(2,15))),
    (((0,1),(23,10)),((0,1),(26,2))),
    (((0,2),(25,6)),((0,4),(24,8))),
    (((0,13),(16,15)),((0,14),(14,16))),
    (((0,4),(26,0)),((0,11),(18,14))),
    (((0,12),(11,18)),((0,17),(7,18))),
    (((0,0),(9,20)),((0,2),(23,10))),
    (((0,3),(4,21)),((0,8),(24,7))),
    (((0,1),(9,20)),((0,6),(11,19))),
    (((1,3),(4,21)),((1,8),(24,7))),
    (((0,3),(25,6)),((0,4),(17,16))),
    (((0,0),(14,18)),((0,6),(2,21))),
    (((0,8),(23,9)),((0,12),(15,16))),
    (((0,1),(14,18)),((0,2),(9,20))),
    (((0,3),(23,10)),((0,3),(26,2))),
    (((1,1),(14,18)),((1,2),(9,20))),
    (((0,5),(24,8)),((0,6),(22,11))),
    (((0,7),(0,21)),((0,7),(15,17))),
    (((0,2),(14,18)),((0,4),(4,21))),
    (((0,17),(0,19)),((0,20),(0,18))),
    (((0,0),(5,21)),((0,14),(10,18))),
    (((0,0),(12,19)),((0,3),(9,20))),
    (((0,1),(5,21)),((0,14),(24,3))),
    (((0,0),(26,3)),((0,1),(12,19))),
    (((0,5),(17,16)),((0,5),(26,1))),
    (((0,1),(26,3)),((0,4),(23,10))),
    (((0,3),(14,18)),((0,7),(18,15))),
    (((0,2),(5,21)),((0,6),(3,21))),
    (((0,2),(12,19)),((0,7),(11,19))),
    (((0,8),(13,18)),((0,8),(19,14))),
    (((0,2),(26,3)),((0,11),(17,15))),
    (((0,7),(2,21)),((0,7),(8,20))),
    (((0,4),(9,20)),((0,5),(4,21))),
    (((0,6),(24,8)),((0,9),(24,7))),
    (((0,0),(16,17)),((0,8),(21,12))),
    (((0,3),(5,21)),((0,5),(25,6))),
    (((0,1),(16,17)),((0,3),(12,19))),
    (((0,4),(14,18)),((0,13),(8,19))),
    (((0,3),(26,3)),((0,9),(23,9))),
    (((0,5),(23,10)),((0,5),(26,2))),
    (((0,8),(0,21)),((0,8),(15,17))),
    (((0,2),(16,17)),((0,6),(17,16))),
    (((0,10),(10,19)),((0,15),(24,2))),
    (((0,13),(11,18)),((0,15),(22,8))),
    (((0,8),(1,21)),((0,8),(25,5))),
    (((0,36),(6,3)),((0,37),(1,3))),
    (((0,4),(5,21)),((0,5),(9,20))),
    (((0,0),(20,14)),((0,4),(12,19))),
    (((0,0),(21,13)),((0,27),(6,14))),
    (((0,1),(20,14)),((0,3),(16,17))),
    (((0,1),(21,13)),((0,9),(20,13))),
    (((0,5),(14,18)),((0,8),(11,19))),
    (((0,6),(25,6)),((0,12),(25,1))),
    (((0,7),(24,8)),((0,16),(9,18))),
    (((0,0),(6,21)),((0,0),(24,9))),
    (((0,0),(25,7)),((0,2),(21,13))),
    (((0,0),(26,4)),((0,1),(6,21))),
    (((0,1),(25,7)),((0,10),(25,4))),
    (((0,1),(26,4)),((0,18),(7,18))),
    (((0,8),(22,11)),((0,14),(1,20))),
    (((0,4),(16,17)),((0,5),(5,21))),
    (((0,0),(19,15)),((0,2),(6,21))),
    (((0,2),(25,7)),((0,3),(20,14))),
    (((0,1),(19,15)),((0,2),(26,4))),
    (((0,0),(10,20)),((0,0),(22,12))),
    (((0,12),(17,15)),((0,24),(20,3)))]
  have hc : ∀ i : Fin 100, Good (2042+i.val) (c i).1 ∧
      Good (2042+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2042,by omega⟩
  have he : 2042+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2142 (n : ℕ) (hlo : 2142≤n) (hhi : n<2242) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(10,20)),((0,1),(22,12))),
    (((0,10),(23,9)),((0,12),(25,2))),
    (((0,2),(19,15)),((0,6),(14,18))),
    (((0,3),(6,21)),((0,3),(24,9))),
    (((0,3),(25,7)),((0,8),(3,21))),
    (((0,2),(10,20)),((0,2),(22,12))),
    (((0,7),(25,6)),((0,18),(0,19))),
    (((0,4),(20,14)),((0,19),(20,9))),
    (((0,4),(21,13)),((0,5),(16,17))),
    (((0,9),(18,15)),((0,12),(12,18))),
    (((0,3),(19,15)),((0,7),(23,10))),
    (((0,6),(5,21)),((0,9),(11,19))),
    (((0,6),(12,19)),((0,8),(26,0))),
    (((0,3),(10,20)),((0,3),(22,12))),
    (((0,4),(6,21)),((0,4),(24,9))),
    (((0,4),(25,7)),((0,21),(0,18))),
    (((0,4),(26,4)),((0,18),(19,11))),
    (((0,7),(9,20)),((0,16),(6,19))),
    (((0,8),(17,16)),((0,8),(26,1))),
    (((0,9),(22,11)),((0,12),(22,10))),
    (((0,16),(12,17)),((0,16),(18,13))),
    (((0,4),(19,15)),((0,5),(20,14))),
    (((0,5),(21,13)),((0,7),(14,18))),
    (((0,10),(21,12)),((0,11),(25,4))),
    (((0,0),(18,16)),((0,4),(10,20))),
    (((0,6),(16,17)),((0,12),(25,3))),
    (((0,1),(18,16)),((0,8),(4,21))),
    (((0,35),(2,8)),((0,37),(4,3))),
    (((0,0),(7,21)),((0,5),(6,21))),
    (((0,0),(23,11)),((0,5),(25,7))),
    (((0,1),(7,21)),((0,5),(26,4))),
    (((0,0),(13,19)),((0,1),(23,11))),
    (((0,0),(26,5)),((0,7),(12,19))),
    (((0,0),(15,18)),((0,1),(13,19))),
    (((0,1),(26,5)),((0,7),(26,3))),
    (((0,1),(15,18)),((0,2),(7,21))),
    (((0,2),(23,11)),((0,9),(24,8))),
    (((0,13),(17,15)),((0,15),(1,20))),
    (((0,2),(13,19)),((0,5),(10,20))),
    (((0,2),(26,5)),((0,3),(18,16))),
    (((0,2),(15,18)),((0,8),(9,20))),
    (((0,13),(24,6)),((0,14),(4,20))),
    (((1,2),(15,18)),((1,8),(9,20))),
    (((0,3),(7,21)),((0,10),(2,21))),
    (((0,3),(23,11)),((0,9),(17,16))),
    (((0,6),(6,21)),((0,6),(24,9))),
    (((0,3),(13,19)),((0,6),(25,7))),
    (((0,3),(26,5)),((0,6),(26,4))),
    (((0,3),(15,18)),((0,10),(22,11))),
    (((0,15),(13,17)),((0,18),(13,16))),
    (((0,4),(18,16)),((0,11),(13,18))),
    (((0,29),(2,14)),((0,32),(5,11))),
    (((0,6),(19,15)),((0,9),(4,21))),
    (((0,18),(11,17)),((0,19),(21,8))),
    (((0,4),(7,21)),((0,8),(5,21))),
    (((0,4),(23,11)),((0,6),(10,20))),
    (((0,15),(8,19)),((0,21),(8,17))),
    (((0,4),(13,19)),((0,8),(26,3))),
    (((0,0),(25,8)),((0,4),(26,5))),
    (((0,4),(15,18)),((0,7),(21,13))),
    (((0,1),(25,8)),((0,24),(0,17))),
    (((0,11),(0,21)),((0,11),(15,17))),
    (((0,0),(11,20)),((0,13),(6,20))),
    (((0,12),(24,7)),((0,13),(25,3))),
    (((0,1),(11,20)),((0,5),(18,16))),
    (((0,2),(25,8)),((0,7),(6,21))),
    (((0,7),(25,7)),((0,9),(9,20))),
    (((0,7),(26,4)),((0,10),(26,0))),
    (((0,0),(17,17)),((0,5),(7,21))),
    (((0,0),(0,22)),((0,2),(11,20))),
    (((0,1),(17,17)),((0,11),(18,15))),
    (((0,1),(0,22)),((0,5),(13,19))),
    (((0,0),(27,0)),((0,5),(26,5))),
    (((0,0),(1,22)),((0,3),(25,8))),
    (((0,0),(8,21)),((0,1),(27,0))),
    (((0,0),(24,10)),((0,1),(1,22))),
    (((0,1),(8,21)),((0,2),(0,22))),
    (((0,1),(24,10)),((0,3),(11,20))),
    (((0,0),(27,1)),((0,13),(16,16))),
    (((0,2),(27,0)),((0,24),(10,15))),
    (((0,1),(27,1)),((0,2),(1,22))),
    (((0,2),(8,21)),((0,6),(18,16))),
    (((0,2),(24,10)),((0,8),(21,13))),
    (((0,0),(2,22)),((0,0),(26,6))),
    (((0,3),(0,22)),((0,4),(25,8))),
    (((0,1),(2,22)),((0,1),(26,6))),
    (((0,6),(23,11)),((0,18),(5,19))),
    (((0,3),(27,0)),((0,14),(14,17))),
    (((0,3),(1,22)),((0,4),(11,20))),
    (((0,3),(8,21)),((0,6),(26,5))),
    (((0,2),(2,22)),((0,2),(26,6))),
    (((0,11),(3,21)),((0,16),(23,7))),
    (((0,19),(3,19)),((0,34),(9,7))),
    (((0,0),(27,2)),((0,3),(27,1))),
    (((0,4),(17,17)),((0,9),(16,17))),
    (((0,1),(27,2)),((0,4),(0,22))),
    (((0,12),(0,21)),((0,12),(15,17))),
    (((0,11),(24,8)),((0,17),(24,3))),
    (((0,3),(2,22)),((0,3),(26,6))),
    (((0,0),(3,22)),((0,4),(1,22)))]
  have hc : ∀ i : Fin 100, Good (2142+i.val) (c i).1 ∧
      Good (2142+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2142,by omega⟩
  have he : 2142+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2242 (n : ℕ) (hlo : 2242≤n) (hhi : n<2342) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(27,2)),((0,4),(8,21))),
    (((0,1),(3,22)),((0,4),(24,10))),
    (((0,5),(11,20)),((0,13),(7,20))),
    (((0,14),(6,20)),((0,15),(25,0))),
    (((0,4),(27,1)),((0,14),(25,3))),
    (((0,0),(21,14)),((0,7),(7,21))),
    (((0,2),(3,22)),((0,7),(23,11))),
    (((0,1),(21,14)),((0,9),(20,14))),
    (((0,3),(27,2)),((0,5),(17,17))),
    (((0,4),(2,22)),((0,4),(26,6))),
    (((0,7),(15,18)),((0,10),(12,19))),
    (((0,18),(24,1)),((0,26),(20,1))),
    (((0,0),(22,13)),((0,2),(21,14))),
    (((0,0),(14,19)),((0,0),(20,15))),
    (((0,1),(22,13)),((0,3),(3,22))),
    (((0,1),(14,19)),((0,1),(20,15))),
    (((0,9),(26,4)),((0,11),(25,6))),
    (((0,0),(27,3)),((0,29),(5,14))),
    (((0,5),(27,1)),((0,13),(20,13))),
    (((0,1),(27,3)),((0,2),(22,13))),
    (((0,2),(14,19)),((0,2),(20,15))),
    (((0,0),(4,22)),((0,9),(19,15))),
    (((0,14),(10,19)),((0,15),(17,15))),
    (((0,1),(4,22)),((0,5),(2,22))),
    (((0,2),(27,3)),((0,8),(18,16))),
    (((0,4),(3,22)),((0,6),(17,17))),
    (((0,0),(9,21)),((0,6),(0,22))),
    (((0,0),(16,18)),((0,3),(22,13))),
    (((0,1),(9,21)),((0,2),(4,22))),
    (((0,1),(16,18)),((0,6),(27,0))),
    (((0,6),(1,22)),((0,17),(0,20))),
    (((0,4),(21,14)),((0,6),(8,21))),
    (((0,0),(12,20)),((0,3),(27,3))),
    (((0,2),(9,21)),((0,5),(27,2))),
    (((0,0),(23,12)),((0,1),(12,20))),
    (((0,6),(27,1)),((0,7),(25,8))),
    (((0,0),(19,16)),((0,0),(25,9))),
    (((0,10),(21,13)),((0,14),(25,4))),
    (((0,1),(19,16)),((0,1),(25,9))),
    (((0,2),(12,20)),((0,4),(14,19))),
    (((0,6),(2,22)),((0,6),(26,6))),
    (((0,2),(23,12)),((0,3),(9,21))),
    (((0,3),(16,18)),((0,11),(12,19))),
    (((0,0),(26,7)),((0,2),(19,16))),
    (((0,10),(25,7)),((0,11),(26,3))),
    (((0,1),(26,7)),((0,5),(21,14))),
    (((0,7),(0,22)),((0,17),(13,17))),
    (((0,3),(12,20)),((0,4),(4,22))),
    (((0,12),(4,21)),((0,13),(2,21))),
    (((0,0),(5,22)),((0,3),(23,12))),
    (((0,0),(27,4)),((0,2),(26,7))),
    (((0,1),(5,22)),((0,3),(19,16))),
    (((0,1),(27,4)),((0,4),(9,21))),
    (((0,4),(16,18)),((0,5),(14,19))),
    (((0,9),(7,21)),((0,27),(7,15))),
    (((0,7),(27,1)),((0,9),(23,11))),
    (((0,2),(5,22)),((0,6),(3,22))),
    (((0,2),(27,4)),((0,5),(27,3))),
    (((0,3),(26,7)),((0,4),(12,20))),
    (((0,9),(15,18)),((0,14),(20,13))),
    (((0,4),(23,12)),((0,7),(2,22))),
    (((0,5),(4,22)),((0,19),(24,0))),
    (((0,4),(19,16)),((0,4),(25,9))),
    (((0,15),(16,16)),((0,28),(5,15))),
    (((0,3),(5,22)),((0,13),(3,21))),
    (((0,3),(27,4)),((0,35),(11,4))),
    (((0,5),(9,21)),((0,15),(10,19))),
    (((0,5),(16,18)),((0,12),(14,18))),
    (((0,8),(17,17)),((0,11),(20,14))),
    (((0,4),(26,7)),((0,6),(22,13))),
    (((0,6),(14,19)),((0,6),(20,15))),
    (((0,0),(24,11)),((0,16),(25,2))),
    (((0,5),(12,20)),((0,8),(27,0))),
    (((0,1),(24,11)),((0,8),(1,22))),
    (((0,0),(18,17)),((0,5),(23,12))),
    (((0,4),(5,22)),((0,8),(24,10))),
    (((0,1),(18,17)),((0,4),(27,4))),
    (((0,11),(26,4)),((0,12),(12,19))),
    (((0,2),(24,11)),((0,6),(4,22))),
    (((0,10),(18,16)),((0,12),(26,3))),
    (((0,39),(0,2)),((1,2),(24,11))),
    (((0,2),(18,17)),((0,15),(25,4))),
    (((0,7),(21,14)),((0,11),(19,15))),
    (((0,0),(6,22)),((0,5),(26,7))),
    (((0,0),(10,21)),((0,6),(16,18))),
    (((0,1),(6,22)),((0,11),(10,20))),
    (((0,1),(10,21)),((0,3),(24,11))),
    (((0,10),(26,5)),((0,15),(7,20))),
    (((0,9),(11,20)),((0,10),(15,18))),
    (((0,3),(18,17)),((0,5),(5,22))),
    (((0,2),(6,22)),((0,5),(27,4))),
    (((0,2),(10,21)),((0,6),(23,12))),
    (((0,0),(27,5)),((0,35),(2,10))),
    (((0,6),(19,16)),((0,6),(25,9))),
    (((0,1),(27,5)),((0,7),(27,3))),
    (((0,9),(0,22)),((0,16),(25,3))),
    (((0,19),(17,14)),((0,33),(10,9))),
    (((0,4),(24,11)),((0,18),(2,20))),
    (((0,3),(6,22)),((0,7),(4,22))),
    (((0,2),(27,5)),((0,3),(10,21)))]
  have hc : ∀ i : Fin 100, Good (2242+i.val) (c i).1 ∧
      Good (2242+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2242,by omega⟩
  have he : 2242+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2342 (n : ℕ) (hlo : 2342≤n) (hhi : n<2442) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,4),(18,17)),((0,6),(26,7))),
    (((0,0),(15,19)),((0,9),(24,10))),
    (((0,28),(11,13)),((0,29),(15,9))),
    (((0,1),(15,19)),((0,7),(9,21))),
    (((0,7),(16,18)),((0,9),(27,1))),
    (((0,8),(21,14)),((0,13),(14,18))),
    (((0,6),(5,22)),((0,17),(25,1))),
    (((0,3),(27,5)),((0,6),(27,4))),
    (((0,0),(13,20)),((0,2),(15,19))),
    (((0,4),(6,22)),((0,7),(12,20))),
    (((0,1),(13,20)),((0,4),(10,21))),
    (((0,5),(24,11)),((0,7),(23,12))),
    (((0,0),(26,8)),((0,8),(22,13))),
    (((0,7),(19,16)),((0,7),(25,9))),
    (((0,1),(26,8)),((0,5),(18,17))),
    (((0,2),(13,20)),((0,11),(7,21))),
    (((0,3),(15,19)),((0,11),(23,11))),
    (((0,8),(27,3)),((0,10),(11,20))),
    (((0,4),(27,5)),((0,11),(13,19))),
    (((0,2),(26,8)),((0,9),(27,2))),
    (((0,7),(26,7)),((0,11),(15,18))),
    (((0,8),(4,22)),((0,17),(25,2))),
    (((0,31),(1,14)),((0,34),(4,11))),
    (((0,0),(7,22)),((0,0),(25,10))),
    (((0,5),(10,21)),((0,10),(0,22))),
    (((0,1),(7,22)),((0,1),(25,10))),
    (((0,7),(5,22)),((0,8),(9,21))),
    (((0,0),(17,18)),((0,3),(26,8))),
    (((0,6),(24,11)),((0,10),(1,22))),
    (((0,1),(17,18)),((0,10),(8,21))),
    (((0,2),(7,22)),((0,2),(25,10))),
    (((0,6),(18,17)),((0,9),(21,14))),
    (((0,5),(27,5)),((0,8),(12,20))),
    (((0,10),(27,1)),((0,15),(2,21))),
    (((0,2),(17,18)),((0,4),(13,20))),
    (((0,0),(22,14)),((0,18),(4,20))),
    (((0,8),(19,16)),((0,8),(25,9))),
    (((0,0),(21,15)),((0,1),(22,14))),
    (((0,0),(28,0)),((0,3),(7,22))),
    (((0,1),(21,15)),((0,9),(14,19))),
    (((0,1),(28,0)),((0,6),(6,22))),
    (((0,5),(15,19)),((0,6),(10,21))),
    (((0,2),(22,14)),((0,3),(17,18))),
    (((0,0),(27,6)),((0,8),(26,7))),
    (((0,0),(28,1)),((0,2),(21,15))),
    (((0,1),(27,6)),((0,2),(28,0))),
    (((0,1),(28,1)),((0,12),(18,16))),
    (((0,9),(4,22)),((1,1),(27,6))),
    (((0,0),(11,21)),((0,0),(23,13))),
    (((0,4),(7,22)),((0,4),(25,10))),
    (((0,1),(11,21)),((0,1),(23,13))),
    (((0,2),(28,1)),((0,7),(18,17))),
    (((0,3),(21,15)),((0,5),(26,8))),
    (((0,3),(28,0)),((0,4),(17,18))),
    (((0,0),(20,16)),((0,10),(3,22))),
    (((0,2),(11,21)),((0,2),(23,13))),
    (((0,1),(20,16)),((0,11),(0,22))),
    (((0,15),(26,0)),((0,23),(22,5))),
    (((0,3),(27,6)),((0,6),(15,19))),
    (((0,0),(28,2)),((0,3),(28,1))),
    (((0,7),(6,22)),((0,9),(23,12))),
    (((0,1),(28,2)),((0,2),(20,16))),
    (((0,9),(19,16)),((0,9),(25,9))),
    (((0,3),(11,21)),((0,3),(23,13))),
    (((0,4),(28,0)),((0,36),(12,0))),
    (((0,6),(13,20)),((0,11),(27,1))),
    (((0,2),(28,2)),((0,16),(0,21))),
    (((0,5),(17,18)),((0,10),(22,13))),
    (((0,10),(14,19)),((0,10),(20,15))),
    (((0,0),(8,22)),((0,3),(20,16))),
    (((0,4),(28,1)),((0,11),(2,22))),
    (((0,1),(8,22)),((0,8),(24,11))),
    (((0,10),(27,3)),((0,18),(17,15))),
    (((0,0),(0,23)),((0,23),(23,0))),
    (((0,3),(28,2)),((0,4),(11,21))),
    (((0,1),(0,23)),((0,5),(22,14))),
    (((0,0),(24,12)),((0,2),(8,22))),
    (((0,0),(1,23)),((0,5),(21,15))),
    (((0,1),(24,12)),((0,5),(28,0))),
    (((0,1),(1,23)),((0,23),(23,1))),
    (((0,2),(0,23)),((0,4),(20,16))),
    (((0,10),(9,21)),((0,18),(14,17))),
    (((0,10),(16,18)),((0,14),(20,14))),
    (((0,0),(28,3)),((0,2),(24,12))),
    (((0,2),(1,23)),((0,3),(8,22))),
    (((0,1),(28,3)),((0,4),(28,2))),
    (((0,0),(19,17)),((0,11),(3,22))),
    (((0,0),(2,23)),((0,10),(12,20))),
    (((0,1),(19,17)),((0,3),(0,23))),
    (((0,1),(2,23)),((0,7),(26,8))),
    (((0,0),(14,20)),((0,0),(26,9))),
    (((0,3),(24,12)),((0,10),(19,16))),
    (((0,1),(14,20)),((0,1),(26,9))),
    (((0,2),(19,17)),((0,13),(15,18))),
    (((0,2),(2,23)),((0,5),(20,16))),
    (((0,0),(16,19)),((0,4),(8,22))),
    (((0,12),(8,21)),((0,14),(19,15))),
    (((0,1),(16,19)),((0,2),(14,20))),
    (((0,3),(28,3)),((0,10),(26,7))),
    (((0,4),(0,23)),((0,5),(28,2)))]
  have hc : ∀ i : Fin 100, Good (2342+i.val) (c i).1 ∧
      Good (2342+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2342,by omega⟩
  have he : 2342+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2442 (n : ℕ) (hlo : 2442≤n) (hhi : n<2542) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,6),(27,6)),((0,7),(7,22))),
    (((0,3),(19,17)),((0,6),(28,1))),
    (((0,2),(16,19)),((0,3),(2,23))),
    (((0,0),(3,23)),((0,0),(27,7))),
    (((0,7),(17,18)),((0,10),(5,22))),
    (((0,1),(3,23)),((0,1),(27,7))),
    (((1,7),(17,18)),((1,10),(5,22))),
    (((0,23),(21,8)),((0,25),(2,18))),
    (((0,8),(13,20)),((0,11),(4,22))),
    (((0,4),(28,3)),((0,5),(8,22))),
    (((0,2),(3,23)),((0,2),(27,7))),
    (((0,6),(20,16)),((0,21),(20,11))),
    (((0,4),(19,17)),((0,7),(22,14))),
    (((0,4),(2,23)),((0,5),(0,23))),
    (((0,7),(21,15)),((0,11),(16,18))),
    (((0,7),(28,0)),((0,12),(27,2))),
    (((0,0),(28,4)),((0,4),(14,20))),
    (((0,5),(1,23)),((0,21),(17,14))),
    (((0,0),(12,21)),((0,1),(28,4))),
    (((0,0),(25,11)),((0,11),(12,20))),
    (((0,1),(12,21)),((0,7),(27,6))),
    (((0,0),(9,22)),((0,1),(25,11))),
    (((0,13),(11,20)),((0,37),(2,9))),
    (((0,1),(9,22)),((0,2),(28,4))),
    (((0,29),(2,16)),((0,34),(7,11))),
    (((0,0),(4,23)),((0,2),(12,21))),
    (((0,2),(25,11)),((0,5),(19,17))),
    (((0,1),(4,23)),((0,5),(2,23))),
    (((0,2),(9,22)),((0,13),(17,17))),
    (((0,4),(3,23)),((0,4),(27,7))),
    (((0,5),(14,20)),((0,5),(26,9))),
    (((0,3),(28,4)),((0,7),(20,16))),
    (((0,2),(4,23)),((0,13),(27,0))),
    (((0,0),(18,18)),((0,3),(12,21))),
    (((0,3),(25,11)),((0,6),(1,23))),
    (((0,1),(18,18)),((0,5),(16,19))),
    (((0,3),(9,22)),((0,7),(28,2))),
    (((0,8),(21,15)),((0,11),(27,4))),
    (((0,8),(28,0)),((0,9),(26,8))),
    (((0,10),(10,21)),((0,12),(27,3))),
    (((0,2),(18,18)),((0,3),(4,23))),
    (((0,18),(23,9)),((0,27),(8,16))),
    (((0,4),(28,4)),((0,36),(12,4))),
    (((0,5),(3,23)),((0,5),(27,7))),
    (((0,4),(12,21)),((0,6),(2,23))),
    (((0,4),(25,11)),((0,25),(4,18))),
    (((0,7),(8,22)),((0,16),(5,21))),
    (((0,4),(9,22)),((0,6),(14,20))),
    (((0,3),(18,18)),((0,8),(11,21))),
    (((0,9),(7,22)),((0,9),(25,10))),
    (((0,7),(0,23)),((0,20),(4,20))),
    (((0,4),(4,23)),((0,23),(23,4))),
    (((0,6),(16,19)),((0,17),(24,8))),
    (((0,0),(5,23)),((0,7),(24,12))),
    (((0,7),(1,23)),((0,8),(20,16))),
    (((0,1),(5,23)),((0,26),(15,13))),
    (((0,5),(28,4)),((0,10),(15,19))),
    (((0,38),(2,8)),((1,1),(5,23))),
    (((0,0),(28,5)),((0,5),(12,21))),
    (((0,4),(18,18)),((0,5),(25,11))),
    (((0,1),(28,5)),((0,2),(5,23))),
    (((0,5),(9,22)),((0,9),(22,14))),
    (((0,22),(6,19)),((0,29),(4,16))),
    (((0,7),(19,17)),((0,9),(21,15))),
    (((0,7),(2,23)),((0,9),(28,0))),
    (((0,2),(28,5)),((0,5),(4,23))),
    (((1,7),(2,23)),((1,9),(28,0))),
    (((0,0),(22,15)),((0,7),(14,20))),
    (((0,3),(5,23)),((0,17),(4,21))),
    (((0,1),(22,15)),((0,8),(8,22))),
    (((0,9),(28,1)),((0,11),(6,22))),
    (((0,0),(23,14)),((0,11),(10,21))),
    (((0,0),(27,8)),((0,7),(16,19))),
    (((0,1),(23,14)),((0,3),(28,5))),
    (((0,1),(27,8)),((0,2),(22,15))),
    (((0,6),(12,21)),((0,14),(8,21))),
    (((0,6),(25,11)),((0,8),(24,12))),
    (((0,0),(26,10)),((0,8),(1,23))),
    (((0,0),(15,20)),((0,0),(21,16))),
    (((0,0),(10,22)),((0,1),(26,10))),
    (((0,1),(15,20)),((0,1),(21,16))),
    (((0,1),(10,22)),((0,13),(4,22))),
    (((0,3),(22,15)),((0,6),(4,23))),
    (((0,8),(28,3)),((0,18),(2,21))),
    (((0,2),(26,10)),((0,4),(28,5))),
    (((0,2),(15,20)),((0,2),(21,16))),
    (((0,2),(10,22)),((0,3),(23,14))),
    (((0,0),(6,23)),((0,3),(27,8))),
    (((0,11),(15,19)),((0,18),(22,11))),
    (((0,1),(6,23)),((0,20),(25,2))),
    (((0,0),(24,13)),((0,6),(18,18))),
    (((0,20),(24,6)),((0,24),(1,19))),
    (((0,1),(24,13)),((0,3),(26,10))),
    (((0,3),(15,20)),((0,3),(21,16))),
    (((0,0),(13,21)),((0,2),(6,23))),
    (((0,0),(17,19)),((0,7),(12,21))),
    (((0,1),(13,21)),((0,7),(25,11))),
    (((0,1),(17,19)),((0,2),(24,13))),
    (((0,4),(27,8)),((0,5),(28,5))),
    (((0,9),(0,23)),((0,10),(28,1)))]
  have hc : ∀ i : Fin 100, Good (2442+i.val) (c i).1 ∧
      Good (2442+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2442,by omega⟩
  have he : 2442+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2542 (n : ℕ) (hlo : 2542≤n) (hhi : n<2642) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,14),(3,22)),((0,23),(9,18))),
    (((0,2),(13,21)),((0,24),(2,19))),
    (((0,2),(17,19)),((0,3),(6,23))),
    (((0,4),(26,10)),((0,8),(3,23))),
    (((0,0),(20,17)),((0,4),(15,20))),
    (((0,3),(24,13)),((0,4),(10,22))),
    (((0,1),(20,17)),((0,12),(10,21))),
    (((0,5),(22,15)),((0,15),(11,20))),
    (((0,40),(4,4)),((1,1),(20,17))),
    (((0,0),(28,6)),((0,3),(13,21))),
    (((0,0),(29,0)),((0,3),(17,19))),
    (((0,1),(28,6)),((0,2),(20,17))),
    (((0,1),(29,0)),((0,5),(27,8))),
    (((0,4),(6,23)),((0,9),(2,23))),
    (((0,10),(28,2)),((0,11),(17,18))),
    (((0,6),(28,5)),((0,23),(24,0))),
    (((0,0),(29,1)),((0,2),(28,6))),
    (((0,2),(29,0)),((0,5),(26,10))),
    (((0,1),(29,1)),((0,5),(15,20))),
    (((0,3),(20,17)),((0,5),(10,22))),
    (((0,4),(13,21)),((0,15),(24,10))),
    (((0,4),(17,19)),((0,8),(9,22))),
    (((0,11),(22,14)),((0,14),(4,22))),
    (((0,2),(29,1)),((0,12),(15,19))),
    (((0,0),(25,12)),((0,3),(28,6))),
    (((0,3),(29,0)),((0,8),(4,23))),
    (((0,1),(25,12)),((0,28),(4,17))),
    (((0,0),(7,23)),((0,5),(6,23))),
    (((0,6),(23,14)),((0,10),(0,23))),
    (((0,1),(7,23)),((0,6),(27,8))),
    (((0,4),(20,17)),((0,5),(24,13))),
    (((0,0),(29,2)),((0,2),(25,12))),
    (((0,10),(1,23)),((0,17),(26,4))),
    (((0,1),(29,2)),((0,8),(18,18))),
    (((0,2),(7,23)),((0,5),(13,21))),
    (((0,4),(28,6)),((0,5),(17,19))),
    (((0,4),(29,0)),((0,6),(10,22))),
    (((0,14),(19,16)),((0,14),(25,9))),
    (((0,2),(29,2)),((0,10),(28,3))),
    (((0,3),(25,12)),((0,19),(2,21))),
    (((0,17),(10,20)),((0,17),(22,12))),
    (((0,10),(19,17)),((0,11),(20,16))),
    (((0,3),(7,23)),((0,4),(29,1))),
    (((0,0),(11,22)),((0,13),(6,22))),
    (((0,5),(20,17)),((0,6),(6,23))),
    (((0,0),(19,18)),((0,1),(11,22))),
    (((0,3),(29,2)),((0,11),(28,2))),
    (((0,1),(19,18)),((0,6),(24,13))),
    (((0,7),(23,14)),((0,22),(8,19))),
    (((0,5),(28,6)),((0,7),(27,8))),
    (((0,0),(27,9)),((0,2),(11,22))),
    (((0,6),(13,21)),((0,9),(4,23))),
    (((0,1),(27,9)),((0,2),(19,18))),
    (((0,4),(7,23)),((0,8),(5,23))),
    (((0,7),(26,10)),((0,16),(11,20))),
    (((0,0),(29,3)),((0,7),(15,20))),
    (((0,5),(29,1)),((0,7),(10,22))),
    (((0,1),(29,3)),((0,2),(27,9))),
    (((0,3),(11,22)),((0,8),(28,5))),
    (((0,9),(18,18)),((0,12),(21,15))),
    (((0,3),(19,18)),((0,11),(0,23))),
    (((0,6),(20,17)),((0,13),(15,19))),
    (((0,2),(29,3)),((0,15),(27,3))),
    (((0,11),(24,12)),((0,18),(16,17))),
    (((0,5),(25,12)),((0,7),(6,23))),
    (((0,3),(27,9)),((0,12),(27,6))),
    (((0,6),(28,6)),((0,12),(28,1))),
    (((0,5),(7,23)),((0,6),(29,0))),
    (((0,13),(13,20)),((0,20),(20,13))),
    (((0,0),(28,7)),((0,4),(11,22))),
    (((0,3),(29,3)),((0,11),(28,3))),
    (((0,1),(28,7)),((0,4),(19,18))),
    (((0,0),(16,20)),((0,7),(17,19))),
    (((0,0),(8,23)),((0,0),(26,11))),
    (((0,1),(16,20)),((0,10),(25,11))),
    (((0,1),(8,23)),((0,1),(26,11))),
    (((0,0),(14,21)),((0,2),(28,7))),
    (((0,8),(26,10)),((0,11),(14,20))),
    (((0,1),(14,21)),((0,8),(15,20))),
    (((0,2),(16,20)),((0,8),(10,22))),
    (((0,2),(8,23)),((0,2),(26,11))),
    (((0,4),(29,3)),((0,6),(25,12))),
    (((0,11),(16,19)),((0,23),(16,15))),
    (((0,2),(14,21)),((0,5),(11,22))),
    (((0,3),(28,7)),((0,6),(7,23))),
    (((0,5),(19,18)),((0,14),(10,21))),
    (((0,0),(0,24)),((0,7),(28,6))),
    (((0,3),(16,20)),((0,7),(29,0))),
    (((0,0),(29,4)),((0,1),(0,24))),
    (((0,39),(3,8)),((0,39),(9,4))),
    (((0,0),(1,24)),((0,1),(29,4))),
    (((0,3),(14,21)),((0,12),(8,22))),
    (((0,1),(1,24)),((0,24),(24,1))),
    (((0,2),(0,24)),((0,7),(29,1))),
    (((0,8),(13,21)),((0,15),(5,22))),
    (((0,2),(29,4)),((0,4),(28,7))),
    (((0,19),(14,18)),((0,25),(23,4))),
    (((0,2),(1,24)),((0,9),(23,14))),
    (((0,4),(16,20)),((0,9),(27,8))),
    (((0,4),(8,23)),((0,4),(26,11)))]
  have hc : ∀ i : Fin 100, Good (2542+i.val) (c i).1 ∧
      Good (2542+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2542,by omega⟩
  have he : 2542+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2642 (n : ℕ) (hlo : 2642≤n) (hhi : n<2742) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,0),(2,24)),((0,6),(11,22))),
    (((0,0),(18,19)),((0,3),(0,24))),
    (((0,1),(2,24)),((0,4),(14,21))),
    (((0,0),(23,15)),((0,1),(18,19))),
    (((0,7),(7,23)),((0,8),(20,17))),
    (((0,1),(23,15)),((0,3),(1,24))),
    (((0,11),(25,11)),((0,19),(12,19))),
    (((0,2),(2,24)),((0,6),(27,9))),
    (((0,0),(22,16)),((0,2),(18,19))),
    (((0,5),(28,7)),((0,8),(28,6))),
    (((0,1),(22,16)),((0,2),(23,15))),
    (((0,17),(0,22)),((0,34),(14,8))),
    (((0,4),(0,24)),((0,5),(16,20))),
    (((0,0),(12,22)),((0,0),(24,14))),
    (((0,4),(29,4)),((0,13),(20,16))),
    (((0,1),(12,22)),((0,1),(24,14))),
    (((0,0),(3,24)),((0,3),(18,19))),
    (((0,12),(16,19)),((0,17),(24,10))),
    (((0,1),(3,24)),((0,3),(23,15))),
    (((0,13),(28,2)),((0,15),(18,17))),
    (((0,2),(12,22)),((0,2),(24,14))),
    (((0,9),(17,19)),((0,24),(17,14))),
    (((0,7),(19,18)),((0,10),(22,15))),
    (((0,2),(3,24)),((0,3),(22,16))),
    (((0,8),(25,12)),((0,14),(7,22))),
    (((0,0),(9,23)),((0,12),(3,23))),
    (((0,4),(2,24)),((0,5),(0,24))),
    (((0,1),(9,23)),((0,4),(18,19))),
    (((0,0),(21,17)),((0,3),(12,22))),
    (((0,4),(23,15)),((0,6),(16,20))),
    (((0,0),(29,5)),((0,1),(21,17))),
    (((0,3),(3,24)),((0,8),(29,2))),
    (((0,1),(29,5)),((0,2),(9,23))),
    (((0,6),(14,21)),((0,10),(15,20))),
    (((0,4),(22,16)),((0,10),(10,22))),
    (((0,2),(21,17)),((0,9),(28,6))),
    (((0,9),(29,0)),((0,13),(24,12))),
    (((0,0),(27,10)),((0,2),(29,5))),
    (((0,0),(4,24)),((0,0),(25,13))),
    (((0,1),(27,10)),((0,4),(12,22))),
    (((0,1),(4,24)),((0,1),(25,13))),
    (((0,5),(18,19)),((0,12),(25,11))),
    (((0,4),(3,24)),((0,9),(29,1))),
    (((0,3),(21,17)),((0,5),(23,15))),
    (((0,2),(27,10)),((0,14),(27,6))),
    (((0,2),(4,24)),((0,2),(25,13))),
    (((0,7),(28,7)),((0,13),(19,17))),
    (((0,6),(1,24)),((0,12),(4,23))),
    (((0,5),(22,16)),((0,26),(19,11))),
    (((0,7),(16,20)),((0,10),(13,21))),
    (((0,7),(8,23)),((0,7),(26,11))),
    (((0,4),(9,23)),((0,39),(2,9))),
    (((0,3),(27,10)),((0,26),(2,19))),
    (((0,3),(4,24)),((0,3),(25,13))),
    (((0,4),(21,17)),((0,11),(22,15))),
    (((0,8),(29,3)),((0,12),(18,18))),
    (((0,4),(29,5)),((0,5),(3,24))),
    (((0,6),(2,24)),((0,9),(29,2))),
    (((0,6),(18,19)),((0,11),(23,14))),
    (((0,10),(20,17)),((0,11),(27,8))),
    (((0,6),(23,15)),((0,14),(28,2))),
    (((0,40),(4,7)),((0,42),(3,1))),
    (((0,29),(9,16)),((1,6),(23,15))),
    (((0,0),(20,18)),((0,4),(27,10))),
    (((0,0),(15,21)),((0,4),(4,24))),
    (((0,1),(20,18)),((0,5),(9,23))),
    (((0,0),(5,24)),((0,1),(15,21))),
    (((0,7),(1,24)),((0,18),(27,0))),
    (((0,1),(5,24)),((0,5),(21,17))),
    (((0,8),(28,7)),((0,9),(11,22))),
    (((0,2),(20,18)),((0,5),(29,5))),
    (((0,2),(15,21)),((0,9),(19,18))),
    (((0,0),(17,20)),((0,8),(16,20))),
    (((0,2),(5,24)),((0,6),(3,24))),
    (((0,1),(17,20)),((0,11),(6,23))),
    (((0,12),(5,23)),((0,16),(6,22))),
    (((0,8),(14,21)),((0,9),(27,9))),
    (((0,5),(27,10)),((0,7),(2,24))),
    (((0,0),(26,12)),((0,3),(20,18))),
    (((0,2),(17,20)),((0,3),(15,21))),
    (((0,1),(26,12)),((0,7),(23,15))),
    (((0,0),(29,6)),((0,3),(5,24))),
    (((0,6),(9,23)),((0,10),(7,23))),
    (((0,0),(10,23)),((0,1),(29,6))),
    (((0,14),(28,3)),((0,16),(27,5))),
    (((0,1),(10,23)),((0,2),(26,12))),
    (((0,8),(0,24)),((0,10),(29,2))),
    (((0,3),(17,20)),((0,6),(29,5))),
    (((0,0),(30,0)),((0,2),(29,6))),
    (((0,0),(13,22)),((0,4),(20,18))),
    (((0,1),(30,0)),((0,2),(10,23))),
    (((0,1),(13,22)),((0,11),(20,17))),
    (((0,4),(5,24)),((0,17),(27,4))),
    (((0,3),(26,12)),((0,7),(3,24))),
    (((0,0),(30,1)),((0,6),(27,10))),
    (((0,2),(30,0)),((0,6),(4,24))),
    (((0,1),(30,1)),((0,2),(13,22))),
    (((0,11),(29,0)),((0,35),(17,0))),
    (((0,3),(10,23)),((0,4),(17,20))),
    (((0,9),(8,23)),((0,9),(26,11)))]
  have hc : ∀ i : Fin 100, Good (2642+i.val) (c i).1 ∧
      Good (2642+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2642,by omega⟩
  have he : 2642+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2742 (n : ℕ) (hlo : 2742≤n) (hhi : n<2842) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,0),(6,24)),((0,8),(2,24))),
    (((0,2),(30,1)),((0,8),(18,19))),
    (((0,1),(6,24)),((0,7),(9,23))),
    (((0,3),(30,0)),((0,5),(20,18))),
    (((0,3),(13,22)),((0,4),(26,12))),
    (((0,7),(21,17)),((0,10),(27,9))),
    (((0,5),(5,24)),((0,24),(24,5))),
    (((0,2),(6,24)),((0,4),(29,6))),
    (((0,8),(22,16)),((0,18),(14,19))),
    (((0,0),(30,2)),((0,3),(30,1))),
    (((0,10),(29,3)),((0,26),(15,15))),
    (((0,1),(30,2)),((0,11),(25,12))),
    (((0,5),(17,20)),((0,9),(0,24))),
    (((0,0),(19,19)),((0,8),(12,22))),
    (((0,4),(30,0)),((0,7),(27,10))),
    (((0,1),(19,19)),((0,3),(6,24))),
    (((0,0),(28,9)),((0,2),(30,2))),
    (((0,12),(17,19)),((0,14),(28,4))),
    (((0,1),(28,9)),((0,5),(26,12))),
    (((0,14),(12,21)),((0,16),(17,18))),
    (((0,2),(19,19)),((0,4),(30,1))),
    (((0,5),(29,6)),((0,6),(15,21))),
    (((0,14),(9,22)),((0,15),(1,23))),
    (((0,2),(28,9)),((0,5),(10,23))),
    (((0,3),(30,2)),((0,10),(28,7))),
    (((0,8),(9,23)),((0,17),(6,22))),
    (((0,4),(6,24)),((0,9),(2,24))),
    (((0,9),(18,19)),((0,10),(16,20))),
    (((0,3),(19,19)),((0,5),(30,0))),
    (((0,5),(13,22)),((0,6),(17,20))),
    (((0,8),(29,5)),((0,11),(11,22))),
    (((0,3),(28,9)),((0,10),(14,21))),
    (((0,11),(19,18)),((0,12),(29,0))),
    (((0,0),(27,11)),((0,0),(30,3))),
    (((0,5),(30,1)),((0,9),(22,16))),
    (((0,1),(27,11)),((0,1),(30,3))),
    (((0,16),(28,1)),((0,32),(20,1))),
    (((0,8),(27,10)),((0,11),(27,9))),
    (((0,6),(29,6)),((0,8),(4,24))),
    (((0,4),(19,19)),((0,9),(12,22))),
    (((0,0),(7,24)),((0,2),(27,11))),
    (((0,0),(29,7)),((0,7),(15,21))),
    (((0,1),(7,24)),((0,4),(28,9))),
    (((0,1),(29,7)),((0,7),(5,24))),
    (((0,0),(23,16)),((0,18),(5,22))),
    (((0,0),(24,15)),((0,6),(30,0))),
    (((0,1),(23,16)),((0,6),(13,22))),
    (((0,0),(11,23)),((0,1),(24,15))),
    (((0,2),(29,7)),((0,3),(27,11))),
    (((0,1),(11,23)),((0,5),(30,2))),
    (((0,13),(24,13)),((0,17),(13,20))),
    (((0,2),(23,16)),((0,6),(30,1))),
    (((0,2),(24,15)),((0,25),(2,20))),
    (((0,5),(19,19)),((0,12),(29,2))),
    (((0,2),(11,23)),((0,9),(21,17))),
    (((0,3),(7,24)),((0,7),(26,12))),
    (((0,3),(29,7)),((0,5),(28,9))),
    (((0,6),(6,24)),((0,24),(24,6))),
    (((0,0),(16,21)),((0,0),(22,17))),
    (((0,3),(23,16)),((0,4),(27,11))),
    (((0,1),(16,21)),((0,1),(22,17))),
    (((0,0),(25,14)),((0,15),(28,4))),
    (((0,3),(11,23)),((0,21),(26,4))),
    (((0,1),(25,14)),((0,8),(20,18))),
    (((0,8),(15,21)),((0,9),(4,24))),
    (((0,2),(16,21)),((0,2),(22,17))),
    (((0,0),(30,4)),((0,4),(7,24))),
    (((0,4),(29,7)),((0,12),(19,18))),
    (((0,1),(30,4)),((0,2),(25,14))),
    (((0,13),(28,6)),((0,16),(1,23))),
    (((0,4),(23,16)),((0,6),(19,19))),
    (((0,0),(14,22)),((0,4),(24,15))),
    (((0,8),(17,20)),((0,12),(27,9))),
    (((0,1),(14,22)),((0,2),(30,4))),
    (((0,25),(15,16)),((0,30),(20,7))),
    (((0,11),(29,4)),((0,16),(28,3))),
    (((0,3),(25,14)),((0,13),(29,1))),
    (((0,7),(6,24)),((0,11),(1,24))),
    (((0,0),(18,20)),((0,2),(14,22))),
    (((0,14),(15,20)),((0,14),(21,16))),
    (((0,1),(18,20)),((0,5),(7,24))),
    (((0,3),(30,4)),((0,5),(29,7))),
    (((0,16),(14,20)),((0,16),(26,9))),
    (((0,8),(10,23)),((0,10),(21,17))),
    (((0,4),(16,21)),((0,4),(22,17))),
    (((0,2),(18,20)),((0,5),(24,15))),
    (((0,0),(8,24)),((0,3),(14,22))),
    (((0,0),(21,18)),((0,4),(25,14))),
    (((0,1),(8,24)),((0,8),(30,0))),
    (((0,1),(21,18)),((0,8),(13,22))),
    (((0,6),(27,11)),((0,6),(30,3))),
    (((0,12),(28,7)),((0,13),(29,2))),
    (((0,0),(26,13)),((0,4),(30,4))),
    (((0,2),(8,24)),((0,3),(18,20))),
    (((0,1),(26,13)),((0,2),(21,18))),
    (((0,11),(22,16)),((0,12),(8,23))),
    (((0,14),(17,19)),((0,17),(20,16))),
    (((0,4),(14,22)),((0,6),(7,24))),
    (((0,5),(16,21)),((0,5),(22,17))),
    (((0,2),(26,13)),((0,29),(5,18)))]
  have hc : ∀ i : Fin 100, Good (2742+i.val) (c i).1 ∧
      Good (2742+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2742,by omega⟩
  have he : 2742+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2842 (n : ℕ) (hlo : 2842≤n) (hhi : n<2942) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,8),(6,24)),((0,11),(12,22))),
    (((0,3),(8,24)),((0,5),(25,14))),
    (((0,3),(21,18)),((0,6),(24,15))),
    (((0,0),(28,10)),((0,11),(3,24))),
    (((0,4),(18,20)),((0,6),(11,23))),
    (((0,1),(28,10)),((0,13),(19,18))),
    (((0,5),(30,4)),((0,31),(20,6))),
    (((0,3),(26,13)),((0,9),(29,6))),
    (((0,0),(0,25)),((0,0),(30,5))),
    (((0,8),(30,2)),((0,9),(10,23))),
    (((0,0),(29,8)),((0,1),(0,25))),
    (((0,5),(14,22)),((0,14),(29,0))),
    (((0,0),(1,25)),((0,1),(29,8))),
    (((0,4),(21,18)),((0,8),(19,19))),
    (((0,1),(1,25)),((0,9),(30,0))),
    (((0,2),(0,25)),((0,2),(30,5))),
    (((0,8),(28,9)),((0,15),(23,14))),
    (((0,0),(12,23)),((0,2),(29,8))),
    (((0,3),(28,10)),((0,4),(26,13))),
    (((0,1),(12,23)),((0,2),(1,25))),
    (((0,9),(30,1)),((0,37),(16,1))),
    (((0,7),(23,16)),((0,10),(5,24))),
    (((0,0),(2,25)),((0,7),(24,15))),
    (((0,3),(0,25)),((0,3),(30,5))),
    (((0,1),(2,25)),((0,2),(12,23))),
    (((0,3),(29,8)),((0,11),(4,24))),
    (((0,5),(8,24)),((0,9),(6,24))),
    (((0,3),(1,25)),((0,5),(21,18))),
    (((0,6),(14,22)),((0,14),(7,23))),
    (((0,2),(2,25)),((0,4),(28,10))),
    (((0,12),(22,16)),((0,18),(22,14))),
    (((0,0),(20,19)),((0,20),(4,22))),
    (((0,3),(12,23)),((0,5),(26,13))),
    (((0,1),(20,19)),((0,8),(27,11))),
    (((0,4),(0,25)),((0,4),(30,5))),
    (((0,6),(18,20)),((0,7),(16,21))),
    (((0,4),(29,8)),((0,10),(29,6))),
    (((0,3),(2,25)),((0,17),(16,19))),
    (((0,0),(3,25)),((0,0),(9,24))),
    (((0,9),(19,19)),((0,15),(13,21))),
    (((0,1),(3,25)),((0,1),(9,24))),
    (((0,8),(29,7)),((0,21),(0,22))),
    (((0,9),(28,9)),((0,20),(12,20))),
    (((0,4),(12,23)),((0,5),(28,10))),
    (((0,6),(21,18)),((0,8),(23,16))),
    (((0,2),(3,25)),((0,2),(9,24))),
    (((0,3),(20,19)),((0,13),(0,24))),
    (((0,8),(11,23)),((0,12),(9,23))),
    (((0,4),(2,25)),((0,5),(0,25))),
    (((0,6),(26,13)),((0,10),(30,1))),
    (((0,5),(29,8)),((0,11),(20,18))),
    (((0,11),(15,21)),((0,14),(27,9))),
    (((0,5),(1,25)),((0,12),(29,5))),
    (((0,3),(3,25)),((0,3),(9,24))),
    (((0,15),(28,6)),((0,18),(28,2))),
    (((0,7),(18,20)),((0,10),(6,24))),
    (((0,14),(29,3)),((0,34),(19,3))),
    (((0,4),(20,19)),((0,5),(12,23))),
    (((0,0),(17,21)),((0,8),(16,21))),
    (((0,0),(15,22)),((0,0),(30,6))),
    (((0,0),(4,25)),((0,1),(17,21))),
    (((0,1),(15,22)),((0,1),(30,6))),
    (((0,1),(4,25)),((0,5),(2,25))),
    (((0,7),(8,24)),((0,13),(23,15))),
    (((0,4),(3,25)),((0,4),(9,24))),
    (((0,2),(17,21)),((0,6),(0,25))),
    (((0,2),(15,22)),((0,2),(30,6))),
    (((0,2),(4,25)),((0,6),(29,8))),
    (((0,10),(19,19)),((0,11),(29,6))),
    (((0,6),(1,25)),((0,7),(26,13))),
    (((0,9),(23,16)),((0,11),(10,23))),
    (((0,5),(20,19)),((0,8),(14,22))),
    (((0,0),(31,0)),((0,15),(7,23))),
    (((0,3),(17,21)),((0,9),(11,23))),
    (((0,1),(31,0)),((0,3),(15,22))),
    (((0,3),(4,25)),((0,11),(30,0))),
    (((0,11),(13,22)),((0,13),(3,24))),
    (((0,14),(14,21)),((0,21),(21,14))),
    (((0,0),(31,1)),((0,5),(3,25))),
    (((0,2),(31,0)),((0,6),(2,25))),
    (((0,1),(31,1)),((0,7),(28,10))),
    (((0,11),(30,1)),((0,18),(19,17))),
    (((0,16),(24,13)),((0,18),(2,23))),
    (((0,42),(9,1)),((0,43),(4,4))),
    (((0,4),(17,21)),((0,9),(16,21))),
    (((0,2),(31,1)),((0,4),(15,22))),
    (((0,0),(24,16)),((0,4),(4,25))),
    (((0,3),(31,0)),((0,7),(29,8))),
    (((0,0),(5,25)),((0,0),(29,9))),
    (((0,7),(1,25)),((0,14),(29,4))),
    (((0,0),(19,20)),((0,1),(5,25))),
    (((0,14),(1,24)),((0,25),(24,7))),
    (((0,1),(19,20)),((0,8),(26,13))),
    (((0,0),(13,23)),((0,0),(25,15))),
    (((0,0),(23,17)),((0,7),(12,23))),
    (((0,1),(13,23)),((0,1),(25,15))),
    (((0,0),(10,24)),((0,1),(23,17))),
    (((0,2),(19,20)),((0,9),(14,22))),
    (((0,1),(10,24)),((0,4),(31,0))),
    (((0,0),(28,11)),((0,5),(15,22)))]
  have hc : ∀ i : Fin 100, Good (2842+i.val) (c i).1 ∧
      Good (2842+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2842,by omega⟩
  have he : 2842+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_2942 (n : ℕ) (hlo : 2942≤n) (hhi : n<3042) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(13,23)),((0,2),(25,15))),
    (((0,1),(28,11)),((0,2),(23,17))),
    (((0,10),(11,23)),((0,14),(18,19))),
    (((0,2),(10,24)),((0,3),(5,25))),
    (((0,4),(31,1)),((0,9),(18,20))),
    (((0,3),(19,20)),((0,12),(10,23))),
    (((0,2),(28,11)),((0,21),(23,12))),
    (((0,43),(7,0)),((1,3),(19,20))),
    (((0,3),(13,23)),((0,3),(25,15))),
    (((0,3),(23,17)),((0,14),(22,16))),
    (((0,8),(29,8)),((0,12),(30,0))),
    (((0,3),(10,24)),((0,12),(13,22))),
    (((0,4),(24,16)),((0,5),(31,0))),
    (((0,9),(21,18)),((0,10),(16,21))),
    (((0,3),(28,11)),((0,4),(5,25))),
    (((0,0),(26,14)),((0,6),(17,21))),
    (((0,4),(19,20)),((0,6),(15,22))),
    (((0,0),(22,18)),((0,0),(31,3))),
    (((0,5),(31,1)),((0,9),(26,13))),
    (((0,0),(30,7)),((0,1),(22,18))),
    (((0,4),(23,17)),((0,11),(27,11))),
    (((0,1),(30,7)),((0,10),(30,4))),
    (((0,0),(6,25)),((0,2),(26,14))),
    (((0,13),(20,18)),((0,16),(29,2))),
    (((0,1),(6,25)),((0,2),(22,18))),
    (((0,4),(28,11)),((0,27),(3,20))),
    (((0,2),(30,7)),((0,5),(24,16))),
    (((0,11),(7,24)),((0,19),(24,12))),
    (((0,5),(5,25)),((0,5),(29,9))),
    (((0,2),(6,25)),((0,6),(31,0))),
    (((0,3),(26,14)),((0,5),(19,20))),
    (((0,8),(20,19)),((0,11),(23,16))),
    (((0,3),(22,18)),((0,3),(31,3))),
    (((0,5),(13,23)),((0,5),(25,15))),
    (((0,3),(30,7)),((0,5),(23,17))),
    (((0,6),(31,1)),((0,7),(17,21))),
    (((0,5),(10,24)),((0,7),(15,22))),
    (((0,3),(6,25)),((0,7),(4,25))),
    (((0,8),(3,25)),((0,8),(9,24))),
    (((0,5),(28,11)),((0,14),(4,24))),
    (((1,8),(3,25)),((1,8),(9,24))),
    (((0,4),(26,14)),((0,10),(8,24))),
    (((0,10),(21,18)),((0,16),(27,9))),
    (((0,4),(22,18)),((0,4),(31,3))),
    (((0,24),(16,17)),((0,34),(8,15))),
    (((0,4),(30,7)),((0,6),(5,25))),
    (((0,15),(18,19)),((0,17),(20,17))),
    (((0,6),(19,20)),((0,10),(26,13))),
    (((0,4),(6,25)),((0,9),(2,25))),
    (((0,7),(31,0)),((0,13),(13,22))),
    (((0,0),(31,4)),((0,6),(13,23))),
    (((0,6),(23,17)),((0,17),(28,6))),
    (((0,0),(27,13)),((0,1),(31,4))),
    (((0,0),(16,22)),((0,6),(10,24))),
    (((0,1),(27,13)),((0,13),(30,1))),
    (((0,0),(21,19)),((0,1),(16,22))),
    (((0,6),(28,11)),((0,21),(10,21))),
    (((0,1),(21,19)),((0,2),(31,4))),
    (((0,8),(17,21)),((0,10),(28,10))),
    (((0,2),(27,13)),((0,5),(30,7))),
    (((0,0),(11,24)),((0,2),(16,22))),
    (((0,15),(3,24)),((0,16),(28,7))),
    (((0,0),(7,25)),((0,1),(11,24))),
    (((0,7),(24,16)),((0,10),(0,25))),
    (((0,0),(18,21)),((0,1),(7,25))),
    (((0,3),(31,4)),((0,7),(5,25))),
    (((0,1),(18,21)),((0,12),(23,16))),
    (((0,2),(11,24)),((0,3),(27,13))),
    (((0,3),(16,22)),((0,16),(14,21))),
    (((0,2),(7,25)),((0,12),(11,23))),
    (((0,3),(21,19)),((0,7),(13,23))),
    (((0,2),(18,21)),((0,7),(23,17))),
    (((0,6),(26,14)),((0,8),(31,0))),
    (((0,7),(10,24)),((0,11),(8,24))),
    (((0,6),(22,18)),((0,6),(31,3))),
    (((0,0),(14,23)),((0,0),(29,10))),
    (((0,4),(31,4)),((0,6),(30,7))),
    (((0,1),(14,23)),((0,1),(29,10))),
    (((0,4),(27,13)),((0,8),(31,1))),
    (((0,3),(18,21)),((0,4),(16,22))),
    (((0,12),(16,21)),((0,12),(22,17))),
    (((0,4),(21,19)),((0,39),(14,5))),
    (((0,2),(14,23)),((0,2),(29,10))),
    (((0,12),(25,14)),((0,15),(4,24))),
    (((0,9),(17,21)),((0,14),(10,23))),
    (((0,9),(15,22)),((0,9),(30,6))),
    (((0,4),(11,24)),((0,8),(24,16))),
    (((0,17),(19,18)),((0,20),(1,23))),
    (((0,0),(30,8)),((0,4),(7,25))),
    (((0,14),(30,0)),((0,18),(13,21))),
    (((0,1),(30,8)),((0,3),(14,23))),
    (((0,40),(4,11)),((1,14),(30,0))),
    (((0,0),(31,5)),((0,5),(27,13))),
    (((0,5),(16,22)),((0,8),(13,23))),
    (((0,1),(31,5)),((0,7),(22,18))),
    (((0,2),(30,8)),((0,5),(21,19))),
    (((0,7),(30,7)),((0,8),(10,24))),
    (((0,11),(29,8)),((0,17),(29,3))),
    (((0,9),(31,0)),((0,23),(27,2))),
    (((0,2),(31,5)),((0,7),(6,25)))]
  have hc : ∀ i : Fin 100, Good (2942+i.val) (c i).1 ∧
      Good (2942+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-2942,by omega⟩
  have he : 2942+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3042 (n : ℕ) (hlo : 3042≤n) (hhi : n<3142) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,5),(11,24)),((0,12),(18,20))),
    (((0,4),(14,23)),((0,4),(29,10))),
    (((0,5),(7,25)),((0,29),(19,12))),
    (((0,3),(30,8)),((0,35),(2,16))),
    (((0,0),(28,12)),((0,5),(18,21))),
    (((0,13),(24,15)),((0,16),(12,22))),
    (((0,1),(28,12)),((0,30),(3,19))),
    (((0,3),(31,5)),((0,6),(31,4))),
    (((0,0),(8,25)),((0,0),(20,20))),
    (((0,6),(27,13)),((0,11),(2,25))),
    (((0,1),(8,25)),((0,1),(20,20))),
    (((0,2),(28,12)),((0,15),(5,24))),
    (((0,6),(21,19)),((0,9),(24,16))),
    (((0,10),(17,21)),((0,20),(3,23))),
    (((0,4),(30,8)),((0,9),(5,25))),
    (((0,2),(8,25)),((0,2),(20,20))),
    (((0,9),(19,20)),((0,21),(28,1))),
    (((0,6),(11,24)),((0,8),(22,18))),
    (((0,4),(31,5)),((0,11),(20,19))),
    (((0,3),(28,12)),((0,6),(7,25))),
    (((0,9),(23,17)),((0,16),(21,17))),
    (((0,6),(18,21)),((0,13),(25,14))),
    (((0,8),(6,25)),((0,9),(10,24))),
    (((0,3),(8,25)),((0,3),(20,20))),
    (((0,45),(0,1)),((1,8),(6,25))),
    (((0,9),(28,11)),((0,11),(3,25))),
    (((0,13),(30,4)),((0,15),(29,6))),
    (((0,7),(31,4)),((0,10),(31,0))),
    (((0,5),(30,8)),((0,15),(10,23))),
    (((0,7),(27,13)),((0,16),(27,10))),
    (((0,0),(12,24)),((0,4),(28,12))),
    (((0,13),(14,22)),((0,20),(9,22))),
    (((0,1),(12,24)),((0,5),(31,5))),
    (((0,10),(31,1)),((0,15),(30,0))),
    (((0,0),(25,16)),((0,4),(8,25))),
    (((0,20),(4,23)),((0,31),(12,16))),
    (((0,0),(24,17)),((0,1),(25,16))),
    (((0,2),(12,24)),((0,7),(11,24))),
    (((0,1),(24,17)),((0,13),(18,20))),
    (((0,0),(0,26)),((0,7),(7,25))),
    (((0,18),(19,18)),((0,25),(26,4))),
    (((0,1),(0,26)),((0,2),(25,16))),
    (((0,14),(29,7)),((0,17),(2,24))),
    (((0,0),(1,26)),((0,0),(31,6))),
    (((0,5),(28,12)),((0,12),(2,25))),
    (((0,1),(1,26)),((0,1),(31,6))),
    (((0,2),(0,26)),((0,11),(15,22))),
    (((0,0),(26,15)),((0,11),(4,25))),
    (((0,5),(8,25)),((0,5),(20,20))),
    (((0,1),(26,15)),((0,3),(25,16))),
    (((0,2),(1,26)),((0,2),(31,6))),
    (((0,3),(24,17)),((0,10),(10,24))),
    (((0,7),(14,23)),((0,7),(29,10))),
    (((0,0),(2,26)),((0,0),(17,22))),
    (((0,2),(26,15)),((0,3),(0,26))),
    (((0,1),(2,26)),((0,1),(17,22))),
    (((0,4),(12,24)),((0,16),(15,21))),
    (((0,43),(1,8)),((1,1),(2,26))),
    (((0,3),(1,26)),((0,3),(31,6))),
    (((0,11),(31,0)),((0,14),(16,21))),
    (((0,0),(9,25)),((0,2),(2,26))),
    (((0,6),(28,12)),((0,15),(28,9))),
    (((0,0),(32,0)),((0,1),(9,25))),
    (((0,0),(15,23)),((0,13),(28,10))),
    (((0,1),(32,0)),((0,8),(18,21))),
    (((0,1),(15,23)),((0,4),(0,26))),
    (((0,0),(30,9)),((0,40),(10,9))),
    (((0,2),(9,25)),((0,14),(30,4))),
    (((0,0),(32,1)),((0,1),(30,9))),
    (((0,0),(3,26)),((0,2),(32,0))),
    (((0,1),(32,1)),((0,2),(15,23))),
    (((0,0),(29,11)),((0,1),(3,26))),
    (((0,10),(22,18)),((0,10),(31,3))),
    (((0,1),(29,11)),((0,2),(30,9))),
    (((0,5),(25,16)),((0,10),(30,7))),
    (((0,0),(27,14)),((0,2),(32,1))),
    (((0,0),(19,21)),((0,2),(3,26))),
    (((0,1),(27,14)),((0,3),(32,0))),
    (((0,1),(19,21)),((0,2),(29,11))),
    (((0,4),(2,26)),((0,4),(17,22))),
    (((0,11),(13,23)),((0,11),(25,15))),
    (((0,3),(30,9)),((0,7),(28,12))),
    (((0,2),(27,14)),((0,12),(4,25))),
    (((0,0),(32,2)),((0,2),(19,21))),
    (((0,3),(3,26)),((0,26),(26,3))),
    (((0,0),(22,19)),((0,1),(32,2))),
    (((0,3),(29,11)),((0,4),(9,25))),
    (((0,1),(22,19)),((0,5),(26,15))),
    (((0,4),(32,0)),((0,8),(30,8))),
    (((0,4),(15,23)),((0,15),(23,16))),
    (((0,2),(32,2)),((0,3),(27,14))),
    (((0,0),(4,26)),((0,3),(19,21))),
    (((0,2),(22,19)),((0,4),(30,9))),
    (((0,1),(4,26)),((0,5),(2,26))),
    (((0,4),(32,1)),((0,12),(31,0))),
    (((0,4),(3,26)),((0,18),(2,24))),
    (((0,6),(0,26)),((0,18),(18,19))),
    (((0,4),(29,11)),((0,20),(6,23))),
    (((0,2),(4,26)),((0,3),(32,2))),
    (((1,4),(29,11)),((1,20),(6,23)))]
  have hc : ∀ i : Fin 100, Good (3042+i.val) (c i).1 ∧
      Good (3042+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3042,by omega⟩
  have he : 3042+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3142 (n : ℕ) (hlo : 3142≤n) (hhi : n<3242) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,3),(22,19)),((0,5),(9,25))),
    (((0,4),(27,14)),((0,9),(14,23))),
    (((0,4),(19,21)),((0,5),(32,0))),
    (((0,0),(31,7)),((0,5),(15,23))),
    (((0,6),(26,15)),((0,8),(28,12))),
    (((0,1),(31,7)),((0,10),(31,4))),
    (((0,0),(13,24)),((0,3),(4,26))),
    (((0,0),(32,3)),((0,7),(12,24))),
    (((0,1),(13,24)),((0,5),(32,1))),
    (((0,1),(32,3)),((0,4),(32,2))),
    (((0,2),(31,7)),((0,6),(2,26))),
    (((0,4),(22,19)),((0,5),(29,11))),
    (((0,12),(19,20)),((0,24),(19,16))),
    (((0,2),(13,24)),((0,7),(24,17))),
    (((0,2),(32,3)),((0,9),(30,8))),
    (((0,5),(27,14)),((0,10),(11,24))),
    (((0,5),(19,21)),((0,7),(0,26))),
    (((0,4),(4,26)),((0,6),(9,25))),
    (((0,0),(10,25)),((0,0),(28,13))),
    (((0,0),(5,26)),((0,6),(32,0))),
    (((0,1),(10,25)),((0,1),(28,13))),
    (((0,1),(5,26)),((0,3),(13,24))),
    (((0,3),(32,3)),((0,25),(27,0))),
    (((0,5),(32,2)),((0,6),(30,9))),
    (((0,7),(26,15)),((0,19),(8,23))),
    (((0,2),(10,25)),((0,2),(28,13))),
    (((0,2),(5,26)),((0,6),(3,26))),
    (((0,19),(14,21)),((0,22),(14,20))),
    (((0,6),(29,11)),((0,23),(7,22))),
    (((0,4),(31,7)),((0,40),(13,7))),
    (((0,7),(2,26)),((0,7),(17,22))),
    (((0,5),(4,26)),((0,15),(8,24))),
    (((0,0),(21,20)),((0,4),(13,24))),
    (((0,3),(10,25)),((0,3),(28,13))),
    (((0,1),(21,20)),((0,3),(5,26))),
    (((0,43),(1,9)),((0,44),(5,6))),
    (((0,8),(24,17)),((0,16),(23,16))),
    (((0,7),(9,25)),((0,11),(31,4))),
    (((0,13),(31,1)),((0,37),(19,1))),
    (((0,2),(21,20)),((0,7),(32,0))),
    (((0,0),(32,4)),((0,6),(32,2))),
    (((0,12),(30,7)),((0,19),(1,24))),
    (((0,1),(32,4)),((0,6),(22,19))),
    (((0,5),(31,7)),((0,7),(30,9))),
    (((0,4),(10,25)),((0,4),(28,13))),
    (((0,4),(5,26)),((0,7),(32,1))),
    (((0,5),(13,24)),((0,7),(3,26))),
    (((0,2),(32,4)),((0,3),(21,20))),
    (((0,6),(4,26)),((0,7),(29,11))),
    (((0,11),(7,25)),((0,21),(26,10))),
    (((0,13),(19,20)),((0,16),(16,21))),
    (((0,11),(18,21)),((0,17),(30,2))),
    (((0,7),(27,14)),((0,19),(18,19))),
    (((0,0),(6,26)),((0,0),(30,10))),
    (((0,13),(23,17)),((0,19),(23,15))),
    (((0,1),(6,26)),((0,1),(30,10))),
    (((0,9),(12,24)),((0,13),(10,24))),
    (((0,0),(16,23)),((0,15),(1,25))),
    (((0,4),(21,20)),((0,5),(10,25))),
    (((0,0),(18,22)),((0,1),(16,23))),
    (((0,2),(6,26)),((0,2),(30,10))),
    (((0,1),(18,22)),((0,14),(4,25))),
    (((0,7),(22,19)),((0,8),(32,0))),
    (((0,6),(13,24)),((0,8),(15,23))),
    (((0,2),(16,23)),((0,6),(32,3))),
    (((0,9),(0,26)),((0,20),(29,3))),
    (((0,2),(18,22)),((0,4),(32,4))),
    (((0,15),(2,25)),((0,18),(17,20))),
    (((0,3),(6,26)),((0,3),(30,10))),
    (((0,8),(3,26)),((0,9),(1,26))),
    (((0,16),(18,20)),((0,22),(18,18))),
    (((0,8),(29,11)),((0,25),(4,22))),
    (((0,0),(31,8)),((0,3),(16,23))),
    (((0,9),(26,15)),((0,14),(31,0))),
    (((0,1),(31,8)),((0,3),(18,22))),
    (((0,6),(10,25)),((0,6),(28,13))),
    (((0,0),(29,12)),((0,6),(5,26))),
    (((0,12),(21,19)),((0,13),(22,18))),
    (((0,1),(29,12)),((0,16),(8,24))),
    (((0,2),(31,8)),((0,4),(6,26))),
    (((0,5),(32,4)),((0,7),(31,7))),
    (((0,19),(29,5)),((0,21),(28,6))),
    (((0,0),(11,25)),((0,0),(32,5))),
    (((0,2),(29,12)),((0,4),(16,23))),
    (((0,0),(25,17)),((0,1),(11,25))),
    (((0,4),(18,22)),((0,8),(22,19))),
    (((0,1),(25,17)),((0,9),(9,25))),
    (((0,3),(31,8)),((0,14),(24,16))),
    (((0,0),(14,24)),((0,0),(26,16))),
    (((0,2),(11,25)),((0,2),(32,5))),
    (((0,1),(14,24)),((0,1),(26,16))),
    (((0,2),(25,17)),((0,3),(29,12))),
    (((0,9),(30,9)),((0,23),(2,23))),
    (((0,0),(7,26)),((0,5),(6,26))),
    (((0,0),(20,21)),((0,9),(32,1))),
    (((0,0),(24,18)),((0,1),(7,26))),
    (((0,1),(20,21)),((0,7),(5,26))),
    (((0,1),(24,18)),((0,3),(11,25))),
    (((0,4),(31,8)),((0,10),(1,26))),
    (((0,3),(25,17)),((0,5),(18,22)))]
  have hc : ∀ i : Fin 100, Good (3142+i.val) (c i).1 ∧
      Good (3142+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3142,by omega⟩
  have he : 3142+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3242 (n : ℕ) (hlo : 3242≤n) (hhi : n<3342) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(7,26)),((0,14),(28,11))),
    (((0,2),(20,21)),((0,9),(27,14))),
    (((0,2),(24,18)),((0,4),(29,12))),
    (((0,3),(14,24)),((0,3),(26,16))),
    (((0,15),(15,22)),((0,15),(30,6))),
    (((0,15),(4,25)),((0,26),(27,1))),
    (((0,8),(13,24)),((0,32),(13,16))),
    (((0,0),(27,15)),((0,8),(32,3))),
    (((0,3),(7,26)),((0,4),(11,25))),
    (((0,1),(27,15)),((0,3),(20,21))),
    (((0,3),(24,18)),((0,4),(25,17))),
    (((0,9),(22,19)),((0,18),(28,9))),
    (((0,5),(31,8)),((0,13),(27,13))),
    (((0,13),(16,22)),((0,17),(14,22))),
    (((0,2),(27,15)),((0,4),(14,24))),
    (((0,10),(9,25)),((0,13),(21,19))),
    (((0,5),(29,12)),((0,6),(18,22))),
    (((0,7),(32,4)),((0,9),(4,26))),
    (((0,8),(10,25)),((0,8),(28,13))),
    (((0,4),(7,26)),((0,8),(5,26))),
    (((0,4),(20,21)),((0,13),(11,24))),
    (((0,0),(23,19)),((0,4),(24,18))),
    (((0,3),(27,15)),((0,5),(11,25))),
    (((0,1),(23,19)),((0,10),(32,1))),
    (((0,5),(25,17)),((0,10),(3,26))),
    (((1,1),(23,19)),((1,10),(32,1))),
    (((0,10),(29,11)),((0,11),(0,26))),
    (((0,21),(29,3)),((0,22),(24,13))),
    (((0,2),(23,19)),((0,5),(14,24))),
    (((0,6),(31,8)),((0,9),(31,7))),
    (((0,7),(6,26)),((0,7),(30,10))),
    (((0,10),(19,21)),((0,15),(24,16))),
    (((0,8),(21,20)),((0,9),(13,24))),
    (((0,0),(32,6)),((0,4),(27,15))),
    (((0,5),(20,21)),((0,7),(16,23))),
    (((0,1),(32,6)),((0,5),(24,18))),
    (((0,3),(23,19)),((0,7),(18,22))),
    (((0,46),(1,4)),((1,1),(32,6))),
    (((0,10),(32,2)),((0,15),(13,23))),
    (((0,0),(8,26)),((0,6),(11,25))),
    (((0,2),(32,6)),((0,8),(32,4))),
    (((0,0),(28,14)),((0,1),(8,26))),
    (((0,18),(11,23)),((0,25),(27,5))),
    (((0,1),(28,14)),((0,32),(5,19))),
    (((0,9),(10,25)),((0,9),(28,13))),
    (((0,6),(14,24)),((0,6),(26,16))),
    (((0,2),(8,26)),((0,10),(4,26))),
    (((0,4),(23,19)),((0,5),(27,15))),
    (((0,2),(28,14)),((0,3),(32,6))),
    (((0,0),(30,11)),((0,7),(31,8))),
    (((0,0),(31,9)),((0,6),(7,26))),
    (((0,1),(30,11)),((0,6),(20,21))),
    (((0,0),(12,25)),((0,1),(31,9))),
    (((0,7),(29,12)),((0,8),(6,26))),
    (((0,1),(12,25)),((0,3),(8,26))),
    (((0,11),(32,1)),((0,39),(18,1))),
    (((0,2),(30,11)),((0,3),(28,14))),
    (((0,0),(17,23)),((0,2),(31,9))),
    (((0,0),(33,0)),((0,9),(21,20))),
    (((0,1),(17,23)),((0,2),(12,25))),
    (((0,1),(33,0)),((0,15),(26,14))),
    (((0,5),(23,19)),((0,7),(25,17))),
    (((0,0),(22,20)),((0,10),(32,3))),
    (((0,11),(19,21)),((0,14),(7,25))),
    (((0,0),(33,1)),((0,1),(22,20))),
    (((0,2),(33,0)),((0,3),(31,9))),
    (((0,1),(33,1)),((0,9),(32,4))),
    (((0,3),(12,25)),((0,4),(28,14))),
    (((0,13),(8,25)),((0,13),(20,20))),
    (((0,2),(22,20)),((0,12),(26,15))),
    (((0,7),(7,26)),((0,11),(32,2))),
    (((0,0),(19,22)),((0,2),(33,1))),
    (((0,3),(17,23)),((0,7),(24,18))),
    (((0,1),(19,22)),((0,3),(33,0))),
    (((0,10),(5,26)),((0,20),(15,21))),
    (((0,4),(30,11)),((0,12),(2,26))),
    (((0,0),(15,24)),((0,4),(31,9))),
    (((0,3),(22,20)),((0,23),(27,8))),
    (((0,1),(15,24)),((0,2),(19,22))),
    (((0,0),(0,27)),((0,0),(33,2))),
    (((0,16),(5,25)),((0,16),(29,9))),
    (((0,1),(0,27)),((0,1),(33,2))),
    (((0,8),(11,25)),((0,8),(32,5))),
    (((0,0),(1,27)),((0,2),(15,24))),
    (((0,4),(33,0)),((0,7),(27,15))),
    (((0,1),(1,27)),((0,9),(18,22))),
    (((0,2),(0,27)),((0,2),(33,2))),
    (((0,10),(21,20)),((0,18),(26,13))),
    (((0,4),(22,20)),((0,8),(14,24))),
    (((0,5),(30,11)),((0,14),(30,8))),
    (((0,0),(29,13)),((0,2),(1,27))),
    (((0,0),(9,26)),((0,3),(15,24))),
    (((0,1),(29,13)),((0,5),(12,25))),
    (((0,0),(2,27)),((0,0),(32,7))),
    (((0,3),(0,27)),((0,3),(33,2))),
    (((0,1),(2,27)),((0,1),(32,7))),
    (((0,6),(8,26)),((0,13),(24,17))),
    (((0,2),(29,13)),((0,4),(19,22))),
    (((0,2),(9,26)),((0,3),(1,27))),
    (((0,13),(0,26)),((0,20),(13,22)))]
  have hc : ∀ i : Fin 100, Good (3242+i.val) (c i).1 ∧
      Good (3242+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3242,by omega⟩
  have he : 3242+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3342 (n : ℕ) (hlo : 3342≤n) (hhi : n<3442) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(2,27)),((0,2),(32,7))),
    (((0,17),(15,22)),((0,17),(30,6))),
    (((0,4),(15,24)),((0,5),(22,20))),
    (((0,0),(33,3)),((0,13),(1,26))),
    (((0,5),(33,1)),((0,20),(30,1))),
    (((0,1),(33,3)),((0,3),(29,13))),
    (((0,3),(9,26)),((0,6),(30,11))),
    (((0,6),(31,9)),((0,8),(27,15))),
    (((0,3),(2,27)),((0,3),(32,7))),
    (((0,0),(3,27)),((0,4),(1,27))),
    (((0,2),(33,3)),((0,7),(32,6))),
    (((0,1),(3,27)),((0,5),(19,22))),
    (((0,10),(16,23)),((0,18),(12,23))),
    (((0,12),(4,26)),((0,13),(2,26))),
    (((0,6),(17,23)),((0,9),(14,24))),
    (((0,6),(33,0)),((0,23),(29,0))),
    (((0,2),(3,27)),((0,4),(29,13))),
    (((0,4),(9,26)),((0,18),(2,25))),
    (((0,0),(21,21)),((0,3),(33,3))),
    (((0,4),(2,27)),((0,4),(32,7))),
    (((0,1),(21,21)),((0,9),(20,21))),
    (((0,6),(33,1)),((0,8),(23,19))),
    (((0,13),(32,0)),((0,19),(14,22))),
    (((0,5),(1,27)),((0,13),(15,23))),
    (((0,3),(3,27)),((0,27),(27,3))),
    (((0,2),(21,21)),((0,12),(31,7))),
    (((0,7),(30,11)),((0,13),(30,9))),
    (((0,7),(31,9)),((0,10),(31,8))),
    (((0,0),(13,25)),((0,6),(19,22))),
    (((0,4),(33,3)),((0,7),(12,25))),
    (((0,1),(13,25)),((0,5),(29,13))),
    (((0,0),(4,27)),((0,5),(9,26))),
    (((0,17),(19,20)),((0,23),(7,23))),
    (((0,1),(4,27)),((0,3),(21,21))),
    (((0,7),(17,23)),((0,24),(28,5))),
    (((0,2),(13,25)),((0,4),(3,27))),
    (((0,0),(33,4)),((0,6),(0,27))),
    (((0,0),(31,10)),((0,10),(11,25))),
    (((0,0),(26,17)),((0,1),(33,4))),
    (((0,1),(31,10)),((0,7),(22,20))),
    (((0,1),(26,17)),((0,6),(1,27))),
    (((0,7),(33,1)),((0,8),(28,14))),
    (((0,16),(31,4)),((0,36),(21,4))),
    (((0,0),(25,18)),((0,2),(33,4))),
    (((0,2),(31,10)),((0,4),(21,21))),
    (((0,1),(25,18)),((0,2),(26,17))),
    (((0,3),(4,27)),((0,11),(18,22))),
    (((0,6),(29,13)),((0,9),(23,19))),
    (((0,0),(27,16)),((0,6),(9,26))),
    (((0,0),(10,26)),((0,5),(3,27))),
    (((0,1),(27,16)),((0,2),(25,18))),
    (((0,1),(10,26)),((0,3),(33,4))),
    (((0,3),(31,10)),((0,8),(12,25))),
    (((0,3),(26,17)),((0,7),(15,24))),
    (((0,0),(30,12)),((0,4),(13,25))),
    (((0,2),(27,16)),((0,18),(4,25))),
    (((0,1),(30,12)),((0,2),(10,26))),
    (((0,4),(4,27)),((0,8),(17,23))),
    (((0,3),(25,18)),((0,5),(21,21))),
    (((0,0),(5,27)),((0,9),(32,6))),
    (((0,6),(33,3)),((0,7),(1,27))),
    (((0,1),(5,27)),((0,2),(30,12))),
    (((0,0),(32,8)),((0,4),(33,4))),
    (((0,0),(18,23)),((0,0),(24,19))),
    (((0,1),(32,8)),((0,3),(10,26))),
    (((0,1),(18,23)),((0,1),(24,19))),
    (((0,2),(5,27)),((0,6),(3,27))),
    (((0,7),(29,13)),((0,9),(28,14))),
    (((0,5),(13,25)),((0,7),(9,26))),
    (((0,2),(32,8)),((0,3),(30,12))),
    (((0,0),(16,24)),((0,2),(18,23))),
    (((0,5),(4,27)),((0,8),(19,22))),
    (((0,1),(16,24)),((0,14),(29,11))),
    (((0,0),(28,15)),((0,18),(31,1))),
    (((0,3),(5,27)),((0,4),(27,16))),
    (((0,1),(28,15)),((0,4),(10,26))),
    (((0,5),(33,4)),((0,8),(15,24))),
    (((0,2),(16,24)),((0,3),(32,8))),
    (((0,0),(33,5)),((0,3),(18,23))),
    (((0,8),(0,27)),((0,8),(33,2))),
    (((0,1),(33,5)),((0,2),(28,15))),
    (((0,11),(20,21)),((0,12),(18,22))),
    (((0,11),(24,18)),((0,19),(20,19))),
    (((0,5),(25,18)),((0,8),(1,27))),
    (((0,9),(33,0)),((0,14),(32,2))),
    (((0,2),(33,5)),((0,3),(16,24))),
    (((0,7),(3,27)),((0,14),(22,19))),
    (((0,46),(7,4)),((0,47),(2,4))),
    (((0,3),(28,15)),((0,4),(32,8))),
    (((0,0),(20,22)),((0,4),(18,23))),
    (((0,8),(29,13)),((0,9),(33,1))),
    (((0,1),(20,22)),((0,8),(9,26))),
    (((0,13),(21,20)),((0,14),(4,26))),
    (((0,0),(6,27)),((0,3),(33,5))),
    (((0,5),(30,12)),((0,6),(31,10))),
    (((0,1),(6,27)),((0,6),(26,17))),
    (((0,2),(20,22)),((0,4),(16,24))),
    (((0,9),(19,22)),((0,17),(21,19))),
    (((0,0),(23,20)),((0,12),(29,12))),
    (((0,4),(28,15)),((0,5),(5,27)))]
  have hc : ∀ i : Fin 100, Good (3342+i.val) (c i).1 ∧
      Good (3342+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3342,by omega⟩
  have he : 3342+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3442 (n : ℕ) (hlo : 3442≤n) (hhi : n<3542) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(23,20)),((0,2),(6,27))),
    (((0,22),(15,21)),((0,44),(4,10))),
    (((0,5),(32,8)),((0,9),(15,24))),
    (((0,5),(18,23)),((0,5),(24,19))),
    (((0,3),(20,22)),((0,4),(33,5))),
    (((0,2),(23,20)),((0,6),(27,16))),
    (((0,6),(10,26)),((0,12),(25,17))),
    (((0,10),(12,25)),((0,14),(13,24))),
    (((0,3),(6,27)),((0,7),(4,27))),
    (((0,8),(3,27)),((0,9),(1,27))),
    (((0,0),(14,25)),((0,5),(16,24))),
    (((0,6),(30,12)),((0,15),(30,9))),
    (((0,1),(14,25)),((0,10),(17,23))),
    (((0,0),(11,26)),((0,0),(29,14))),
    (((0,7),(31,10)),((0,15),(3,26))),
    (((0,1),(11,26)),((0,1),(29,14))),
    (((0,6),(5,27)),((0,9),(29,13))),
    (((0,2),(14,25)),((0,9),(9,26))),
    (((0,5),(33,5)),((0,8),(21,21))),
    (((0,4),(6,27)),((0,6),(32,8))),
    (((0,2),(11,26)),((0,2),(29,14))),
    (((0,15),(19,21)),((0,23),(3,24))),
    (((0,16),(12,24)),((0,20),(1,25))),
    (((0,19),(31,0)),((0,35),(23,0))),
    (((0,4),(23,20)),((0,28),(23,12))),
    (((0,3),(14,25)),((0,7),(27,16))),
    (((0,7),(10,26)),((0,10),(19,22))),
    (((0,6),(16,24)),((0,20),(12,23))),
    (((0,3),(11,26)),((0,3),(29,14))),
    (((0,0),(33,6)),((0,5),(20,22))),
    (((0,6),(28,15)),((0,15),(22,19))),
    (((0,1),(33,6)),((0,7),(30,12))),
    (((0,13),(31,8)),((0,20),(2,25))),
    (((0,0),(7,27)),((0,0),(31,11))),
    (((0,10),(0,27)),((0,10),(33,2))),
    (((0,1),(7,27)),((0,1),(31,11))),
    (((0,2),(33,6)),((0,4),(14,25))),
    (((0,8),(31,10)),((0,11),(31,9))),
    (((0,5),(23,20)),((0,8),(26,17))),
    (((0,4),(11,26)),((0,4),(29,14))),
    (((0,0),(32,9)),((0,2),(7,27))),
    (((0,14),(32,4)),((0,19),(19,20))),
    (((0,1),(32,9)),((0,13),(11,25))),
    (((0,8),(25,18)),((0,12),(23,19))),
    (((0,3),(33,6)),((0,9),(21,21))),
    (((0,10),(29,13)),((0,11),(33,0))),
    (((0,6),(20,22)),((0,10),(9,26))),
    (((0,2),(32,9)),((0,7),(16,24))),
    (((0,0),(22,21)),((0,3),(7,27))),
    (((0,8),(10,26)),((0,11),(22,20))),
    (((0,1),(22,21)),((0,5),(14,25))),
    (((0,11),(33,1)),((0,15),(13,24))),
    (((0,15),(32,3)),((0,16),(9,25))),
    (((0,5),(11,26)),((0,5),(29,14))),
    (((0,8),(30,12)),((0,9),(13,25))),
    (((0,2),(22,21)),((0,3),(32,9))),
    (((1,8),(30,12)),((1,9),(13,25))),
    (((0,9),(4,27)),((0,18),(7,25))),
    (((0,10),(33,3)),((0,11),(19,22))),
    (((0,4),(7,27)),((0,4),(31,11))),
    (((0,0),(34,0)),((0,14),(18,22))),
    (((0,12),(8,26)),((0,16),(3,26))),
    (((0,1),(34,0)),((0,8),(32,8))),
    (((0,3),(22,21)),((0,8),(18,23))),
    (((0,9),(26,17)),((0,10),(3,27))),
    (((0,39),(3,16)),((0,40),(4,15))),
    (((0,0),(34,1)),((0,4),(32,9))),
    (((0,2),(34,0)),((0,6),(14,25))),
    (((0,0),(30,13)),((0,1),(34,1))),
    (((0,5),(33,6)),((0,9),(25,18))),
    (((0,0),(17,24)),((0,1),(30,13))),
    (((0,12),(30,11)),((0,23),(5,24))),
    (((0,1),(17,24)),((0,12),(31,9))),
    (((0,2),(34,1)),((0,5),(7,27))),
    (((0,4),(22,21)),((0,9),(27,16))),
    (((0,0),(19,23)),((0,2),(30,13))),
    (((0,17),(25,16)),((0,24),(2,24))),
    (((0,1),(19,23)),((0,2),(17,24))),
    (((0,8),(33,5)),((0,11),(9,26))),
    (((0,0),(8,27)),((0,12),(17,23))),
    (((0,5),(32,9)),((0,9),(30,12))),
    (((0,0),(34,2)),((0,1),(8,27))),
    (((0,2),(19,23)),((0,20),(31,0))),
    (((0,0),(12,26)),((0,1),(34,2))),
    (((0,12),(22,20)),((0,21),(1,25))),
    (((0,1),(12,26)),((0,3),(17,24))),
    (((0,2),(8,27)),((0,4),(34,0))),
    (((0,7),(14,25)),((0,18),(31,5))),
    (((0,2),(34,2)),((0,5),(22,21))),
    (((0,0),(33,7)),((0,8),(20,22))),
    (((0,2),(12,26)),((0,3),(19,23))),
    (((0,1),(33,7)),((0,10),(33,4))),
    (((0,4),(34,1)),((0,10),(31,10))),
    (((0,8),(6,27)),((0,10),(26,17))),
    (((0,3),(8,27)),((0,4),(30,13))),
    (((0,14),(20,21)),((0,16),(31,7))),
    (((0,2),(33,7)),((0,3),(34,2))),
    (((0,0),(26,18)),((0,6),(32,9))),
    (((0,0),(15,25)),((0,0),(27,17))),
    (((0,1),(26,18)),((0,9),(28,15)))]
  have hc : ∀ i : Fin 100, Good (3442+i.val) (c i).1 ∧
      Good (3442+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3442,by omega⟩
  have he : 3442+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3542 (n : ℕ) (hlo : 3542≤n) (hhi : n<3642) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(15,25)),((0,1),(27,17))),
    (((0,4),(19,23)),((0,12),(0,27))),
    (((0,15),(16,23)),((0,17),(9,25))),
    (((0,10),(27,16)),((0,18),(8,25))),
    (((0,2),(26,18)),((0,3),(33,7))),
    (((0,0),(34,3)),((0,2),(15,25))),
    (((0,5),(34,1)),((0,7),(33,6))),
    (((0,1),(34,3)),((0,4),(34,2))),
    (((0,5),(30,13)),((0,14),(27,15))),
    (((0,4),(12,26)),((0,10),(30,12))),
    (((0,5),(17,24)),((0,7),(7,27))),
    (((0,0),(25,19)),((0,16),(5,26))),
    (((0,2),(34,3)),((0,3),(26,18))),
    (((0,0),(21,22)),((0,1),(25,19))),
    (((0,0),(28,16)),((0,10),(5,27))),
    (((0,1),(21,22)),((0,4),(33,7))),
    (((0,1),(28,16)),((0,34),(7,19))),
    (((0,6),(34,0)),((0,7),(32,9))),
    (((0,2),(25,19)),((0,10),(18,23))),
    (((0,5),(8,27)),((0,9),(6,27))),
    (((0,2),(21,22)),((0,3),(34,3))),
    (((0,2),(28,16)),((0,5),(34,2))),
    (((0,13),(22,20)),((0,14),(23,19))),
    (((0,4),(26,18)),((0,5),(12,26))),
    (((0,4),(15,25)),((0,4),(27,17))),
    (((0,6),(30,13)),((0,7),(22,21))),
    (((0,3),(25,19)),((0,19),(14,23))),
    (((0,0),(32,10)),((0,6),(17,24))),
    (((0,0),(0,28)),((0,3),(21,22))),
    (((0,1),(32,10)),((0,3),(28,16))),
    (((0,1),(0,28)),((0,11),(25,18))),
    (((0,0),(9,27)),((0,4),(34,3))),
    (((0,0),(1,28)),((0,6),(19,23))),
    (((0,1),(9,27)),((0,8),(7,27))),
    (((0,1),(1,28)),((0,2),(32,10))),
    (((0,2),(0,28)),((0,11),(27,16))),
    (((0,6),(8,27)),((0,9),(14,25))),
    (((0,4),(25,19)),((0,5),(26,18))),
    (((0,0),(31,12)),((0,0),(34,4))),
    (((0,2),(1,28)),((0,4),(21,22))),
    (((0,0),(24,20)),((0,1),(31,12))),
    (((0,11),(30,12)),((0,40),(14,11))),
    (((0,0),(2,28)),((0,1),(24,20))),
    (((0,3),(0,28)),((0,7),(34,1))),
    (((0,1),(2,28)),((0,10),(20,22))),
    (((0,0),(29,15)),((0,2),(31,12))),
    (((0,3),(9,27)),((0,6),(33,7))),
    (((0,1),(29,15)),((0,2),(24,20))),
    (((0,8),(22,21)),((0,10),(6,27))),
    (((0,2),(2,28)),((0,11),(32,8))),
    (((0,11),(18,23)),((0,11),(24,19))),
    (((0,5),(25,19)),((0,13),(9,26))),
    (((0,2),(29,15)),((0,7),(19,23))),
    (((0,3),(31,12)),((0,3),(34,4))),
    (((0,4),(0,28)),((0,5),(28,16))),
    (((0,3),(24,20)),((0,6),(15,25))),
    (((0,7),(8,27)),((0,32),(3,21))),
    (((0,3),(2,28)),((0,4),(9,27))),
    (((0,0),(3,28)),((0,0),(33,8))),
    (((0,0),(13,26)),((0,9),(7,27))),
    (((0,1),(3,28)),((0,1),(33,8))),
    (((0,1),(13,26)),((0,17),(5,26))),
    (((0,6),(34,3)),((0,20),(27,13))),
    (((0,13),(33,3)),((0,14),(22,20))),
    (((0,4),(31,12)),((0,4),(34,4))),
    (((0,2),(3,28)),((0,2),(33,8))),
    (((0,2),(13,26)),((0,4),(24,20))),
    (((0,5),(32,10)),((0,28),(1,23))),
    (((0,4),(2,28)),((0,5),(0,28))),
    (((0,13),(3,27)),((0,34),(3,20))),
    (((0,6),(21,22)),((0,8),(17,24))),
    (((0,4),(29,15)),((0,5),(9,27))),
    (((0,5),(1,28)),((0,14),(19,22))),
    (((0,3),(3,28)),((0,3),(33,8))),
    (((0,3),(13,26)),((0,7),(26,18))),
    (((0,7),(15,25)),((0,7),(27,17))),
    (((0,0),(18,24)),((0,11),(20,22))),
    (((0,14),(15,24)),((0,26),(27,9))),
    (((0,1),(18,24)),((0,5),(31,12))),
    (((0,8),(8,27)),((0,27),(27,8))),
    (((0,0),(4,28)),((0,0),(34,5))),
    (((0,8),(34,2)),((0,12),(5,27))),
    (((0,1),(4,28)),((0,1),(34,5))),
    (((0,2),(18,24)),((0,8),(12,26))),
    (((0,0),(23,21)),((0,4),(3,28))),
    (((0,4),(13,26)),((0,5),(29,15))),
    (((0,1),(23,21)),((0,9),(34,0))),
    (((0,2),(4,28)),((0,2),(34,5))),
    (((0,6),(9,27)),((0,7),(25,19))),
    (((0,0),(10,27)),((0,6),(1,28))),
    (((0,7),(21,22)),((0,19),(0,26))),
    (((0,0),(30,14)),((0,1),(10,27))),
    (((0,0),(16,25)),((0,9),(34,1))),
    (((0,0),(20,23)),((0,1),(30,14))),
    (((0,1),(16,25)),((0,9),(30,13))),
    (((0,1),(20,23)),((0,3),(4,28))),
    (((0,2),(10,27)),((0,9),(17,24))),
    (((0,6),(24,20)),((0,8),(26,18))),
    (((0,2),(30,14)),((0,5),(3,28))),
    (((0,2),(16,25)),((0,3),(23,21)))]
  have hc : ∀ i : Fin 100, Good (3542+i.val) (c i).1 ∧
      Good (3542+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3542,by omega⟩
  have he : 3542+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3642 (n : ℕ) (hlo : 3642≤n) (hhi : n<3742) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(20,23)),((0,11),(11,26))),
    (((0,9),(19,23)),((0,17),(18,22))),
    (((0,4),(18,24)),((0,6),(29,15))),
    (((0,10),(22,21)),((0,13),(25,18))),
    (((0,3),(10,27)),((0,7),(32,10))),
    (((0,7),(0,28)),((0,8),(34,3))),
    (((0,3),(30,14)),((0,4),(4,28))),
    (((0,3),(16,25)),((0,9),(34,2))),
    (((0,0),(5,28)),((0,3),(20,23))),
    (((0,7),(1,28)),((0,9),(12,26))),
    (((0,1),(5,28)),((0,4),(23,21))),
    (((0,8),(25,19)),((0,12),(20,22))),
    (((1,1),(5,28)),((1,4),(23,21))),
    (((0,8),(21,22)),((0,16),(23,19))),
    (((0,8),(28,16)),((0,13),(30,12))),
    (((0,2),(5,28)),((0,4),(10,27))),
    (((0,5),(18,24)),((0,6),(13,26))),
    (((0,4),(30,14)),((0,7),(24,20))),
    (((0,4),(16,25)),((0,17),(29,12))),
    (((0,4),(20,23)),((0,7),(2,28))),
    (((0,5),(4,28)),((0,5),(34,5))),
    (((0,10),(34,1)),((0,15),(15,24))),
    (((0,7),(29,15)),((0,13),(32,8))),
    (((0,0),(32,11)),((0,3),(5,28))),
    (((0,5),(23,21)),((0,9),(15,25))),
    (((0,1),(32,11)),((0,10),(17,24))),
    (((0,17),(25,17)),((0,19),(27,14))),
    (((0,8),(32,10)),((0,11),(32,9))),
    (((0,8),(0,28)),((0,15),(1,27))),
    (((0,5),(10,27)),((0,14),(13,25))),
    (((0,2),(32,11)),((0,10),(19,23))),
    (((0,0),(34,6)),((0,5),(30,14))),
    (((0,5),(16,25)),((0,8),(1,28))),
    (((0,1),(34,6)),((0,5),(20,23))),
    (((0,4),(5,28)),((0,10),(8,27))),
    (((0,7),(3,28)),((0,7),(33,8))),
    (((0,0),(33,9)),((0,7),(13,26))),
    (((0,6),(4,28)),((0,6),(34,5))),
    (((0,1),(33,9)),((0,2),(34,6))),
    (((0,9),(21,22)),((0,14),(26,17))),
    (((0,8),(24,20)),((0,9),(28,16))),
    (((0,0),(14,26)),((0,6),(23,21))),
    (((0,0),(6,28)),((0,8),(2,28))),
    (((0,0),(22,22)),((0,1),(14,26))),
    (((0,1),(6,28)),((0,10),(33,7))),
    (((0,1),(22,22)),((0,8),(29,15))),
    (((0,3),(34,6)),((0,6),(10,27))),
    (((0,11),(34,0)),((0,21),(14,23))),
    (((0,2),(14,26)),((0,5),(5,28))),
    (((0,2),(6,28)),((0,4),(32,11))),
    (((0,2),(22,22)),((0,6),(20,23))),
    (((0,3),(33,9)),((0,12),(33,6))),
    (((0,0),(31,13)),((0,10),(26,18))),
    (((0,0),(11,27)),((0,7),(18,24))),
    (((0,1),(31,13)),((0,9),(0,28))),
    (((0,1),(11,27)),((0,11),(30,13))),
    (((0,3),(14,26)),((0,16),(33,1))),
    (((0,0),(27,18)),((0,3),(6,28))),
    (((0,3),(22,22)),((0,8),(3,28))),
    (((0,1),(27,18)),((0,2),(31,13))),
    (((0,2),(11,27)),((0,10),(34,3))),
    (((0,7),(23,21)),((0,28),(23,14))),
    (((0,4),(33,9)),((0,11),(19,23))),
    (((0,5),(32,11)),((0,14),(32,8))),
    (((0,0),(28,17)),((0,2),(27,18))),
    (((0,0),(26,19)),((0,6),(5,28))),
    (((0,1),(28,17)),((0,7),(10,27))),
    (((0,1),(26,19)),((0,3),(31,13))),
    (((0,0),(35,0)),((0,3),(11,27))),
    (((0,4),(22,22)),((0,7),(16,25))),
    (((0,1),(35,0)),((0,7),(20,23))),
    (((0,2),(28,17)),((0,5),(34,6))),
    (((0,2),(26,19)),((0,3),(27,18))),
    (((0,13),(11,26)),((0,13),(29,14))),
    (((0,0),(35,1)),((0,14),(28,15))),
    (((0,2),(35,0)),((0,16),(1,27))),
    (((0,1),(35,1)),((0,5),(33,9))),
    (((0,18),(11,25)),((0,18),(32,5))),
    (((0,4),(31,13)),((0,20),(32,1))),
    (((0,3),(28,17)),((0,4),(11,27))),
    (((0,3),(26,19)),((0,6),(32,11))),
    (((0,2),(35,1)),((0,5),(14,26))),
    (((0,0),(7,28)),((0,5),(6,28))),
    (((0,3),(35,0)),((0,4),(27,18))),
    (((0,1),(7,28)),((0,8),(23,21))),
    (((0,7),(5,28)),((0,9),(13,26))),
    (((0,0),(29,16)),((0,10),(9,27))),
    (((0,10),(1,28)),((0,22),(31,4))),
    (((0,0),(19,24)),((0,0),(25,20))),
    (((0,0),(35,2)),((0,2),(7,28))),
    (((0,1),(19,24)),((0,1),(25,20))),
    (((0,0),(34,7)),((0,1),(35,2))),
    (((0,0),(17,25)),((0,5),(31,13))),
    (((0,1),(34,7)),((0,2),(29,16))),
    (((0,1),(17,25)),((0,4),(35,0))),
    (((0,2),(19,24)),((0,2),(25,20))),
    (((0,2),(35,2)),((0,46),(10,7))),
    (((0,3),(7,28)),((0,5),(27,18))),
    (((0,2),(34,7)),((0,6),(14,26))),
    (((0,2),(17,25)),((0,6),(6,28)))]
  have hc : ∀ i : Fin 100, Good (3642+i.val) (c i).1 ∧
      Good (3642+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3642,by omega⟩
  have he : 3642+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3742 (n : ℕ) (hlo : 3742≤n) (hhi : n<3842) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,4),(35,1)),((0,6),(22,22))),
    (((0,3),(29,16)),((0,11),(28,16))),
    (((0,9),(18,24)),((0,18),(27,15))),
    (((0,3),(19,24)),((0,3),(25,20))),
    (((0,3),(35,2)),((0,5),(28,17))),
    (((0,5),(26,19)),((0,12),(12,26))),
    (((0,3),(34,7)),((0,9),(4,28))),
    (((0,3),(17,25)),((0,15),(32,8))),
    (((0,4),(7,28)),((0,5),(35,0))),
    (((0,6),(31,13)),((0,29),(18,18))),
    (((0,6),(11,27)),((0,9),(23,21))),
    (((0,12),(33,7)),((0,14),(14,25))),
    (((0,4),(29,16)),((0,22),(14,23))),
    (((0,0),(35,3)),((0,7),(33,9))),
    (((0,4),(19,24)),((0,4),(25,20))),
    (((0,1),(35,3)),((0,4),(35,2))),
    (((0,18),(23,19)),((0,20),(13,24))),
    (((0,0),(21,23)),((0,4),(34,7))),
    (((0,4),(17,25)),((0,7),(14,26))),
    (((0,1),(21,23)),((0,7),(6,28))),
    (((0,2),(35,3)),((0,7),(22,22))),
    (((0,6),(28,17)),((0,17),(0,27))),
    (((0,5),(7,28)),((0,6),(26,19))),
    (((0,0),(12,27)),((0,0),(30,15))),
    (((0,2),(21,23)),((0,23),(30,7))),
    (((0,1),(12,27)),((0,1),(30,15))),
    (((0,0),(24,21)),((0,5),(29,16))),
    (((0,11),(24,20)),((0,12),(34,3))),
    (((0,0),(8,28)),((0,0),(32,12))),
    (((0,0),(15,26)),((0,5),(35,2))),
    (((0,1),(8,28)),((0,1),(32,12))),
    (((0,1),(15,26)),((0,5),(34,7))),
    (((0,3),(21,23)),((0,5),(17,25))),
    (((0,2),(24,21)),((0,12),(25,19))),
    (((0,7),(27,18)),((0,9),(5,28))),
    (((0,2),(8,28)),((0,2),(32,12))),
    (((0,2),(15,26)),((0,8),(33,9))),
    (((0,25),(21,18)),((0,27),(29,5))),
    (((0,3),(12,27)),((0,3),(30,15))),
    (((0,4),(35,3)),((0,6),(7,28))),
    (((0,16),(27,16)),((0,21),(32,1))),
    (((0,3),(24,21)),((0,7),(28,17))),
    (((0,7),(26,19)),((0,8),(6,28))),
    (((0,3),(8,28)),((0,3),(32,12))),
    (((0,3),(15,26)),((0,10),(10,27))),
    (((0,6),(19,24)),((0,6),(25,20))),
    (((0,0),(35,4)),((0,6),(35,2))),
    (((0,10),(16,25)),((0,18),(12,25))),
    (((0,1),(35,4)),((0,6),(34,7))),
    (((0,4),(12,27)),((0,4),(30,15))),
    (((0,12),(0,28)),((0,20),(32,4))),
    (((0,7),(35,1)),((0,16),(5,27))),
    (((0,4),(24,21)),((0,8),(31,13))),
    (((0,2),(35,4)),((0,5),(35,3))),
    (((0,4),(8,28)),((0,4),(32,12))),
    (((0,4),(15,26)),((0,15),(14,25))),
    (((0,40),(4,17)),((0,41),(5,16))),
    (((0,5),(21,23)),((0,8),(27,18))),
    (((0,13),(15,25)),((0,13),(27,17))),
    (((0,7),(7,28)),((0,18),(33,1))),
    (((0,0),(34,8)),((0,12),(31,12))),
    (((0,3),(35,4)),((0,14),(34,0))),
    (((0,1),(34,8)),((0,9),(33,9))),
    (((0,5),(12,27)),((0,5),(30,15))),
    (((0,8),(28,17)),((0,12),(2,28))),
    (((0,7),(19,24)),((0,7),(25,20))),
    (((0,5),(24,21)),((0,7),(35,2))),
    (((0,2),(34,8)),((0,9),(14,26))),
    (((0,5),(8,28)),((0,5),(32,12))),
    (((0,5),(15,26)),((0,7),(17,25))),
    (((0,6),(35,3)),((0,16),(33,5))),
    (((0,11),(23,21)),((0,13),(25,19))),
    (((0,4),(35,4)),((0,19),(23,19))),
    (((0,13),(21,22)),((0,17),(4,27))),
    (((0,6),(21,23)),((0,8),(35,1))),
    (((0,0),(31,14)),((0,3),(34,8))),
    (((0,11),(10,27)),((0,14),(19,23))),
    (((0,1),(31,14)),((0,34),(4,21))),
    (((0,9),(31,13)),((0,10),(32,11))),
    (((0,0),(23,22)),((0,9),(11,27))),
    (((0,0),(9,28)),((0,6),(12,27))),
    (((0,1),(23,22)),((0,12),(13,26))),
    (((0,1),(9,28)),((0,2),(31,14))),
    (((0,6),(24,21)),((0,9),(27,18))),
    (((0,14),(12,26)),((0,19),(32,6))),
    (((0,6),(8,28)),((0,6),(32,12))),
    (((0,0),(0,29)),((0,2),(23,22))),
    (((0,2),(9,28)),((0,13),(32,10))),
    (((0,0),(35,5)),((0,1),(0,29))),
    (((0,8),(35,2)),((0,44),(17,2))),
    (((0,0),(1,29)),((0,1),(35,5))),
    (((0,8),(34,7)),((0,9),(26,19))),
    (((0,1),(1,29)),((0,8),(17,25))),
    (((0,2),(0,29)),((0,15),(22,21))),
    (((0,3),(23,22)),((0,7),(21,23))),
    (((0,2),(35,5)),((0,3),(9,28))),
    (((0,10),(14,26)),((0,17),(30,12))),
    (((0,2),(1,29)),((0,10),(6,28))),
    (((0,0),(18,25)),((0,10),(22,22))),
    (((0,0),(13,27)),((0,14),(15,25)))]
  have hc : ∀ i : Fin 100, Good (3742+i.val) (c i).1 ∧
      Good (3742+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3742,by omega⟩
  have he : 3742+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3842 (n : ℕ) (hlo : 3842≤n) (hhi : n<3942) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,0),(2,29)),((0,1),(18,25))),
    (((0,1),(13,27)),((0,3),(0,29))),
    (((0,1),(2,29)),((0,12),(4,28))),
    (((0,3),(35,5)),((0,6),(35,4))),
    (((0,17),(32,8)),((0,18),(3,27))),
    (((0,2),(18,25)),((0,3),(1,29))),
    (((0,0),(20,24)),((0,2),(13,27))),
    (((0,2),(2,29)),((0,10),(31,13))),
    (((0,1),(20,24)),((0,9),(7,28))),
    (((0,19),(33,0)),((0,23),(28,12))),
    (((0,11),(32,11)),((0,25),(4,25))),
    (((0,12),(10,27)),((0,15),(34,1))),
    (((0,4),(0,29)),((0,9),(29,16))),
    (((0,2),(20,24)),((0,3),(18,25))),
    (((0,3),(13,27)),((0,4),(35,5))),
    (((0,3),(2,29)),((0,5),(31,14))),
    (((0,0),(3,29)),((0,4),(1,29))),
    (((0,6),(34,8)),((0,8),(21,23))),
    (((0,1),(3,29)),((0,9),(17,25))),
    (((0,0),(33,11)),((0,5),(23,22))),
    (((0,5),(9,28)),((0,10),(26,19))),
    (((0,1),(33,11)),((0,3),(20,24))),
    (((0,19),(19,22)),((0,22),(22,19))),
    (((0,0),(16,26)),((0,0),(28,18))),
    (((0,4),(18,25)),((0,15),(8,27))),
    (((0,0),(27,19)),((0,1),(16,26))),
    (((0,2),(33,11)),((0,4),(2,29))),
    (((0,1),(27,19)),((0,19),(15,24))),
    (((0,5),(35,5)),((0,8),(8,28))),
    (((0,8),(15,26)),((0,10),(35,1))),
    (((0,2),(16,26)),((0,2),(28,18))),
    (((0,3),(3,29)),((0,17),(20,22))),
    (((0,2),(27,19)),((0,4),(20,24))),
    (((0,14),(1,28)),((0,18),(26,17))),
    (((0,3),(33,11)),((0,15),(33,7))),
    (((0,17),(6,27)),((0,23),(12,24))),
    (((0,0),(29,17)),((0,6),(23,22))),
    (((0,6),(9,28)),((0,7),(34,8))),
    (((0,0),(4,29)),((0,0),(10,28))),
    (((0,0),(35,6)),((0,5),(13,27))),
    (((0,1),(4,29)),((0,1),(10,28))),
    (((0,1),(35,6)),((0,10),(29,16))),
    (((0,0),(26,20)),((0,0),(32,13))),
    (((0,2),(29,17)),((0,6),(0,29))),
    (((0,1),(26,20)),((0,1),(32,13))),
    (((0,2),(4,29)),((0,2),(10,28))),
    (((0,2),(35,6)),((0,5),(20,24))),
    (((0,0),(22,23)),((0,6),(1,29))),
    (((0,21),(29,12)),((0,23),(1,26))),
    (((0,1),(22,23)),((0,2),(26,20))),
    (((0,15),(34,3)),((0,41),(21,1))),
    (((0,3),(29,17)),((0,4),(27,19))),
    (((0,7),(31,14)),((0,9),(24,21))),
    (((0,3),(4,29)),((0,3),(10,28))),
    (((0,2),(22,23)),((0,3),(35,6))),
    (((0,6),(18,25)),((0,9),(15,26))),
    (((0,5),(3,29)),((0,6),(13,27))),
    (((0,3),(26,20)),((0,3),(32,13))),
    (((0,12),(33,9)),((0,15),(21,22))),
    (((0,5),(33,11)),((0,14),(3,28))),
    (((0,8),(34,8)),((0,14),(13,26))),
    (((0,11),(35,1)),((0,43),(19,1))),
    (((0,3),(22,23)),((0,4),(29,17))),
    (((0,5),(16,26)),((0,5),(28,18))),
    (((0,0),(30,16)),((0,4),(4,29))),
    (((0,4),(35,6)),((0,5),(27,19))),
    (((0,0),(5,29)),((0,1),(30,16))),
    (((0,7),(1,29)),((0,16),(19,23))),
    (((0,1),(5,29)),((0,4),(26,20))),
    (((0,11),(7,28)),((0,19),(21,21))),
    (((0,46),(7,11)),((0,47),(2,11))),
    (((0,2),(30,16)),((0,16),(8,27))),
    (((0,9),(35,4)),((0,10),(21,23))),
    (((0,2),(5,29)),((0,4),(22,23))),
    (((0,0),(25,21)),((0,12),(31,13))),
    (((0,7),(18,25)),((0,8),(31,14))),
    (((0,1),(25,21)),((0,5),(29,17))),
    (((0,7),(2,29)),((0,14),(18,24))),
    (((0,5),(4,29)),((0,5),(10,28))),
    (((0,3),(30,16)),((0,5),(35,6))),
    (((0,6),(16,26)),((0,6),(28,18))),
    (((0,0),(14,27)),((0,2),(25,21))),
    (((0,0),(36,0)),((0,5),(26,20))),
    (((0,1),(14,27)),((0,7),(20,24))),
    (((0,1),(36,0)),((0,10),(15,26))),
    (((0,14),(23,21)),((0,15),(24,20))),
    (((0,8),(0,29)),((0,9),(34,8))),
    (((0,5),(22,23)),((0,12),(26,19))),
    (((0,0),(36,1)),((0,2),(14,27))),
    (((0,2),(36,0)),((0,3),(25,21))),
    (((0,1),(36,1)),((0,4),(30,16))),
    (((0,13),(34,6)),((0,41),(20,6))),
    (((0,4),(5,29)),((0,14),(30,14))),
    (((0,6),(29,17)),((0,7),(3,29))),
    (((0,14),(20,23)),((0,19),(25,18))),
    (((0,2),(36,1)),((0,6),(4,29))),
    (((0,3),(14,27)),((0,6),(35,6))),
    (((0,3),(36,0)),((0,16),(34,3))),
    (((0,8),(18,25)),((0,36),(25,4))),
    (((0,0),(35,7)),((0,6),(26,20)))]
  have hc : ∀ i : Fin 100, Good (3842+i.val) (c i).1 ∧
      Good (3842+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3842,by omega⟩
  have he : 3842+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_3942 (n : ℕ) (hlo : 3942≤n) (hhi : n<4042) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,0),(6,29)),((0,4),(25,21))),
    (((0,1),(35,7)),((0,9),(31,14))),
    (((0,0),(11,28)),((0,1),(6,29))),
    (((0,0),(36,2)),((0,3),(36,1))),
    (((0,1),(11,28)),((0,5),(30,16))),
    (((0,1),(36,2)),((0,9),(23,22))),
    (((0,2),(35,7)),((0,5),(5,29))),
    (((0,0),(31,15)),((0,2),(6,29))),
    (((0,4),(36,0)),((0,12),(29,16))),
    (((0,1),(31,15)),((0,2),(11,28))),
    (((0,0),(19,25)),((0,2),(36,2))),
    (((0,12),(35,2)),((0,21),(8,26))),
    (((0,1),(19,25)),((0,9),(0,29))),
    (((0,7),(29,17)),((0,11),(24,21))),
    (((0,2),(31,15)),((0,3),(35,7))),
    (((0,3),(6,29)),((0,7),(4,29))),
    (((0,7),(35,6)),((0,8),(3,29))),
    (((0,2),(19,25)),((0,3),(11,28))),
    (((0,3),(36,2)),((0,47),(14,2))),
    (((0,7),(26,20)),((0,7),(32,13))),
    (((0,16),(0,28)),((0,26),(13,23))),
    (((0,0),(24,22)),((0,5),(14,27))),
    (((0,3),(31,15)),((0,5),(36,0))),
    (((0,0),(17,26)),((0,1),(24,22))),
    (((0,0),(33,12)),((0,7),(22,23))),
    (((0,0),(34,10)),((0,1),(17,26))),
    (((0,1),(33,12)),((0,4),(6,29))),
    (((0,0),(36,3)),((0,1),(34,10))),
    (((0,2),(24,22)),((0,4),(11,28))),
    (((0,1),(36,3)),((0,4),(36,2))),
    (((0,0),(21,24)),((0,2),(17,26))),
    (((0,2),(33,12)),((0,6),(25,21))),
    (((0,1),(21,24)),((0,2),(34,10))),
    (((0,4),(31,15)),((0,11),(35,4))),
    (((0,2),(36,3)),((0,10),(23,22))),
    (((0,10),(9,28)),((0,12),(35,3))),
    (((0,3),(24,22)),((0,4),(19,25))),
    (((0,2),(21,24)),((0,14),(33,9))),
    (((0,3),(17,26)),((0,6),(14,27))),
    (((0,3),(33,12)),((0,5),(35,7))),
    (((0,0),(7,29)),((0,3),(34,10))),
    (((0,7),(30,16)),((0,10),(0,29))),
    (((0,1),(7,29)),((0,3),(36,3))),
    (((0,5),(36,2)),((0,7),(5,29))),
    (((0,14),(22,22)),((0,19),(6,27))),
    (((0,3),(21,24)),((0,6),(36,1))),
    (((0,13),(29,16)),((0,20),(33,4))),
    (((0,2),(7,29)),((0,4),(24,22))),
    (((0,12),(24,21)),((0,13),(19,24))),
    (((0,4),(17,26)),((0,9),(16,26))),
    (((0,4),(33,12)),((0,5),(19,25))),
    (((0,4),(34,10)),((0,7),(25,21))),
    (((0,13),(17,25)),((0,24),(19,21))),
    (((0,4),(36,3)),((0,10),(18,25))),
    (((0,10),(13,27)),((0,14),(11,27))),
    (((0,3),(7,29)),((0,10),(2,29))),
    (((0,4),(21,24)),((0,6),(35,7))),
    (((0,6),(6,29)),((0,29),(29,6))),
    (((0,7),(14,27)),((0,14),(27,18))),
    (((0,6),(11,28)),((0,7),(36,0))),
    (((0,0),(36,4)),((0,6),(36,2))),
    (((0,5),(24,22)),((0,10),(20,24))),
    (((0,1),(36,4)),((0,9),(29,17))),
    (((0,5),(17,26)),((0,18),(30,13))),
    (((0,5),(33,12)),((0,6),(31,15))),
    (((0,0),(32,14)),((0,5),(34,10))),
    (((0,4),(7,29)),((0,8),(5,29))),
    (((0,1),(32,14)),((0,2),(36,4))),
    (((0,0),(35,8)),((0,9),(26,20))),
    (((0,0),(15,27)),((0,14),(35,0))),
    (((0,1),(35,8)),((0,5),(21,24))),
    (((0,1),(15,27)),((0,10),(3,29))),
    (((0,0),(12,28)),((0,2),(32,14))),
    (((0,9),(22,23)),((0,11),(0,29))),
    (((0,1),(12,28)),((0,8),(25,21))),
    (((0,2),(35,8)),((0,3),(36,4))),
    (((0,2),(15,27)),((0,7),(35,7))),
    (((0,7),(6,29)),((0,11),(1,29))),
    (((0,6),(24,22)),((0,10),(16,26))),
    (((0,2),(12,28)),((0,7),(11,28))),
    (((0,3),(32,14)),((0,5),(7,29))),
    (((0,6),(33,12)),((0,8),(14,27))),
    (((0,6),(34,10)),((0,8),(36,0))),
    (((0,0),(23,23)),((0,3),(35,8))),
    (((0,3),(15,27)),((0,6),(36,3))),
    (((0,1),(23,23)),((0,11),(18,25))),
    (((0,0),(8,29)),((0,4),(36,4))),
    (((0,3),(12,28)),((0,6),(21,24))),
    (((0,1),(8,29)),((0,8),(36,1))),
    (((0,13),(15,26)),((0,14),(19,24))),
    (((0,2),(23,23)),((0,9),(30,16))),
    (((0,0),(28,19)),((0,4),(32,14))),
    (((0,9),(5,29)),((0,14),(34,7))),
    (((0,1),(28,19)),((0,2),(8,29))),
    (((0,4),(35,8)),((0,10),(35,6))),
    (((0,0),(29,18)),((0,4),(15,27))),
    (((0,38),(8,19)),((0,39),(9,18))),
    (((0,1),(29,18)),((0,6),(7,29))),
    (((0,2),(28,19)),((0,3),(23,23))),
    (((0,8),(35,7)),((0,19),(22,21)))]
  have hc : ∀ i : Fin 100, Good (3942+i.val) (c i).1 ∧
      Good (3942+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-3942,by omega⟩
  have he : 3942+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4042 (n : ℕ) (hlo : 4042≤n) (hhi : n<4142) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,5),(36,4)),((0,7),(17,26))),
    (((0,3),(8,29)),((0,7),(33,12))),
    (((0,0),(27,20)),((0,0),(36,5))),
    (((0,8),(36,2)),((0,11),(3,29))),
    (((0,1),(27,20)),((0,1),(36,5))),
    (((0,5),(32,14)),((0,32),(5,23))),
    (((0,3),(28,19)),((0,11),(33,11))),
    (((0,7),(21,24)),((0,8),(31,15))),
    (((0,5),(35,8)),((0,9),(36,0))),
    (((0,2),(27,20)),((0,2),(36,5))),
    (((0,3),(29,18)),((0,8),(19,25))),
    (((0,19),(34,0)),((0,39),(24,0))),
    (((0,4),(8,29)),((0,5),(12,28))),
    (((0,15),(35,0)),((0,22),(15,24))),
    (((0,0),(30,17)),((0,9),(36,1))),
    (((0,16),(32,11)),((0,21),(25,18))),
    (((0,1),(30,17)),((0,22),(0,27))),
    (((0,3),(27,20)),((0,3),(36,5))),
    (((0,14),(21,23)),((0,17),(18,24))),
    (((0,10),(30,16)),((0,15),(35,1))),
    (((0,12),(18,25)),((0,13),(34,8))),
    (((0,0),(34,11)),((0,2),(30,17))),
    (((0,6),(32,14)),((0,12),(2,29))),
    (((0,1),(34,11)),((0,5),(23,23))),
    (((0,8),(33,12)),((0,14),(12,27))),
    (((0,6),(35,8)),((0,8),(34,10))),
    (((0,5),(8,29)),((0,6),(15,27))),
    (((0,8),(36,3)),((0,14),(24,21))),
    (((0,0),(20,25)),((0,0),(26,21))),
    (((0,0),(18,26)),((0,3),(30,17))),
    (((0,1),(20,25)),((0,1),(26,21))),
    (((0,1),(18,26)),((0,5),(28,19))),
    (((0,19),(34,2)),((0,39),(24,2))),
    (((0,9),(31,15)),((0,15),(19,24))),
    (((0,11),(22,23)),((0,15),(35,2))),
    (((0,2),(20,25)),((0,2),(26,21))),
    (((0,2),(18,26)),((0,3),(34,11))),
    (((0,7),(36,4)),((0,10),(36,0))),
    (((0,0),(9,29)),((0,0),(33,13))),
    (((0,13),(23,22)),((0,20),(33,6))),
    (((0,1),(9,29)),((0,1),(33,13))),
    (((0,12),(33,11)),((0,25),(4,26))),
    (((0,5),(27,20)),((0,5),(36,5))),
    (((0,3),(20,25)),((0,3),(26,21))),
    (((0,3),(18,26)),((0,16),(31,13))),
    (((0,2),(9,29)),((0,2),(33,13))),
    (((0,0),(35,9)),((0,7),(15,27))),
    (((0,4),(34,11)),((0,9),(24,22))),
    (((0,0),(13,28)),((0,0),(31,16))),
    (((0,7),(12,28)),((0,9),(17,26))),
    (((0,1),(13,28)),((0,1),(31,16))),
    (((0,9),(34,10)),((0,11),(30,16))),
    (((0,6),(29,18)),((0,24),(29,12))),
    (((0,0),(0,30)),((0,0),(36,6))),
    (((0,4),(20,25)),((0,4),(26,21))),
    (((0,1),(0,30)),((0,1),(36,6))),
    (((0,9),(21,24)),((0,16),(28,17))),
    (((0,0),(1,30)),((0,10),(11,28))),
    (((0,10),(36,2)),((0,12),(29,17))),
    (((0,1),(1,30)),((0,6),(27,20))),
    (((0,0),(22,24)),((0,2),(0,30))),
    (((0,3),(35,9)),((0,5),(34,11))),
    (((0,1),(22,24)),((0,10),(31,15))),
    (((0,0),(16,27)),((0,3),(13,28))),
    (((0,2),(1,30)),((0,4),(9,29))),
    (((0,1),(16,27)),((0,8),(32,14))),
    (((0,9),(7,29)),((0,13),(20,24))),
    (((0,0),(2,30)),((0,2),(22,24))),
    (((0,3),(0,30)),((0,3),(36,6))),
    (((0,0),(25,22)),((0,1),(2,30))),
    (((0,2),(16,27)),((0,20),(34,0))),
    (((0,1),(25,22)),((0,6),(30,17))),
    (((0,3),(1,30)),((0,4),(35,9))),
    (((0,15),(8,28)),((0,15),(32,12))),
    (((0,2),(2,30)),((0,4),(13,28))),
    (((0,3),(22,24)),((0,11),(36,1))),
    (((0,2),(25,22)),((0,10),(24,22))),
    (((0,51),(6,4)),((1,3),(22,24))),
    (((0,3),(16,27)),((0,5),(9,29))),
    (((0,4),(0,30)),((0,4),(36,6))),
    (((0,10),(34,10)),((0,14),(23,22))),
    (((0,14),(9,28)),((0,16),(35,2))),
    (((0,3),(2,30)),((0,10),(36,3))),
    (((0,0),(3,30)),((0,4),(1,30))),
    (((0,3),(25,22)),((0,16),(17,25))),
    (((0,1),(3,30)),((0,6),(20,25))),
    (((0,4),(22,24)),((0,5),(35,9))),
    (((0,11),(6,29)),((0,14),(0,29))),
    (((0,5),(13,28)),((0,5),(31,16))),
    (((0,4),(16,27)),((0,11),(11,28))),
    (((0,2),(3,30)),((0,11),(36,2))),
    (((0,7),(30,17)),((0,8),(28,19))),
    (((0,52),(4,0)),((1,2),(3,30))),
    (((0,4),(2,30)),((0,5),(0,30))),
    (((0,9),(35,8)),((0,11),(31,15))),
    (((0,4),(25,22)),((0,6),(9,29))),
    (((0,0),(10,29)),((0,12),(25,21))),
    (((0,0),(32,15)),((0,5),(1,30))),
    (((0,1),(10,29)),((0,3),(3,30))),
    (((0,1),(32,15)),((0,13),(35,6)))]
  have hc : ∀ i : Fin 100, Good (4042+i.val) (c i).1 ∧
      Good (4042+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4042,by omega⟩
  have he : 4042+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4142 (n : ℕ) (hlo : 4142≤n) (hhi : n<4242) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,5),(22,24)),((0,14),(13,27))),
    (((0,14),(2,29)),((0,21),(33,6))),
    (((0,0),(37,0)),((0,8),(27,20))),
    (((0,2),(10,29)),((0,5),(16,27))),
    (((0,1),(37,0)),((0,2),(32,15))),
    (((0,0),(4,30)),((0,6),(13,28))),
    (((0,7),(18,26)),((0,17),(28,17))),
    (((0,1),(4,30)),((0,5),(2,30))),
    (((0,0),(37,1)),((0,11),(24,22))),
    (((0,2),(37,0)),((0,4),(3,30))),
    (((0,1),(37,1)),((0,6),(0,30))),
    (((0,3),(10,29)),((0,11),(33,12))),
    (((0,2),(4,30)),((0,3),(32,15))),
    (((0,0),(36,7)),((0,48),(6,11))),
    (((0,6),(1,30)),((0,8),(30,17))),
    (((0,1),(36,7)),((0,2),(37,1))),
    (((0,17),(35,1)),((0,41),(23,1))),
    (((0,3),(37,0)),((0,6),(22,24))),
    (((0,16),(24,21)),((0,18),(32,11))),
    (((0,39),(3,20)),((0,44),(8,15))),
    (((0,2),(36,7)),((0,3),(4,30))),
    (((0,8),(34,11)),((0,9),(29,18))),
    (((0,4),(10,29)),((0,12),(6,29))),
    (((0,0),(37,2)),((0,3),(37,1))),
    (((0,6),(2,30)),((0,10),(15,27))),
    (((0,0),(24,23)),((0,1),(37,2))),
    (((0,0),(34,12)),((0,6),(25,22))),
    (((0,1),(24,23)),((0,10),(12,28))),
    (((0,1),(34,12)),((0,3),(36,7))),
    (((0,8),(18,26)),((0,12),(31,15))),
    (((0,0),(14,28)),((0,2),(37,2))),
    (((0,4),(4,30)),((0,15),(0,29))),
    (((0,1),(14,28)),((0,2),(24,23))),
    (((0,0),(5,30)),((0,0),(35,10))),
    (((0,4),(37,1)),((0,7),(1,30))),
    (((0,1),(5,30)),((0,1),(35,10))),
    (((0,5),(10,29)),((0,18),(14,26))),
    (((0,2),(14,28)),((0,5),(32,15))),
    (((0,3),(37,2)),((0,8),(9,29))),
    (((0,4),(36,7)),((0,14),(4,29))),
    (((0,2),(5,30)),((0,2),(35,10))),
    (((0,0),(19,26)),((0,3),(34,12))),
    (((0,5),(37,0)),((0,13),(36,0))),
    (((0,1),(19,26)),((0,12),(24,22))),
    (((0,7),(2,30)),((0,15),(13,27))),
    (((0,3),(14,28)),((0,5),(4,30))),
    (((0,7),(25,22)),((0,8),(35,9))),
    (((0,0),(37,3)),((0,9),(34,11))),
    (((0,2),(19,26)),((0,3),(5,30))),
    (((0,1),(37,3)),((0,4),(37,2))),
    (((0,10),(29,18)),((0,20),(24,20))),
    (((0,4),(24,23)),((0,15),(20,24))),
    (((0,0),(21,25)),((0,4),(34,12))),
    (((0,5),(36,7)),((0,6),(10,29))),
    (((0,1),(21,25)),((0,2),(37,3))),
    (((0,9),(18,26)),((0,11),(35,8))),
    (((0,3),(19,26)),((0,4),(14,28))),
    (((0,8),(1,30)),((0,10),(27,20))),
    (((0,51),(9,2)),((1,3),(19,26))),
    (((0,2),(21,25)),((0,4),(5,30))),
    (((0,0),(11,29)),((0,7),(3,30))),
    (((0,0),(33,14)),((0,15),(3,29))),
    (((0,1),(11,29)),((0,3),(37,3))),
    (((0,0),(17,27)),((0,0),(29,19))),
    (((0,9),(9,29)),((0,9),(33,13))),
    (((0,1),(17,27)),((0,1),(29,19))),
    (((0,5),(34,12)),((0,22),(33,6))),
    (((0,0),(6,30)),((0,2),(11,29))),
    (((0,0),(28,20)),((0,2),(33,14))),
    (((0,1),(6,30)),((0,8),(25,22))),
    (((0,1),(28,20)),((0,2),(17,27))),
    (((0,16),(23,22)),((0,17),(15,26))),
    (((0,9),(35,9)),((0,16),(9,28))),
    (((0,0),(30,18)),((0,4),(37,3))),
    (((0,2),(6,30)),((0,7),(32,15))),
    (((0,1),(30,18)),((0,2),(28,20))),
    (((0,3),(33,14)),((0,10),(34,11))),
    (((0,18),(7,28)),((0,21),(34,3))),
    (((0,3),(17,27)),((0,3),(29,19))),
    (((0,7),(37,0)),((0,9),(0,30))),
    (((0,0),(37,4)),((0,2),(30,18))),
    (((0,5),(19,26)),((0,13),(24,22))),
    (((0,0),(36,8)),((0,1),(37,4))),
    (((0,3),(28,20)),((0,6),(34,12))),
    (((0,1),(36,8)),((0,10),(18,26))),
    (((0,7),(37,1)),((0,13),(34,10))),
    (((0,4),(11,29)),((0,9),(22,24))),
    (((0,2),(37,4)),((0,4),(33,14))),
    (((0,0),(27,21)),((0,3),(30,18))),
    (((0,2),(36,8)),((0,4),(17,27))),
    (((0,1),(27,21)),((0,6),(5,30))),
    (((0,12),(15,27)),((0,16),(13,27))),
    (((0,5),(21,25)),((0,15),(22,23))),
    (((0,4),(6,30)),((0,9),(2,30))),
    (((0,4),(28,20)),((0,12),(12,28))),
    (((0,2),(27,21)),((0,3),(37,4))),
    (((0,0),(23,24)),((0,8),(10,29))),
    (((0,3),(36,8)),((0,8),(32,15))),
    (((0,0),(31,17)),((0,1),(23,24))),
    (((0,4),(30,18)),((0,20),(10,27)))]
  have hc : ∀ i : Fin 100, Good (4142+i.val) (c i).1 ∧
      Good (4142+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4142,by omega⟩
  have he : 4142+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4242 (n : ℕ) (hlo : 4242≤n) (hhi : n<4342) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,1),(31,17)),((0,5),(11,29))),
    (((0,5),(33,14)),((0,10),(35,9))),
    (((0,7),(24,23)),((0,8),(37,0))),
    (((0,2),(23,24)),((0,3),(27,21))),
    (((0,6),(37,3)),((0,14),(36,2))),
    (((0,2),(31,17)),((0,8),(4,30))),
    (((0,4),(37,4)),((0,48),(15,4))),
    (((0,0),(7,30)),((0,5),(6,30))),
    (((0,4),(36,8)),((0,5),(28,20))),
    (((0,1),(7,30)),((0,6),(21,25))),
    (((0,7),(5,30)),((0,7),(35,10))),
    (((0,3),(23,24)),((0,14),(19,25))),
    (((0,10),(1,30)),((0,18),(21,23))),
    (((0,3),(31,17)),((0,5),(30,18))),
    (((0,2),(7,30)),((0,4),(27,21))),
    (((0,10),(22,24)),((0,11),(20,25))),
    (((0,11),(18,26)),((0,19),(26,19))),
    (((0,6),(11,29)),((0,12),(29,18))),
    (((0,0),(15,28)),((0,6),(33,14))),
    (((0,15),(25,21)),((0,19),(35,0))),
    (((0,1),(15,28)),((0,5),(37,4))),
    (((0,17),(23,22)),((0,18),(24,21))),
    (((0,0),(37,5)),((0,3),(7,30))),
    (((0,0),(26,22)),((0,8),(37,2))),
    (((0,1),(37,5)),((0,4),(31,17))),
    (((0,1),(26,22)),((0,2),(15,28))),
    (((0,8),(34,12)),((0,14),(34,10))),
    (((0,15),(36,0)),((0,43),(22,0))),
    (((0,5),(27,21)),((0,9),(37,0))),
    (((0,0),(35,11)),((0,2),(37,5))),
    (((0,0),(12,29)),((0,2),(26,22))),
    (((0,1),(35,11)),((0,9),(4,30))),
    (((0,1),(12,29)),((0,13),(12,28))),
    (((0,3),(15,28)),((0,4),(7,30))),
    (((0,9),(37,1)),((0,16),(26,20))),
    (((0,11),(13,28)),((0,11),(31,16))),
    (((0,2),(35,11)),((0,5),(23,24))),
    (((0,2),(12,29)),((0,3),(37,5))),
    (((0,0),(32,16)),((0,3),(26,22))),
    (((0,6),(36,8)),((0,9),(36,7))),
    (((0,0),(34,13)),((0,1),(32,16))),
    (((0,8),(19,26)),((0,14),(7,29))),
    (((0,1),(34,13)),((0,17),(2,29))),
    (((0,12),(34,11)),((0,13),(23,23))),
    (((0,3),(35,11)),((0,4),(15,28))),
    (((0,2),(32,16)),((0,3),(12,29))),
    (((0,13),(8,29)),((0,20),(33,9))),
    (((0,2),(34,13)),((0,5),(7,30))),
    (((0,4),(37,5)),((0,15),(36,2))),
    (((0,4),(26,22)),((0,9),(37,2))),
    (((0,7),(30,18)),((0,11),(16,27))),
    (((0,9),(24,23)),((0,10),(10,29))),
    (((0,8),(21,25)),((0,9),(34,12))),
    (((0,0),(8,30)),((0,3),(32,16))),
    (((0,11),(2,30)),((0,24),(33,5))),
    (((0,1),(8,30)),((0,3),(34,13))),
    (((0,4),(12,29)),((0,9),(14,28))),
    (((0,7),(37,4)),((0,10),(37,0))),
    (((0,5),(15,28)),((0,16),(5,29))),
    (((0,0),(20,26)),((0,7),(36,8))),
    (((0,0),(36,9)),((0,2),(8,30))),
    (((0,1),(20,26)),((0,8),(33,14))),
    (((0,1),(36,9)),((0,5),(37,5))),
    (((0,5),(26,22)),((0,8),(17,27))),
    (((0,4),(32,16)),((0,6),(7,30))),
    (((0,7),(27,21)),((0,17),(16,26))),
    (((0,2),(20,26)),((0,4),(34,13))),
    (((0,2),(36,9)),((0,8),(6,30))),
    (((0,3),(8,30)),((0,8),(28,20))),
    (((0,0),(18,27)),((0,5),(35,11))),
    (((0,5),(12,29)),((0,11),(3,30))),
    (((0,1),(18,27)),((0,23),(34,1))),
    (((0,15),(36,3)),((0,43),(22,3))),
    (((0,0),(25,23)),((0,0),(37,6))),
    (((0,3),(20,26)),((0,13),(30,17))),
    (((0,1),(25,23)),((0,1),(37,6))),
    (((0,2),(18,27)),((0,26),(30,11))),
    (((0,19),(24,21)),((0,22),(24,20))),
    (((0,5),(32,16)),((0,9),(21,25))),
    (((0,4),(8,30)),((0,6),(37,5))),
    (((0,2),(25,23)),((0,2),(37,6))),
    (((0,10),(34,12)),((0,13),(34,11))),
    (((0,0),(22,25)),((0,8),(36,8))),
    (((0,11),(10,29)),((0,18),(35,5))),
    (((0,1),(22,25)),((0,3),(18,27))),
    (((0,4),(20,26)),((0,10),(14,28))),
    (((0,4),(36,9)),((0,6),(35,11))),
    (((0,6),(12,29)),((0,9),(33,14))),
    (((0,3),(25,23)),((0,3),(37,6))),
    (((0,2),(22,25)),((0,9),(17,27))),
    (((0,43),(4,18)),((0,44),(5,17))),
    (((0,12),(25,22)),((0,16),(35,7))),
    (((0,11),(4,30)),((0,14),(28,19))),
    (((0,0),(33,15)),((0,5),(8,30))),
    (((0,9),(28,20)),((0,16),(11,28))),
    (((0,1),(33,15)),((0,4),(18,27))),
    (((0,8),(23,24)),((0,10),(19,26))),
    (((0,3),(22,25)),((0,6),(34,13))),
    (((0,8),(31,17)),((0,13),(9,29))),
    (((0,4),(25,23)),((0,4),(37,6)))]
  have hc : ∀ i : Fin 100, Good (4242+i.val) (c i).1 ∧
      Good (4242+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4242,by omega⟩
  have he : 4242+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4342 (n : ℕ) (hlo : 4342≤n) (hhi : n<4442) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,2),(33,15)),((0,5),(36,9))),
    (((0,18),(20,24)),((0,20),(34,7))),
    (((0,10),(37,3)),((0,16),(19,25))),
    (((0,14),(27,20)),((0,14),(36,5))),
    (((0,25),(30,12)),((0,37),(12,20))),
    (((0,0),(9,30)),((0,12),(3,30))),
    (((0,0),(13,29)),((0,7),(35,11))),
    (((0,1),(9,30)),((0,7),(12,29))),
    (((0,1),(13,29)),((0,3),(33,15))),
    (((0,5),(18,27)),((0,24),(7,27))),
    (((0,6),(8,30)),((0,11),(37,2))),
    (((0,18),(3,29)),((0,19),(34,8))),
    (((0,0),(16,28)),((0,2),(9,30))),
    (((0,2),(13,29)),((0,5),(25,23))),
    (((0,1),(16,28)),((0,9),(27,21))),
    (((0,7),(32,16)),((0,10),(11,29))),
    (((0,6),(20,26)),((0,10),(33,14))),
    (((0,6),(36,9)),((0,7),(34,13))),
    (((0,8),(15,28)),((0,10),(17,27))),
    (((0,2),(16,28)),((0,4),(33,15))),
    (((0,3),(9,30)),((0,11),(5,30))),
    (((0,3),(13,29)),((0,22),(23,21))),
    (((0,5),(22,25)),((0,8),(37,5))),
    (((0,8),(26,22)),((0,10),(28,20))),
    (((0,9),(31,17)),((0,12),(37,0))),
    (((0,21),(11,27)),((0,30),(11,24))),
    (((0,6),(18,27)),((0,19),(31,14))),
    (((0,3),(16,28)),((0,12),(4,30))),
    (((0,0),(38,0)),((0,10),(30,18))),
    (((0,0),(0,31)),((0,8),(35,11))),
    (((0,1),(38,0)),((0,6),(25,23))),
    (((0,1),(0,31)),((0,4),(9,30))),
    (((0,4),(13,29)),((0,16),(7,29))),
    (((0,0),(1,31)),((0,0),(37,7))),
    (((0,0),(35,12)),((0,0),(38,1))),
    (((0,1),(1,31)),((0,1),(37,7))),
    (((0,1),(35,12)),((0,1),(38,1))),
    (((0,7),(36,9)),((0,10),(36,8))),
    (((0,0),(24,24)),((0,4),(16,28))),
    (((0,6),(22,25)),((0,11),(21,25))),
    (((0,0),(29,20)),((0,1),(24,24))),
    (((0,0),(30,19)),((0,2),(35,12))),
    (((0,1),(29,20)),((0,17),(6,29))),
    (((0,0),(2,31)),((0,1),(30,19))),
    (((0,3),(0,31)),((0,9),(15,28))),
    (((0,1),(2,31)),((0,2),(24,24))),
    (((0,5),(13,29)),((0,7),(18,27))),
    (((0,0),(36,10)),((0,2),(29,20))),
    (((0,2),(30,19)),((0,3),(1,31))),
    (((0,0),(38,2)),((0,1),(36,10))),
    (((0,2),(2,31)),((0,6),(33,15))),
    (((0,1),(38,2)),((0,10),(23,24))),
    (((0,5),(16,28)),((0,12),(14,28))),
    (((0,3),(24,24)),((0,8),(8,30))),
    (((0,0),(28,21)),((0,2),(36,10))),
    (((0,3),(29,20)),((0,4),(0,31))),
    (((0,1),(28,21)),((0,2),(38,2))),
    (((0,0),(31,18)),((0,13),(32,15))),
    (((0,3),(2,31)),((0,14),(1,30))),
    (((0,0),(3,31)),((0,1),(31,18))),
    (((0,4),(35,12)),((0,4),(38,1))),
    (((0,1),(3,31)),((0,2),(28,21))),
    (((0,3),(36,10)),((0,6),(9,30))),
    (((0,0),(10,30)),((0,0),(34,14))),
    (((0,2),(31,18)),((0,3),(38,2))),
    (((0,1),(10,30)),((0,1),(34,14))),
    (((0,2),(3,31)),((0,4),(29,20))),
    (((0,4),(30,19)),((0,11),(37,4))),
    (((0,5),(38,0)),((0,13),(37,1))),
    (((0,3),(28,21)),((0,4),(2,31))),
    (((0,2),(10,30)),((0,2),(34,14))),
    (((0,27),(33,1)),((0,35),(29,1))),
    (((0,3),(31,18)),((0,17),(21,24))),
    (((0,0),(38,3)),((0,4),(36,10))),
    (((0,3),(3,31)),((0,5),(35,12))),
    (((0,1),(38,3)),((0,4),(38,2))),
    (((0,18),(14,27)),((0,19),(27,19))),
    (((0,10),(37,5)),((0,18),(36,0))),
    (((0,3),(10,30)),((0,3),(34,14))),
    (((0,9),(8,30)),((0,22),(6,28))),
    (((0,2),(38,3)),((0,4),(28,21))),
    (((0,0),(4,31)),((0,0),(19,27))),
    (((0,7),(9,30)),((0,8),(22,25))),
    (((0,0),(21,26)),((0,0),(27,22))),
    (((0,10),(35,11)),((0,14),(3,30))),
    (((0,1),(21,26)),((0,1),(27,22))),
    (((0,6),(0,31)),((0,9),(36,9))),
    (((0,5),(36,10)),((0,16),(29,18))),
    (((0,0),(14,29)),((0,0),(32,17))),
    (((0,4),(10,30)),((0,4),(34,14))),
    (((0,1),(14,29)),((0,1),(32,17))),
    (((0,6),(35,12)),((0,6),(38,1))),
    (((0,42),(6,19)),((0,43),(7,18))),
    (((0,8),(33,15)),((0,10),(32,16))),
    (((0,5),(28,21)),((0,11),(7,30))),
    (((0,2),(14,29)),((0,2),(32,17))),
    (((0,3),(4,31)),((0,3),(19,27))),
    (((0,5),(31,18)),((0,6),(29,20))),
    (((0,3),(21,26)),((0,3),(27,22))),
    (((0,4),(38,3)),((0,5),(3,31)))]
  have hc : ∀ i : Fin 100, Good (4342+i.val) (c i).1 ∧
      Good (4342+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4342,by omega⟩
  have he : 4342+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4442 (n : ℕ) (hlo : 4442≤n) (hhi : n<4542) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,6),(2,31)),((0,20),(1,29))),
    (((0,13),(19,26)),((0,21),(15,26))),
    (((0,0),(37,8)),((0,12),(37,4))),
    (((0,3),(14,29)),((0,3),(32,17))),
    (((0,1),(37,8)),((0,6),(36,10))),
    (((0,7),(38,0)),((0,8),(9,30))),
    (((0,0),(38,4)),((0,6),(38,2))),
    (((0,4),(4,31)),((0,4),(19,27))),
    (((0,1),(38,4)),((0,9),(22,25))),
    (((0,0),(5,31)),((0,2),(37,8))),
    (((0,7),(1,31)),((0,7),(37,7))),
    (((0,1),(5,31)),((0,6),(28,21))),
    (((0,0),(17,28)),((0,8),(16,28))),
    (((0,2),(38,4)),((0,5),(38,3))),
    (((0,1),(17,28)),((0,4),(14,29))),
    (((0,7),(24,24)),((0,10),(36,9))),
    (((0,2),(5,31)),((0,6),(3,31))),
    (((0,3),(37,8)),((0,7),(29,20))),
    (((0,0),(23,25)),((0,7),(30,19))),
    (((0,2),(17,28)),((0,9),(33,15))),
    (((0,1),(23,25)),((0,6),(10,30))),
    (((0,3),(38,4)),((0,5),(4,31))),
    (((0,18),(36,3)),((0,42),(24,3))),
    (((0,5),(21,26)),((0,5),(27,22))),
    (((0,3),(5,31)),((0,7),(36,10))),
    (((0,2),(23,25)),((0,11),(32,16))),
    (((0,7),(38,2)),((0,14),(24,23))),
    (((0,0),(11,30)),((0,0),(26,23))),
    (((0,4),(37,8)),((0,5),(14,29))),
    (((0,1),(11,30)),((0,1),(26,23))),
    (((0,6),(38,3)),((0,16),(9,29))),
    (((0,7),(28,21)),((0,9),(9,30))),
    (((0,4),(38,4)),((0,9),(13,29))),
    (((0,3),(23,25)),((0,8),(1,31))),
    (((0,0),(33,16)),((0,2),(11,30))),
    (((0,4),(5,31)),((0,18),(7,29))),
    (((0,1),(33,16)),((0,7),(3,31))),
    (((0,10),(22,25)),((0,17),(29,18))),
    (((0,4),(17,28)),((0,6),(4,31))),
    (((0,19),(36,1)),((0,25),(33,7))),
    (((0,6),(21,26)),((0,6),(27,22))),
    (((0,2),(33,16)),((0,8),(30,19))),
    (((0,3),(11,30)),((0,3),(26,23))),
    (((0,0),(6,31)),((0,0),(36,11))),
    (((0,4),(23,25)),((0,12),(37,5))),
    (((0,1),(6,31)),((0,1),(36,11))),
    (((0,5),(38,4)),((0,11),(20,26))),
    (((0,8),(36,10)),((0,11),(36,9))),
    (((0,0),(35,13)),((0,0),(38,5))),
    (((0,3),(33,16)),((0,5),(5,31))),
    (((0,1),(35,13)),((0,1),(38,5))),
    (((0,12),(35,11)),((0,19),(6,29))),
    (((0,5),(17,28)),((0,12),(12,29))),
    (((0,4),(11,30)),((0,4),(26,23))),
    (((0,8),(28,21)),((0,9),(38,0))),
    (((0,2),(35,13)),((0,2),(38,5))),
    (((0,11),(18,27)),((0,13),(23,24))),
    (((0,8),(31,18)),((0,20),(22,23))),
    (((0,3),(6,31)),((0,3),(36,11))),
    (((0,6),(37,8)),((0,8),(3,31))),
    (((0,4),(33,16)),((0,7),(21,26))),
    (((0,10),(13,29)),((0,14),(11,29))),
    (((0,12),(34,13)),((0,14),(33,14))),
    (((0,3),(35,13)),((0,3),(38,5))),
    (((0,9),(24,24)),((0,14),(17,27))),
    (((0,7),(14,29)),((0,7),(32,17))),
    (((0,6),(5,31)),((0,9),(29,20))),
    (((0,5),(11,30)),((0,5),(26,23))),
    (((0,14),(6,30)),((0,15),(37,2))),
    (((0,4),(6,31)),((0,4),(36,11))),
    (((0,15),(24,23)),((0,17),(20,25))),
    (((0,15),(34,12)),((0,17),(18,26))),
    (((0,19),(24,22)),((0,21),(2,29))),
    (((0,8),(38,3)),((0,9),(36,10))),
    (((0,4),(35,13)),((0,4),(38,5))),
    (((0,6),(23,25)),((0,9),(38,2))),
    (((0,0),(15,29)),((0,19),(34,10))),
    (((0,25),(32,10)),((0,27),(16,24))),
    (((0,1),(15,29)),((0,13),(15,28))),
    (((0,7),(37,8)),((0,23),(35,1))),
    (((0,0),(37,9)),((0,9),(28,21))),
    (((0,8),(4,31)),((0,8),(19,27))),
    (((0,1),(37,9)),((0,12),(36,9))),
    (((0,0),(7,31)),((0,2),(15,29))),
    (((0,6),(11,30)),((0,6),(26,23))),
    (((0,1),(7,31)),((0,9),(3,31))),
    (((0,0),(25,24)),((0,7),(5,31))),
    (((0,2),(37,9)),((0,23),(7,28))),
    (((0,1),(25,24)),((0,5),(35,13))),
    (((0,7),(17,28)),((0,9),(10,30))),
    (((0,2),(7,31)),((0,13),(12,29))),
    (((0,3),(15,29)),((0,6),(33,16))),
    (((0,11),(9,30)),((0,15),(37,3))),
    (((0,2),(25,24)),((0,10),(24,24))),
    (((0,16),(37,0)),((0,23),(35,2))),
    (((0,0),(34,15)),((0,3),(37,9))),
    (((0,10),(30,19)),((0,23),(34,7))),
    (((0,0),(12,30)),((0,1),(34,15))),
    (((0,3),(7,31)),((0,10),(2,31))),
    (((0,0),(20,27)),((0,0),(38,6)))]
  have hc : ∀ i : Fin 100, Good (4442+i.val) (c i).1 ∧
      Good (4442+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4442,by omega⟩
  have he : 4442+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4542 (n : ℕ) (hlo : 4542≤n) (hhi : n<4642) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,6),(6,31)),((0,6),(36,11))),
    (((0,1),(20,27)),((0,1),(38,6))),
    (((0,2),(34,15)),((0,4),(15,29))),
    (((0,45),(0,18)),((0,48),(3,15))),
    (((0,2),(12,30)),((0,7),(11,30))),
    (((0,6),(35,13)),((0,6),(38,5))),
    (((0,2),(20,27)),((0,2),(38,6))),
    (((0,9),(4,31)),((0,9),(19,27))),
    (((0,14),(7,30)),((0,15),(17,27))),
    (((0,4),(7,31)),((0,8),(5,31))),
    (((0,3),(34,15)),((0,20),(6,29))),
    (((0,7),(33,16)),((0,17),(25,22))),
    (((0,3),(12,30)),((0,4),(25,24))),
    (((0,0),(22,26)),((0,13),(8,30))),
    (((0,3),(20,27)),((0,3),(38,6))),
    (((0,1),(22,26)),((0,11),(38,0))),
    (((0,5),(15,29)),((0,11),(0,31))),
    (((0,16),(24,23)),((0,20),(31,15))),
    (((0,0),(18,28)),((0,0),(30,20))),
    (((0,13),(20,26)),((0,14),(15,28))),
    (((0,1),(18,28)),((0,1),(30,20))),
    (((0,4),(34,15)),((0,11),(35,12))),
    (((0,16),(14,28)),((0,23),(21,23))),
    (((0,4),(12,30)),((0,5),(7,31))),
    (((0,14),(26,22)),((0,18),(18,26))),
    (((0,0),(31,19)),((0,2),(18,28))),
    (((0,0),(29,21)),((0,5),(25,24))),
    (((0,1),(31,19)),((0,8),(11,30))),
    (((0,1),(29,21)),((0,3),(22,26))),
    (((0,0),(8,31)),((0,13),(18,27))),
    (((0,11),(2,31)),((0,14),(35,11))),
    (((0,1),(8,31)),((0,14),(12,29))),
    (((0,2),(31,19)),((0,9),(38,4))),
    (((0,2),(29,21)),((0,3),(18,28))),
    (((0,8),(33,16)),((0,11),(36,10))),
    (((0,5),(34,15)),((0,9),(5,31))),
    (((0,2),(8,31)),((0,10),(4,31))),
    (((0,5),(12,30)),((0,6),(37,9))),
    (((0,9),(17,28)),((0,10),(21,26))),
    (((0,4),(22,26)),((0,5),(20,27))),
    (((0,3),(31,19)),((0,6),(7,31))),
    (((0,3),(29,21)),((0,11),(28,21))),
    (((0,13),(22,25)),((0,19),(28,19))),
    (((0,6),(25,24)),((0,8),(6,31))),
    (((0,3),(8,31)),((0,4),(18,28))),
    (((1,6),(25,24)),((1,8),(6,31))),
    (((0,11),(3,31)),((0,19),(29,18))),
    (((0,0),(32,18)),((0,17),(4,30))),
    (((0,0),(36,12)),((0,8),(35,13))),
    (((0,0),(28,22)),((0,1),(32,18))),
    (((0,1),(36,12)),((0,11),(10,30))),
    (((0,1),(28,22)),((0,4),(31,19))),
    (((0,4),(29,21)),((0,6),(34,15))),
    (((0,5),(22,26)),((0,7),(15,29))),
    (((0,2),(32,18)),((0,6),(12,30))),
    (((0,2),(36,12)),((0,4),(8,31))),
    (((0,2),(28,22)),((0,6),(20,27))),
    (((0,7),(37,9)),((0,10),(37,8))),
    (((0,5),(18,28)),((0,5),(30,20))),
    (((0,0),(38,7)),((0,16),(6,30))),
    (((0,0),(24,25)),((0,0),(39,0))),
    (((0,1),(38,7)),((0,10),(38,4))),
    (((0,1),(24,25)),((0,1),(39,0))),
    (((0,3),(36,12)),((0,7),(25,24))),
    (((0,3),(28,22)),((0,10),(5,31))),
    (((0,5),(31,19)),((0,12),(2,31))),
    (((0,0),(39,1)),((0,2),(38,7))),
    (((0,0),(37,10)),((0,2),(24,25))),
    (((0,1),(39,1)),((0,11),(4,31))),
    (((0,1),(37,10)),((0,5),(8,31))),
    (((0,0),(16,29)),((0,6),(22,26))),
    (((0,0),(35,14)),((0,12),(38,2))),
    (((0,1),(16,29)),((0,7),(34,15))),
    (((0,0),(13,30)),((0,1),(35,14))),
    (((0,2),(37,10)),((0,3),(38,7))),
    (((0,1),(13,30)),((0,3),(24,25))),
    (((0,7),(20,27)),((0,7),(38,6))),
    (((0,2),(16,29)),((0,27),(17,24))),
    (((0,2),(35,14)),((0,18),(3,30))),
    (((0,12),(31,18)),((0,19),(20,25))),
    (((0,2),(13,30)),((0,8),(37,9))),
    (((0,0),(9,31)),((0,0),(39,2))),
    (((0,3),(37,10)),((0,6),(31,19))),
    (((0,1),(9,31)),((0,1),(39,2))),
    (((0,0),(33,17)),((0,22),(22,23))),
    (((0,3),(16,29)),((0,4),(38,7))),
    (((0,1),(33,17)),((0,3),(35,14))),
    (((0,0),(27,23)),((0,5),(32,18))),
    (((0,2),(9,31)),((0,2),(39,2))),
    (((0,1),(27,23)),((0,5),(28,22))),
    (((0,7),(22,26)),((0,16),(31,17))),
    (((0,2),(33,17)),((0,18),(10,29))),
    (((0,4),(39,1)),((0,18),(32,15))),
    (((0,4),(37,10)),((0,11),(38,4))),
    (((0,2),(27,23)),((0,13),(35,12))),
    (((0,7),(18,28)),((0,7),(30,20))),
    (((0,3),(9,31)),((0,3),(39,2))),
    (((0,4),(35,14)),((0,8),(12,30))),
    (((0,10),(6,31)),((0,10),(36,11))),
    (((0,3),(33,17)),((0,4),(13,30)))]
  have hc : ∀ i : Fin 100, Good (4542+i.val) (c i).1 ∧
      Good (4542+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4542,by omega⟩
  have he : 4542+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4642 (n : ℕ) (hlo : 4642≤n) (hhi : n<4742) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,5),(24,25)),((0,5),(39,0))),
    (((0,13),(30,19)),((0,20),(28,19))),
    (((0,3),(27,23)),((0,7),(31,19))),
    (((0,7),(29,21)),((0,10),(35,13))),
    (((0,6),(32,18)),((0,15),(20,26))),
    (((0,0),(39,3)),((0,6),(36,12))),
    (((0,5),(39,1)),((0,6),(28,22))),
    (((0,1),(39,3)),((0,4),(9,31))),
    (((0,18),(36,7)),((0,19),(1,30))),
    (((0,9),(7,31)),((0,13),(38,2))),
    (((0,4),(33,17)),((0,5),(16,29))),
    (((0,5),(35,14)),((0,19),(22,24))),
    (((0,2),(39,3)),((0,9),(25,24))),
    (((0,4),(27,23)),((0,5),(13,30))),
    (((0,0),(0,32)),((0,11),(11,30))),
    (((0,16),(26,22)),((0,17),(30,18))),
    (((0,1),(0,32)),((0,6),(38,7))),
    (((0,6),(24,25)),((0,6),(39,0))),
    (((0,0),(1,32)),((0,8),(18,28))),
    (((0,13),(3,31)),((0,22),(36,0))),
    (((0,1),(1,32)),((0,3),(39,3))),
    (((0,2),(0,32)),((0,5),(9,31))),
    (((0,16),(12,29)),((0,17),(37,4))),
    (((0,0),(21,27)),((0,6),(39,1))),
    (((0,5),(33,17)),((0,6),(37,10))),
    (((0,1),(21,27)),((0,2),(1,32))),
    (((0,7),(28,22)),((0,8),(29,21))),
    (((0,5),(27,23)),((0,6),(16,29))),
    (((0,0),(2,32)),((0,0),(38,8))),
    (((0,3),(0,32)),((0,8),(8,31))),
    (((0,0),(19,28)),((0,1),(2,32))),
    (((0,4),(39,3)),((0,10),(15,29))),
    (((0,1),(19,28)),((0,16),(34,13))),
    (((0,3),(1,32)),((0,13),(38,3))),
    (((0,12),(17,28)),((0,14),(1,31))),
    (((0,2),(2,32)),((0,2),(38,8))),
    (((0,0),(34,16)),((0,7),(38,7))),
    (((0,2),(19,28)),((0,7),(24,25))),
    (((0,0),(39,4)),((0,1),(34,16))),
    (((0,0),(10,31)),((0,9),(22,26))),
    (((0,0),(26,24)),((0,1),(39,4))),
    (((0,1),(10,31)),((0,6),(33,17))),
    (((0,1),(26,24)),((0,14),(30,19))),
    (((0,2),(34,16)),((0,3),(2,32))),
    (((0,0),(3,32)),((0,4),(1,32))),
    (((0,2),(39,4)),((0,3),(19,28))),
    (((0,1),(3,32)),((0,2),(10,31))),
    (((0,2),(26,24)),((0,7),(16,29))),
    (((0,7),(35,14)),((0,8),(36,12))),
    (((0,0),(23,26)),((0,4),(21,27))),
    (((0,7),(13,30)),((0,10),(34,15))),
    (((0,1),(23,26)),((0,2),(3,32))),
    (((0,9),(29,21)),((0,10),(12,30))),
    (((0,3),(39,4)),((0,19),(37,0))),
    (((0,3),(10,31)),((0,4),(2,32))),
    (((0,0),(14,30)),((0,3),(26,24))),
    (((0,2),(23,26)),((0,4),(19,28))),
    (((0,1),(14,30)),((0,15),(16,28))),
    (((0,5),(1,32)),((0,7),(9,31))),
    (((0,3),(3,32)),((0,8),(38,7))),
    (((0,8),(24,25)),((0,8),(39,0))),
    (((0,7),(33,17)),((0,16),(18,27))),
    (((0,0),(36,13)),((0,2),(14,30))),
    (((0,0),(37,11)),((0,5),(21,27))),
    (((0,1),(36,13)),((0,3),(23,26))),
    (((0,1),(37,11)),((0,4),(10,31))),
    (((0,0),(4,32)),((0,4),(26,24))),
    (((0,8),(37,10)),((0,11),(37,9))),
    (((0,1),(4,32)),((0,5),(2,32))),
    (((0,2),(36,13)),((0,13),(5,31))),
    (((0,0),(17,29)),((0,2),(37,11))),
    (((0,6),(0,32)),((0,8),(35,14))),
    (((0,1),(17,29)),((0,13),(17,28))),
    (((0,2),(4,32)),((0,8),(13,30))),
    (((0,9),(36,12)),((0,14),(38,3))),
    (((0,4),(23,26)),((0,6),(1,32))),
    (((0,5),(34,16)),((0,19),(24,23))),
    (((0,2),(17,29)),((0,3),(36,13))),
    (((0,3),(37,11)),((0,5),(39,4))),
    (((0,5),(10,31)),((0,15),(35,12))),
    (((0,0),(39,5)),((0,5),(26,24))),
    (((0,3),(4,32)),((0,4),(14,30))),
    (((0,1),(39,5)),((0,7),(39,3))),
    (((0,15),(24,24)),((0,18),(27,21))),
    (((0,5),(3,32)),((0,8),(33,17))),
    (((0,3),(17,29)),((0,6),(2,32))),
    (((0,9),(24,25)),((0,9),(39,0))),
    (((0,2),(39,5)),((0,6),(19,28))),
    (((0,4),(36,13)),((0,15),(2,31))),
    (((0,4),(37,11)),((0,5),(23,26))),
    (((0,31),(32,6)),((0,51),(16,2))),
    (((0,7),(0,32)),((0,18),(23,24))),
    (((0,4),(4,32)),((0,9),(39,1))),
    (((0,6),(34,16)),((0,9),(37,10))),
    (((0,0),(5,32)),((0,13),(33,16))),
    (((0,3),(39,5)),((0,5),(14,30))),
    (((0,1),(5,32)),((0,4),(17,29))),
    (((0,6),(26,24)),((0,9),(35,14))),
    (((0,12),(15,29)),((0,16),(13,29))),
    (((0,9),(13,30)),((0,15),(28,21)))]
  have hc : ∀ i : Fin 100, Good (4642+i.val) (c i).1 ∧
      Good (4642+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4642,by omega⟩
  have he : 4642+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4742 (n : ℕ) (hlo : 4742≤n) (hhi : n<4842) : 2≤a n := by
  let c : Fin 100 → Tuple4×Tuple4 := ![
    (((0,7),(21,27)),((0,11),(22,26))),
    (((0,2),(5,32)),((0,6),(3,32))),
    (((0,0),(31,20)),((0,5),(36,13))),
    (((0,0),(11,31)),((0,0),(35,15))),
    (((0,0),(30,21)),((0,1),(31,20))),
    (((0,1),(11,31)),((0,1),(35,15))),
    (((0,0),(38,9)),((0,1),(30,21))),
    (((0,7),(19,28)),((0,9),(9,31))),
    (((0,0),(25,25)),((0,1),(38,9))),
    (((0,2),(31,20)),((0,3),(5,32))),
    (((0,1),(25,25)),((0,2),(11,31))),
    (((0,2),(30,21)),((0,17),(18,27))),
    (((0,6),(14,30)),((0,11),(31,19))),
    (((0,2),(38,9)),((0,7),(34,16))),
    (((0,8),(0,32)),((0,10),(38,7))),
    (((0,0),(32,19)),((0,2),(25,25))),
    (((0,7),(10,31)),((0,11),(8,31))),
    (((0,1),(32,19)),((0,3),(31,20))),
    (((0,3),(11,31)),((0,3),(35,15))),
    (((0,3),(30,21)),((0,6),(36,13))),
    (((0,4),(5,32)),((0,5),(39,5))),
    (((0,0),(29,22)),((0,3),(38,9))),
    (((0,2),(32,19)),((0,10),(37,10))),
    (((0,1),(29,22)),((0,3),(25,25))),
    (((0,17),(22,25)),((0,18),(35,11))),
    (((0,10),(16,29)),((0,16),(1,31))),
    (((0,7),(23,26)),((0,10),(35,14))),
    (((0,6),(17,29)),((0,30),(32,8))),
    (((0,0),(6,32)),((0,2),(29,22))),
    (((0,4),(11,31)),((0,4),(35,15))),
    (((0,1),(6,32)),((0,3),(32,19))),
    (((0,0),(39,6)),((0,9),(39,3))),
    (((0,4),(38,9)),((0,7),(14,30))),
    (((0,1),(39,6)),((0,15),(14,29))),
    (((0,4),(25,25)),((0,5),(5,32))),
    (((0,2),(6,32)),((0,11),(36,12))),
    (((0,3),(29,22)),((0,8),(34,16))),
    (((0,6),(39,5)),((0,43),(7,20))),
    (((0,2),(39,6)),((0,8),(39,4))),
    (((0,7),(36,13)),((0,8),(10,31))),
    (((0,7),(37,11)),((0,8),(26,24))),
    (((0,4),(32,19)),((0,16),(38,2))),
    (((0,5),(31,20)),((0,10),(27,23))),
    (((0,0),(15,30)),((0,0),(33,18))),
    (((0,5),(30,21)),((0,8),(3,32))),
    (((0,1),(15,30)),((0,1),(33,18))),
    (((0,3),(39,6)),((0,5),(38,9))),
    (((0,4),(29,22)),((0,7),(17,29))),
    (((0,0),(20,28)),((0,5),(25,25))),
    (((0,8),(23,26)),((0,9),(21,27))),
    (((0,1),(20,28)),((0,2),(15,30))),
    (((0,6),(5,32)),((0,12),(8,31))),
    (((1,1),(20,28)),((1,2),(15,30))),
    (((0,0),(22,27)),((0,0),(28,23))),
    (((0,4),(6,32)),((0,9),(2,32))),
    (((0,1),(22,27)),((0,1),(28,23))),
    (((0,9),(19,28)),((0,25),(20,24))),
    (((0,4),(39,6)),((0,7),(39,5))),
    (((0,3),(15,30)),((0,3),(33,18))),
    (((0,6),(31,20)),((0,13),(20,27))),
    (((0,2),(22,27)),((0,2),(28,23))),
    (((0,5),(29,22)),((0,6),(30,21))),
    (((0,8),(36,13)),((0,9),(34,16))),
    (((0,3),(20,28)),((0,6),(38,9))),
    (((0,9),(39,4)),((0,18),(18,27))),
    (((0,6),(25,25)),((0,9),(10,31))),
    (((0,8),(4,32)),((0,9),(26,24))),
    (((0,54),(3,9)),((1,6),(25,25))),
    (((0,0),(7,32)),((0,0),(37,12))),
    (((0,4),(15,30)),((0,4),(33,18))),
    (((0,1),(7,32)),((0,1),(37,12))),
    (((0,5),(39,6)),((0,7),(5,32))),
    (((0,6),(32,19)),((0,15),(11,30))),
    (((0,0),(12,31)),((0,10),(1,32))),
    (((0,4),(20,28)),((0,11),(27,23))),
    (((0,1),(12,31)),((0,2),(7,32))),
    (((0,0),(18,29)),((0,17),(35,12))),
    (((0,14),(15,29)),((0,18),(22,25))),
    (((0,1),(18,29)),((0,6),(29,22))),
    (((0,4),(22,27)),((0,4),(28,23))),
    (((0,2),(12,31)),((0,7),(11,31))),
    (((0,7),(30,21)),((0,9),(14,30))),
    (((0,12),(24,25)),((0,12),(39,0))),
    (((0,2),(18,29)),((0,3),(7,32))),
    (((0,14),(7,31)),((0,36),(2,25))),
    (((0,0),(36,14)),((0,6),(6,32))),
    (((0,0),(34,17)),((0,13),(29,21))),
    (((0,1),(36,14)),((0,14),(25,24))),
    (((0,1),(34,17)),((0,3),(12,31))),
    (((0,9),(37,11)),((0,12),(37,10))),
    (((0,20),(37,4)),((0,22),(0,30))),
    (((0,0),(24,26)),((0,0),(39,7))),
    (((0,2),(36,14)),((0,7),(32,19))),
    (((0,0),(38,10)),((0,1),(24,26))),
    (((0,4),(7,32)),((0,4),(37,12))),
    (((0,1),(38,10)),((0,10),(26,24))),
    (((0,9),(17,29)),((0,14),(34,15))),
    (((0,21),(24,23)),((0,22),(22,24))),
    (((0,0),(40,0)),((0,2),(24,26))),
    (((0,4),(12,31)),((0,10),(3,32)))]
  have hc : ∀ i : Fin 100, Good (4742+i.val) (c i).1 ∧
      Good (4742+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 100 := ⟨n-4742,by omega⟩
  have he : 4742+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma cert_4842 (n : ℕ) (hlo : 4842≤n) (hhi : n<4900) : 2≤a n := by
  let c : Fin 58 → Tuple4×Tuple4 := ![
    (((0,0),(27,24)),((0,1),(40,0))),
    (((0,3),(34,17)),((0,11),(0,32))),
    (((0,1),(27,24)),((0,4),(18,29))),
    (((0,8),(11,31)),((0,8),(35,15))),
    (((0,0),(40,1)),((0,8),(30,21))),
    (((0,2),(40,0)),((0,6),(20,28))),
    (((0,1),(40,1)),((0,3),(24,26))),
    (((0,2),(27,24)),((0,13),(32,18))),
    (((0,3),(38,10)),((0,5),(7,32))),
    (((0,12),(27,23)),((0,13),(28,22))),
    (((0,6),(22,27)),((0,6),(28,23))),
    (((0,2),(40,1)),((0,4),(36,14))),
    (((0,4),(34,17)),((0,37),(7,24))),
    (((0,3),(40,0)),((0,5),(12,31))),
    (((0,0),(8,32)),((0,14),(22,26))),
    (((0,3),(27,24)),((0,8),(32,19))),
    (((0,1),(8,32)),((0,5),(18,29))),
    (((0,4),(24,26)),((0,4),(39,7))),
    (((0,10),(37,11)),((0,29),(2,28))),
    (((0,0),(40,2)),((0,3),(40,1))),
    (((0,7),(15,30)),((0,7),(33,18))),
    (((0,1),(40,2)),((0,2),(8,32))),
    (((0,33),(31,8)),((0,34),(29,11))),
    (((0,11),(34,16)),((0,17),(4,31))),
    (((0,4),(40,0)),((0,18),(0,31))),
    (((0,5),(36,14)),((0,6),(7,32))),
    (((0,2),(40,2)),((0,4),(27,24))),
    (((0,11),(26,24)),((0,12),(39,3))),
    (((0,8),(6,32)),((0,9),(31,20))),
    (((0,3),(8,32)),((0,9),(11,31))),
    (((0,4),(40,1)),((0,6),(12,31))),
    (((0,5),(24,26)),((0,5),(39,7))),
    (((0,9),(38,9)),((0,20),(37,5))),
    (((0,5),(38,10)),((0,6),(18,29))),
    (((0,3),(40,2)),((0,9),(25,25))),
    (((0,10),(39,5)),((0,16),(6,31))),
    (((0,11),(23,26)),((0,12),(0,32))),
    (((0,0),(16,30)),((0,45),(16,15))),
    (((0,5),(40,0)),((0,18),(2,31))),
    (((0,1),(16,30)),((0,20),(35,11))),
    (((0,4),(8,32)),((0,5),(27,24))),
    (((0,9),(32,19)),((0,13),(9,31))),
    (((0,6),(36,14)),((0,11),(14,30))),
    (((0,0),(40,3)),((0,6),(34,17))),
    (((0,0),(35,16)),((0,2),(16,30))),
    (((0,1),(40,3)),((0,4),(40,2))),
    (((0,1),(35,16)),((0,26),(33,11))),
    (((0,9),(29,22)),((0,13),(27,23))),
    (((0,6),(24,26)),((0,6),(39,7))),
    (((0,0),(13,31)),((0,10),(5,32))),
    (((0,2),(40,3)),((0,6),(38,10))),
    (((0,1),(13,31)),((0,2),(35,16))),
    (((0,3),(16,30)),((0,12),(19,28))),
    (((0,7),(18,29)),((0,8),(22,27))),
    (((0,5),(8,32)),((0,9),(6,32))),
    (((0,6),(40,0)),((0,28),(26,19))),
    (((0,2),(13,31)),((0,19),(9,30))),
    (((0,6),(27,24)),((0,9),(39,6)))]
  have hc : ∀ i : Fin 58, Good (4842+i.val) (c i).1 ∧
      Good (4842+i.val) (c i).2 ∧ (c i).1 ≠ (c i).2 := by decide
  let i : Fin 58 := ⟨n-4842,by omega⟩
  have he : 4842+i.val=n := by dsimp [i]; omega
  obtain ⟨h1,h2,hne⟩ := hc i
  rw [he] at h1 h2
  exact two_good h1 h2 hne

lemma count_middle (n : ℕ) (hlo : 42≤n) (hhi : n<4900) : 2≤a n := by
  by_cases h142 : n<142
  · exact cert_42 n (by omega) h142
  by_cases h242 : n<242
  · exact cert_142 n (by omega) h242
  by_cases h342 : n<342
  · exact cert_242 n (by omega) h342
  by_cases h442 : n<442
  · exact cert_342 n (by omega) h442
  by_cases h542 : n<542
  · exact cert_442 n (by omega) h542
  by_cases h642 : n<642
  · exact cert_542 n (by omega) h642
  by_cases h742 : n<742
  · exact cert_642 n (by omega) h742
  by_cases h842 : n<842
  · exact cert_742 n (by omega) h842
  by_cases h942 : n<942
  · exact cert_842 n (by omega) h942
  by_cases h1042 : n<1042
  · exact cert_942 n (by omega) h1042
  by_cases h1142 : n<1142
  · exact cert_1042 n (by omega) h1142
  by_cases h1242 : n<1242
  · exact cert_1142 n (by omega) h1242
  by_cases h1342 : n<1342
  · exact cert_1242 n (by omega) h1342
  by_cases h1442 : n<1442
  · exact cert_1342 n (by omega) h1442
  by_cases h1542 : n<1542
  · exact cert_1442 n (by omega) h1542
  by_cases h1642 : n<1642
  · exact cert_1542 n (by omega) h1642
  by_cases h1742 : n<1742
  · exact cert_1642 n (by omega) h1742
  by_cases h1842 : n<1842
  · exact cert_1742 n (by omega) h1842
  by_cases h1942 : n<1942
  · exact cert_1842 n (by omega) h1942
  by_cases h2042 : n<2042
  · exact cert_1942 n (by omega) h2042
  by_cases h2142 : n<2142
  · exact cert_2042 n (by omega) h2142
  by_cases h2242 : n<2242
  · exact cert_2142 n (by omega) h2242
  by_cases h2342 : n<2342
  · exact cert_2242 n (by omega) h2342
  by_cases h2442 : n<2442
  · exact cert_2342 n (by omega) h2442
  by_cases h2542 : n<2542
  · exact cert_2442 n (by omega) h2542
  by_cases h2642 : n<2642
  · exact cert_2542 n (by omega) h2642
  by_cases h2742 : n<2742
  · exact cert_2642 n (by omega) h2742
  by_cases h2842 : n<2842
  · exact cert_2742 n (by omega) h2842
  by_cases h2942 : n<2942
  · exact cert_2842 n (by omega) h2942
  by_cases h3042 : n<3042
  · exact cert_2942 n (by omega) h3042
  by_cases h3142 : n<3142
  · exact cert_3042 n (by omega) h3142
  by_cases h3242 : n<3242
  · exact cert_3142 n (by omega) h3242
  by_cases h3342 : n<3342
  · exact cert_3242 n (by omega) h3342
  by_cases h3442 : n<3442
  · exact cert_3342 n (by omega) h3442
  by_cases h3542 : n<3542
  · exact cert_3442 n (by omega) h3542
  by_cases h3642 : n<3642
  · exact cert_3542 n (by omega) h3642
  by_cases h3742 : n<3742
  · exact cert_3642 n (by omega) h3742
  by_cases h3842 : n<3842
  · exact cert_3742 n (by omega) h3842
  by_cases h3942 : n<3942
  · exact cert_3842 n (by omega) h3942
  by_cases h4042 : n<4042
  · exact cert_3942 n (by omega) h4042
  by_cases h4142 : n<4142
  · exact cert_4042 n (by omega) h4142
  by_cases h4242 : n<4242
  · exact cert_4142 n (by omega) h4242
  by_cases h4342 : n<4342
  · exact cert_4242 n (by omega) h4342
  by_cases h4442 : n<4442
  · exact cert_4342 n (by omega) h4442
  by_cases h4542 : n<4542
  · exact cert_4442 n (by omega) h4542
  by_cases h4642 : n<4642
  · exact cert_4542 n (by omega) h4642
  by_cases h4742 : n<4742
  · exact cert_4642 n (by omega) h4742
  by_cases h4842 : n<4842
  · exact cert_4742 n (by omega) h4842
  exact cert_4842 n (by omega) hhi
end Aux306439

/-! ### Combining the ranges -/
set_option maxHeartbeats 0
namespace Aux306439
lemma count_above (n : ℕ) (hn : 42≤n) : 2≤a n := by
  by_cases h : n<4900
  · exact count_middle n hn h
  · exact count_large n (by omega)
lemma final_result :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  constructor
  · intro n hn
    by_cases h : n≤41
    · rw [small_repSet n h]
      exact (count_small ⟨n,by omega⟩).2 hn
    · have := count_above n (by omega)
      omega
  · intro n
    by_cases h : n≤41
    · rw [small_repSet n h]
      exact (count_small ⟨n,by omega⟩).1
    · have hc := count_above n (by omega)
      have ha : a n ≠ 1 := by omega
      have hn : n ∉ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
        omega
      exact iff_of_false ha hn
end Aux306439

/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by
  exact Aux306439.final_result

theorem a306439_conjecture_1.disproof : ¬ (type_of% @a306439_conjecture_1) := sorry
