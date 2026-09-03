import Submission.MovingAnchorPell

/-! Completeness of polynomial Pell powers for the coefficient `X²-1`.
This is a classification of a polynomial identity, not of arbitrary
rational-distance point sets or of square values at individual parameters. -/
namespace Erdos213.PolynomialPellClassification
open Polynomial MovingAnchorPell
noncomputable section
set_option maxHeartbeats 3000000

def K : ℝ[X] := X^2-1

def U (n : ℕ) : ℝ[X] := (pellPower K X 1 n).1
def V (n : ℕ) : ℝ[X] := (pellPower K X 1 n).2

@[simp] lemma U_zero : U 0=1 := rfl
@[simp] lemma V_zero : V 0=0 := rfl
@[simp] lemma U_one : U 1=X := by simp [U,pellPower]
@[simp] lemma V_one : V 1=1 := by simp [V,pellPower]

lemma U_succ (n : ℕ) : U (n+1)=X*U n+K*V n := by simp [U,V,pellPower]
lemma V_succ (n : ℕ) : V (n+1)=U n+X*V n := by simp [U,V,pellPower]

lemma U_inverse (n : ℕ) : X*U (n+1)-K*V (n+1)=U n := by
  rw [U_succ,V_succ]
  dsimp [K]
  ring

lemma V_inverse (n : ℕ) : X*V (n+1)-U (n+1)=V n := by
  rw [U_succ,V_succ]
  dsimp [K]
  ring

lemma power_norm (n : ℕ) : U n^2-K*V n^2=1 :=
  pellPower_norm K X 1 (by dsimp [K]; ring) n

def Represented (u v : ℝ[X]) : Prop :=
  ∃ n : ℕ, (u=U n ∨ u= -U n) ∧ (v=V n ∨ v= -V n)

lemma represented_neg_v {u v : ℝ[X]} (h : Represented u v) : Represented u (-v) := by
  obtain ⟨n,hu,hv⟩ := h
  refine ⟨n,hu,?_⟩
  rcases hv with h | h
  · exact Or.inr (by rw [h])
  · exact Or.inl (by rw [h,neg_neg])

lemma represented_forward {u v : ℝ[X]} (h : Represented u v) :
    Represented (X*u+K*v) (u+X*v) := by
  obtain ⟨n,hu,hv⟩ := h
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨n+1,Or.inl (U_succ n).symm,Or.inl (V_succ n).symm⟩
  · cases n with
    | zero => exact ⟨1,Or.inl (by simp),Or.inl (by simp)⟩
    | succ n =>
      refine ⟨n,Or.inl ?_,Or.inr ?_⟩
      · simpa only [mul_neg,sub_eq_add_neg] using U_inverse n
      · linear_combination -(V_inverse n)
  · cases n with
    | zero => exact ⟨1,Or.inr (by simp),Or.inr (by simp)⟩
    | succ n =>
      refine ⟨n,Or.inr ?_,Or.inl ?_⟩
      · linear_combination -(U_inverse n)
      · linear_combination V_inverse n
  · refine ⟨n+1,Or.inr ?_,Or.inr ?_⟩
    · rw [U_succ]; ring
    · rw [V_succ]; ring

lemma pell_degree_leading {u v : ℝ[X]} (hv : v≠0) (h : u^2-K*v^2=1) :
    u.natDegree=v.natDegree+1 ∧ u.leadingCoeff^2=v.leadingCoeff^2 := by
  have hKd : K.natDegree=2 := by
    change (X^2-C (1 : ℝ)).natDegree=2
    exact natDegree_X_pow_sub_C
  have hK : K≠0 := by intro hz; simp [hz] at hKd
  have hKl : K.leadingCoeff=1 := by simp [K]
  have hd : 0<(K*v^2).natDegree := by
    rw [natDegree_mul hK (pow_ne_zero 2 hv),natDegree_pow,hKd]
    omega
  have he : u^2=K*v^2+1 := by linear_combination h
  constructor
  · have hh := congrArg natDegree he
    rw [natDegree_pow,natDegree_add_eq_left_of_natDegree_lt (by simpa using hd),
      natDegree_mul hK (pow_ne_zero 2 hv),natDegree_pow,hKd] at hh
    omega
  · have hh := congrArg leadingCoeff he
    rw [leadingCoeff_pow,leadingCoeff_add_of_degree_lt' (degree_lt_degree (by simpa using hd)),
      leadingCoeff_mul,leadingCoeff_pow,hKl,one_mul] at hh
    exact hh

lemma oriented_difference_degree {u v : ℝ[X]} (hv : v≠0) (h : u^2-K*v^2=1)
    (hl : u.leadingCoeff=v.leadingCoeff) :
    u-X*v=0 ∨ (u-X*v).natDegree<v.natDegree := by
  have hd := (pell_degree_leading hv h).1
  have hu : u≠0 := by intro hz; simp [hz] at hd
  have hXv : X*v≠0 := mul_ne_zero X_ne_zero hv
  have hXvd : (X*v).natDegree=u.natDegree := by
    rw [natDegree_mul X_ne_zero hv,natDegree_X,hd]
    omega
  have hde : (X*v).degree=u.degree := by
    rw [degree_eq_natDegree hXv,degree_eq_natDegree hu,hXvd]
  have hlc : u.leadingCoeff+(X*v).leadingCoeff≠0 := by
    rw [leadingCoeff_mul,leadingCoeff_X,one_mul,hl]
    intro hz
    exact (leadingCoeff_ne_zero.mpr hv) (by linarith)
  have hsum : (u+X*v).natDegree=u.natDegree := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc,hde,max_self]
  have hsum0 : u+X*v≠0 := by intro hz; simp [hz] at hsum; omega
  have hp : (u-X*v)*(u+X*v)=1-v^2 := by
    dsimp [K] at h
    linear_combination h
  by_cases hp0 : u-X*v=0
  · exact Or.inl hp0
  right
  have hpd : (u-X*v).natDegree+(u+X*v).natDegree=(1-v^2).natDegree := by
    rw [←natDegree_mul hp0 hsum0,hp]
  have hb : (1-v^2).natDegree≤2*v.natDegree := by
    have hh := natDegree_sub_le (1 : ℝ[X]) (v^2)
    simpa only [natDegree_one,natDegree_pow,Nat.zero_max,mul_comm] using hh
  omega

/-- Multiplication by the inverse fundamental Pell unit strictly lowers the
first coordinate degree after its leading direction has been chosen. -/
lemma oriented_descent {u v : ℝ[X]} (hv : v≠0) (h : u^2-K*v^2=1)
    (hl : u.leadingCoeff=v.leadingCoeff) :
    ∃ u' v' : ℝ[X], u'^2-K*v'^2=1 ∧ u'.natDegree<u.natDegree ∧
      u=X*u'+K*v' ∧ v=u'+X*v' := by
  let u' := X*u-K*v
  let v' := X*v-u
  have hp : u'^2-K*v'^2=1 := by
    have hh := pell_step K X (-1) u v (by dsimp [K]; ring) h
    dsimp [u',v']
    convert hh using 1; ring
  have hd := (pell_degree_leading hv h).1
  have hvd := oriented_difference_degree hv h hl
  have hdegree : u'.natDegree<u.natDegree := by
    by_cases hv0 : v'=0
    · have hh : u'^2=1 := by simpa [hv0] using hp
      have hh' := congrArg natDegree hh
      rw [natDegree_pow,natDegree_one] at hh'
      omega
    · have hd' := (pell_degree_leading hv0 hp).1
      have he : u-X*v= -v' := by dsimp [v']; ring
      rw [he] at hvd
      rcases hvd with hvd | hvd
      · exact (hv0 (neg_eq_zero.mp hvd)).elim
      · rw [natDegree_neg] at hvd
        omega
  refine ⟨u',v',hp,hdegree,?_,?_⟩ <;> dsimp [u',v',K] <;> ring

lemma represented_by_degree (N : ℕ) : ∀ u v : ℝ[X], u.natDegree=N →
    u^2-K*v^2=1 → Represented u v := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro u v hN hp
    by_cases hv : v=0
    · have hu : u^2=(1 : ℝ[X])^2 := by simpa [hv] using hp
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hu with hu | hu
      · exact ⟨0,Or.inl (by simpa using hu),Or.inl (by simpa using hv)⟩
      · exact ⟨0,Or.inr (by simpa using hu),Or.inl (by simpa using hv)⟩
    have oriented (w : ℝ[X]) (hw : w≠0) (he : u^2-K*w^2=1)
        (hl : u.leadingCoeff=w.leadingCoeff) : Represented u w := by
      obtain ⟨u',v',hp',hd',hu',hv'⟩ := oriented_descent hw he hl
      have hr := ih u'.natDegree (by omega) u' v' rfl hp'
      rw [hu',hv']
      exact represented_forward hr
    have hl := (pell_degree_leading hv hp).2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hl with hl | hl
    · exact oriented v hv hp hl
    · have hh := oriented (-v) (neg_ne_zero.mpr hv) (by simpa using hp)
        (by simpa using hl)
      simpa using represented_neg_v hh

/-- Every real polynomial solution of the normalized Pell equation is a
fundamental-unit power, with independent signs for the two coordinates. -/
theorem polynomial_pell_classification (u v : ℝ[X]) :
    u^2-(X^2-1)*v^2=1 ↔
      ∃ n : ℕ, (u=U n ∨ u= -U n) ∧ (v=V n ∨ v= -V n) := by
  constructor
  · exact represented_by_degree u.natDegree u v rfl
  · rintro ⟨n,hu,hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simpa [K] using power_norm n

lemma U_add_two (n : ℕ) : U (n+2)=2*X*U (n+1)-U n := by
  rw [show n+2=(n+1)+1 by omega,U_succ]
  linear_combination -(U_inverse n)

lemma V_add_two (n : ℕ) : V (n+2)=2*X*V (n+1)-V n := by
  rw [show n+2=(n+1)+1 by omega,V_succ]
  linear_combination -(V_inverse n)

lemma U_eq_chebyshev (n : ℕ) : U n=Chebyshev.T ℝ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    rw [U_add_two,ih0,ih1]
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      (Chebyshev.T_add_two ℝ (n : ℤ)).symm

lemma V_succ_eq_chebyshev (n : ℕ) : V (n+1)=Chebyshev.U ℝ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [V_succ,Chebyshev.U_one]; ring
  | more n ih0 ih1 =>
    rw [show n+2+1=(n+1)+2 by omega,V_add_two]
    rw [show n+1+1=n+2 by omega] at *
    rw [ih0,ih1]
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      (Chebyshev.U_add_two ℝ (n : ℤ)).symm

@[simp] lemma U_natDegree (n : ℕ) : (U n).natDegree=n := by
  rw [U_eq_chebyshev,Chebyshev.natDegree_T]
  simp

@[simp] lemma V_succ_natDegree (n : ℕ) : (V (n+1)).natDegree=n := by
  rw [V_succ_eq_chebyshev,Chebyshev.natDegree_U_natCast]

lemma power_substitution (D L : ℝ[X]) (c : ℝ)
    (hs : L^2-D*(C c)^2=1) (n : ℕ) :
    (U n).comp L=(pellPower D L (C c) n).1 ∧
    C c*(V n).comp L=(pellPower D L (C c) n).2 := by
  have hK : K.comp L=D*(C c)^2 := by
    simp only [K,sub_comp,pow_comp,X_comp,one_comp]
    linear_combination hs
  induction n with
  | zero => simp [pellPower]
  | succ n ih =>
    rw [U_succ,V_succ]
    simp only [add_comp,mul_comp,X_comp]
    constructor
    · change L*(U n).comp L+K.comp L*(V n).comp L=
        L*(pellPower D L (C c) n).1+D*C c*(pellPower D L (C c) n).2
      rw [hK,←ih.1,←ih.2]
      ring
    · change C c*((U n).comp L+L*(V n).comp L)=
        C c*(pellPower D L (C c) n).1+L*(pellPower D L (C c) n).2
      rw [←ih.1,←ih.2]
      ring

/-- Transport through inverse affine coordinates proves completeness for
any coefficient equipped with a nonzero constant Pell seed. -/
lemma classification_of_inverse_seed (D L M : ℝ[X]) (c : ℝ) (hc : c≠0)
    (hLM : L.comp M=X) (hML : M.comp L=X)
    (hseed : L^2-D*(C c)^2=1) (u v : ℝ[X]) (h : u^2-D*v^2=1) :
    ∃ n : ℕ,
      (u=(pellPower D L (C c) n).1 ∨ u= -(pellPower D L (C c) n).1) ∧
      (v=(pellPower D L (C c) n).2 ∨ v= -(pellPower D L (C c) n).2) := by
  have hci : (C c : ℝ[X])*C c⁻¹=1 := by rw [←map_mul,mul_inv_cancel₀ hc,map_one]
  have hci2 : (C c : ℝ[X])^2*(C c⁻¹)^2=1 := by rw [←mul_pow,hci]; simp
  have hD : D.comp M*(C c)^2=K := by
    have hh := congrArg (fun p : ℝ[X] => p.comp M) hseed
    simp only [sub_comp,pow_comp,mul_comp,C_comp,one_comp,hLM] at hh
    dsimp [K]
    linear_combination -hh
  have hK : K*(C c⁻¹)^2=D.comp M := by
    linear_combination -(C c⁻¹)^2*hD+D.comp M*hci2
  have he : (u.comp M)^2-K*(C c⁻¹*v.comp M)^2=1 := by
    have hh := congrArg (fun p : ℝ[X] => p.comp M) h
    simp only [sub_comp,pow_comp,mul_comp,one_comp] at hh
    rw [mul_pow,←mul_assoc,hK]
    exact hh
  obtain ⟨n,hu,hv⟩ := (polynomial_pell_classification _ _).mp he
  obtain ⟨hU,hV⟩ := power_substitution D L c hseed n
  refine ⟨n,?_,?_⟩
  · rcases hu with hu | hu
    · left
      have hh := congrArg (fun p : ℝ[X] => p.comp L) hu
      simpa only [comp_assoc,hML,comp_X,hU] using hh
    · right
      have hh := congrArg (fun p : ℝ[X] => p.comp L) hu
      simpa only [comp_assoc,hML,comp_X,neg_comp,hU] using hh
  · rcases hv with hv | hv
    · left
      have hh := congrArg (fun p : ℝ[X] => C c*p.comp L) hv
      simp only [mul_comp,C_comp,comp_assoc,hML,comp_X] at hh
      rw [←mul_assoc,hci,one_mul,hV] at hh
      exact hh
    · right
      have hh := congrArg (fun p : ℝ[X] => C c*p.comp L) hv
      simp only [mul_comp,C_comp,comp_assoc,hML,comp_X,neg_comp] at hh
      rw [←mul_assoc,hci,one_mul,mul_neg,hV] at hh
      exact hh

def movingD (a b : ℝ) : ℝ[X] := X^2-(C a*X+C b)^2
def movingL (a b : ℝ) : ℝ[X] := C ((1-a^2)/b)*X-C a
def movingM (a b : ℝ) : ℝ[X] := C (b/(1-a^2))*X+C (a*b/(1-a^2))

lemma moving_coordinates_inverse (a b s : ℝ) (hb : b≠0) (hs : s≠0)
    (h : a^2+s^2=1) :
    (movingL a b).comp (movingM a b)=X ∧
    (movingM a b).comp (movingL a b)=X := by
  have hA : 1-a^2≠0 := by nlinarith [sq_pos_of_ne_zero hs]
  constructor
  all_goals
    apply Polynomial.funext
    intro t
    simp only [eval_comp,movingL,movingM,eval_add,eval_sub,eval_mul,eval_C,eval_X]
    field_simp
    ring

lemma moving_seed (a b s : ℝ) (hb : b≠0) (h : a^2+s^2=1) :
    movingL a b^2-movingD a b*(C (s/b))^2=1 := by
  apply Polynomial.funext
  intro t
  simp only [movingL,movingD,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_add,eval_one]
  convert pell_seed t a b s hb h using 1; ring

/-- Completeness of the exact recurrence used for moving-anchor motions,
including both independent sign choices. -/
theorem moving_pell_classification (a b s : ℝ) (hb : b≠0) (hs : s≠0)
    (h : a^2+s^2=1) (u v : ℝ[X]) :
    u^2-movingD a b*v^2=1 ↔
    ∃ n : ℕ,
      (u=(pellPower (movingD a b) (movingL a b) (C (s/b)) n).1 ∨
       u= -(pellPower (movingD a b) (movingL a b) (C (s/b)) n).1) ∧
      (v=(pellPower (movingD a b) (movingL a b) (C (s/b)) n).2 ∨
       v= -(pellPower (movingD a b) (movingL a b) (C (s/b)) n).2) := by
  constructor
  · intro hp
    obtain ⟨hLM,hML⟩ := moving_coordinates_inverse a b s hb hs h
    exact classification_of_inverse_seed _ _ _ (s/b) (div_ne_zero hs hb)
      hLM hML (moving_seed a b s hb h) u v hp
  · rintro ⟨n,hu,hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simpa only [neg_sq] using pellPower_norm _ _ _ (moving_seed a b s hb h) n

lemma moving_degrees (a b s : ℝ) (hb : b≠0) (hs : s≠0) (h : a^2+s^2=1) :
    (movingD a b).natDegree=2 ∧ (movingL a b).natDegree=1 := by
  have hA : 1-a^2≠0 := by nlinarith [sq_pos_of_ne_zero hs]
  constructor
  · have hd : movingD a b=C (1-a^2)*X^2+C (-2*a*b)*X+C (-b^2) := by
      simp only [movingD,map_sub,map_one,map_mul,map_pow,map_neg,map_ofNat]
      ring
    rw [hd]
    exact natDegree_quadratic hA
  · change (C ((1-a^2)/b)*X-C a).natDegree=1
    rw [sub_eq_add_neg,←map_neg]
    exact natDegree_linear (div_ne_zero hA hb)

lemma moving_power_degrees (a b s : ℝ) (hb : b≠0) (hs : s≠0)
    (h : a^2+s^2=1) (n : ℕ) :
    ((pellPower (movingD a b) (movingL a b) (C (s/b)) n).1).natDegree=n ∧
    ((pellPower (movingD a b) (movingL a b) (C (s/b)) (n+1)).2).natDegree=n := by
  obtain ⟨_,hL⟩ := moving_degrees a b s hb hs h
  constructor
  · rw [←(power_substitution _ _ _ (moving_seed a b s hb h) n).1,
      natDegree_comp,U_natDegree,hL,mul_one]
  · rw [←(power_substitution _ _ _ (moving_seed a b s hb h) (n+1)).2,
      natDegree_C_mul (div_ne_zero hs hb),natDegree_comp,V_succ_natDegree,hL,mul_one]

/-- A fully parametrized version of the high-degree moving-anchor reduction.
The norm-one pair is now known to be a power of the fundamental seed, rather
than an unspecified solution of a further Pell equation. Mutual distances
between different exterior motions are still separate requirements. -/
theorem high_degree_motion_classification (x y : ℝ[X]) (hy : y≠0)
    (hdeg : 2<x.natDegree ∨ 2<y.natDegree)
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2)) :
    ∃ a b s : ℝ, ∃ n : ℕ, ∃ u v : ℝ[X],
      b≠0 ∧ 0<s ∧ a^2+s^2=1 ∧
      2*x=X+(C a*X+C b)*u ∧ 2*y=movingD a b*v ∧
      (u=(pellPower (movingD a b) (movingL a b) (C (s/b)) n).1 ∨
       u= -(pellPower (movingD a b) (movingL a b) (C (s/b)) n).1) ∧
      (v=(pellPower (movingD a b) (movingL a b) (C (s/b)) n).2 ∨
       v= -(pellPower (movingD a b) (movingL a b) (C (s/b)) n).2) := by
  obtain ⟨a,b,u,v,hb,ha,hx,hy2,hpell⟩ :=
    high_degree_pell_normal_form_bounded x y hy hdeg h0 h1
  let s := Real.sqrt (1-a^2)
  have hs : 0<s := Real.sqrt_pos.mpr (by linarith)
  have hnorm : a^2+s^2=1 := by
    have hh : s^2=1-a^2 := Real.sq_sqrt (by linarith)
    linarith
  obtain ⟨n,hu,hv⟩ := (moving_pell_classification a b s hb (ne_of_gt hs) hnorm u v).mp hpell
  exact ⟨a,b,s,n,u,v,hb,hs,hnorm,hx,hy2,hu,hv⟩

/-- In a non-axis represented motion, the Pell index is one less than the
vertical degree; the horizontal degree is no larger than that vertical degree. -/
lemma motion_degrees (a b s : ℝ) (hb : b≠0) (hs : s≠0) (hnorm : a^2+s^2=1)
    (n : ℕ) (x y u v : ℝ[X]) (hy : y≠0)
    (hx : 2*x=X+(C a*X+C b)*u) (hy2 : 2*y=movingD a b*v)
    (hu : u=(pellPower (movingD a b) (movingL a b) (C (s/b)) n).1 ∨
      u= -(pellPower (movingD a b) (movingL a b) (C (s/b)) n).1)
    (hv : v=(pellPower (movingD a b) (movingL a b) (C (s/b)) n).2 ∨
      v= -(pellPower (movingD a b) (movingL a b) (C (s/b)) n).2) :
    0<n ∧ y.natDegree=n+1 ∧ x.natDegree≤n+1 := by
  have hv0 : v≠0 := by
    intro hz
    rw [hz,mul_zero] at hy2
    exact hy ((mul_eq_zero.mp hy2).resolve_left (by norm_num))
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    subst n
    simp only [pellPower,neg_zero] at hv
    exact hv.elim hv0 hv0
  have hud : u.natDegree=n := by
    have hh := (moving_power_degrees a b s hb hs hnorm n).1
    rcases hu with hu | hu <;> simpa [hu] using hh
  have hxd : x.natDegree≤n+1 := by
    have hx' : C (2 : ℝ)*x=X+(C a*X+C b)*u := by simpa only [map_ofNat] using hx
    calc
      _ = (C (2 : ℝ)*x).natDegree := by rw [natDegree_C_mul (by norm_num)]
      _ = (X+(C a*X+C b)*u).natDegree := by rw [hx']
      _ ≤ max (X : ℝ[X]).natDegree ((C a*X+C b)*u).natDegree := natDegree_add_le _ _
      _ ≤ n+1 := max_le (by simp) (by
        have hh : ((C a*X+C b)*u).natDegree ≤
            (C a*X+C b).natDegree + u.natDegree := natDegree_mul_le
        have ha := natDegree_linear_le (a:=a) (b:=b)
        rw [hud] at hh
        omega)
  refine ⟨hn,?_,hxd⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have hvd : v.natDegree=k := by
    have hh := (moving_power_degrees a b s hb hs hnorm k).2
    rcases hv with hv | hv <;> simpa [hv] using hh
  have hD := (moving_degrees a b s hb hs hnorm).1
  have hD0 : movingD a b≠0 := by intro hz; simp [hz] at hD
  have hy' : C (2 : ℝ)*y=movingD a b*v := by simpa only [map_ofNat] using hy2
  calc
    _ = (C (2 : ℝ)*y).natDegree := by rw [natDegree_C_mul (by norm_num)]
    _ = (movingD a b*v).natDegree := by rw [hy']
    _ = (movingD a b).natDegree+v.natDegree := natDegree_mul hD0 hv0
    _ = k+1+1 := by omega

lemma U_three : U 3=4*X^3-3*X := by
  simp [U, pellPower, K]
  ring

lemma V_three : V 3=4*X^2-1 := by
  simp [V, pellPower, K]
  ring

def quarticX (a b : ℝ) : ℝ[X] :=
  C (1/2 : ℝ)*(X+(C a*X+C b)*(4*(movingL a b)^3-3*movingL a b))
def quarticY (a b s : ℝ) : ℝ[X] :=
  C (1/2 : ℝ)*movingD a b*C (s/b)*(4*(movingL a b)^2-1)

/-- Complete real-polynomial quartic template, with the two reflection signs
explicit. The degree condition does not assume in advance that `y` is quartic. -/
theorem quartic_motion_classification (x y : ℝ[X]) (hy : y≠0)
    (hd : max x.natDegree y.natDegree=4)
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2)) :
    ∃ a b s : ℝ, b≠0 ∧ 0<s ∧ a^2+s^2=1 ∧
      (x=quarticX a b ∨ x=X-quarticX a b) ∧
      (y=quarticY a b s ∨ y= -quarticY a b s) := by
  have hdeg : 2<x.natDegree ∨ 2<y.natDegree := by omega
  obtain ⟨a,b,s,n,u,v,hb,hs,hnorm,hx,hy2,hu,hv⟩ :=
    high_degree_motion_classification x y hy hdeg h0 h1
  obtain ⟨_,hyd,hxd⟩ := motion_degrees a b s hb (ne_of_gt hs) hnorm n x y u v hy hx hy2 hu hv
  have hn : n=3 := by omega
  subst n
  have hpu : (pellPower (movingD a b) (movingL a b) (C (s/b)) 3).1=
      4*(movingL a b)^3-3*movingL a b := by
    rw [←(power_substitution _ _ _ (moving_seed a b s hb hnorm) 3).1,U_three]
    simp only [sub_comp,mul_comp,pow_comp,X_comp,ofNat_comp,Nat.cast_ofNat]
  have hpv : (pellPower (movingD a b) (movingL a b) (C (s/b)) 3).2=
      C (s/b)*(4*(movingL a b)^2-1) := by
    rw [←(power_substitution _ _ _ (moving_seed a b s hb hnorm) 3).2,V_three]
    simp only [sub_comp,mul_comp,pow_comp,X_comp,ofNat_comp,one_comp,Nat.cast_ofNat]
  rw [hpu] at hu
  rw [hpv] at hv
  have h2 : (2 : ℝ[X])*C (1/2 : ℝ)=1 := by
    have hh := congrArg (C : ℝ →+* ℝ[X]) (show (2 : ℝ)*(1/2)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  refine ⟨a,b,s,hb,hs,hnorm,?_,?_⟩
  · rcases hu with hu | hu
    · left
      rw [hu] at hx
      dsimp [quarticX]
      linear_combination C (1/2 : ℝ)*hx - x*h2
    · right
      rw [hu] at hx
      dsimp [quarticX]
      linear_combination C (1/2 : ℝ)*hx - (x-X)*h2
  · rcases hv with hv | hv
    · left
      rw [hv] at hy2
      dsimp [quarticY]
      linear_combination C (1/2 : ℝ)*hy2-y*h2
    · right
      rw [hv] at hy2
      dsimp [quarticY]
      linear_combination C (1/2 : ℝ)*hy2-y*h2

#print axioms oriented_descent
#print axioms polynomial_pell_classification
#print axioms classification_of_inverse_seed
#print axioms moving_pell_classification
#print axioms high_degree_motion_classification
#print axioms quartic_motion_classification
end
end Erdos213.PolynomialPellClassification
