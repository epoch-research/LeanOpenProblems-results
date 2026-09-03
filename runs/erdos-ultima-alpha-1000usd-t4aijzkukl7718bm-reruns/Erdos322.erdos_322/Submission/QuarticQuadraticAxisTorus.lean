import Submission.TernaryNonsquareClassification
import Submission.QuadraticFormMiddleZero
import Submission.QuarticQuadraticZeroSpectrum

/-! Quadratic forms over F_5 avoiding the coordinate axes and the torus.
These are finite-field construction obstructions, not integer count bounds. -/
namespace Erdos322Research.QuarticQuadraticAxisTorus

open Finset
open TernaryNonsquareClassification
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev V4 := Fin 4 → K

def linear (b x : Vec) : K := b 0*x 0+b 1*x 1+b 2*x 2

def quad (b : Vec) (c : Coeff) (x : V4) : K :=
  x 0^2 + linear b (Fin.tail x)*x 0 + value c (Fin.tail x)

def discr (b : Vec) (c : Coeff) : Coeff :=
  ![b 0^2-4*c 0,b 1^2-4*c 1,b 2^2-4*c 2,
    2*b 0*b 1-4*c 3,2*b 0*b 2-4*c 4,2*b 1*b 2-4*c 5]

private lemma discr_eval (b : Vec) (c : Coeff) (y : Vec) :
    value (discr b c) y = (linear b y)^2-4*value c y := by
  simp only [value, discr, linear, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

private lemma square_eval (d : Coeff) (l y : Vec) (h : twiceSquare d l) :
    value d y = 2*(linear l y)^2 := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  simp only [value, linear, h0,h1,h2,h3,h4,h5]
  ring

private lemma unit_ne : ∀ i : Fin 4, unit i ≠ 0 := by decide +kernel

private lemma quadratic_roots : ∀ b c : K,
    (∀ i : Fin 4, (unit i)^2+b*unit i+c ≠ 0) →
    (b^2-4*c ≠ 1 ∧ b^2-4*c ≠ 4) ∧ (b^2-4*c=0 → b=0) := by
  decide +kernel

private def diagExceptional (a : Vec) : Prop :=
  (a 0=0 ∧ a 1^2=1 ∧ a 2^2=1) ∨
  (a 1=0 ∧ a 0^2=1 ∧ a 2^2=1) ∨
  (a 2=0 ∧ a 0^2=1 ∧ a 1^2=1)

private instance (a : Vec) : Decidable (diagExceptional a) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

private lemma exceptional_diagonal : ∀ a b : Vec, diagExceptional a →
    (∀ u v : Fin 4,
      a 0+a 1*(unit u)^2+a 2*(unit v)^2=0 →
        b 0+b 1*unit u+b 2*unit v=0) → ∃ j, b j^2=a j := by
  decide +kernel

private lemma linear_zero : ∀ b : Vec,
    (∀ u v : Fin 4, linear b ![1,unit u,unit v]=0) → b=0 := by
  decide +kernel

private lemma kernel_count : ∀ l : Vec, l ≠ 0 →
    (univ.filter (fun y : Vec => linear l y=0)).card=25 := by
  decide +kernel

private lemma cancel_four : ∀ s t : K, s=s-4*t → t=0 := by
  decide +kernel

private lemma anisotropic : ∀ a b : K, a^2-2*b^2=0 → a=0 ∧ b=0 := by
  decide +kernel

/-- The normalized quadratic avoiding all axes and all nonzero-coordinate
vectors has at most twenty-five affine zeros. -/
theorem normalized_zero_bound (b : Vec) (c : Coeff)
    (hc : c 0 ≠ 0 ∧ c 1 ≠ 0 ∧ c 2 ≠ 0)
    (ht : ∀ x : V4, (∀ i, x i ≠ 0) → quad b c x ≠ 0) :
    (univ.filter (fun x : V4 => quad b c x=0)).card ≤ 25 := by
  have hr (u v : Fin 4) := quadratic_roots
    (linear b ![1,unit u,unit v]) (value c ![1,unit u,unit v]) (by
      intro t
      have h := ht ![unit t,1,unit u,unit v] (by
        intro i
        fin_cases i <;> simp [unit_ne])
      simpa only [quad, Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] using h)
  have hd : TorusCondition (discr b c) := by
    intro u v
    rw [discr_eval]
    exact (hr u v).1
  have hz (u v : Fin 4) (h : value (discr b c) ![1,unit u,unit v]=0) :
      linear b ![1,unit u,unit v]=0 := by
    rw [discr_eval] at h
    exact (hr u v).2 h
  obtain hsq | hexc := classify (discr b c) hd
  · obtain ⟨l,hl⟩ := hsq
    have hln : l ≠ 0 := by
      intro he
      have hb : b=0 := linear_zero b (by
        intro u v
        apply hz
        rw [square_eval _ l _ hl, he]
        simp [linear])
      have hh := hl.1
      simp [discr, he, hb] at hh
      exact hc.1 (hh.resolve_left (by decide))
    have hidentity (x : V4) :
        4*quad b c x = (2*x 0+linear b (Fin.tail x))^2-
          2*(linear l (Fin.tail x))^2 := by
      have hh := square_eval (discr b c) l (Fin.tail x) hl
      rw [discr_eval] at hh
      dsimp only [quad]
      linear_combination -hh
    have hzero (x : V4) (hx : quad b c x=0) :
        2*x 0+linear b (Fin.tail x)=0 ∧ linear l (Fin.tail x)=0 := by
      apply anisotropic
      rw [← hidentity, hx, mul_zero]
    calc
      _ ≤ (univ.filter (fun y : Vec => linear l y=0)).card := by
        apply Finset.card_le_card_of_injOn Fin.tail
          (s := univ.filter (fun x : V4 => quad b c x=0))
          (t := univ.filter (fun y : Vec => linear l y=0))
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          exact (hzero x hx).2
        · intro x hx y hy hxy
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx hy
          have hx0 := (hzero x hx).1
          have hy0 := (hzero y hy).1
          rw [← hxy] at hy0
          have he : x 0=y 0 := mul_left_cancel₀ (by decide : (2 : K) ≠ 0)
            (add_right_cancel (hx0.trans hy0.symm))
          rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, he, hxy]
      _ = 25 := kernel_count l hln
  · rcases hexc with ⟨h3,h4,h5,hdiag⟩
    let a : Vec := ![(discr b c) 0,(discr b c) 1,(discr b c) 2]
    have ha : diagExceptional a := hdiag
    obtain ⟨j,hj⟩ := exceptional_diagonal a b ha (by
      intro u v he
      have hh := hz u v
      simp only [value, h3,h4,h5, zero_mul, add_zero] at hh
      have hhe : value (discr b c) ![1,unit u,unit v]=0 := by
        simpa [value, h3,h4,h5,a] using he
      simpa [linear] using hz u v hhe)
    fin_cases j
    all_goals simp only [a, discr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at hj
    · exact False.elim (hc.1 (cancel_four _ _ hj))
    · exact False.elim (hc.2.1 (cancel_four _ _ hj))
    · exact False.elim (hc.2.2 (cancel_four _ _ hj))

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable instance : Invertible (2 : K) := invertibleOfNonzero (by decide)

private theorem coordinates (Q : QuadraticForm K V4) :
    ∃ a : K, ∃ b : Vec, ∃ c : Coeff, ∀ x : V4,
      Q x = a*x 0^2+linear b (Fin.tail x)*x 0+value c (Fin.tail x) := by
  let B := QuadraticMap.associated Q
  let e := QuarticQuadraticMiddleZero.axis
  refine ⟨B (e 0) (e 0),
    ![B (e 0) (e 1)+B (e 1) (e 0), B (e 0) (e 2)+B (e 2) (e 0),
      B (e 0) (e 3)+B (e 3) (e 0)],
    ![B (e 1) (e 1), B (e 2) (e 2), B (e 3) (e 3),
      B (e 1) (e 2)+B (e 2) (e 1), B (e 1) (e 3)+B (e 3) (e 1),
      B (e 2) (e 3)+B (e 3) (e 2)], ?_⟩
  intro x
  rw [← QuadraticFormMiddleZero.formPolynomial_eval Q x]
  simp only [QuadraticFormMiddleZero.formPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp only [Fin.sum_univ_four]
  dsimp [linear, value, Fin.tail, B, e]
  ring

/-- Any four-variable quadratic form that is nonzero on every coordinate
axis and on the torus has at most twenty-five affine zeros. -/
theorem form_axis_torus_bound (Q : QuadraticForm K V4)
    (ha : ∀ i : Fin 4, Q (Pi.single i 1) ≠ 0)
    (ht : ∀ x : V4, (∀ i, x i ≠ 0) → Q x ≠ 0) :
    QuarticQuadraticZeroSpectrum.formZeroCount Q ≤ 25 := by
  obtain ⟨a,b,c,hform⟩ := coordinates Q
  have ha0 : a ≠ 0 := by
    simpa [hform, linear, value, Fin.tail, Pi.single_apply] using ha 0
  have hc0 : c 0 ≠ 0 := by
    simpa [hform, linear, value, Fin.tail, Pi.single_apply] using ha 1
  have hc1 : c 1 ≠ 0 := by
    simpa [hform, linear, value, Fin.tail, Pi.single_apply] using ha 2
  have hc2 : c 2 ≠ 0 := by
    simpa [hform, linear, value, Fin.tail, Pi.single_apply] using ha 3
  let b' : Vec := fun j => a⁻¹*b j
  let c' : Coeff := fun j => a⁻¹*c j
  have hnorm (x : V4) : quad b' c' x = a⁻¹*Q x := by
    rw [hform]
    dsimp [quad, linear, value, b', c']
    field_simp [ha0]
  have hb := normalized_zero_bound b' c'
    ⟨mul_ne_zero (inv_ne_zero ha0) hc0, mul_ne_zero (inv_ne_zero ha0) hc1,
      mul_ne_zero (inv_ne_zero ha0) hc2⟩ (by
        intro x hx
        rw [hnorm]
        exact mul_ne_zero (inv_ne_zero ha0) (ht x hx))
  simpa only [hnorm, mul_eq_zero, inv_eq_zero, ha0, false_or,
    QuarticQuadraticZeroSpectrum.formZeroCount] using hb

/-- In fact, the zero count is exactly twenty-five. -/
theorem form_axis_torus_count (Q : QuadraticForm K V4)
    (ha : ∀ i : Fin 4, Q (Pi.single i 1) ≠ 0)
    (ht : ∀ x : V4, (∀ i, x i ≠ 0) → Q x ≠ 0) :
    QuarticQuadraticZeroSpectrum.formZeroCount Q = 25 := by
  have hb := form_axis_torus_bound Q ha ht
  have hs := QuarticQuadraticZeroSpectrum.form_zero_spectrum Q
  omega

end Erdos322Research.QuarticQuadraticAxisTorus
