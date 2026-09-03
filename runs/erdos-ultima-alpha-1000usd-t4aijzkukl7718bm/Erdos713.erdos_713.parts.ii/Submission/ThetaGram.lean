import FormalConjecturesUtil

/-! Fixed-Gram families of vector-valued quadratics avoid the oriented theta(2,2,4).
This is an obstruction to a proposed auxiliary unbalanced bound, not a disproof
of the main Erdős conjecture. -/
open Finset
namespace Erdos713ThetaGram
set_option maxHeartbeats 2000000

abbrev Coeffs (V : Type*) := Fin 3 → V → ℝ

def eval {V : Type*} (f : Coeffs V) (x : ℝ) : V → ℝ :=
  f 0 + x • f 1 + x^2 • f 2

def SameGram {V : Type*} [Fintype V] (f g : Coeffs V) : Prop :=
  ∀ i j, dotProduct (f i) (f j) = dotProduct (g i) (g j)

lemma SameGram.eval {V : Type*} [Fintype V] {f g : Coeffs V} (h : SameGram f g)
    (x y : ℝ) : dotProduct (eval f x) (eval f y) = dotProduct (eval g x) (eval g y) := by
  dsimp only [SameGram] at h
  simp only [Erdos713ThetaGram.eval, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, h]

lemma factor_of_two_equal_evals {V : Type*} {f g : Coeffs V} {i j : ℝ}
    (hij : i ≠ j) (hi : eval f i = eval g i) (hj : eval f j = eval g j) (x : ℝ) :
    eval g x = eval f x + ((x-i)*(x-j)) • (g 2-f 2) := by
  funext v
  have hi' := congr_fun hi v
  have hj' := congr_fun hj v
  simp only [eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi' hj'
  have hz : (i-j)*((g 1 v-f 1 v)+(i+j)*(g 2 v-f 2 v)) = 0 := by nlinarith
  have hz' := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij)
  simp only [eval, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination -hi' + (x-i)*hz'

lemma eq_of_eval_eq {V : Type*} {f g : Coeffs V} (h : ∀ x : ℝ, eval f x = eval g x) : f = g := by
  funext i v
  have h0 := congr_fun (h 0) v
  have h1 := congr_fun (h 1) v
  have hn := congr_fun (h (-1)) v
  simp only [eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 hn
  fin_cases i <;> dsimp <;> norm_num at h0 h1 hn <;> linarith

lemma theta_rigid {V : Type*} [Fintype V] {f g h : Coeffs V} {i j k l : ℝ}
    (hfg : SameGram f g) (hfh : SameGram f h)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hi : eval f i = eval g i) (hj : eval f j = eval g j)
    (hk : eval h k = eval f k) (hl : eval h l = eval g l) : f = g := by
  let D : V → ℝ := g 2-f 2
  have hf (x : ℝ) : eval g x = eval f x + ((x-i)*(x-j)) • D :=
    factor_of_two_equal_evals hij hi hj x
  have hlne : (l-i)*(l-j) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hli) (sub_ne_zero.mpr hlj)
  have hkne : (k-i)*(k-j) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hki) (sub_ne_zero.mpr hkj)
  have hMixed := hfh.eval k l
  rw [hk,hl,hf l,dotProduct_add,dotProduct_smul,smul_eq_mul] at hMixed
  have hOrth : dotProduct (eval f k) D = 0 := by
    have hz : ((l-i)*(l-j))*dotProduct (eval f k) D = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hlne
  have hNorm := hfg.eval k k
  rw [hf k] at hNorm
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul] at hNorm
  rw [dotProduct_comm D (eval f k),hOrth] at hNorm
  have hDD : dotProduct D D = 0 := by
    have hz : (((k-i)*(k-j))^2)*dotProduct D D = 0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hkne)
  have hD : D = 0 := dotProduct_self_eq_zero.mp hDD
  apply eq_of_eval_eq
  intro x
  simpa only [hD,smul_zero,add_zero] using (hf x).symm

/-- The orientation has three row vertices and four column vertices. -/
def HasTheta {A B : Type*} (R : A → B → Prop) : Prop :=
  ∃ (a : Fin 3 → A) (b : Fin 4 → B), Function.Injective a ∧ Function.Injective b ∧
    R (a 0) (b 0) ∧ R (a 1) (b 0) ∧ R (a 0) (b 1) ∧ R (a 1) (b 1) ∧
    R (a 0) (b 2) ∧ R (a 2) (b 2) ∧ R (a 1) (b 3) ∧ R (a 2) (b 3)

lemma no_theta_of_gram {A I V : Type*} [Fintype V] (f : A → Coeffs V)
    (hf : Function.Injective f) (hGram : ∀ a b, SameGram (f a) (f b))
    (x : I → ℝ) (hx : Function.Injective x) :
    ¬ HasTheta (fun a (b : I × (V → ℝ)) => eval (f a) (x b.1) = b.2) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hidx {u v : Fin 4} (huv : u ≠ v) {w : Fin 3}
      (hu : eval (f (a w)) (x (b u).1) = (b u).2)
      (hv : eval (f (a w)) (x (b v).1) = (b v).2) : x (b u).1 ≠ x (b v).1 := by
    intro he
    apply huv
    apply hb
    exact Prod.ext (hx he) (hu.symm.trans ((congrArg (eval (f (a w))) he).trans hv))
  have he := theta_rigid (hGram (a 0) (a 1)) (hGram (a 0) (a 2))
    (hidx (by decide : (0 : Fin 4) ≠ 1) h00 h01)
    (hidx (by decide : (2 : Fin 4) ≠ 0) h02 h00)
    (hidx (by decide : (2 : Fin 4) ≠ 1) h02 h01)
    (hidx (by decide : (3 : Fin 4) ≠ 0) h13 h10)
    (hidx (by decide : (3 : Fin 4) ≠ 1) h13 h11)
    (h00.trans h10.symm) (h01.trans h11.symm) (h22.trans h02.symm) (h23.trans h13.symm)
  exact (by decide : (0 : Fin 3) ≠ 1) (ha (hf he))

#print axioms theta_rigid
#print axioms no_theta_of_gram
end Erdos713ThetaGram
