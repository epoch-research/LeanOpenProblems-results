import FormalConjecturesUtil
import Submission.ThetaGramUpperSize
import Submission.ThetaColumnPadding
import Submission.ThetaTransversalCompletion

/-! Three common columns identify a fixed-Gram row. The property survives
column splitting, padding, and linear transversal completion. -/
namespace Erdos713ThetaThreePoint
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713ThetaBalancedSplit
open Erdos713ThetaColumnPadding Erdos713ThetaTransversal
variable {A B C : Type*}
set_option maxHeartbeats 2000000

def Rigid3 (R : A → B → Prop) : Prop :=
  ∀ a b (f : Fin 3 → B), Function.Injective f →
    (∀ i, R a (f i)) → (∀ i, R b (f i)) → a = b

lemma eq_of_three_equal_evals {V : Type*} {f g : Coeffs V} {i j k : ℝ}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : eval f i = eval g i) (hj : eval f j = eval g j) (hk : eval f k = eval g k) : f = g := by
  have hmul : (k-i)*(k-j) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hki) (sub_ne_zero.mpr hkj)
  have he := factor_of_two_equal_evals hij hi hj k
  have hD : g 2-f 2 = 0 := by
    funext v
    have hkv := congr_fun hk v
    have hev := congr_fun he v
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] at hev
    have hz : ((k-i)*(k-j))*(g 2 v-f 2 v) = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hmul
  apply eq_of_eval_eq
  intro x
  simpa only [hD,smul_zero,add_zero] using (factor_of_two_equal_evals hij hi hj x).symm

lemma incidence_rigid {d r N : ℕ} (g : GramCode d N) : Rigid3 (incidence (r := r) g) := by
  intro a b f hf ha hb
  have hidx : Function.Injective (fun i => (f i).1) := by
    intro i j he
    apply hf
    refine Prod.ext he ?_
    change ∀ i, evalFin a.val (f i).1 = (f i).2 at ha
    exact (ha i).symm.trans ((congrArg (evalFin a.val) he).trans (ha j))
  let t : Fin 3 → ℝ := fun i => ((f i).1.val : ℝ)+1
  have ht : Function.Injective t := by
    intro i j he
    apply hidx
    apply Fin.ext
    dsimp [t] at he
    exact_mod_cast (show (((f i).1.val : ℝ)) = (f j).1.val by linarith)
  have hev (i : Fin 3) : eval (toReal a.val) (t i) = eval (toReal b.val) (t i) :=
    (incidence_real g (ha i)).trans (incidence_real g (hb i)).symm
  have he := eq_of_three_equal_evals
    (fun he => (by decide : (0 : Fin 3) ≠ 1) (ht he))
    (fun he => (by decide : (2 : Fin 3) ≠ 0) (ht he))
    (fun he => (by decide : (2 : Fin 3) ≠ 1) (ht he))
    (hev 0) (hev 1) (hev 2)
  exact Subtype.ext (toReal_injective d N he)

lemma rigid_of_projection {R : A → B → Prop} {T : A → C → Prop}
    (p : C → B) (hp : ∀ a b, T a b → R a (p b))
    (hpi : ∀ a b c, T a b → T a c → p b = p c → b = c)
    (hR : Rigid3 R) : Rigid3 T := by
  intro a b f hf ha hb
  apply hR a b (p ∘ f)
  · intro i j he
    exact hf (hpi a (f i) (f j) (ha i) (ha j) he)
  · exact fun i => hp a (f i) (ha i)
  · exact fun i => hp b (f i) (hb i)

lemma core_rigid [Fintype A] (R : A → B → Prop) (d : ℕ) (hR : Rigid3 R) :
    Rigid3 (coreSplit R d) := by
  apply rigid_of_projection Sigma.fst ?_ ?_ hR
  · rintro a ⟨b,i⟩ hh
    exact hh.choose
  · rintro a ⟨b,i⟩ ⟨c,j⟩ hi hj he
    change b = c at he
    subst c
    obtain ⟨ha,hi⟩ := hi
    obtain ⟨ha',hj⟩ := hj
    have hij : i = j := Fin.ext (hi.symm.trans hj)
    subst j
    rfl

lemma pad_rigid [Nonempty B] {f : B → C} (hf : Function.Injective f)
    {R : A → B → Prop} (hR : Rigid3 R) : Rigid3 (pad f R) := by
  classical
  apply rigid_of_projection (Function.invFun f) ?_ ?_ hR
  · rintro a c ⟨b,hb,rfl⟩
    simpa only [Function.leftInverse_invFun hf b] using hb
  · rintro a c d ⟨b,hb,rfl⟩ ⟨b',hb',rfl⟩ he
    rw [Function.leftInverse_invFun hf b,Function.leftInverse_invFun hf b'] at he
    exact congrArg f he

lemma complete_rigid {I F : Type*} [Field F] (s : I → F) (hs : Function.Injective s)
    {R : A → F → Prop} (hR : Rigid3 R) : Rigid3 (complete s R) := by
  intro a b f hf ha hb
  by_contra hab
  obtain ⟨⟨a',ha'⟩,⟨b',hb'⟩⟩ := branches_old s hs R hab
    (fun he => (by decide : (0 : Fin 3) ≠ 1) (hf he)) (ha 0) (ha 1) (hb 0) (hb 1)
  subst a b
  have hidx : a'.1 = b'.1 := (ha 0).1.trans (hb 0).1.symm
  have he : a'.2 = b'.2 := by
    apply hR a'.2 b'.2 (fun i => (f i).2)
    · intro i j hij
      apply hf
      exact Prod.ext ((ha i).1.symm.trans (ha j).1) hij
    · exact fun i => (ha i).2
    · exact fun i => (hb i).2
  exact hab (congrArg Sum.inl (Prod.ext hidx he))

lemma exists_examples (r L : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ Rigid3 R ∧ L*(Nat.card B)^2 < Nat.card A ∧
      Nat.card A*r ≤ (Nat.card B)^3 ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      Nat.card {p : A × B // R p.1 p.2} = Nat.card A*r := by
  classical
  obtain ⟨N,g,hN,hg⟩ := exists_large_fiber r L
  refine ⟨Fiber g,Columns 19 r N,inferInstance,inferInstance,incidence g,
    incidence_no_theta g,incidence_rigid g,?_,
    Erdos713ThetaGramUpperSize.fiber_cubic_bound hr g,row_card g,edge_card g⟩
  simpa only [Nat.card_eq_fintype_card] using hg

#print axioms incidence_rigid
#print axioms complete_rigid
#print axioms exists_examples
end Erdos713ThetaThreePoint
