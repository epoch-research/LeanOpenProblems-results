import FormalConjecturesUtil
import Submission.ThetaGramCount

/-! The proposed asymmetric minimum-degree criterion also fails. -/
open Finset
namespace Erdos713ThetaGram
set_option maxHeartbeats 2000000

noncomputable def rectCount {A B : Type*} (R : A → B → Prop) (S : Finset A) (T : Finset B) : ℕ := by
  classical
  exact ∑ a ∈ S, (T.filter (R a)).card

open scoped Classical in
lemma rect_cols {A B : Type*} (R : A → B → Prop) (S : Finset A) (T : Finset B) :
    rectCount R S T = ∑ b ∈ T, (S.filter (fun a => R a b)).card := by
  classical
  unfold rectCount
  have hRow (a) : (T.filter (R a)).card = ∑ b ∈ T, if R a b then 1 else 0 :=
    (sum_boole (R a) T).symm
  have hCol (b) : (S.filter (fun a => R a b)).card = ∑ a ∈ S, if R a b then 1 else 0 :=
    (sum_boole (fun a => R a b) S).symm
  simp only [hRow,hCol]
  exact sum_comm

lemma rect_full {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop) :
    rectCount R univ univ = Nat.card {p : A × B // R p.1 p.2} := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold rectCount
  have hRow (a) : (univ.filter (R a)).card = ∑ b : B, if R a b then 1 else 0 :=
    (sum_boole (R a) univ).symm
  simp only [hRow]
  simpa only [Fintype.sum_prod_type] using
    (sum_boole (fun p : A × B => R p.1 p.2) univ)

open scoped Classical in
lemma exists_dense_rectangle {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hDense : a*(Fintype.card A : ℝ)+b*(Fintype.card B : ℝ) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ)) :
    ∃ (S : Finset A) (T : Finset B), S.Nonempty ∧ T.Nonempty ∧
      (∀ x ∈ S, a ≤ ((T.filter (R x)).card : ℝ)) ∧
      (∀ y ∈ T, b ≤ ((S.filter (fun x => R x y)).card : ℝ)) := by
  classical
  let f : Finset A × Finset B → ℝ := fun p => (rectCount R p.1 p.2 : ℝ)-a*p.1.card-b*p.2.card
  obtain ⟨p,_,hp⟩ := exists_max_image (univ : Finset (Finset A × Finset B)) f
    ⟨(univ,univ),mem_univ _⟩
  rcases p with ⟨S,T⟩
  have hPos : 0 < f (S,T) := by
    have hh := hp (univ,univ) (mem_univ _)
    dsimp only [f] at hh ⊢
    rw [rect_full] at hh
    simp only [card_univ] at hh
    linarith
  have hS : S.Nonempty := by
    by_contra hh
    have hEmpty := not_nonempty_iff_eq_empty.mp hh
    simp only [f,hEmpty,rectCount,sum_empty,Nat.cast_zero,card_empty,mul_zero,sub_zero,zero_sub] at hPos
    exact (not_lt_of_ge (mul_nonneg hb (Nat.cast_nonneg T.card))) (by linarith)
  have hT : T.Nonempty := by
    by_contra hh
    have hEmpty := not_nonempty_iff_eq_empty.mp hh
    have hE : rectCount R S T = 0 := by simp [rectCount,hEmpty]
    dsimp only [f] at hPos
    rw [hE,hEmpty] at hPos
    simp only [Nat.cast_zero,card_empty,mul_zero,sub_zero,zero_sub] at hPos
    exact (not_lt_of_ge (mul_nonneg ha (Nat.cast_nonneg S.card))) (by linarith)
  refine ⟨S,T,hS,hT,?_,?_⟩
  · intro x hx
    have hm := hp (S.erase x,T) (mem_univ _)
    have hc : ((S.erase x).card : ℝ)+1 = S.card := by exact_mod_cast card_erase_add_one hx
    have he : (rectCount R (S.erase x) T : ℝ)+(T.filter (R x)).card = rectCount R S T := by
      exact_mod_cast (sum_erase_add S (fun x => (T.filter (R x)).card) hx)
    dsimp only [f] at hm
    rw [← hc] at hm
    linarith
  · intro y hy
    have hm := hp (S,T.erase y) (mem_univ _)
    have hc : ((T.erase y).card : ℝ)+1 = T.card := by exact_mod_cast card_erase_add_one hy
    have he : (rectCount R S (T.erase y) : ℝ)+(S.filter (fun x => R x y)).card = rectCount R S T := by
      rw [rect_cols,rect_cols]
      exact_mod_cast (sum_erase_add T (fun y => (S.filter (fun x => R x y)).card) hy)
    dsimp only [f] at hm
    rw [← hc] at hm
    linarith

open scoped Classical in
lemma subtype_degree {B : Type*} (T : Finset B) (P : B → Prop) :
    Nat.card {b : T // P b.val} = (T.filter P).card := by
  classical
  let e : {b : T // P b.val} ≃ ↥(T.filter P) :=
    { toFun := fun b => ⟨b.val.val,mem_filter.mpr ⟨b.val.prop,b.prop⟩⟩
      invFun := fun b => ⟨⟨b.val,(mem_filter.mp b.prop).1⟩,(mem_filter.mp b.prop).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

lemma no_theta_subtype {A B : Type*} (R : A → B → Prop) (h : ¬ HasTheta R)
    (S : Finset A) (T : Finset B) : ¬ HasTheta (fun (a : S) (b : T) => R a.val b.val) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  exact h ⟨Subtype.val ∘ a,Subtype.val ∘ b,Subtype.val_injective.comp ha,
    Subtype.val_injective.comp hb,h00,h10,h01,h11,h02,h22,h13,h23⟩

lemma no_minimum_degree_criterion (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (D : ℝ),
      0 < Nat.card A ∧ 0 < D ∧ ¬ HasTheta R ∧
      (∀ x, a ≤ (Nat.card {y // R x y} : ℝ)) ∧
      (∀ y, D ≤ (Nat.card {x // R x y} : ℝ)) ∧
      C*(Nat.card A : ℝ) < D^2 := by
  classical
  obtain ⟨r,hr⟩ := exists_nat_gt (a+1)
  obtain ⟨L,hL⟩ := exists_nat_gt (C+1)
  obtain ⟨A,B,instA,instB,R,hFree,hLarge,hRows,hEdges⟩ := exists_oriented_counterexamples r L
  have hm : 0 < Nat.card A := by nlinarith
  have hmr : (0 : ℝ) < Nat.card A := by exact_mod_cast hm
  have hLarge' : (C+1)*(Nat.card B : ℝ)^2 < Nat.card A := by
    have hh : (L : ℝ)*(Nat.card B : ℝ)^2 < Nat.card A := by exact_mod_cast hLarge
    have hl := mul_le_mul_of_nonneg_right hL.le (sq_nonneg (Nat.card B : ℝ))
    linarith
  let D : ℝ := Real.sqrt ((C+1)*(Nat.card A : ℝ))
  have hD : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hDsq : D^2 = (C+1)*(Nat.card A : ℝ) := Real.sq_sqrt (by positivity)
  have hDk : D*(Nat.card B : ℝ) < Nat.card A := by
    apply (sq_lt_sq₀ (by positivity : 0 ≤ D*(Nat.card B : ℝ)) hmr.le).mp
    rw [mul_pow,hDsq]
    have hh := mul_lt_mul_of_pos_right hLarge' hmr
    nlinarith
  have hDensity : a*(Fintype.card A : ℝ)+D*(Fintype.card B : ℝ) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by
    rw [hEdges,Nat.cast_mul]
    simp only [Fintype.card_eq_nat_card]
    have hh := mul_lt_mul_of_pos_right hr hmr
    nlinarith
  obtain ⟨S,T,hS,hT,hRow,hCol⟩ := exists_dense_rectangle R ha.le hD.le hDensity
  have hSpos : 0 < Nat.card S := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    exact hS.card_pos
  have hSle : Nat.card S ≤ Nat.card A := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  refine ⟨S,T,inferInstance,inferInstance,(fun x y => R x.val y.val),D,
    hSpos,hD,no_theta_subtype R hFree S T,?_,?_,?_⟩
  · intro x
    rw [subtype_degree]
    exact hRow x.val x.prop
  · intro y
    change D ≤ (Nat.card {x : S // R x.val y.val} : ℝ)
    rw [subtype_degree S (fun x => R x y.val)]
    exact hCol y.val y.prop
  · have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hSle : (Nat.card S : ℝ) ≤ Nat.card A) hC.le
    nlinarith

#print axioms exists_dense_rectangle
#print axioms no_minimum_degree_criterion
end Erdos713ThetaGram
