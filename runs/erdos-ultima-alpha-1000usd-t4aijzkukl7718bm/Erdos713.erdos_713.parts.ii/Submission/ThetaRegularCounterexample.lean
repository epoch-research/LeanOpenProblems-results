import FormalConjecturesUtil
import Submission.ThetaCappedCounterexample
import Submission.ThetaGramPrune

/-! Local theta counterexamples with no isolated vertices and quantitative
degree control on both shores. This is not a counterexample to Erdos 713. -/
open Finset
namespace Erdos713ThetaRegular
open Erdos713ThetaGram Erdos713ThetaSplit
set_option maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open scoped Classical in
lemma exists_dense_rectangle_with_mass {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hDense : a*(Fintype.card A : ℝ)+b*(Fintype.card B : ℝ) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ)) :
    ∃ (S : Finset A) (T : Finset B), S.Nonempty ∧ T.Nonempty ∧
      (∀ x ∈ S, a ≤ ((T.filter (R x)).card : ℝ)) ∧
      (∀ y ∈ T, b ≤ ((S.filter (fun x => R x y)).card : ℝ)) ∧
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) - a*Fintype.card A - b*Fintype.card B ≤
        (rectCount R S T : ℝ) := by
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
  refine ⟨S,T,hS,hT,?_,?_,?_⟩
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

  · have hm := hp (univ,univ) (mem_univ _)
    dsimp only [f] at hm
    rw [rect_full] at hm
    simp only [card_univ] at hm
    have h₁ := mul_nonneg ha (Nat.cast_nonneg S.card)
    have h₂ := mul_nonneg hb (Nat.cast_nonneg T.card)
    linarith

lemma columns_le_mul {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) {d q : ℕ} (hd : 0 < d)
    (he : Nat.card {p : A × B // R p.1 p.2} ≤ q*d^2) :
    Nat.card (SplitColumns R d) ≤ (q+1)*d+Nat.card B := by
  classical
  have hc : Nat.card (SplitColumns R d) =
      (∑ b, Nat.card {a // R a b}/d)+Nat.card B+d := by
    simp [SplitColumns,sum_add_distrib,Nat.card_eq_fintype_card]
  have hs : d*(∑ b, Nat.card {a // R a b}/d) ≤ d*(q*d) := by
    calc
      _ = ∑ b, d*(Nat.card {a // R a b}/d) := by rw [mul_sum]
      _ ≤ ∑ b, Nat.card {a // R a b} := sum_le_sum (fun b _ => Nat.mul_div_le _ _)
      _ ≤ q*d^2 := by rwa [← edge_card_eq_cols]
      _ = d*(q*d) := by ring
  have hsd : (∑ b, Nat.card {a // R a b}/d) ≤ q*d := Nat.le_of_mul_le_mul_left hs hd
  nlinarith

lemma restricted_row_le {A B : Type*} [Fintype B] (R : A → B → Prop)
    (S : Finset A) (T : Finset B) (a : S) :
    Nat.card {b : T // R a.val b.val} ≤ Nat.card {b // R a.val b} := by
  apply Nat.card_le_card_of_injective (fun b => (⟨b.val.val,b.prop⟩ : {b // R a.val b}))
  intro b c he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : {b // R a.val b} => z.val) he

lemma restricted_col_le {A B : Type*} [Fintype A] (R : A → B → Prop)
    (S : Finset A) (T : Finset B) (b : T) :
    Nat.card {a : S // R a.val b.val} ≤ Nat.card {a // R a b.val} :=
  restricted_row_le (fun b a => R a b) T S b

lemma restricted_edge_count {A B : Type*} (R : A → B → Prop)
    (S : Finset A) (T : Finset B) :
    Nat.card {p : S × T // R p.1.val p.2.val} = rectCount R S T := by
  classical
  rw [edge_card_eq_rows (fun (a : S) (b : T) => R a.val b.val)]
  simp only [subtype_degree,rectCount]
  exact sum_coe_sort S (fun a => (T.filter (R a)).card)

#print axioms exists_dense_rectangle_with_mass
#print axioms columns_le_mul
end Erdos713ThetaRegular

namespace Erdos713ThetaRegular
open Erdos713ThetaGram Erdos713ThetaSplit
set_option maxHeartbeats 2000000

/-- Even uniformly nonzero degrees and bounded degree ratios on both shores
do not imply the proposed unbalanced local theta bound. -/
lemma exists_regular_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      0 < r ∧ N ≤ r ∧ ¬ HasTheta R ∧ 0 < Nat.card A ∧ 0 < Nat.card B ∧
      Nat.card A ≤ (Nat.card B)^2 ∧
      (∀ a, r ≤ Nat.card {b // R a b} ∧ Nat.card {b // R a b} ≤ 16*r) ∧
      (∀ b, Nat.card B ≤ 1152*Nat.card {a // R a b} ∧ Nat.card {a // R a b} ≤ Nat.card B) ∧
      N*(Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1)) <
        Nat.card {p : A × B // R p.1 p.2} := by
  classical
  let t := 100*N+100
  have ht : 1 ≤ t := by dsimp [t]; omega
  obtain ⟨A,B,instA,instB,R,hFree,hLarge,hRow,hEdges⟩ :=
    exists_oriented_counterexamples (16*t^2) 1
  simp only [one_mul] at hLarge
  let m := Nat.card A
  have hm : 0 < m := by dsimp [m]; nlinarith
  haveI : Nonempty A := (Nat.card_pos_iff.mp hm).1
  have hBpos : 0 < Nat.card B := by
    let a : A := Classical.arbitrary A
    have hh := Nat.card_le_card_of_injective
      (fun b : {b // R a b} => b.val) Subtype.val_injective
    rw [hRow a] at hh
    nlinarith
  haveI : Nonempty B := (Nat.card_pos_iff.mp hBpos).1
  let s := Nat.sqrt m+1
  let d := t*s
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hd : 0 < d := Nat.mul_pos (by omega) (by omega)
  have hms : m ≤ s^2 := by
    have hlt : m < s^2 := by
      simpa only [s,pow_two,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt m
    exact hlt.le
  have hs4 : s^2 ≤ 4*m := by
    have hz := Nat.sqrt_le m
    have hz' := Nat.sqrt_le_self m
    dsimp [s]
    nlinarith
  have hk : Nat.card B ≤ s := by
    have hh : Nat.card B ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by dsimp [m]; nlinarith)
    dsimp [s]
    omega
  have hsd : s ≤ d := by dsimp [d]; nlinarith
  have hd4 : d^2 ≤ 4*m*t^2 := by
    have hh := Nat.mul_le_mul_right (t^2) hs4
    dsimp [d]
    nlinarith only [hh]
  have he : Nat.card {p : A × B // R p.1 p.2} ≤ 16*d^2 := by
    rw [hEdges]
    have hh := Nat.mul_le_mul_right (16*t^2) hms
    dsimp [d,m] at *
    nlinarith only [hh]
  let Q := split R d
  let K := Nat.card (SplitColumns R d)
  have hK : K ≤ 18*d := by
    have hh := columns_le_mul R hd he
    dsimp [K]
    nlinarith
  have hEdge : Nat.card {p : A × SplitColumns R d // Q p.1 p.2} = 16*m*t^2 := by
    change Nat.card {p : A × SplitColumns R d // split R d p.1 p.2} = _
    rw [Erdos713ThetaSplit.edge_card,hEdges]
    dsimp [m]
    ring
  have hdK : d*K ≤ 72*m*t^2 := by
    have hh := Nat.mul_le_mul_left d hK
    nlinarith
  have hWeight : (t : ℝ)^2*(m : ℝ)+(d : ℝ)/64*(K : ℝ) ≤ 8*(m : ℝ)*(t : ℝ)^2 := by
    have hh : (d : ℝ)*(K : ℝ) ≤ 72*(m : ℝ)*(t : ℝ)^2 := by exact_mod_cast hdK
    nlinarith [show (0 : ℝ) ≤ (m : ℝ)*(t : ℝ)^2 by positivity]
  have hPositive : (0 : ℝ) < (m : ℝ)*(t : ℝ)^2 := by positivity
  have hDense : (t : ℝ)^2*(Fintype.card A : ℝ)+(d : ℝ)/64*(Fintype.card (SplitColumns R d) : ℝ) <
      (Nat.card {p : A × SplitColumns R d // Q p.1 p.2} : ℝ) := by
    rw [hEdge]
    simp only [Fintype.card_eq_nat_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    change (t : ℝ)^2*(m : ℝ)+(d : ℝ)/64*(K : ℝ) < 16*(m : ℝ)*(t : ℝ)^2
    nlinarith
  obtain ⟨S,T,hS,hT,hRows,hCols,hMass⟩ := exists_dense_rectangle_with_mass Q
    (sq_nonneg (t : ℝ)) (show 0 ≤ (d : ℝ)/64 by positivity) hDense
  have hM : 16*m*t^2 ≤ 2*rectCount Q S T := by
    have hh : (16 : ℝ)*(m : ℝ)*(t : ℝ)^2 ≤ 2*(rectCount Q S T : ℝ) := by
      rw [hEdge] at hMass
      simp only [Fintype.card_eq_nat_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hMass
      change 16*(m : ℝ)*(t : ℝ)^2 - (t : ℝ)^2*(m : ℝ) -
        (d : ℝ)/64*(K : ℝ) ≤ (rectCount Q S T : ℝ) at hMass
      nlinarith
    exact_mod_cast hh
  have hSle : Nat.card S ≤ m := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hTle : Nat.card T ≤ K := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hRowUpper (a : S) : Nat.card {b : T // Q a.val b.val} ≤ 16*t^2 := by
    exact (restricted_row_le Q S T a).trans_eq (by change Nat.card {b // split R d a.val b} = _; rw [Erdos713ThetaSplit.row_card,hRow])
  have hColUpper (b : T) : Nat.card {a : S // Q a.val b.val} ≤ d :=
    (restricted_col_le Q S T b).trans (col_card_le R hd b.val)
  have hET : rectCount Q S T ≤ d*Nat.card T := by
    rw [rect_cols,Nat.card_eq_fintype_card,Fintype.card_coe]
    calc
      _ ≤ ∑ _b ∈ T, d := sum_le_sum (fun b hb => by
        have hh := hColUpper ⟨b,hb⟩
        change Nat.card {a : S // Q a.val b} ≤ d at hh
        rwa [subtype_degree S (fun a => Q a b)] at hh)
      _ = d*T.card := by simp [Nat.mul_comm]
  have hDsmall : 2*d ≤ Nat.card T := by
    apply Nat.le_of_mul_le_mul_left (c := d) _ hd
    nlinarith [hd4,hM,hET]
  have hRowLower (a : S) : t^2 ≤ Nat.card {b : T // Q a.val b.val} := by
    rw [subtype_degree]
    have hh := hRows a.val a.prop
    exact_mod_cast hh
  have hColLower (b : T) : Nat.card T ≤ 1152*Nat.card {a : S // Q a.val b.val} := by
    have hh := hCols b.val b.prop
    have hK' : (Nat.card T : ℝ) ≤ 18*(d : ℝ) := by exact_mod_cast hTle.trans hK
    rw [← subtype_degree S (fun a => Q a b.val)] at hh
    have hFinal : (Nat.card T : ℝ) ≤ 1152*(Nat.card {a : S // Q a.val b.val} : ℝ) := by
      nlinarith
    exact_mod_cast hFinal
  have hSize : Nat.card S ≤ (Nat.card T)^2 := by
    calc
      Nat.card S ≤ m := hSle
      _ ≤ s^2 := hms
      _ ≤ d^2 := Nat.pow_le_pow_left hsd 2
      _ ≤ (Nat.card T)^2 := Nat.pow_le_pow_left (by omega) 2
  have hSqrt : Nat.sqrt (Nat.card S)+1 ≤ s := by
    have hh := Nat.sqrt_le_sqrt hSle
    dsimp [s]
    omega
  have hSmall : Nat.card S+Nat.card T*(Nat.sqrt (Nat.card S)+1) ≤ (1+72*t)*m := by
    calc
      _ ≤ m+(18*d)*s := Nat.add_le_add hSle (Nat.mul_le_mul (hTle.trans hK) hSqrt)
      _ = m+18*t*s^2 := by dsimp [d]; ring
      _ ≤ m+18*t*(4*m) := Nat.add_le_add_left (Nat.mul_le_mul_left (18*t) hs4) m
      _ = _ := by ring
  have hBig : N*(1+72*t) < 8*t^2 := by dsimp [t]; nlinarith
  have hMany : N*(Nat.card S+Nat.card T*(Nat.sqrt (Nat.card S)+1)) < rectCount Q S T := by
    calc
      _ ≤ N*((1+72*t)*m) := Nat.mul_le_mul_left N hSmall
      _ = (N*(1+72*t))*m := by ring
      _ < (8*t^2)*m := Nat.mul_lt_mul_of_pos_right hBig hm
      _ ≤ rectCount Q S T := by nlinarith [hM]
  refine ⟨S,T,inferInstance,inferInstance,(fun a b => Q a.val b.val),t^2,
    by positivity,by dsimp [t]; nlinarith,no_theta_subtype Q (split_no_theta R d hFree) S T,
    ?_,?_,hSize,fun a => ⟨hRowLower a,hRowUpper a⟩,
    fun b => ⟨hColLower b,(hColUpper b).trans (by omega)⟩,?_⟩
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hS.card_pos
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hT.card_pos
  · rwa [restricted_edge_count]

#print axioms exists_regular_counterexample
end Erdos713ThetaRegular

namespace Erdos713ThetaRegular
open Erdos713ThetaGram

lemma no_regular_unbalanced_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → 0 < Nat.card A → 0 < Nat.card B → Nat.card A ≤ (Nat.card B)^2 →
      (∃ r : ℕ, 0 < r ∧ ∀ a, r ≤ Nat.card {b // R a b} ∧ Nat.card {b // R a b} ≤ 16*r) →
      (∀ b, Nat.card B ≤ 1152*Nat.card {a // R a b} ∧ Nat.card {a // R a b} ≤ Nat.card B) →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
          C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,instA,instB,R,r,hr,_,hFree,hm,hk,hSize,hRow,hCol,hMany⟩ :=
    exists_regular_counterexample N
  have hs : Real.sqrt (Nat.card A) ≤ (Nat.sqrt (Nat.card A) : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh : Nat.card A ≤ (Nat.sqrt (Nat.card A)+1)^2 := by
      simpa only [Nat.succ_eq_add_one,pow_two] using (Nat.lt_succ_sqrt (Nat.card A)).le
    exact_mod_cast hh
  have hM : (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
      (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*((Nat.sqrt (Nat.card A) : ℝ)+1)) := by
    calc
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) :=
        hBound A B R hFree hm hk hSize ⟨r,hr,hRow⟩ hCol
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*((Nat.sqrt (Nat.card A) : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))) hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.le (by positivity)
  have hM' : (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*((Nat.sqrt (Nat.card A) : ℝ)+1)) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by exact_mod_cast hMany
  exact (not_lt_of_ge hM) hM'

#print axioms no_regular_unbalanced_bound
end Erdos713ThetaRegular
