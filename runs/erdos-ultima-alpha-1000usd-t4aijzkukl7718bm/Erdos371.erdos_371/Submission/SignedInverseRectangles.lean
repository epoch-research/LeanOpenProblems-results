import Submission.InverseIntervalRectangles

/-! Rectangle estimates for both modular-inverse orientations. Negating a
coordinate preserves the explicit translation-smoothing error. -/
namespace Erdos371.Kloosterman
open Finset Filter
open scoped Topology

section Reflection
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def negatedSet (A : Finset F) : Finset F := A.image Neg.neg

omit [Fintype F] in
lemma negatedSet_card (A : Finset F) : (negatedSet A).card=A.card :=
  card_image_of_injective A neg_injective

omit [Fintype F] in
lemma setIndicator_negatedSet (A : Finset F) (x : F) :
    setIndicator (negatedSet A) x=setIndicator A (-x) := by
  have h : x∈negatedSet A ↔ -x∈A := by
    simp only [negatedSet,mem_image]
    constructor
    · rintro ⟨y,hy,he⟩
      simpa only [← he,neg_neg] using hy
    · intro hx
      exact ⟨-x,hx,neg_neg x⟩
  simp only [setIndicator,h]

lemma translationError_negatedSet (A : Finset F) (y : F) :
    translationError (negatedSet A) y=translationError A y := by
  unfold translationError
  simp_rw [setIndicator_negatedSet]
  apply Fintype.sum_equiv (Equiv.subLeft y)
  intro x
  change ‖setIndicator A (-x)-setIndicator A (-(x-y))‖ =
    ‖setIndicator A (y-x)-setIndicator A ((y-x)-y)‖
  rw [show -(x-y)=y-x by abel,show (y-x)-y= -x by abel,norm_sub_rev]

lemma smoothingError_negatedSet (A J : Finset F) :
    smoothingError (negatedSet A) J=smoothingError A J := by
  simp only [smoothingError,translationError_negatedSet]
end Reflection

section Prime
variable (p : ℕ) [Fact p.Prime]

noncomputable def orientedInterval (s : Bool) (L : ℕ) : Finset (ZMod p) :=
  if s then negatedSet (residueInterval p L) else residueInterval p L

lemma orientedInterval_card (s : Bool) (L : ℕ) (hL : L≤p) :
    (orientedInterval p s L).card=L := by
  cases s <;> simp [orientedInterval,negatedSet_card,residueInterval_card p L hL]

lemma orientedInterval_smoothingError (s : Bool) (L H : ℕ) (hH : 0<H) (hHp : H≤p) :
    smoothingError (orientedInterval p s L) (residueInterval p H)≤2*(H : ℝ) := by
  cases s <;> simp only [orientedInterval,Bool.false_eq_true,if_false,if_true,smoothingError_negatedSet] <;>
    exact residueInterval_smoothingError p L H hH hHp

noncomputable def signedRectangleCount (s : Bool) (L M : ℕ) : ℕ :=
  inverseRectangleCount (residueInterval p L) (orientedInterval p s M)

noncomputable def signedIntervalDiscrepancy (s : Bool) (L M : ℕ) : ℝ :=
  |(signedRectangleCount p s L M : ℝ)-
    (p-1 : ℕ)*((L : ℝ)/p)*((M : ℝ)/p)|/(p : ℝ)

lemma signed_rectangle_bound (s : Bool) (L M H : ℕ) (hL : L≤p) (hM : M≤p)
    (hH : 0<H) (hHp : H≤p) :
    signedIntervalDiscrepancy p s L M≤
      4*(H : ℝ)/p+Real.sqrt (Real.sqrt (3/(p : ℝ)))*((p : ℝ)/H) := by
  have h := inverseRectangleCount_smoothing_bound ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar p) (residueInterval p L) (orientedInterval p s M)
    (residueInterval p H) (residueInterval_nonempty p H hH)
  simp only [ZMod.card,ZMod.card_units,residueInterval_card p L hL,
    orientedInterval_card p s M hM,residueInterval_card p H hHp] at h
  apply h.trans
  gcongr
  have h1 := residueInterval_smoothingError p L H hH hHp
  have h2 := orientedInterval_smoothingError p s M H hH hHp
  linarith

/-- The coordinate description of the two signs; neither inverse value is
zero because x ranges over units. -/
lemma signedRectangleCount_eq_filter (s : Bool) (L M : ℕ) :
    signedRectangleCount p s L M=
      (univ.filter fun x : (ZMod p)ˣ => (x : ZMod p).val<L ∧
        (if s then -(x : ZMod p)⁻¹ else (x : ZMod p)⁻¹).val<M).card := by
  unfold signedRectangleCount inverseRectangleCount
  congr 1
  ext x
  cases s
  · simp only [orientedInterval,Bool.false_eq_true,if_false,residueInterval,mem_filter,mem_univ,true_and]
  · have hn : (x : ZMod p)⁻¹∈negatedSet (residueInterval p M) ↔
        -(x : ZMod p)⁻¹∈residueInterval p M := by
      simp only [negatedSet,mem_image]
      constructor
      · rintro ⟨y,hy,he⟩
        simpa only [← he,neg_neg] using hy
      · intro hx; exact ⟨-(x : ZMod p)⁻¹,hx,neg_neg _⟩
    simp only [orientedInterval,if_true,mem_filter,mem_univ,true_and]
    rw [hn]
    simp only [residueInterval,mem_filter,mem_univ,true_and]

lemma signed_rectangle_div_width (s : Bool) (L M K : ℕ) (hL : L≤p) (hM : M≤p) (hK : 2≤K) :
    signedIntervalDiscrepancy p s L M≤4/(K : ℝ)+4/(p : ℝ)+
      Real.sqrt (Real.sqrt (3/(p : ℝ)))*(K : ℝ) := by
  have hp2 : 2≤p := (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hK0 : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
  let H : ℕ := p/K+1
  have hH : 0<H := Nat.succ_pos _
  have hHp : H≤p := by
    have hle : p/K≤p/2 := Nat.div_le_div_left hK (by norm_num)
    dsimp [H]
    omega
  have hHr : (0 : ℝ)<H := by exact_mod_cast hH
  have hf : (H : ℝ)≤(p : ℝ)/K+1 := by
    dsimp [H]
    push_cast
    exact add_le_add (Nat.cast_div_le (α := ℝ) (m := p) (n := K)) le_rfl
  have hratio : (H : ℝ)/p≤1/(K : ℝ)+1/(p : ℝ) := by
    have h := div_le_div_of_nonneg_right hf hp0.le
    convert h using 1
    field_simp
  have hprod : p≤H*K := by
    have hm := Nat.mod_lt p (show 0<K by omega)
    have he := Nat.div_add_mod p K
    dsimp [H]
    nlinarith
  have hinv : (p : ℝ)/H≤K := by
    apply (div_le_iff₀ hHr).mpr
    exact_mod_cast (by nlinarith : p≤K*H)
  have hb := signed_rectangle_bound p s L M H hL hM hH hHp
  change signedIntervalDiscrepancy p s L M≤_ at hb
  apply hb.trans
  calc
    _ ≤ 4*(1/(K : ℝ)+1/(p : ℝ))+Real.sqrt (Real.sqrt (3/(p : ℝ)))*(K : ℝ) := by
      rw [mul_div_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hratio (by norm_num))
        (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = _ := by ring
lemma signed_rectangle_ratio_error_le (s : Bool) (L M : ℕ) (hL : L≤p) (hM : M≤p) :
    |(signedRectangleCount p s L M : ℝ)/p-
        ((L : ℝ)/p)*((M : ℝ)/p)| ≤ signedIntervalDiscrepancy p s L M+1/(p : ℝ) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : 1≤p := (Fact.out : p.Prime).one_le
  have hL' : (L : ℝ)/p≤1 := (div_le_iff₀ hp0).mpr (by simpa using (show (L : ℝ)≤p from by exact_mod_cast hL))
  have hM' : (M : ℝ)/p≤1 := (div_le_iff₀ hp0).mpr (by simpa using (show (M : ℝ)≤p from by exact_mod_cast hM))
  have hprod : ((L : ℝ)/p)*((M : ℝ)/p)≤1 := by
    nlinarith [div_nonneg (Nat.cast_nonneg (α := ℝ) L) hp0.le,
      div_nonneg (Nat.cast_nonneg (α := ℝ) M) hp0.le]
  have he : (signedRectangleCount p s L M : ℝ)/p-
      ((L : ℝ)/p)*((M : ℝ)/p) =
      ((signedRectangleCount p s L M : ℝ)-
        (p-1 : ℕ)*((L : ℝ)/p)*((M : ℝ)/p))/p-
          (((L : ℝ)/p)*((M : ℝ)/p))/p := by
    rw [Nat.cast_sub hp1]
    push_cast
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_div,abs_of_nonneg hp0.le,
    abs_of_nonneg (show 0≤(((L : ℝ)/p)*((M : ℝ)/p))/p by positivity)]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hprod hp0.le)


lemma signed_rectangle_ratio_uniform (s : Bool) (L M T : ℕ) (hL : L≤p) (hM : M≤p) (hT : 2≤T) :
    |(signedRectangleCount p s L M : ℝ)/p-((L : ℝ)/p)*((M : ℝ)/p)|≤
      4/(T : ℝ)+5/(p : ℝ)+Real.sqrt (Real.sqrt (3/(p : ℝ)))*(T : ℝ) := by
  have h1 := signed_rectangle_ratio_error_le p s L M hL hM
  have h2 := signed_rectangle_div_width p s L M T hL hM hT
  apply (h1.trans (add_le_add h2 le_rfl)).trans_eq
  ring
end Prime

#print axioms translationError_negatedSet
#print axioms signed_rectangle_bound
#print axioms signed_rectangle_ratio_uniform
#print axioms signedRectangleCount_eq_filter
end Erdos371.Kloosterman
