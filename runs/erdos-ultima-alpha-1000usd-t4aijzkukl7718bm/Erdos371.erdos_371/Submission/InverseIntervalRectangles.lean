import Submission.InverseRectangleSmoothing

/-! Uniform modular-inverse rectangle discrepancy via translation smoothing.
This is not a theorem about unweighted prime-factor comparison density. -/
namespace Erdos371.Kloosterman
open Finset Filter
open scoped Topology

section Translation
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma translationError_nat_succ (A : Finset F) (n : ℕ) :
    translationError A ((n+1:ℕ):F)≤translationError A n+translationError A 1 := by
  have he : (∑ x : F, ‖setIndicator A (x-(n:F))-setIndicator A (x-((n+1:ℕ):F))‖) =
      translationError A 1 := by
    unfold translationError
    apply Fintype.sum_equiv (Equiv.subRight (n:F))
    intro x
    change ‖setIndicator A (x-(n:F))-setIndicator A (x-((n+1:ℕ):F))‖ =
      ‖setIndicator A (x-(n:F))-setIndicator A ((x-(n:F))-1)‖
    congr 3
    push_cast
    ring
  change (∑ x : F, ‖setIndicator A x-setIndicator A (x-((n+1:ℕ):F))‖) ≤
    (∑ x : F, ‖setIndicator A x-setIndicator A (x-(n:F))‖)+translationError A 1
  calc
    _ ≤ ∑ x : F, (‖setIndicator A x-setIndicator A (x-(n:F))‖+
        ‖setIndicator A (x-(n:F))-setIndicator A (x-((n+1:ℕ):F))‖) :=
      sum_le_sum fun x _ => norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = _ := by rw [sum_add_distrib,he]

lemma translationError_nat_le (A : Finset F) (n : ℕ) :
    translationError A n≤(n : ℝ)*translationError A 1 := by
  induction n with
  | zero => simp [translationError]
  | succ n ih =>
    have h := (translationError_nat_succ A n).trans (add_le_add ih le_rfl)
    convert h using 1
    push_cast
    ring
end Translation

section Prime
variable (p : ℕ) [Fact p.Prime]

noncomputable def residueInterval (L : ℕ) : Finset (ZMod p) :=
  univ.filter fun x => x.val<L

lemma residueInterval_card (L : ℕ) (hL : L≤p) : (residueInterval p L).card=L := by
  calc
    _ = (range L).card := by
      apply card_bij (fun x _ => x.val)
      · intro x hx
        exact mem_range.mpr (mem_filter.mp hx).2
      · intro x hx y hy he
        exact ZMod.val_injective p he
      · intro n hn
        have hn' : n<p := (mem_range.mp hn).trans_le hL
        have hv : (n : ZMod p).val=n := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt hn']
        exact ⟨(n : ZMod p),mem_filter.mpr ⟨mem_univ _,by rw [hv]; exact mem_range.mp hn⟩,hv⟩
    _ = L := card_range L

lemma residueInterval_nonempty (H : ℕ) (hH : 0<H) : (residueInterval p H).Nonempty := by
  exact ⟨0,by simp [residueInterval,hH]⟩

lemma residueInterval_one_step_point (L : ℕ) (x : ZMod p) :
    ‖setIndicator (residueInterval p L) x-setIndicator (residueInterval p L) (x-1)‖ ≤
      (if x=(L : ZMod p) then (1 : ℝ) else 0)+(if x=0 then 1 else 0) := by
  have hnorm : ‖setIndicator (residueInterval p L) x-setIndicator (residueInterval p L) (x-1)‖≤1 := by
    unfold setIndicator
    split_ifs <;> norm_num
  by_cases hx : x=0
  · rw [if_pos hx]
    exact hnorm.trans (by split_ifs <;> norm_num)
  by_cases hL : x=(L : ZMod p)
  · rw [if_pos hL,if_neg hx]
    simpa using hnorm
  rw [if_neg hL,if_neg hx,add_zero]
  have hv0 : 0<x.val := by have := (ZMod.val_eq_zero x).not.mpr hx; omega
  have hvL : x.val≠L := by
    intro he
    apply hL
    rw [← he,ZMod.natCast_zmod_val]
  have hv : (x-1).val=x.val-1 := by
    have h1 : (1 : ZMod p).val=1 := ZMod.val_one'' (Fact.out : p.Prime).ne_one
    rw [ZMod.val_sub (by omega),h1]
  have hi : setIndicator (residueInterval p L) x=setIndicator (residueInterval p L) (x-1) := by
    simp only [setIndicator,residueInterval,mem_filter,mem_univ,true_and,hv]
    have he : x.val<L ↔ x.val-1<L := by omega
    simp only [he]
  rw [hi,sub_self,norm_zero]

lemma residueInterval_translation_one (L : ℕ) : translationError (residueInterval p L) 1≤2 := by
  unfold translationError
  have h := sum_le_sum (s := (univ : Finset (ZMod p))) (fun x _ => residueInterval_one_step_point p L x)
  simpa only [sum_add_distrib,sum_ite_eq',mem_univ,if_true,one_add_one_eq_two] using h

lemma residueInterval_smoothingError (L H : ℕ) (hH : 0<H) (hHp : H≤p) :
    smoothingError (residueInterval p L) (residueInterval p H)≤2*(H : ℝ) := by
  have hj : (0 : ℝ)<(residueInterval p H).card := by
    rw [residueInterval_card p H hHp]; exact_mod_cast hH
  unfold smoothingError
  apply (div_le_iff₀ hj).mpr
  calc
    _ ≤ ∑ _y ∈ residueInterval p H, 2*(H : ℝ) := by
      apply sum_le_sum
      intro y hy
      have hyH := (mem_filter.mp hy).2
      have h := translationError_nat_le (residueInterval p L) y.val
      rw [ZMod.natCast_zmod_val] at h
      have ht := residueInterval_translation_one p L
      have hy' : (y.val : ℝ)≤H := by exact_mod_cast hyH.le
      nlinarith
    _ = _ := by simp [mul_comm]

/-- Uniform finite discrepancy for two initial residue intervals. H is the
smoothing width, not an unproved equidistribution parameter. -/
theorem inverse_interval_rectangle_bound (L M H : ℕ) (hL : L≤p) (hM : M≤p)
    (hH : 0<H) (hHp : H≤p) :
    |(inverseRectangleCount (residueInterval p L) (residueInterval p M) : ℝ)-
        (p-1 : ℕ)*((L : ℝ)/p)*((M : ℝ)/p)|/(p : ℝ) ≤
      4*(H : ℝ)/p+Real.sqrt (Real.sqrt (3/(p : ℝ)))*((p : ℝ)/H) := by
  have h := inverseRectangleCount_smoothing_bound ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar p) (residueInterval p L) (residueInterval p M)
    (residueInterval p H) (residueInterval_nonempty p H hH)
  simp only [ZMod.card,ZMod.card_units,residueInterval_card p L hL,
    residueInterval_card p M hM,residueInterval_card p H hHp] at h
  apply h.trans
  gcongr
  have h1 := residueInterval_smoothingError p L H hH hHp
  have h2 := residueInterval_smoothingError p M H hH hHp
  linarith

noncomputable def intervalDiscrepancy (L M : ℕ) : ℝ :=
  |(inverseRectangleCount (residueInterval p L) (residueInterval p M) : ℝ)-
    (p-1 : ℕ)*((L : ℝ)/p)*((M : ℝ)/p)|/(p : ℝ)

lemma inverse_interval_rectangle_div_width (L M K : ℕ) (hL : L≤p) (hM : M≤p) (hK : 2≤K) :
    intervalDiscrepancy p L M≤4/(K : ℝ)+4/(p : ℝ)+
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
  have hb := inverse_interval_rectangle_bound p L M H hL hM hH hHp
  change intervalDiscrepancy p L M≤_ at hb
  apply hb.trans
  calc
    _ ≤ 4*(1/(K : ℝ)+1/(p : ℝ))+Real.sqrt (Real.sqrt (3/(p : ℝ)))*(K : ℝ) := by
      rw [mul_div_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hratio (by norm_num))
        (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = _ := by ring
lemma inverse_interval_ratio_error_le (L M : ℕ) (hL : L≤p) (hM : M≤p) :
    |(inverseRectangleCount (residueInterval p L) (residueInterval p M) : ℝ)/p-
        ((L : ℝ)/p)*((M : ℝ)/p)| ≤ intervalDiscrepancy p L M+1/(p : ℝ) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : 1≤p := (Fact.out : p.Prime).one_le
  have hL' : (L : ℝ)/p≤1 := (div_le_iff₀ hp0).mpr (by simpa using (show (L : ℝ)≤p from by exact_mod_cast hL))
  have hM' : (M : ℝ)/p≤1 := (div_le_iff₀ hp0).mpr (by simpa using (show (M : ℝ)≤p from by exact_mod_cast hM))
  have hprod : ((L : ℝ)/p)*((M : ℝ)/p)≤1 := by
    nlinarith [div_nonneg (Nat.cast_nonneg (α := ℝ) L) hp0.le,
      div_nonneg (Nat.cast_nonneg (α := ℝ) M) hp0.le]
  have he : (inverseRectangleCount (residueInterval p L) (residueInterval p M) : ℝ)/p-
      ((L : ℝ)/p)*((M : ℝ)/p) =
      ((inverseRectangleCount (residueInterval p L) (residueInterval p M) : ℝ)-
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

end Prime

/-- Discrepancy is o(p) uniformly over moving interval endpoints along any
sequence of prime moduli tending to infinity. This is an unconditional
modular-inverse counting theorem, not an assertion about divisor weights. -/
theorem inverse_interval_rectangle_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (L M : ℕ → ℕ) (hL : ∀ n, L n≤p n) (hM : ∀ n, M n≤p n) :
    Tendsto (fun n => intervalDiscrepancy (p n) (L n) (M n)) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun n => hε.trans_le (by unfold intervalDiscrepancy; positivity)
  · intro ε hε
    obtain ⟨K,hK⟩ := exists_nat_gt (max (2 : ℝ) (8/ε))
    have hK2 : 2≤K := by exact_mod_cast (le_max_left _ _).trans hK.le
    have hK0 : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
    have hKe : 4/(K : ℝ)<ε := by
      have hk := (le_max_right _ _).trans_lt hK
      have hk' := (div_lt_iff₀ hε).mp hk
      apply (div_lt_iff₀ hK0).mpr
      nlinarith
    have ht := ((tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp hp).add
      (((((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp hp).sqrt).sqrt).mul_const (K : ℝ))
    simp only [Real.sqrt_zero,zero_mul,zero_add] at ht
    filter_upwards [ht.eventually_lt_const (show 0<ε-4/(K : ℝ) by linarith)] with n hn
    dsimp only [Function.comp_apply] at hn
    have hb := inverse_interval_rectangle_div_width (p n) (L n) (M n) K (hL n) (hM n) hK2
    linarith

/-- The usual normalized rectangle equidistribution statement. It is uniform
in both endpoints, which may depend arbitrarily on the prime modulus. -/
theorem inverse_interval_rectangle_ratio_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (L M : ℕ → ℕ) (hL : ∀ n, L n≤p n) (hM : ∀ n, M n≤p n) :
    Tendsto (fun n =>
      |(inverseRectangleCount (residueInterval (p n) (L n)) (residueInterval (p n) (M n)) : ℝ)/(p n)-
        ((L n : ℝ)/(p n))*((M n : ℝ)/(p n))|) atTop (nhds 0) := by
  have ht := (inverse_interval_rectangle_tendsto p hp L M hL hM).add
    ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hp)
  simp only [add_zero] at ht
  exact squeeze_zero (fun n => abs_nonneg _) (fun n =>
    inverse_interval_ratio_error_le (p n) (L n) (M n) (hL n) (hM n)) ht


#print axioms residueInterval_translation_one
#print axioms residueInterval_smoothingError
#print axioms inverse_interval_rectangle_bound
#print axioms inverse_interval_rectangle_tendsto
#print axioms inverse_interval_rectangle_ratio_tendsto
end Erdos371.Kloosterman
