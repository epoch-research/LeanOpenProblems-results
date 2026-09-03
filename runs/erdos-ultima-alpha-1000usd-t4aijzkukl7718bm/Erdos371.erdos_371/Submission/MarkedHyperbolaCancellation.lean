import Submission.InverseMonotoneRegions
import Submission.CompositeDivisorReflection

/-! Cancellation for actual divisor-marked comparison pairs with a common
losing-product cutoff. Divisor multiplicities are retained. -/
namespace Erdos371.Kloosterman
open Finset Filter
open scoped Topology

section Prime
variable (p : ℕ) [Fact p.Prime]

def chosenDivisorMarks (s : Bool) : Finset (ℕ×ℕ) :=
  if s then riseDivisorMarks p else fallDivisorMarks p

noncomputable def canonicalDivisorPair (s : Bool) (x : (ZMod p)ˣ) : ℕ×ℕ :=
  ((x : ZMod p).val,(orientedInverse p s x).val)

lemma unit_val_pos (x : (ZMod p)ˣ) : 0<(x : ZMod p).val := by
  have h := (ZMod.val_eq_zero (x : ZMod p)).not.mpr (Units.ne_zero x)
  omega

lemma canonicalDivisorPair_mem (s : Bool) (x : (ZMod p)ˣ) (hx : 2≤(x : ZMod p).val) :
    canonicalDivisorPair p s x∈chosenDivisorMarks p s := by
  have hy : 0<(orientedInverse p s x).val := by
    have h := (ZMod.val_eq_zero (orientedInverse p s x)).not.mpr (orientedInverse_ne_zero p s x)
    omega
  have hprod : 1≤(x : ZMod p).val*(orientedInverse p s x).val := by nlinarith
  have hbase : canonicalDivisorPair p s x∈(Ico 2 p).product (Ico 1 p) :=
    mem_product.mpr ⟨mem_Ico.mpr ⟨hx,ZMod.val_lt _⟩,mem_Ico.mpr ⟨hy,ZMod.val_lt _⟩⟩
  cases s
  · apply mem_filter.mpr ⟨hbase,?_⟩
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    dsimp only [canonicalDivisorPair]
    rw [Nat.cast_sub hprod,Nat.cast_mul,Nat.cast_one]
    simp only [orientedInverse,Bool.false_eq_true,if_false,
      ZMod.natCast_zmod_val,mul_inv_cancel₀ (Units.ne_zero x),sub_self]
  · apply mem_filter.mpr ⟨hbase,?_⟩
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    simp only [canonicalDivisorPair,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
      ZMod.natCast_zmod_val,orientedInverse,if_true,mul_neg,mul_inv_cancel₀ (Units.ne_zero x),neg_add_cancel]

lemma exists_unit_of_divisorMark (s : Bool) (ab : ℕ×ℕ) (hab : ab∈chosenDivisorMarks p s) :
    ∃ x : (ZMod p)ˣ, canonicalDivisorPair p s x=ab := by
  have hbounds : ab∈(Ico 2 p).product (Ico 1 p) := by
    cases s <;> exact (mem_filter.mp hab).1
  obtain ⟨ha,hb⟩ := mem_product.mp hbounds
  obtain ⟨ha,ha'⟩ := mem_Ico.mp ha
  obtain ⟨hb,hb'⟩ := mem_Ico.mp hb
  have hval : (ab.1 : ZMod p).val=ab.1 := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt ha']
  have ha0 : (ab.1 : ZMod p)≠0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    simp only [hval,ZMod.val_zero] at hv
    omega
  let x : (ZMod p)ˣ := Units.mk0 (ab.1 : ZMod p) ha0
  have he : (ab.2 : ZMod p)=orientedInverse p s x := by
    have hprod : 1≤ab.1*ab.2 := by nlinarith
    cases s
    · have hd : p∣ab.1*ab.2-1 := (mem_filter.mp hab).2
      have hz := (ZMod.natCast_eq_zero_iff (ab.1*ab.2-1) p).mpr hd
      rw [Nat.cast_sub hprod,Nat.cast_mul,Nat.cast_one] at hz
      change (ab.2 : ZMod p)=(ab.1 : ZMod p)⁻¹
      apply mul_left_cancel₀ ha0
      rw [mul_inv_cancel₀ ha0]
      exact sub_eq_zero.mp hz
    · have hd : p∣ab.1*ab.2+1 := (mem_filter.mp hab).2
      have hz := (ZMod.natCast_eq_zero_iff (ab.1*ab.2+1) p).mpr hd
      rw [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hz
      change (ab.2 : ZMod p)= -(ab.1 : ZMod p)⁻¹
      apply mul_left_cancel₀ ha0
      rw [mul_neg,mul_inv_cancel₀ ha0]
      exact eq_neg_of_add_eq_zero_left hz
  refine ⟨x,Prod.ext ?_ ?_⟩
  · exact hval
  · change (orientedInverse p s x).val=ab.2
    rw [← he,ZMod.val_natCast,Nat.mod_eq_of_lt hb']

noncomputable def markedProductCount (s : Bool) (N : ℕ) : ℕ :=
  ((chosenDivisorMarks p s).filter fun ab => ab.1*ab.2<N).card

lemma markedProductCount_eq_unit_filter (s : Bool) (N : ℕ) :
    markedProductCount p s N=
      (univ.filter fun x : (ZMod p)ˣ => 2≤(x : ZMod p).val ∧
        (x : ZMod p).val*(orientedInverse p s x).val<N).card := by
  symm
  apply card_bij (fun x _ => canonicalDivisorPair p s x)
  · intro x hx
    obtain ⟨hx,hx2,hxN⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨canonicalDivisorPair_mem p s x hx2,hxN⟩
  · intro x hx y hy he
    apply Units.ext
    exact ZMod.val_injective p (congrArg Prod.fst he)
  · intro ab hab
    obtain ⟨hab,hN⟩ := mem_filter.mp hab
    obtain ⟨x,hx⟩ := exists_unit_of_divisorMark p s ab hab
    have hb : ab∈(Ico 2 p).product (Ico 1 p) := by
      cases s <;> exact (mem_filter.mp hab).1
    have ha := (mem_Ico.mp (mem_product.mp hb).1).1
    have hxa : (x : ZMod p).val=ab.1 := congrArg Prod.fst hx
    have hxb : (orientedInverse p s x).val=ab.2 := congrArg Prod.snd hx
    exact ⟨x,mem_filter.mpr ⟨mem_univ _,by omega,by rwa [hxa,hxb]⟩,hx⟩

/-- The only removed inverse-curve point has first coordinate one. -/
lemma markedProductCount_error (s : Bool) (N : ℕ) :
    |(markedProductCount p s N : ℝ)-inverseHyperbolaCount p s N|≤1 := by
  let S : Finset (ZMod p)ˣ := univ.filter fun x => (x : ZMod p).val*(orientedInverse p s x).val<N
  have hsmall : (S.filter fun x : (ZMod p)ˣ => ¬2≤(x : ZMod p).val).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    have hx2 := (mem_filter.mp hx).2
    have hy2 := (mem_filter.mp hy).2
    have hx1 := unit_val_pos p x
    have hy1 := unit_val_pos p y
    apply Units.ext
    apply ZMod.val_injective p
    omega
  have hpart := card_filter_add_card_filter_not (s := S) (fun x : (ZMod p)ˣ => 2≤(x : ZMod p).val)
  have hlarge : (S.filter fun x : (ZMod p)ˣ => 2≤(x : ZMod p).val).card=markedProductCount p s N := by
    rw [markedProductCount_eq_unit_filter]
    congr 1
    ext x
    simp only [S,mem_filter,mem_univ,true_and,and_comm]
  have htotal : S.card=inverseHyperbolaCount p s N := rfl
  rw [hlarge,htotal] at hpart
  have hpart' : (markedProductCount p s N : ℝ)+(S.filter fun x : (ZMod p)ˣ => ¬2≤(x : ZMod p).val).card=
      inverseHyperbolaCount p s N := by exact_mod_cast hpart
  have hsmall' : ((S.filter fun x : (ZMod p)ˣ => ¬2≤(x : ZMod p).val).card : ℝ)≤1 := by exact_mod_cast hsmall
  have hn := Nat.cast_nonneg (α := ℝ) (S.filter fun x : (ZMod p)ˣ => ¬2≤(x : ZMod p).val).card
  rw [abs_le]
  constructor <;> linarith

lemma markedProductCount_difference_bound (N : ℕ) :
    |(markedProductCount p true N : ℝ)/p-(markedProductCount p false N : ℝ)/p|≤
      |(inverseHyperbolaCount p true N : ℝ)/p-(inverseHyperbolaCount p false N : ℝ)/p|+2/(p : ℝ) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ht : |(markedProductCount p true N : ℝ)/p-(inverseHyperbolaCount p true N : ℝ)/p|≤1/(p : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hp0]
    exact div_le_div_of_nonneg_right (markedProductCount_error p true N) hp0.le
  have hf : |(inverseHyperbolaCount p false N : ℝ)/p-(markedProductCount p false N : ℝ)/p|≤1/(p : ℝ) := by
    rw [abs_sub_comm,← sub_div,abs_div,abs_of_pos hp0]
    exact div_le_div_of_nonneg_right (markedProductCount_error p false N) hp0.le
  have h1 := abs_sub_le ((markedProductCount p true N : ℝ)/p)
    ((inverseHyperbolaCount p true N : ℝ)/p) ((markedProductCount p false N : ℝ)/p)
  have h2 := abs_sub_le ((inverseHyperbolaCount p true N : ℝ)/p)
    ((inverseHyperbolaCount p false N : ℝ)/p) ((markedProductCount p false N : ℝ)/p)
  have he : (2 : ℝ)/p=1/p+1/p := by ring
  rw [he]
  linarith
end Prime

/-- Actual rising and falling divisor marks have matching counts to o(p),
uniformly in their common losing-product cutoff. No divisor mark is removed
from its multiplicity at the corresponding natural index. -/
theorem marked_product_difference_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (N : ℕ → ℕ) :
    Tendsto (fun n => |(markedProductCount (p n) true (N n) : ℝ)/(p n)-
      (markedProductCount (p n) false (N n) : ℝ)/(p n)|) atTop (nhds 0) := by
  have ht := (inverse_hyperbola_difference_tendsto p hp N).add
    ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hp)
  simp only [add_zero] at ht
  exact squeeze_zero (fun n => abs_nonneg _) (fun n => markedProductCount_difference_bound (p n) (N n)) ht

#print axioms canonicalDivisorPair_mem
#print axioms markedProductCount_eq_unit_filter
#print axioms markedProductCount_error
#print axioms marked_product_difference_tendsto
end Erdos371.Kloosterman
