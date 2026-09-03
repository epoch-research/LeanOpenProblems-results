import Submission.BinaryQuadraticEnergy
import Submission.QuadraticImageMass

/-! Distinct-value reciprocal divergence for an affine binary-quadratic
lattice with a positive proportion of admissible parameter pairs. -/
namespace Erdos1206.AffineQuadraticImageMass
open Finset Filter QuadraticLatticeLines BinaryQuadraticEnergy FiniteImageEnergy QuadraticImageMass
open scoped Classical Topology

def eval (a b c M v w : ℕ) (x : ℕ × ℕ) : ℕ :=
  a*(M*x.1+v)^2+b*(M*x.1+v)*(M*x.2+w)+c*(M*x.2+w)^2

def parameter (M v w : ℕ) (x : ℕ × ℕ) : Vec :=
  ((M*x.1+v:ℕ),(M*x.2+w:ℕ))

def shift (M v w : ℕ) : ℕ := M+v+w+1

def heightBound (a b c M v w : ℕ) : ℕ := (a+b+c)*(shift M v w)^2

lemma parameter_injective {M v w : ℕ} (hM : 0<M) : Function.Injective (parameter M v w) := by
  intro x y he
  have h1 : M*x.1+v=M*y.1+v := by
    have hh := congrArg Prod.fst he
    dsimp [parameter] at hh
    exact_mod_cast hh
  have h2 : M*x.2+w=M*y.2+w := by
    have hh := congrArg Prod.snd he
    dsimp [parameter] at hh
    exact_mod_cast hh
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left hM (Nat.add_right_cancel h1))
    (Nat.eq_of_mul_eq_mul_left hM (Nat.add_right_cancel h2))

lemma parameter_bounds {M v w k : ℕ} {x : ℕ × ℕ} (hx : x∈grid k) :
    M*x.1+v≤shift M v w*2^k ∧ M*x.2+w≤shift M v w*2^k := by
  obtain ⟨h1,h2⟩ := mem_product.mp hx
  have h1' := Nat.mul_le_mul_left M (mem_range.mp h1).le
  have h2' := Nat.mul_le_mul_left M (mem_range.mp h2).le
  have hp : 1≤(2:ℕ)^k := Nat.one_le_two_pow
  have hv := Nat.mul_le_mul_left v hp
  have hw := Nat.mul_le_mul_left w hp
  dsimp [shift]
  constructor <;> nlinarith

lemma parameter_box {M v w k : ℕ} {x : ℕ × ℕ} (hx : x∈grid k) :
    parameter M v w x∈box (2^(k+shift M v w)) := by
  obtain ⟨h1,h2⟩ := parameter_bounds hx
  have hJ : shift M v w≤2^(shift M v w) := Nat.lt_two_pow_self.le
  have hpow : shift M v w*2^k≤2^(k+shift M v w) := by
    rw [pow_add]
    simpa [mul_comm] using Nat.mul_le_mul_right (2^k) hJ
  apply mem_box_iff.mpr
  apply max_le
  · dsimp [parameter]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast h1.trans hpow
  · dsimp [parameter]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast h2.trans hpow

lemma eval_cast (a b c M v w : ℕ) (x : ℕ × ℕ) :
    (eval a b c M v w x:ℤ)=form a b c (parameter M v w x) := by
  simp [eval,parameter,form]

lemma eval_lower (a b c M v w : ℕ) (ha : 0<a) (hc : 0<c) (hM : 0<M)
    (x : ℕ × ℕ) : (max x.1 x.2)^2≤eval a b c M v w x := by
  have h1 : x.1≤M*x.1+v := by nlinarith
  have h2 : x.2≤M*x.2+w := by nlinarith
  have hh1 := Nat.pow_le_pow_left h1 2
  have hh2 := Nat.pow_le_pow_left h2 2
  have ha1 : (M*x.1+v)^2≤a*(M*x.1+v)^2 := Nat.le_mul_of_pos_left _ ha
  have hc1 : (M*x.2+w)^2≤c*(M*x.2+w)^2 := Nat.le_mul_of_pos_left _ hc
  dsimp [eval]
  rcases le_total x.1 x.2 with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

lemma eval_upper (a b c M v w k : ℕ) {x : ℕ × ℕ} (hx : x∈grid k) :
    eval a b c M v w x≤heightBound a b c M v w*(2^k)^2 := by
  obtain ⟨h1,h2⟩ := parameter_bounds hx
  have h1s := Nat.pow_le_pow_left h1 2
  have h2s := Nat.pow_le_pow_left h2 2
  have h12 := Nat.mul_le_mul h1 h2
  have ha := Nat.mul_le_mul_left a h1s
  have hb := Nat.mul_le_mul_left b h12
  have hc := Nat.mul_le_mul_left c h2s
  dsimp [eval,heightBound]
  nlinarith

lemma equal_pairs_card_bound (a b c M v w k : ℕ) (hM : 0<M)
    (hd : 4*(a:ℤ)*c-(b:ℤ)^2 ≠ 0) :
    (equalPairs (grid k) (eval a b c M v w)).card ≤
      ((100*(coeffBound a b c+1)+9)*(2^(shift M v w))^2)*
        (k+(shift M v w+2))*(2^k)^2 := by
  let F := parameter M v w
  have hFi : Function.Injective F := parameter_injective hM
  let G (p : (ℕ × ℕ) × (ℕ × ℕ)) : Vec × Vec := (F p.1,F p.2)
  have hG : Function.Injective G := by
    intro x y he
    exact Prod.ext (hFi (congrArg Prod.fst he)) (hFi (congrArg Prod.snd he))
  have hm : ∀ p∈equalPairs (grid k) (eval a b c M v w),
      G p∈energy a b c (2^(k+shift M v w)) := by
    intro p hp
    obtain ⟨hpm,he⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp hpm
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨parameter_box hx,parameter_box hy⟩,?_⟩
    have hh := congrArg (fun n : ℕ => (n:ℤ)) he
    simpa only [eval_cast] using hh
  have hc := card_le_card_of_injOn
    (s := equalPairs (grid k) (eval a b c M v w))
    (t := energy a b c (2^(k+shift M v w))) G (fun p hp => hm p hp) hG.injOn
  have he := hc.trans (energy_dyadic_bound hd (k+shift M v w))
  calc
    _ ≤ (100*(coeffBound a b c+1)+9)*(k+shift M v w+2)*(2^(k+shift M v w))^2 := he
    _ = _ := by rw [pow_add]; ring

/-- This conclusion concerns distinct natural output values, not parameter
pairs or collision tuples. -/
theorem distinct_values_not_summable (a b c M v w : ℕ)
    (ha : 0<a) (hc : 0<c) (hM : 0<M)
    (hd : 4*(a:ℤ)*c-(b:ℤ)^2 ≠ 0)
    (P : ℕ × ℕ → Prop) (hpos : ∀ x, P x → 0<eval a b c M v w x)
    (hmany : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
      (((range N) ×ˢ (range N)).filter P).card) :
    ¬ Summable (fun n : ℕ => if n∈(eval a b c M v w) '' {x | P x} then (1:ℝ)/n else 0) := by
  let K := heightBound a b c M v w
  let C := (100*(coeffBound a b c+1)+9)*(2^(shift M v w))^2
  let L := shift M v w+2
  have hK : 0<K := by dsimp [K,heightBound,shift]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  apply QuadraticImageMass.distinct_values_not_summable P (eval a b c M v w)
    K C L hK hC hpos (eval_lower a b c M v w ha hc hM)
    (eval_upper a b c M v w) (fun k => equal_pairs_card_bound a b c M v w k hM hd)
  have hh := (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ))).eventually hmany
  simpa only [grid,Nat.cast_pow,Nat.cast_ofNat] using hh

#print axioms distinct_values_not_summable
end Erdos1206.AffineQuadraticImageMass
