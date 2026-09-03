import FormalConjecturesUtil
import Submission.SuzukiTraceExponentSeparation

/-! Finite-field Fourier extraction for a trace-product obstruction. -/
namespace Erdos713SuzukiTraceFourier
open scoped Classical
open Finset Erdos713SuzukiTraceExponentSeparation
variable {F : Type*} [Field F] [Fintype F]
set_option maxHeartbeats 2000000

lemma sum_pow_div_pow (a b : ℕ) :
    (∑ x : Fˣ, (x : F)^a/(x : F)^b) =
      if Nat.ModEq (Fintype.card F-1) a b then -1 else 0 := by
  classical
  let φ : Fˣ →* F :=
    { toFun := fun x => (x : F)^a/(x : F)^b
      map_one' := by simp
      map_mul' := by intro x y; simp only [Units.val_mul,mul_pow]; ring }
  have he : φ=1 ↔ Nat.ModEq (Fintype.card F-1) a b := by
    constructor
    · intro h
      obtain ⟨x,hx⟩ := IsCyclic.exists_generator (α := Fˣ)
      have horder : orderOf x = Fintype.card F-1 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hx,Nat.card_eq_fintype_card,Fintype.card_units]
      rw [← horder,← pow_eq_pow_iff_modEq]
      apply Units.ext
      have hx' := DFunLike.congr_fun h x
      change (x : F)^a/(x : F)^b=1 at hx'
      simpa only [Units.val_pow_eq_pow_val] using (div_eq_one_iff_eq (pow_ne_zero b (Units.ne_zero x))).mp hx'
    · intro h
      ext x
      change (x : F)^a/(x : F)^b=1
      apply (div_eq_one_iff_eq (pow_ne_zero b (Units.ne_zero x))).mpr
      exact pow_eq_pow_of_modEq h (FiniteField.pow_card_sub_one_eq_one (x : F) (Units.ne_zero x))
  have hs := sum_hom_units φ
  simp only [Nat.cast_ite,Nat.cast_zero] at hs
  change (∑ x : Fˣ, (x : F)^a/(x : F)^b) = if φ=1 then (Fintype.card Fˣ : F) else 0 at hs
  simp only [he] at hs
  rw [hs]
  split_ifs
  · rw [Fintype.card_units,Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨0⟩),FiniteField.cast_card_eq_zero,Nat.cast_one,zero_sub]
  · rfl

lemma sum_three {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (b : I → F) (c : J → F) (d : K → F)
    (n : I → ℕ) (p : J → ℕ) (q : K → ℕ) (E : ℕ) :
    (∑ x : Fˣ, (∑ i, b i/(x : F)^(n i)) *
      (∑ j, c j*(x : F)^(p j)) * (∑ k, d k*(x : F)^(q k))/(x : F)^E) =
    ∑ i, ∑ j, ∑ k, b i*c j*d k *
      (if Nat.ModEq (Fintype.card F-1) (p j+q k) (E+n i) then -1 else 0) := by
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ x : Fˣ,
        (b i/(x : F)^(n i))*(c j*(x : F)^(p j))*(d k*(x : F)^(q k))/(x : F)^E := by
      simp only [sum_mul,mul_sum,sum_div]
      rw [sum_comm]
      conv_lhs =>
        arg 2; ext k
        rw [sum_comm]
        arg 2; ext j
        rw [sum_comm]
      rw [sum_comm]
      conv_lhs =>
        arg 2; ext j
        rw [sum_comm]
      rw [sum_comm]
    _ = ∑ i, ∑ j, ∑ k, b i*c j*d k *
        (∑ x : Fˣ, (x : F)^(p j+q k)/(x : F)^(E+n i)) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      simp only [pow_add]
      field_simp
    _ = _ := by simp only [sum_pow_div_pow]

lemma sum_two_negative {I J : Type*} [Fintype I] [Fintype J]
    (b : I → F) (c : J → F) (n : I → ℕ) (p : J → ℕ) (E : ℕ) :
    (∑ x : Fˣ, (∑ i, b i/(x : F)^(n i)) *
      (∑ j, c j*(x : F)^(p j))/(x : F)^E) =
    ∑ i, ∑ j, b i*c j *
      (if Nat.ModEq (Fintype.card F-1) (p j) (E+n i) then -1 else 0) := by
  simpa only [Fintype.sum_unique,pow_zero,mul_one,add_zero] using
    sum_three b c (fun _ : Unit => (1 : F)) n p (fun _ => 0) E

lemma sum_two_positive {J K : Type*} [Fintype J] [Fintype K]
    (c : J → F) (d : K → F) (p : J → ℕ) (q : K → ℕ) (E : ℕ) :
    (∑ x : Fˣ, (∑ j, c j*(x : F)^(p j)) *
      (∑ k, d k*(x : F)^(q k))/(x : F)^E) =
    ∑ j, ∑ k, c j*d k *
      (if Nat.ModEq (Fintype.card F-1) (p j+q k) E then -1 else 0) := by
  simpa only [Fintype.sum_unique,pow_zero,div_one,one_mul,add_zero] using
    sum_three (fun _ : Unit => (1 : F)) c d (fun _ => 0) p q E

lemma sum_single_positive {J : Type*} [Fintype J]
    (c : J → F) (p : J → ℕ) (E : ℕ) :
    (∑ x : Fˣ, (∑ j, c j*(x : F)^(p j))/(x : F)^E) =
    ∑ j, c j*(if Nat.ModEq (Fintype.card F-1) (p j) E then -1 else 0) := by
  simpa only [Fintype.sum_unique,pow_zero,mul_one,add_zero] using
    sum_two_positive c (fun _ : Unit => (1 : F)) p (fun _ => 0) E

noncomputable def lin (m : ℕ) (a x : F) : F := ∑ j : Fin m, a^(2^j.val)*x^(2^j.val)
noncomputable def invQuad (r : ℕ) (b x : F) : F :=
  ∑ i : Fin (2*r-1), b^(2^i.val)/x^(2^i.val+2^((i.val+r)%(2*r-1)))

omit [Fintype F] in
lemma sparse_sum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i₀ : I) (j₀ k₀ : J) (hjk : j₀ ≠ k₀) (f : I → J → J → F) :
    (∑ i, ∑ j, ∑ k, if i=i₀ ∧ ((j=j₀ ∧ k=k₀) ∨ (j=k₀ ∧ k=j₀)) then f i j k else 0) =
      f i₀ j₀ k₀ + f i₀ k₀ j₀ := by
  classical
  have he (i : I) (j k : J) :
      (if i=i₀ ∧ ((j=j₀ ∧ k=k₀) ∨ (j=k₀ ∧ k=j₀)) then f i j k else 0) =
      (if i=i₀ then if j=j₀ then if k=k₀ then f i j k else 0 else 0 else 0) +
      (if i=i₀ then if j=k₀ then if k=j₀ then f i j k else 0 else 0 else 0) := by
    split_ifs <;> simp_all
  simp_rw [he,sum_add_distrib]
  simp

lemma cubic_extraction (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F = 2^(2*r-1)) (b d : F) :
    (∑ x : Fˣ, invQuad r b (x : F) * lin (2*r-1) 1 (x : F) * lin (2*r-1) d (x : F) /
      (x : F)^(3+3*2^r)) = -(b*(d^4+d^(2^(r+2)))) := by
  simp only [invQuad,lin]
  rw [sum_three,hcard]
  let i₀ : Fin (2*r-1) := ⟨0,by omega⟩
  let j₀ : Fin (2*r-1) := ⟨2,by omega⟩
  let k₀ : Fin (2*r-1) := ⟨r+2,by omega⟩
  have hjk : j₀ ≠ k₀ := by intro h; have hh := congrArg Fin.val h; dsimp [j₀,k₀] at hh; omega
  have he (i j k : Fin (2*r-1)) :
      b^(2^i.val)*1^(2^j.val)*d^(2^k.val) *
          (if Nat.ModEq (2^(2*r-1)-1) (2^j.val+2^k.val)
            (3+3*2^r+(2^i.val+2^((i.val+r)%(2*r-1)))) then -1 else 0) =
      if i=i₀ ∧ ((j=j₀ ∧ k=k₀) ∨ (j=k₀ ∧ k=j₀)) then -(b^(2^i.val)*d^(2^k.val)) else 0 := by
    rw [← add_assoc]
    simp only [unique_coefficient r i.val j.val k.val hr i.isLt j.isLt k.isLt]
    have hi : i.val=0 ↔ i=i₀ := by simp only [Fin.ext_iff]; rfl
    have hj : j.val=2 ↔ j=j₀ := by simp only [Fin.ext_iff]; rfl
    have hk : k.val=r+2 ↔ k=k₀ := by simp only [Fin.ext_iff]; rfl
    have hj' : j.val=r+2 ↔ j=k₀ := by simp only [Fin.ext_iff]; rfl
    have hk' : k.val=2 ↔ k=j₀ := by simp only [Fin.ext_iff]; rfl
    simp only [hi,hj,hk,hj',hk',one_pow,mul_one,mul_ite,mul_neg,mul_zero,and_comm]
  simp_rw [he]
  apply (sparse_sum i₀ j₀ k₀ hjk (fun i _ k => -(b^(2^i.val)*d^(2^k.val)))).trans
  dsimp [i₀,j₀,k₀]
  norm_num
  ring

lemma mixed_extraction_zero (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F = 2^(2*r-1)) (b : F) :
    (∑ x : Fˣ, invQuad r b (x : F) * lin (2*r-1) 1 (x : F) / (x : F)^(3+3*2^r)) = 0 := by
  simp only [invQuad,lin]
  rw [sum_two_negative,hcard]
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j _
  rw [← add_assoc,if_neg (no_single_with_negative r i.val j.val hr i.isLt j.isLt),mul_zero]

lemma quadratic_extraction_zero (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F = 2^(2*r-1)) (d : F) :
    (∑ x : Fˣ, lin (2*r-1) 1 (x : F) * lin (2*r-1) d (x : F) / (x : F)^(3+3*2^r)) = 0 := by
  simp only [lin]
  rw [sum_two_positive,hcard]
  apply sum_eq_zero
  intro j _
  apply sum_eq_zero
  intro k _
  rw [if_neg (no_two_without_negative r j.val k.val hr j.isLt k.isLt),mul_zero]

lemma linear_extraction_zero (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F = 2^(2*r-1)) :
    (∑ x : Fˣ, lin (2*r-1) (1 : F) (x : F) / (x : F)^(3+3*2^r)) = 0 := by
  simp only [lin]
  rw [sum_single_positive,hcard]
  apply sum_eq_zero
  intro j _
  rw [if_neg (no_single_without_negative r j.val hr j.isLt),mul_zero]

/-- Vanishing of the product forces its isolated Fourier coefficient to vanish. -/
theorem product_coefficient (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F = 2^(2*r-1)) (a b d : F)
    (h : ∀ x : Fˣ, (invQuad r b (x : F)+1)*lin (2*r-1) 1 (x : F)*(lin (2*r-1) d (x : F)+a)=0) :
    b*(d^4+d^(2^(r+2)))=0 := by
  have hs : (∑ x : Fˣ, (invQuad r b (x : F)+1)*lin (2*r-1) 1 (x : F)*(lin (2*r-1) d (x : F)+a) /
      (x : F)^(3+3*2^r)) = 0 := by simp only [h,zero_div,sum_const_zero]
  have he (x : Fˣ) : (invQuad r b (x : F)+1)*lin (2*r-1) 1 (x : F)*(lin (2*r-1) d (x : F)+a) /
      (x : F)^(3+3*2^r) =
      invQuad r b (x : F)*lin (2*r-1) 1 (x : F)*lin (2*r-1) d (x : F)/(x : F)^(3+3*2^r) +
      a*(invQuad r b (x : F)*lin (2*r-1) 1 (x : F)/(x : F)^(3+3*2^r)) +
      lin (2*r-1) 1 (x : F)*lin (2*r-1) d (x : F)/(x : F)^(3+3*2^r) +
      a*(lin (2*r-1) 1 (x : F)/(x : F)^(3+3*2^r)) := by ring
  simp only [he,sum_add_distrib,← mul_sum] at hs
  rw [cubic_extraction r hr hcard,mixed_extraction_zero r hr hcard,
    quadratic_extraction_zero r hr hcard,linear_extraction_zero r hr hcard] at hs
  simpa only [mul_zero,add_zero,neg_eq_zero] using hs

end Erdos713SuzukiTraceFourier
