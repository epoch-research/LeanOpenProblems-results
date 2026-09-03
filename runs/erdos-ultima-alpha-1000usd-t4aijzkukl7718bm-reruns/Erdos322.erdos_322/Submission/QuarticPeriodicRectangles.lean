import Submission.QuarticDensityMaximalOrder

/-! Full-period rectangular congruence counts and their range-pigeonhole
certificates. The estimates here do not bound exact representation counts. -/
namespace Erdos322Research.QuarticPeriodicRectangles
noncomputable section
open Finset QuarticFiberBasic QuarticDensityMaximalOrder
open scoped Classical
set_option Elab.async false

/-- The side in coordinate i contains w_i complete periods modulo q. -/
abbrev RectangleFiber (q n : ℕ) (w : Fin 4 → ℕ) :=
  {x : (i : Fin 4) → Fin (w i*q) // (∑ i, (x i : ℕ)^4) ≡ n [MOD q]}

def rectangleCount (q n : ℕ) (w : Fin 4 → ℕ) : ℕ :=
  Fintype.card (RectangleFiber q n w)

private lemma reduce_sum (q : ℕ) (w : Fin 4 → ℕ)
    (x : (i : Fin 4) → Fin (w i*q)) :
    (∑ i, ((x i).modNat : ℕ)^4) ≡ (∑ i, (x i : ℕ)^4) [MOD q] := by
  exact Nat.ModEq.sum fun i _ ↦ (Nat.mod_modEq (x i : ℕ) q).pow 4

private lemma encode_sum (q : ℕ) (w : Fin 4 → ℕ)
    (x : Fin 4 → Fin q) (t : (i : Fin 4) → Fin (w i)) :
    (∑ i, (finProdFinEquiv (t i,x i) : ℕ)^4) ≡ (∑ i, (x i : ℕ)^4) [MOD q] := by
  apply Nat.ModEq.sum
  intro i _
  apply Nat.ModEq.pow
  change ((x i : ℕ)+q*(t i : ℕ))%q=(x i : ℕ)%q
  exact Nat.add_mul_mod_self_left _ _ _

/-- Splitting each coordinate into its residue and quotient is an exact
bijection, including boxes with a zero side length. -/
def rectangleEquiv (q n : ℕ) (w : Fin 4 → ℕ) :
    RectangleFiber q n w ≃ Fiber q n × ((i : Fin 4) → Fin (w i)) where
  toFun x := (⟨fun i ↦ (x.val i).modNat,(reduce_sum q w x.val).trans x.property⟩,
    fun i ↦ (x.val i).divNat)
  invFun y := ⟨fun i ↦ finProdFinEquiv (y.2 i,y.1.val i),
    (encode_sum q w y.1.val y.2).trans y.1.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact finProdFinEquiv.apply_symm_apply (x.val i)
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (y.2 i,y.1.val i))
    · funext i
      exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (y.2 i,y.1.val i))

/-- The congruence count grows exactly by the product of the side multipliers. -/
theorem rectangle_count (q n : ℕ) (w : Fin 4 → ℕ) :
    rectangleCount q n w = fiberCount q n * ∏ i, w i := by
  unfold rectangleCount fiberCount
  rw [Fintype.card_congr (rectangleEquiv q n w),Fintype.card_prod,Fintype.card_pi]
  simp

/-- A direct four-variable AM-GM certificate. -/
lemma four_mul_prod_le_sum_fourth (w : Fin 4 → ℝ) :
    4*(∏ i, w i) ≤ ∑ i, w i^4 := by
  rw [Fin.prod_univ_four,Fin.sum_univ_four]
  nlinarith [sq_nonneg (w 0^2-w 1^2),sq_nonneg (w 2^2-w 3^2),
    sq_nonneg (w 0*w 1-w 2*w 3)]

/-- The upper bound on the target-quotient index used by the full-range
pigeonhole argument. It deliberately includes a harmless endpoint. -/
def rangeLength (q : ℕ) (w : Fin 4 → ℕ) : ℕ :=
  q^3*(∑ i, w i^4)+1

/-- At residue zero, every represented exact target has an index in this range. -/
theorem target_index_lt (q : ℕ) (hq : 0 < q) (w : Fin 4 → ℕ)
    (x : (i : Fin 4) → Fin (w i*q)) :
    (∑ i, (x i : ℕ)^4)/q < rangeLength q w := by
  have hb : (∑ i, (x i : ℕ)^4) ≤ q*(q^3*(∑ i, w i^4)) := by
    calc
      (∑ i, (x i : ℕ)^4) ≤ ∑ i, (w i*q)^4 := by
        exact sum_le_sum fun i _ ↦ Nat.pow_le_pow_left (x i).isLt.le 4
      _ = q*(q^3*(∑ i, w i^4)) := by
        simp only [mul_pow,← Finset.sum_mul]
        ring
  have hd := Nat.div_le_div_right (c := q) hb
  rw [Nat.mul_div_cancel_left _ hq] at hd
  exact Nat.lt_succ_of_le hd

/-- The average supplied by counting the whole interval of possible target
indices. This is a lower certificate for a peak, not an upper bound on a peak. -/
def rangeCertificate (q n : ℕ) (w : Fin 4 → ℕ) : ℝ :=
  (rectangleCount q n w : ℝ)/(rangeLength q w : ℝ)

/-- Unequal full-period side lengths cannot improve this certificate beyond
one fourth of the normalized local density. -/
theorem certificate_le_density (q n : ℕ) (hq : 0 < q) (w : Fin 4 → ℕ) :
    4*rangeCertificate q n w ≤ (fiberCount q n : ℝ)/(q : ℝ)^3 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlen : (0 : ℝ) < rangeLength q w := by
    exact_mod_cast (show 0 < rangeLength q w by unfold rangeLength; omega)
  have hmean := four_mul_prod_le_sum_fourth (fun i ↦ (w i : ℝ))
  have hnonneg : (0 : ℝ) ≤ fiberCount q n := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ ∏ i, (w i : ℝ) := by positivity
  unfold rangeCertificate
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hlen (pow_pos hqR 3)).mpr
  rw [rectangle_count]
  push_cast
  have hlen_eq : (rangeLength q w : ℝ) = (q : ℝ)^3*(∑ i, (w i : ℝ)^4)+1 := by
    simp only [rangeLength,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum,Nat.cast_one]
  rw [hlen_eq]
  nlinarith [mul_le_mul_of_nonneg_left hmean (mul_nonneg hnonneg (pow_nonneg hqR.le 3))]

/-- Uniform divisor-scale control of these certificates for all residues and
all full-period rectangular shapes, without an upper bound on their side lengths. -/
theorem certificate_divisor_scale (N q n : ℕ)
    (hN : 65536 ≤ N) (hq : 0 < q) (hqN : q ≤ N) (w : Fin 4 → ℕ) :
    4*rangeCertificate q n w ≤
      Real.exp (128*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ))) := by
  exact (certificate_le_density q n hq w).trans (normalized_fiber_upper N q n hN hq hqN)


/-- The tight endpoint bound for the quotient of a target in the rectangle. -/
def exactRangeLength (q : ℕ) (w : Fin 4 → ℕ) : ℕ :=
  (∑ i, (w i*q-1)^4)/q+1

/-- Using the tight endpoints instead of the coarse range changes the bound
by at most a fixed factor. Thus the earlier conclusion is not an artifact
of including a loose endpoint. -/
theorem exact_certificate_le_density (q n : ℕ) (hq : 2 ≤ q)
    (w : Fin 4 → ℕ) (hw : ∀ i, 0 < w i) :
    (rectangleCount q n w : ℝ)/(exactRangeLength q w : ℝ) ≤
      4*((fiberCount q n : ℝ)/(q : ℝ)^3) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hlen : (0 : ℝ) < exactRangeLength q w := by
    have hN : 0 < exactRangeLength q w := Nat.succ_pos _
    exact_mod_cast hN
  have hside (i : Fin 4) : ((w i*q : ℕ) : ℝ)^4 ≤
      16*(((w i*q-1 : ℕ) : ℝ)^4) := by
    have htwo : 2 ≤ w i*q := by nlinarith [hw i]
    have hsmall : w i*q ≤ 2*(w i*q-1) := by omega
    have hp := Nat.pow_le_pow_left hsmall 4
    have hpR : ((w i*q : ℕ) : ℝ)^4 ≤ ((2*(w i*q-1) : ℕ) : ℝ)^4 := by
      exact_mod_cast hp
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,show (2 : ℝ)^4=16 by norm_num] using hpR
  have hsum : (q : ℝ)^4*(∑ i, (w i : ℝ)^4) ≤
      16*((∑ i, (w i*q-1)^4 : ℕ) : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hside i)
    simpa only [Nat.cast_mul,mul_pow,← Finset.sum_mul,← Finset.mul_sum,
      Nat.cast_sum,Nat.cast_pow,mul_comm] using hh
  have hquot : ((∑ i, (w i*q-1)^4 : ℕ) : ℝ) ≤
      (q : ℝ)*(exactRangeLength q w : ℝ) := by
    have hh := Nat.div_add_mod (∑ i, (w i*q-1)^4) q
    have hm := Nat.mod_lt (∑ i, (w i*q-1)^4) hq0
    have hN : (∑ i, (w i*q-1)^4) ≤ q*exactRangeLength q w := by
      unfold exactRangeLength
      nlinarith
    exact_mod_cast hN
  have hden : (q : ℝ)^3*(∑ i, (w i : ℝ)^4) ≤ 16*(exactRangeLength q w : ℝ) := by
    apply le_of_mul_le_mul_left (a := (q : ℝ)) ?_ hqR
    nlinarith [hsum.trans (mul_le_mul_of_nonneg_left hquot (by norm_num : (0 : ℝ) ≤ 16))]
  have hmean := four_mul_prod_le_sum_fourth (fun i ↦ (w i : ℝ))
  have hprod : (q : ℝ)^3*(∏ i, (w i : ℝ)) ≤ 4*(exactRangeLength q w : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hmean (pow_nonneg hqR.le 3)]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hlen (pow_pos hqR 3)).mpr
  rw [rectangle_count]
  push_cast
  have hh := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (fiberCount q n) : (0 : ℝ) ≤ _)
  nlinarith

/-- Even the tight-endpoint certificates are bounded uniformly over every
full-period rectangle by a divisor-scale function of the modulus bound. -/
theorem exact_certificate_divisor_scale (N q n : ℕ)
    (hN : 65536 ≤ N) (hq : 2 ≤ q) (hqN : q ≤ N)
    (w : Fin 4 → ℕ) (hw : ∀ i, 0 < w i) :
    (rectangleCount q n w : ℝ)/(exactRangeLength q w : ℝ) ≤
      4*Real.exp (128*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ))) := by
  exact (exact_certificate_le_density q n hq w hw).trans
    (mul_le_mul_of_nonneg_left (normalized_fiber_upper N q n hN (by omega) hqN) (by norm_num))

end
end Erdos322Research.QuarticPeriodicRectangles
