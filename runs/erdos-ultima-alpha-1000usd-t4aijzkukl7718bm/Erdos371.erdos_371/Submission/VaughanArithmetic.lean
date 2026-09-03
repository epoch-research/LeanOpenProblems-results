import Submission.PrimePowerKernelReplacement

/-! A truncated convolution identity, with its signed terms retained. -/
namespace Erdos371
open Finset
open scoped ArithmeticFunction

noncomputable def arithmeticTruncate (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤U then f n else 0,by simp⟩

@[simp] lemma arithmeticTruncate_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticTruncate U f n = if n≤U then f n else 0 := rfl

/-- Vaughan's identity as an identity of arithmetic functions. -/
theorem vonMangoldt_truncated_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      arithmeticTruncate V ArithmeticFunction.vonMangoldt +
      arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.log -
      arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticTruncate V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta +
      ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)-arithmeticTruncate U ArithmeticFunction.moebius)*
        (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt)*
          ArithmeticFunction.zeta := by
  have he : (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.vonMangoldt*
      ArithmeticFunction.zeta = ArithmeticFunction.vonMangoldt := by
    rw [mul_right_comm,ArithmeticFunction.coe_moebius_mul_coe_zeta,one_mul]
  have hv : (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticTruncate V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta =
      arithmeticTruncate V ArithmeticFunction.vonMangoldt := by
    rw [mul_right_comm,ArithmeticFunction.coe_moebius_mul_coe_zeta,one_mul]
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  linear_combination -he + hv

lemma truncated_convolution_apply (U q : ℕ) (f g : ArithmeticFunction ℝ) (hq : q≠0) :
    (arithmeticTruncate U f*g) q =
      ∑ u ∈ (Icc 1 U).filter (fun u => u ∣ q), f u*g (q/u) := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun u v => arithmeticTruncate U f u * g v)]
  simp only [arithmeticTruncate_apply,ite_mul,zero_mul,← sum_filter]
  apply sum_congr _ (fun u _ => rfl)
  ext u
  simp only [mem_filter,Nat.mem_divisors,mem_Icc]
  constructor
  · rintro ⟨⟨hd,_⟩,hu⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hq),hu⟩,hd⟩
  · rintro ⟨⟨_,hu⟩,hd⟩
    exact ⟨⟨hd,hq⟩,hu⟩

lemma sum_interval_multiples (C X u : ℕ) (hu : 0 < u) (H : ℕ → ℝ) :
    (∑ q ∈ (Ioc C X).filter (fun q => u∣q), H q) =
      ∑ v ∈ Ioc (C/u) (X/u), H (u*v) := by
  symm
  apply sum_bij (fun v _ => u*v)
  · intro v hv
    obtain ⟨hvC,hvX⟩ := mem_Ioc.mp hv
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨by simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hu).mp hvC,
        by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hu).mp hvX⟩,dvd_mul_right u v⟩
  · intro v hv w hw he
    exact Nat.eq_of_mul_eq_mul_left hu he
  · intro q hq
    obtain ⟨hq,hud⟩ := mem_filter.mp hq
    obtain ⟨hC,hX⟩ := mem_Ioc.mp hq
    have he := Nat.mul_div_cancel' hud
    refine ⟨q/u,mem_Ioc.mpr ⟨?_,Nat.div_le_div_right hX⟩,he⟩
    apply (Nat.div_lt_iff_lt_mul hu).mpr
    simpa only [mul_comm,he] using hC
  · intro v hv
    rfl

/-- Weighted summation of a truncated convolution, with the original
hyperbolic endpoints retained exactly. -/
theorem truncated_convolution_interval (U C X : ℕ) (f g : ArithmeticFunction ℝ) (H : ℕ → ℝ) :
    (∑ q ∈ Ioc C X, (arithmeticTruncate U f*g) q*H q) =
      ∑ u ∈ Icc 1 U, f u * ∑ v ∈ Ioc (C/u) (X/u), g v*H (u*v) := by
  have he (q : ℕ) (hq : q ∈ Ioc C X) :
      (arithmeticTruncate U f*g) q*H q =
        ∑ u ∈ Icc 1 U, if u∣q then f u*g (q/u)*H q else 0 := by
    rw [truncated_convolution_apply U q f g (by have := mem_Ioc.mp hq; omega),sum_mul,sum_filter]
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [← sum_filter,sum_interval_multiples C X u (mem_Icc.mp hu).1,mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [Nat.mul_div_cancel_left v (mem_Icc.mp hu).1,mul_assoc]

lemma arithmeticTruncate_convolution_support (U V : ℕ) (f g : ArithmeticFunction ℝ) :
    arithmeticTruncate (U*V) (arithmeticTruncate U f*arithmeticTruncate V g) =
      arithmeticTruncate U f*arithmeticTruncate V g := by
  ext q
  rw [arithmeticTruncate_apply]
  split_ifs with hq
  · rfl
  · symm
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro uv huv
    have he := (Nat.mem_divisorsAntidiagonal.mp huv).1
    by_cases hu : uv.1≤U
    · have hv : ¬uv.2≤V := by
        intro hv
        have hprod := Nat.mul_le_mul hu hv
        rw [he] at hprod
        exact hq hprod
      simp [hv]
    · simp [hu]

#print axioms vonMangoldt_truncated_identity
#print axioms truncated_convolution_interval
end Erdos371
