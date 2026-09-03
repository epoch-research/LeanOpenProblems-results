import Submission.VaughanLongCoefficients
import Submission.RoughPrimePart

/-! Exact signed annihilation of a class of long Vaughan coefficients.
The conclusion concerns coefficients, not the size of the surviving kernel. -/
namespace Erdos371
open Finset
set_option autoImplicit false

lemma coprime_of_small_rough (T d r : ℕ) (hd : 0 < d) (hdT : d ≤ T)
    (hr : ∀ p, p.Prime → p ∣ r → T < p) : d.Coprime r := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpr
  have hpd' := Nat.le_of_dvd hd hpd
  have hpT := hr p hp hpr
  omega

lemma small_divisor_of_mul_rough (T m r d : ℕ) (hd : 0 < d) (hdT : d ≤ T)
    (hr : ∀ p, p.Prime → p ∣ r → T < p) (hdiv : d ∣ m*r) : d ∣ m :=
  (coprime_of_small_rough T d r hd hdT hr).dvd_mul_right.mp hdiv

lemma truncated_moebius_zeta_zero_of_divisors (T m n : ℕ) (hm : 1 < m) (hmT : m ≤ T)
    (hmn : m ∣ n) (hproj : ∀ d, d ∣ n → 0 < d → d ≤ T → d ∣ m) :
    (arithmeticTruncate T (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      ArithmeticFunction.zeta) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [arithmeticTruncate_apply,← sum_filter]
  by_cases hn : n = 0
  · simp [hn]
  have he : n.divisors.filter (fun d => d ≤ T) = m.divisors := by
    ext d
    simp only [mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,_⟩,hdT⟩
      exact ⟨hproj d hd (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)) hdT,by omega⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨hd.trans hmn,hn⟩,(Nat.le_of_dvd (show 0 < m by omega) hd).trans hmT⟩
  rw [he]
  have hz := congrArg (fun f : ArithmeticFunction ℝ => f m)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  dsimp only at hz
  rw [ArithmeticFunction.coe_mul_zeta_apply] at hz
  simpa [ArithmeticFunction.one_apply,show m ≠ 1 by omega] using hz

lemma vaughanLongFunction_moebius_zeta (U V : ℕ) :
    vaughanLongFunction U V =
      (1-arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        ArithmeticFunction.zeta)*
      (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) := by
  rw [vaughanLongFunction,mul_right_comm,sub_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- The whole signed coefficient vanishes, without squarefreeness assumptions.
Every nonzero long Mangoldt factor lies in the rough part. -/
theorem vaughanLongFunction_small_times_rough (T m r : ℕ)
    (hm : 1 < m) (hmT : m ≤ T)
    (hr : ∀ p, p.Prime → p ∣ r → T < p) :
    vaughanLongFunction T T (m*r) = 0 := by
  rw [vaughanLongFunction_moebius_zeta,ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro uv huv
  obtain ⟨he,hne⟩ := Nat.mem_divisorsAntidiagonal.mp huv
  have hm0 : 0 < m := by omega
  have hvq : uv.2 ∣ m*r := he ▸ dvd_mul_left uv.2 uv.1
  by_cases hvT : uv.2 ≤ T
  · change _ * (ArithmeticFunction.vonMangoldt uv.2 -
      (if uv.2≤T then ArithmeticFunction.vonMangoldt uv.2 else 0)) = _
    simp [hvT]
  by_cases hvL : ArithmeticFunction.vonMangoldt uv.2 = 0
  · change _ * (ArithmeticFunction.vonMangoldt uv.2 -
      (if uv.2≤T then ArithmeticFunction.vonMangoldt uv.2 else 0)) = _
    simp [hvL]
  have hmr : m.Coprime r := coprime_of_small_rough T m r hm0 hmT hr
  have hpow : IsPrimePow uv.2 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hvL
  have hvr : uv.2 ∣ r := (hmr.isPrimePow_dvd_mul hpow).mp hvq |>.resolve_left (by
    intro hvm
    exact hvT ((Nat.le_of_dvd hm0 hvm).trans hmT))
  have hmvu : m.Coprime uv.2 := hmr.of_dvd_right hvr
  have hmu : m ∣ uv.1 := hmvu.dvd_mul_right.mp (he.symm ▸ dvd_mul_right m r)
  have hz := truncated_moebius_zeta_zero_of_divisors T m uv.1 hm hmT hmu
    (fun d hdu hd hdT => small_divisor_of_mul_rough T m r d hd hdT hr
      (hdu.trans (he ▸ dvd_mul_right uv.1 uv.2)))
  have hu1 : uv.1 ≠ 1 := by
    intro hu
    have : m ∣ 1 := hu ▸ hmu
    have := Nat.dvd_one.mp this
    omega
  change ((1 : ArithmeticFunction ℝ) uv.1 -
    (arithmeticTruncate T (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      ArithmeticFunction.zeta) uv.1) * _ = _
  simp [hz,hu1]

/-- If the canonical small-prime part is nontrivial but no larger than T,
the long coefficient is exactly zero. -/
theorem vaughanLongFunction_smoothPart_zero (T q : ℕ)
    (hm : 1 < smoothPrimePart T q) (hmT : smoothPrimePart T q ≤ T) :
    vaughanLongFunction T T q = 0 := by
  by_cases hq : q = 0
  · simp [hq]
  have he : smoothPrimePart T q * roughPrimePart T q = q := by
    rw [mul_comm,roughPrimePart_mul_smoothPrimePart T q hq]
  rw [← he]
  exact vaughanLongFunction_small_times_rough T _ _ hm hmT
    (fun p hp hpr => roughPrimePart_prime_large T q p hp hpr)

#print axioms vaughanLongFunction_smoothPart_zero
end Erdos371
