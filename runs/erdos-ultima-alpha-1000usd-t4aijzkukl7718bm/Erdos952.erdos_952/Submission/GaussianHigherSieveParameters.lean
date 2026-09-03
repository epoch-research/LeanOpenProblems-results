import Submission.GaussianHigherOptimizedSieve

/-! Explicit choice of smoothing order. Moduli of norm <= A with 16*A<=R
have a geometric error whose polynomial prefactor is controlled uniformly
in the polynomial. The main Selberg denominator is still not estimated. -/
namespace Erdos952Investigation.GaussianHigherSieveParameters
open GaussianIdealBoxCounts GaussianHigherOptimizedSieve
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

lemma finite_norm_card_le_square (D : Finset GaussianInt) (A R : ℕ)
    (hlevel : ∀ d ∈ D, d.norm.natAbs ≤ A) (hR : 2*A+1 ≤ R) : D.card ≤ R^2 := by
  let a : GaussianInt := ⟨-(A : ℤ),-(A : ℤ)⟩
  have hb (d : D) : InBox a R d.val := by
    have hn : d.val.norm ≤ (A : ℤ) := by
      have hh : (d.val.norm.natAbs : ℤ) ≤ A := by exact_mod_cast hlevel d.val d.property
      simpa only [Int.natCast_natAbs,abs_of_nonneg (GaussianInt.norm_nonneg _)] using hh
    rw [gaussian_norm_sq] at hn
    have hr := Int.le_self_sq d.val.re
    have hr' := Int.le_self_sq (-d.val.re)
    have hi := Int.le_self_sq d.val.im
    have hi' := Int.le_self_sq (-d.val.im)
    have hR' : 2*(A : ℤ)+1 ≤ R := by exact_mod_cast hR
    dsimp only [InBox,a]
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg d.val.re,sq_nonneg d.val.im]
  let f : D → Box a R := fun d => ⟨d.val,hb d⟩
  have hf : Function.Injective f := by
    intro d e he
    exact Subtype.ext (congrArg (fun t : Box a R => t.val) he)
  have hh := Nat.card_le_card_of_injective f hf
  have hDcard : Nat.card D = D.card := by simp
  rwa [hDcard,box_card] at hh

lemma sieve_support_card_le (D : Finset GaussianInt) (hD : 1 ∈ D) (A R : ℕ)
    (hlevel : ∀ d ∈ D, d.norm.natAbs ≤ A) (hAR : 16*A ≤ R) : D.card ≤ R^2 := by
  have hA : 1 ≤ A := by simpa using hlevel 1 hD
  exact finite_norm_card_le_square D A R hlevel (by omega)

/-- With R<=2^m, order n=4m+k makes the whole error at most 4^(-k)/16.
The bound includes the number of moduli and both weight factors. -/
theorem dyadic_sieveError_le (D : Finset GaussianInt) (hD : 1 ∈ D) (A R m k : ℕ)
    (hlevel : ∀ d ∈ D, d.norm.natAbs ≤ A) (hAR : 16*A ≤ R) (hRm : R ≤ 2^m) :
    sieveError D R (4*m+k) A ≤ (1/2 : ℝ)^(2*k)/16 := by
  have hA : 1 ≤ A := by simpa using hlevel 1 hD
  have hR : 0 < R := by omega
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hAR' : (16 : ℝ)*(A : ℝ) ≤ R := by exact_mod_cast hAR
  have hAl : (A : ℝ) ≤ R := by exact_mod_cast (show A ≤ R by omega)
  have hc : (D.card : ℝ) ≤ (R : ℝ)^2 := by exact_mod_cast sieve_support_card_le D hD A R hlevel hAR
  have hκ : 8*(A : ℝ)/(R : ℝ) ≤ 1/2 := (div_le_iff₀ hRp).mpr (by linarith)
  have hpref : (D.card : ℝ)^2*(A : ℝ)^2*(R : ℝ)^2 ≤ (R : ℝ)^8 := by
    calc
      _ ≤ ((R : ℝ)^2)^2*(R : ℝ)^2*(R : ℝ)^2 := by gcongr
      _ = _ := by ring
  have hpow : (R : ℝ)^8 ≤ (2 : ℝ)^(8*m) := by
    have hh : (R : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast hRm
    calc
      _ ≤ ((2 : ℝ)^m)^8 := pow_le_pow_left₀ (Nat.cast_nonneg _) hh _
      _ = _ := by rw [← pow_mul,Nat.mul_comm]
  have he : (2 : ℝ)^(8*m)*(1/2 : ℝ)^(2*((4*m+k)+2)) = (1/2 : ℝ)^(2*k)/16 := by
    rw [show 2*((4*m+k)+2) = 8*m+2*k+4 by omega,pow_add,pow_add]
    have hcancel : (2 : ℝ)^(8*m)*(1/2 : ℝ)^(8*m) = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = ((2 : ℝ)^(8*m)*(1/2 : ℝ)^(8*m))*(1/2 : ℝ)^(2*k)*(1/2 : ℝ)^4 := by ring
      _ = _ := by rw [hcancel]; norm_num; ring
  unfold sieveError
  exact (mul_le_mul (hpref.trans hpow) (pow_le_pow_left₀ (by positivity) hκ _)
    (by positivity) (by positivity)).trans_eq he

#print axioms finite_norm_card_le_square
#print axioms dyadic_sieveError_le
end
end Erdos952Investigation.GaussianHigherSieveParameters
