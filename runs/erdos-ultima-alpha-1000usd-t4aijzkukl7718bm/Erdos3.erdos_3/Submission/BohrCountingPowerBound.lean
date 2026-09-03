import Submission.BohrTopDegreeCounting

/-! Explicit density/rank dependence of the robust mixed-factor counting
bound. It is independent of all ambient finite-group cardinalities, but the
lower character rank and Lipschitz constant are still structural parameters. -/
namespace Erdos3BohrCountingPowerBound
open Finset Erdos3BohrTopDegreeCounting Erdos3TopDegreeFiberCounting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

lemma returnMesh_scaled (m : ℕ) (A : NNReal) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2*(returnMesh m A δ : ℝ)+1)*δ^(2*m+2) ≤ 8*(2*m+2 : ℕ)*(A : ℝ)+5 := by
  let x : ℝ := (4*(2*m+2 : ℕ)*(A : ℝ))/(δ^(2*m+2))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hc := Nat.ceil_lt_add_one hx
  have hq : (returnMesh m A δ : ℝ) ≤ x+2 := by
    change ((⌈x⌉₊+1 : ℕ) : ℝ) ≤ x+2
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  have hp : 0 < δ^(2*m+2) := pow_pos hδ _
  have hp1 : δ^(2*m+2) ≤ 1 := pow_le_one₀ hδ.le hδ1
  have he : x*δ^(2*m+2) = 4*(2*m+2 : ℕ)*(A : ℝ) := by
    dsimp [x]
    exact div_mul_cancel₀ _ hp.ne'
  have hh := mul_le_mul_of_nonneg_right hq hp.le
  nlinarith only [hh,he,hp1]

lemma power_count_comparison (k e : ℕ) {δ b c : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (hc : 0 < c) (hscale : b*δ^k ≤ c) :
    δ^(k*(e+1))/(2*c^e) ≤ δ^k/(2*b^e) := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*c^e) (by positivity : (0 : ℝ) < 2*b^e)).mpr
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ b*δ^k) hscale e
  rw [mul_pow] at hp
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*δ^k)
  rw [pow_mul,pow_succ]
  convert hh using 1 <;> ring

variable {H Q C I : Type*} [AddCommGroup H] [Fintype H]
variable [AddCommGroup Q] [Fintype Q] [AddCommGroup C] [Fintype C] [Fintype I]

/-- For k=2m+2 and lower character rank r, the model count is at least
 delta^(k*(2*r*k+1)) / (2*(8*k*A+5)^(2*r*k)).
The top-degree rank and all finite-group cardinalities have disappeared. -/
theorem bohr_fibered_power_bound (m : ℕ) (χ : I → AddChar H ℂ) (L : Fin (2*m+2) → C →+ H)
    (f : H → Q → ℝ) (hf : ∀ a z, 0 ≤ f a z ∧ f a z ≤ 1) (A : NNReal)
    (hlip : ∀ a b z, |f a z-f b z| ≤ (A : ℝ)*‖(fun i ↦ χ i a)-(fun i ↦ χ i b)‖)
    (hδ : 0 < 𝔼 a : H, 𝔼 z : Q, f a z) :
    let δ := 𝔼 a : H, 𝔼 z : Q, f a z
    δ^((2*m+2)*(2*(Fintype.card I*(2*m+2))+1))/
      (2*(8*(2*m+2 : ℕ)*(A : ℝ)+5)^(2*(Fintype.card I*(2*m+2)))) ≤
      fiberedEvenCount m (fun a c j ↦ a+L j c) f := by
  dsimp only
  let δ := 𝔼 a : H, 𝔼 z : Q, f a z
  have hδ1 : δ ≤ 1 := by
    have ha (a : H) : (𝔼 z : Q, f a z) ≤ 1 := by
      calc
        _ ≤ 𝔼 _z : Q, (1 : ℝ) := expect_le_expect (fun z _ ↦ (hf a z).2)
        _ = _ := Fintype.expect_const _
    calc
      _ ≤ 𝔼 _a : H, (1 : ℝ) := expect_le_expect (fun a _ ↦ ha a)
      _ = _ := Fintype.expect_const _
  have hscale := returnMesh_scaled m A hδ hδ1
  have hcmp := power_count_comparison (2*m+2) (2*(Fintype.card I*(2*m+2))) hδ
    (by positivity : (0 : ℝ) < 2*(returnMesh m A δ : ℝ)+1)
    (by positivity : (0 : ℝ) < 8*(2*m+2 : ℕ)*(A : ℝ)+5) hscale
  exact hcmp.trans (explicit_bohr_fibered_count m χ L f hf A hlip hδ)

#print axioms returnMesh_scaled
#print axioms bohr_fibered_power_bound
end Erdos3BohrCountingPowerBound
