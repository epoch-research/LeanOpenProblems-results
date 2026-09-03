import Submission.LatticeCoordinateBounds
import Submission.PrimitiveLatticeFunctional

/-! A primitive lattice recurrence obstruction with explicit dimension, accuracy,
and logarithmic covolume costs. The functional's norm and the integer arithmetic
denominator remain separate. -/
namespace Erdos3PrimitiveHeightObstruction
open Finset Module Erdos3LatticePhaseCoordinates Erdos3LatticeRecurrenceObstruction
  Erdos3LatticePrecisionBudget Erdos3LatticeCoordinateBounds
  Erdos3AnisotropicAvoidanceParameters Erdos3SharpHigherPhaseWeylInverse
  Erdos3PrimitiveLatticeFunctional
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

def precisionHeight (m s V : ℕ) : ℕ := basisPrecisionBudget m s (m^2+V)
def dualHeight (m s : ℕ) : ℕ := s+m^2+2*m+7
def weylHeight (k m s V : ℕ) : ℕ := sharpWeylConstant k*(2*m+9)*precisionHeight m s V

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma height_dual_norm_budget {m : ℕ} (b : Basis (Fin m) ℝ E) (t : Fin m → ℕ) (s P : ℕ)
    (hmass : precisionMass t ≤ P)
    (hscale : ∀ i, (2:ℝ)^(t i) ≤ (2:ℝ)^(s+m+1)*‖b i‖)
    (hcondition : ∀ i, ‖b i‖*‖coordinate b i‖ ≤ (2:ℝ)^(m^2)) :
    (kernelPower t:ℝ)*(∑ i, (2:ℝ)^(t i+2)*‖coordinate b i‖) ≤
      (2:ℝ)^(dualHeight m s)*(P:ℝ)^2 := by
  have hK : (kernelPower t:ℝ) ≤ 16*(P:ℝ)^2 := by
    exact_mod_cast (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hmass 2))
  have hm : (m:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  calc
    _ ≤ 4*(kernelPower t:ℝ)*(m:ℝ)*(2:ℝ)^(s+m+1)*(2:ℝ)^(m^2) := by
      simpa only [Fintype.card_fin] using dual_norm_budget b t (by positivity) hscale hcondition
    _ ≤ 4*(16*(P:ℝ)^2)*(2:ℝ)^m*(2:ℝ)^(s+m+1)*(2:ℝ)^(m^2) := by gcongr
    _ = (2:ℝ)^(2+4+m+(s+m+1)+m^2)*(P:ℝ)^2 := by
      simp only [pow_add]
      norm_num only [pow_one]
      ring
    _ = _ := by rw [show 2+4+m+(s+m+1)+m^2 = dualHeight m s by unfold dualHeight; omega]

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Failure of monomial recurrence yields a primitive functional. Its norm is
polynomial in the logarithmic covolume parameter; its arithmetic denominator
may be exponential in that parameter. -/
theorem primitive_height_obstruction (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (α : E) (k s V N : ℕ)
    (hmin : ∀ x : E, x ∈ L → x ≠ 0 → 1 ≤ ‖x‖)
    (hvol : ZLattice.covolume L ≤ (2:ℝ)^V)
    (hN : 2^(weylHeight k (finrank ℝ E) s V) ≤ N)
    (havoid : ∀ n : ℕ, 0 < n → n ≤ N → ∀ y : E, y ∈ L →
      (1/2:ℝ)^s < ‖((n^(k+1):ℕ):ℝ) • α-y‖) :
    ∃ F : E →L[ℝ] ℝ, F ≠ 0 ∧
      (∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c:ℝ)) ∧
      (1/2:ℝ)^((finrank ℝ E)^2+V) ≤ ‖F‖ ∧
      ‖F‖ ≤ (2:ℝ)^(dualHeight (finrank ℝ E) s)*(precisionHeight (finrank ℝ E) s V:ℝ)^2 ∧
      ∃ v : E, v ∈ L ∧ F v = 1 ∧ ∃ q : ℕ, ∃ c : ℤ, 0 < q ∧
      q ≤ 2^(weylHeight k (finrank ℝ E) s V+(k+1).factorial+
        dualHeight (finrank ℝ E) s+((finrank ℝ E)^2+V))*(precisionHeight (finrank ℝ E) s V)^2 ∧
      |(q:ℝ)*F α-(c:ℝ)| ≤ (2:ℝ)^(weylHeight k (finrank ℝ E) s V)/(N:ℝ)^(k+1) := by
  let m := finrank ℝ E
  let P := precisionHeight m s V
  let W := weylHeight k m s V
  let T := dualHeight m s
  let U := m^2+V
  obtain ⟨b,t,hspan,hbmin,hbprod,hcondition,hmass,hscale,hsmall⟩ :=
    lattice_precision_parameters L s V hmin hvol
  have hW : sharpWeylConstant k*(frequencyMeanExponent t+1) ≤ W := by
    have hfreq : frequencyMeanExponent t+1 ≤ (2*m+9)*P := by
      have hh := meanExponent_le_mass t
      simp only [Fintype.card_fin] at hh
      exact hh.trans (Nat.mul_le_mul_left (2*m+9) hmass)
    simpa only [W,weylHeight,P,Nat.mul_assoc] using Nat.mul_le_mul_left (sharpWeylConstant k) hfreq
  have hN' : 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)) ≤ N :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hW).trans hN
  obtain ⟨F,hF,hint,hFnorm,q,c,hq,hqbound,happrox⟩ := lattice_recurrence_obstruction b α k t N
    (η := (1/2:ℝ)^s) (by
      have hp : 0 ≤ (1/2:ℝ)^s := by positivity
      linarith only [hsmall,hp])
    hN' (by simpa only [hspan] using havoid)
  have hFnorm' : ‖F‖ ≤ (2:ℝ)^T*(P:ℝ)^2 :=
    hFnorm.trans (height_dual_norm_budget b t s P hmass hscale hcondition)
  have hqbound' : q ≤ 2^(W+(k+1).factorial) :=
    hqbound.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.add_le_add_right hW _))
  have happrox' : |(q:ℝ)*F α-(c:ℝ)| ≤ (2:ℝ)^W/(N:ℝ)^(k+1) := by
    exact happrox.trans (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hW) (by positivity))
  obtain ⟨g,F₀,v,hg,hsplit,hvL,hv,hint₀,hnorm₀,i,hgi⟩ := primitive_lattice_functional b F hF hint
  have hF₀ : F₀ ≠ 0 := by intro hz; simp [hz] at hv
  have hlower : (1/2:ℝ)^U ≤ ‖F₀‖ :=
    integral_dual_norm_lower_of_product b hbmin U hbprod F₀ hF₀ hint₀
  have hupper : ‖F₀‖ ≤ (2:ℝ)^T*(P:ℝ)^2 := hnorm₀.trans hFnorm'
  have hbi : ‖b i‖ ≤ (2:ℝ)^U := (length_le_product b hbmin i).trans hbprod
  have hgbound : (g:ℝ) ≤ (2:ℝ)^(T+U)*(P:ℝ)^2 := by
    calc
      _ ≤ |F (b i)| := hgi
      _ ≤ ‖F‖*‖b i‖ := by simpa only [Real.norm_eq_abs] using F.le_opNorm (b i)
      _ ≤ ((2:ℝ)^T*(P:ℝ)^2)*(2:ℝ)^U := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hgnat : g ≤ 2^(T+U)*P^2 := by exact_mod_cast hgbound
  have hqg : q*g ≤ 2^(W+(k+1).factorial+T+U)*P^2 := by
    calc
      _ ≤ 2^(W+(k+1).factorial)*(2^(T+U)*P^2) := Nat.mul_le_mul hqbound' hgnat
      _ = 2^((W+(k+1).factorial)+(T+U))*P^2 := by rw [pow_add]; ring
      _ = _ := by simp only [Nat.add_assoc]
  refine ⟨F₀,hF₀,by simpa only [hspan] using hint₀,hlower,hupper,v,?_,hv,q*g,c,
    Nat.mul_pos hq hg,hqg,?_⟩
  · simpa only [hspan] using hvL
  · simpa only [hsplit,ContinuousLinearMap.smul_apply,smul_eq_mul,Nat.cast_mul,mul_assoc] using happrox'

#print axioms primitive_height_obstruction
end Hilbert
end Erdos3PrimitiveHeightObstruction
