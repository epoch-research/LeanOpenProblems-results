import Submission.LatticeHeightDescent
import Submission.LinearScaleKernelLift
import Submission.PrimitiveKernelCovolume

/-! Monomial recurrence near a full Euclidean lattice, with an exponent
polynomial in the dimension and linear in dyadic accuracy and logarithmic
covolume. The minimum nonzero lattice length is assumed at least one. -/
namespace Erdos3PolynomialDimensionLatticeRecurrence
open Module MeasureTheory Erdos3PrimitiveHeightObstruction Erdos3LatticeHeightDescent
  Erdos3KernelProjectionEstimates Erdos3KernelMonomialLift Erdos3LinearScaleKernelLift
  Erdos3PrimitiveKernelLattice Erdos3PrimitiveKernelCovolume
open scoped Classical
set_option maxHeartbeats 6000000
universe u

private theorem lattice_recurrence_aux (k D H : ℕ) (hH : 16 ≤ H) (hD : D ≤ H) (m : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
      (α : E) (s V : ℕ), finrank ℝ E = m → m ≤ D →
      (∀ x : E, x ∈ L → x ≠ 0 → 1 ≤ ‖x‖) →
      ZLattice.covolume L ≤ (2:ℝ)^V → dualHeight m s ≤ H → V ≤ (3*(D-m)+1)*H →
      ∃ n : ℕ, 0 < n ∧ n ≤ 2^(m*stepHeight k D H) ∧
        ∃ y : E, y ∈ L ∧ ‖((n^(k+1):ℕ):ℝ) • α-y‖ ≤ (1/2:ℝ)^s := by
  induction m with
  | zero =>
    intro E _ _ _ _ _ L _ _ α s V hdim _ _ _ _ _
    letI : Subsingleton E := finrank_zero_iff.mp hdim
    refine ⟨1,by decide,by simp,0,L.zero_mem,?_⟩
    have hα : α = 0 := Subsingleton.elim _ _
    simp [hα]
  | succ m ih =>
    intro E _ _ _ _ _ L _ _ α s V hdim hm hmin hvol hT hV
    let B := stepHeight k D H
    let N := 2^((m+1)*B)
    let W := weylHeight k (m+1) s V
    let U := (m+1)^2+V
    let P := precisionHeight (m+1) s V
    obtain ⟨_,hP,hWB,hstep⟩ := height_controls k D H (m+1) s V hH hD hm hT hV
    by_contra hno
    have havoid : ∀ n : ℕ, 0 < n → n ≤ N → ∀ y : E, y ∈ L →
        (1/2:ℝ)^s < ‖((n^(k+1):ℕ):ℝ) • α-y‖ := by
      intro n hn hnN y hy
      exact lt_of_not_ge (fun hclose ↦ hno ⟨n,hn,hnN,y,hy,hclose⟩)
    have hN : 2^(weylHeight k (finrank ℝ E) s V) ≤ N := by
      rw [hdim]
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      exact hWB.trans (by dsimp only [B]; nlinarith)
    obtain ⟨F,hF,hint,hlower,hupper,v,hvL,hv,q,c,hq,hqbound,happrox⟩ :=
      primitive_height_obstruction L α k s V N hmin hvol hN havoid
    simp only [hdim] at hlower hupper hqbound happrox
    have hFnorm : ‖F‖ ≤ (2:ℝ)^(3*H) := hupper.trans (dyadic_norm_budget _ _ H hT hP)
    let K := kernelLattice L F
    letI : IsZLattice ℝ K := kernelLattice_isZLattice L F hint v hvL hv
    have hdimK : finrank ℝ F.toLinearMap.ker = m := by
      have hh := kernel_finrank F v hv
      rw [hdim] at hh
      omega
    have hminK : ∀ x : F.toLinearMap.ker, x ∈ K → x ≠ 0 → 1 ≤ ‖x‖ := by
      intro x hx hx0
      apply hmin (x : E) hx
      intro hz
      exact hx0 (Subtype.ext hz)
    have hvolK : ZLattice.covolume K ≤ (2:ℝ)^(V+3*H) := by
      calc
        _ = ‖F‖*ZLattice.covolume L := primitive_kernel_covolume L F hF hint v hvL hv
        _ ≤ (2:ℝ)^(3*H)*(2:ℝ)^V := by
          gcongr
          exact (ZLattice.covolume_pos L).le
        _ = _ := by rw [pow_add]; ring
    let β : F.toLinearMap.ker :=
      projectToKernel F (normalVector F) (normalVector_evaluate F hF) (adjustedCoefficient α v q k c)
    obtain ⟨n,hn,hnM,y,hy,hclose⟩ := ih F.toLinearMap.ker K β (s+1) (V+3*H) hdimK (by omega)
      hminK hvolK ((dualHeight_descends m s).trans hT) (covolumeHeight_descends D H m V hm hV)
    let M := 2^(m*B)
    let S := 2^(W+(s+1)+U)
    have hqS : q*S ≤ 2^B := dyadic_stride_budget q W (dualHeight (m+1) s) U P H s k B hqbound hP hstep
    have hscale : q*M*S ≤ N := by
      calc
        _ = (q*S)*M := by ring
        _ ≤ 2^B*2^(m*B) := Nat.mul_le_mul_right M hqS
        _ = N := by dsimp only [N]; rw [← pow_add]; congr 1; ring
    have herror : (2:ℝ)^W ≤ (1/2:ℝ)^(s+1)*‖F‖*(S:ℝ)^(k+1) :=
      dyadic_lift_error_budget W U s k hlower
    have hcloseE : ‖((n^(k+1):ℕ):ℝ) • projectionAlong F (normalVector F)
        (adjustedCoefficient α v q k c)-(y:E)‖ ≤ (1/2:ℝ)^(s+1) := hclose
    obtain ⟨r,hr,hrN,w,hw,hrclose⟩ := kernel_lift_at_linear_scale L F hF α v hvL hv
      q k M n S N c hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) hn hnM hscale
      (by positivity : (0:ℝ) ≤ (2:ℝ)^W) (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(s+1))
      herror happrox (y:E) hy hcloseE
    apply hno
    refine ⟨r,hr,hrN,w,hw,?_⟩
    calc
      _ ≤ (1/2:ℝ)^(s+1)+(1/2:ℝ)^(s+1) := hrclose
      _ = _ := by rw [pow_succ]; ring

def recurrenceHeight (d s V : ℕ) : ℕ := d^2+2*d+s+V+32

/-- A polynomial-dimension quantitative recurrence theorem for lattices. -/
theorem quantitative_lattice_monomial_recurrence {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (α : E) (k s V : ℕ)
    (hmin : ∀ x : E, x ∈ L → x ≠ 0 → 1 ≤ ‖x‖)
    (hvol : ZLattice.covolume L ≤ (2:ℝ)^V) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ 2^((finrank ℝ E)*stepHeight k (finrank ℝ E) (recurrenceHeight (finrank ℝ E) s V)) ∧
      ∃ y : E, y ∈ L ∧ ‖((n^(k+1):ℕ):ℝ) • α-y‖ ≤ (1/2:ℝ)^s := by
  let d := finrank ℝ E
  let H := recurrenceHeight d s V
  apply lattice_recurrence_aux k d H (by dsimp only [H,recurrenceHeight]; omega)
    (by dsimp only [H,recurrenceHeight]; omega) d E L α s V rfl le_rfl hmin hvol
  · dsimp only [H,recurrenceHeight,dualHeight]
    omega
  · simp only [Nat.sub_self,mul_zero,zero_add,one_mul]
    dsimp only [H,recurrenceHeight]
    omega

#print axioms quantitative_lattice_monomial_recurrence
end Erdos3PolynomialDimensionLatticeRecurrence
