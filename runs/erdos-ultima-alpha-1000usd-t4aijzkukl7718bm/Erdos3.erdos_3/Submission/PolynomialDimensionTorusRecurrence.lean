import Submission.PolynomialDimensionLatticeRecurrence

/-! Simultaneous monomial recurrence of real and unit-circle tuples with a
polynomial-dimensional exponent. The standard lattice has minimum one and
covolume one. -/
namespace Erdos3PolynomialDimensionTorusRecurrence
open Finset Module MeasureTheory Erdos3PrimitiveKernelCovolume
  Erdos3PolynomialDimensionLatticeRecurrence Erdos3LatticeHeightDescent
  Erdos3CircleIntegerApproximation
open scoped BigOperators RealInnerProductSpace Classical
set_option maxHeartbeats 4000000

section Orthonormal
variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma orthonormal_coordinate_le_norm (o : OrthonormalBasis I ℝ E) (x : E) (i : I) :
    |o.toBasis.repr x i| ≤ ‖x‖ := by
  rw [OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
  simpa only [o.orthonormal.norm_eq_one i,one_mul] using abs_real_inner_le_norm (o i) x

lemma orthonormal_lattice_minimum (o : OrthonormalBasis I ℝ E) (x : E)
    (hx : x ∈ Submodule.span ℤ (Set.range o.toBasis)) (hx0 : x ≠ 0) : 1 ≤ ‖x‖ := by
  have hn : ∃ i, o.toBasis.repr x i ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hx0
    apply o.toBasis.ext_elem
    intro i
    simpa only [map_zero,Finsupp.zero_apply] using hh i
  obtain ⟨i,hi⟩ := hn
  obtain ⟨c,hc⟩ := (o.toBasis.mem_span_iff_repr_mem ℤ x).mp hx i
  have hc0 : c ≠ 0 := by intro hz; simp [← hc,hz] at hi
  have h1 : (1:ℝ) ≤ |o.toBasis.repr x i| := by
    rw [← hc]
    change (1:ℝ) ≤ |(c:ℝ)|
    exact_mod_cast Int.one_le_abs hc0
  exact h1.trans (orthonormal_coordinate_le_norm o x i)

lemma orthonormal_lattice_covolume (o : OrthonormalBasis I ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range o.toBasis)) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain o.toBasis volume)]
  exact orthonormal_fundamental_volume o

theorem orthonormal_monomial_recurrence (o : OrthonormalBasis I ℝ E) (α : E) (k s : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ 2^((Fintype.card I)*stepHeight k (Fintype.card I) (recurrenceHeight (Fintype.card I) s 0)) ∧
      ∃ c : I → ℤ, ∀ i, |((n^(k+1):ℕ):ℝ)*(o.toBasis.repr α i)-(c i:ℝ)| ≤ (1/2:ℝ)^s := by
  let L := Submodule.span ℤ (Set.range o.toBasis)
  have hdim : finrank ℝ E = Fintype.card I := finrank_eq_card_basis o.toBasis
  obtain ⟨n,hn,hnb,y,hy,hclose⟩ := quantitative_lattice_monomial_recurrence L α k s 0
    (fun x hx hx0 ↦ orthonormal_lattice_minimum o x hx hx0)
    (by rw [orthonormal_lattice_covolume]; simp)
  have hyint : ∀ i, ∃ c : ℤ, (c:ℝ) = o.toBasis.repr y i :=
    (o.toBasis.mem_span_iff_repr_mem ℤ y).mp hy
  choose c hc using hyint
  refine ⟨n,hn,by simpa only [hdim] using hnb,c,?_⟩
  intro i
  have hh := (orthonormal_coordinate_le_norm o (((n^(k+1):ℕ):ℝ) • α-y) i).trans hclose
  simpa only [map_sub,map_smul,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,← hc] using hh
end Orthonormal

/-- Simultaneous approximation of a real tuple by integers at a monomial time. -/
theorem simultaneous_real_monomial_recurrence {I : Type*} [Fintype I]
    (α : I → ℝ) (k s : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ 2^((Fintype.card I)*stepHeight k (Fintype.card I) (recurrenceHeight (Fintype.card I) s 0)) ∧
      ∃ c : I → ℤ, ∀ i, |((n^(k+1):ℕ):ℝ)*α i-(c i:ℝ)| ≤ (1/2:ℝ)^s := by
  let o := EuclideanSpace.basisFun I ℝ
  let β : EuclideanSpace ℝ I := WithLp.toLp 2 α
  obtain ⟨n,hn,hnb,c,hc⟩ := orthonormal_monomial_recurrence o β k s
  refine ⟨n,hn,hnb,c,?_⟩
  intro i
  simpa only [o,OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr] using hc i

def tupleRecurrenceConstant (k m : ℕ) : ℕ :=
  m*((2*baseWeylCost k m+6*m+10)*(m^2+2*m+36)+(k+1).factorial)

lemma tuple_exponent_bound (k m s : ℕ) :
    m*stepHeight k m (recurrenceHeight m (s+3) 0) ≤ tupleRecurrenceConstant k m*(s+1) := by
  unfold stepHeight recurrenceHeight tupleRecurrenceConstant
  let A := 2*baseWeylCost k m+6*m+10
  have hinner : m^2+2*m+(s+3)+0+32 ≤ (m^2+2*m+36)*(s+1) := by nlinarith
  have hh := Nat.mul_le_mul_left A hinner
  have hf : (k+1).factorial ≤ (k+1).factorial*(s+1) := by nlinarith
  change m*(A*(m^2+2*m+(s+3)+0+32)+(k+1).factorial) ≤
    m*(A*(m^2+2*m+36)+(k+1).factorial)*(s+1)
  nlinarith only [Nat.mul_le_mul_left m (Nat.add_le_add hh hf)]

/-- All coordinates recur at the same monomial time. For fixed degree, the
constant is polynomial, not exponential, in the tuple length. -/
theorem simultaneous_unit_monomial_recurrence {I : Type*} [Fintype I]
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (k s : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2^(tupleRecurrenceConstant k (Fintype.card I)*(s+1)) ∧
      ∀ i, ‖(v i)^(n^(k+1))-1‖ ≤ (1/2:ℝ)^s := by
  obtain ⟨n,hn,hnb,c,hc⟩ := simultaneous_real_monomial_recurrence (fun i ↦ unitAngle (v i)) k (s+3)
  refine ⟨n,hn,hnb.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (tuple_exponent_bound k _ s)),?_⟩
  intro i
  calc
    _ = ‖ephase (((n^(k+1):ℕ):ℝ)*unitAngle (v i))-1‖ := by rw [← ephase_pow,ephase_unitAngle _ (hv i)]
    _ ≤ 8*|((n^(k+1):ℕ):ℝ)*unitAngle (v i)-(c i:ℝ)| := ephase_near_integer _ _
    _ ≤ 8*(1/2:ℝ)^(s+3) := mul_le_mul_of_nonneg_left (hc i) (by norm_num)
    _ = _ := by rw [pow_add]; norm_num; ring

#print axioms simultaneous_unit_monomial_recurrence
end Erdos3PolynomialDimensionTorusRecurrence
