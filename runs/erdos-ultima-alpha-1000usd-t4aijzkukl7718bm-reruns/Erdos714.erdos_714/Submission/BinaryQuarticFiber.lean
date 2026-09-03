import Submission.WittNormCircleFinite

/-!
A uniform four-point fiber of a binary quadratic-norm parabola. This is an
auxiliary algebraic result; it is not a solution of Erdős 714.
-/
noncomputable section
open Classical Finset Polynomial
open scoped CharTwo
set_option maxHeartbeats 4000000
namespace Erdos714BinaryQuarticFiber
open Erdos714BinaryInverseTrace
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

lemma exists_parameter (hq : 4<Fintype.card F) :
    ∃ t : F, t ≠ 0 ∧ t ≠ 1 ∧ t^2+t ≠ 0 ∧ t^2+t+1 ≠ 0 := by
  let P : F[X] := X^4-X
  have hd : P.natDegree=4 := by dsimp [P]; compute_degree!
  have hn : P ≠ 0 := by intro h; simp [h] at hd
  obtain ⟨t,ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card P hn (by
    simpa only [hd,Cardinal.mk_fintype,Nat.cast_lt] using hq)
  have ht4 : t^4-t ≠ 0 := by simpa [P] using ht
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht4
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht4
  have hA : t^2+t ≠ 0 := by
    intro h
    have hp : t*(t+1)=0 := by linear_combination h
    rcases mul_eq_zero.mp hp with h | h
    · exact ht0 h
    · apply ht1
      simpa using (CharTwo.add_eq_zero.mp h)
  refine ⟨t,ht0,ht1,hA,?_⟩
  intro h
  apply ht4
  have he : t^4-t=(t^2+t+1)*(t^2+t) := by
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!
  rw [he,h,zero_mul]

def linearized (A x : F) : F := x^4+(A+1)*x^2+A*x

def coset (t w : F) : Fin 4 → F := ![w,w+1,w+t,w+t+1]

omit [Fintype F] in
lemma coset_injective (t w : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Function.Injective (coset t w) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp [coset,ht0,ht1,add_assoc] at he ⊢
  all_goals apply ht1
  all_goals linear_combination (norm := ring_nf) he
  all_goals reduce_mod_char!

omit [Fintype F] in
lemma linearized_coset (t w : F) (i : Fin 4) :
    linearized (t^2+t) (coset t w i)=linearized (t^2+t) w := by
  fin_cases i <;> dsimp [coset,linearized]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals reduce_mod_char!

/-- The two lower-degree trace terms cancel as an Artin--Schreier value. -/
lemma trace_identity (m : ℕ) (hcard : Fintype.card F=2^m)
    (A w : F) (hA : A ≠ 0) :
    traceSum m (((A+1)/A^2)*linearized A w)=traceSum m (((A+1)/A^2)*w^4) := by
  have he : ((A+1)/A^2)*linearized A w =
      ((A+1)/A^2)*w^4+(((A+1)/A)*w)^2+((A+1)/A)*w := by
    dsimp [linearized]
    field_simp
  rw [he,traceSum_add,traceSum_add,traceSum_square m hcard]
  simp

/-- Four nonzero, distinct roots with a trace-one quadratic parameter. -/
theorem quartic_parameters (m : ℕ) (hcard : Fintype.card F=2^m)
    (hq : 4<Fintype.card F) :
    ∃ T K b : F, T ≠ 0 ∧ K ≠ 0 ∧ b ≠ 0 ∧ traceSum m (K/T^2)=1 ∧
      ∃ v : Fin 4 ↪ F, (∀ i, v i ≠ 0) ∧
        ∀ i, (v i)^4+T*(v i)^3+K*(v i)^2=b := by
  obtain ⟨t,ht0,ht1,hA,hA1⟩ := exists_parameter hq
  let A := t^2+t
  let C := (A+1)/A^2
  have hC : C ≠ 0 := div_ne_zero hA1 (pow_ne_zero 2 hA)
  obtain ⟨y,hy⟩ := exists_traceSum_one m hcard
  have hp : Function.Injective (fun w : F => w^4) := by
    simpa only [iterateFrobenius_def,Nat.reducePow] using
      (iterateFrobenius F 2 2).injective
  obtain ⟨w,hw⟩ := Finite.surjective_of_injective
    (fun x z h => hp (mul_left_cancel₀ hC h)) y
  change C*w^4=y at hw
  let z := linearized A w
  have hztrace : traceSum m (C*z)=1 := by
    rw [show C*z=((A+1)/A^2)*linearized A w from rfl,
      trace_identity m hcard A w hA]
    change traceSum m (C*w^4)=1
    rw [hw,hy]
  have hz : z ≠ 0 := by
    intro h
    simp [h,traceSum] at hztrace
  have hs (i : Fin 4) : linearized A (coset t w i)=z := linearized_coset t w i
  have hw0 (i : Fin 4) : coset t w i ≠ 0 := by
    intro h
    have hh := hs i
    simp [h,linearized] at hh
    exact hz hh.symm
  let v : Fin 4 ↪ F := ⟨fun i => (coset t w i)⁻¹,by
    intro i j he
    exact coset_injective t w ht0 ht1 (inv_injective he)⟩
  refine ⟨A/z,(A+1)/z,1/z,div_ne_zero hA hz,div_ne_zero hA1 hz,
    div_ne_zero one_ne_zero hz,?_,v,?_,?_⟩
  · have he : ((A+1)/z)/(A/z)^2=C*z := by
      dsimp [C]
      field_simp
    rw [he]
    exact hztrace
  · intro i
    exact inv_ne_zero (hw0 i)
  · intro i
    change ((coset t w i)⁻¹)^4+(A/z)*((coset t w i)⁻¹)^3+
      ((A+1)/z)*((coset t w i)⁻¹)^2=1/z
    have hh := hs i
    dsimp [linearized] at hh
    field_simp [hz,hw0 i]
    apply sub_eq_zero.mp
    linear_combination (norm := ring_nf) hh
    reduce_mod_char!

section Extension
variable {E : Type*} [Field E] [Fintype E] [CharP E 2] [Algebra F E]

omit [CharP F 2] in
/-- Realize the trace-one parameter in the actual quadratic extension. -/
lemma norm_quadratic (m : ℕ) (hcard : Fintype.card F=2^m)
    (hE : Fintype.card E=Fintype.card F^2) (T K : F) (hT : T ≠ 0)
    (htrace : traceSum m (K/T^2)=1) :
    ∃ Z : E, ∀ v : F, Algebra.norm F (algebraMap F E v+Z)=v^2+T*v+K := by
  obtain ⟨y,hy,hyq⟩ := Erdos714WittNormCircle.extension_root m hcard hE (K/T^2) htrace
  refine ⟨algebraMap F E T*y,?_⟩
  intro v
  apply (algebraMap F E).injective
  rw [Erdos714TranslatedNorm.quadratic_norm_power hE]
  have hpow (x : E) : x^(Fintype.card F+1)=
      x*Erdos714WittNormCircle.conjugation m x := by
    rw [Erdos714WittNormCircle.conjugation_apply,←hcard,pow_succ,mul_comm]
  rw [hpow,map_add,map_mul,Erdos714WittNormCircle.conjugation_coefficient m hcard,
    Erdos714WittNormCircle.conjugation_coefficient m hcard,hyq]
  simp only [map_add,map_mul,map_pow]
  have ht : algebraMap F E T ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hT
  have hh : (algebraMap F E T)^2*(y^2+y)=algebraMap F E K := by
    rw [hy,map_div₀,map_pow]
    field_simp
  linear_combination (norm := ring_nf) hh
  reduce_mod_char!

/-- A uniform actual-norm fiber, with all four scalars nonzero. -/
theorem norm_four_fiber (m : ℕ) (hcard : Fintype.card F=2^m)
    (hE : Fintype.card E=Fintype.card F^2) (hq : 4<Fintype.card F) :
    ∃ Z : E, Z ≠ 0 ∧ ∃ b : F, b ≠ 0 ∧ ∃ v : Fin 4 ↪ F,
      (∀ i, v i ≠ 0) ∧ ∀ i, (v i)^2*Algebra.norm F (algebraMap F E (v i)+Z)=b := by
  obtain ⟨T,K,b,hT,hK,hb,htr,v,hv,he⟩ := quartic_parameters m hcard hq
  obtain ⟨Z,hZ⟩ := norm_quadratic m hcard hE T K hT htr
  have hn : Z ≠ 0 := by
    intro hz
    have h := hZ 0
    simp [hz,Algebra.norm_zero] at h
    exact hK h.symm
  refine ⟨Z,hn,b,hb,v,hv,?_⟩
  intro i
  rw [hZ]
  linear_combination he i
end Extension
#print axioms exists_parameter
#print axioms trace_identity
#print axioms quartic_parameters
#print axioms norm_quadratic
#print axioms norm_four_fiber
end Erdos714BinaryQuarticFiber
