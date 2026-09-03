import Submission.LocalPeakCounting
import Submission.PolynomialPeakCriterion

/-! Large-multiplicity power-sum tuples are Zariski dense. Thus conditioning a
polynomial identity on arbitrarily high multiplicity does not weaken it.
This is not a positive-power count bound. -/
namespace Erdos322Research.LargeCountPolynomialDensity
noncomputable section
open Finset LocalPeakCounting PolynomialPeakCriterion
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- Critical zero-fiber density is unbounded for every exponent >= 2. -/
lemma exists_large_root_density (k C : ℕ) :
    ∃ q : ℕ, 0 < q ∧ C*q^(k+1) < rootCount (k+2) q := by
  obtain ⟨p,hp,hpk,a,ha,hseed⟩ := exists_good_prime (k+2) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  let d := C*p^(k+1)
  let q := p^((k+2)*d+1)
  have hq : 0 < q := pow_pos hp.pos _
  have hg := rootCount_growth p k hpk a ha hseed d
  refine ⟨q,hq,?_⟩
  calc
    C*q^(k+1) = d*p^((k+2)*d*(k+1)) := by
      dsimp only [q,d]
      rw [← pow_mul,show ((k+2)*(C*p^(k+1))+1)*(k+1)=
        (k+1)+(k+2)*(C*p^(k+1))*(k+1) by ring,pow_add]
      ring
    _ < (d+1)*p^((k+2)*d*(k+1)) := by
      exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos _)
    _ ≤ rootCount (k+2) q := hg

def target {K q : ℕ} (x : Roots K q) : ℕ := ∑ i, (x.val i : ℕ)^K

private lemma target_bound (K q : ℕ) (hK : 0 < K) (x : Roots K q) :
    target x ≤ q*(K*q^(K-1)) := by
  calc
    target x ≤ ∑ _i : Fin K, q^K := sum_le_sum fun i _ ↦
      Nat.pow_le_pow_left (x.val i).isLt.le K
    _ = K*q^K := by simp
    _ = q*(K*q^(K-1)) := by
      have he : q^K=q^(K-1)*q := by rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ K)]
      rw [he]
      ring

private def targetIndex (K q : ℕ) (hK : 0 < K) (hq : 0 < q) (x : Roots K q) :
    Fin (K*q^(K-1)+1) :=
  ⟨target x/q,by
    have hh := Nat.div_le_div_right (c := q) (target_bound K q hK x)
    rw [Nat.mul_div_cancel_left _ hq] at hh
    omega⟩

private lemma target_eq_index (K q : ℕ) (hK : 0 < K) (hq : 0 < q) (x : Roots K q) :
    target x=q*(targetIndex K q hK hq x : ℕ) := (Nat.mul_div_cancel' x.property).symm

/-- All low-multiplicity targets together account for at most M times the
number of possible target indices. -/
lemma low_count_bound (K q M : ℕ) (hK : 0 < K) (hq : 0 < q) :
    Fintype.card {x : Roots K q // Erdos322.representationCount K (target x) ≤ M} ≤
      (K*q^(K-1)+1)*M := by
  let L := {x : Roots K q // Erdos322.representationCount K (target x) ≤ M}
  let f : L → Fin (K*q^(K-1)+1) := fun x ↦ targetIndex K q hK hq x.val
  have hbound (y : Fin (K*q^(K-1)+1)) : Fintype.card {x : L // f x=y} ≤ M := by
    let T := {x : L // f x=y}
    by_cases ht : Nonempty T
    · obtain ⟨z⟩ := ht
      have hz : Erdos322.representationCount K (q*(y : ℕ)) ≤ M := by
        have hh := z.val.property
        rw [target_eq_index K q hK hq z.val.val,show targetIndex K q hK hq z.val.val=y from z.property] at hh
        exact hh
      let E : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
      let v : Fin (Fintype.card T) → Fin K → ℕ := fun a i ↦ ((E a).val.val.val i : ℕ)
      have hsum (a : Fin (Fintype.card T)) : ∑ i, v a i^K=q*(y : ℕ) := by
        change target (E a).val.val=q*(y : ℕ)
        rw [target_eq_index K q hK hq,show targetIndex K q hK hq (E a).val.val=y from (E a).property]
      have hi : Function.Injective v := by
        intro a b h
        apply E.injective
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact congrFun h i
      exact (count_lower_of_injective hK v hsum hi).trans hz
    · haveI : IsEmpty T := not_nonempty_iff.mp ht
      change Fintype.card T ≤ M
      rw [Fintype.card_eq_zero]
      omega
  calc
    Fintype.card L = ∑ y, Fintype.card {x : L // f x=y} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _y : Fin (K*q^(K-1)+1), M := sum_le_sum fun y _ ↦ hbound y
    _ = _ := by simp

/-- A nonzero polynomial accounts for at most deg(P)*q^(K-1) points in the
whole box, hence also among the modular roots in that box. -/
lemma polynomial_root_bound (K q : ℕ) (hK : 0 < K) (hq : 0 < q)
    (P : MvPolynomial (Fin K) ℚ) (hP : P ≠ 0) :
    Fintype.card {x : Roots K q // MvPolynomial.eval (fun i ↦ ((x.val i : ℕ) : ℚ)) P=0} ≤
      P.totalDegree*q^(K-1) := by
  let S : Finset ℚ := (range q).image Nat.cast
  let T := (Fintype.piFinset (fun _ : Fin K ↦ S)).filter (fun x ↦ MvPolynomial.eval x P=0)
  let Z := {x : Roots K q // MvPolynomial.eval (fun i ↦ ((x.val i : ℕ) : ℚ)) P=0}
  let f : Z → T := fun x ↦ ⟨fun i ↦ ((x.val.val i : ℕ) : ℚ),by
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_,x.property⟩
    intro i
    exact mem_image.mpr ⟨(x.val.val i : ℕ),mem_range.mpr (x.val.val i).isLt,rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun t : T ↦ t.val i) h
    change (((x.val.val i : ℕ) : ℚ)) = (((y.val.val i : ℕ) : ℚ)) at hh
    exact_mod_cast hh
  have hcard : Fintype.card Z ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hS : S.card=q := by
    rw [card_image_of_injective _ Nat.cast_injective,card_range]
  have hz := MvPolynomial.schwartz_zippel_totalDegree hP S
  change (T.card : ℚ≥0)/(S.card : ℚ≥0)^K ≤ (P.totalDegree : ℚ≥0)/S.card at hz
  rw [hS] at hz
  have hqp : (0 : ℚ≥0) < q := by exact_mod_cast hq
  have hm := (div_le_div_iff₀ (pow_pos hqp K) hqp).mp hz
  have hm' : T.card*q ≤ P.totalDegree*q^K := by exact_mod_cast hm
  have he : q^K=q*q^(K-1) := by rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ K)]
  rw [he] at hm'
  have hb : T.card ≤ P.totalDegree*q^(K-1) := by
    exact Nat.le_of_mul_le_mul_right
      (show T.card*q ≤ (P.totalDegree*q^(K-1))*q by nlinarith [hm']) hq
  exact hcard.trans hb

/-- A polynomial vanishing at every natural tuple whose target has more than
M representations must be the zero polynomial. -/
theorem eq_zero_of_vanish_on_large_counts (k M : ℕ)
    (P : MvPolynomial (Fin (k+2)) ℚ)
    (h : ∀ a : Fin (k+2) → ℕ,
      M < Erdos322.representationCount (k+2) (∑ i, a i^(k+2)) →
        MvPolynomial.eval (fun i ↦ (a i : ℚ)) P=0) : P=0 := by
  by_contra hP
  obtain ⟨q,hq,hlarge⟩ := exists_large_root_density k (M*(k+3)+P.totalDegree)
  let L : Roots (k+2) q → Prop := fun x ↦ Erdos322.representationCount (k+2) (target x) ≤ M
  let Z : Roots (k+2) q → Prop := fun x ↦ MvPolynomial.eval (fun i ↦ ((x.val i : ℕ) : ℚ)) P=0
  have hlo : Fintype.card {x // L x} ≤ ((k+2)*q^(k+1)+1)*M := by
    simpa only [Nat.add_sub_cancel] using low_count_bound (k+2) q M (by omega) hq
  have hzero : Fintype.card {x // Z x} ≤ P.totalDegree*q^(k+1) := by
    simpa only [Nat.add_sub_cancel] using polynomial_root_bound (k+2) q (by omega) hq P hP
  have hsub : Fintype.card {x // ¬ L x} ≤ Fintype.card {x // Z x} :=
    Fintype.card_subtype_mono _ _ (fun x hx ↦ h (fun i ↦ (x.val i : ℕ)) (by exact Nat.lt_of_not_ge hx))
  have hcomp := Fintype.card_subtype_compl L
  have hle := Fintype.card_subtype_le L
  change Fintype.card {x // ¬ L x}=rootCount (k+2) q-Fintype.card {x // L x} at hcomp
  change Fintype.card {x // L x} ≤ rootCount (k+2) q at hle
  have hqpow : 1 ≤ q^(k+1) := one_le_pow₀ (by omega)
  have htotal : rootCount (k+2) q ≤ Fintype.card {x // L x} + Fintype.card {x // Z x} := by omega
  have hmqp : M ≤ M*q^(k+1) := by nlinarith
  nlinarith

/-- Large-count tuples escape every prescribed proper polynomial zero set. -/
theorem exists_large_count_off_polynomial (k M : ℕ)
    (P : MvPolynomial (Fin (k+2)) ℚ) (hP : P ≠ 0) :
    ∃ a : Fin (k+2) → ℕ,
      M < Erdos322.representationCount (k+2) (∑ i, a i^(k+2)) ∧
        MvPolynomial.eval (fun i ↦ (a i : ℚ)) P ≠ 0 := by
  by_contra hh
  push_neg at hh
  exact hP (eq_zero_of_vanish_on_large_counts k M P hh)

/-- Requiring a polynomial identity only above a fixed multiplicity threshold
already implies the unrestricted polynomial identity. -/
theorem identity_of_large_counts (k M : ℕ)
    (P Q : MvPolynomial (Fin (k+2)) ℚ)
    (h : ∀ a : Fin (k+2) → ℕ,
      M < Erdos322.representationCount (k+2) (∑ i, a i^(k+2)) →
        MvPolynomial.eval (fun i ↦ (a i : ℚ)) P = MvPolynomial.eval (fun i ↦ (a i : ℚ)) Q) : P=Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_vanish_on_large_counts k M
  intro a ha
  rw [map_sub,h a ha,sub_self]

/-- A fixed exceptional denominator does not change the conclusion: equality
on all high-count tuples away from its zero set is still a polynomial identity. -/
theorem identity_of_large_counts_off_zero (k M : ℕ)
    (P Q D : MvPolynomial (Fin (k+2)) ℚ) (hD : D ≠ 0)
    (h : ∀ a : Fin (k+2) → ℕ,
      M < Erdos322.representationCount (k+2) (∑ i, a i^(k+2)) →
      MvPolynomial.eval (fun i ↦ (a i : ℚ)) D ≠ 0 →
      MvPolynomial.eval (fun i ↦ (a i : ℚ)) P = MvPolynomial.eval (fun i ↦ (a i : ℚ)) Q) : P=Q := by
  have hz : D*(P-Q)=0 := by
    apply eq_zero_of_vanish_on_large_counts k M
    intro a ha
    rw [map_mul,map_sub]
    by_cases hd : MvPolynomial.eval (fun i ↦ (a i : ℚ)) D=0
    · rw [hd,zero_mul]
    · rw [h a ha hd,sub_self,mul_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hD)

end
end Erdos322Research.LargeCountPolynomialDensity
