import FormalConjecturesUtil

/-! A Mason--Stothers degree bound for a specified polynomial support.
This bounds polynomial S-unit identities, not arbitrary rational-distance
configurations or rational functions with additional squared factors. -/
namespace Erdos213.SUnitDegreeBound
open Polynomial UniqueFactorizationMonoid
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- If all factors of `a*b*c` are supported in `h`, the nonconstant ABC
alternative bounds all three degrees by `natDegree h - 1`. -/
theorem degree_bound_of_support_power {a b c h : K[X]} (n : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0)
    (hab : IsCoprime a b) (hsum : a+b+c=0)
    (hsupport : a*b*c ∣ h^(n+1)) :
    a.natDegree ≤ h.natDegree-1 ∧ b.natDegree ≤ h.natDegree-1 ∧
      c.natDegree ≤ h.natDegree-1 := by
  classical
  have hrad : radical (a*b*c) ∣ radical h := by
    have hd := radical_dvd_radical hsupport (pow_ne_zero (n+1) hh)
    simpa only [radical_pow h (Nat.succ_ne_zero n)] using hd
  have hdeg : (radical (a*b*c)).natDegree ≤ h.natDegree :=
    (natDegree_le_of_dvd hrad radical_ne_zero).trans natDegree_radical_le
  rcases Polynomial.abc ha hb hc hab hsum with h | h
  · omega
  · simp only [natDegree_eq_zero_of_derivative_eq_zero h.1,
      natDegree_eq_zero_of_derivative_eq_zero h.2.1,
      natDegree_eq_zero_of_derivative_eq_zero h.2.2, Nat.zero_le, and_self]

/-- The finite support polynomial has one linear factor for each branch. -/
def support (S : Finset K) : K[X] := ∏ r ∈ S, (X-C r)

omit [CharZero K] in
lemma support_ne_zero (S : Finset K) : support S ≠ 0 := by
  classical
  exact (monic_prod_X_sub_C id S).ne_zero

omit [CharZero K] in
lemma support_natDegree (S : Finset K) : (support S).natDegree=S.card := by
  classical
  unfold support
  rw [natDegree_prod_of_monic (s := S) (f := fun r : K => (X-C r : K[X]))
    (fun r _ => monic_X_sub_C r)]
  simp

omit [CharZero K] in
lemma supported_product_dvd_power (S : Finset K) (e : K → ℕ) (u : K) (hu : u≠0)
    (N : ℕ) (he : ∀ r∈S, e r≤N) :
    C u * (∏ r ∈ S, (X-C r)^e r) ∣ (support S)^N := by
  classical
  rw [(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu)).mul_left_dvd]
  unfold support
  rw [← Finset.prod_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun r hr => pow_dvd_pow _ (he r hr))


/-- A support of `m` finite roots gives the usual degree bound `m-1`.
Infinity may be a zero or pole of the corresponding rational function. -/
theorem finite_root_degree_bound {a b c : K[X]} (S : Finset K) (n : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a+b+c=0)
    (hsupport : a*b*c ∣ (support S)^(n+1)) :
    a.natDegree ≤ S.card-1 ∧ b.natDegree ≤ S.card-1 ∧ c.natDegree ≤ S.card-1 := by
  simpa only [support_natDegree] using
    degree_bound_of_support_power n ha hb hc (support_ne_zero S) hab hsum hsupport

/-- A factorization formulation: all exponents are unrestricted natural
numbers, not pre-bounded by the enumerator. -/
theorem finite_root_degree_bound_of_factorization {a b c : K[X]}
    (S : Finset K) (u : K) (hu : u≠0) (e : K → ℕ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hab : IsCoprime a b) (hsum : a+b+c=0)
    (hf : a*b*c=C u*(∏ r ∈ S, (X-C r)^e r)) :
    a.natDegree ≤ S.card-1 ∧ b.natDegree ≤ S.card-1 ∧ c.natDegree ≤ S.card-1 := by
  classical
  let N := ∑ r ∈ S, e r
  apply finite_root_degree_bound S N ha hb hc hab hsum
  rw [hf]
  apply supported_product_dvd_power S e u hu
  intro r hr
  have h : e r ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr
  exact h.trans (Nat.le_succ N)

/-- The seven transformed finite roots used by `BuchiEightInput`. -/
def eightInputSupport : Finset ℚ := {0,1,12/5,9/2,8,15,36}

lemma eightInputSupport_card : eightInputSupport.card=7 := by
  decide +kernel

theorem eightInput_degree_le_six {a b c : ℚ[X]} (n : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a+b+c=0)
    (hsupport : a*b*c ∣ (support eightInputSupport)^(n+1)) :
    a.natDegree ≤ 6 ∧ b.natDegree ≤ 6 ∧ c.natDegree ≤ 6 := by
  simpa only [eightInputSupport_card, Nat.reduceSub] using
    finite_root_degree_bound eightInputSupport n ha hb hc hab hsum hsupport

#print axioms degree_bound_of_support_power
#print axioms finite_root_degree_bound
#print axioms finite_root_degree_bound_of_factorization
#print axioms eightInput_degree_le_six
end
end Erdos213.SUnitDegreeBound
