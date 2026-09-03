import FormalConjecturesUtil

/-!
# A limitation of the exponential-polynomial proof of Kanold's bound

For distinct primes and primitive roots of those orders, the product
`∏ p ∈ P, (z p ^ n - c p)` with nonzero `c p` has no constant-coefficient
linear recurrence of order below `2 ^ P.card`. This does not bound its longest
zero interval from below, and in particular does not disprove Erdős 970.
-/

namespace Erdos970.KanoldRecurrence

open Finset

/-- Distinct geometric sequences are linearly independent. -/
theorem coefficients_zero {ι K : Type*} [Field K] (s : Finset ι)
    (z c : ι → K) (hz : Set.InjOn z (↑s : Set ι))
    (hzero : ∀ n : ℕ, ∑ i ∈ s, c i * z i ^ n = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | @insert a s ha ih =>
    have hs : Set.InjOn z (↑s : Set ι) :=
      hz.mono (by intro i hi; exact mem_insert_of_mem hi)
    have hd (n : ℕ) : ∑ i ∈ s, (c i * (z i - z a)) * z i ^ n = 0 := by
      have h0 := hzero n
      have h1 := hzero (n + 1)
      rw [sum_insert ha] at h0 h1
      calc
        (∑ i ∈ s, (c i * (z i - z a)) * z i ^ n) =
            (∑ i ∈ s, c i * z i ^ (n + 1)) -
              z a * (∑ i ∈ s, c i * z i ^ n) := by
          rw [mul_sum, ← sum_sub_distrib]
          apply sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring
        _ = 0 := by rw [pow_succ] at h1; linear_combination h1 - z a * h0
    have hc : ∀ i ∈ s, c i = 0 := by
      intro i hi
      have hd' := ih (fun i => c i * (z i - z a)) hs hd i hi
      apply (mul_eq_zero.mp hd').resolve_right
      intro heq
      have hia := hz (mem_insert_of_mem hi) (mem_insert_self a s) (sub_eq_zero.mp heq)
      exact ha (hia ▸ hi)
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · have hh := hzero 0
      have hsum : (∑ x ∈ s, c x) = 0 := sum_eq_zero hc
      simpa [sum_insert ha, hsum] using hh
    · exact hc i hi

/-- Products of roots with distinct prime orders have the expected order. -/
theorem orderOf_prod (P : Finset ℕ) (z : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (hz : ∀ p ∈ P, IsPrimitiveRoot (z p) p) :
    orderOf (∏ p ∈ P, z p) = ∏ p ∈ P, p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hP' := fun q hq => hP q (mem_insert_of_mem hq)
    have hz' := fun q hq => hz q (mem_insert_of_mem hq)
    have hord := ih hP' hz'
    rw [prod_insert hp, prod_insert hp,
      (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
    · rw [← (hz p (mem_insert_self _ _)).eq_orderOf, hord]
    · rw [← (hz p (mem_insert_self _ _)).eq_orderOf, hord]
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes (hP p (mem_insert_self _ _)) (hP' q hq)).mpr
        (fun hpq => hp (hpq ▸ hq))

/-- The subset products are all different: no frequencies merge. -/
theorem prod_injective_on_powerset (P : Finset ℕ) (z : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (hz : ∀ p ∈ P, IsPrimitiveRoot (z p) p) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, z p) (↑P.powerset : Set (Finset ℕ)) := by
  classical
  intro S hS T hT heq
  dsimp only at heq
  have hSP := mem_powerset.mp hS
  have hTP := mem_powerset.mp hT
  have hprod : (∏ p ∈ S, p) = ∏ p ∈ T, p := by
    rw [← orderOf_prod S z (fun p hp => hP p (hSP hp)) (fun p hp => hz p (hSP hp)),
      ← orderOf_prod T z (fun p hp => hP p (hTP hp)) (fun p hp => hz p (hTP hp)), heq]
  have hsub {A B : Finset ℕ} (hAP : A ⊆ P) (hBP : B ⊆ P)
      (he : (∏ p ∈ A, p) = ∏ p ∈ B, p) : A ⊆ B := by
    intro p hp
    have hd : p ∣ ∏ q ∈ B, q := he ▸ dvd_prod_of_mem (fun q => q) hp
    obtain ⟨q, hq, hpq⟩ := ((hP p (hAP hp)).prime.dvd_finset_prod_iff id).mp hd
    have heq : p = q := (((hP q (hBP hq)).dvd_iff_eq (hP p (hAP hp)).ne_one).mp hpq).symm
    exact heq ▸ hq
  exact Subset.antisymm (hsub hSP hTP hprod) (hsub hTP hSP hprod.symm)

/-- A recurrence for a sum of distinct geometric sequences has every frequency
as a root of its characteristic polynomial, if its coefficient is nonzero. -/
theorem recurrence_roots {ι K : Type*} [Field K] (s : Finset ι)
    (z c : ι → K) (hz : Set.InjOn z (↑s : Set ι)) (hc : ∀ i ∈ s, c i ≠ 0)
    (E : LinearRecurrence K)
    (hE : E.IsSolution (fun n => ∑ i ∈ s, c i * z i ^ n)) :
    ∀ i ∈ s, E.charPoly.eval (z i) = 0 := by
  classical
  have hzsum (n : ℕ) :
      ∑ i ∈ s, (c i * E.charPoly.eval (z i)) * z i ^ n = 0 := by
    have heval (i : ι) : E.charPoly.eval (z i) =
        z i ^ E.order - ∑ j : Fin E.order, E.coeffs j * z i ^ j.val := by
      simp [LinearRecurrence.charPoly, Polynomial.eval_finset_sum]
    simp_rw [heval]
    calc
      (∑ i ∈ s, (c i * (z i ^ E.order -
          ∑ j : Fin E.order, E.coeffs j * z i ^ j.val)) * z i ^ n) =
          (∑ i ∈ s, c i * z i ^ (n + E.order)) -
            ∑ j : Fin E.order, E.coeffs j * (∑ i ∈ s, c i * z i ^ (n + j.val)) := by
        simp only [mul_sub, sub_mul, sum_sub_distrib, sum_mul, mul_sum, pow_add]
        rw [sum_comm]
        congr 1
        · apply sum_congr rfl
          intro i hi
          ring
        · apply sum_congr rfl
          intro j hj
          apply sum_congr rfl
          intro i hi
          ring
      _ = 0 := sub_eq_zero.mpr (hE n)
  have hh := coefficients_zero s z (fun i => c i * E.charPoly.eval (z i)) hz hzsum
  intro i hi
  exact (mul_eq_zero.mp (hh i hi)).resolve_left (hc i hi)

lemma charPoly_degree {K : Type*} [Field K] (E : LinearRecurrence K) :
    E.charPoly ≠ 0 ∧ E.charPoly.natDegree ≤ E.order := by
  have hcoeff : E.charPoly.coeff E.order = 1 := by
    simp only [LinearRecurrence.charPoly, Polynomial.coeff_sub, Polynomial.finset_sum_coeff,
      Polynomial.coeff_monomial]
    have hh : (∑ j : Fin E.order, if (j : ℕ) = E.order then E.coeffs j else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      exact if_neg (Nat.ne_of_lt j.isLt)
    simp only [hh, sub_zero, ite_true]
  constructor
  · intro he
    simpa only [he, Polynomial.coeff_zero, zero_ne_one] using hcoeff
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_monomial_le _
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      exact (Polynomial.natDegree_monomial_le _).trans j.isLt.le

/-- The order is at least the number of distinct, nonzero-weighted frequencies. -/
theorem card_le_recurrence_order {ι K : Type*} [Field K] (s : Finset ι)
    (z c : ι → K) (hz : Set.InjOn z (↑s : Set ι)) (hc : ∀ i ∈ s, c i ≠ 0)
    (E : LinearRecurrence K)
    (hE : E.IsSolution (fun n => ∑ i ∈ s, c i * z i ^ n)) : s.card ≤ E.order := by
  classical
  have hroots := recurrence_roots s z c hz hc E hE
  have hcP := charPoly_degree E
  have hsub : (s.image z).val ⊆ E.charPoly.roots := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact (Polynomial.mem_roots hcP.1).mpr (hroots i hi)
  have hh := (Polynomial.card_le_degree_of_subset_roots hsub).trans hcP.2
  rwa [(card_image_iff.mpr hz)] at hh

/-- In the Kanold product all `2 ^ P.card` frequencies really are needed by
any constant-coefficient linear recurrence, even for one fixed residue vector. -/
theorem two_pow_le_order_of_product_solution (P : Finset ℕ) (z c : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (hz : ∀ p ∈ P, IsPrimitiveRoot (z p) p)
    (hc : ∀ p ∈ P, c p ≠ 0) (E : LinearRecurrence ℂ)
    (hE : E.IsSolution (fun n => ∏ p ∈ P, (z p ^ n - c p))) :
    2 ^ P.card ≤ E.order := by
  classical
  let base : Finset ℕ → ℂ := fun S => ∏ p ∈ P \ S, z p
  let coeff : Finset ℕ → ℂ := fun S => (-1) ^ S.card * ∏ p ∈ S, c p
  have hb : Set.InjOn base (↑P.powerset : Set (Finset ℕ)) := by
    intro S hS T hT he
    have hSP := mem_powerset.mp hS
    have hTP := mem_powerset.mp hT
    have he' : P \ S = P \ T := prod_injective_on_powerset P z hP hz
      (mem_powerset.mpr sdiff_subset) (mem_powerset.mpr sdiff_subset) he
    have hh := congrArg (fun A : Finset ℕ => P \ A) he'
    simpa only [sdiff_sdiff_eq_self hSP, sdiff_sdiff_eq_self hTP] using hh
  have hcoeff : ∀ S ∈ P.powerset, coeff S ≠ 0 := by
    intro S hS
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact hc p (mem_powerset.mp hS hp)
  have hexpand (n : ℕ) : (∏ p ∈ P, (z p ^ n - c p)) =
      ∑ S ∈ P.powerset, coeff S * base S ^ n := by
    rw [prod_sub]
    apply sum_congr rfl
    intro S hS
    simp only [coeff, base, prod_pow]
    ring
  have hEsum : E.IsSolution (fun n => ∑ S ∈ P.powerset, coeff S * base S ^ n) := by
    simpa only [hexpand] using hE
  simpa only [card_powerset] using card_le_recurrence_order P.powerset base coeff hb hcoeff E hEsum

/-- The nonzero-coefficient hypothesis always holds for the prime-residue product. -/
theorem two_pow_le_order_of_residue_product (P : Finset ℕ) (z : ℕ → ℂ) (r : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hz : ∀ p ∈ P, IsPrimitiveRoot (z p) p)
    (E : LinearRecurrence ℂ)
    (hE : E.IsSolution (fun n => ∏ p ∈ P, (z p ^ n - z p ^ r p))) :
    2 ^ P.card ≤ E.order :=
  two_pow_le_order_of_product_solution P z (fun p => z p ^ r p) hP hz
    (fun p hp => pow_ne_zero _ ((hz p hp).ne_zero (hP p hp).ne_zero)) E hE

#print axioms coefficients_zero
#print axioms prod_injective_on_powerset
#print axioms two_pow_le_order_of_residue_product
end Erdos970.KanoldRecurrence
