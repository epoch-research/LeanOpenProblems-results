import Submission.SharpWeightedExceptionArithmetic
import Submission.DoubleExceptionOdd

/-! A distinct no-three odd family cannot be completed by three additional
classes with distinct nontrivial odd moduli. This is a restricted obstruction,
not a settlement of the unrestricted odd covering problem. -/
namespace Erdos7ThreeDistinctExceptions
open scoped BigOperators
open Erdos7Reduction Erdos7WeightedExceptionArithmetic
open Erdos7MinimumTernaryClass Erdos7DoubleExceptionOdd
set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma weight_nonneg (d : ℕ) : 0 ≤ weight d := by unfold weight; positivity

lemma weight_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    weight (a*b) ≤ weight a * weight b := by
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 5/4)
    (Finset.card_union_le a.primeFactors b.primeFactors)
  rw [pow_add] at hh
  unfold weight
  rw [Nat.primeFactors_mul ha hb, Nat.cast_mul, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hh (by positivity)

lemma prime_weight (p : ℕ) (hp : p.Prime) : weight p = (5/4 : ℚ)/p := by
  simp only [weight,hp.primeFactors,Finset.card_singleton,pow_one]

lemma weight_le_quarter (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d) :
    weight d ≤ (1/4 : ℚ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hp : d.Prime
    · have h5 := (prime_factor_ge_five d ho h3 d (by simp [hp.primeFactors])).2
      rw [prime_weight d hp]
      have h5' : (5 : ℚ) ≤ d := by exact_mod_cast h5
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
      linarith
    · obtain ⟨u,v,hu,hv,he⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ d)).mp hp
      have hu1 : 1 < u := by nlinarith
      have hv1 : 1 < v := by nlinarith
      have hud : u ∣ d := he ▸ dvd_mul_right u v
      have hvd : v ∣ d := he ▸ dvd_mul_left v u
      have hwu := ih u hu hu1 (ho.of_dvd_nat hud) (fun hh => h3 (hh.trans hud))
      have hwv := ih v hv hv1 (ho.of_dvd_nat hvd) (fun hh => h3 (hh.trans hvd))
      have hh := (weight_mul_le u v (by omega) (by omega)).trans
        (mul_le_mul hwu hwv (weight_nonneg v) (by norm_num))
      rw [he] at hh
      linarith

lemma composite_weight_le (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (hp : ¬ d.Prime) : weight d ≤ (1/16 : ℚ) := by
  obtain ⟨u,v,hu,hv,he⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ d)).mp hp
  have hu1 : 1 < u := by nlinarith
  have hv1 : 1 < v := by nlinarith
  have hud : u ∣ d := he ▸ dvd_mul_right u v
  have hvd : v ∣ d := he ▸ dvd_mul_left v u
  have hwu := weight_le_quarter u hu1 (ho.of_dvd_nat hud) (fun hh => h3 (hh.trans hud))
  have hwv := weight_le_quarter v hv1 (ho.of_dvd_nat hvd) (fun hh => h3 (hh.trans hvd))
  have hh := (weight_mul_le u v (by omega) (by omega)).trans
    (mul_le_mul hwu hwv (weight_nonneg v) (by norm_num))
  rw [he] at hh
  norm_num at hh ⊢
  exact hh

lemma weight_le_outside_five_seven (d : ℕ) (hd : 1 < d) (ho : Odd d)
    (h3 : ¬ 3 ∣ d) (h5 : d ≠ 5) (h7 : d ≠ 7) : weight d ≤ (5/44 : ℚ) := by
  by_cases hp : d.Prime
  · have hge : 11 ≤ d := by
      by_contra hn
      interval_cases d <;> norm_num at *
    rw [prime_weight d hp]
    have hge' : (11 : ℚ) ≤ d := by exact_mod_cast hge
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
    linarith
  · exact (composite_weight_le d hd ho h3 hp).trans (by norm_num)

lemma three_distinct_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (hJ : Fintype.card J ≤ 3) : (∑ j, weight (d j)) ≤ (167/308 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (5/44 : ℚ) +
      (if d j=5 then 3/22 else 0) + (if d j=7 then 5/77 else 0) := by
    by_cases h5 : d j=5
    · rw [h5]
      norm_num [prime_weight 5 (by decide)]
    · by_cases h7 : d j=7
      · rw [h7]
        norm_num [prime_weight 7 (by decide)]
      · simpa only [if_neg h5,if_neg h7,add_zero] using
          weight_le_outside_five_seven (d j) (hd j).1 (hd j).2 (h3 j) h5 h7
  have he (p : ℕ) (c : ℚ) (hc : 0 ≤ c) :
      (∑ j : J, if d j=p then c else 0) ≤ c := by
    have hcard : (Finset.univ.filter (fun j : J => d j=p)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      exact hinj ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm)
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard' : ((Finset.univ.filter (fun j : J => d j=p)).card : ℚ) ≤ 1 := by exact_mod_cast hcard
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcard' hc
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h5 := he 5 (3/22) (by norm_num)
  have h7 := he 7 (5/77) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 3 := by exact_mod_cast hJ
  linarith

theorem not_cover_three_distinct_no_three {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hd3 : ∀ j, ¬ 3 ∣ d j)
    (hJ : Fintype.card J ≤ 3) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  apply Erdos7SharpWeightedExceptionArithmetic.not_cover_with_weighted_exceptions
    m a hinj hm h3 d b (fun j => ⟨by have := (hd j).1; omega,(hd j).2⟩) hd3
  exact (three_distinct_weight d hdi hd hd3 hJ).trans (by norm_num)

/-- The extra moduli may contain three and may duplicate base labels,
but they must be distinct from one another. -/
theorem not_cover_three_distinct_odd {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 3) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  by_cases hsmall : Fintype.card J ≤ 2
  · exact not_cover_with_at_most_two_odd_exceptions m a hinj hm h3 d hd b hsmall
  by_cases hnone : ∀ j, ¬ 3 ∣ d j
  · exact not_cover_three_distinct_no_three m a hinj hm h3 d b hdi hd hnone hJ
  by_cases hall : ∀ j, 3 ∣ d j
  · obtain ⟨j₀,hj₀⟩ : ∃ j, d j ≠ 3 := by
      by_contra! hn
      have hh := Fintype.card_le_of_injective (fun _ : J => ()) (by
        intro j k _
        exact hdi ((hn j).trans (hn k).symm))
      norm_num at hh
      omega
    have hother : Fintype.card {j : J // j≠j₀} ≤ 2 := by
      have hh := Fintype.card_subtype_lt (p := fun j : J => j≠j₀) (x := j₀) (by simp)
      simp only [Fintype.card_subtype] at hh ⊢
      omega
    obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue
      (fun j : {j : J // j≠j₀} => b j) hother
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    have hquot : 1 < d j₀/3 ∧ Odd (d j₀/3) := by
      have hh := Nat.mul_div_cancel' (hall j₀)
      have hpos := (hd j₀).1
      refine ⟨by omega,(hd j₀).2.of_dvd_nat (Nat.div_dvd_of_dvd (hall j₀))⟩
    intro hcover
    apply Erdos7NoThreeHoleSpan.not_cover_with_odd_exception
      m a' hinj hm h3 (d j₀/3) hquot ((b j₀-r)/3)
    intro x
    rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact Or.inl ⟨i,ha' i x hi⟩
    · have hres : (3 : ℤ) ∣ b j-r := by
        have hh := (Int.natCast_dvd_natCast.mpr (hall j)).trans hj
        omega
      have he : j=j₀ := by
        by_contra hn
        exact hr ⟨j,hn⟩ hres
      subst j
      exact Or.inr (Erdos7SmallTernaryBranches.quotient_residue
        (d j₀) (b j₀) r (hall j₀) hres x hj)
  · push_neg at hnone hall
    obtain ⟨j₀,hj₀⟩ := hnone
    obtain ⟨j₁,hj₁⟩ := hall
    let T := {j : J // 3 ∣ d j}
    let K := {j : J // ¬ 3 ∣ d j}
    have hT : Fintype.card T ≤ 2 := by
      have hh := Fintype.card_subtype_lt (p := fun j : J => 3 ∣ d j) (x := j₁) hj₁
      simp only [T,Fintype.card_subtype] at hh ⊢
      omega
    have hK : Fintype.card K ≤ 2 := by
      have hh := Fintype.card_subtype_lt (p := fun j : J => ¬ 3 ∣ d j) (x := j₀) (by simpa using hj₀)
      simp only [K,Fintype.card_subtype] at hh ⊢
      omega
    obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue (fun j : T => b j) hT
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    choose b' hb' using fun j : K => affine_residue (d j) j.property (b j) r
    intro hcover
    apply not_cover_with_at_most_two_odd_exceptions m a' hinj hm h3
      (fun j : K => d j) (fun j => hd j) b' hK
    intro x
    rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact Or.inl ⟨i,ha' i x hi⟩
    · have hj3 : ¬ 3 ∣ d j := by
        intro hh
        have hz := (Int.natCast_dvd_natCast.mpr hh).trans hj
        apply hr ⟨j,hh⟩
        change (3 : ℤ) ∣ b j-r
        omega
      exact Or.inr ⟨⟨j,hj3⟩,hb' ⟨j,hj3⟩ x hj⟩

/-- Every coarse ternary branch not containing actual modulus three has at
least four classes. This requires neither irredundance nor minimality. -/
theorem ternary_branch_card_four {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    4 ≤ Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} := by
  classical
  by_contra hsmall
  let K := {i : I // ¬ 3 ∣ m i}
  let J := {j : I // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r}
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  have hd (j : J) : 1 < m j/3 ∧ Odd (m j/3) := by
    have he : 3*(m j/3)=m j := Nat.mul_div_cancel' j.property.1
    have hm := hc.2.1 j
    have hne := hno j j.property.2
    refine ⟨by omega,hm.2.of_dvd_nat (Nat.div_dvd_of_dvd j.property.1)⟩
  have hdi : Function.Injective (fun j : J => m j/3) := by
    intro j k hjk
    change m j/3=m k/3 at hjk
    apply Subtype.ext
    apply hc.1
    have hj := Nat.mul_div_cancel' j.property.1
    have hk := Nat.mul_div_cancel' k.property.1
    omega
  apply not_cover_three_distinct_odd
    (fun i : K => m i) b (hc.1.comp Subtype.val_injective)
    (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : J => m j/3) (fun j => (a j-r)/3) hdi hd _ hb
  simp only [J,Fintype.card_subtype] at hsmall ⊢
  omega

#print axioms weight_mul_le
#print axioms composite_weight_le
#print axioms three_distinct_weight
#print axioms not_cover_three_distinct_no_three
#print axioms not_cover_three_distinct_odd
#print axioms ternary_branch_card_four
end Erdos7ThreeDistinctExceptions
