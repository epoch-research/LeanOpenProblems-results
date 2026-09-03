import Submission.CertifiedBinaryFamilySieve

/-!
A single positive-density sieve for every primitive parameter, every common-
factor normalization, and every integer dilation of a fixed certified binary
family of degree at least three. The result remains familywise.
-/
namespace Erdos1206.AllNormalizationsFamilySieve
open MvPolynomial CertifiedBinaryFamilySieve NormalizedBinaryFamilySieve
open scoped Classical

noncomputable def normalized {m : ℕ} (P : Fin m → BinaryForm) (g : ℕ)
    (p : ℤ × ℤ) (i : Fin m) : ℤ := eval ![p.1,p.2] (P i)/(g:ℤ)

def parameters {m : ℕ} (P : Fin m → BinaryForm) (g : ℕ) : Set (ℤ × ℤ) :=
  {p | IsCoprime p.1 p.2 ∧ (∀ i, (g:ℤ) ∣ eval ![p.1,p.2] (P i)) ∧
    1 < rootHeight (normalized P g p)}

private lemma normalization_eq {m : ℕ} {P : Fin m → BinaryForm} {g : ℕ} {p : ℤ × ℤ}
    (hg : ∀ i, (g:ℤ) ∣ eval ![p.1,p.2] (P i)) (i : Fin m) :
    eval ![p.1,p.2] (P i)=(g:ℤ)*normalized P g p i := (Int.mul_ediv_cancel' (hg i)).symm

/-- The set includes outputs from every admissible common divisor, not one
arbitrarily selected normalization. Divisibility of all such divisors by R
makes this a finite union of summable parameter families. -/
theorem all_normalizations_summable {m d n : ℕ} (hd : 3 ≤ d)
    {P H K : Fin m → BinaryForm} {R : ℤ} (hR : R ≠ 0)
    (hP : ∀ i, (P i).IsHomogeneous d)
    (hH : ∑ i, H i*P i=C R*X 0^n) (hK : ∑ i, K i*P i=C R*X 1^n) :
    ∃ B : Set ℕ, 1 ∉ B ∧ Summable (fun k : ℕ => if k ∈ B then (1:ℝ)/k else 0) ∧
      ∀ (p : ℤ × ℤ) (g : ℕ), p ∈ parameters P g → rootHeight (normalized P g p) ∈ B := by
  classical
  let I := {g : ℕ // g ∈ R.natAbs.divisors}
  let B : Set ℕ := ⋃ g : I, Set.range (fun p : parameters P g.val =>
    rootHeight (normalized P g.val p.val))
  have hgs (g : I) : Summable (fun k : ℕ =>
      if k ∈ Set.range (fun p : parameters P g.val => rootHeight (normalized P g.val p.val))
      then (1:ℝ)/k else 0) := by
    exact certified_maxima_summable hd hR hP hH hK (fun p => p.2.1)
      (fun p => normalized P g.val p.val) (fun _ => (g.val:ℤ))
      (fun p => normalization_eq p.2.2.1)
  have h1 : 1 ∉ B := by
    rintro h
    obtain ⟨g,p,hp⟩ := Set.mem_iUnion.mp h
    have hh := p.2.2.2
    change rootHeight (normalized P g.val p.val)=1 at hp
    omega
  have hsum : Summable (fun k : ℕ => if k ∈ B then (1:ℝ)/k else 0) := by
    have hs := summable_sum (s := (Finset.univ : Finset I)) (fun g _ => hgs g)
    apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ hs
    intro k
    by_cases hk : k ∈ B
    · rw [if_pos hk]
      obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hk
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset I))
        (f := fun g => if k ∈ Set.range (fun p : parameters P g.val =>
          rootHeight (normalized P g.val p.val)) then (1:ℝ)/k else 0)
        (fun _ _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ g)
      simpa only [if_pos hg] using hh
    · rw [if_neg hk]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  refine ⟨B,h1,hsum,fun p g hp => ?_⟩
  have hgR : (g:ℤ) ∣ R := normalized_divisor_dvd hH hK hp.1 (normalization_eq hp.2.1)
  have hgI : g ∈ R.natAbs.divisors := Nat.mem_divisors.mpr
    ⟨Int.natCast_dvd.mp hgR,Int.natAbs_ne_zero.mpr hR⟩
  exact Set.mem_iUnion.mpr ⟨⟨g,hgI⟩,⟨⟨p,hp⟩,rfl⟩⟩

/-- A fixed higher-degree certified family cannot force a collision in
every positive-density set, even when all integer normalizations and dilations
are allowed. -/
theorem positive_density_avoids_all_normalizations {m d n : ℕ} (hm : 0 < m) (hd : 3 ≤ d)
    {P H K : Fin m → BinaryForm} {R : ℤ} (hR : R ≠ 0)
    (hP : ∀ i, (P i).IsHomogeneous d)
    (hH : ∑ i, H i*P i=C R*X 0^n) (hK : ∑ i, K i*P i=C R*X 1^n) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ (p : ℤ × ℤ) (g t : ℕ), p ∈ parameters P g →
        ∃ i : Fin m, t*(normalized P g p i).natAbs ∉ A := by
  obtain ⟨B,h1,hB,hcover⟩ := all_normalizations_summable hd hR hP hH hK
  let A := divisorAvoider B
  have hden : 0 < A.lowerDensity := divisorAvoider_positive_density_of_summable h1 hB
  refine ⟨A,?_,hden,fun p g t hp => ?_⟩
  · by_contra hf
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hf)).liminf_eq
    linarith
  · obtain ⟨i,hi⟩ := rootHeight_attained hm (normalized P g p)
    refine ⟨i,fun ht => ?_⟩
    apply ht.2 (rootHeight (normalized P g p)) (hcover p g hp)
    rw [hi]
    exact dvd_mul_left _ _

#print axioms all_normalizations_summable
#print axioms positive_density_avoids_all_normalizations
end Erdos1206.AllNormalizationsFamilySieve
