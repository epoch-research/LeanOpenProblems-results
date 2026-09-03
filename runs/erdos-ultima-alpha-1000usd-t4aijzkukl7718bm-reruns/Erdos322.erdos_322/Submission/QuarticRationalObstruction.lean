import Submission.Spec

/-! Local obstructions to generic rational quartic norm amplification.
These obstructions do not settle the representation-count conjecture. -/
namespace Erdos322Research.QuarticRational

open Erdos322

private lemma fourth_mod_sixteen (x : ℕ) : x^4%16 ≤ 1 := by
  have h : ∀ r : Fin 16, (r.val^4)%16 ≤ 1 := by decide
  rw [Nat.pow_mod]
  exact h ⟨x%16,Nat.mod_lt _ (by decide)⟩

private lemma sum_fourth_mod_sixteen (a : Fin 4 → ℕ) : (∑ i, a i^4)%16 ≤ 4 := by
  have h0 := fourth_mod_sixteen (a 0)
  have h1 := fourth_mod_sixteen (a 1)
  have h2 := fourth_mod_sixteen (a 2)
  have h3 := fourth_mod_sixteen (a 3)
  simp only [Fin.sum_univ_four]
  omega

/-- A forbidden residue stays forbidden after multiplication by any nonzero
fourth power; denominators cannot remove the local obstruction. -/
theorem no_scaled_representation {n : ℕ} (hn : 4 < n%16) :
    ∀ d : ℕ, 0 < d → ∀ a : Fin 4 → ℕ, ∑ i, a i^4 ≠ n*d^4 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd a he
    by_cases heven : 2 ∣ d
    · have h16 : 16 ∣ n*d^4 := by
        obtain ⟨e,rfl⟩ := heven
        refine ⟨n*e^4,?_⟩
        ring
      have ha := two_dvd_all_of_fourth_sum he h16
      have hsmall : d/2 < d := Nat.div_lt_self hd (by decide)
      have hd' : 0 < d/2 := by
        have h2 : 2 ≤ d := Nat.le_of_dvd hd heven
        omega
      apply ih (d/2) hsmall hd' (fun i ↦ a i/2)
      have had (i : Fin 4) : 2*(a i/2)=a i := Nat.mul_div_cancel' (ha i)
      have hdd : 2*(d/2)=d := Nat.mul_div_cancel' heven
      have hh : 16*(∑ i, (a i/2)^4) = 16*(n*(d/2)^4) := by
        calc
          16*(∑ i, (a i/2)^4) = ∑ i, (2*(a i/2))^4 := by
            simp only [Fin.sum_univ_four]
            ring
          _ = ∑ i, a i^4 := by simp only [had]
          _ = n*d^4 := he
          _ = 16*(n*(d/2)^4) := by
            conv_lhs => rw [← hdd]
            ring
      omega
    · have hpow : d^4%16=1 := by
        have hmod : d%16 < 16 := Nat.mod_lt _ (by decide)
        have hodd : d%2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using heven
        have hodd' : (d%16)%2 ≠ 0 := by omega
        rw [Nat.pow_mod]
        interval_cases d%16 <;> norm_num at *
      have h := sum_fourth_mod_sixteen a
      rw [he,Nat.mul_mod,hpow] at h
      omega

private lemma rational_common_denominator (a : Fin 4 → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ b : Fin 4 → ℤ, ∀ i, (b i : ℚ) = d*a i := by
  let d := ∏ i, (a i).den
  have hd : 0 < d := Finset.prod_pos (fun i _ ↦ (a i).den_pos)
  refine ⟨d,hd,fun i ↦ (a i).num * (d/(a i).den),?_⟩
  intro i
  have hdiv : (a i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hmul : (a i).den*(d/(a i).den)=d := Nat.mul_div_cancel' hdiv
  have hm : ((a i).den : ℚ)*(d/(a i).den : ℕ)=d := by exact_mod_cast hmul
  push_cast
  calc
    ((a i).num : ℚ)*(d/(a i).den : ℕ) =
        (a i * (a i).den)*(d/(a i).den : ℕ) := by rw [Rat.mul_den_eq_num]
    _ = (d : ℚ)*a i := by rw [mul_assoc,hm,mul_comm]

/-- The modulo-sixteen obstruction applies to rational, not only integer,
representations by four fourth powers. -/
theorem no_rational_representation {n : ℕ} (hn : 4 < n%16)
    (a : Fin 4 → ℚ) : ∑ i, a i^4 ≠ (n : ℚ) := by
  intro he
  obtain ⟨d,hd,b,hb⟩ := rational_common_denominator a
  have hq : ∑ i, (b i : ℚ)^4 = (n : ℚ)*d^4 := by
    simp_rw [hb,mul_pow]
    rw [← Finset.mul_sum,he,mul_comm]
  have hz : ∑ i, (b i)^4 = (n : ℤ)*d^4 := by exact_mod_cast hq
  have hnabs : ∑ i, (b i).natAbs^4 = n*d^4 := by
    have hpow (i : Fin 4) : ((b i).natAbs : ℤ)^4 = (b i)^4 := by
      rw [Int.natCast_natAbs,← abs_pow,abs_of_nonneg (by positivity)]
    have hh : ∑ i, ((b i).natAbs : ℤ)^4 = (n : ℤ)*d^4 := by simpa only [hpow] using hz
    exact_mod_cast hh
  exact no_scaled_representation hn d hd (fun i ↦ (b i).natAbs) hnabs


private def seed : Fin 4 ⊕ Fin 4 → ℕ
  | .inl i => if i < 2 then 1 else 0
  | .inr i => if i < 3 then 1 else 0

private def grid (a : Fin 4 ⊕ Fin 4 → ℕ) (i : Fin 4 ⊕ Fin 4) : ℕ :=
  16*a i + seed i

private lemma grid_fourth_mod (a : Fin 4 ⊕ Fin 4 → ℕ) (i : Fin 4 ⊕ Fin 4) :
    (grid a i)^4%16 = (seed i)^4%16 := by
  unfold grid
  have hm : (16*a i+seed i)%16=seed i%16 := by omega
  rw [Nat.pow_mod,hm]
  exact (Nat.pow_mod (seed i) 4 16).symm

private lemma grid_product_mod (a : Fin 4 ⊕ Fin 4 → ℕ) :
    ((∑ i : Fin 4, (grid a (.inl i))^4) *
      (∑ i : Fin 4, (grid a (.inr i))^4))%16 = 6 := by
  have h0 := grid_fourth_mod a (.inl 0)
  have h1 := grid_fourth_mod a (.inl 1)
  have h2 := grid_fourth_mod a (.inl 2)
  have h3 := grid_fourth_mod a (.inl 3)
  have h4 := grid_fourth_mod a (.inr 0)
  have h5 := grid_fourth_mod a (.inr 1)
  have h6 := grid_fourth_mod a (.inr 2)
  have h7 := grid_fourth_mod a (.inr 3)
  norm_num [seed,Fin.lt_def] at h0 h1 h2 h3 h4 h5 h6 h7
  have hl : (∑ i : Fin 4, (grid a (.inl i))^4)%16=2 := by
    simp only [Fin.sum_univ_four]
    omega
  have hr : (∑ i : Fin 4, (grid a (.inr i))^4)%16=3 := by
    simp only [Fin.sum_univ_four]
    omega
  rw [Nat.mul_mod,hl,hr]

/-- Even with an arbitrary polynomial denominator and allowing poles, no
rational formula universally multiplies two four-coordinate quartic norms. -/
theorem no_generic_rational_product
    (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0) :
    ¬ (∀ x : Fin 4 ⊕ Fin 4 → ℚ,
      (∑ i, (MvPolynomial.eval x (P i))^4) =
        (MvPolynomial.eval x D)^4 * (∑ i : Fin 4, x (.inl i)^4) *
          (∑ i : Fin 4, x (.inr i)^4)) := by
  intro H
  apply hD
  let s (i : Fin 4 ⊕ Fin 4) : Set ℚ := Set.range (fun t : ℕ ↦ ((16*t+seed i : ℕ) : ℚ))
  have hs (i : Fin 4 ⊕ Fin 4) : (s i).Infinite := by
    apply Set.infinite_range_of_injective
    intro a b he
    change ((16*a+seed i : ℕ) : ℚ) = ((16*b+seed i : ℕ) : ℚ) at he
    have hh : 16*a+seed i=16*b+seed i := by exact_mod_cast he
    omega
  apply MvPolynomial.funext_set s hs
  intro x hx
  simp only [map_zero]
  by_contra hdx
  have hx' (i : Fin 4 ⊕ Fin 4) : ∃ t : ℕ, x i = ((16*t+seed i : ℕ) : ℚ) := by
    obtain ⟨t,ht⟩ := hx i (Set.mem_univ i)
    exact ⟨t,ht.symm⟩
  choose a ha using hx'
  have hg (i : Fin 4 ⊕ Fin 4) : x i = (grid a i : ℚ) := ha i
  let n : ℕ := (∑ i : Fin 4, (grid a (.inl i))^4) *
    (∑ i : Fin 4, (grid a (.inr i))^4)
  have hn : 4 < n%16 := by dsimp [n]; rw [grid_product_mod]; decide
  apply no_rational_representation hn (fun i ↦ MvPolynomial.eval x (P i)/MvPolynomial.eval x D)
  have he := H x
  have hnorm : (∑ i : Fin 4, x (.inl i)^4) * (∑ i : Fin 4, x (.inr i)^4) = (n : ℚ) := by
    simp only [hg,n,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow]
  calc
    ∑ i, (MvPolynomial.eval x (P i)/MvPolynomial.eval x D)^4 =
        (∑ i, (MvPolynomial.eval x (P i))^4)/(MvPolynomial.eval x D)^4 := by
      simp_rw [div_pow]
      rw [Finset.sum_div]
    _ = (n : ℚ) := by
      rw [he]
      rw [mul_assoc,hnorm]
      field_simp

/-- Polynomial-identity version of the same generic rational obstruction. -/
theorem no_rational_product_identity
    (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0) :
    ∑ i, (P i)^4 ≠ D^4 * (∑ i : Fin 4, (MvPolynomial.X (.inl i))^4) *
      (∑ i : Fin 4, (MvPolynomial.X (.inr i))^4) := by
  intro H
  apply no_generic_rational_product P D hD
  intro x
  have hh := congrArg (MvPolynomial.eval x) H
  simpa only [map_sum,map_mul,map_pow,MvPolynomial.eval_X] using hh


/-- High multiplicity does not even ensure rational representability after
squaring: clearing any denominator still leaves the local obstruction. -/
theorem infinitely_many_large_counts_with_rationally_unrepresented_square (M : ℕ) :
    {n : ℕ | M < primitiveRepresentationCount 4 n ∧
      ∀ a : Fin 4 → ℚ, ∑ i, a i^4 ≠ (n : ℚ)^2}.Infinite := by
  have hi : Function.Injective (fun t : ℕ ↦ 2*7^(4*(M+t))+1) := by
    intro a b he
    dsimp only at he
    have hp : 7^(4*(M+a))=7^(4*(M+b)) := by omega
    have hh := Nat.pow_right_injective (by decide : 2 ≤ 7) hp
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨t,rfl⟩
  dsimp only
  constructor
  · have := primitive_quartic_count_lower (M+t)
    omega
  · intro a
    have h7 : 7^(4*(M+t))%16=1 := by
      rw [pow_mul,Nat.pow_mod]
      norm_num
    have hn : (2*7^(4*(M+t))+1)%16=3 := by
      rw [Nat.add_mod,Nat.mul_mod,h7]
    have hs : 4 < ((2*7^(4*(M+t))+1)^2)%16 := by
      rw [Nat.pow_mod,hn]
      norm_num
    simpa only [Nat.cast_pow] using no_rational_representation hs a

/-- No threshold on the number of integer representations can make squaring
universally preserve representability, even if rational outputs are allowed. -/
theorem no_eventual_rational_square_amplification :
    ¬ (∃ M : ℕ, ∀ n : ℕ, M < representationCount 4 n →
      ∃ a : Fin 4 → ℚ, ∑ i, a i^4 = (n : ℚ)^2) := by
  rintro ⟨M,hM⟩
  obtain ⟨n,hn,hno⟩ :=
    (infinitely_many_large_counts_with_rationally_unrepresented_square M).nonempty
  have hh : M < representationCount 4 n :=
    hn.trans_le (primitiveRepresentationCount_le 4 n)
  obtain ⟨a,ha⟩ := hM n hh
  exact hno a ha

end Erdos322Research.QuarticRational


