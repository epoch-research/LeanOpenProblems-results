import Mathlib

/-!
# Checked obstructions for a proposed Carmichael subset-product route

This file does not import `Submission.Spec`, does not use either of its
unfinished declarations, and does not prove or disprove Erdős 1057.

The results certify positive-arc obstructions to short zero sums and an
arithmetic obstruction to inverse-pair symmetrization of a common-multiplier
prime pool. No primality assumption is needed for the latter obstruction.
-/

open scoped BigOperators

namespace CarmichaelSubsetProductStudy

/-- Positive integer lifts cannot sum to zero modulo `M` before wrapping around. -/
theorem positive_lifts_sum_ne_zero
    {ι : Type*} {M h : ℕ} (s : Finset ι) (a : ι → ℕ)
    (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ h)
    (hsize : s.card * h < M) :
    (∑ i ∈ s, (a i : ZMod M)) ≠ 0 := by
  have hpos : 0 < ∑ i ∈ s, a i :=
    Finset.sum_pos (fun i hi ↦ (ha i hi).1) hne
  have hbound : (∑ i ∈ s, a i) ≤ s.card * h := by
    calc
      (∑ i ∈ s, a i) ≤ ∑ _i ∈ s, h :=
        Finset.sum_le_sum (fun i hi ↦ (ha i hi).2)
      _ = s.card * h := by simp
  intro hz
  have hz' : ((∑ i ∈ s, a i : ℕ) : ZMod M) = 0 := by
    simpa only [Nat.cast_sum] using hz
  have hdvd : M ∣ ∑ i ∈ s, a i :=
    (ZMod.natCast_eq_zero_iff _ _).mp hz'
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hdvd)) (hbound.trans_lt hsize)

/-- A positive-arc obstruction in any cyclic quotient obstructs a zero sum
in the original group. In multiplicative notation this obstructs product one. -/
theorem quotient_positive_lifts_sum_ne_zero
    {ι A : Type*} [AddCommMonoid A] {M h : ℕ}
    (s : Finset ι) (g : ι → A) (π : A →+ ZMod M) (a : ι → ℕ)
    (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ h)
    (hlift : ∀ i ∈ s, π (g i) = (a i : ZMod M))
    (hsize : s.card * h < M) :
    (∑ i ∈ s, g i) ≠ 0 := by
  intro hz
  apply positive_lifts_sum_ne_zero s a hne ha hsize
  calc
    (∑ i ∈ s, (a i : ZMod M)) = ∑ i ∈ s, π (g i) :=
      Finset.sum_congr rfl (fun i hi ↦ (hlift i hi).symm)
    _ = π (∑ i ∈ s, g i) := (map_sum π _ _).symm
    _ = 0 := by rw [hz, map_zero]

/-- A diagonal strip in a product of two cyclic groups has no short zero sum.
For prime `M` its coordinate projections are uniform, as proved in the note. -/
theorem diagonal_strip_no_short_zero_sum
    {M h : ℕ} [NeZero M] (s : Finset (ZMod M × ZMod M))
    (hne : s.Nonempty)
    (hs : ∀ x ∈ s, 0 < (x.1 + x.2).val ∧ (x.1 + x.2).val ≤ h)
    (hsize : s.card * h < M) :
    (∑ x ∈ s, x) ≠ 0 := by
  let π : (ZMod M × ZMod M) →+ ZMod M :=
    { toFun := fun x ↦ x.1 + x.2
      map_zero' := by simp
      map_add' := by intro x y; dsimp; abel }
  apply quotient_positive_lifts_sum_ne_zero s (fun x ↦ x) π
    (fun x ↦ (x.1 + x.2).val) hne hs
  · intro x _hx
    exact (ZMod.natCast_zmod_val (x.1 + x.2)).symm
  · exact hsize

/-- The concrete strip modulo 101 has no nonempty zero sum of length at most 10. -/
theorem diagonal_strip_101
    (s : Finset (ZMod 101 × ZMod 101)) (hne : s.Nonempty)
    (hs : ∀ x ∈ s, 0 < (x.1 + x.2).val ∧ (x.1 + x.2).val ≤ 10)
    (hsize : s.card ≤ 10) :
    (∑ x ∈ s, x) ≠ 0 := by
  apply diagonal_strip_no_short_zero_sum s hne hs
  calc
    s.card * 10 ≤ 10 * 10 := Nat.mul_le_mul_right 10 hsize
    _ < 101 := by norm_num

/-- The interval `1,...,N` is zero-sum-free modulo any `M > N^2`.
The stronger threshold `N*(N+1)/2 < M` is not needed for the examples. -/
theorem interval_zero_sum_free
    {M N : ℕ} (s : Finset ℕ) (hne : s.Nonempty)
    (hsub : s ⊆ Finset.Icc 1 N) (hM : N * N < M) :
    (∑ i ∈ s, (i : ZMod M)) ≠ 0 := by
  have hcard : s.card ≤ N := by
    calc
      s.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
      _ = N := by simp
  apply positive_lifts_sum_ne_zero s (fun i ↦ i) hne
  · intro i hi
    have hb := Finset.mem_Icc.mp (hsub hi)
    exact ⟨by omega, hb.2⟩
  · exact (Nat.mul_le_mul_right N hcard).trans_lt hM

/-- If `d,e | L` and `k` is coprime to `L`, the residues `kd+1` and
`ke+1` can be mutual inverses only if `d=e`. Thus distinct primes in this
pool cannot be paired with their inverses. Squarefreeness is not required. -/
theorem common_multiplier_inverse_pair_eq
    {k L d e : ℕ} (hk : Nat.Coprime k L) (hd : d ∣ L) (he : e ∣ L)
    (hprod : Nat.ModEq L ((k * d + 1) * (k * e + 1)) 1) :
    d = e := by
  have hexpand : (k * d + 1) * (k * e + 1) =
      k * (k * d * e + d + e) + 1 := by ring
  rw [hexpand] at hprod
  have hzero : Nat.ModEq L (k * (k * d * e + d + e)) 0 :=
    Nat.ModEq.add_right_cancel' 1 (by simpa using hprod)
  have hdiv : L ∣ k * (k * d * e + d + e) :=
    Nat.modEq_zero_iff_dvd.mp hzero
  have hcancel : L ∣ k * d * e + d + e :=
    hk.symm.dvd_of_dvd_mul_left hdiv
  have hde : d ∣ e := by
    have hdtotal := hd.trans hcancel
    have hdprefix : d ∣ k * d * e + d := by
      exact dvd_add (by exact ⟨k * e, by ring⟩) (dvd_refl d)
    exact (Nat.dvd_add_iff_right hdprefix).mpr hdtotal
  have hed : e ∣ d := by
    have hetotal : e ∣ (k * d * e + e) + d := by
      convert he.trans hcancel using 1
      ring
    have heprefix : e ∣ k * d * e + e := by
      exact dvd_add (by exact ⟨k * d, by ring⟩) (dvd_refl e)
    exact (Nat.dvd_add_iff_right heprefix).mpr hetotal
  exact Nat.dvd_antisymm hde hed

#print axioms positive_lifts_sum_ne_zero
#print axioms quotient_positive_lifts_sum_ne_zero
#print axioms diagonal_strip_no_short_zero_sum
#print axioms diagonal_strip_101
#print axioms interval_zero_sum_free
#print axioms common_multiplier_inverse_pair_eq

end CarmichaelSubsetProductStudy
