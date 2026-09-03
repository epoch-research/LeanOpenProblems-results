import Submission.PowerfulTotient

/-!
# Fixed first-power arity gives subpower multiplicity

Allowing arbitrarily many higher prime powers does not help a family whose
number of input primes occurring exactly once is bounded. Its size in any
fixed totient fiber is bounded by a fixed divisor polynomial. This is a
structural restriction, not a settlement of Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

noncomputable def gFirstPowerAtMost (r n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n ∧ (firstPowerSupport m).card ≤ r}.ncard

lemma finite_firstPowerAtMost_fiber (r n : ℕ) :
    {m : ℕ | Nat.totient m = n ∧ (firstPowerSupport m).card ≤ r}.Finite :=
  (finite_totient_fiber n).subset (fun _ hm => hm.1)

lemma firstPowerSupport_subset_shiftedPrimeDivisors {m n : ℕ} (hn : 0 < n)
    (hφ : Nat.totient m = n) : firstPowerSupport m ⊆ shiftedPrimeDivisors n := by
  have h := primeFactors_mem_admissibleSupports hn hφ
  exact (Finset.filter_subset _ _).trans
    (Finset.mem_powerset.mp (Finset.mem_filter.mp h).1)

/-- Finite form: no bound on the number or size of higher input prime powers
is required. Only the number of first-power primes is bounded. -/
lemma card_fiber_firstPowerAtMost_le (n r : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS : ∀ m ∈ S, Nat.totient m = n ∧ (firstPowerSupport m).card ≤ r) :
    S.card ≤ (r+1) * (n.divisors.card+1)^r := by
  have hinj : Set.InjOn firstPowerSupport (S : Set ℕ) := by
    intro a ha b hb he
    exact firstPowerSupport_injOn_totient_fiber n (hS a ha).1 (hS b hb).1 he
  have hb : (S.image firstPowerSupport).card ≤
      (r+1) * ((shiftedPrimeDivisors n).card+1)^r := by
    apply card_bounded_subset_family_le
    intro T hT
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hT
    exact ⟨firstPowerSupport_subset_shiftedPrimeDivisors hn (hS m hm).1, (hS m hm).2⟩
  rw [Finset.card_image_of_injOn hinj] at hb
  exact hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (shiftedPrimeDivisors_card_le_divisors_card hn) 1) _))

lemma gFirstPowerAtMost_le_divisor_polynomial (n r : ℕ) (hn : 0 < n) :
    gFirstPowerAtMost r n ≤ (r+1) * (n.divisors.card+1)^r := by
  let S := (finite_firstPowerAtMost_fiber r n).toFinset
  have hS (m : ℕ) : m ∈ S ↔ Nat.totient m = n ∧ (firstPowerSupport m).card ≤ r :=
    (finite_firstPowerAtMost_fiber r n).mem_toFinset
  have hc : S.card = gFirstPowerAtMost r n :=
    (Set.ncard_eq_toFinset_card _ (finite_firstPowerAtMost_fiber r n)).symm
  rw [← hc]
  exact card_fiber_firstPowerAtMost_le n r hn S (fun m hm => (hS m).mp hm)

lemma eventually_firstPower_divisor_polynomial_le (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ((r+1 : ℕ) : ℝ) * ((n.divisors.card : ℝ)+1)^r ≤ (n : ℝ)^δ := by
  let e := δ / (2*((r : ℝ)+1))
  have he : 0 < e := div_pos hδ (by positivity)
  let C : ℝ := ((r : ℝ)+1)*2^(r+1)
  have heq : e*((r : ℝ)+1) = δ/2 := by dsimp [e]; field_simp
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_card_divisors_le_rpow e he,
    hlim.eventually (eventually_ge_atTop C), eventually_ge_atTop 1] with n hnD hnC hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by positivity
  have hge : (1 : ℝ) ≤ (n : ℝ)^e := Real.one_le_rpow hnR he.le
  have hpower : ((n : ℝ)^e)^(r+1) = (n : ℝ)^(δ/2) := by
    rw [← Real.rpow_natCast ((n : ℝ)^e) (r+1), ← Real.rpow_mul hnRpos.le]
    push_cast
    rw [heq]
  calc
    ((r+1 : ℕ) : ℝ) * ((n.divisors.card : ℝ)+1)^r ≤
        ((r : ℝ)+1) * ((n.divisors.card : ℝ)+1)^(r+1) := by
      push_cast
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀
        (by linarith [Nat.cast_nonneg (α := ℝ) n.divisors.card]) (Nat.le_succ _)
    _ ≤ ((r : ℝ)+1) * (2*(n : ℝ)^e)^(r+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = C*(n : ℝ)^(δ/2) := by
      rw [mul_pow, hpower]
      dsimp [C]
      ring
    _ ≤ (n : ℝ)^(δ/2)*(n : ℝ)^(δ/2) :=
      mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnRpos.le _)
    _ = (n : ℝ)^δ := by rw [← Real.rpow_add hnRpos]; congr 1; ring

/-- Every fixed first-power arity contributes less than any fixed positive
power of the output, eventually. -/
theorem eventually_gFirstPowerAtMost_le_rpow (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (gFirstPowerAtMost r n : ℝ) ≤ (n : ℝ)^δ := by
  filter_upwards [eventually_firstPower_divisor_polynomial_le r δ hδ,
    eventually_ge_atTop 1] with n hn hn1
  have hb : (gFirstPowerAtMost r n : ℝ) ≤
      ((r+1 : ℕ) : ℝ) * ((n.divisors.card : ℝ)+1)^r := by
    exact_mod_cast gFirstPowerAtMost_le_divisor_polynomial n r (by omega)
  exact hb.trans hn

noncomputable def gFirstPowerAbove (r n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n ∧ r < (firstPowerSupport m).card}.ncard

lemma g_eq_firstPower_partition (r n : ℕ) :
    g n = gFirstPowerAtMost r n + gFirstPowerAbove r n := by
  let F := (finite_totient_fiber n).toFinset
  have hF (m : ℕ) : m ∈ F ↔ Nat.totient m = n :=
    (finite_totient_fiber n).mem_toFinset
  have he₁ : {m : ℕ | Nat.totient m = n ∧ (firstPowerSupport m).card ≤ r} =
      ↑(F.filter (fun m => (firstPowerSupport m).card ≤ r)) := by
    ext m
    simp only [Finset.mem_coe, Finset.mem_filter, hF, Set.mem_setOf_eq]
  have he₂ : {m : ℕ | Nat.totient m = n ∧ r < (firstPowerSupport m).card} =
      ↑(F.filter (fun m => ¬(firstPowerSupport m).card ≤ r)) := by
    ext m
    simp only [Finset.mem_coe, Finset.mem_filter, hF, Set.mem_setOf_eq, not_le]
  have hc : F.card = g n := (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
  rw [gFirstPowerAtMost, gFirstPowerAbove, he₁, he₂, Set.ncard_coe_finset,
    Set.ncard_coe_finset, Finset.card_filter_add_card_filter_not]
  exact hc.symm

/-- In every sufficiently large polynomial-size fiber, more than half of
its inputs have more than any prescribed fixed number of first-power primes. -/
theorem eventually_large_fiber_most_firstPowerAbove (r : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^α < (g n : ℝ) →
      (g n : ℝ) < 2*(gFirstPowerAbove r n : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(α/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hα)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gFirstPowerAtMost_le_rpow r (α/2) (half_pos hα),
    hlim.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hn h2 hn1 hbig
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have heq : (n : ℝ)^α = ((n : ℝ)^(α/2))^2 := by
    rw [← Real.rpow_mul_natCast hnpos.le]
    congr 1
    norm_num
  have hpart : (g n : ℝ) = (gFirstPowerAtMost r n : ℝ)+(gFirstPowerAbove r n : ℝ) := by
    exact_mod_cast g_eq_firstPower_partition r n
  rw [heq] at hbig
  nlinarith

end Erdos821
