import Submission.EndpointCriterion

/-!
# Unconditional bounds for totient fibers

This file gives finite-candidate Euler bounds, odd-prime support capacity,
and the unconditional bound `Squarefree n → fiberCard n ≤ 4`.
All cardinalities use the existing `Erdos821Aux.fiberCard`.

The exact negation lemma concerns the original quantification over positive
**real** `ε`; it does not assert either the endpoint conjecture or its negation.
These are partial results, not a proof of the full endpoint conjecture.
This file does not import `Submission.Spec`, use its conjectural declarations,
or introduce any axioms. No eventual power gap for arbitrary large `n`
is asserted.

For squarefree `n ≥ 3`, the odd prime support of a preimage has one element
`p`. Euler's kernel formula and squarefreeness force the quotient by the
kernel to be `1` or `p`, giving `n = p - 1` or `n = p * (p - 1)`.
Thus all preimages lie in four explicit choices, with `p = n + 1` in the
first case and `p = Nat.sqrt n + 1` in the second. The small values `1, 2`
are handled separately, and the bound is sharp at `n = 6`.
-/

namespace Erdos821Aux

open Nat

/-- The zero totient fiber consists only of zero. -/
@[simp] theorem fiberCard_zero : fiberCard 0 = 1 := by
  simp [fiberCard, Nat.totient_eq_zero]

/-- The totient fiber at one has the two elements `1, 2`. -/
@[simp] theorem fiberCard_one : fiberCard 1 = 2 := by
  have hs : {m : ℕ | Nat.totient m = 1} = ({1, 2} : Set ℕ) := by
    ext m
    simp [Nat.totient_eq_one_iff]
  rw [fiberCard, hs]
  exact Set.ncard_pair (by decide)

/-- The exact logical negation is an eventual fixed power gap. -/
theorem not_endpoint_iff_eventual_power_gap :
    ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (fiberCard n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔ ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (fiberCard n : ℝ) ≤ (n : ℝ) ^ c := by
  classical
  constructor
  · intro h
    simp only [not_forall, Set.not_infinite] at h
    obtain ⟨ε, hε, hfinite⟩ := h
    have hε1 : ε < 1 := by
      by_contra hn
      have hinf : {n : ℕ | (fiberCard n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
        exact conjecture_for_epsilon_ge_one ε (le_of_not_gt hn)
      exact hfinite.not_infinite hinf
    refine ⟨1 - ε, by linarith, by linarith, ?_⟩
    obtain ⟨N, hN⟩ := Set.finite_iff_bddAbove.mp hfinite
    refine ⟨N + 1, ?_⟩
    intro n hn
    apply le_of_not_gt
    intro hgood
    have hupper := hN hgood
    omega
  · rintro ⟨c, hc0, hc1, N, hN⟩ h
    have hpos : (0 : ℝ) < 1 - c := by linarith
    have hinf := h (1 - c) hpos
    obtain ⟨n, hgood, hn⟩ := Set.infinite_iff_exists_gt.mp hinf N
    have he : (1 : ℝ) - (1 - c) = c := by ring
    change (fiberCard n : ℝ) > (n : ℝ) ^ (1 - (1 - c)) at hgood
    rw [he] at hgood
    exact (not_lt_of_ge (hN n (le_of_lt hn))) hgood

/-- The candidate-prime set is finite for every nonzero fiber value. -/
theorem candidate_primes_finite {n : ℕ} (hn : n ≠ 0) :
    {p : ℕ | p.Prime ∧ p - 1 ∣ n}.Finite := by
  apply (Set.finite_Iic (n + 1)).subset
  intro p hp
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp.2
  have hp2 := hp.1.two_le
  change p ≤ n + 1
  omega

/-- Every prime in a positive totient preimage is genuinely admissible. -/
theorem prime_factor_candidate {m n p : ℕ} (hm : Nat.totient m = n)
    (hp : p ∈ m.primeFactors) : p.Prime ∧ p - 1 ∣ n := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  refine ⟨hprime, ?_⟩
  have hdiv := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
  rwa [Nat.totient_prime hprime, hm] at hdiv

/-- A sharper finite Euler bound: prime-power geometric factors are unnecessary,
    since equal prime support and equal totient determine the preimage. -/
theorem squarefree_weighted_bound {n : ℕ} (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s)
    (P : Finset ℕ)
    (hP : ∀ m : ℕ, Nat.totient m = n → ∀ p ∈ m.primeFactors, p ∈ P) :
    (fiberCard n : ℝ) * (n : ℝ) ^ (-s) ≤
      ∏ p ∈ P, (1 + ((p - 1 : ℕ) : ℝ) ^ (-s)) := by
  classical
  let F : Finset ℕ := (totient_fiber_finite n).toFinset
  let w : Finset ℕ → ℝ := fun S => ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) ^ (-s)
  have hF : ∀ m ∈ F, Nat.totient m = n := by
    intro m hm
    exact (Set.Finite.mem_toFinset (totient_fiber_finite n)).mp hm
  have hcard : F.card = fiberCard n := by
    exact (Set.ncard_eq_toFinset_card _ (totient_fiber_finite n)).symm
  have hnonneg : ∀ S : Finset ℕ, 0 ≤ w S := by
    intro S
    exact Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hweight : ∀ m ∈ F, (n : ℝ) ^ (-s) ≤ w m.primeFactors := by
    intro m hm
    have hdiv := totient_rad_dvd m
    rw [hF m hm] at hdiv
    have hle := Nat.le_of_dvd hn hdiv
    have hpos : (0 : ℝ) < (Nat.totient (rad m) : ℝ) := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (squarefree_rad m).ne_zero))
    have hprod : (∏ p ∈ m.primeFactors, ((p - 1 : ℕ) : ℝ)) =
        (Nat.totient (rad m) : ℝ) := by
      exact_mod_cast (totient_rad m).symm
    dsimp only [w]
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg _) (-s), hprod]
    exact Real.rpow_le_rpow_of_nonpos hpos (by exact_mod_cast hle) (by linarith)
  have hinj : Set.InjOn Nat.primeFactors F := by
    intro a ha b hb hab
    exact eq_of_primeFactors_eq_of_totient_eq hab ((hF a ha).trans (hF b hb).symm)
  have hsubset : F.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powerset.mpr (hP m (hF m hm))
  calc
    (fiberCard n : ℝ) * (n : ℝ) ^ (-s) = ∑ m ∈ F, (n : ℝ) ^ (-s) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ ∑ m ∈ F, w m.primeFactors := Finset.sum_le_sum hweight
    _ = ∑ S ∈ F.image Nat.primeFactors, w S := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ S ∈ P.powerset, w S :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun S _ _ => hnonneg S)
    _ = ∏ p ∈ P, (1 + ((p - 1 : ℕ) : ℝ) ^ (-s)) := by
      exact (Finset.prod_one_add P).symm

/-- The weighted Euler bound for the canonical candidate-prime set. -/
theorem canonical_squarefree_weighted_bound {n : ℕ} (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) :
    (fiberCard n : ℝ) * (n : ℝ) ^ (-s) ≤
      ∏ p ∈ (candidate_primes_finite hn.ne').toFinset,
        (1 + ((p - 1 : ℕ) : ℝ) ^ (-s)) := by
  apply squarefree_weighted_bound hn s hs
  intro m hm p hp
  exact (Set.Finite.mem_toFinset (candidate_primes_finite hn.ne')).mpr
    (prime_factor_candidate hm hp)

/-- Each distinct odd support prime uses one factor of two in the totient. -/
theorem two_pow_odd_support_card_dvd_totient (m : ℕ) :
    2 ^ (m.primeFactors.erase 2).card ∣ Nat.totient m := by
  have hd : (∏ p ∈ m.primeFactors.erase 2, (2 : ℕ)) ∣
      ∏ p ∈ m.primeFactors.erase 2, (p - 1) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    obtain ⟨hp2, hpm⟩ := Finset.mem_erase.mp hp
    exact (Nat.prime_of_mem_primeFactors hpm).even_sub_one hp2 |>.two_dvd
  have hsub : (∏ p ∈ m.primeFactors.erase 2, (p - 1)) ∣
      ∏ p ∈ m.primeFactors, (p - 1) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset 2 m.primeFactors)
  have hprod := hd.trans hsub
  rw [← totient_rad m] at hprod
  simpa only [Finset.prod_const] using hprod.trans (totient_rad_dvd m)

/-- The two-adic exponent of a nonzero totient value bounds odd support. -/
theorem odd_support_capacity {m n : ℕ} (hn : n ≠ 0)
    (hm : Nat.totient m = n) :
    (m.primeFactors.erase 2).card ≤ n.factorization 2 := by
  apply Nat.prime_two.pow_dvd_iff_le_factorization hn |>.mp
  rw [← hm]
  exact two_pow_odd_support_card_dvd_totient m

private theorem eq_one_or_eq_of_squarefree_support {a p : ℕ} (ha : Squarefree a)
    (hs : a.primeFactors ⊆ {p}) : a = 1 ∨ a = p := by
  rcases Finset.subset_singleton_iff.mp hs with hempty | hsingle
  · left
    simpa only [hempty, Finset.prod_empty] using
      (Nat.prod_primeFactors_of_squarefree ha).symm
  · right
    simpa only [hsingle, Finset.prod_singleton] using
      (Nat.prod_primeFactors_of_squarefree ha).symm

private theorem le_two_of_squarefree_totient_of_odd_support_empty {m n : ℕ}
    (hn : Squarefree n) (hm : Nat.totient m = n)
    (hs : m.primeFactors.erase 2 = ∅) : n ≤ 2 := by
  have hm0 : m ≠ 0 := by
    intro h0
    exact hn.ne_zero (by simpa only [h0, Nat.totient_zero] using hm.symm)
  have hrad : Nat.totient (rad m) = 1 := by
    rw [totient_rad, ← Finset.prod_erase m.primeFactors (f := fun p : ℕ => p - 1) (a := 2)
      (by decide : (2 : ℕ) - 1 = 1), hs, Finset.prod_empty]
  have hdiv : n ∣ m := by
    rw [totient_eq_div_rad_mul_totient_rad, hrad, Nat.mul_one] at hm
    exact hm ▸ Nat.div_dvd_of_dvd (rad_dvd m)
  have hsub : m.primeFactors ⊆ {2} := by
    exact Finset.subset_singleton_iff.mpr ((Finset.erase_eq_empty_iff _ _).mp hs)
  rcases eq_one_or_eq_of_squarefree_support hn
    ((Nat.primeFactors_mono hdiv hm0).trans hsub) with h | h <;> omega

private theorem squarefree_totient_preimage_prime {m n : ℕ} (hn : Squarefree n)
    (hn3 : 3 ≤ n) (hm : Nat.totient m = n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((n = p - 1 ∧ (m = p ∨ m = 2 * p)) ∨
        (n = p * (p - 1) ∧ (m = p ^ 2 ∨ m = 2 * p ^ 2))) := by
  have hm0 : m ≠ 0 := by
    intro h0
    exact hn.ne_zero (by simpa only [h0, Nat.totient_zero] using hm.symm)
  have hcap : (m.primeFactors.erase 2).card ≤ 1 :=
    (odd_support_capacity hn.ne_zero hm).trans (hn.natFactorization_le_one 2)
  have hnonempty : (m.primeFactors.erase 2).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have := le_two_of_squarefree_totient_of_odd_support_empty hn hm he
    omega
  have hcard : (m.primeFactors.erase 2).card = 1 := by
    have := Finset.card_pos.mpr hnonempty
    omega
  obtain ⟨p, hs⟩ := Finset.card_eq_one.mp hcard
  have hpm : p ∈ m.primeFactors.erase 2 := by
    rw [hs]
    exact Finset.mem_singleton_self p
  obtain ⟨hp2, hpMem⟩ := Finset.mem_erase.mp hpm
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hrad : rad m = p ∨ rad m = 2 * p := by
    dsimp only [rad]
    by_cases h2 : 2 ∈ m.primeFactors
    · right
      rw [← Finset.mul_prod_erase m.primeFactors (fun p => p) h2, hs,
        Finset.prod_singleton]
    · left
      rw [← Finset.erase_eq_of_notMem h2, hs, Finset.prod_singleton]
  have hradPhi : Nat.totient (rad m) = p - 1 := by
    rw [totient_rad, ← Finset.prod_erase m.primeFactors (f := fun p : ℕ => p - 1) (a := 2)
      (by decide : (2 : ℕ) - 1 = 1), hs, Finset.prod_singleton]
  let q := m / rad m
  have hqn : q * (p - 1) = n := by
    have he := hm
    rw [totient_eq_div_rad_mul_totient_rad, hradPhi] at he
    exact he
  have hsq : Squarefree (q * (p - 1)) := hqn.symm ▸ hn
  have hcop : Nat.Coprime q (p - 1) := Nat.coprime_of_squarefree_mul hsq
  have hq2 : ¬ 2 ∣ q := by
    intro hd
    exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < (2 : ℕ)) hd
      (hp.even_sub_one hp2).two_dvd hcop
  have hdiv : q ∣ m := Nat.div_dvd_of_dvd (rad_dvd m)
  have hqSupport : q.primeFactors ⊆ {p} := by
    intro r hr
    have hrm := Nat.primeFactors_mono hdiv hm0 hr
    have hr2 : r ≠ 2 := by
      intro he
      exact hq2 (he ▸ Nat.dvd_of_mem_primeFactors hr)
    have hrErase := Finset.mem_erase.mpr ⟨hr2, hrm⟩
    rwa [hs] at hrErase
  have hmRec : m = q * rad m := (Nat.div_mul_cancel (rad_dvd m)).symm
  refine ⟨p, hp, hp2, ?_⟩
  rcases eq_one_or_eq_of_squarefree_support hsq.of_mul_left hqSupport with hq | hq
  · left
    refine ⟨by simpa only [hq, one_mul] using hqn.symm, ?_⟩
    rcases hrad with hrad | hrad
    · left
      rw [hmRec, hq, one_mul, hrad]
    · right
      rw [hmRec, hq, one_mul, hrad]
  · right
    refine ⟨by simpa only [hq] using hqn.symm, ?_⟩
    rcases hrad with hrad | hrad
    · left
      rw [hmRec, hq, hrad, pow_two]
    · right
      rw [hmRec, hq, hrad, pow_two]
      ring

/-- At squarefree values at least three, every totient preimage belongs to
four explicit choices. -/
theorem totient_preimage_of_squarefree_ge_three {m n : ℕ} (hn : Squarefree n)
    (hn3 : 3 ≤ n) (hm : Nat.totient m = n) :
    m = n + 1 ∨ m = 2 * (n + 1) ∨
      m = (n.sqrt + 1) ^ 2 ∨ m = 2 * (n.sqrt + 1) ^ 2 := by
  obtain ⟨p, hp, _, hcase⟩ := squarefree_totient_preimage_prime hn hn3 hm
  have hpPred : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  rcases hcase with ⟨hnp, hmp⟩ | ⟨hnp, hmp⟩
  · have he : p = n + 1 := by omega
    rcases hmp with h | h
    · exact Or.inl (he ▸ h)
    · exact Or.inr (Or.inl (he ▸ h))
  · have hsqrt : p - 1 = n.sqrt := by
      apply Nat.eq_sqrt'.mpr
      constructor <;> nlinarith [hp.two_le]
    have he : p = n.sqrt + 1 := by omega
    rcases hmp with h | h
    · exact Or.inr (Or.inr (Or.inl (he ▸ h)))
    · exact Or.inr (Or.inr (Or.inr (he ▸ h)))

/-- The totient fiber at two has the three elements `3, 4, 6`. -/
@[simp] theorem fiberCard_two : fiberCard 2 = 3 := by
  have hs : {m : ℕ | Nat.totient m = 2} = ({3, 4, 6} : Set ℕ) := by
    ext m
    constructor
    · intro hm
      change Nat.totient m = 2 at hm
      have hb : m ≤ 8 := by
        simpa only [hm] using totient_bound m
      have henum : ∀ k : Fin 9, Nat.totient k.val = 2 →
          k.val ∈ ({3, 4, 6} : Set ℕ) := by decide
      exact henum ⟨m, Nat.lt_succ_of_le hb⟩ hm
    · intro hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl | rfl <;> decide
  rw [fiberCard, hs, Set.ncard_insert_of_notMem (by decide : (3 : ℕ) ∉ ({4, 6} : Set ℕ)),
    Set.ncard_pair (by decide : (4 : ℕ) ≠ 6)]

/-- Unconditionally, every squarefree totient value has at most four preimages.
This is a partial fiber bound, not the full endpoint conjecture. -/
theorem fiberCard_le_four_of_squarefree {n : ℕ} (hn : Squarefree n) : fiberCard n ≤ 4 := by
  classical
  by_cases h1 : n = 1
  · subst n
    rw [fiberCard_one]
    decide
  by_cases h2 : n = 2
  · subst n
    rw [fiberCard_two]
    decide
  have hn3 : 3 ≤ n := by
    have := Nat.pos_of_ne_zero hn.ne_zero
    omega
  let T : Finset ℕ :=
    {n + 1, 2 * (n + 1), (n.sqrt + 1) ^ 2, 2 * (n.sqrt + 1) ^ 2}
  have hsub : {m : ℕ | Nat.totient m = n} ⊆ (T : Set ℕ) := by
    intro m hm
    simpa only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using
      totient_preimage_of_squarefree_ge_three hn hn3 hm
  calc
    fiberCard n ≤ (T : Set ℕ).ncard := Set.ncard_le_ncard hsub T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ 4 := Finset.card_le_four

/-- The bound four is attained at the squarefree value six. -/
@[simp] theorem fiberCard_six : fiberCard 6 = 4 := by
  have hsix : Squarefree (6 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr
      ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  apply Nat.le_antisymm (fiberCard_le_four_of_squarefree hsix)
  have hsub : (({7, 9, 14, 18} : Finset ℕ) : Set ℕ) ⊆
      {m : ℕ | Nat.totient m = 6} := by
    intro m hm
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide
  have hc := Set.ncard_le_ncard hsub (totient_fiber_finite 6)
  rw [Set.ncard_coe_finset, show ({7, 9, 14, 18} : Finset ℕ).card = 4 by decide] at hc
  exact hc

end Erdos821Aux

#print axioms Erdos821Aux.fiberCard_zero
#print axioms Erdos821Aux.fiberCard_one
#print axioms Erdos821Aux.not_endpoint_iff_eventual_power_gap
#print axioms Erdos821Aux.candidate_primes_finite
#print axioms Erdos821Aux.prime_factor_candidate
#print axioms Erdos821Aux.squarefree_weighted_bound
#print axioms Erdos821Aux.canonical_squarefree_weighted_bound
#print axioms Erdos821Aux.two_pow_odd_support_card_dvd_totient
#print axioms Erdos821Aux.odd_support_capacity
#print axioms Erdos821Aux.totient_preimage_of_squarefree_ge_three
#print axioms Erdos821Aux.fiberCard_two
#print axioms Erdos821Aux.fiberCard_le_four_of_squarefree
#print axioms Erdos821Aux.fiberCard_six
