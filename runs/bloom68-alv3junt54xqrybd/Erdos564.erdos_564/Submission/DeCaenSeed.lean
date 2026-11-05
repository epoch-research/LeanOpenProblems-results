import Submission.DensitySeed

/-!
# A direct finite de Caen seed bound

This file does not import `Submission.Spec` and assumes no density recurrence.
It proves the finite Turán covering bound in the `(r+1,r)` case, for an
arbitrary zero-one weighted family and arbitrary ambient finite set, then
applies it to the even quadruples of a two-colouring of triples.

## Source and parameters

`/corpus/src/math_9502238/cover.tex`, lines 48--51, states
`C(v,k,t) ≥ ((t+1)(v-t)/((k+1)(v-k))) * choose(v,t)/choose(k,t)`.
Lines 451--456 give `C(v,k,t) = T(v,v-t,v-k)`. Substitution gives
`T(N,ell,r)/choose(N,r) ≥ (N-ell+1)/((N-r+1)*choose(ell-1,r-1))`.
In particular, for `ell=5, r=4` the finite density is `(N-4)/(4*(N-3))`,
not merely the asymptotic `1/4`.

The related proof in `/corpus/src/2108.10406/codegreesquare2.tex`,
lines 2296--2314, counts adjacent edge/nonedge pairs by their common triple.
The proof below uses that elementary double count, not an imported de Caen
covering theorem. For `r=k+1`, let `E` be the edge count, `F` the nonedge
count, and `d(T)` the nonedge codegree of a `k`-set. Every `(k+2)`-set
contains an edge, so the adjacent mixed-pair count `X` is at least
`(N-k-1)*F`. Also
`X + sum_T d(T)^2 = (N-k)*(k+1)*F`, and Cauchy--Schwarz gives
`((k+1)*F)^2 ≤ choose(N,k)*sum_T d(T)^2`.
Cancellation (handling `F=0` separately) gives the finite bound.

The resulting monochromatic seed is
`M/choose(N,4) ≥ 1/16 - 13/(16*(N-3))` for `N ≥ 5`.
This is an unconditional asymptotic seed, not a proof of the proposed
multiplicity recurrence or of a Ramsey disproof.
-/

namespace Combinatorics.DensityRoute.DeCaen

open Finset SmallRamsey

universe u
variable {α : Type u} [DecidableEq α]

/-- Two distinct `(k+1)`-sets have as many common `k`-subsets as common
`(k+2)`-supersets: either one on each side, or zero on each side. -/
lemma adjacent_pair_card {V A B : Finset α} {k : ℕ}
    (hA : A ∈ V.powersetCard (k + 1)) (hB : B ∈ V.powersetCard (k + 1))
    (hne : A ≠ B) :
    ((V.powersetCard k).filter (fun T => T ⊆ A ∧ T ⊆ B)).card =
      ((V.powersetCard (k + 2)).filter (fun S => A ⊆ S ∧ B ⊆ S)).card := by
  obtain ⟨hAV, hAc⟩ := mem_powersetCard.mp hA
  obtain ⟨hBV, hBc⟩ := mem_powersetCard.mp hB
  have hI : (A ∩ B).card ≤ k := by
    have hle : (A ∩ B).card ≤ k + 1 :=
      (card_le_card inter_subset_left).trans hAc.le
    by_contra hn
    have heA : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left (by omega)
    have heB : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hne (heA.symm.trans heB)
  have hU := card_union_add_card_inter A B
  rw [hAc, hBc] at hU
  by_cases hIk : (A ∩ B).card = k
  · have hUk : (A ∪ B).card = k + 2 := by omega
    have hleft : (V.powersetCard k).filter (fun T => T ⊆ A ∧ T ⊆ B) =
        {A ∩ B} := by
      ext T
      simp only [mem_filter, mem_powersetCard, mem_singleton]
      constructor
      · rintro ⟨⟨_, hTc⟩, hTA, hTB⟩
        exact eq_of_subset_of_card_le (subset_inter hTA hTB) (by omega)
      · rintro rfl
        exact ⟨⟨inter_subset_left.trans hAV, hIk⟩, inter_subset_left, inter_subset_right⟩
    have hright : (V.powersetCard (k + 2)).filter (fun S => A ⊆ S ∧ B ⊆ S) =
        {A ∪ B} := by
      ext S
      simp only [mem_filter, mem_powersetCard, mem_singleton]
      constructor
      · rintro ⟨⟨_, hSc⟩, hAS, hBS⟩
        exact (eq_of_subset_of_card_le (union_subset hAS hBS) (by omega)).symm
      · rintro rfl
        exact ⟨⟨union_subset hAV hBV, hUk⟩, subset_union_left, subset_union_right⟩
    simp only [hleft, hright, card_singleton]
  · have hIlt : (A ∩ B).card < k := by omega
    have hUbig : k + 3 ≤ (A ∪ B).card := by omega
    have hleft : (V.powersetCard k).filter (fun T => T ⊆ A ∧ T ⊆ B) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨⟨_, hTc⟩, hTA, hTB⟩ := by
        simpa only [mem_filter, mem_powersetCard] using hT
      have hle := card_le_card (subset_inter hTA hTB)
      omega
    have hright : (V.powersetCard (k + 2)).filter (fun S => A ⊆ S ∧ B ⊆ S) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨⟨_, hSc⟩, hAS, hBS⟩ := by
        simpa only [mem_filter, mem_powersetCard] using hS
      have hle := card_le_card (union_subset hAS hBS)
      omega
    rw [hleft, hright]

/-- Adjacent mixed pairs can be counted by their intersection or their union. -/
lemma mixed_count_succ (V : Finset α) (k : ℕ) (w z : Finset α → ℕ)
    (ho : ∀ A ∈ V.powersetCard (k + 1), w A * z A = 0) :
    (∑ T ∈ V.powersetCard k, degree V (k + 1) w T * degree V (k + 1) z T) =
      ∑ S ∈ V.powersetCard (k + 2), total S (k + 1) w * total S (k + 1) z := by
  calc
    _ = ∑ T ∈ V.powersetCard k, ∑ A ∈ V.powersetCard (k + 1),
        ∑ B ∈ V.powersetCard (k + 1),
          if T ⊆ A ∧ T ⊆ B then w A * z B else 0 := by
      apply sum_congr rfl
      intro T _
      exact degree_mul_expand V T (k + 1) w z
    _ = ∑ A ∈ V.powersetCard (k + 1), ∑ B ∈ V.powersetCard (k + 1),
        ∑ T ∈ V.powersetCard k, if T ⊆ A ∧ T ⊆ B then w A * z B else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro A _
      rw [sum_comm]
    _ = ∑ A ∈ V.powersetCard (k + 1), ∑ B ∈ V.powersetCard (k + 1),
        ∑ S ∈ V.powersetCard (k + 2), if A ⊆ S ∧ B ⊆ S then w A * z B else 0 := by
      apply sum_congr rfl
      intro A hA
      apply sum_congr rfl
      intro B hB
      by_cases hAB : A = B
      · subst B
        simp only [ho A hA, ite_self, sum_const_zero]
      · rw [← sum_filter, ← sum_filter, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
        rw [adjacent_pair_card hA hB hAB]
    _ = ∑ S ∈ V.powersetCard (k + 2), ∑ A ∈ V.powersetCard (k + 1),
        ∑ B ∈ V.powersetCard (k + 1), if A ⊆ S ∧ B ⊆ S then w A * z B else 0 := by
      symm
      rw [sum_comm]
      apply sum_congr rfl
      intro A _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      exact (total_mul_expand V S (k + 1) w z (mem_powersetCard.mp hS).1).symm

omit [DecidableEq α] in
/-- A zero-one weight and its complement count all sets of the given size. -/
lemma indicator_total_add (V : Finset α) (r : ℕ) (w : Finset α → ℕ)
    (hw : ∀ S ∈ V.powersetCard r, w S ≤ 1) :
    total V r w + total V r (fun S => 1 - w S) = V.card.choose r := by
  calc
    _ = ∑ S ∈ V.powersetCard r, (w S + (1 - w S)) := by
      simp only [total, sum_add_distrib]
    _ = ∑ S ∈ V.powersetCard r, 1 := by
      apply sum_congr rfl
      intro S hS
      have h := hw S hS
      omega
    _ = _ := by simp

/-- Complementary codegrees add to the number of possible extensions. -/
lemma indicator_degree_add (V T : Finset α) (k : ℕ) (w : Finset α → ℕ)
    (hw : ∀ S ∈ V.powersetCard (k + 1), w S ≤ 1)
    (hT : T ∈ V.powersetCard k) :
    degree V (k + 1) w T + degree V (k + 1) (fun S => 1 - w S) T = V.card - k := by
  obtain ⟨hTV, hTc⟩ := mem_powersetCard.mp hT
  rw [← degree_add]
  rw [degree_congr V (k + 1) (fun S => w S + (1 - w S)) (fun _ => 1) T
    (fun S hS _ => by
      change w S + (1 - w S) = 1
      have h := hw S hS
      omega)]
  rw [degree_one V T (k + 1) hTV (by omega), hTc]
  simp

/-- The algebraic cancellation in the direct proof, with zero nonedges handled
separately. All constants are finite and all denominators have been cleared. -/
lemma cover_count_algebra (N k E F X S₂ : ℕ) (hN : k + 2 ≤ N)
    (htotal : E + F = N.choose (k + 1))
    (hidentity : S₂ + X = (N - k) * (k + 1) * F)
    (hlower : (N - (k + 1)) * F ≤ X)
    (hCS : ((k + 1) * F) ^ 2 ≤ S₂ * N.choose k) :
    (N - (k + 1)) * N.choose (k + 1) ≤ (k + 1) * (N - k) * E := by
  by_cases hF : F = 0
  · have hE : E = N.choose (k + 1) := by omega
    rw [hE]
    have hcoef : N - (k + 1) ≤ (k + 1) * (N - k) := by
      calc
        _ ≤ N - k := by omega
        _ ≤ (k + 1) * (N - k) := by
          simpa only [one_mul] using
            Nat.mul_le_mul_right (N - k) (show 1 ≤ k + 1 by omega)
    exact Nat.mul_le_mul_right _ hcoef
  · have hFpos : 0 < F := by omega
    have hprod : ((k + 1) ^ 2 * F + N.choose k * (N - (k + 1))) * F ≤
        (N.choose k * (N - k) * (k + 1)) * F := by
      calc
        _ = ((k + 1) * F) ^ 2 + N.choose k * ((N - (k + 1)) * F) := by ring
        _ ≤ S₂ * N.choose k + N.choose k * X :=
          add_le_add hCS (Nat.mul_le_mul_left _ hlower)
        _ = N.choose k * (S₂ + X) := by ring
        _ = N.choose k * ((N - k) * (k + 1) * F) := by rw [hidentity]
        _ = _ := by ring
    have hcancel := Nat.le_of_mul_le_mul_right hprod hFpos
    have hchoose : N.choose k * (N - k) = (k + 1) * N.choose (k + 1) := by
      have h := Nat.choose_mul (n := N) (show k ≤ k + 1 by omega)
      simpa only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
        Nat.choose_one_right, Nat.mul_comm] using h.symm
    have hrhs : N.choose k * (N - k) * (k + 1) =
        (k + 1) ^ 2 * (E + F) := by
      rw [hchoose, htotal]
      ring
    rw [hrhs, mul_add] at hcancel
    have hsmall : N.choose k * (N - (k + 1)) ≤ (k + 1) ^ 2 * E := by omega
    have hfinal : (k + 1) * ((N - (k + 1)) * N.choose (k + 1)) ≤
        (k + 1) * ((k + 1) * (N - k) * E) := by
      calc
        _ = ((k + 1) * N.choose (k + 1)) * (N - (k + 1)) := by ring
        _ = (N.choose k * (N - k)) * (N - (k + 1)) := by rw [hchoose]
        _ = (N - k) * (N.choose k * (N - (k + 1))) := by ring
        _ ≤ (N - k) * ((k + 1) ^ 2 * E) := Nat.mul_le_mul_left _ hsmall
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hfinal (by omega)

/-- The finite de Caen bound for a family of `(k+1)`-sets covering all
`(k+2)`-sets. This applies to arbitrary families, without a parity hypothesis. -/
theorem deCaen_succ_cover (V : Finset α) (k : ℕ) (w : Finset α → ℕ)
    (hV : k + 2 ≤ V.card)
    (hw : ∀ S ∈ V.powersetCard (k + 1), w S ≤ 1)
    (hcover : ∀ S ∈ V.powersetCard (k + 2), 1 ≤ total S (k + 1) w) :
    (V.card - (k + 1)) * V.card.choose (k + 1) ≤
      (k + 1) * (V.card - k) * total V (k + 1) w := by
  let z : Finset α → ℕ := fun S => 1 - w S
  let X := ∑ T ∈ V.powersetCard k, degree V (k + 1) w T * degree V (k + 1) z T
  let S₂ := ∑ T ∈ V.powersetCard k, degree V (k + 1) z T ^ 2
  have htotal : total V (k + 1) w + total V (k + 1) z = V.card.choose (k + 1) :=
    indicator_total_add V (k + 1) w hw
  have horth : ∀ A ∈ V.powersetCard (k + 1), w A * z A = 0 := by
    intro A hA
    have h := hw A hA
    have hcases : w A = 0 ∨ w A = 1 := by omega
    rcases hcases with h | h <;> simp [z, h]
  have hcount := mixed_count_succ V k w z horth
  have hlower : (V.card - (k + 1)) * total V (k + 1) z ≤ X := by
    calc
      _ = ∑ S ∈ V.powersetCard (k + 2), total S (k + 1) z := by
        rw [sum_totals_subsets V (k + 2) (k + 1) z (by omega)]
        simp
      _ ≤ ∑ S ∈ V.powersetCard (k + 2), total S (k + 1) w * total S (k + 1) z := by
        apply sum_le_sum
        intro S hS
        simpa only [one_mul] using Nat.mul_le_mul_right (total S (k + 1) z) (hcover S hS)
      _ = X := hcount.symm
  have hidentity : S₂ + X = (V.card - k) * (k + 1) * total V (k + 1) z := by
    calc
      _ = ∑ T ∈ V.powersetCard k,
          (degree V (k + 1) z T ^ 2 + degree V (k + 1) w T * degree V (k + 1) z T) := by
        simp only [S₂, X, sum_add_distrib]
      _ = ∑ T ∈ V.powersetCard k, (V.card - k) * degree V (k + 1) z T := by
        apply sum_congr rfl
        intro T hT
        have h := indicator_degree_add V T k w hw hT
        change degree V (k + 1) w T + degree V (k + 1) z T = V.card - k at h
        rw [show degree V (k + 1) z T ^ 2 +
            degree V (k + 1) w T * degree V (k + 1) z T =
            (degree V (k + 1) w T + degree V (k + 1) z T) *
              degree V (k + 1) z T by ring, h]
      _ = _ := by
        rw [← mul_sum, sum_degrees, Nat.choose_succ_self_right]
        ring
  have hCS : ((k + 1) * total V (k + 1) z) ^ 2 ≤ S₂ * V.card.choose k := by
    have h := sum_mul_sq_le_sq_mul_sq (V.powersetCard k)
      (fun T => degree V (k + 1) z T) (fun _ => (1 : ℕ))
    simpa only [mul_one, one_pow, sum_const, smul_eq_mul, card_powersetCard,
      sum_degrees, Nat.choose_succ_self_right] using h
  exact cover_count_algebra V.card k (total V (k + 1) w) (total V (k + 1) z)
    X S₂ hV htotal hidentity hlower hCS

/-- The special case needed for even quadruples: any quadruple family covering
all five-sets has finite density at least `(N-4)/(4*(N-3))`. -/
theorem deCaen_four_cover (V : Finset α) (w : Finset α → ℕ) (hV : 5 ≤ V.card)
    (hw : ∀ S ∈ V.powersetCard 4, w S ≤ 1)
    (hcover : ∀ S ∈ V.powersetCard 5, 1 ≤ total S 4 w) :
    (V.card - 4) * V.card.choose 4 ≤ 4 * (V.card - 3) * total V 4 w := by
  simpa only [Nat.reduceAdd] using deCaen_succ_cover V 3 w hV hw hcover

/-- A cardinality-only interface for an arbitrary family of quadruples covering
all five-sets. The covering assumption is the usual subset formulation. -/
theorem deCaen_four_cover_card (V : Finset α) (E : Finset (Finset α))
    (hV : 5 ≤ V.card) (hE : E ⊆ V.powersetCard 4)
    (hcover : ∀ S ∈ V.powersetCard 5, ∃ e ∈ E, e ⊆ S) :
    (V.card - 4) * V.card.choose 4 ≤ 4 * (V.card - 3) * E.card := by
  let w : Finset α → ℕ := fun S => if S ∈ E then 1 else 0
  have hw : ∀ S ∈ V.powersetCard 4, w S ≤ 1 := by
    intro S _
    dsimp [w]
    split_ifs <;> omega
  have hc : ∀ S ∈ V.powersetCard 5, 1 ≤ total S 4 w := by
    intro S hS
    obtain ⟨e, heE, heS⟩ := hcover S hS
    have he : e ∈ S.powersetCard 4 :=
      mem_powersetCard.mpr ⟨heS, (mem_powersetCard.mp (hE heE)).2⟩
    calc
      1 = w e := by simp [w, heE]
      _ ≤ total S 4 w := single_le_sum (fun _ _ => Nat.zero_le _) he
  have hf : (V.powersetCard 4).filter (fun S => S ∈ E) = E := by
    ext S
    simp only [mem_filter]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hE h, h⟩
  have ht : total V 4 w = E.card := by
    change (∑ S ∈ V.powersetCard 4, if S ∈ E then (1 : ℕ) else 0) = E.card
    rw [sum_boole, hf]
    simp
  have h := deCaen_four_cover V w hV hw hc
  rwa [ht] at h

/-- A normalized finite bound for an arbitrary four-uniform cover of five-sets. -/
theorem deCaen_four_cover_density (V : Finset α) (w : Finset α → ℕ)
    (hV : 5 ≤ V.card) (hw : ∀ S ∈ V.powersetCard 4, w S ≤ 1)
    (hcover : ∀ S ∈ V.powersetCard 5, 1 ≤ total S 4 w) :
    (V.card - 4 : ℕ) / ((4 : ℝ) * (V.card - 3 : ℕ)) ≤
      (total V 4 w : ℝ) / (V.card.choose 4 : ℝ) := by
  have h := deCaen_four_cover V w hV hw hcover
  have hr : (V.card - 4 : ℕ) * (V.card.choose 4 : ℝ) ≤
      4 * (V.card - 3 : ℕ) * (total V 4 w : ℝ) := by exact_mod_cast h
  have ht : (0 : ℝ) < (V.card - 3 : ℕ) := by
    exact_mod_cast (show 0 < V.card - 3 by omega)
  have hQ : (0 : ℝ) < (V.card.choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 4 ≤ V.card by omega)
  apply (div_le_div_iff₀ (show (0 : ℝ) < 4 * (V.card - 3 : ℕ) by positivity) hQ).2
  nlinarith

/-- Every five-set contains an even quadruple, unconditionally, by odd parity. -/
lemma evenQuad_covers_five (c : Finset α → Bool) (V : Finset α) :
    ∀ S ∈ V.powersetCard 5, 1 ≤ total S 4 (evenQuad c) := by
  intro S hS
  obtain ⟨m, hm⟩ := evenQuad_odd_five c S (mem_powersetCard.mp hS).2
  omega

/-- The direct de Caen bound applies to the even-quadruple family. -/
theorem evenQuad_finite_bound (c : Finset α → Bool) (V : Finset α) (hV : 5 ≤ V.card) :
    (V.card - 4) * V.card.choose 4 ≤ 4 * (V.card - 3) * total V 4 (evenQuad c) :=
  deCaen_four_cover V (evenQuad c) hV (fun S _ => evenQuad_le_one c S)
    (evenQuad_covers_five c V)

/-- The actual finite even-quadruple density, not just its limiting value `1/4`. -/
theorem evenQuad_density_bound (c : Finset α → Bool) (V : Finset α) (hV : 5 ≤ V.card) :
    (V.card - 4 : ℕ) / ((4 : ℝ) * (V.card - 3 : ℕ)) ≤
      (total V 4 (evenQuad c) : ℝ) / (V.card.choose 4 : ℝ) :=
  deCaen_four_cover_density V (evenQuad c) hV (fun S _ => evenQuad_le_one c S)
    (evenQuad_covers_five c V)

omit [DecidableEq α] in
/-- Even quadruples consist exactly of monochromatic and balanced quadruples. -/
lemma evenQuad_total_eq (c : Finset α → Bool) (V : Finset α) :
    total V 4 (evenQuad c) = total V 4 (monoFour c) + total V 4 (balanced c) := by
  calc
    _ = ∑ S ∈ V.powersetCard 4, (monoFour c S + balanced c S) := by
      apply sum_congr rfl
      intro S hS
      exact evenQuad_eq c S (mem_powersetCard.mp hS).2
    _ = _ := by simp only [total, sum_add_distrib]

/-- Mixed-triple counting gives `E ≤ 4M + 3Q/(N-3)`, with denominators cleared. -/
theorem evenQuad_vs_mono (c : Finset α → Bool) (V : Finset α) :
    (V.card - 3) * total V 4 (evenQuad c) ≤
      4 * (V.card - 3) * total V 4 (monoFour c) + 3 * V.card.choose 4 := by
  have h := balanced_vs_mono c V
  rw [evenQuad_total_eq, mul_add]
  nlinarith

/-- An unconditional finite monochromatic seed. Equivalently, after division,
`M/Q ≥ (N-16)/(16*(N-3))`, interpreting the numerator in the integers. -/
theorem monochromatic_four_finite_bound (c : Finset α → Bool) (V : Finset α)
    (hV : 5 ≤ V.card) :
    (V.card - 4) * V.card.choose 4 ≤
      16 * (V.card - 3) * total V 4 (monoFour c) + 12 * V.card.choose 4 := by
  have hlo := evenQuad_finite_bound c V hV
  have hup := Nat.mul_le_mul_left 4 (evenQuad_vs_mono c V)
  nlinarith

/-- The same finite seed arranged to expose its `13/(16*(N-3))` error term. -/
theorem monochromatic_four_shifted_finite_bound (c : Finset α → Bool) (V : Finset α)
    (hV : 5 ≤ V.card) :
    (V.card - 3) * V.card.choose 4 ≤
      16 * (V.card - 3) * total V 4 (monoFour c) + 13 * V.card.choose 4 := by
  have h := monochromatic_four_finite_bound c V hV
  have hn : V.card - 3 = V.card - 4 + 1 := by omega
  calc
    _ = (V.card - 4) * V.card.choose 4 + V.card.choose 4 := by rw [hn]; ring
    _ ≤ (16 * (V.card - 3) * total V 4 (monoFour c) + 12 * V.card.choose 4) +
        V.card.choose 4 := Nat.add_le_add_right h _
    _ = _ := by ring

/-- A natural-number version with the nonnegative numerator `N-16`. -/
theorem monochromatic_four_nonnegative_finite_bound (c : Finset α → Bool) (V : Finset α)
    (hV : 5 ≤ V.card) :
    (V.card - 16) * V.card.choose 4 ≤ 16 * (V.card - 3) * total V 4 (monoFour c) := by
  have h := monochromatic_four_finite_bound c V hV
  by_cases hN : 16 ≤ V.card
  · have hn : V.card - 4 = V.card - 16 + 12 := by omega
    rw [hn, add_mul] at h
    omega
  · have hz : V.card - 16 = 0 := by omega
    simp only [hz, zero_mul, Nat.zero_le]

/-- The stronger normalized seed and its exact finite error term. -/
theorem monochromatic_four_density_bound (c : Finset α → Bool) (V : Finset α)
    (hV : 5 ≤ V.card) :
    (1 : ℝ) / 16 - 13 / (16 * (V.card - 3 : ℕ)) ≤
      (total V 4 (monoFour c) : ℝ) / (V.card.choose 4 : ℝ) := by
  have h := monochromatic_four_shifted_finite_bound c V hV
  have hr : (V.card - 3 : ℕ) * (V.card.choose 4 : ℝ) ≤
      16 * (V.card - 3 : ℕ) * (total V 4 (monoFour c) : ℝ) +
        13 * (V.card.choose 4 : ℝ) := by exact_mod_cast h
  have ht : (0 : ℝ) < (V.card - 3 : ℕ) := by
    exact_mod_cast (show 0 < V.card - 3 by omega)
  have hQ : (0 : ℝ) < (V.card.choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 4 ≤ V.card by omega)
  apply (le_div_iff₀ hQ).2
  have heq : ((1 : ℝ) / 16 - 13 / (16 * (V.card - 3 : ℕ))) * (V.card.choose 4 : ℝ) =
      ((V.card - 3 : ℕ) * (V.card.choose 4 : ℝ) - 13 * (V.card.choose 4 : ℝ)) /
        (16 * (V.card - 3 : ℕ)) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ (show (0 : ℝ) < 16 * (V.card - 3 : ℕ) by positivity)).2
  nlinarith

/-- A uniform asymptotic formulation of `c₄ ≥ 1/16`, without introducing or
assuming a minimum-density limit. It applies to every colouring. -/
theorem monochromatic_four_uniform_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧ ∀ (c : Finset α → Bool) (V : Finset α), N₀ ≤ V.card →
      (1 : ℝ) / 16 - ε ≤ (total V 4 (monoFour c) : ℝ) / (V.card.choose 4 : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((13 : ℝ) / (16 * ε))
  refine ⟨K + 5, by omega, ?_⟩
  intro c V hV
  have hV5 : 5 ≤ V.card := by omega
  have ht : (0 : ℝ) < (V.card - 3 : ℕ) := by
    exact_mod_cast (show 0 < V.card - 3 by omega)
  have hKL : (K : ℝ) ≤ (V.card - 3 : ℕ) := by
    exact_mod_cast (show K ≤ V.card - 3 by omega)
  have hlarge : (13 : ℝ) / (16 * ε) < (V.card - 3 : ℕ) := lt_of_lt_of_le hK hKL
  have hmul := (div_lt_iff₀ (show (0 : ℝ) < 16 * ε by positivity)).mp hlarge
  have herr : (13 : ℝ) / (16 * (V.card - 3 : ℕ)) ≤ ε := by
    apply (div_le_iff₀ (show (0 : ℝ) < 16 * (V.card - 3 : ℕ) by positivity)).2
    nlinarith
  exact le_trans (by linarith) (monochromatic_four_density_bound c V hV5)

/- ## Conditional numerical consequence of the extra-factor recurrence

Nothing in this section proves a recurrence for minimum monochromatic densities.
The argument only verifies that a reciprocal seed `f 4 ≤ 16` would suffice if
`f (n+1) ≤ 2^(choose(n,2)+1) * (f n)^2` were proved independently.
-/
namespace ExtraFactorPotential

/-- The extra factor two raises the weight by one relative to `DensityCriterion`. -/
def weight (n : ℕ) : ℕ := (n + 1).choose 2 + 2

def doubleTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)

lemma weight_identity (n : ℕ) :
    n.choose 2 + 1 + weight (n + 1) = weight n * 2 := by
  have h₁ : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  have h₂ : (n + 2).choose 2 = (n + 1) + (n + 1).choose 2 := by
    simpa using Nat.choose_succ_succ (n + 1) 1
  simp only [weight]
  rw [show n + 1 + 1 = n + 2 by omega, h₂, h₁]
  omega

/-- This is a critical seed, not a strictly subcritical seed. -/
theorem critical_weighted_seed : (16 : ℚ) * 2 ^ weight 4 = doubleTower 4 := by
  norm_num [weight, doubleTower, Nat.choose]

lemma weighted_step (f : ℕ → ℝ) (n : ℕ)
    (h : f (n + 1) ≤ (2 : ℝ) ^ (n.choose 2 + 1) * f n ^ 2) :
    f (n + 1) * (2 : ℝ) ^ weight (n + 1) ≤ (f n * (2 : ℝ) ^ weight n) ^ 2 := by
  calc
    _ ≤ ((2 : ℝ) ^ (n.choose 2 + 1) * f n ^ 2) * (2 : ℝ) ^ weight (n + 1) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = f n ^ 2 * (2 : ℝ) ^ (n.choose 2 + 1 + weight (n + 1)) := by
      rw [pow_add]
      ring
    _ = (f n * (2 : ℝ) ^ weight n) ^ 2 := by
      rw [weight_identity, pow_mul, mul_pow]

lemma doubleTower_step (n : ℕ) : doubleTower (n + 1) = doubleTower n ^ 2 := by
  simp only [doubleTower]
  rw [← pow_mul, pow_succ]

/-- Conditional weighted bound with the extra factor two. The recurrence and
reciprocal seed are explicit hypotheses; they are not asserted for density minima. -/
theorem weighted_bound_of_recurrence (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, 4 ≤ n → 0 ≤ f n) (hseed : f 4 ≤ 16)
    (hrec : ∀ n : ℕ, 4 ≤ n →
      f (n + 1) ≤ (2 : ℝ) ^ (n.choose 2 + 1) * f n ^ 2) :
    ∀ n : ℕ, 4 ≤ n → f n * (2 : ℝ) ^ weight n ≤ (doubleTower n : ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hw : weight 4 = 12 := by decide
    have ht : doubleTower 4 = 65536 := by decide
    rw [hw, ht]
    norm_num
    nlinarith
  | succ n hn ih =>
    calc
      _ ≤ (f n * (2 : ℝ) ^ weight n) ^ 2 := weighted_step f n (hrec n hn)
      _ ≤ (doubleTower n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (hf n hn) (by positivity)) ih 2
      _ = (doubleTower (n + 1) : ℝ) := by
        rw [doubleTower_step, Nat.cast_pow]

lemma correction_weight_bound (n : ℕ) (hn : 4 ≤ n) :
    4 * n.choose 2 ≤ 2 ^ weight n := by
  have hC : n.choose 2 ≤ 2 ^ n.choose 2 := Nat.le_of_lt Nat.lt_two_pow_self
  have hnext : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  have hW : n.choose 2 + 2 ≤ weight n := by
    simp only [weight]
    rw [hnext]
    omega
  calc
    4 * n.choose 2 ≤ 4 * 2 ^ n.choose 2 := Nat.mul_le_mul_left 4 hC
    _ = 2 ^ (n.choose 2 + 2) := by rw [pow_add]; ring
    _ ≤ 2 ^ weight n := Nat.pow_le_pow_right (by decide) hW

/-- The polynomial collision margin is strict even at the critical seed.
This remains conditional on the explicitly displayed extra-factor recurrence. -/
theorem injective_margin_of_recurrence (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, 4 ≤ n → 0 ≤ f n) (hseed : f 4 ≤ 16)
    (hrec : ∀ n : ℕ, 4 ≤ n →
      f (n + 1) ≤ (2 : ℝ) ^ (n.choose 2 + 1) * f n ^ 2) :
    ∀ n : ℕ, 4 ≤ n → 2 * (n.choose 2 : ℝ) * f n < (doubleTower n : ℝ) := by
  intro n hn
  have hbound := weighted_bound_of_recurrence f hf hseed hrec n hn
  have hweight : (4 : ℝ) * (n.choose 2 : ℝ) ≤ (2 : ℝ) ^ weight n := by
    exact_mod_cast correction_weight_bound n hn
  have hmul := mul_le_mul_of_nonneg_right hweight (hf n hn)
  have ht : (0 : ℝ) < (doubleTower n : ℝ) := by
    exact_mod_cast (show 0 < doubleTower n by dsimp [doubleTower]; positivity)
  nlinarith

end ExtraFactorPotential

end Combinatorics.DensityRoute.DeCaen
