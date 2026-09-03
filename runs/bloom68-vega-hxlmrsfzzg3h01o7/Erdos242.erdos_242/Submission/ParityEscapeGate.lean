import Submission.DivisorCriterion

/-!
# A certified failure of the proposed seed-component parity escape

For the prime `30241 ≡ 1 (mod 24)`, a 29-state set contains the seed,
contains no good state, and is closed under every permitted transition.
This refutes the seed-reachability claim, NOT the Erdős–Straus conjecture.
Indeed `es_30241` below proves the ES instance using the existing criterion.

`Step` allows any two valid states sharing `k`, any two sharing `r`, or
swapping `k,q`. Thus it includes all the factor-switch edges in the question:
a factor-switch preserves the indicated coordinate and the exact equation.
The closure checks enumerate only one coordinate at a time, not all triples.
The explicit coordinate bound is part of the proposed state space.

This file does not import or modify `Submission.Spec`.
-/

namespace Erdos242.Development.ParityEscapeGate

abbrev Triple := ℕ × ℕ × ℕ

/-- The positive, bounded, exact state space in the proposed route. -/
def Valid (p : ℕ) (s : Triple) : Prop :=
  0 < s.1 ∧ 0 < s.2.1 ∧ 0 < s.2.2 ∧
  s.1 ≤ p + 2 ∧ s.2.1 ≤ p + 2 ∧ s.2.2 ≤ p + 2 ∧
  p + s.1 + s.2.1 = s.1 * s.2.1 * s.2.2

def swap (s : Triple) : Triple := (s.2.1, s.1, s.2.2)

def Good (s : Triple) : Prop := s.2.1 % 4 = 3 ∧ s.2.2 % 4 = 3

/-- A supergraph of the prescribed transitions (in fact, the same graph). -/
def Step (p : ℕ) (a b : Triple) : Prop :=
  Valid p a ∧ Valid p b ∧
  (b = swap a ∨ b.1 = a.1 ∨ b.2.2 = a.2.2)

inductive Reachable (p : ℕ) : Triple → Prop
  | seed : Reachable p (1, 1, p + 2)
  | step {a b : Triple} : Reachable p a → Step p a b → Reachable p b

/-- The complete seed component, as certified independently in the JSON file. -/
def component : Finset Triple := {
  (1, 1, 30243),
  (1, 30242, 2), (30242, 1, 2),
  (1, 15121, 3), (15121, 1, 3),
  (1, 2, 15122), (2, 1, 15122),
  (2, 10081, 2), (10081, 2, 2),
  (25, 409, 3), (409, 25, 3),
  (2, 30243, 1), (30243, 2, 1),
  (2, 1779, 9), (1779, 2, 9),
  (2, 593, 26), (593, 2, 26),
  (2, 51, 297), (51, 2, 297),
  (2, 17, 890), (17, 2, 890),
  (2, 3, 5041), (3, 2, 5041),
  (3, 15122, 1), (15122, 3, 1),
  (19, 178, 9), (178, 19, 9),
  (22, 53, 26), (53, 22, 26)
}

private def kValues : Finset ℕ := component.image Prod.fst
private def rValues : Finset ℕ := component.image (fun s => s.2.2)

theorem component_card : component.card = 29 := by native_decide

theorem component_valid : ∀ s ∈ component, Valid 30241 s := by
  unfold Valid
  native_decide

theorem seed_mem : (1, 1, 30243) ∈ component := by native_decide

theorem swap_closed : ∀ s ∈ component, swap s ∈ component := by native_decide

theorem component_good_free : ∀ s ∈ component, ¬ Good s := by
  unfold Good
  native_decide

/-- Complete fixed-k slice check, solving for r from k and q. -/
private theorem fixed_k_check :
    ∀ k ∈ kValues, ∀ q ∈ Finset.range 30244,
      0 < k * q → (30241 + k + q) % (k * q) = 0 →
      (k, q, (30241 + k + q) / (k * q)) ∈ component := by
  native_decide

/-- Complete fixed-r slice check, solving for q from k and r. -/
private theorem fixed_r_check :
    ∀ r ∈ rValues, ∀ k ∈ Finset.range 30244,
      0 < k * r - 1 → (30241 + k) % (k * r - 1) = 0 →
      (k, (30241 + k) / (k * r - 1), r) ∈ component := by
  native_decide

/-- The finite set is closed under every allowed factor-switch and swap. -/
theorem component_closed {a b : Triple} (ha : a ∈ component)
    (hstep : Step 30241 a b) : b ∈ component := by
  rcases b with ⟨k, q, r⟩
  rcases hstep with ⟨_, ⟨hk, hq, _, hkb, hqb, _, heq⟩, hkind⟩
  change 30241 + k + q = k * q * r at heq
  change (k, q, r) = swap a ∨ k = a.1 ∨ r = a.2.2 at hkind
  rcases hkind with hswap | hfixk | hfixr
  · rw [hswap]
    exact swap_closed a ha
  · have hK : k ∈ kValues := by
      rw [hfixk]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hqRange : q ∈ Finset.range 30244 := by
      apply Finset.mem_range.mpr
      change q ≤ 30241 + 2 at hqb
      omega
    have hkq : 0 < k * q := Nat.mul_pos hk hq
    have hmod : (30241 + k + q) % (k * q) = 0 := by
      rw [heq]
      exact Nat.mul_mod_right _ _
    have hdiv : (30241 + k + q) / (k * q) = r :=
      Nat.div_eq_of_eq_mul_right hkq heq
    have ht := fixed_k_check k hK q hqRange hkq hmod
    rwa [hdiv] at ht
  · have hR : r ∈ rValues := by
      rw [hfixr]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hkRange : k ∈ Finset.range 30244 := by
      apply Finset.mem_range.mpr
      change k ≤ 30241 + 2 at hkb
      omega
    have hkr : 1 < k * r := by
      by_contra h
      have hle : k * r ≤ 1 := by omega
      have hm := Nat.mul_le_mul_left q hle
      nlinarith only [heq, hm]
    have hsub : k * r - 1 + 1 = k * r := Nat.sub_add_cancel (by omega)
    have hrel : 30241 + k = q * (k * r - 1) := by
      have hm := congrArg (fun n : ℕ => q * n) hsub
      nlinarith only [heq, hm]
    have hpos : 0 < k * r - 1 := by omega
    have hmod : (30241 + k) % (k * r - 1) = 0 := by
      rw [hrel]
      exact Nat.mul_mod_left _ _
    have hdiv : (30241 + k) / (k * r - 1) = q :=
      Nat.div_eq_of_eq_mul_left hpos hrel
    have ht := fixed_r_check r hR k hkRange hpos hmod
    rwa [hdiv] at ht

/-- Reachability cannot leave a closed set containing the seed. -/
theorem reachable_mem {s : Triple} (h : Reachable 30241 s) : s ∈ component := by
  induction h with
  | seed => exact seed_mem
  | step _ hs ih => exact component_closed ih hs

theorem no_good_reachable {s : Triple} (h : Reachable 30241 s) : ¬ Good s :=
  component_good_free s (reachable_mem h)

/-- The proposed universal prime seed-escape statement is false. -/
theorem seed_escape_claim_false :
    ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧
      ¬ ∃ s : Triple, Reachable p s ∧ Good s := by
  refine ⟨30241, by norm_num, by norm_num, ?_⟩
  rintro ⟨s, hr, hg⟩
  exact no_good_reachable hr hg

/-- A good state exists in a different component; this is not an ES obstruction. -/
theorem good_state_elsewhere :
    Valid 30241 (398, 7, 11) ∧ Good (398, 7, 11) ∧
      ¬ Reachable 30241 (398, 7, 11) := by
  have hg : Good (398, 7, 11) := by norm_num [Good]
  refine ⟨by norm_num [Valid], hg, ?_⟩
  intro h
  exact no_good_reachable h hg

/-- The existing Type I constructor proves ES for the obstructing prime. -/
theorem es_30241 : ES 30241 := by
  apply es_of_typeI_pair (u := 7562) (d := 19) (v := 3009676)
  all_goals norm_num

end Erdos242.Development.ParityEscapeGate
