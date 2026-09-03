import FormalConjecturesUtil
import Submission.CofactorReflection
import Submission.ReflectionCore

/-! Structural facts about the prime-factor reflection. These do not assert
that the reflection preserves counting measure or a counting interval. -/

namespace Erdos371ReflectionDynamics

open Erdos371Cofactor

def valid (n : ℕ) : Prop := 1 < n ∧ n + 1 < P n * P (n+1)

abbrev win (n : ℕ) := max (P n) (P (n+1))
abbrev lose (n : ℕ) := min (P n) (P (n+1))

lemma reflection_sum {n : ℕ} (hn : valid n) :
    reflect n + 1 + n = P n * P (n+1) := by
  unfold reflect
  obtain ⟨hn, hb⟩ := hn
  omega

lemma reflection_factors {n : ℕ} (hn : valid n) :
    reflect n = (P n - cofactor (n+1)) * P (n+1) ∧
    reflect n + 1 = (P (n+1) - cofactor n) * P n ∧
    cofactor (n+1) < P n ∧ cofactor n < P (n+1) := by
  have hn1 : 1 < n := hn.1
  have ha := cofactor_mul n
  have hb := cofactor_mul (n+1)
  have hpa := (Nat.prime_maxPrimeFac_of_one_lt n hn.1).pos
  have hpb := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).pos
  have ha' : cofactor n < P (n+1) := by
    by_contra h
    have hh := Nat.mul_le_mul_right (P n) (Nat.le_of_not_gt h)
    nlinarith [hn.2]
  have hb' : cofactor (n+1) < P n := by
    by_contra h
    have hh := Nat.mul_le_mul_right (P (n+1)) (Nat.le_of_not_gt h)
    nlinarith [hn.2]
  refine ⟨?_, ?_, hb', ha'⟩
  · rw [Nat.sub_mul, hb]
    unfold reflect
    omega
  · rw [Nat.sub_mul, ha, Nat.mul_comm]
    have hh := reflection_sum hn
    omega

/-- The winner is unchanged, the loser can only increase, and the comparison
reverses. The image stays in the finite reflection core of the same winner. -/
theorem reflection_structure {n : ℕ} (hn : valid n) :
    valid (reflect n) ∧ win (reflect n) = win n ∧ lose n ≤ lose (reflect n) ∧
      (P (reflect n) < P (reflect n+1) ↔ P (n+1) < P n) := by
  have hn1 : 1 < n := hn.1
  obtain ⟨ht, ht1, hb, ha⟩ := reflection_factors hn
  have hpn := Nat.prime_maxPrimeFac_of_one_lt n hn.1
  have hpn1 := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega : 1 < n+1)
  have hca := cofactor_pos hn.1
  have hcb := cofactor_pos (n := n+1) (by omega)
  have hd1 : 0 < P n - cofactor (n+1) := Nat.sub_pos_of_lt hb
  have hd2 : 0 < P (n+1) - cofactor n := Nat.sub_pos_of_lt ha
  have hL : P (reflect n) = max (P (P n - cofactor (n+1))) (P (n+1)) := by
    rw [ht, P, Nat.maxPrimeFac_mul hd1.ne' hpn1.ne_zero, hpn1.maxPrimeFac_eq_self]
  have hR : P (reflect n+1) = max (P (P (n+1) - cofactor n)) (P n) := by
    rw [ht1, P, Nat.maxPrimeFac_mul hd2.ne' hpn.ne_zero, hpn.maxPrimeFac_eq_self]
  have hsmallL : P (P n - cofactor (n+1)) < P n :=
    Nat.maxPrimeFac_le.trans_lt (Nat.sub_lt hpn.pos hcb)
  have hsmallR : P (P (n+1) - cofactor n) < P (n+1) :=
    Nat.maxPrimeFac_le.trans_lt (Nat.sub_lt hpn1.pos hca)
  have hleft : P (n+1) ≤ P (reflect n) := by rw [hL]; exact le_max_right _ _
  have hright : P n ≤ P (reflect n+1) := by rw [hR]; exact le_max_right _ _
  have hprod : P n * P (n+1) ≤ P (reflect n) * P (reflect n+1) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul hright hleft
  have htpos : 1 < reflect n := by
    rw [ht]
    have hh := Nat.mul_le_mul_right (P (n+1)) hd1
    nlinarith [hpn1.two_le]
  have htvalid : valid (reflect n) := by
    refine ⟨htpos, ?_⟩
    have hs := reflection_sum hn
    have hh : reflect n + 1 < P n * P (n+1) := by omega
    exact hh.trans_le hprod
  refine ⟨htvalid, ?_, ?_, ?_⟩
  · unfold win
    rw [hL, hR]
    omega
  · unfold lose
    omega
  · rw [hL, hR]
    omega

lemma win_mul_lose (n : ℕ) : win n * lose n = P n * P (n+1) := by
  unfold win lose
  exact max_mul_min _ _

/-- Every two reflection steps move weakly to the right. Strict movement is
exactly the effect of increasing the losing prime in the first step. -/
theorem reflection_twice {n : ℕ} (hn : valid n) :
    reflect (reflect n) = n + win n * (lose (reflect n) - lose n) := by
  obtain ⟨ht, hw, hl, _⟩ := reflection_structure hn
  have hs := reflection_sum hn
  have hs' := reflection_sum ht
  rw [← win_mul_lose n] at hs
  rw [← win_mul_lose (reflect n), hw] at hs'
  have hd : win n * (lose (reflect n) - lose n) =
      win n * lose (reflect n) - win n * lose n := Nat.mul_sub _ _ _
  have hh := Nat.mul_le_mul_left (win n) hl
  omega

lemma reflection_twice_ge {n : ℕ} (hn : valid n) : n ≤ reflect (reflect n) := by
  rw [reflection_twice hn]
  omega

lemma reflection_twice_eq_iff {n : ℕ} (hn : valid n) :
    reflect (reflect n) = n ↔ lose (reflect n) = lose n := by
  rw [reflection_twice hn]
  have hw : 0 < win n := lt_of_lt_of_le
    (Nat.prime_maxPrimeFac_of_one_lt n hn.1).pos (le_max_left _ _)
  have hl := (reflection_structure hn).2.2.1
  constructor
  · intro h
    have hz : win n * (lose (reflect n) - lose n) = 0 := by omega
    have hh := (Nat.mul_eq_zero.mp hz).resolve_left hw.ne'
    omega
  · intro h
    simp [h]

def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k+1 => reflect (orbit n k)

lemma orbit_valid_win {n : ℕ} (hn : valid n) (k : ℕ) :
    valid (orbit n k) ∧ win (orbit n k) = win n := by
  induction k with
  | zero => exact ⟨hn, rfl⟩
  | succ k ih =>
    obtain ⟨hv, hw, _⟩ := reflection_structure ih.1
    exact ⟨hv, hw.trans ih.2⟩

lemma orbit_loser_step {n : ℕ} (hn : valid n) (k : ℕ) :
    lose (orbit n k) ≤ lose (orbit n (k+1)) :=
  (reflection_structure (orbit_valid_win hn k).1).2.2.1

lemma loser_two_le {n : ℕ} (hn : valid n) : 2 ≤ lose n := by
  have hn1 := hn.1
  exact le_min (Nat.prime_maxPrimeFac_of_one_lt n hn1).two_le
    (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).two_le

lemma orbit_loser_stabilizes {n : ℕ} (hn : valid n) :
    ∃ k < win n, lose (orbit n (k+1)) = lose (orbit n k) := by
  by_contra h
  push_neg at h
  have hg (k : ℕ) (hk : k ≤ win n) : lose n + k ≤ lose (orbit n k) := by
    induction k with
    | zero => simp [orbit]
    | succ k ih =>
      have hi := ih (by omega)
      have hm := orbit_loser_step hn k
      have he := h k (by omega)
      omega
  have hb : lose (orbit n (win n)) ≤ win n := by
    calc
      _ ≤ win (orbit n (win n)) := (min_le_left _ _).trans (le_max_left _ _)
      _ = win n := (orbit_valid_win hn (win n)).2
  have hh := hg (win n) le_rfl
  have hl := loser_two_le hn
  omega

/-- Every orbit in a reflection core eventually repeats after two steps.
This is an orbit statement, not an equidistribution statement about the core. -/
theorem orbit_eventually_two_cycle {n : ℕ} (hn : valid n) :
    ∃ k < win n, ∀ j : ℕ, orbit n (k+j+2) = orbit n (k+j) := by
  obtain ⟨k, hk, he⟩ := orbit_loser_stabilizes hn
  have ht : orbit n (k+2) = orbit n k := by
    change reflect (reflect (orbit n k)) = orbit n k
    exact (reflection_twice_eq_iff (orbit_valid_win hn k).1).mpr he
  refine ⟨k, hk, fun j => ?_⟩
  induction j with
  | zero => simpa using ht
  | succ j ih =>
    have h1 : k+(j+1)+2 = (k+j+2)+1 := by omega
    have h2 : k+(j+1) = (k+j)+1 := by omega
    rw [h1, h2]
    change reflect (orbit n (k+j+2)) = reflect (orbit n (k+j))
    exact congrArg reflect ih

def sources (p : ℕ) : Finset ℕ :=
  (Erdos371ReflectionCore.core p).filter fun n =>
    n ∉ (Erdos371ReflectionCore.core p).image reflect

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma sources_seventeen : sources 17 = {16, 50} := by decide +kernel

/-- Sources are not confined to comparisons adjacent to the winning prime
itself. This finite fact does not say whether the sources have density zero. -/
lemma composite_source : 50 ∈ sources 17 ∧ ¬Nat.Prime 50 ∧ ¬Nat.Prime 51 := by
  rw [sources_seventeen]
  decide +kernel

end Erdos371ReflectionDynamics

#print axioms Erdos371ReflectionDynamics.reflection_structure
#print axioms Erdos371ReflectionDynamics.reflection_twice
#print axioms Erdos371ReflectionDynamics.orbit_eventually_two_cycle
#print axioms Erdos371ReflectionDynamics.composite_source
