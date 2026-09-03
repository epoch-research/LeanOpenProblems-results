import Submission.MixedPatternJointExample

/-! Joint deletion inequalities for an arbitrary finite family of added moduli.
These combine already available count bounds; they do not assert a uniform
quadratic Jacobsthal estimate. -/
namespace Erdos970.MixedPattern
open OptimalCoverCore JointExample BlockSieve.SievePolynomial

/-- A point that does not survive all added conditions can survive after deleting
at most one of them. This remains true for arbitrary moduli, without primality. -/
theorem sum_deleted_survivors_le (m : ℕ) (S D : Finset ℕ) (r : ℕ → ℕ)
    (hD : D.Nonempty) :
    (∑ p ∈ D, (survivors m (S ∪ D.erase p) r).card) ≤
      (survivors m S r).card + (D.card - 1) * (survivors m (S ∪ D) r).card := by
  classical
  simp only [survivor_count_sum]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  dsimp only
  by_cases hS : ∀ q ∈ S, ¬i ≡ r q [MOD q]
  · by_cases hfull : ∀ q ∈ D, ¬i ≡ r q [MOD q]
    · have he (p : ℕ) (hp : p ∈ D) : ∀ q ∈ S ∪ D.erase p, ¬i ≡ r q [MOD q] := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq | hq
        · exact hS q hq
        · exact hfull q (Finset.mem_of_mem_erase hq)
      have hefull : ∀ q ∈ S ∪ D, ¬i ≡ r q [MOD q] := by
        simpa only [Finset.forall_mem_union] using And.intro hS hfull
      rw [if_pos hS, if_pos hefull]
      have hsum : (∑ p ∈ D, if ∀ q ∈ S ∪ D.erase p, ¬i ≡ r q [MOD q]
          then (1 : ℕ) else 0) = D.card := by
        calc
          _ = ∑ p ∈ D, (1 : ℕ) := Finset.sum_congr rfl (fun p hp => if_pos (he p hp))
          _ = D.card := by simp
      rw [hsum]
      have hc := Finset.card_pos.mpr hD
      omega
    · push_neg at hfull
      obtain ⟨q, hq, hiq'⟩ := hfull
      have hzero : ¬∀ q ∈ S ∪ D, ¬i ≡ r q [MOD q] := by
        intro h
        exact h q (Finset.mem_union_right S hq) hiq'
      rw [if_pos hS, if_neg hzero]
      simp only [Nat.mul_zero, Nat.add_zero]
      have hterm (p : ℕ) (hp : p ∈ D) :
          (if ∀ v ∈ S ∪ D.erase p, ¬i ≡ r v [MOD v] then (1 : ℕ) else 0) ≤
            if p = q then 1 else 0 := by
        by_cases hpq : p = q
        · simp only [hpq, if_true]
          split_ifs <;> omega
        · have hnot : ¬∀ v ∈ S ∪ D.erase p, ¬i ≡ r v [MOD v] := by
            intro h
            exact h q (Finset.mem_union_right S (Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩)) hiq'
          simp only [hnot, hpq, if_false, le_refl]
      calc
        _ ≤ ∑ p ∈ D, if p = q then (1 : ℕ) else 0 := Finset.sum_le_sum hterm
        _ = 1 := by simp [hq]
  · have hnot (E : Finset ℕ) : ¬∀ q ∈ S ∪ E, ¬i ≡ r q [MOD q] := by
      intro h
      exact hS (fun q hq => h q (Finset.mem_union_left E hq))
    rw [if_neg hS, if_neg (hnot D)]
    simp only [Nat.mul_zero, Nat.add_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro p hp
    exact if_neg (hnot (D.erase p))

/-- A numerical lower bound for every single deletion can be combined against
one upper bound for the common core. -/
theorem joint_count_bound (m : ℕ) (S D : Finset ℕ) (r : ℕ → ℕ)
    (hD : D.Nonempty) (L : ℕ → ℕ) (U : ℕ)
    (hL : ∀ p ∈ D, L p ≤ (survivors m (S ∪ D.erase p) r).card)
    (hU : (survivors m S r).card ≤ U) :
    (∑ p ∈ D, L p) ≤ U + (D.card - 1) * (survivors m (S ∪ D) r).card := by
  exact (Finset.sum_le_sum hL).trans
    ((sum_deleted_survivors_le m S D r hD).trans (Nat.add_le_add_right hU _))

lemma ceilQuotient_le_of_le_mul {n d c : ℕ} (hd : 0 < d) (h : n ≤ c * d) :
    ceilQuotient n d ≤ c := by
  unfold ceilQuotient
  have he := Nat.mod_add_div n d
  have hm := Nat.mod_lt n hd
  split_ifs with hz
  · rw [Nat.add_zero]
    have hh := Nat.div_le_div_right (c := d) h
    simpa only [Nat.mul_div_cancel _ hd] using hh
  · by_contra hbad
    have hq : c ≤ n / d := by omega
    have hh := Nat.mul_le_mul_left d hq
    have hzpos : 0 < n % d := by omega
    nlinarith

/-- Integer rounding is valid after the joint inequality. No LP solver or
floating-point optimization occurs in this theorem. -/
theorem joint_rounded_lower (m : ℕ) (S D : Finset ℕ) (r : ℕ → ℕ)
    (hD : 2 ≤ D.card) (L : ℕ → ℕ) (U : ℕ)
    (hL : ∀ p ∈ D, L p ≤ (survivors m (S ∪ D.erase p) r).card)
    (hU : (survivors m S r).card ≤ U) :
    ceilQuotient ((∑ p ∈ D, L p) - U) (D.card - 1) ≤
      (survivors m (S ∪ D) r).card := by
  have hne : D.Nonempty := Finset.card_pos.mp (by omega)
  have hh := joint_count_bound m S D r hne L U hL hU
  apply ceilQuotient_le_of_le_mul (by omega)
  have ht : (∑ p ∈ D, L p) - U ≤ (D.card - 1) * (survivors m (S ∪ D) r).card := by omega
  simpa only [Nat.mul_comm] using ht

#print axioms sum_deleted_survivors_le
#print axioms joint_rounded_lower
end Erdos970.MixedPattern
