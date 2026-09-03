import Submission.IncrementReduction

/-! Exact parity reduction for prime-class interval bounds. -/
namespace Erdos970.IncrementReduction

theorem primeSetBound_of_insert_two {P : Finset ℕ} {m : ℕ}
    (h2 : 2 ∉ P) (h : PrimeSetBound (insert 2 P) (2 * m)) :
    PrimeSetBound P m := by
  classical
  intro r
  let r' : ℕ → ℕ := Function.update (fun q => 2 * r q) 2 1
  obtain ⟨i, hi, hia⟩ := h r'
  have hi2 : ¬i ≡ 1 [MOD 2] := by
    simpa [r'] using hia 2 (Finset.mem_insert_self _ _)
  have himod : i % 2 = 0 := by
    have := Nat.mod_lt i (by omega : 0 < 2)
    change ¬i % 2 = 1 % 2 at hi2
    omega
  have hieq : 2 * (i / 2) = i := by omega
  refine ⟨i / 2, by omega, ?_⟩
  intro q hq hbad
  have hq2 : q ≠ 2 := by intro hq2; exact h2 (hq2 ▸ hq)
  have hh := hia q (Finset.mem_insert_of_mem hq)
  apply hh
  have hh' : 2 * (i / 2) ≡ 2 * r q [MOD q] := hbad.mul_left 2
  simpa [r', hq2, hieq] using hh'

theorem primeSetBound_insert_two {P : Finset ℕ} {m : ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ q ≠ 2) (h : PrimeSetBound P m) :
    PrimeSetBound (insert 2 P) (2 * m) := by
  classical
  intro r
  let e : ℕ := if r 2 % 2 = 0 then 1 else 0
  have he : e < 2 := by dsimp [e]; split_ifs <;> omega
  have hemod : ¬e ≡ r 2 [MOD 2] := by
    have hr := Nat.mod_lt (r 2) (by omega : 0 < 2)
    change ¬e % 2 = r 2 % 2
    dsimp [e]
    split_ifs <;> omega
  let t : ℕ → ℕ := fun q => r q + (q - 1) * e
  let r' : ℕ → ℕ := fun q => ((q + 1) / 2) * t q
  obtain ⟨i, hi, hia⟩ := h r'
  refine ⟨2 * i + e, by omega, ?_⟩
  intro q hq hbad
  rcases Finset.mem_insert.mp hq with rfl | hq
  · apply hemod
    simpa [Nat.ModEq] using hbad
  · obtain ⟨hqprime, hq2⟩ := hP q hq
    have hqodd : q % 2 = 1 := hqprime.mod_two_eq_one_iff_ne_two.mpr hq2
    have hhalf : 2 * ((q + 1) / 2) = q + 1 := by omega
    have hq1 : q - 1 + 1 = q := by have := hqprime.pos; omega
    have hbase : 2 * r' q + e ≡ r q [MOD q] := by
      have hteq : t q + e = r q + q * e := by dsimp [t]; nlinarith
      have heq : 2 * r' q + e = r q + q * (t q + e) := by
        dsimp [r']
        nlinarith
      rw [heq]
      simp
    have hm : 2 * i ≡ 2 * r' q [MOD q] :=
      Nat.ModEq.add_right_cancel' e (hbad.trans hbase.symm)
    have hgcd : Nat.gcd q 2 = 1 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, hqodd]
      norm_num
    exact hia q hq (Nat.ModEq.cancel_left_of_coprime hgcd hm)

/-- For odd prime sets, the least bound is doubled by adjoining 2. -/
theorem primeSetBound_insert_two_iff {P : Finset ℕ} {m : ℕ}
    (hP : ∀ q ∈ P, q.Prime ∧ q ≠ 2) :
    PrimeSetBound (insert 2 P) (2 * m) ↔ PrimeSetBound P m := by
  have h2 : 2 ∉ P := fun h => (hP 2 h).2 rfl
  exact ⟨primeSetBound_of_insert_two h2, primeSetBound_insert_two hP⟩

#print axioms primeSetBound_insert_two_iff
end Erdos970.IncrementReduction
