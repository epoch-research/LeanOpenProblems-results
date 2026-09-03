import Submission.TwoSurvivorReduction

/-!
Exact reduction from arbitrary interval bounds to gaps following a surviving position.
This justifies imposing nonzero forbidden residues when searching for maximal gaps.
-/
namespace Erdos970.IncrementReduction

def PrimeSetNextBound (P : Finset ℕ) (m : ℕ) : Prop :=
  ∀ r : ℕ → ℕ, (∀ q ∈ P, ¬0 ≡ r q [MOD q]) →
    ∃ i, 0 < i ∧ i ≤ m ∧ ∀ q ∈ P, ¬i ≡ r q [MOD q]

theorem primeSetBound_factorial (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) :
    PrimeSetBound P (P.card + 1).factorial := by
  classical
  intro r
  by_contra h
  push_neg at h
  exact ((not_isJacobsthalBound_iff_cover P.card (P.card + 1).factorial).mpr
    ⟨P, hP, le_rfl, r, h⟩) (isJacobsthalBound_factorial P.card)

theorem primeSetNextBound_of_bound {P : Finset ℕ} {m : ℕ}
    (hP : ∀ q ∈ P, 0 < q) (h : PrimeSetBound P m) : PrimeSetNextBound P m := by
  intro r hr
  obtain ⟨i, hi, ha⟩ := primeSetBound_translate hP h r 1
  exact ⟨1 + i, by omega, by omega, ha⟩

theorem primeSetBound_of_next {P : Finset ℕ} {m : ℕ}
    (hP : ∀ q ∈ P, q.Prime) (h : PrimeSetNextBound P m) : PrimeSetBound P m := by
  classical
  intro r
  by_contra hbad
  push_neg at hbad
  let g := (P.card + 1).factorial
  let Q := g * ∏ q ∈ P, q
  have hgpos : 0 < g := Nat.factorial_pos _
  have hprod : 0 < ∏ q ∈ P, q := Finset.prod_pos fun q hq => (hP q hq).pos
  have hgQ : g ≤ Q := by dsimp [Q]; nlinarith
  have hQ : 0 < Q := lt_of_lt_of_le hgpos hgQ
  have hqdvd (q : ℕ) (hq : q ∈ P) : q ∣ Q := by
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem (fun q => q) hq
  let S := (Finset.range Q).filter (fun i => ∀ q ∈ P, ¬i ≡ r q [MOD q])
  have hSne : S.Nonempty := by
    obtain ⟨i, hi, ha⟩ := primeSetBound_factorial P hP r
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hi.trans_le hgQ), ha⟩⟩
  let a := S.max' hSne
  have haS : a ∈ S := Finset.max'_mem S hSne
  have haQ : a < Q := Finset.mem_range.mp (Finset.mem_filter.mp haS).1
  have haa : ∀ q ∈ P, ¬a ≡ r q [MOD q] := (Finset.mem_filter.mp haS).2
  let r' : ℕ → ℕ := fun q => r q + (q - 1) * a
  have hbase (q : ℕ) (hq : q ∈ P) : a + r' q ≡ r q [MOD q] := by
    have hq1 : q - 1 + 1 = q := by have := (hP q hq).pos; omega
    have heq : a + r' q = r q + q * a := by dsimp [r']; nlinarith
    rw [heq]
    simp
  have hzero : ∀ q ∈ P, ¬0 ≡ r' q [MOD q] := by
    intro q hq hmod
    apply haa q hq
    have hh := hmod.add_left a
    simpa only [Nat.add_zero] using hh.trans (hbase q hq)
  obtain ⟨t, ht0, htm, hta⟩ := h r' hzero
  have hata : ∀ q ∈ P, ¬(a + t) ≡ r q [MOD q] := by
    intro q hq hmod
    exact hta q hq (Nat.ModEq.add_left_cancel' a (hmod.trans (hbase q hq).symm))
  by_cases hatQ : a + t < Q
  · have hatS : a + t ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hatQ, hata⟩
    have hle : a + t ≤ a := Finset.le_max' S (a + t) hatS
    omega
  · have htlt : a + t - Q < m := by omega
    obtain ⟨q, hq, hmod⟩ := hbad (a + t - Q) htlt
    apply hata q hq
    have hQzero : Q ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr (hqdvd q hq)
    have hh := hmod.add hQzero
    simpa only [Nat.add_zero, Nat.sub_add_cancel (by omega : Q ≤ a + t)] using hh

theorem primeSetBound_iff_next {P : Finset ℕ} {m : ℕ}
    (hP : ∀ q ∈ P, q.Prime) :
    PrimeSetBound P m ↔ PrimeSetNextBound P m :=
  ⟨primeSetNextBound_of_bound (fun q hq => (hP q hq).pos), primeSetBound_of_next hP⟩

#print axioms primeSetBound_iff_next
end Erdos970.IncrementReduction
