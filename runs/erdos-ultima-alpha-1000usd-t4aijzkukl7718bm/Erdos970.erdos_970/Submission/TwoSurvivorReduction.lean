import Submission.IncrementReduction

/-!
An exact characterization of adjoining a prime larger than a known interval bound.
This isolates a necessary part of the unproved increment estimate; it does not prove
that estimate or settle Erdős 970.
-/
namespace Erdos970.IncrementReduction

def PrimeSetTwoBound (P : Finset ℕ) (m : ℕ) : Prop :=
  ∀ r : ℕ → ℕ, ∃ i < m, ∃ j < m, i ≠ j ∧
    (∀ q ∈ P, ¬i ≡ r q [MOD q]) ∧ (∀ q ∈ P, ¬j ≡ r q [MOD q])

theorem primeSetBound_translate {P : Finset ℕ} {g : ℕ}
    (hpos : ∀ q ∈ P, 0 < q) (h : PrimeSetBound P g)
    (r : ℕ → ℕ) (a : ℕ) :
    ∃ i < g, ∀ q ∈ P, ¬(a + i) ≡ r q [MOD q] := by
  let r' : ℕ → ℕ := fun q => r q + (q - 1) * a
  obtain ⟨i, hi, havoid⟩ := h r'
  refine ⟨i, hi, fun q hq hbad => havoid q hq ?_⟩
  have hbase : a + r' q ≡ r q [MOD q] := by
    have hq1 : q - 1 + 1 = q := by have := hpos q hq; omega
    have heq : a + r' q = r q + q * a := by dsimp [r']; nlinarith
    rw [heq]
    simp
  exact Nat.ModEq.add_left_cancel' a (hbad.trans hbase.symm)

theorem primeSetTwoBound_of_insert {P : Finset ℕ} {p m : ℕ}
    (hp : p ∉ P) (h : PrimeSetBound (insert p P) m) :
    PrimeSetTwoBound P m := by
  classical
  intro r
  obtain ⟨i, hi, hia⟩ := h (Function.update r p 0)
  obtain ⟨j, hj, hja⟩ := h (Function.update r p i)
  have hne (q : ℕ) (hq : q ∈ P) : q ≠ p := by
    intro hqp
    exact hp (hqp ▸ hq)
  refine ⟨i, hi, j, hj, ?_, ?_, ?_⟩
  · intro hij
    have hh := hja p (Finset.mem_insert_self _ _)
    apply hh
    simp [hij, Nat.ModEq]
  · intro q hq
    simpa [Function.update_of_ne (hne q hq)] using
      hia q (Finset.mem_insert_of_mem hq)
  · intro q hq
    simpa [Function.update_of_ne (hne q hq)] using
      hja q (Finset.mem_insert_of_mem hq)

theorem primeSetBound_insert_of_two {P : Finset ℕ} {p g m : ℕ}
    (hpos : ∀ q ∈ P, 0 < q) (hg : PrimeSetBound P g) (hgp : g < p)
    (hm : PrimeSetTwoBound P m) : PrimeSetBound (insert p P) m := by
  classical
  intro r
  by_contra hbad
  push_neg at hbad
  have hforced (x : ℕ) (hx : x < m) (hxa : ∀ q ∈ P, ¬x ≡ r q [MOD q]) :
      x ≡ r p [MOD p] := by
    obtain ⟨q, hq, hxq⟩ := hbad x hx
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hxq
    · exact False.elim (hxa q hq hxq)
  obtain ⟨i, hi, j, hj, hij, hia, hja⟩ := hm r
  wlog hijlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hja hia (by omega)
  have hmod : j ≡ i [MOD p] := (hforced j hj hja).trans (hforced i hi hia).symm
  have hdvd : p ∣ j - i := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  have hgap : p ≤ j - i := Nat.le_of_dvd (by omega) hdvd
  obtain ⟨t, ht, hta⟩ := primeSetBound_translate hpos hg r (i + 1)
  have htm : i + 1 + t < m := by omega
  have htmod : i + 1 + t ≡ i [MOD p] :=
    (hforced _ htm hta).trans (hforced i hi hia).symm
  have htmod' : 1 + t ≡ 0 [MOD p] := by
    apply Nat.ModEq.add_left_cancel' i
    simpa only [Nat.add_assoc, Nat.add_zero] using htmod
  have hteq : 1 + t = 0 := htmod'.eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- For a sufficiently large new prime, adjoining it is exactly a two-survivor test. -/
theorem primeSetBound_insert_iff_two {P : Finset ℕ} {p g m : ℕ}
    (hp : p ∉ P) (hpos : ∀ q ∈ P, 0 < q) (hg : PrimeSetBound P g)
    (hgp : g < p) :
    PrimeSetBound (insert p P) m ↔ PrimeSetTwoBound P m :=
  ⟨primeSetTwoBound_of_insert hp, primeSetBound_insert_of_two hpos hg hgp⟩

/-- The proposed recurrence necessarily gives this two-survivor strengthening. -/
theorem two_survivors_of_largestPrimeIncrement (hstep : LargestPrimeIncrement)
    {P : Finset ℕ} {g : ℕ} (hne : P.Nonempty)
    (hP : ∀ q ∈ P, q.Prime) (hg : PrimeSetBound P g) :
    PrimeSetTwoBound P (g + 2 * P.card) := by
  classical
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (P.sup id + 1)
  have hlt (q : ℕ) (hq : q ∈ P) : q < p := by
    have hqle : q ≤ P.sup id := Finset.le_sup (f := id) hq
    omega
  have hpP : p ∉ P := fun h => (hlt p h).false
  exact primeSetTwoBound_of_insert hpP
    (hstep P p g hne hp (fun q hq => ⟨hP q hq, hlt q hq⟩) hg)

#print axioms primeSetBound_insert_iff_two
#print axioms two_survivors_of_largestPrimeIncrement
end Erdos970.IncrementReduction
