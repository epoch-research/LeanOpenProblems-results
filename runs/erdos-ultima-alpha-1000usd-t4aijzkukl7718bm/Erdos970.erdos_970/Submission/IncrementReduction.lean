import Submission.Work

/-!
A conditional route to Erdős 970. The largest-prime increment estimate is an explicit
hypothesis here; this file does not establish that estimate or settle the conjecture.
-/

namespace Erdos970.IncrementReduction

def PrimeSetBound (P : Finset ℕ) (m : ℕ) : Prop :=
  ∀ r : ℕ → ℕ, ∃ i : ℕ, i < m ∧ ∀ p ∈ P, ¬i ≡ r p [MOD p]

theorem primeSetBound_mono {P : Finset ℕ} {m m' : ℕ}
    (h : PrimeSetBound P m) (hmm' : m ≤ m') : PrimeSetBound P m' := by
  intro r
  obtain ⟨i, hi, havoids⟩ := h r
  exact ⟨i, hi.trans_le hmm', havoids⟩

theorem primeSetBound_singleton (p : ℕ) (hp : p.Prime) : PrimeSetBound {p} 2 := by
  intro r
  by_cases h0 : 0 ≡ r p [MOD p]
  · refine ⟨1, by omega, ?_⟩
    intro q hq h1
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    have h01 : (0 : ℕ) ≡ 1 [MOD p] := h0.trans h1.symm
    have := h01.eq_of_lt_of_lt hp.pos hp.one_lt
    omega
  · refine ⟨0, by omega, ?_⟩
    intro q hq
    simpa only [Finset.mem_singleton.mp hq] using h0

/-- This is the unproved recurrence being investigated, stated without choosing a maximum gap. -/
def LargestPrimeIncrement : Prop :=
  ∀ (P : Finset ℕ) (p g : ℕ), P.Nonempty → p.Prime →
    (∀ q ∈ P, q.Prime ∧ q < p) →
    PrimeSetBound P g → PrimeSetBound (insert p P) (g + 2 * P.card)

theorem primeSetBound_quadratic_of_increment (hstep : LargestPrimeIncrement) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      PrimeSetBound P (P.card * (P.card - 1) + 2) := by
  classical
  intro P
  induction P using Finset.induction_on_max with
  | h0 =>
    intro hP r
    exact ⟨0, by simp, by simp⟩
  | @step p P hlt ih =>
    intro hP
    have hp : p.Prime := hP p (Finset.mem_insert_self _ _)
    have hPprime : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hpP : p ∉ P := by
      intro hh
      exact (hlt p hh).false
    by_cases hne : P.Nonempty
    · have hh := hstep P p (P.card * (P.card - 1) + 2) hne hp
        (fun q hq => ⟨hPprime q hq, hlt q hq⟩) (ih hPprime)
      have hpos : 0 < P.card := Finset.card_pos.mpr hne
      have heq : P.card * (P.card - 1) + 2 + 2 * P.card =
          (insert p P).card * ((insert p P).card - 1) + 2 := by
        rw [Finset.card_insert_of_notMem hpP]
        have hsub : P.card - 1 + 1 = P.card := by omega
        simp only [Nat.add_sub_cancel]
        nlinarith
      rwa [← heq]
    · have he : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst P
      simpa using primeSetBound_singleton p hp

/-- The recurrence would imply the original real-valued quadratic conjecture, with `C = 2`. -/
theorem quadratic_bound_of_increment (hstep : LargestPrimeIncrement) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  refine ⟨2, by norm_num, fun k hk => ?_⟩
  have hb : IsJacobsthalBound k (2 * k ^ 2) := by
    by_contra hbad
    obtain ⟨P, hP, hPk, r, hcover⟩ :=
      (not_isJacobsthalBound_iff_cover k (2 * k ^ 2)).mp hbad
    have hsize : P.card * (P.card - 1) + 2 ≤ 2 * k ^ 2 := by
      have h1 : P.card * (P.card - 1) ≤ k * (k - 1) :=
        Nat.mul_le_mul hPk (Nat.sub_le_sub_right hPk 1)
      have hk1 : k - 1 + 1 = k := by omega
      nlinarith
    obtain ⟨i, hi, havoids⟩ :=
      primeSetBound_mono (primeSetBound_quadratic_of_increment hstep P hP) hsize r
    obtain ⟨p, hp, hip⟩ := hcover i hi
    exact havoids p hp hip
  have hh := (jacobsthalFunction_le_iff k (2 * k ^ 2)).mpr hb
  exact_mod_cast hh

#print axioms quadratic_bound_of_increment
end Erdos970.IncrementReduction
