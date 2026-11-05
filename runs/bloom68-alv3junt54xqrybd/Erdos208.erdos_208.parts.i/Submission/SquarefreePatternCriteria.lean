import Submission.SquarefreeCubic
import Submission.SquarefreePatternExtraction

/-!
# A fixed-pattern counting criterion for squarefree intervals

A completely nonsquarefree interval supplies a positive-density set of
private large-prime-square witnesses. Block pigeonholing turns it into
linearly many occurrences of one fixed, bounded-width pattern. The final
criterion below is conditional on a strict upper bound for these actual
pattern occurrences; no such counting bound is assumed as an axiom.
-/

namespace SquarefreePatternCriteria

/-- An integer with a prime-square divisor whose prime exceeds the cutoff. -/
def LargePrimeSquare (Y m : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ Y < p ∧ p ^ 2 ∣ m

/-- Starts in a dyadic interval where every translate in `I` has a large
prime-square divisor. The witnesses may vary with the translate and start. -/
noncomputable def patternStarts (X Y : ℕ) (I : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc X (2 * X)).filter (fun n => ∀ i ∈ I, LargePrimeSquare Y (n + i))

/-- The explicit loss from the block width and the finite pattern list. -/
def patternConstant (k : ℕ) : ℕ := 48 * (24 * k) * 2 ^ (24 * k)

lemma patternConstant_pos {k : ℕ} (hk : 0 < k) : 0 < patternConstant k := by
  unfold patternConstant
  positivity

lemma mem_patternStarts {X Y n : ℕ} {I : Finset ℕ} :
    n ∈ patternStarts X Y I ↔ X ≤ n ∧ n ≤ 2 * X ∧
      ∀ i ∈ I, LargePrimeSquare Y (n + i) := by
  classical
  simp only [patternStarts, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The large-prime witnesses survive translating the interval back to its
finite set of offsets. -/
lemma survivors_offsets (N H : ℕ) (hH : 48 ≤ H)
    (hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 H ∧ H ≤ 12 * S.card ∧
      ∀ i ∈ S, LargePrimeSquare H (N + i) := by
  classical
  let T := SquarefreeCubic.survivors N H
  let S := T.image (fun m => m - N)
  have hT : ∀ m ∈ T, N < m ∧ m ≤ N + H := by
    intro m hm
    have h := SquarefreeCubic.mem_survivors.mp hm
    exact ⟨h.1, h.2.1⟩
  have hcard : S.card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    change a - N = b - N at hab
    obtain ⟨haN, _⟩ := hT a ha
    obtain ⟨hbN, _⟩ := hT b hb
    omega
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hmN, hmH⟩ := hT m hm
    simp only [Finset.mem_Icc]
    omega
  · rw [hcard]
    have h := SquarefreeCubic.survivors_card_ge_twelfth N H hH
    have hreal : (H : ℝ) ≤ 12 * (T.card : ℝ) := by
      dsimp [T]
      linarith
    exact_mod_cast hreal
  · intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hmN, hmH⟩ := hT m hm
    obtain ⟨p, q, hp, hpH, _, heq⟩ :=
      SquarefreeCubic.survivor_large_square hm (hbad m hmN hmH)
    refine ⟨p, hp, hpH, ?_⟩
    have hrecover : N + (m - N) = m := by omega
    rw [hrecover, heq]
    exact dvd_mul_left (p ^ 2) q

/-- A completely nonsquarefree interval forces one fixed pattern to have
many starts. No equidistribution or independence assumption is used. -/
theorem many_patternStarts_of_nonsquarefree (N H k : ℕ)
    (hk : 0 < k) (hH : 48 * k ≤ H) (hHN : H ≤ N)
    (hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    ∃ I : Finset ℕ, I ⊆ Finset.Icc 1 (24 * k) ∧ I.card = k ∧
      H ≤ patternConstant k * (patternStarts N H I).card := by
  classical
  have hH48 : 48 ≤ H := by nlinarith
  obtain ⟨S, hS, hdensity, hwitness⟩ := survivors_offsets N H hH48 hbad
  obtain ⟨I, hI, hIcard, hmany⟩ :=
    SquarefreePatternExtraction.exists_repeated_pattern k H S hk hH hS hdensity
  let B := 24 * k
  let M := (Finset.range (H / B + 1)).filter
    (fun j => ∀ i ∈ I, j * B + i ∈ S)
  have hB : 0 < B := by dsimp [B]; omega
  have hmap : M.card ≤ (patternStarts N H I).card := by
    apply Finset.card_le_card_of_injOn (fun j => N + j * B)
    · intro j hj
      change j ∈ M at hj
      obtain ⟨hjJ, hjS⟩ := Finset.mem_filter.mp hj
      have hjle : j ≤ H / B := by
        have := Finset.mem_range.mp hjJ
        omega
      have hjH : j * B ≤ H :=
        (Nat.mul_le_mul_right B hjle).trans (Nat.div_mul_le_self H B)
      change N + j * B ∈ patternStarts N H I
      apply mem_patternStarts.mpr
      refine ⟨by omega, by omega, ?_⟩
      intro i hi
      simpa only [Nat.add_assoc] using hwitness (j * B + i) (hjS i hi)
    · intro a _ b _ hab
      change N + a * B = N + b * B at hab
      have hm : a * B = b * B := by omega
      exact Nat.eq_of_mul_eq_mul_right hB hm
  refine ⟨I, hI, hIcard, ?_⟩
  have hmany' : H ≤ patternConstant k * M.card := by
    simpa only [patternConstant, M, B] using hmany
  exact hmany'.trans (Nat.mul_le_mul_left (patternConstant k) hmap)

/-- A strict upper bound for every bounded-width pattern excludes a
completely nonsquarefree interval. The counting premise is explicit. -/
theorem exists_squarefree_of_pattern_bound (N H k : ℕ)
    (hk : 0 < k) (hH : 48 * k ≤ H) (hHN : H ≤ N)
    (hcount : ∀ I : Finset ℕ, I ⊆ Finset.Icc 1 (24 * k) → I.card = k →
      patternConstant k * (patternStarts N H I).card < H) :
    ∃ m : ℕ, N < m ∧ m ≤ N + H ∧ Squarefree m := by
  classical
  by_contra h
  have hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m := by
    intro m hmN hmH hm
    exact h ⟨m, hmN, hmH, hm⟩
  obtain ⟨I, hI, hIcard, hmany⟩ :=
    many_patternStarts_of_nonsquarefree N H k hk hH hHN hbad
  exact (hcount I hI hIcard).not_ge hmany

end SquarefreePatternCriteria

#print axioms SquarefreePatternCriteria.many_patternStarts_of_nonsquarefree
#print axioms SquarefreePatternCriteria.exists_squarefree_of_pattern_bound
