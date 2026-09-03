import Submission.SummableDivisorCover

/-!
A finite optimization criterion for a summable cube-divisor cover.
A uniform bound on the reciprocal weights is still required; this file does
not establish such a bound and does not settle Erdős 1206.
-/

namespace Erdos1206
open Filter Finset
open scoped Classical Topology

/-- A finite forbidden-divisor set meeting every nontrivial positive cubic
collision whose roots are at most `N`. -/
def FiniteCubeDivisorCover (N : ℕ) (B : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ Set.Icc 1 N → b ∈ Set.Icc 1 N →
    c ∈ Set.Icc 1 N → d ∈ Set.Icc 1 N →
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → a ≠ c → a ≠ d →
    ∃ p ∈ B, p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d

/-- Uniformly bounded finite cover weights yield a global summable cover.
The bound `C` is arbitrary; no hypothesis `C < 1` is needed. -/
lemma summable_divisor_cover_of_uniform_finite_covers (C : ℝ)
    (h : ∀ N : ℕ, ∃ B : Finset ℕ, 1 ∉ B ∧
      (∑ p ∈ B, (1 : ℝ) / p) ≤ C ∧ FiniteCubeDivisorCover N B) :
    ∃ D : Set ℕ, 1 ∉ D ∧ IsCubeDivisorCover D ∧
      Summable (fun p : ℕ => if p ∈ D then (1 : ℝ) / p else 0) := by
  classical
  choose B h1 hsum hcover using h
  let x : ℕ → ℕ → Bool := fun N p => decide (p ∈ B N)
  obtain ⟨f, φ, hφ, hf⟩ := SeqCompactSpace.tendsto_subseq x
  let D : Set ℕ := {p | f p = true}
  have hev (p : ℕ) : ∀ᶠ j in atTop, (p ∈ B (φ j) ↔ p ∈ D) := by
    have ht := (tendsto_pi_nhds.mp hf) p
    have he := ht.eventually (isOpen_discrete {f p} |>.mem_nhds (by simp))
    filter_upwards [he] with j hj
    change decide (p ∈ B (φ j)) = f p at hj
    change (p ∈ B (φ j)) ↔ f p = true
    rw [← hj]
    simp
  have hpre (M : ℕ) : ∃ j : ℕ, M ≤ φ j ∧
      ∀ p ≤ M, (p ∈ B (φ j) ↔ p ∈ D) := by
    have he : ∀ᶠ j in atTop, ∀ p ∈ range (M + 1),
        (p ∈ B (φ j) ↔ p ∈ D) :=
      (Finset.eventually_all _).mpr (fun p _ => hev p)
    have hb : ∀ᶠ j : ℕ in atTop, M ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop M)
    obtain ⟨j, hj, hj'⟩ := (hb.and he).exists
    exact ⟨j, hj, fun p hp => hj' p (mem_range.mpr (by omega))⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · obtain ⟨j, _, hj⟩ := hpre 1
    exact fun hD => h1 (φ j) ((hj 1 le_rfl).mpr hD)
  · intro a b c d ha hb hc hd heq hac had
    let M := a + b + c + d
    obtain ⟨j, hj, hmem⟩ := hpre M
    obtain ⟨p, hp, hpd⟩ := hcover (φ j) a b c d
      ⟨ha, by dsimp [M] at hj; omega⟩
      ⟨hb, by dsimp [M] at hj; omega⟩
      ⟨hc, by dsimp [M] at hj; omega⟩
      ⟨hd, by dsimp [M] at hj; omega⟩ heq hac had
    have hpM : p ≤ M := by
      rcases hpd with hpa | hpb | hpc | hpd
      · have := Nat.le_of_dvd ha hpa; dsimp [M]; omega
      · have := Nat.le_of_dvd hb hpb; dsimp [M]; omega
      · have := Nat.le_of_dvd hc hpc; dsimp [M]; omega
      · have := Nat.le_of_dvd hd hpd; dsimp [M]; omega
    exact ⟨p, (hmem p hpM).mp hp, hpd⟩
  · apply summable_of_sum_range_le (c := C)
    · intro p; split_ifs <;> positivity
    · intro M
      obtain ⟨j, _, hj⟩ := hpre M
      calc
        (∑ p ∈ range M, @ite ℝ (p ∈ D) (Classical.propDecidable _) (1 / p) 0) =
            ∑ p ∈ (range M).filter (fun p => p ∈ B (φ j)), (1 : ℝ) / p := by
          rw [Finset.sum_filter]
          apply sum_congr rfl
          intro p hp
          by_cases hpD : p ∈ D
          · have hpB := (hj p (mem_range.mp hp).le).mpr hpD
            simp [hpD, hpB]
          · have hpB : p ∉ B (φ j) := fun hh => hpD ((hj p (mem_range.mp hp).le).mp hh)
            simp [hpD, hpB]
        _ ≤ ∑ p ∈ B (φ j), (1 : ℝ) / p := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp; exact (mem_filter.mp hp).2
          · intro p hp hnot; positivity
        _ ≤ C := hsum (φ j)

/-- A single uniform real bound on finite divisor-cover weights would imply the
conjecture. Existence of this bound is not proved. -/
lemma uniform_finite_divisor_covers_suffice (C : ℝ)
    (h : ∀ N : ℕ, ∃ B : Finset ℕ, 1 ∉ B ∧
      (∑ p ∈ B, (1 : ℝ) / p) ≤ C ∧ FiniteCubeDivisorCover N B) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  obtain ⟨D, h1, hc, hs⟩ := summable_divisor_cover_of_uniform_finite_covers C h
  exact summable_divisor_cover_suffices hc h1 hs



/-- The finite uniform-weight condition is equivalent to the existence of a
summable divisor cover. It is not asserted to be equivalent to the original
conjecture, since a positive-density witness need not be a divisor avoider. -/
lemma summable_cover_iff_uniform_finite_covers :
    (∃ D : Set ℕ, 1 ∉ D ∧ IsCubeDivisorCover D ∧
      Summable (fun p : ℕ => if p ∈ D then (1 : ℝ) / p else 0)) ↔
    (∃ C : ℝ, ∀ N : ℕ, ∃ B : Finset ℕ, 1 ∉ B ∧
      (∑ p ∈ B, (1 : ℝ) / p) ≤ C ∧ FiniteCubeDivisorCover N B) := by
  classical
  constructor
  · rintro ⟨D, h1, hc, hs⟩
    let w : ℕ → ℝ := fun p => if p ∈ D then 1 / p else 0
    have hw : Summable w := hs
    refine ⟨∑' p, w p, fun N => ?_⟩
    let B := (range (N + 1)).filter (fun p => p ∈ D)
    refine ⟨B, ?_, ?_, ?_⟩
    · intro hh
      exact h1 (mem_filter.mp hh).2
    · calc
        (∑ p ∈ B, (1 : ℝ) / p) = ∑ p ∈ B, w p := by
          apply sum_congr rfl
          intro p hp
          simp [w, (mem_filter.mp hp).2]
        _ ≤ ∑' p, w p := hw.sum_le_tsum B (fun p _ => by dsimp [w]; split_ifs <;> positivity)
    · intro a b c d ha hb hc' hd heq hac had
      obtain ⟨p, hp, hpd⟩ := hc a b c d ha.1 hb.1 hc'.1 hd.1 heq hac had
      have hpN : p ≤ N := by
        rcases hpd with hpa | hpb | hpc | hpd
        · exact (Nat.le_of_dvd ha.1 hpa).trans ha.2
        · exact (Nat.le_of_dvd hb.1 hpb).trans hb.2
        · exact (Nat.le_of_dvd hc'.1 hpc).trans hc'.2
        · exact (Nat.le_of_dvd hd.1 hpd).trans hd.2
      exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩, hpd⟩
  · rintro ⟨C, h⟩
    exact summable_divisor_cover_of_uniform_finite_covers C h

end Erdos1206
