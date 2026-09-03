import FormalConjecturesUtil

/-! A counterexample to obtaining balanced comparisons from doubling invariance alone.
This file does not disprove Erdős 371. -/

namespace DilationCounterexample

/-- Parity of the number of trailing zero bits, with value `false` at zero. -/
def mark : ℕ → Bool :=
  Nat.evenOddRec false (fun n b => if n = 0 then false else !b) (fun _ _ => false)

@[simp] lemma mark_zero : mark 0 = false := by simp [mark]

@[simp] lemma mark_even (n : ℕ) :
    mark (2 * n) = if n = 0 then false else !mark n := by
  unfold mark
  rw [Nat.evenOddRec_even _ _ _ (by simp)]

@[simp] lemma mark_odd (n : ℕ) : mark (2 * n + 1) = false := by
  unfold mark
  rw [Nat.evenOddRec_odd _ _ _ (by simp)]

/-- A nonnegative integer-valued function that is exactly invariant under doubling. -/
def height : ℕ → ℕ :=
  Nat.evenOddRec 0 (fun _ x => x) (fun n x => x + if mark n then 1 else 2)

@[simp] lemma height_zero : height 0 = 0 := by simp [height]

@[simp] lemma height_even (n : ℕ) : height (2 * n) = height n := by
  unfold height
  rw [Nat.evenOddRec_even _ _ _ rfl]

@[simp] lemma height_odd (n : ℕ) :
    height (2 * n + 1) = height n + if mark n then 1 else 2 := by
  unfold height
  rw [Nat.evenOddRec_odd _ _ _ rfl]

lemma even_ascent (n : ℕ) : height (2 * n) < height (2 * n + 1) := by
  simp only [height_even, height_odd]
  split_ifs <;> omega

lemma residue_five_ascent (n : ℕ) : height (8 * n + 5) < height (8 * n + 6) := by
  have h1 : 8 * n + 5 = 2 * (2 * (2 * n + 1)) + 1 := by omega
  have h2 : 8 * n + 6 = 2 * (2 * (2 * n + 1) + 1) := by omega
  rw [h1, h2, height_odd, height_even, height_even, height_odd]
  simp

lemma gap_classification (n : ℕ) (hn : 0 < n) :
    (mark n = true ∧ height (n + 1) = height n + 2) ∨
    (mark n = false ∧
      (height (n + 1) = height n + 1 ∨ height (n + 1) ≤ height n)) := by
  induction n using Nat.evenOddRec with
  | h0 => omega
  | h_even n ih =>
      have hn0 : n ≠ 0 := by omega
      simp only [height_even, height_odd, mark_even, if_neg hn0]
      cases mark n <;> simp
  | h_odd n ih =>
      have he : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      simp only [he, height_even, height_odd, mark_odd, Bool.false_eq_true,
        false_and, true_and, false_or]
      by_cases hn0 : n = 0
      · subst n
        decide +kernel
      · rcases ih (by omega) with ⟨hm, hg⟩ | ⟨hm, hg⟩
        · simp [hm, hg]
        · simp only [hm, Bool.false_eq_true, if_false]
          rcases hg with hg | hg <;> omega

lemma adjacent_ne {n : ℕ} (hn : 2 ≤ n) : height (n + 1) ≠ height n := by
  obtain ⟨k, hk | hk⟩ := n.even_or_odd'
  · subst n
    exact (even_ascent k).ne'
  · subst n
    have hkp : 0 < k := by omega
    have he : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [he, height_even, height_odd]
    rcases gap_classification k hkp with ⟨hm, hg⟩ | ⟨hm, hg⟩
    · simp [hm, hg]
    · simp only [hm, Bool.false_eq_true, if_false]
      rcases hg with hg | hg <;> omega

def easy (n : ℕ) : Prop := n % 2 = 0 ∨ n % 8 = 5

instance (n : ℕ) : Decidable (easy n) := inferInstanceAs (Decidable (_ ∨ _))

lemma easy_ascent {n : ℕ} (hn : easy n) : height n < height (n + 1) := by
  rcases hn with h | h
  · have he : n = 2 * (n / 2) := by omega
    rw [he]
    exact even_ascent _
  · have he : n = 8 * (n / 8) + 5 := by omega
    rw [he]
    exact residue_five_ascent _

lemma easy_count (N : ℕ) : ((Finset.range (8 * N)).filter easy).card = 5 * N := by
  let f : ℕ → ℕ := fun n => if easy n then 1 else 0
  have hp (n : ℕ) : f (8 + n) = f n := by simp [f, easy, Nat.add_mod]
  have hc (M : ℕ) : ((Finset.range M).filter easy).card =
      ∑ n ∈ Finset.range M, f n := by simp [f]
  rw [hc]
  induction N with
  | zero => simp
  | succ N ih =>
      have he : 8 * (N + 1) = 8 + 8 * N := by omega
      rw [he, Finset.sum_range_add]
      simp_rw [hp]
      rw [ih]
      have h8 : ∑ n ∈ Finset.range 8, f n = 5 := by decide +kernel
      rw [h8]
      omega

lemma ascent_count_lower (N : ℕ) :
    5 * N ≤ ((Finset.range (8 * N)).filter (fun n => height n < height (n + 1))).card := by
  rw [← easy_count]
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hr, he⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hr, easy_ascent he⟩

open Filter
open scoped Topology

lemma ascent_partialDensity (N : ℕ) :
    {n | height n < height (n + 1)}.partialDensity Set.univ N =
      (((Finset.range N).filter (fun n => height n < height (n + 1))).card : ℝ) / N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have he : {n | height n < height (n + 1)} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => height n < height (n + 1))) := by
    ext n
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma not_density_half : ¬{n | height n < height (n + 1)}.HasDensity (1 / 2) := by
  intro h
  have ht : Tendsto (fun N : ℕ => 8 * (N + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hlim := h.comp ht
  have hlower (N : ℕ) : (5 / 8 : ℝ) ≤
      {n | height n < height (n + 1)}.partialDensity Set.univ (8 * (N + 1)) := by
    rw [ascent_partialDensity]
    have hpos : (0 : ℝ) < (8 * (N + 1) : ℕ) := by positivity
    apply (le_div_iff₀ hpos).mpr
    have hc : (5 : ℝ) * (N + 1) ≤
        (((Finset.range (8 * (N + 1))).filter
          (fun n => height n < height (n + 1))).card : ℝ) := by
      exact_mod_cast ascent_count_lower (N + 1)
    push_cast
    linarith
  have hh : (5 / 8 : ℝ) ≤ 1 / 2 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hlower)
  norm_num at hh

/-- This rules out a proof based only on doubling invariance and eventual absence of ties. -/
theorem doubling_invariance_is_insufficient :
    ∃ f : ℕ → ℕ, (∀ n, f (2 * n) = f n) ∧
      (∀ n ≥ 2, f (n + 1) ≠ f n) ∧
      ¬{n | f n < f (n + 1)}.HasDensity (1 / 2) :=
  ⟨height, height_even, fun _ hn => adjacent_ne hn, not_density_half⟩

end DilationCounterexample

#print axioms DilationCounterexample.doubling_invariance_is_insufficient
