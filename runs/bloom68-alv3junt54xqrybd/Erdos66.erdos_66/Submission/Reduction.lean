import FormalConjecturesUtil
import Mathlib.Order.KonigLemma

/-!
# Finite-prefix reductions for Erdős Problem 66

This module does not import either admitted conjecture theorem.
-/

open Filter AdditiveCombinatorics
open scoped Topology
set_option linter.style.namespace false
set_option linter.style.stubs false
set_option linter.style.openClassical false

namespace Erdos66.Compactness

lemma positive_limit_of_sumRep {A : Set ℕ} {c : ℝ}
    (hc : c ≠ 0)
    (h : Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) : 0 < c := by
  have hnonneg : 0 ≤ c := ge_of_tendsto h (Filter.Eventually.of_forall fun n =>
    div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  exact lt_of_le_of_ne hnonneg (Ne.symm hc)

lemma sumRep_prefix_local {A B : Set ℕ} {n : ℕ}
    (h : ∀ i ≤ n, i ∈ A ↔ i ∈ B) : sumRep A n = sumRep B n := by
  classical
  rw [sumRep_def, sumRep_def]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p hp
  have hs : p.1 + p.2 = n := by simpa using hp
  exact and_congr (h p.1 (by omega)) (h p.2 (by omega))

lemma finite_set_has_zero_limit {A : Set ℕ} (hA : A.Finite) :
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 0) := by
  classical
  obtain ⟨M, hM⟩ := hA.bddAbove
  have hzero : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ) / Real.log n = 0 := by
    filter_upwards [eventually_gt_atTop (2 * M)] with n hn
    have hs : sumRep A n = 0 := by
      rw [sumRep_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp hmem
      have hp' : p.1 + p.2 = n := by simpa using hp
      have h1 := hM hmem.1
      have h2 := hM hmem.2
      omega
    simp only [hs, Nat.cast_zero, zero_div]
  have hz' : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) :=
    hzero.mono fun _ h => h.symm
  exact tendsto_const_nhds.congr' hz'

lemma finite_set_cannot_witness {A : Set ℕ} {c : ℝ} (hA : A.Finite)
    (h : Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) : c = 0 :=
  tendsto_nhds_unique h (finite_set_has_zero_limit hA)

lemma boolean_finite_prefix_compactness
    (P : ℕ → (ℕ → Bool) → Prop)
    (hloc : ∀ n f g, (∀ i ≤ n, f i = g i) → (P n f ↔ P n g))
    (hfin : ∀ N, ∃ f, ∀ n ≤ N, P n f) : ∃ f, ∀ n, P n f := by
  classical
  let α : ℕ → Type := fun N => {b : Fin (N + 1) → Bool //
    ∃ f : ℕ → Bool, (∀ i : Fin (N + 1), b i = f i) ∧ ∀ n ≤ N, P n f}
  let π : {i j : ℕ} → i ≤ j → α j → α i := fun {i j} hij b =>
    ⟨fun t => b.val ⟨t.val, by omega⟩, by
      obtain ⟨f, hf, hP⟩ := b.property
      exact ⟨f, fun t => hf ⟨t.val, by omega⟩, fun n hn => hP n (hn.trans hij)⟩⟩
  have hnonempty : ∀ N, Nonempty (α N) := by
    intro N
    obtain ⟨f, hf⟩ := hfin N
    exact ⟨⟨fun t => f t.val, f, fun _ => rfl, hf⟩⟩
  letI : ∀ N, Nonempty (α N) := hnonempty
  have hrefl : ∀ i (a : α i), π le_rfl a = a := by
    intros
    apply Subtype.ext
    rfl
  have htrans : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (a : α k),
      π hij (π hjk a) = π (hij.trans hjk) a := by
    intros
    apply Subtype.ext
    rfl
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
    (by intro i a; exact hrefl i a)
    (by intro i j k hij hjk a; exact htrans i j k hij hjk a)
    (fun _ _ => Set.toFinite _)
  let g : ℕ → Bool := fun i => (f i).val ⟨i, Nat.lt_succ_self i⟩
  refine ⟨g, fun n => ?_⟩
  obtain ⟨u, hu, hPu⟩ := (f n).property
  have hgu : ∀ i ≤ n, g i = u i := by
    intro i hi
    have hcoh := congrArg (fun a : α i => a.val ⟨i, Nat.lt_succ_self i⟩) (hf hi)
    calc
      g i = (f n).val ⟨i, by omega⟩ := hcoh.symm
      _ = u i := hu ⟨i, by omega⟩
  exact (hloc n g u hgu).mpr (hPu n le_rfl)

lemma finite_prefix_approximation_gives_limit
    (c : ℝ) (hc : 0 < c) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (N0 : ℕ)
    (hfin : ∀ M : ℕ, ∃ A : Set ℕ, ∀ n : ℕ, N0 ≤ n → n ≤ M →
      |(sumRep A n : ℝ) / Real.log n - c| ≤ e n) :
    ∃ A : Set ℕ, c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  classical
  let P : ℕ → (ℕ → Bool) → Prop := fun n f => N0 ≤ n →
    |(sumRep {i | f i = true} n : ℝ) / Real.log n - c| ≤ e n
  have hloc : ∀ n f g, (∀ i ≤ n, f i = g i) → (P n f ↔ P n g) := by
    intro n f g hfg
    have hsum : sumRep {i | f i = true} n = sumRep {i | g i = true} n := by
      apply sumRep_prefix_local
      intro i hi
      simp only [Set.mem_setOf_eq, hfg i hi]
    simp only [P, hsum]
  have hfin' : ∀ M, ∃ f, ∀ n ≤ M, P n f := by
    intro M
    obtain ⟨A, hA⟩ := hfin M
    refine ⟨fun i => decide (i ∈ A), fun n hn hN => ?_⟩
    simpa [P] using hA n hN hn
  obtain ⟨f, hf⟩ := boolean_finite_prefix_compactness P hloc hfin'
  refine ⟨{i | f i = true}, ne_of_gt hc, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have heε := (tendsto_order.mp he).2 ε hε
  filter_upwards [eventually_ge_atTop N0, heε] with n hn hne
  rw [Real.dist_eq]
  exact (hf n hn).trans_lt hne

end Erdos66.Compactness
