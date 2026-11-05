import Submission.GraphInterface

/-!
# Conditional criteria for an eventual diagonal Ramsey ratio gap

Write `R n = hypergraphRamsey 2 n`. An eventual avoiding graph whose order is at least
`(1 + δ) * (R n - 1)`, for a fixed real `δ > 0`, suffices for a positive eventual ratio gap.
In particular, avoiding graphs of order `2 * (R n - 1)` suffice, with ratio constant `1/2`.

The doubled-order hypothesis can be viewed as an eventual self-completion sufficient
criterion: an eventual construction completing two critical-size parts to a graph with
neither an `(n + 1)`-clique nor an `(n + 1)`-clique in its complement would supply it.
This file neither assumes nor proves such a construction or its eventual existence;
the graph existence statements occur only as hypotheses of implications.

The last theorem gives the exact negation of a positive eventual ratio gap as arbitrarily
late relative gaps smaller than every positive real `ε`. All results are conditional
implications or an equivalence; none asserts a resolution of the ratio problem.
-/

namespace Erdos812.RatioCriteria

open Combinatorics Filter

local notation "R" => hypergraphRamsey 2

/-- Eventual avoiding graphs with a fixed fractional increase over critical order give a
positive eventual ratio gap. The graph order bound supplies the extra `+ 1` required by
`Support.extension_implies_ratio`. -/
theorem fixed_factor_avoiding_graphs_imply_ratio {δ : ℝ} (hδ : 0 < δ)
    (hgraphs : ∀ᶠ n : ℕ in atTop,
      ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
        G.CliqueFree (n + 1) ∧ Gᶜ.CliqueFree (n + 1) ∧
          (1 + δ) * ((R n : ℝ) - 1) ≤ (m : ℝ)) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (R (n + 1) : ℝ) / (R n : ℝ) ≥ 1 + c := by
  apply Support.extension_implies_ratio hδ
  filter_upwards [hgraphs] with n hn
  obtain ⟨m, G, hr, hb, hsize⟩ := hn
  have horder : m + 1 ≤ R (n + 1) :=
    Nat.succ_le_of_lt (Support.graph_order_lt_ramsey G hr hb)
  have horder_real : (m : ℝ) + 1 ≤ (R (n + 1) : ℝ) := by
    exact_mod_cast horder
  linarith

/-- Eventual existence of a graph on twice the critical order avoiding both next targets
is sufficient. In fact one may choose `c = 1/2`; the existence hypothesis is not proved here.
The subtraction inside the vertex order is natural-number subtraction. -/
theorem doubled_avoiding_graphs_imply_ratio
    (hgraphs : ∀ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin (2 * (R n - 1))),
        G.CliqueFree (n + 1) ∧ Gᶜ.CliqueFree (n + 1)) :
    ∃ c > (0 : ℝ), (1 / 2 : ℝ) ≤ c ∧
      ∀ᶠ n : ℕ in atTop, (R (n + 1) : ℝ) / (R n : ℝ) ≥ 1 + c := by
  refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
  filter_upwards [hgraphs, eventually_ge_atTop (2 : ℕ)] with n hn hn₂
  obtain ⟨G, hr, hb⟩ := hn
  have hR_nat : 2 ≤ R n := hn₂.trans (Support.target_le_graph_ramsey n)
  have hR : (2 : ℝ) ≤ (R n : ℝ) := by exact_mod_cast hR_nat
  have hpos : (0 : ℝ) < (R n : ℝ) := by linarith
  have hpred : ((R n - 1 : ℕ) : ℝ) = (R n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ R n)]
    norm_num
  have horder : 2 * (R n - 1) + 1 ≤ R (n + 1) :=
    Nat.succ_le_of_lt (Support.graph_order_lt_ramsey G hr hb)
  have horder_real : (2 : ℝ) * ((R n : ℝ) - 1) + 1 ≤ (R (n + 1) : ℝ) := by
    rw [← hpred]
    exact_mod_cast horder
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- Failure of every positive eventual ratio gap is exactly the existence, past each
cutoff, of a positive-index gap smaller than any prescribed positive fraction of `R n`. -/
theorem not_eventual_ratio_iff_small_gaps :
    ¬ (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (R (n + 1) : ℝ) / (R n : ℝ) ≥ 1 + c) ↔
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ 1 ≤ n ∧ (R (n + 1) : ℝ) - (R n : ℝ) < ε * (R n : ℝ) := by
  classical
  constructor
  · intro h ε hε N
    have hnot : ¬ ∀ᶠ n : ℕ in atTop,
        (R (n + 1) : ℝ) / (R n : ℝ) ≥ 1 + ε := by
      intro hevent
      exact h ⟨ε, hε, hevent⟩
    rw [eventually_atTop] at hnot
    push_neg at hnot
    obtain ⟨n, hn, hratio⟩ := hnot (max N 1)
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn₁ : 1 ≤ n := (le_max_right N 1).trans hn
    have hpos : (0 : ℝ) < (R n : ℝ) := by
      exact_mod_cast Support.graph_ramsey_pos (by omega : 0 < n)
    refine ⟨n, hnN, hn₁, ?_⟩
    have hlt := (div_lt_iff₀ hpos).1 hratio
    nlinarith
  · intro hgaps hratio
    obtain ⟨c, hc, hevent⟩ := hratio
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    obtain ⟨n, hnN, hn₁, hgap⟩ := hgaps c hc N
    have hpos : (0 : ℝ) < (R n : ℝ) := by
      exact_mod_cast Support.graph_ramsey_pos (by omega : 0 < n)
    have hge := (le_div_iff₀ hpos).1 (hN n hnN)
    nlinarith

#print axioms fixed_factor_avoiding_graphs_imply_ratio
#print axioms doubled_avoiding_graphs_imply_ratio
#print axioms not_eventual_ratio_iff_small_gaps

end Erdos812.RatioCriteria
