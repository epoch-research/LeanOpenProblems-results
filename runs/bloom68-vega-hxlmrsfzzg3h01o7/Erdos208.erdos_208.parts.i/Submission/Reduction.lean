import FormalConjecturesUtil

/-!
# Exact reductions for the squarefree-gap conjecture

The lemmas in this development do not assume either theorem in `Spec.lean`.
They separate the finite enumeration facts from the unresolved short-interval estimate.
-/

open Filter Real

namespace SquarefreeGaps

noncomputable def seq : ℕ → ℕ := Nat.nth Squarefree

lemma seq_strictMono : StrictMono seq := Nat.nth_strictMono Nat.squarefree_infinite

lemma seq_squarefree (n : ℕ) : Squarefree (seq n) :=
  Nat.nth_mem_of_infinite Nat.squarefree_infinite n

lemma seq_pos (n : ℕ) : 0 < seq n := Nat.pos_of_ne_zero (seq_squarefree n).ne_zero

lemma seq_tendsto : Tendsto seq atTop atTop := seq_strictMono.tendsto_atTop

lemma next_le {n q : ℕ} (hq : Squarefree q) (hlt : seq n < q) : seq (n + 1) ≤ q := by
  by_contra hn
  exact (not_lt_of_ge (Nat.le_nth_of_lt_nth_succ (Nat.lt_of_not_ge hn) hq)) hlt

lemma gap_nonneg (n : ℕ) : 0 ≤ (seq (n + 1) - seq n : ℝ) := by
  exact sub_nonneg.mpr (Nat.cast_le.mpr (seq_strictMono.monotone (Nat.le_succ n)))

/-- The asymptotic property at a fixed exponent, with precisely the target's norms and casts. -/
def GapBound (ε : ℝ) : Prop :=
  (fun n => (seq (n + 1) - seq n : ℝ)) =O[atTop] (fun n => (seq n : ℝ)^ε)

/-- A squarefree integer in every sufficiently large interval, allowing an ε-dependent constant. -/
def IntervalBound (ε : ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
    ∃ q : ℕ, Squarefree q ∧ x < q ∧ (q - x : ℝ) ≤ C * (x : ℝ)^ε

lemma gap_of_interval {ε : ℝ} (h : IntervalBound ε) : GapBound ε := by
  rcases h with ⟨C, hC, h⟩
  apply Asymptotics.isBigO_iff'.mpr
  refine ⟨C, hC, ?_⟩
  filter_upwards [seq_tendsto.eventually h] with n hn
  rcases hn with ⟨q, hq, hnq, hbound⟩
  have hs : (seq (n+1) : ℝ) ≤ q := Nat.cast_le.mpr (next_le hq hnq)
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg n), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact le_trans (sub_le_sub_right hs _) hbound

lemma exists_preceding (x N : ℕ) (hx : seq N ≤ x) :
    ∃ n : ℕ, N ≤ n ∧ seq n ≤ x ∧ x < seq (n + 1) := by
  classical
  have hc : N + 1 ≤ Nat.count Squarefree (x + 1) := by
    rw [← Nat.count_nth_succ_of_infinite Nat.squarefree_infinite N]
    exact Nat.count_monotone Squarefree (Nat.succ_le_succ hx)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.count Squarefree (x + 1) ≠ 0 by omega)
  refine ⟨n, by omega, ?_, ?_⟩
  · have hncount : n < Nat.count Squarefree (x + 1) := by omega
    have := Nat.nth_lt_of_lt_count hncount
    exact Nat.le_of_lt_succ this
  · have := Nat.le_nth_count Nat.squarefree_infinite (x + 1)
    rw [hn] at this
    exact this

lemma interval_of_gap {ε : ℝ} (hε : 0 ≤ ε) (h : GapBound ε) : IntervalBound ε := by
  rcases Asymptotics.isBigO_iff'.mp h with ⟨C, hC, h⟩
  rcases Filter.eventually_atTop.mp h with ⟨N, hN⟩
  refine ⟨C, hC, Filter.eventually_atTop.mpr ⟨seq N, ?_⟩⟩
  intro x hx
  obtain ⟨n, hn, hnx, hxn⟩ := exists_preceding x N hx
  refine ⟨seq (n+1), seq_squarefree (n+1), hxn, ?_⟩
  have hb := hN n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg n), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hb
  calc
    (seq (n+1) - x : ℝ) ≤ seq (n+1) - seq n :=
      sub_le_sub_left (Nat.cast_le.mpr hnx) _
    _ ≤ C * (seq n : ℝ)^ε := hb
    _ ≤ C * (x : ℝ)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hnx) hε) hC.le

lemma gap_iff_interval {ε : ℝ} (hε : 0 ≤ ε) : GapBound ε ↔ IntervalBound ε :=
  ⟨interval_of_gap hε, gap_of_interval⟩

/-- A weak but unconditional baseline using Bertrand's postulate. -/
lemma gapBound_of_one_le {ε : ℝ} (hε : 1 ≤ ε) : GapBound ε := by
  apply gap_of_interval
  refine ⟨1, by norm_num, Filter.eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro x hx
  obtain ⟨p, hp, hxp, hpx⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
  refine ⟨p, hp.squarefree, hxp, ?_⟩
  have hpx' : (p : ℝ) ≤ 2 * x := by exact_mod_cast hpx
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  calc
    (p - x : ℝ) ≤ x := by linarith
    _ ≤ (x : ℝ)^ε := Real.self_le_rpow_of_one_le hx' hε
    _ = 1 * (x : ℝ)^ε := (one_mul _).symm

/-- In the all-positive-exponents statement the interval constant may be fixed to one. -/
lemma all_gap_iff_unit_intervals :
    (∀ ε > (0 : ℝ), GapBound ε) ↔
      ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
        ∃ q : ℕ, Squarefree q ∧ x < q ∧ (q - x : ℝ) ≤ (x : ℝ)^ε := by
  constructor
  · intro h ε hε
    have hhalf : 0 < ε / 2 := by positivity
    obtain ⟨C, _, hC⟩ := interval_of_gap hhalf.le (h (ε / 2) hhalf)
    have hlim : Tendsto (fun x : ℕ => (x : ℝ)^(ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
    filter_upwards [hC, hlim.eventually (eventually_ge_atTop C), eventually_ge_atTop 1]
      with x hx hxC hx1
    obtain ⟨q, hq, hxq, hb⟩ := hx
    refine ⟨q, hq, hxq, hb.trans ?_⟩
    calc
      C * (x : ℝ)^(ε / 2) ≤ (x : ℝ)^(ε / 2) * (x : ℝ)^(ε / 2) :=
        mul_le_mul_of_nonneg_right hxC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (x : ℝ)^(ε / 2 + ε / 2) :=
        (Real.rpow_add (by exact_mod_cast (show 0 < x by omega)) _ _).symm
      _ = (x : ℝ)^ε := by congr 1; ring
  · intro h ε hε
    apply gap_of_interval
    refine ⟨1, by norm_num, ?_⟩
    simpa only [one_mul] using h ε hε

#print axioms all_gap_iff_unit_intervals
#print axioms gapBound_of_one_le

end SquarefreeGaps
