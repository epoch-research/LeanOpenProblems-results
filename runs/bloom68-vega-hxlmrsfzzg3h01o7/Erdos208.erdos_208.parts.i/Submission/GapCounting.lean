import FormalConjecturesUtil

/-!
# Finite gap counting and three-point packing

Generic finite-combinatorial tools for an increasing sequence of natural numbers:

* isolated zero labels force many positive labels;
* monotone edge lengths telescope, and a total length budget bounds long edges;
* equal-gap edge fibres have distinct, separated natural-number starts;
* a set with no three ordered points of span at most `V` has at most two points
  in each quotient fibre `(d - a) / V`.

Edge lengths, spans in the natural-number interfaces, and all quotients use
`ℕ`. The integer-weight adapters state their pairwise differences in `ℤ`. The
scaled packing bound keeps the exact endpoint allowance `2*k*V` and has no extra
floor-loss term. No numeric FT estimate or unproved conjecture is used here.
-/

open Finset

namespace GapCounting

/-- An isolated-zero label sequence has at least half as many positive labels,
up to the two endpoint contributions. -/
theorem zero_isolation_count {T : ℕ} (k : ℕ → ℤ)
    (hnonneg : ∀ i < T, 0 ≤ k i)
    (hisolated : ∀ i, i + 1 < T → ¬ (k i = 0 ∧ k (i + 1) = 0)) :
    T + 1 ≤ 2 * ((range T).filter (fun i => 0 < k i)).card + 2 := by
  induction T using Nat.twoStepInduction with
  | zero => simp
  | one => omega
  | more n ih _ =>
    have hsmall := ih (fun i hi => hnonneg i (by omega))
      (fun i hi => hisolated i (by omega))
    have hpos : 0 < k n ∨ 0 < k (n + 1) := by
      have hn := hnonneg n (by omega)
      have hn1 := hnonneg (n + 1) (by omega)
      have hz := hisolated n (by omega)
      omega
    have hc : ((range n).filter (fun i => 0 < k i)).card + 1 ≤
        ((range (n + 2)).filter (fun i => 0 < k i)).card := by
      simp only [card_filter, sum_range_succ]
      rcases hpos with hpos | hpos <;> simp only [hpos, ↓reduceIte] <;> omega
    omega

/-- The isolated-zero count for labels indexed directly by `Fin T`.
Adjacency is stated using the natural-number values of the indices. -/
theorem zero_isolation_count_fin {T : ℕ} (k : Fin T → ℤ)
    (hnonneg : ∀ i, 0 ≤ k i)
    (hisolated : ∀ i j : Fin T, i.val + 1 = j.val → ¬ (k i = 0 ∧ k j = 0)) :
    T + 1 ≤ 2 * (univ.filter (fun i : Fin T => 0 < k i)).card + 2 := by
  let l : ℕ → ℤ := fun i => if h : i < T then k ⟨i, h⟩ else 0
  have hnonneg' : ∀ i < T, 0 ≤ l i := by
    intro i hi
    simpa [l, hi] using hnonneg ⟨i, hi⟩
  have hisolated' : ∀ i, i + 1 < T → ¬ (l i = 0 ∧ l (i + 1) = 0) := by
    intro i hi
    have hi' : i < T := by omega
    simpa [l, hi', hi] using hisolated ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
  have hc := zero_isolation_count l hnonneg' hisolated'
  have heq : ((range T).filter (fun i => 0 < l i)).card =
      (univ.filter (fun i : Fin T => 0 < k i)).card := by
    simp only [card_filter]
    rw [sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro i hi
    simp [l, mem_range.mp hi]
  rwa [heq] at hc

/-- The natural-number length of an edge of a finite sequence. -/
def edgeGap {T : ℕ} (f : Fin (T + 1) → ℕ) (i : Fin T) : ℕ :=
  f i.succ - f i.castSucc

/-- Edge lengths telescope for a monotone finite sequence. -/
theorem sum_edgeGap_eq {T : ℕ} {f : Fin (T + 1) → ℕ} (hf : Monotone f) :
    ∑ i : Fin T, edgeGap f i = f (Fin.last T) - f 0 := by
  unfold edgeGap
  rw [sum_tsub_distrib _ (fun i _ => hf (Fin.castSucc_le_succ i))]
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  omega

/-- A sequence whose first and last terms lie between `N` and `2*N` has total
edge length at most `N`. Only the two relevant endpoint inequalities are needed. -/
theorem sum_edgeGap_le_of_endpoints {T N : ℕ} {f : Fin (T + 1) → ℕ}
    (hf : Monotone f) (hfirst : N ≤ f 0) (hlast : f (Fin.last T) ≤ 2 * N) :
    ∑ i : Fin T, edgeGap f i ≤ N := by
  rw [sum_edgeGap_eq hf]
  omega

/-- Every edge of a strictly increasing natural-number sequence has positive length. -/
theorem edgeGap_pos {T : ℕ} {f : Fin (T + 1) → ℕ} (hf : StrictMono f)
    (i : Fin T) : 0 < edgeGap f i := by
  exact Nat.sub_pos_of_lt (hf Fin.castSucc_lt_succ)

/-- Edges longer than a given threshold. -/
def largeGapEdges {T : ℕ} (f : Fin (T + 1) → ℕ) (B : ℕ) : Finset (Fin T) :=
  univ.filter (fun i => B < edgeGap f i)

/-- Charging `B` to each edge longer than `B` does not exceed the total length.
No monotonicity or positivity assumption is needed for this charging step. -/
theorem mul_card_largeGapEdges_le_sum {T : ℕ} (f : Fin (T + 1) → ℕ) (B : ℕ) :
    B * (largeGapEdges f B).card ≤ ∑ i : Fin T, edgeGap f i := by
  calc
    B * (largeGapEdges f B).card = ∑ _i ∈ largeGapEdges f B, B := by simp [mul_comm]
    _ ≤ ∑ i ∈ largeGapEdges f B, edgeGap f i := by
      apply sum_le_sum
      intro i hi
      exact le_of_lt (mem_filter.mp hi).2
    _ ≤ ∑ i : Fin T, edgeGap f i := sum_le_sum_of_subset (subset_univ _)

/-- A total gap budget `N` bounds the number of edges longer than positive `B`
by the natural-number quotient `N / B`. -/
theorem card_largeGapEdges_le_div {T N B : ℕ} {f : Fin (T + 1) → ℕ}
    (hB : 0 < B) (hbudget : ∑ i : Fin T, edgeGap f i ≤ N) :
    (largeGapEdges f B).card ≤ N / B := by
  apply (Nat.le_div_iff_mul_le hB).mpr
  rw [mul_comm]
  exact (mul_card_largeGapEdges_le_sum f B).trans hbudget

/-- The large-edge count in an interval `[N, 2*N]`. -/
theorem card_largeGapEdges_le_div_of_endpoints {T N B : ℕ}
    {f : Fin (T + 1) → ℕ} (hf : Monotone f) (hB : 0 < B)
    (hfirst : N ≤ f 0) (hlast : f (Fin.last T) ≤ 2 * N) :
    (largeGapEdges f B).card ≤ N / B :=
  card_largeGapEdges_le_div hB (sum_edgeGap_le_of_endpoints hf hfirst hlast)

/-- An earlier edge ends no later than the start of any later edge. -/
theorem start_add_edgeGap_le_start {T : ℕ} {f : Fin (T + 1) → ℕ}
    (hf : Monotone f) {i j : Fin T} (hij : i < j) :
    f i.castSucc + edgeGap f i ≤ f j.castSucc := by
  have hi := hf (Fin.castSucc_le_succ i)
  have hj : f i.succ ≤ f j.castSucc := hf (by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij)
  unfold edgeGap
  omega

/-- In particular, the start of an edge of length `b` precedes every later
edge start by at least `b`. The later edge need not have the same length. -/
theorem start_add_le_start_of_gap_eq {T b : ℕ} {f : Fin (T + 1) → ℕ}
    (hf : Monotone f) {i j : Fin T} (hij : i < j) (hi : edgeGap f i = b) :
    f i.castSucc + b ≤ f j.castSucc := by
  simpa only [hi] using start_add_edgeGap_le_start hf hij

/-- The fibre of edges having length exactly `b`. -/
def fixedGapEdges {T : ℕ} (f : Fin (T + 1) → ℕ) (b : ℕ) : Finset (Fin T) :=
  univ.filter (fun i => edgeGap f i = b)

/-- Natural-number starts of the edges of length exactly `b`. -/
def fixedGapStarts {T : ℕ} (f : Fin (T + 1) → ℕ) (b : ℕ) : Finset ℕ :=
  (fixedGapEdges f b).image (fun i => f i.castSucc)

/-- Membership in the finite set of equal-gap starts. -/
theorem mem_fixedGapStarts {T b d : ℕ} {f : Fin (T + 1) → ℕ} :
    d ∈ fixedGapStarts f b ↔
      ∃ i : Fin T, edgeGap f i = b ∧ f i.castSucc = d := by
  simp [fixedGapStarts, fixedGapEdges]

/-- Passing from fixed-gap edge indices to their starts preserves cardinality
for a strictly increasing sequence. -/
theorem card_fixedGapStarts {T : ℕ} {f : Fin (T + 1) → ℕ}
    (hf : StrictMono f) (b : ℕ) :
    (fixedGapStarts f b).card = (fixedGapEdges f b).card := by
  apply card_image_iff.mpr
  intro i _ j _ hij
  exact Fin.castSucc_injective T (hf.injective hij)

/-- Distinct ordered members of the fixed-gap start set are `b`-separated. -/
theorem fixedGapStarts_separated {T b u v : ℕ} {f : Fin (T + 1) → ℕ}
    (hf : StrictMono f) (hu : u ∈ fixedGapStarts f b)
    (hv : v ∈ fixedGapStarts f b) (huv : u < v) : u + b ≤ v := by
  obtain ⟨i, hi, rfl⟩ := mem_fixedGapStarts.mp hu
  obtain ⟨j, _, rfl⟩ := mem_fixedGapStarts.mp hv
  have hij : i < j := Fin.castSucc_lt_castSucc_iff.mp (hf.lt_iff_lt.mp huv)
  exact start_add_le_start_of_gap_eq hf.monotone hij hi

/-- Every three ordered points of `S` have span strictly greater than `V`. -/
def TripleSeparated (S : Finset ℕ) (V : ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, u < v → v < w → V < w - u

/-- A finite natural-number set with more than two elements contains three
strictly ordered members. -/
theorem exists_ordered_triple {S : Finset ℕ} (hS : 2 < S.card) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, u < v ∧ v < w := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hS
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨a, ha, b, hb, c, hc, hab, hbc⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨a, ha, c, hc, b, hb, hac, hcb⟩
      · exact ⟨c, hc, a, ha, b, hb, hca, hab⟩
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact ⟨b, hb, a, ha, c, hc, hba, hac⟩
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨b, hb, c, hc, a, ha, hbc, hca⟩
      · exact ⟨c, hc, b, hb, a, ha, hcb, hba⟩

/-- Two points above `a` in the same quotient fibre are less than `V` apart. -/
theorem sub_lt_of_quotient_eq {a u w V : ℕ} (hV : 0 < V)
    (hu : a ≤ u) (hw : a ≤ w) (hq : (u - a) / V = (w - a) / V) :
    w - u < V := by
  have huq := Nat.mod_add_div (u - a) V
  have hwq := Nat.mod_add_div (w - a) V
  have hur := Nat.mod_lt (u - a) hV
  have hwr := Nat.mod_lt (w - a) hV
  rw [hq] at huq
  omega

/-- Each quotient fibre of a three-point separated set contains at most two
points. This applies in particular when `a` is the minimum of the set. -/
theorem card_quotient_fiber_le_two {S : Finset ℕ} {a V : ℕ}
    (hV : 0 < V) (ha : ∀ d ∈ S, a ≤ d) (hsep : TripleSeparated S V) (q : ℕ) :
    (S.filter (fun d => (d - a) / V = q)).card ≤ 2 := by
  by_contra! hc
  obtain ⟨u, hu, v, hv, w, hw, huv, hvw⟩ := exists_ordered_triple hc
  obtain ⟨huS, huq⟩ := mem_filter.mp hu
  obtain ⟨hvS, _⟩ := mem_filter.mp hv
  obtain ⟨hwS, hwq⟩ := mem_filter.mp hw
  have hlong := hsep u huS v hvS w hwS huv hvw
  have hshort := sub_lt_of_quotient_eq hV (ha u huS) (ha w hwS) (huq.trans hwq.symm)
  omega

/-- Quotient-fibre packing in an interval of length `D`, including the empty
set. The factor `2` is the allowance of two points per quotient fibre. -/
theorem packing_card_le_of_bounds {S : Finset ℕ} {a D V : ℕ}
    (hV : 0 < V) (hsep : TripleSeparated S V)
    (hS : ∀ d ∈ S, a ≤ d ∧ d ≤ a + D) :
    S.card ≤ 2 * (D / V + 1) := by
  have hmap : Set.MapsTo (fun d => (d - a) / V) (S : Set ℕ)
      (range (D / V + 1) : Set ℕ) := by
    intro d hd
    have hdD : d - a ≤ D := by have := (hS d hd).2; omega
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hdD))
  calc
    S.card = ∑ q ∈ range (D / V + 1), (S.filter (fun d => (d - a) / V = q)).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _q ∈ range (D / V + 1), 2 := by
      apply sum_le_sum
      intro q _
      exact card_quotient_fiber_le_two hV (fun d hd => (hS d hd).1) hsep q
    _ = 2 * (D / V + 1) := by simp [mul_comm]

/-- Packing in terms of the actual minimum and maximum of a nonempty set. -/
theorem packing_card_le_of_diameter {S : Finset ℕ} (hS : S.Nonempty) {D V : ℕ}
    (hV : 0 < V) (hsep : TripleSeparated S V)
    (hdiam : S.max' hS - S.min' hS ≤ D) :
    S.card ≤ 2 * (D / V + 1) := by
  apply packing_card_le_of_bounds (a := S.min' hS) hV hsep
  intro d hd
  have hlo := S.min'_le d hd
  have hhi := S.le_max' d hd
  exact ⟨hlo, by omega⟩

/-- A version of the diameter bound stated for all ordered pairs, so no
nonemptiness witness or extremum needs to be supplied. -/
theorem packing_card_le {S : Finset ℕ} {D V : ℕ} (hV : 0 < V)
    (hsep : TripleSeparated S V)
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, u < v → v - u ≤ D) :
    S.card ≤ 2 * (D / V + 1) := by
  by_cases hS : S.Nonempty
  · apply packing_card_le_of_diameter hS hV hsep
    by_cases hlt : S.min' hS < S.max' hS
    · exact hdiam _ (S.min'_mem hS) _ (S.max'_mem hS) hlt
    · omega
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

/-- The scaled diameter bound loses only `2*k*V` at the endpoints. No rounding
loss is introduced when the quotient estimate is multiplied out. The estimate
also holds for `k = 0`. -/
theorem packing_scaled_le_of_diameter {S : Finset ℕ} (hS : S.Nonempty)
    {k V L : ℕ} (hV : 0 < V) (hsep : TripleSeparated S V)
    (hdiam : k * (S.max' hS - S.min' hS) ≤ L) :
    k * V * S.card ≤ 2 * k * V + 2 * L := by
  let D := S.max' hS - S.min' hS
  have hc : S.card ≤ 2 * (D / V + 1) :=
    packing_card_le_of_diameter hS hV hsep le_rfl
  calc
    k * V * S.card ≤ k * V * (2 * (D / V + 1)) := Nat.mul_le_mul_left _ hc
    _ = 2 * k * V + 2 * (k * (D / V * V)) := by ring
    _ ≤ 2 * k * V + 2 * (k * D) := by
      gcongr
      exact Nat.div_mul_le_self D V
    _ ≤ 2 * k * V + 2 * L := by gcongr

/-- Scaled packing from a bound on every ordered pair. It includes empty and
singleton sets, for which the pairwise diameter hypothesis is vacuous. -/
theorem packing_scaled_le {S : Finset ℕ} {k V L : ℕ}
    (hV : 0 < V) (hsep : TripleSeparated S V)
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, u < v → k * (v - u) ≤ L) :
    k * V * S.card ≤ 2 * k * V + 2 * L := by
  by_cases hS : S.Nonempty
  · apply packing_scaled_le_of_diameter hS hV hsep
    by_cases hlt : S.min' hS < S.max' hS
    · exact hdiam _ (S.min'_mem hS) _ (S.max'_mem hS) hlt
    · have heq : S.max' hS - S.min' hS = 0 := by omega
      simp [heq]
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

/-- The frequently used `10*H` diameter budget gives the exact constant `20*H`. -/
theorem packing_scaled_le_twenty {S : Finset ℕ} {k V H : ℕ}
    (hV : 0 < V) (hsep : TripleSeparated S V)
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, u < v → k * (v - u) ≤ 10 * H) :
    k * V * S.card ≤ 2 * k * V + 20 * H := by
  have h := packing_scaled_le hV hsep hdiam
  simpa only [← mul_assoc, show 2 * 10 = (20 : ℕ) from rfl] using h

/-- Integer-weight version of scaled packing. Differences in the diameter
hypothesis are genuine integer differences. Nonnegativity of `L` is explicit,
as required for empty and singleton sets; positive integer labels satisfy `hk`. -/
theorem packing_scaled_le_int {S : Finset ℕ} {k L : ℤ} {V : ℕ}
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hV : 0 < V) (hsep : TripleSeparated S V)
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, u < v → k * ((v : ℤ) - u) ≤ L) :
    k * (V : ℤ) * (S.card : ℤ) ≤ 2 * k * (V : ℤ) + 2 * L := by
  have hdiamNat : ∀ u ∈ S, ∀ v ∈ S, u < v → k.toNat * (v - u) ≤ L.toNat := by
    intro u hu v hv huv
    have hd : (k.toNat : ℤ) * ((v - u : ℕ) : ℤ) ≤ (L.toNat : ℤ) := by
      simpa only [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hL, Nat.cast_sub huv.le]
        using hdiam u hu v hv huv
    exact_mod_cast hd
  have h := packing_scaled_le hV hsep hdiamNat
  have hc : (k.toNat : ℤ) * (V : ℤ) * (S.card : ℤ) ≤
      2 * (k.toNat : ℤ) * (V : ℤ) + 2 * (L.toNat : ℤ) := by
    exact_mod_cast h
  simpa only [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hL] using hc

/-- Integer labels with pairwise budget `10*H` give the same exact `20*H`
conclusion. `H ≥ 0` makes the statement valid even when `S` is empty. -/
theorem packing_scaled_le_twenty_int {S : Finset ℕ} {k H : ℤ} {V : ℕ}
    (hk : 0 ≤ k) (hH : 0 ≤ H) (hV : 0 < V) (hsep : TripleSeparated S V)
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, u < v → k * ((v : ℤ) - u) ≤ 10 * H) :
    k * (V : ℤ) * (S.card : ℤ) ≤ 2 * k * (V : ℤ) + 20 * H := by
  have h := packing_scaled_le_int hk (by positivity) hV hsep hdiam
  simpa only [← mul_assoc, show (2 : ℤ) * 10 = 20 from rfl] using h

end GapCounting
