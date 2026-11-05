import Submission.WalkTreeFacts

/-! A pruned, unmerged stopped walk yielding mixed trees with small timeout mass. -/

namespace ErdosDSS.TreeCode

open scoped BigOperators

namespace Walk

open Tree

noncomputable section

/-- The stopped ±1 walk. A branch is pruned only when it cannot reach a boundary. -/
def build (q : ℕ) : ℕ → ℤ → Tree
  | 0, s => tip (decide (|s| = (q : ℤ)))
  | n + 1, s =>
    if |s| = (q : ℤ) then tip true
    else if ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s| then tip false
    else fork (build q n (s + 1)) (build q n (s - 1))

lemma build_boundary {q n : ℕ} {s : ℤ} (hb : |s| = (q : ℤ)) :
    build q n s = tip true := by
  cases n <;> simp [build, hb]

lemma build_isNode_iff (q n : ℕ) (s : ℤ) :
    (build q n s).isNode = true ↔
      0 < n ∧ |s| ≠ (q : ℤ) ∧ (q : ℤ) - |s| ≤ (n : ℤ) := by
  cases n with
  | zero => simp [build, isNode]
  | succ n =>
    by_cases hb : |s| = (q : ℤ)
    · rw [build, if_pos hb]
      simp [isNode, hb]
    · by_cases hp : ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s|
      · rw [build, if_neg hb, if_pos hp]
        simp only [isNode, Bool.false_eq_true, false_iff]
        omega
      · have hle : (q : ℤ) - |s| ≤ ((n + 1 : ℕ) : ℤ) := by omega
        rw [build, if_neg hb, if_neg hp]
        constructor
        · intro _; exact ⟨Nat.succ_pos _, hb, hle⟩
        · intro _; rfl

lemma build_hasAbs_of_notNode {q n : ℕ} {s : ℤ}
    (hn : (build q n s).isNode = false) :
    (build q n s).hasAbs = decide (|s| = (q : ℤ)) := by
  cases n with
  | zero => rfl
  | succ n =>
    by_cases hb : |s| = (q : ℤ)
    · rw [build, if_pos hb]
      simp [hasAbs, hb]
    · by_cases hp : ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s|
      · rw [build, if_neg hb, if_pos hp]
        simp [hasAbs, hb]
      · rw [build, if_neg hb, if_neg hp] at hn
        simp [isNode] at hn

lemma build_pruned_of_notNode {q n : ℕ} {s : ℤ} (hnpos : 0 < n)
    (hb : |s| ≠ (q : ℤ)) (hn : (build q n s).isNode = false) :
    (n : ℤ) < (q : ℤ) - |s| := by
  by_contra hp
  have hnode := (build_isNode_iff q n s).mpr ⟨hnpos, hb, by omega⟩
  simp [hn] at hnode

/-- Opposite parities rule out querying exactly at the remaining boundary distance. -/
lemma active_distance {q n : ℕ} {s : ℤ} (hq : q % 2 = 0)
    (hp : (s + ((n + 1 : ℕ) : ℤ)) % 2 = 1)
    (hr : |s| ≤ (q : ℤ)) (hb : |s| ≠ (q : ℤ))
    (hd : (q : ℤ) - |s| ≤ ((n + 1 : ℕ) : ℤ)) :
    |s| < (q : ℤ) ∧ (q : ℤ) - |s| ≤ (n : ℤ) := by
  constructor
  · omega
  · have hq' : (q : ℤ) % 2 = 0 := by exact_mod_cast hq
    by_cases hs : 0 ≤ s
    · rw [abs_of_nonneg hs] at hd ⊢
      omega
    · rw [abs_of_nonpos (by omega : s ≤ 0)] at hd ⊢
      omega

lemma neighbor_range {q : ℕ} {s : ℤ} (hs : |s| < (q : ℤ)) :
    |s + 1| ≤ (q : ℤ) ∧ |s - 1| ≤ (q : ℤ) := by
  have hs' := abs_lt.mp hs
  constructor <;> apply abs_le.mpr <;> omega

lemma nearer_neighbor {q n : ℕ} {s : ℤ}
    (hs : |s| < (q : ℤ)) (hd : (q : ℤ) - |s| ≤ (n : ℤ)) :
    0 < n ∧ ((q : ℤ) - |s + 1| ≤ (n : ℤ) ∨
      (q : ℤ) - |s - 1| ≤ (n : ℤ)) := by
  constructor
  · omega
  · by_cases h : 0 ≤ s
    · left
      rw [abs_of_nonneg h] at hd
      rw [abs_of_nonneg (by omega : 0 ≤ s + 1)]
      omega
    · right
      rw [abs_of_nonpos (by omega : s ≤ 0)] at hd
      rw [abs_of_nonpos (by omega : s - 1 ≤ 0)]
      omega

lemma not_both_boundary {q : ℕ} {s : ℤ} (hq : 2 ≤ q) :
    ¬ (|s + 1| = (q : ℤ) ∧ |s - 1| = (q : ℤ)) := by
  intro h
  rw [abs_eq (by positivity), abs_eq (by positivity)] at h
  rcases h with ⟨h, h'⟩
  rcases h with h | h <;> rcases h' with h' | h' <;> omega

/-- Every cherry has exactly one boundary leaf and one pruned timeout. -/
theorem build_mixed (q n : ℕ) (s : ℤ) (hq : 2 ≤ q) (heven : q % 2 = 0)
    (hr : |s| ≤ (q : ℤ)) (hpar : (s + (n : ℤ)) % 2 = 1) :
    (build q n s).Mixed := by
  induction n generalizing s with
  | zero => simp [build, Mixed]
  | succ n ih =>
    by_cases hb : |s| = (q : ℤ)
    · rw [build, if_pos hb]
      trivial
    · by_cases hpr : ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s|
      · rw [build, if_neg hb, if_pos hpr]
        trivial
      · have hd : (q : ℤ) - |s| ≤ ((n + 1 : ℕ) : ℤ) := by omega
        obtain ⟨hs, hdist⟩ := active_distance heven hpar hr hb hd
        obtain ⟨hleft, hright⟩ := neighbor_range hs
        have hpl : (s + 1 + (n : ℤ)) % 2 = 1 := by omega
        have hpr' : (s - 1 + (n : ℤ)) % 2 = 1 := by omega
        rw [build, if_neg hb, if_neg hpr]
        refine ⟨ih (s + 1) hleft hpl, ih (s - 1) hright hpr', ?_⟩
        intro hnl hnr
        rw [build_hasAbs_of_notNode hnl, build_hasAbs_of_notNode hnr]
        obtain ⟨hnpos, hnear⟩ := nearer_neighbor hs hdist
        have hone : |s + 1| = (q : ℤ) ∨ |s - 1| = (q : ℤ) := by
          rcases hnear with hl | hr
          · left
            by_contra hbl
            have := build_pruned_of_notNode hnpos hbl hnl
            omega
          · right
            by_contra hbr
            have := build_pruned_of_notNode hnpos hbr hnr
            omega
        have hnot := not_both_boundary (s := s) hq
        rcases hone with hbl | hbr
        · have hbr : |s - 1| ≠ (q : ℤ) := by
            intro hbr
            exact hnot ⟨hbl, hbr⟩
          simp [hbl, hbr]
        · have hbl : |s + 1| ≠ (q : ℤ) := by
            intro hbl
            exact hnot ⟨hbl, hbr⟩
          simp [hbl, hbr]

/-- Leaf states stay in the closed interval, and absorbing states are on its boundary. -/
theorem build_leaf_state (q n : ℕ) (s : ℤ) (hr : |s| ≤ (q : ℤ)) :
    ∀ j : (build q n s).Leaf,
      |s + displacement (build q n s) j| ≤ (q : ℤ) ∧
        ((build q n s).absorbed j = true →
          |s + displacement (build q n s) j| = (q : ℤ)) := by
  induction n generalizing s with
  | zero =>
    intro j
    simp only [build, displacement, absorbed, add_zero]
    exact ⟨hr, of_decide_eq_true⟩
  | succ n ih =>
    by_cases hb : |s| = (q : ℤ)
    · rw [build, if_pos hb]
      simp [displacement, absorbed, hb]
    · by_cases hpr : ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s|
      · rw [build, if_neg hb, if_pos hpr]
        simp [displacement, absorbed, hr]
      · have hs : |s| < (q : ℤ) := by omega
        obtain ⟨hleft, hright⟩ := neighbor_range hs
        rw [build, if_neg hb, if_neg hpr]
        intro j
        cases j with
        | inl j =>
          simpa [displacement, absorbed, ← add_assoc] using ih (s + 1) hleft j
        | inr j =>
          simpa [displacement, absorbed, ← add_assoc, sub_eq_add_neg] using
            ih (s - 1) hright j

/-- A timeout can occur only with fewer than `q` steps left. -/
theorem build_timeout_depth (q n : ℕ) (s : ℤ) (hq : 0 < q) :
    ∀ j : (build q n s).Leaf, (build q n s).absorbed j = false →
      (n : ℤ) < (q : ℤ) + ((build q n s).depth j : ℤ) := by
  induction n generalizing s with
  | zero =>
    intro j hj
    have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
    simpa [build, depth] using hq'
  | succ n ih =>
    by_cases hb : |s| = (q : ℤ)
    · rw [build, if_pos hb]
      simp [absorbed]
    · by_cases hpr : ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s|
      · rw [build, if_neg hb, if_pos hpr]
        intro j hj
        simp only [depth, Nat.cast_zero, add_zero]
        have := abs_nonneg s
        omega
      · rw [build, if_neg hb, if_neg hpr]
        intro j hj
        cases j with
        | inl j =>
          have h := ih (s + 1) j hj
          simp only [depth, Nat.cast_add, Nat.cast_one]
          omega
        | inr j =>
          have h := ih (s - 1) j hj
          simp only [depth, Nat.cast_add, Nat.cast_one]
          omega

/-- The even horizon has ample room for the depth and first-moment estimates. -/
def horizon (q : ℕ) : ℕ := 16 * q ^ 2

/-- The unmerged walk starts in state `1`, including the matrix root's `1`. -/
def tree (q : ℕ) : Tree := build q (horizon q) 1

lemma horizon_even (q : ℕ) : Even (horizon q) := by
  refine ⟨8 * q ^ 2, ?_⟩
  unfold horizon
  ring

lemma horizon_parity (q : ℕ) : (1 + (horizon q : ℤ)) % 2 = 1 := by
  simp [horizon, Int.add_emod, Int.mul_emod]

lemma le_square {q : ℕ} (hq : 2 ≤ q) : q ≤ q ^ 2 := by
  nlinarith

lemma le_horizon {q : ℕ} (hq : 2 ≤ q) : q ≤ horizon q := by
  have hs := le_square hq
  unfold horizon
  omega

/-- The walk tree is mixed for every positive even boundary of size at least two. -/
theorem tree_mixed (q : ℕ) (hq : 2 ≤ q) (heven : Even q) : (tree q).Mixed := by
  apply build_mixed q (horizon q) 1 hq (Nat.even_iff.mp heven)
  · norm_num
    omega
  · exact horizon_parity q

/-- The start is an active query, never a boundary or pruned leaf. -/
theorem tree_isNode (q : ℕ) (hq : 2 ≤ q) : (tree q).isNode = true := by
  apply (build_isNode_iff q (horizon q) 1).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hh := le_horizon hq
    omega
  · norm_num
    omega
  · have hh : (q : ℤ) ≤ (horizon q : ℤ) := by exact_mod_cast le_horizon hq
    norm_num
    omega

/-- Every column's charge is the integer walk state at that leaf. -/
theorem tree_leaf_charge_bound (q : ℕ) (hq : 2 ≤ q) (j : (tree q).Leaf) :
    |charge (fun i => (tree q).path i j)| ≤ (q : ℤ) := by
  rw [path_charge]
  apply (build_leaf_state q (horizon q) 1 ?_ j).1
  norm_num
  omega

/-- Absorbing columns have precisely one of the two prescribed charges. -/
theorem tree_absorbing_charge (q : ℕ) (hq : 2 ≤ q) (j : (tree q).Leaf)
    (hj : (tree q).absorbed j = true) :
    charge (fun i => (tree q).path i j) = (q : ℤ) ∨
      charge (fun i => (tree q).path i j) = -(q : ℤ) := by
  rw [path_charge]
  apply (abs_eq (by positivity : (0 : ℤ) ≤ (q : ℤ))).mp
  apply (build_leaf_state q (horizon q) 1 ?_ j).2 hj
  norm_num
  omega

/-- Timeouts lie strictly beyond horizon minus the boundary size. -/
theorem tree_timeout_depth_cutoff (q : ℕ) (hq : 2 ≤ q) (j : (tree q).Leaf)
    (hj : (tree q).absorbed j = false) :
    horizon q - q + 1 ≤ (tree q).depth j := by
  have hd := build_timeout_depth q (horizon q) 1 (by omega : 0 < q) j hj
  have hd' : horizon q < q + (tree q).depth j := by exact_mod_cast hd
  have hh := le_horizon hq
  omega

/-- The long horizon makes every timeout depth at least eight boundary squares. -/
theorem tree_timeout_depth_large (q : ℕ) (hq : 2 ≤ q) (j : (tree q).Leaf)
    (hj : (tree q).absorbed j = false) :
    8 * q ^ 2 ≤ (tree q).depth j := by
  have hd := tree_timeout_depth_cutoff q hq j hj
  have hs := le_square hq
  unfold horizon at hd
  omega

/-- In particular all timeout depths are at least the requested charge size. -/
theorem tree_timeout_depth (q : ℕ) (hq : 2 ≤ q) (j : (tree q).Leaf)
    (hj : (tree q).absorbed j = false) : q ≤ (tree q).depth j := by
  have hd := tree_timeout_depth_large q hq j hj
  have hs := le_square hq
  omega

lemma square_slack {q : ℕ} {s : ℤ} (hs : |s| ≤ (q : ℤ)) :
    0 ≤ (q : ℚ) ^ 2 - (s : ℚ) ^ 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hs
  have hl' : -(q : ℚ) ≤ (s : ℚ) := by exact_mod_cast hl
  have hu' : (s : ℚ) ≤ (q : ℚ) := by exact_mod_cast hu
  have hprod := mul_nonneg (sub_nonneg.mpr hu')
    (show 0 ≤ (q : ℚ) + (s : ℚ) by linarith)
  nlinarith

/-- The quadratic stopped-walk potential bounds the number of queries. -/
theorem build_expectedDepth_le (q n : ℕ) (s : ℤ) (hr : |s| ≤ (q : ℤ)) :
    expectedDepth (build q n s) ≤ (q : ℚ) ^ 2 - (s : ℚ) ^ 2 := by
  induction n generalizing s with
  | zero =>
    rw [build, expectedDepth]
    exact square_slack hr
  | succ n ih =>
    by_cases hb : |s| = (q : ℤ)
    · rw [build, if_pos hb, expectedDepth]
      exact square_slack hr
    · by_cases hpr : ((n + 1 : ℕ) : ℤ) < (q : ℤ) - |s|
      · rw [build, if_neg hb, if_pos hpr, expectedDepth]
        exact square_slack hr
      · have hs : |s| < (q : ℤ) := by omega
        obtain ⟨hleft, hright⟩ := neighbor_range hs
        rw [build, if_neg hb, if_neg hpr, expectedDepth]
        have hl := ih (s + 1) hleft
        have hr' := ih (s - 1) hright
        push_cast at hl hr'
        nlinarith only [hl, hr']

/-- Starting at `1` saves one unit of the quadratic potential. -/
theorem tree_expectedDepth_le (q : ℕ) (hq : 2 ≤ q) :
    expectedDepth (tree q) ≤ (q : ℚ) ^ 2 - 1 := by
  have hs : |(1 : ℤ)| ≤ (q : ℤ) := by
    norm_num
    omega
  simpa [tree] using build_expectedDepth_le q (horizon q) 1 hs

/-- All timeout mass lies at depth at least `8*q²`. -/
theorem tree_timeout_first_moment (q : ℕ) (hq : 2 ≤ q) :
    (8 * (q : ℚ) ^ 2) * (tree q).tau ≤ expectedDepth (tree q) := by
  apply timeout_mass_mul_le_expectedDepth
  intro j hj
  exact_mod_cast tree_timeout_depth_large q hq j hj

/-- The rational first-moment estimate gives the requested one-eighth tail bound. -/
theorem tree_tau_le_one_eighth (q : ℕ) (hq : 2 ≤ q) :
    (tree q).tau ≤ (1 / 8 : ℚ) := by
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
  refine le_of_mul_le_mul_left (a := 8 * (q : ℚ) ^ 2) ?_ (by positivity)
  calc
    (8 * (q : ℚ) ^ 2) * (tree q).tau ≤ expectedDepth (tree q) :=
      tree_timeout_first_moment q hq
    _ ≤ (q : ℚ) ^ 2 - 1 := tree_expectedDepth_le q hq
    _ ≤ (8 * (q : ℚ) ^ 2) * (1 / 8) := by nlinarith

/-- The complete walk-tree existence certificate for every even `q ≥ 2`. -/
theorem exists_tree (q : ℕ) (hq : 2 ≤ q) (heven : Even q) :
    ∃ t : Tree, t.Mixed ∧ t.isNode = true ∧
      (∀ j : t.Leaf, t.absorbed j = true →
        charge (fun i => t.path i j) = (q : ℤ) ∨
          charge (fun i => t.path i j) = -(q : ℤ)) ∧
      (∀ j : t.Leaf, t.absorbed j = false → q ≤ t.depth j) ∧
      t.tau ≤ (1 / 8 : ℚ) := by
  refine ⟨tree q, tree_mixed q hq heven, tree_isNode q hq, ?_, ?_,
    tree_tau_le_one_eighth q hq⟩
  · exact tree_absorbing_charge q hq
  · exact tree_timeout_depth q hq

/-- A stronger certificate retaining the quadratic lower bound on timeout depth. -/
theorem exists_tree_strong (q : ℕ) (hq : 2 ≤ q) (heven : Even q) :
    ∃ t : Tree, t.Mixed ∧ t.isNode = true ∧
      (∀ j : t.Leaf, t.absorbed j = true →
        charge (fun i => t.path i j) = (q : ℤ) ∨
          charge (fun i => t.path i j) = -(q : ℤ)) ∧
      (∀ j : t.Leaf, t.absorbed j = false → 8 * q ^ 2 ≤ t.depth j) ∧
      t.tau ≤ (1 / 8 : ℚ) := by
  refine ⟨tree q, tree_mixed q hq heven, tree_isNode q hq, ?_, ?_,
    tree_tau_le_one_eighth q hq⟩
  · exact tree_absorbing_charge q hq
  · exact tree_timeout_depth_large q hq

end

end Walk

end ErdosDSS.TreeCode
