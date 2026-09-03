import Mathlib

/-!
# Integer incidence trades for a finite sieve

This file does not import `Submission.Spec` and proves no form of Erdős 970.
It records exact, covering-specific integer identities for incidence arrays.
An odd Boolean-cube trade removes an uncovered row and changes just one
positive intersection count. Feasibility is a separate, explicit condition.
-/

namespace IntegerSieve

open Finset

variable {α : Type*} [DecidableEq α]

/-- The upper-set transform of an integer incidence histogram. -/
def upperCount (P : Finset α) (w : Finset α → ℤ) (S : Finset α) : ℤ :=
  ∑ T ∈ P.powerset, if S ⊆ T then w T else 0

/-- The signed coefficients of `- ∏ i ∈ R, (1 - zᵢ)`. -/
def oddCube (R T : Finset α) : ℤ :=
  if T ⊆ R then -(-1 : ℤ) ^ T.card else 0

lemma alternating_upper_sum (R S : Finset α) :
    (∑ T ∈ R.powerset, if S ⊆ T then (-1 : ℤ) ^ T.card else 0) =
      if S = R then (-1 : ℤ) ^ R.card else 0 := by
  induction R using Finset.induction_on generalizing S with
  | empty => simp
  | @insert a R ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have hnot (T : Finset α) (hT : T ∈ R.powerset) : a ∉ T :=
      fun hat => ha ((Finset.mem_powerset.mp hT) hat)
    by_cases haS : a ∈ S
    · have hfirst : (∑ T ∈ R.powerset,
          if S ⊆ T then (-1 : ℤ) ^ T.card else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        have hST : ¬ S ⊆ T := fun h => hnot T hT (h haS)
        simp [hST]
      rw [hfirst, zero_add]
      have hsecond : (∑ T ∈ R.powerset,
          if S ⊆ insert a T then (-1 : ℤ) ^ (insert a T).card else 0) =
          -(∑ T ∈ R.powerset,
            if S.erase a ⊆ T then (-1 : ℤ) ^ T.card else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro T hT
        have heq : S ⊆ insert a T ↔ S.erase a ⊆ T := by
          constructor
          · intro h x hx
            rcases Finset.mem_insert.mp (h (Finset.mem_of_mem_erase hx)) with hxa | hxT
            · exact False.elim ((Finset.ne_of_mem_erase hx) hxa)
            · exact hxT
          · intro h x hx
            by_cases hxa : x = a
            · simp [hxa]
            · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.mpr ⟨hxa, hx⟩))
        simp only [heq, Finset.card_insert_of_notMem (hnot T hT), pow_succ,
          mul_neg, mul_one]
        split_ifs <;> simp
      rw [hsecond, ih]
      have heq : S.erase a = R ↔ S = insert a R := by
        constructor
        · intro h
          rw [← h, Finset.insert_erase haS]
        · intro h
          simp [h, ha]
      simp only [heq, Finset.card_insert_of_notMem ha, pow_succ, mul_neg, mul_one]
      split_ifs <;> simp
    · have heq (T : Finset α) : S ⊆ insert a T ↔ S ⊆ T := by
        constructor
        · intro h x hx
          rcases Finset.mem_insert.mp (h hx) with hxa | hxT
          · exact False.elim (haS (hxa ▸ hx))
          · exact hxT
        · exact fun h => h.trans (Finset.subset_insert a T)
      have hsecond : (∑ T ∈ R.powerset,
          if S ⊆ insert a T then (-1 : ℤ) ^ (insert a T).card else 0) =
          -(∑ T ∈ R.powerset,
            if S ⊆ T then (-1 : ℤ) ^ T.card else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro T hT
        simp only [heq T, Finset.card_insert_of_notMem (hnot T hT), pow_succ,
          mul_neg, mul_one]
        split_ifs <;> simp
      rw [hsecond, add_neg_cancel]
      have hne : S ≠ insert a R := fun h => haS (h ▸ Finset.mem_insert_self a R)
      simp [hne]

lemma upperCount_add (P : Finset α) (w v : Finset α → ℤ) (S : Finset α) :
    upperCount P (fun T => w T + v T) S = upperCount P w S + upperCount P v S := by
  simp only [upperCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

lemma upperCount_sum (P : Finset α) (F : Finset (Finset α))
    (f : Finset α → Finset α → ℤ) (S : Finset α) :
    upperCount P (fun T => ∑ R ∈ F, f R T) S = ∑ R ∈ F, upperCount P (f R) S := by
  simp only [upperCount]
  calc
    (∑ T ∈ P.powerset, if S ⊆ T then ∑ R ∈ F, f R T else 0) =
        ∑ T ∈ P.powerset, ∑ R ∈ F, if S ⊆ T then f R T else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> simp
    _ = _ := Finset.sum_comm

/-- A Boolean-cube trade changes just its top intersection, with the indicated sign. -/
lemma upperCount_oddCube {P R : Finset α} (hRP : R ⊆ P) (S : Finset α) :
    upperCount P (oddCube R) S = if S = R then -(-1 : ℤ) ^ R.card else 0 := by
  have hreduce : upperCount P (oddCube R) S =
      ∑ T ∈ R.powerset, if S ⊆ T then -(-1 : ℤ) ^ T.card else 0 := by
    unfold upperCount
    calc
      (∑ T ∈ P.powerset, if S ⊆ T then oddCube R T else 0) =
          ∑ T ∈ R.powerset, if S ⊆ T then oddCube R T else 0 := by
        symm
        apply Finset.sum_subset (Finset.powerset_mono.mpr hRP)
        intro T _ hTR
        have hnot : ¬ T ⊆ R := fun h => hTR (Finset.mem_powerset.mpr h)
        simp [oddCube, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [oddCube, Finset.mem_powerset.mp hT]
  rw [hreduce]
  have hneg : (∑ T ∈ R.powerset, if S ⊆ T then -(-1 : ℤ) ^ T.card else 0) =
      -(∑ T ∈ R.powerset, if S ⊆ T then (-1 : ℤ) ^ T.card else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp
  rw [hneg, alternating_upper_sum]
  split_ifs <;> simp

/-- For an odd top set, the changed intersection count increases by exactly one. -/
theorem oddCube_intersections {P R : Finset α} (hRP : R ⊆ P) (hodd : Odd R.card)
    (S : Finset α) :
    upperCount P (oddCube R) S = if S = R then 1 else 0 := by
  rw [upperCount_oddCube hRP]
  simp [hodd.neg_one_pow]

/-- Apply a family of unit Boolean-cube trades to an integer histogram. -/
def traded (w : Finset α → ℤ) (F : Finset (Finset α)) (T : Finset α) : ℤ :=
  w T + ∑ R ∈ F, oddCube R T

/-- The number of trades that consume (if even) or create (if odd) a pattern. -/
def load (F : Finset (Finset α)) (T : Finset α) : ℕ :=
  (F.filter fun R => T ⊆ R).card

lemma traded_eq (w : Finset α → ℤ) (F : Finset (Finset α)) (T : Finset α) :
    traded w F T = w T - (-1 : ℤ) ^ T.card * (load F T : ℤ) := by
  unfold traded oddCube load
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- All positive intersection changes in a family of distinct odd trades are 0 or 1. -/
theorem traded_intersections {P : Finset α} (w : Finset α → ℤ)
    {F : Finset (Finset α)} (hFP : ∀ R ∈ F, R ⊆ P)
    (hodd : ∀ R ∈ F, Odd R.card) (S : Finset α) :
    upperCount P (traded w F) S = upperCount P w S + if S ∈ F then 1 else 0 := by
  unfold traded
  rw [upperCount_add, upperCount_sum]
  congr 1
  calc
    (∑ R ∈ F, upperCount P (oddCube R) S) =
        ∑ R ∈ F, if S = R then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro R hR
      exact oddCube_intersections (hFP R hR) (hodd R hR) S
    _ = _ := by simp

/-- Nonnegativity of the new histogram is exactly an even-pattern capacity condition,
provided the old histogram was nonnegative. -/
theorem traded_nonneg_iff (w : Finset α → ℤ) (F : Finset (Finset α))
    (T : Finset α) (hw : 0 ≤ w T) :
    0 ≤ traded w F T ↔ (Even T.card → (load F T : ℤ) ≤ w T) := by
  rw [traded_eq]
  rcases Nat.even_or_odd T.card with heven | hodd
  · rw [heven.neg_one_pow, one_mul]
    simp only [heven, true_implies]
    omega
  · rw [hodd.neg_one_pow]
    have hneven : ¬ Even T.card := Nat.not_even_iff_odd.mpr hodd
    have hload : (0 : ℤ) ≤ load F T := Nat.cast_nonneg _
    simp only [hneven, false_implies, iff_true]
    omega

/-- Every trade removes one uncovered row. Any nonempty top preserves the total
number of rows; an odd top raises, rather than lowers, its top intersection. -/
lemma traded_empty (w : Finset α → ℤ) (F : Finset (Finset α)) :
    traded w F ∅ = w ∅ - (F.card : ℤ) := by
  simp [traded_eq, load]

/-- A covering-specific, exact integer construction. The displayed capacities are
explicit hypotheses, not assumed to hold for arbitrary primes or lengths. -/
theorem odd_trade_cover {P : Finset α} (w : Finset α → ℤ)
    {F : Finset (Finset α)} (hFP : ∀ R ∈ F, R ⊆ P)
    (hodd : ∀ R ∈ F, Odd R.card)
    (hw : ∀ T ⊆ P, 0 ≤ w T)
    (hcap : ∀ T ⊆ P, Even T.card → (load F T : ℤ) ≤ w T)
    (hempty : w ∅ = (F.card : ℤ)) :
    (∀ T ⊆ P, 0 ≤ traded w F T) ∧
      traded w F ∅ = 0 ∧
      upperCount P (traded w F) ∅ = upperCount P w ∅ ∧
      (∀ S : Finset α,
        upperCount P (traded w F) S = upperCount P w S + if S ∈ F then 1 else 0) := by
  have hnot : (∅ : Finset α) ∉ F := by
    intro h
    have hh := hodd ∅ h
    simp at hh
  refine ⟨?_, ?_, ?_, traded_intersections w hFP hodd⟩
  · intro T hTP
    exact (traded_nonneg_iff w F T (hw T hTP)).mpr (hcap T hTP)
  · rw [traded_empty, hempty, sub_self]
  · rw [traded_intersections w hFP hodd]
    simp [hnot]

/-- Raising only intersections with available integer slack preserves any given
lower and upper bounds (in particular, the exact floor/ceiling bounds). -/
theorem odd_trade_preserves_bounds {P : Finset α} (w : Finset α → ℤ)
    {F : Finset (Finset α)} (hFP : ∀ R ∈ F, R ⊆ P)
    (hodd : ∀ R ∈ F, Odd R.card) (lo hi : Finset α → ℤ)
    (hbounds : ∀ S ⊆ P, lo S ≤ upperCount P w S ∧ upperCount P w S ≤ hi S)
    (hslack : ∀ R ∈ F, upperCount P w R < hi R) :
    ∀ S ⊆ P, lo S ≤ upperCount P (traded w F) S ∧
      upperCount P (traded w F) S ≤ hi S := by
  intro S hSP
  rw [traded_intersections w hFP hodd]
  have hb := hbounds S hSP
  by_cases hSF : S ∈ F
  · rw [if_pos hSF]
    have hs := hslack S hSF
    omega
  · simpa [hSF] using hb

/-- The complete positive-intersection transform determines every histogram
coefficient. In particular, nonnegative real weights cannot simply be treated as
an integer incidence array. -/
theorem upperCount_injective {P : Finset α} {w v : Finset α → ℤ}
    (h : ∀ S ⊆ P, upperCount P w S = upperCount P v S) :
    ∀ T ⊆ P, w T = v T := by
  have main : ∀ n : ℕ, ∀ T ⊆ P, P.card - T.card = n → w T = v T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTP hn
      have hmem : T ∈ P.powerset := Finset.mem_powerset.mpr hTP
      have hrest : (∑ U ∈ P.powerset.erase T, if T ⊆ U then w U else 0) =
          ∑ U ∈ P.powerset.erase T, if T ⊆ U then v U else 0 := by
        apply Finset.sum_congr rfl
        intro U hU
        have hUP : U ⊆ P := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hU)
        have hUT : U ≠ T := Finset.ne_of_mem_erase hU
        by_cases hTU : T ⊆ U
        · simp only [hTU, if_true]
          have hcard : T.card < U.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTU, hUT.symm⟩)
          have hcardP : U.card ≤ P.card := Finset.card_le_card hUP
          have hm : P.card - U.card < n := by omega
          exact ih (P.card - U.card) hm U hUP rfl
        · simp [hTU]
      have heq := h T hTP
      unfold upperCount at heq
      have hw := Finset.sum_erase_add P.powerset
        (fun U => if T ⊆ U then w U else 0) hmem
      have hv := Finset.sum_erase_add P.powerset
        (fun U => if T ⊆ U then v U else 0) hmem
      simp only [Finset.Subset.refl, if_true] at hw hv
      omega
  intro T hTP
  exact main (P.card - T.card) T hTP rfl

/-- Coefficients of the polynomial `∏ i ∈ R, (zᵢ - 1)`. -/
def basisCube (R T : Finset α) : ℤ :=
  -(-1 : ℤ) ^ R.card * oddCube R T

lemma upperCount_mul (P : Finset α) (c : ℤ) (w : Finset α → ℤ) (S : Finset α) :
    upperCount P (fun T => c * w T) S = c * upperCount P w S := by
  unfold upperCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

/-- Boolean Möbius basis: each basis polynomial has exactly one nonzero
intersection coefficient, equal to one. -/
lemma upperCount_basisCube {P R : Finset α} (hRP : R ⊆ P) (S : Finset α) :
    upperCount P (basisCube R) S = if S = R then 1 else 0 := by
  unfold basisCube
  rw [upperCount_mul, upperCount_oddCube hRP]
  rcases neg_one_pow_eq_or ℤ R.card with hsign | hsign <;>
    split_ifs <;> simp [hsign]

/-- Reconstruct integer pattern multiplicities from integer intersection counts. -/
def reconstruct (P : Finset α) (counts : Finset α → ℤ) (T : Finset α) : ℤ :=
  ∑ R ∈ P.powerset, counts R * basisCube R T

lemma reconstruct_intersections (P : Finset α) (counts : Finset α → ℤ)
    {S : Finset α} (hSP : S ⊆ P) :
    upperCount P (reconstruct P counts) S = counts S := by
  unfold reconstruct
  rw [upperCount_sum]
  calc
    (∑ R ∈ P.powerset, upperCount P (fun T => counts R * basisCube R T) S) =
        ∑ R ∈ P.powerset, if S = R then counts R else 0 := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [upperCount_mul, upperCount_basisCube (Finset.mem_powerset.mp hR)]
      split_ifs <;> simp
    _ = counts S := by simp [Finset.mem_powerset.mpr hSP]

/-- Exact Boolean Möbius inversion, including the empty-pattern coefficient
that distinguishes full covering from positive sieve density. -/
theorem histogram_mobius_inversion (P : Finset α) (w : Finset α → ℤ)
    {T : Finset α} (hTP : T ⊆ P) :
    reconstruct P (upperCount P w) T = w T := by
  apply upperCount_injective (P := P) (w := reconstruct P (upperCount P w)) (v := w)
    (fun S hSP => reconstruct_intersections P (upperCount P w) hSP) T hTP

/-- Thus an integer vector of intersection counts is a covered, nonnegative
histogram exactly when its reconstructed coefficients are nonnegative and its
empty-pattern coefficient is zero. This keeps integrality, not just a real LP. -/
theorem covered_histogram_iff (P : Finset α) (counts : Finset α → ℤ) :
    (∃ w : Finset α → ℤ,
      (∀ T ⊆ P, 0 ≤ w T) ∧ w ∅ = 0 ∧
        (∀ S ⊆ P, upperCount P w S = counts S)) ↔
    (∀ T ⊆ P, 0 ≤ reconstruct P counts T) ∧ reconstruct P counts ∅ = 0 := by
  constructor
  · rintro ⟨w, hw, hempty, hcounts⟩
    have heq : ∀ T ⊆ P, reconstruct P counts T = w T := by
      apply upperCount_injective
      intro S hSP
      rw [reconstruct_intersections P counts hSP, hcounts S hSP]
    exact ⟨fun T hTP => heq T hTP ▸ hw T hTP,
      (heq ∅ (Finset.empty_subset P)).trans hempty⟩
  · rintro ⟨hpos, hempty⟩
    exact ⟨reconstruct P counts, hpos, hempty,
      fun S hSP => reconstruct_intersections P counts hSP⟩

/-- An incidence array is represented by the set of prime labels in each row. -/
def rowCount {L : ℕ} (rows : Fin L → Finset ℕ) (S : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun i => S ⊆ rows i).card

/-- Product of the labels of an intersection. For a set of primes this is its
squarefree modulus. -/
def modulus (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- Exact floor/ceiling intersection constraints, not merely an asymptotic error. -/
def RoundedIntersections (L : ℕ) (P : Finset ℕ) (rows : Fin L → Finset ℕ) : Prop :=
  ∀ S ∈ P.powerset,
    L / modulus S ≤ rowCount rows S ∧
      rowCount rows S ≤ (L + modulus S - 1) / modulus S

lemma two_le_rowCount {L : ℕ} (rows : Fin L → Finset ℕ) {i j : Fin L}
    (hij : i ≠ j) {S : Finset ℕ} (hi : S ⊆ rows i) (hj : S ⊆ rows j) :
    2 ≤ rowCount rows S := by
  have hsub : ({i, j} : Finset (Fin L)) ⊆ Finset.univ.filter (fun t => S ⊆ rows t) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [hi, hj]
  simpa [rowCount, Finset.card_pair hij] using Finset.card_le_card hsub

/-- The numerical common-product constraint is already implied by the exact
intersection counts. This does NOT assert divisibility by a position difference. -/
theorem common_product_lt_length {L : ℕ} {P : Finset ℕ}
    (rows : Fin L → Finset ℕ) (hrows : ∀ i, rows i ⊆ P)
    (hround : RoundedIntersections L P rows) {i j : Fin L} (hij : i ≠ j) :
    modulus (rows i ∩ rows j) < L := by
  by_contra h
  have hLd : L ≤ modulus (rows i ∩ rows j) := Nat.le_of_not_gt h
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hd : 0 < modulus (rows i ∩ rows j) := hL.trans_le hLd
  have hsmall : (L + modulus (rows i ∩ rows j) - 1) / modulus (rows i ∩ rows j) < 2 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    omega
  have hSP : rows i ∩ rows j ⊆ P := Finset.inter_subset_left.trans (hrows i)
  have hu := (hround (rows i ∩ rows j) (Finset.mem_powerset.mpr hSP)).2
  have hlo := two_le_rowCount rows hij Finset.inter_subset_left Finset.inter_subset_right
  omega

/-- If all occurrences of each label have pairwise differences divisible by that
label, there is one residue for that label containing every occurrence. -/
theorem column_residues_iff {L : ℕ} (rows : Fin L → Finset ℕ) :
    (∀ (p : ℕ) (i j : Fin L), p ∈ rows i → p ∈ rows j →
      (p : ℤ) ∣ (i.val : ℤ) - (j.val : ℤ)) ↔
    (∃ a : ℕ → ℤ, ∀ (p : ℕ) (i : Fin L), p ∈ rows i →
      (p : ℤ) ∣ (i.val : ℤ) - a p) := by
  classical
  constructor
  · intro h
    have hchoice : ∀ p : ℕ, ∃ a : ℤ, ∀ i : Fin L, p ∈ rows i →
        (p : ℤ) ∣ (i.val : ℤ) - a := by
      intro p
      by_cases hp : ∃ j : Fin L, p ∈ rows j
      · obtain ⟨j, hj⟩ := hp
        exact ⟨j.val, fun i hi => h p i j hi hj⟩
      · exact ⟨0, fun i hi => False.elim (hp ⟨i, hi⟩)⟩
    choose a ha using hchoice
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩ p i j hi hj
    convert dvd_sub (ha p i hi) (ha p j hj) using 1
    ring

/-- Full pair-difference divisibility plus covering already gives a genuine
residue-class interval cover; no density or intersection-count assumptions are needed. -/
theorem residue_cover_of_product_differences {L : ℕ} {P : Finset ℕ}
    (rows : Fin L → Finset ℕ) (hrows : ∀ i, rows i ⊆ P)
    (hcover : ∀ i, (rows i).Nonempty)
    (hdiff : ∀ i j : Fin L, (modulus (rows i ∩ rows j) : ℤ) ∣
      (i.val : ℤ) - (j.val : ℤ)) :
    ∃ a : ℕ → ℤ, ∀ i : Fin L, ∃ p ∈ P, (p : ℤ) ∣ (i.val : ℤ) - a p := by
  have hpairs : ∀ (p : ℕ) (i j : Fin L), p ∈ rows i → p ∈ rows j →
      (p : ℤ) ∣ (i.val : ℤ) - (j.val : ℤ) := by
    intro p i j hi hj
    have hdiv : p ∣ modulus (rows i ∩ rows j) :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_inter.mpr ⟨hi, hj⟩)
    exact (Int.natCast_dvd_natCast.mpr hdiv).trans (hdiff i j)
  obtain ⟨a, ha⟩ := (column_residues_iff rows).mp hpairs
  refine ⟨a, ?_⟩
  intro i
  obtain ⟨p, hp⟩ := hcover i
  exact ⟨p, hrows i hp, ha p i hp⟩

end IntegerSieve

#print axioms IntegerSieve.oddCube_intersections
#print axioms IntegerSieve.odd_trade_cover
#print axioms IntegerSieve.odd_trade_preserves_bounds
#print axioms IntegerSieve.histogram_mobius_inversion
#print axioms IntegerSieve.covered_histogram_iff
#print axioms IntegerSieve.common_product_lt_length
#print axioms IntegerSieve.residue_cover_of_product_differences
