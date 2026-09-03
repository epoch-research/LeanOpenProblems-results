import FormalConjecturesUtil

/-! A recursive first-hit sieve with arbitrary rigorous intersection bounds. -/
namespace Erdos970.RecursiveSieve

/-- The indicator that all coordinates in `T` are hit. -/
def hit (T : Finset ℕ) (ω : ℕ → Bool) : ℝ :=
  if ∀ i ∈ T, ω i = true then 1 else 0

/-- The indicator that the first `k` coordinates are all avoided. -/
def avoid (k : ℕ) (ω : ℕ → Bool) : ℝ :=
  if ∀ i < k, ω i = false then 1 else 0

lemma hit_insert (T : Finset ℕ) (i : ℕ) (ω : ℕ → Bool) :
    hit (insert i T) ω = hit T ω * (if ω i then 1 else 0) := by
  simp only [hit, Finset.forall_mem_insert]
  cases hi : ω i <;> simp [hi]

lemma hit_nonneg (T : Finset ℕ) (ω : ℕ → Bool) : 0 ≤ hit T ω := by
  unfold hit
  split_ifs <;> norm_num

lemma avoid_nonneg (k : ℕ) (ω : ℕ → Bool) : 0 ≤ avoid k ω := by
  unfold avoid
  split_ifs <;> norm_num

lemma avoid_succ (k : ℕ) (ω : ℕ → Bool) :
    avoid (k+1) ω = avoid k ω * (if ω k then 0 else 1) := by
  have he : (∀ i < k+1, ω i = false) ↔ (∀ i < k, ω i = false) ∧ ω k = false := by
    constructor
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩
    · rintro ⟨h, hk⟩ i hi
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact h i hi
      · exact hk
  simp only [avoid, he]
  cases hi : ω k <;> simp [hi]

/-- Exactly one summand corresponds to the first hit, unless there are no hits. -/
theorem first_hit_identity (k : ℕ) (ω : ℕ → Bool) :
    avoid k ω = 1 - ∑ i ∈ Finset.range k, (if ω i then (1 : ℝ) else 0) * avoid i ω := by
  induction k with
  | zero => simp [avoid]
  | succ k ih =>
    rw [avoid_succ, Finset.sum_range_succ, ← sub_sub, ← ih]
    cases ω k <;> simp

/-- Multiplication by an intersection indicator preserves the first-hit decomposition. -/
theorem intersection_first_hit (T : Finset ℕ) (k : ℕ) (ω : ℕ → Bool) :
    hit T ω * avoid k ω = hit T ω -
      ∑ i ∈ Finset.range k, hit (insert i T) ω * avoid i ω := by
  rw [first_hit_identity, mul_sub, mul_one, Finset.mul_sum]
  simp_rw [hit_insert, mul_assoc]

section Weighted
variable {α : Type*} (A : Finset α) (w : α → ℝ) (ω : α → ℕ → Bool)

/-- A weighted intersection count. -/
def moment (T : Finset ℕ) : ℝ := ∑ a ∈ A, w a * hit T (ω a)

/-- A weighted intersection count with a prefix of forbidden coordinates. -/
def sifted (T : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ a ∈ A, w a * (hit T (ω a) * avoid k (ω a))

lemma sifted_nonneg (hw : ∀ a ∈ A, 0 ≤ w a) (T : Finset ℕ) (k : ℕ) :
    0 ≤ sifted A w ω T k := by
  exact Finset.sum_nonneg (fun a ha =>
    mul_nonneg (hw a ha) (mul_nonneg (hit_nonneg _ _) (avoid_nonneg _ _)))

theorem sifted_first_hit (T : Finset ℕ) (k : ℕ) :
    sifted A w ω T k = moment A w ω T -
      ∑ i : Fin k, sifted A w ω (insert i.val T) i.val := by
  unfold sifted moment
  calc
    _ = ∑ a ∈ A, w a * (hit T (ω a) -
        ∑ i ∈ Finset.range k, hit (insert i T) (ω a) * avoid i (ω a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [intersection_first_hit]
    _ = _ := by
      simp_rw [mul_sub, Finset.mul_sum]
      rw [Finset.sum_sub_distrib, Finset.sum_comm]
      congr 1
      exact (Fin.sum_univ_eq_sum_range _ _).symm

end Weighted

/-- A pair of numerical bounds. A lower branch may be discarded whenever convenient;
`keep` affects efficiency and strength, but never correctness. -/
noncomputable def envelope (lo hi : Finset ℕ → ℝ) (keep : ℕ → Finset ℕ → Bool)
    (k : ℕ) (T : Finset ℕ) : ℝ × ℝ :=
  (if keep k T then max 0 (lo T - ∑ i : Fin k,
      (envelope lo hi keep i.val (insert i.val T)).2) else 0,
    hi T - ∑ i : Fin k, (envelope lo hi keep i.val (insert i.val T)).1)
termination_by k

theorem envelope_sound {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (hw : ∀ a ∈ A, 0 ≤ w a)
    (lo hi : Finset ℕ → ℝ) (keep : ℕ → Finset ℕ → Bool)
    (hlo : ∀ T, lo T ≤ moment A w ω T)
    (hhi : ∀ T, moment A w ω T ≤ hi T)
    (k : ℕ) (T : Finset ℕ) :
    (envelope lo hi keep k T).1 ≤ sifted A w ω T k ∧
      sifted A w ω T k ≤ (envelope lo hi keep k T).2 := by
  induction k using Nat.strong_induction_on generalizing T with
  | h k ih =>
    have hsumlo : (∑ i : Fin k, (envelope lo hi keep i.val (insert i.val T)).1) ≤
        ∑ i : Fin k, sifted A w ω (insert i.val T) i.val :=
      Finset.sum_le_sum (fun i _ => (ih i.val i.isLt (insert i.val T)).1)
    have hsumhi : (∑ i : Fin k, sifted A w ω (insert i.val T) i.val) ≤
        ∑ i : Fin k, (envelope lo hi keep i.val (insert i.val T)).2 :=
      Finset.sum_le_sum (fun i _ => (ih i.val i.isLt (insert i.val T)).2)
    have he := sifted_first_hit A w ω T k
    have hn := sifted_nonneg A w ω hw T k
    rw [envelope]
    dsimp only
    constructor
    · split_ifs
      · apply max_le hn
        linarith [hlo T]
      · exact hn
    · linarith [hhi T]

/-- The same positivity criterion holds for arbitrary nonnegative finite weights. -/
theorem weighted_survivor_of_positive_envelope {α : Type*} (A : Finset α)
    (w : α → ℝ) (ω : α → ℕ → Bool) (hw : ∀ a ∈ A, 0 ≤ w a)
    (lo hi : Finset ℕ → ℝ) (keep : ℕ → Finset ℕ → Bool)
    (hlo : ∀ T, lo T ≤ moment A w ω T)
    (hhi : ∀ T, moment A w ω T ≤ hi T)
    (k : ℕ) (hpos : 0 < (envelope lo hi keep k ∅).1) :
    ∃ a ∈ A, ∀ i < k, ω a i = false := by
  have hs : 0 < sifted A w ω ∅ k := hpos.trans_le
    (envelope_sound A w ω hw lo hi keep hlo hhi k ∅).1
  by_contra h
  push_neg at h
  have hz : sifted A w ω ∅ k = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    obtain ⟨i, hi, hω⟩ := h a ha
    have hbad : ¬∀ i < k, ω a i = false := fun hh => hω (hh i hi)
    simp [avoid, hbad]
  rw [hz] at hs
  exact lt_irrefl _ hs

/-- A positive computed lower bound forces an actual surviving position. -/
theorem survivor_of_positive_envelope (m k : ℕ) (ω : ℕ → ℕ → Bool)
    (lo hi : Finset ℕ → ℝ) (keep : ℕ → Finset ℕ → Bool)
    (hlo : ∀ T, lo T ≤ moment (Finset.range m) (fun _ => 1) ω T)
    (hhi : ∀ T, moment (Finset.range m) (fun _ => 1) ω T ≤ hi T)
    (hpos : 0 < (envelope lo hi keep k ∅).1) :
    ∃ a < m, ∀ i < k, ω a i = false := by
  have hh := (envelope_sound (Finset.range m) (fun _ => 1) ω
    (by intros; norm_num) lo hi keep hlo hhi k ∅).1
  have hs : 0 < sifted (Finset.range m) (fun _ => 1) ω ∅ k := hpos.trans_le hh
  by_contra h
  push_neg at h
  have hz : sifted (Finset.range m) (fun _ => 1) ω ∅ k = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    obtain ⟨i, hi, hω⟩ := h a (Finset.mem_range.mp ha)
    have hbad : ¬∀ i < k, ω a i = false := fun hh => hω (hh i hi)
    simp [avoid, hbad]
  rw [hz] at hs
  exact lt_irrefl _ hs

#print axioms envelope_sound
#print axioms survivor_of_positive_envelope
end Erdos970.RecursiveSieve
