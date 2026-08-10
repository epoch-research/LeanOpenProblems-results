import FormalConjectures.Util.ProblemImports

open Nat

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

namespace A264025aux

/-! ### A kernel-reducible integer square root (binary search with structural fuel) -/

def sqrtB : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, lo, _, _ => lo
  | fuel + 1, lo, hi, n =>
    if lo = hi then lo
    else
      let mid := (lo + hi + 1) / 2
      if mid * mid ≤ n then sqrtB fuel mid hi n else sqrtB fuel lo (mid - 1) n

lemma sqrtB_spec : ∀ (fuel lo hi n : ℕ), lo ≤ hi → hi - lo ≤ fuel →
    lo * lo ≤ n → n < (hi + 1) * (hi + 1) →
    sqrtB fuel lo hi n * sqrtB fuel lo hi n ≤ n ∧
      n < (sqrtB fuel lo hi n + 1) * (sqrtB fuel lo hi n + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi n h1 h2 h3 h4
    have : lo = hi := by omega
    subst this
    exact ⟨h3, h4⟩
  | succ fuel ih =>
    intro lo hi n h1 h2 h3 h4
    rw [sqrtB]
    by_cases hlh : lo = hi
    · subst hlh
      simp only [if_pos]
      exact ⟨h3, h4⟩
    · simp only [if_neg hlh]
      have hlt : lo < hi := by omega
      have hmid1 : lo + 1 ≤ (lo + hi + 1) / 2 := by omega
      have hmid2 : (lo + hi + 1) / 2 ≤ hi := by omega
      by_cases hm : ((lo + hi + 1) / 2) * ((lo + hi + 1) / 2) ≤ n
      · simp only [if_pos hm]
        exact ih _ _ _ hmid2 (by omega) hm h4
      · simp only [if_neg hm]
        refine ih _ _ _ (by omega) (by omega) h3 ?_
        have h5 : (lo + hi + 1) / 2 - 1 + 1 = (lo + hi + 1) / 2 := by omega
        rw [h5]
        omega

def msqrt (n : ℕ) : ℕ := sqrtB n 0 n n

lemma msqrt_spec (n : ℕ) : msqrt n * msqrt n ≤ n ∧ n < (msqrt n + 1) * (msqrt n + 1) := by
  refine sqrtB_spec n 0 n n (Nat.zero_le n) (by omega) (by omega) ?_
  nlinarith

lemma le_msqrt {x n : ℕ} (h : x * x ≤ n) : x ≤ msqrt n := by
  obtain ⟨h1, h2⟩ := msqrt_spec n
  by_contra hc
  push_neg at hc
  have : (msqrt n + 1) * (msqrt n + 1) ≤ x * x := Nat.mul_le_mul hc hc
  omega

lemma msqrt_unique {x n : ℕ} (h : x * x = n) : msqrt n = x := by
  obtain ⟨h1, h2⟩ := msqrt_spec n
  have hx1 : msqrt n ≤ x := by
    by_contra hc
    push_neg at hc
    have : (x + 1) * (x + 1) ≤ msqrt n * msqrt n := Nat.mul_le_mul hc hc
    nlinarith
  have hx2 : x ≤ msqrt n := le_msqrt (le_of_eq h)
  omega

/-! ### Counting `Finset`s -/

/-- Triple-set formulation as a concrete `Finset`. -/
def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (msqrt n + 1) ×ˢ Finset.range (msqrt n + 1) ×ˢ
      Finset.range (msqrt (2 * n) + 1)).filter
    fun p =>
      p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
      (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1))

lemma two_dvd_mul_succ (z : ℕ) : 2 ∣ z * (z + 1) :=
  (Nat.even_mul_succ_self z).two_dvd

lemma tri_double (z : ℕ) : z * (z + 1) / 2 * 2 = z * (z + 1) :=
  Nat.div_mul_cancel (two_dvd_mul_succ z)

lemma tri_le {z n : ℕ} (h : z * (z + 1) / 2 ≤ n) : z ≤ msqrt (2 * n) := by
  have h1 := tri_double z
  exact le_msqrt (by nlinarith)

lemma hex_le {y n : ℕ} (h : y * (2 * y + 1) ≤ n) : y ≤ msqrt n :=
  le_msqrt (by nlinarith)

lemma sq_le {x n : ℕ} (h : x ^ 2 ≤ n) : x ≤ msqrt n :=
  le_msqrt (by nlinarith [pow_two x])

lemma mem_triples {n : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ triples n ↔
      p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
      (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1)) := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    obtain ⟨heq, -⟩ := h
    refine Finset.mem_product.2 ⟨?_, Finset.mem_product.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (sq_le (by omega)))
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (hex_le (by omega)))
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (tri_le (by omega)))

lemma A264025_eq_triples (n : ℕ) : A264025 n = (triples n).card := by
  rw [A264025, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun p => by rw [mem_triples]

/-- The pair-counting `Finset`: `x` is uniquely determined by `(y, z)`. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (msqrt n + 1) ×ˢ Finset.range (msqrt (2 * n) + 1)).filter
    fun q =>
      (Nat.Prime q.2 ∨ Nat.Prime (q.2 + 1)) ∧
      q.1 * (2 * q.1 + 1) + q.2 * (q.2 + 1) / 2 ≤ n ∧
      msqrt (n - q.1 * (2 * q.1 + 1) - q.2 * (q.2 + 1) / 2) *
          msqrt (n - q.1 * (2 * q.1 + 1) - q.2 * (q.2 + 1) / 2)
        = n - q.1 * (2 * q.1 + 1) - q.2 * (q.2 + 1) / 2

lemma mem_pairs {n : ℕ} {q : ℕ × ℕ} :
    q ∈ pairs n ↔
      (Nat.Prime q.2 ∨ Nat.Prime (q.2 + 1)) ∧
      q.1 * (2 * q.1 + 1) + q.2 * (q.2 + 1) / 2 ≤ n ∧
      msqrt (n - q.1 * (2 * q.1 + 1) - q.2 * (q.2 + 1) / 2) *
          msqrt (n - q.1 * (2 * q.1 + 1) - q.2 * (q.2 + 1) / 2)
        = n - q.1 * (2 * q.1 + 1) - q.2 * (q.2 + 1) / 2 := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    obtain ⟨-, hle, -⟩ := h
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (hex_le (by omega)))
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (tri_le (by omega)))

def cnt (n : ℕ) : ℕ := (pairs n).card

lemma triples_card_eq_pairs_card (n : ℕ) : (triples n).card = (pairs n).card := by
  refine Finset.card_bij (fun p _ => (p.2.1, p.2.2)) ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    dsimp only
    rw [mem_triples] at hp
    obtain ⟨heq, hg⟩ := hp
    simp only at heq hg
    rw [mem_pairs]
    dsimp only
    refine ⟨hg, by omega, ?_⟩
    have hres : n - y * (2 * y + 1) - z * (z + 1) / 2 = x * x := by
      have := pow_two x
      omega
    rw [hres, msqrt_unique rfl]
  · rintro ⟨x1, y1, z1⟩ h1 ⟨x2, y2, z2⟩ h2 heq
    rw [mem_triples] at h1 h2
    simp only [Prod.mk.injEq] at heq ⊢
    obtain ⟨e1, -⟩ := h1
    obtain ⟨e2, -⟩ := h2
    simp only at e1 e2
    obtain ⟨hy, hz⟩ := heq
    subst hy; subst hz
    have hx : x1 * x1 = x2 * x2 := by
      have p1 := pow_two x1
      have p2 := pow_two x2
      omega
    have hx' : x1 = x2 := by
      have m1 : msqrt (x1 * x1) = x1 := msqrt_unique rfl
      have m2 : msqrt (x2 * x2) = x2 := msqrt_unique rfl
      rw [hx] at m1
      omega
    exact ⟨hx', rfl, rfl⟩
  · rintro ⟨y, z⟩ hq
    rw [mem_pairs] at hq
    obtain ⟨hg, hle, hsq⟩ := hq
    dsimp only at hg hle hsq
    refine ⟨(msqrt (n - y * (2 * y + 1) - z * (z + 1) / 2), y, z), ?_, rfl⟩
    rw [mem_triples]
    dsimp only
    refine ⟨?_, hg⟩
    have := pow_two (msqrt (n - y * (2 * y + 1) - z * (z + 1) / 2))
    omega

/-- Master reduction: `A264025 n` is computed by the executable pair count. -/
lemma A264025_eq_cnt (n : ℕ) : A264025 n = cnt n := by
  rw [A264025_eq_triples, triples_card_eq_pairs_card, cnt]

end A264025aux

namespace A264025aux

/-! Boolean witness search with early exit -/

def goodZ (z : ℕ) : Bool := decide (Nat.Prime z ∨ Nat.Prime (z + 1))

def hitB (n y z : ℕ) : Bool :=
  decide (y * (2 * y + 1) + z * (z + 1) / 2 ≤ n) &&
  decide (msqrt (n - y * (2 * y + 1) - z * (z + 1) / 2) *
      msqrt (n - y * (2 * y + 1) - z * (z + 1) / 2)
    = n - y * (2 * y + 1) - z * (z + 1) / 2)

lemma hit_mem {n y z : ℕ} (hg : goodZ z = true) (h : hitB n y z = true) :
    (y, z) ∈ pairs n := by
  rw [goodZ, decide_eq_true_eq] at hg
  rw [hitB, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rw [mem_pairs]
  dsimp only
  exact ⟨hg, h.1, h.2⟩

def posB (n : ℕ) : Bool :=
  (List.range (msqrt (2 * n) + 1)).any fun z =>
    goodZ z && (List.range (msqrt n + 1)).any fun y => hitB n y z

lemma posB_sound {n : ℕ} (h : posB n = true) : 0 < cnt n := by
  rw [posB, List.any_eq_true] at h
  obtain ⟨z, -, h⟩ := h
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨hg, y, -, h⟩ := h
  exact Finset.card_pos.2 ⟨(y, z), hit_mem hg h⟩

def find2B (n : ℕ) : Bool :=
  (List.range (msqrt (2 * n) + 1)).any fun z =>
    goodZ z && (List.range (msqrt n + 1)).any fun y =>
      hitB n y z &&
      ((List.range (msqrt (2 * n) + 1)).any fun z' =>
        goodZ z' && (List.range (msqrt n + 1)).any fun y' =>
          (!(decide (y = y') && decide (z = z'))) && hitB n y' z')

lemma find2B_sound {n : ℕ} (h : find2B n = true) : 2 ≤ cnt n := by
  rw [find2B, List.any_eq_true] at h
  obtain ⟨z, -, h⟩ := h
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨hg, y, -, h⟩ := h
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨h1, z', -, h⟩ := h
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨hg', y', -, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨hne, h2⟩ := h
  have m1 := hit_mem hg h1
  have m2 := hit_mem hg' h2
  have hne' : (y, z) ≠ (y', z') := by
    intro hc
    rw [Prod.mk.injEq] at hc
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hne
    rcases hne with h' | h' <;> [exact h' hc.1; exact h' hc.2]
  exact Finset.one_lt_card.2 ⟨(y, z), m1, (y', z'), m2, hne'⟩

/-- Membership test for the exceptional list. -/
def inL (n : ℕ) : Bool :=
  n == 1 || n == 2 || n == 3 || n == 8 || n == 9 || n == 23 || n == 30 ||
  n == 44 || n == 48 || n == 198 || n == 219 || n == 1344

/-- Combined check for one `n`. -/
def checkB (n : ℕ) : Bool := n == 0 || inL n || find2B n

def sweep (a b : ℕ) : Bool := (List.range' a b).all checkB

lemma sweep_sound {a b : ℕ} (h : sweep a b = true) {n : ℕ} (h1 : a ≤ n)
    (h2 : n < a + b) : checkB n = true := by
  rw [sweep, List.all_eq_true] at h
  exact h n (List.mem_range'_1.2 ⟨h1, h2⟩)

end A264025aux


namespace A264025aux

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

lemma cnt_0 : cnt 0 = 0 := by decide +kernel
lemma cnt_5 : cnt 5 = 2 := by decide +kernel
lemma cnt_1 : cnt 1 = 1 := by decide +kernel
lemma cnt_2 : cnt 2 = 1 := by decide +kernel
lemma cnt_3 : cnt 3 = 1 := by decide +kernel
lemma cnt_8 : cnt 8 = 1 := by decide +kernel
lemma cnt_9 : cnt 9 = 1 := by decide +kernel
lemma cnt_23 : cnt 23 = 1 := by decide +kernel
lemma cnt_30 : cnt 30 = 1 := by decide +kernel
lemma cnt_44 : cnt 44 = 1 := by decide +kernel
lemma cnt_48 : cnt 48 = 1 := by decide +kernel
lemma cnt_198 : cnt 198 = 1 := by decide +kernel
lemma cnt_219 : cnt 219 = 1 := by decide +kernel
lemma cnt_1344 : cnt 1344 = 1 := by decide +kernel
lemma sweep_0 : sweep 0 50 = true := by decide +kernel
lemma sweep_50 : sweep 50 50 = true := by decide +kernel
lemma sweep_100 : sweep 100 50 = true := by decide +kernel
lemma sweep_150 : sweep 150 50 = true := by decide +kernel
lemma sweep_200 : sweep 200 50 = true := by decide +kernel
lemma sweep_250 : sweep 250 50 = true := by decide +kernel
lemma sweep_300 : sweep 300 50 = true := by decide +kernel
lemma sweep_350 : sweep 350 50 = true := by decide +kernel
lemma sweep_400 : sweep 400 50 = true := by decide +kernel
lemma sweep_450 : sweep 450 50 = true := by decide +kernel
lemma sweep_500 : sweep 500 50 = true := by decide +kernel
lemma sweep_550 : sweep 550 50 = true := by decide +kernel
lemma sweep_600 : sweep 600 50 = true := by decide +kernel
lemma sweep_650 : sweep 650 50 = true := by decide +kernel
lemma sweep_700 : sweep 700 50 = true := by decide +kernel
lemma sweep_750 : sweep 750 50 = true := by decide +kernel
lemma sweep_800 : sweep 800 50 = true := by decide +kernel
lemma sweep_850 : sweep 850 50 = true := by decide +kernel
lemma sweep_900 : sweep 900 50 = true := by decide +kernel
lemma sweep_950 : sweep 950 50 = true := by decide +kernel
lemma sweep_1000 : sweep 1000 50 = true := by decide +kernel
lemma sweep_1050 : sweep 1050 50 = true := by decide +kernel
lemma sweep_1100 : sweep 1100 50 = true := by decide +kernel
lemma sweep_1150 : sweep 1150 50 = true := by decide +kernel
lemma sweep_1200 : sweep 1200 50 = true := by decide +kernel
lemma sweep_1250 : sweep 1250 50 = true := by decide +kernel
lemma sweep_1300 : sweep 1300 50 = true := by decide +kernel
lemma sweep_1350 : sweep 1350 50 = true := by decide +kernel

def L : Finset ℕ := {1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344}

lemma inL_iff (n : ℕ) : inL n = true ↔ n ∈ L := by
  simp only [inL, L, Finset.mem_insert, Finset.mem_singleton,
    Bool.or_eq_true, beq_iff_eq]
  tauto

lemma checkB_below {n : ℕ} (h : n < 1400) : checkB n = true := by
  rcases Nat.lt_or_ge n 50 with h0 | h0
  · exact sweep_sound sweep_0 (by omega) (by omega)
  rcases Nat.lt_or_ge n 100 with h1 | h1
  · exact sweep_sound sweep_50 (by omega) (by omega)
  rcases Nat.lt_or_ge n 150 with h2 | h2
  · exact sweep_sound sweep_100 (by omega) (by omega)
  rcases Nat.lt_or_ge n 200 with h3 | h3
  · exact sweep_sound sweep_150 (by omega) (by omega)
  rcases Nat.lt_or_ge n 250 with h4 | h4
  · exact sweep_sound sweep_200 (by omega) (by omega)
  rcases Nat.lt_or_ge n 300 with h5 | h5
  · exact sweep_sound sweep_250 (by omega) (by omega)
  rcases Nat.lt_or_ge n 350 with h6 | h6
  · exact sweep_sound sweep_300 (by omega) (by omega)
  rcases Nat.lt_or_ge n 400 with h7 | h7
  · exact sweep_sound sweep_350 (by omega) (by omega)
  rcases Nat.lt_or_ge n 450 with h8 | h8
  · exact sweep_sound sweep_400 (by omega) (by omega)
  rcases Nat.lt_or_ge n 500 with h9 | h9
  · exact sweep_sound sweep_450 (by omega) (by omega)
  rcases Nat.lt_or_ge n 550 with h10 | h10
  · exact sweep_sound sweep_500 (by omega) (by omega)
  rcases Nat.lt_or_ge n 600 with h11 | h11
  · exact sweep_sound sweep_550 (by omega) (by omega)
  rcases Nat.lt_or_ge n 650 with h12 | h12
  · exact sweep_sound sweep_600 (by omega) (by omega)
  rcases Nat.lt_or_ge n 700 with h13 | h13
  · exact sweep_sound sweep_650 (by omega) (by omega)
  rcases Nat.lt_or_ge n 750 with h14 | h14
  · exact sweep_sound sweep_700 (by omega) (by omega)
  rcases Nat.lt_or_ge n 800 with h15 | h15
  · exact sweep_sound sweep_750 (by omega) (by omega)
  rcases Nat.lt_or_ge n 850 with h16 | h16
  · exact sweep_sound sweep_800 (by omega) (by omega)
  rcases Nat.lt_or_ge n 900 with h17 | h17
  · exact sweep_sound sweep_850 (by omega) (by omega)
  rcases Nat.lt_or_ge n 950 with h18 | h18
  · exact sweep_sound sweep_900 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1000 with h19 | h19
  · exact sweep_sound sweep_950 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1050 with h20 | h20
  · exact sweep_sound sweep_1000 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1100 with h21 | h21
  · exact sweep_sound sweep_1050 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1150 with h22 | h22
  · exact sweep_sound sweep_1100 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1200 with h23 | h23
  · exact sweep_sound sweep_1150 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1250 with h24 | h24
  · exact sweep_sound sweep_1200 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1300 with h25 | h25
  · exact sweep_sound sweep_1250 (by omega) (by omega)
  rcases Nat.lt_or_ge n 1350 with h26 | h26
  · exact sweep_sound sweep_1300 (by omega) (by omega)
  exact sweep_sound sweep_1350 (by omega) (by omega)

/-- Everything below 1400 is fully machine-checked. -/
theorem A264025_low (n : ℕ) (hn : n < 1400) :
    (0 < n → 0 < A264025 n) ∧ (A264025 n = 1 ↔ n ∈ L) := by
  have hc0 := checkB_below hn
  have hc : (n == 0) = true ∨ (inL n) = true ∨ find2B n = true := by
    rw [checkB] at hc0
    simp only [Bool.or_eq_true] at hc0
    tauto
  by_cases hL : n ∈ L
  · have h1 : A264025 n = 1 := by
      have hL' := hL
      simp only [L, Finset.mem_insert, Finset.mem_singleton] at hL'
      rcases hL' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · rw [A264025_eq_cnt]; exact cnt_1
      · rw [A264025_eq_cnt]; exact cnt_2
      · rw [A264025_eq_cnt]; exact cnt_3
      · rw [A264025_eq_cnt]; exact cnt_8
      · rw [A264025_eq_cnt]; exact cnt_9
      · rw [A264025_eq_cnt]; exact cnt_23
      · rw [A264025_eq_cnt]; exact cnt_30
      · rw [A264025_eq_cnt]; exact cnt_44
      · rw [A264025_eq_cnt]; exact cnt_48
      · rw [A264025_eq_cnt]; exact cnt_198
      · rw [A264025_eq_cnt]; exact cnt_219
      · rw [A264025_eq_cnt]; exact cnt_1344
    exact ⟨fun _ => by omega, ⟨fun _ => hL, fun _ => h1⟩⟩
  · rcases hc with hc | hc | hc
    · have hn0 : n = 0 := by simpa using hc
      subst hn0
      refine ⟨fun h => absurd h (by omega), ?_, fun hL0 => absurd hL0 hL⟩
      intro h1
      rw [A264025_eq_cnt, cnt_0] at h1
      exact absurd h1 (by decide)
    · exact absurd ((inL_iff n).1 hc) hL
    · have h2 : 2 ≤ A264025 n := by
        rw [A264025_eq_cnt]; exact find2B_sound hc
      exact ⟨fun _ => by omega, fun h1 => absurd h1 (by omega),
        fun hLn => absurd hLn hL⟩

lemma L_lt_1400 : ∀ m ∈ L, m < 1400 := by decide

/-- The conjecture is equivalent to its tail: `a(n) ≥ 2` for all `n ≥ 1400`. -/
theorem conjecture_iff_tail :
    ((∀ n : ℕ, n > 0 → A264025 n > 0) ∧
     (∀ n : ℕ, A264025 n = 1 ↔ n ∈ L)) ↔
    (∀ n : ℕ, 1400 ≤ n → 2 ≤ A264025 n) := by
  constructor
  · rintro ⟨h1, h2⟩ n hn
    have hp := h1 n (by omega)
    have hne : A264025 n ≠ 1 := by
      intro he
      have hmem := (h2 n).1 he
      have := L_lt_1400 n hmem
      omega
    omega
  · intro ht
    constructor
    · intro n hn
      rcases Nat.lt_or_ge n 1400 with h | h
      · exact (A264025_low n h).1 hn
      · have := ht n h; omega
    · intro n
      rcases Nat.lt_or_ge n 1400 with h | h
      · exact (A264025_low n h).2
      · have h2 := ht n h
        exact ⟨fun he => absurd he (by omega),
          fun hLn => absurd (L_lt_1400 n hLn) (by omega)⟩

end A264025aux


/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  refine A264025aux.conjecture_iff_tail.mpr ?_
  /- Everything below `1400` has been verified by kernel computation above
     (`A264025aux.A264025_low`), and the 12 listed values are proved to have exactly
     one representation.  What remains is precisely the tail of Zhi-Wei Sun's open
     conjecture: `2 ≤ A264025 n` for all `n ≥ 1400`.  This has been verified
     numerically up to 6.5 × 10^10, but it is an open problem of Hardy–Littlewood
     class (the representation function has average order √n / log n). -/
  sorry
