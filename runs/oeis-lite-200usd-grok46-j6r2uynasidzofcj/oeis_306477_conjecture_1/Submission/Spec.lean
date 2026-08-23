import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxHeartbeats 40000000
set_option maxRecDepth 50000
set_option exponentiation.threshold 1100000

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

def binom2468 (w x y z : ℕ) : ℕ :=
  (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8

lemma choose_two_eq_mul (w : ℕ) :
    (w + 2).choose 2 = (w + 1) * (w + 2) / 2 := by
  rw [choose_two_right (w + 2)]
  have : w + 2 - 1 = w + 1 := by omega
  rw [this, Nat.mul_comm]

lemma choose_two_pos (t : ℕ) : 0 < (t + 2).choose 2 :=
  choose_pos (by omega)

lemma choose_n3_two_gt (n : ℕ) (hn : 0 < n) : n < (n + 3).choose 2 := by
  rw [choose_two_right (n + 3)]
  have hsub : n + 3 - 1 = n + 2 := by omega
  rw [hsub]
  have hdiv : 2 ∣ (n + 2) * (n + 3) := even_iff_two_dvd.mp (even_mul_succ_self (n + 2))
  have hdiv2 : 2 ∣ (n + 3) * (n + 2) := by simpa [mul_comm] using hdiv
  have hcancel : 2 * ((n + 3) * (n + 2) / 2) = (n + 3) * (n + 2) :=
    Nat.mul_div_cancel' hdiv2
  have hlt : 2 * n < (n + 3) * (n + 2) := by
    have : (n + 3) * (n + 2) = n * n + 5 * n + 6 := by ring
    rw [this]
    nlinarith
  rw [← hcancel] at hlt
  exact (Nat.mul_lt_mul_left (by decide : 0 < 2)).1 hlt

lemma choose_succ_ge_succ (m k : ℕ) (hk : 0 < k) (_hm : k ≤ m) :
    (m.choose k).succ ≤ (m + 1).choose k := by
  cases k with
  | zero => exact (lt_irrefl _ hk).elim
  | succ k =>
    rw [choose_succ_succ']
    change (m.choose (k + 1) + 1) ≤ m.choose k + m.choose (k + 1)
    have : 1 ≤ m.choose k := Nat.succ_le_of_lt (choose_pos (by omega))
    linarith

lemma choose_n4_four_gt : ∀ n, 0 < n → n < (n + 4).choose 4
  | 0, hn => absurd hn (Nat.lt_irrefl _)
  | 1, _ => by decide
  | n + 2, _ => by
    have ih : n + 1 < (n + 5).choose 4 := choose_n4_four_gt (n + 1) (Nat.succ_pos _)
    have hgrow : ((n + 5).choose 4).succ ≤ (n + 6).choose 4 :=
      choose_succ_ge_succ _ _ (by decide) (by omega)
    have : n + 2 + 4 = n + 6 := by omega
    rw [this]
    have h1 : n + 2 ≤ (n + 5).choose 4 := Nat.succ_le_of_lt ih
    exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_succ_le hgrow)

lemma choose_n6_six_gt : ∀ n, 0 < n → n < (n + 6).choose 6
  | 0, hn => absurd hn (Nat.lt_irrefl _)
  | 1, _ => by decide
  | n + 2, _ => by
    have ih : n + 1 < (n + 7).choose 6 := choose_n6_six_gt (n + 1) (Nat.succ_pos _)
    have hgrow : ((n + 7).choose 6).succ ≤ (n + 8).choose 6 :=
      choose_succ_ge_succ _ _ (by decide) (by omega)
    have : n + 2 + 6 = n + 8 := by omega
    rw [this]
    have h1 : n + 2 ≤ (n + 7).choose 6 := Nat.succ_le_of_lt ih
    exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_succ_le hgrow)

lemma choose_n8_eight_gt : ∀ n, 0 < n → n < (n + 8).choose 8
  | 0, hn => absurd hn (Nat.lt_irrefl _)
  | 1, _ => by decide
  | n + 2, _ => by
    have ih : n + 1 < (n + 9).choose 8 := choose_n8_eight_gt (n + 1) (Nat.succ_pos _)
    have hgrow : ((n + 9).choose 8).succ ≤ (n + 10).choose 8 :=
      choose_succ_ge_succ _ _ (by decide) (by omega)
    have : n + 2 + 8 = n + 10 := by omega
    rw [this]
    have h1 : n + 2 ≤ (n + 9).choose 8 := Nat.succ_le_of_lt ih
    exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_succ_le hgrow)

lemma lt_succ_of_binom2468 {n w x y z : ℕ}
    (h : binom2468 w x y z = n) (hn : 0 < n) :
    w < n + 1 ∧ x < n + 1 ∧ y < n + 1 ∧ z < n + 1 := by
  have hw0 : (w + 2).choose 2 ≤ n := by
    simp [binom2468] at h ⊢; omega
  have hx0 : (x + 3).choose 4 ≤ n := by
    simp [binom2468] at h ⊢; omega
  have hy0 : (y + 5).choose 6 ≤ n := by
    simp [binom2468] at h ⊢; omega
  have hz0 : (z + 7).choose 8 ≤ n := by
    simp [binom2468] at h ⊢; omega
  refine ⟨?hw, ?hx, ?hy, ?hz⟩
  · by_contra hnot
    have hmono : (n + 3).choose 2 ≤ (w + 2).choose 2 := choose_le_choose 2 (by omega)
    exact (not_le_of_gt (choose_n3_two_gt n hn)) (hmono.trans hw0)
  · by_contra hnot
    have hmono : (n + 4).choose 4 ≤ (x + 3).choose 4 := choose_le_choose 4 (by omega)
    exact (not_le_of_gt (choose_n4_four_gt n hn)) (hmono.trans hx0)
  · by_contra hnot
    have hmono : (n + 6).choose 6 ≤ (y + 5).choose 6 := choose_le_choose 6 (by omega)
    exact (not_le_of_gt (choose_n6_six_gt n hn)) (hmono.trans hy0)
  · by_contra hnot
    have hmono : (n + 8).choose 8 ≤ (z + 7).choose 8 := choose_le_choose 8 (by omega)
    exact (not_le_of_gt (choose_n8_eight_gt n hn)) (hmono.trans hz0)

lemma pos_of_rep {n w x y z : ℕ} (h : binom2468 w x y z = n) (hn : 0 < n) :
    0 <
      let R := Finset.range (n + 1)
      R.sum (fun w =>
        R.sum (fun x =>
          R.sum (fun y =>
            R.sum (fun z =>
              if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 +
                  (z + 7).choose 8 = n then 1 else 0)))) := by
  obtain ⟨hw, hx, hy, hz⟩ := lt_succ_of_binom2468 h hn
  have hwR : w ∈ range (n + 1) := mem_range.mpr hw
  have hxR : x ∈ range (n + 1) := mem_range.mpr hx
  have hyR : y ∈ range (n + 1) := mem_range.mpr hy
  have hzR : z ∈ range (n + 1) := mem_range.mpr hz
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨w, hwR, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x, hxR, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, hyR, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨z, hzR, ?_⟩
  unfold binom2468 at h
  simp [h]

lemma A306477_pos_of_rep {n w x y z : ℕ}
    (h : binom2468 w x y z = n) (hn : 0 < n) :
    0 < A306477 n := by
  simpa [A306477] using pos_of_rep h hn

/-! ### Bitset encoding -/

def triBits : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let t := (k + 1) * (k + 2) / 2
    triBits k ||| (2 ^ t)

def addVals (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (base <<< v) ||| addVals base vs

lemma testBit_triBits_iff (W t : ℕ) :
    (triBits W).testBit t = true ↔ ∃ w < W, (w + 1) * (w + 2) / 2 = t := by
  induction W with
  | zero =>
    simp [triBits]
  | succ W ih =>
    simp only [triBits, testBit_or, Bool.or_eq_true, testBit_two_pow, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨w, hw, rfl⟩ | h)
      · exact ⟨w, Nat.lt_succ_of_lt hw, rfl⟩
      · exact ⟨W, Nat.lt_succ_self W, h⟩
    · rintro ⟨w, hw, rfl⟩
      rw [Nat.lt_succ_iff] at hw
      rcases eq_or_lt_of_le hw with hW | hW
      · subst hW; exact Or.inr rfl
      · exact Or.inl ⟨w, hW, rfl⟩

lemma testBit_addVals_iff (base : ℕ) (vs : List ℕ) (n : ℕ) :
    (addVals base vs).testBit n = true ↔
      ∃ v ∈ vs, v ≤ n ∧ base.testBit (n - v) = true := by
  induction vs with
  | nil =>
    simp [addVals]
  | cons v vs ih =>
    simp only [addVals, testBit_or, Bool.or_eq_true, List.mem_cons, testBit_shiftLeft, ih]
    constructor
    · rintro (h | h)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨v, Or.inl rfl, h.1, h.2⟩
      · rcases h with ⟨v', hv', hge, hb⟩
        exact ⟨v', Or.inr hv', hge, hb⟩
    · rintro ⟨v', hv', hge, hb⟩
      rcases hv' with rfl | hv'
      · refine Or.inl ?_
        simp [hge, hb]
      · exact Or.inr ⟨v', hv', hge, hb⟩

lemma testBit_addVals_tri_iff (W : ℕ) (qs : List ℕ) (n : ℕ) :
    (addVals (triBits W) qs).testBit n = true ↔
      ∃ q ∈ qs, ∃ w < W, q ≤ n ∧ (w + 1) * (w + 2) / 2 = n - q := by
  rw [testBit_addVals_iff]
  constructor
  · rintro ⟨q, hq, hle, hb⟩
    rcases (testBit_triBits_iff W (n - q)).1 hb with ⟨w, hw, hwq⟩
    exact ⟨q, hq, w, hw, hle, hwq⟩
  · rintro ⟨q, hq, w, hw, hle, hwq⟩
    refine ⟨q, hq, hle, ?_⟩
    exact (testBit_triBits_iff W (n - q)).2 ⟨w, hw, hwq⟩

lemma testBit_add4_iff (W : ℕ) (qs rs ss : List ℕ) (n : ℕ) :
    (addVals (addVals (addVals (triBits W) qs) rs) ss).testBit n = true ↔
      ∃ s ∈ ss, ∃ r ∈ rs, ∃ q ∈ qs, ∃ w < W,
        s + r + q ≤ n ∧ (w + 1) * (w + 2) / 2 + q + r + s = n := by
  rw [testBit_addVals_iff]
  constructor
  · intro h
    rcases h with ⟨s, hs, hles, hbit⟩
    have h2 := (testBit_addVals_iff (addVals (triBits W) qs) rs (n - s)).1 hbit
    rcases h2 with ⟨r, hr, hler, hbit2⟩
    have h3 := (testBit_addVals_tri_iff W qs (n - s - r)).1 hbit2
    rcases h3 with ⟨q, hq, w, hw, hleq, hwq⟩
    have hsum : s + r + q ≤ n := by omega
    refine ⟨s, hs, r, hr, q, hq, w, hw, hsum, ?_⟩
    omega
  · intro h
    rcases h with ⟨s, hs, r, hr, q, hq, w, hw, hle, hwq⟩
    refine ⟨s, hs, by omega, ?_⟩
    refine (testBit_addVals_iff (addVals (triBits W) qs) rs (n - s)).2 ⟨r, hr, by omega, ?_⟩
    refine (testBit_addVals_tri_iff W qs (n - s - r)).2 ⟨q, hq, w, hw, by omega, ?_⟩
    omega

def boundN : ℕ := 1000000
def boundW : ℕ := 1413
def boundX : ℕ := 69
def boundY : ℕ := 28
def boundZ : ℕ := 18

def qList : List ℕ := List.map (fun x => (x + 3).choose 4) (List.range boundX)
def rList : List ℕ := List.map (fun y => (y + 5).choose 6) (List.range boundY)
def sList : List ℕ := List.map (fun z => (z + 7).choose 8) (List.range boundZ)

lemma mem_qList_iff {q : ℕ} :
    q ∈ qList ↔ ∃ x < boundX, (x + 3).choose 4 = q := by
  simp [qList, List.mem_map, List.mem_range]

lemma mem_rList_iff {r : ℕ} :
    r ∈ rList ↔ ∃ y < boundY, (y + 5).choose 6 = r := by
  simp [rList, List.mem_map, List.mem_range]

lemma mem_sList_iff {s : ℕ} :
    s ∈ sList ↔ ∃ z < boundZ, (z + 7).choose 8 = s := by
  simp [sList, List.mem_map, List.mem_range]

def covered : ℕ :=
  addVals (addVals (addVals (triBits boundW) qList) rList) sList

def maskN : ℕ := (2 ^ (boundN + 1)) - 2

lemma covered_mask : covered &&& maskN = maskN := by
  decide

lemma maskN_eq : maskN = 2 ^ 1 * (2 ^ boundN - 1) := by
  unfold maskN
  have hpow : 2 ^ (boundN + 1) = 2 * 2 ^ boundN := by
    rw [pow_succ, Nat.mul_comm]
  rw [hpow]
  have hpos : 1 ≤ 2 ^ boundN := Nat.one_le_two_pow
  omega

lemma testBit_maskN {n : ℕ} (h1 : 0 < n) (h2 : n ≤ boundN) :
    maskN.testBit n = true := by
  rw [maskN_eq, testBit_two_pow_mul]
  simp [testBit_two_pow_sub_one]
  exact ⟨h1, Nat.sub_lt_left_of_lt_add h1 (Nat.lt_succ_of_le h2)⟩

lemma testBit_covered_of_le {n : ℕ} (h1 : 0 < n) (h2 : n ≤ boundN) :
    covered.testBit n = true := by
  have hmask := testBit_maskN h1 h2
  have heq := covered_mask
  have : (covered &&& maskN).testBit n = maskN.testBit n := by rw [heq]
  simpa [testBit_and, hmask] using this

lemma exists_rep_of_le_bound {n : ℕ} (hn : 0 < n) (hle : n ≤ boundN) :
    ∃ w x y z, binom2468 w x y z = n := by
  have hbit := testBit_covered_of_le hn hle
  rw [show covered.testBit n = (addVals (addVals (addVals (triBits boundW) qList) rList) sList).testBit n
      from rfl] at hbit
  rcases (testBit_add4_iff boundW qList rList sList n).1 hbit with
    ⟨s, hs, r, hr, q, hq, w, hw, hsum, heq⟩
  rcases mem_qList_iff.1 hq with ⟨x, hx, hxq⟩
  rcases mem_rList_iff.1 hr with ⟨y, hy, hyr⟩
  rcases mem_sList_iff.1 hs with ⟨z, hz, hzs⟩
  refine ⟨w, x, y, z, ?_⟩
  simp [binom2468, choose_two_eq_mul, hxq, hyr, hzs, heq]

lemma choose_eight_eight : (8 : ℕ).choose 8 = 1 := rfl
lemma choose_seven_eight : (7 : ℕ).choose 8 = 0 := rfl
lemma choose_six_six : (6 : ℕ).choose 6 = 1 := rfl
lemma choose_five_six : (5 : ℕ).choose 6 = 0 := rfl
lemma choose_four_four : (4 : ℕ).choose 4 = 1 := rfl
lemma choose_three_four : (3 : ℕ).choose 4 = 0 := rfl

lemma binom2468_inc_z (w x y : ℕ) :
    binom2468 w x y 1 = binom2468 w x y 0 + 1 := by
  unfold binom2468
  change (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (8 : ℕ).choose 8 =
    (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (7 : ℕ).choose 8 + 1
  rw [choose_eight_eight, choose_seven_eight]

lemma binom2468_inc_y (w x z : ℕ) :
    binom2468 w x 1 z = binom2468 w x 0 z + 1 := by
  unfold binom2468
  change (w + 2).choose 2 + (x + 3).choose 4 + (6 : ℕ).choose 6 + (z + 7).choose 8 =
    (w + 2).choose 2 + (x + 3).choose 4 + (5 : ℕ).choose 6 + (z + 7).choose 8 + 1
  rw [choose_six_six, choose_five_six]
  omega

lemma binom2468_inc_x (w y z : ℕ) :
    binom2468 w 1 y z = binom2468 w 0 y z + 1 := by
  unfold binom2468
  change (w + 2).choose 2 + (4 : ℕ).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 =
    (w + 2).choose 2 + (3 : ℕ).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 + 1
  rw [choose_four_four, choose_three_four]
  omega

/-- A representation with a vanishing `x`, `y` or `z` coordinate can be incremented. -/
lemma exists_rep_succ_of_easy {n w x y z : ℕ}
    (h : binom2468 w x y z = n) (heasy : x = 0 ∨ y = 0 ∨ z = 0) :
    ∃ w' x' y' z', binom2468 w' x' y' z' = n + 1 := by
  rcases heasy with hx | hy | hz
  · subst hx
    exact ⟨w, 1, y, z, by rw [binom2468_inc_x, h]⟩
  · subst hy
    exact ⟨w, x, 1, z, by rw [binom2468_inc_y, h]⟩
  · subst hz
    exact ⟨w, x, y, 1, by rw [binom2468_inc_z, h]⟩

/-- `S(a) + 9 = T(1) + Q(2) + R(1) + S(a)`. -/
lemma binom2468_S_add_nine (a : ℕ) :
    binom2468 1 2 1 a = (a + 7).choose 8 + 9 := by
  simp [binom2468]
  decide

/-- `S(a) + 45 = T(8) + S(a)`. -/
lemma binom2468_S_add_fortyfive (a : ℕ) :
    binom2468 8 0 0 a = (a + 7).choose 8 + 45 := by
  simp [binom2468]
  decide

/-! ### Triangular characterisation -/

def isTriangular (m : ℕ) : Prop := ∃ w, (w + 1) * (w + 2) / 2 = m

lemma eight_mul_tri_add_one (w : ℕ) :
    8 * ((w + 1) * (w + 2) / 2) + 1 = (2 * w + 3) * (2 * w + 3) := by
  have hdiv : 2 ∣ (w + 1) * (w + 2) := even_iff_two_dvd.mp (even_mul_succ_self (w + 1))
  have hmul : 2 * ((w + 1) * (w + 2) / 2) = (w + 1) * (w + 2) := Nat.mul_div_cancel' hdiv
  nlinarith

lemma isTriangular_iff_odd_square (m : ℕ) (_hm : 0 < m) :
    isTriangular m ↔ ∃ k : ℕ, k % 2 = 1 ∧ k * k = 8 * m + 1 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨2 * w + 3, ?_, ?_⟩
    · simp [Nat.add_mod]
    · rw [← hw]
      exact (eight_mul_tri_add_one w).symm
  · rintro ⟨k, hodd, hsq⟩
    have hkge : 3 ≤ k := by
      by_contra h
      interval_cases k <;> simp at hodd hsq <;> omega
    set w := (k - 3) / 2
    refine ⟨w, ?_⟩
    have hke : 2 * w + 3 = k := by
      have : k % 2 = 1 := hodd
      omega
    have h8 : 8 * ((w + 1) * (w + 2) / 2) + 1 = 8 * m + 1 := by
      calc 8 * ((w + 1) * (w + 2) / 2) + 1
          = (2 * w + 3) * (2 * w + 3) := eight_mul_tri_add_one w
        _ = k * k := by rw [hke]
        _ = 8 * m + 1 := hsq
    omega

lemma binom2468_eq_iff_triangular (w x y z n : ℕ) :
    binom2468 w x y z = n ↔
      (w + 1) * (w + 2) / 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  simp [binom2468, choose_two_eq_mul]

lemma exists_rep_of_triangular_remainder {n q r s : ℕ}
    (h : isTriangular (n - (q + r + s))) (hle : q + r + s ≤ n) :
    ∃ w, (w + 1) * (w + 2) / 2 + q + r + s = n := by
  rcases h with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  omega

lemma exists_rep_of_isTriangular {n x y z : ℕ}
    (h : isTriangular (n - ((x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8)))
    (hle : (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 ≤ n) :
    ∃ w, binom2468 w x y z = n := by
  obtain ⟨w, hw⟩ := exists_rep_of_triangular_remainder h hle
  exact ⟨w, by simpa [binom2468, choose_two_eq_mul] using hw⟩

lemma factorial_eight : (8 : ℕ).factorial = 40320 := by decide

lemma choose_eight_mul (z : ℕ) :
    40320 * (z + 7).choose 8 = (z + 7).descFactorial 8 := by
  rw [← factorial_eight, descFactorial_eq_factorial_mul_choose]

/-- `C(z+7,8) ≥ z^8 / 40320`. -/
lemma choose_eight_ge (z : ℕ) : z ^ 8 ≤ 40320 * (z + 7).choose 8 := by
  rw [choose_eight_mul, descFactorial_eq_prod_range]
  have h : ∀ i ∈ range 8, z ≤ z + 7 - i := by
    intro i hi
    have : i < 8 := mem_range.mp hi
    omega
  calc
    z ^ 8 = ∏ _i ∈ range 8, z := by simp [prod_const, card_range]
    _ ≤ ∏ i ∈ range 8, (z + 7 - i) := prod_le_prod' h

lemma twentyfour_mul_choose_four (x : ℕ) :
    24 * (x + 3).choose 4 = x * (x + 1) * (x + 2) * (x + 3) := by
  have h := descFactorial_eq_factorial_mul_choose (x + 3) 4
  have hf : (4 : ℕ).factorial = 24 := by decide
  have hd : (x + 3).descFactorial 4 = x * (x + 1) * (x + 2) * (x + 3) := by
    simp [descFactorial_succ]
    ring
  rw [hf] at h
  rw [← h, hd]

/-- `24 * C(x+3,4) + 1 = (x^2 + 3x + 1)^2`. -/
lemma twentyfour_choose_four_add_one (x : ℕ) :
    24 * (x + 3).choose 4 + 1 = (x * x + 3 * x + 1) * (x * x + 3 * x + 1) := by
  have h24 := twentyfour_mul_choose_four x
  have : x * (x + 1) * (x + 2) * (x + 3) + 1 =
      (x * x + 3 * x + 1) * (x * x + 3 * x + 1) := by ring
  omega

lemma eight_mul_choose_two_add_one (w : ℕ) :
    8 * (w + 2).choose 2 + 1 = (2 * w + 3) * (2 * w + 3) := by
  rw [choose_two_eq_mul]
  exact (eight_mul_tri_add_one w).symm

/-- Master identity: a 2468-representation of `n` yields
`u^2 + 3k^2 + 24(R+S) = 4(6n+1)` with `u = x^2+3x+1` and `k = 2w+3`. -/
lemma master_identity (w x y z n : ℕ) (h : binom2468 w x y z = n) :
    (x * x + 3 * x + 1) * (x * x + 3 * x + 1) + 3 * (2 * w + 3) * (2 * w + 3)
      + 24 * ((y + 5).choose 6 + (z + 7).choose 8) = 4 * (6 * n + 1) := by
  unfold binom2468 at h
  have hQ := twentyfour_choose_four_add_one x
  have hT := eight_mul_choose_two_add_one w
  nlinarith

lemma exists_rep_of_odd_square {n x y z : ℕ}
    (hle : (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 ≤ n)
    (hsq : ∃ k : ℕ, k % 2 = 1 ∧ k * k = 8 * (n - ((x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8)) + 1)
    (hn : 0 < n - ((x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8)) :
    ∃ w, binom2468 w x y z = n := by
  have htri : isTriangular (n - ((x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8)) :=
    (isTriangular_iff_odd_square _ hn).2 hsq
  exact exists_rep_of_isTriangular htri hle

lemma factorial_six : (6 : ℕ).factorial = 720 := by decide
lemma factorial_four : (4 : ℕ).factorial = 24 := by decide

lemma choose_six_mul (y : ℕ) :
    720 * (y + 5).choose 6 = (y + 5).descFactorial 6 := by
  rw [← factorial_six, descFactorial_eq_factorial_mul_choose]

lemma choose_four_mul (x : ℕ) :
    24 * (x + 3).choose 4 = (x + 3).descFactorial 4 := by
  rw [← factorial_four, descFactorial_eq_factorial_mul_choose]

/-- `C(y+5,6) ≥ y^6 / 720`. -/
lemma choose_six_ge (y : ℕ) : y ^ 6 ≤ 720 * (y + 5).choose 6 := by
  rw [choose_six_mul, descFactorial_eq_prod_range]
  have h : ∀ i ∈ range 6, y ≤ y + 5 - i := by
    intro i hi
    have : i < 6 := mem_range.mp hi
    omega
  calc
    y ^ 6 = ∏ _i ∈ range 6, y := by simp [prod_const, card_range]
    _ ≤ ∏ i ∈ range 6, (y + 5 - i) := prod_le_prod' h

/-- `C(z+7,8) ≤ (z+7)^8 / 40320`. -/
lemma choose_eight_le (z : ℕ) : 40320 * (z + 7).choose 8 ≤ (z + 7) ^ 8 := by
  rw [choose_eight_mul, descFactorial_eq_prod_range]
  have h : ∀ i ∈ range 8, z + 7 - i ≤ z + 7 := by
    intro i hi
    have : i < 8 := mem_range.mp hi
    omega
  calc
    ∏ i ∈ range 8, (z + 7 - i) ≤ ∏ _i ∈ range 8, (z + 7) := prod_le_prod' h
    _ = (z + 7) ^ 8 := by simp [prod_const, card_range]

lemma choose_eight_succ_sub (z : ℕ) :
    (z + 8).choose 8 - (z + 7).choose 8 = (z + 7).choose 7 := by
  have h : (z + 8).choose 8 = (z + 7).choose 7 + (z + 7).choose 8 := by
    simpa using choose_succ_succ' (z + 7) 7
  rw [h, Nat.add_comm, Nat.add_sub_cancel_left]

/-- The least `z` with `C(z+8,8) > n`, equivalently the greedy octatope index. -/
lemma exists_max_choose_eight (n : ℕ) :
    ∃ z, (z + 7).choose 8 ≤ n ∧ n < (z + 8).choose 8 := by
  have hbig : n < (n + 8).choose 8 := by
    cases n with
    | zero => decide
    | succ n => exact choose_n8_eight_gt (n + 1) (Nat.succ_pos _)
  by_cases h8 : n < (8 : ℕ).choose 8
  · refine ⟨0, ?_, ?_⟩
    · simp
    · simpa using h8
  · have hP0 : (0 + 7).choose 8 ≤ n := by simp
    let P : ℕ → Prop := fun z => (z + 7).choose 8 ≤ n
    have hP0' : P 0 := hP0
    let z := Nat.findGreatest P n
    have hzP : P z := Nat.findGreatest_spec (n := n) (m := 0) (Nat.zero_le _) hP0'
    refine ⟨z, hzP, ?_⟩
    by_contra hnot
    have hle' : (z + 8).choose 8 ≤ n := Nat.le_of_not_gt hnot
    have hPs : P (z + 1) := by simpa [P] using hle'
    have hz_le : ∀ z, P z → z ≤ n := by
      intro z hz
      by_contra hgt
      have : n < z := Nat.lt_of_not_ge hgt
      have hmono : (n + 8).choose 8 ≤ (z + 7).choose 8 :=
        choose_le_choose 8 (by omega)
      exact (not_le_of_gt hbig) (hmono.trans hz)
    have hz1le : z + 1 ≤ n := hz_le _ hPs
    have hng : ¬ P (z + 1) :=
      Nat.findGreatest_is_greatest (P := P) (n := n) (by omega) hz1le
    exact hng hPs

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as
C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
This is also known as "the 2-4-6-8 conjecture".
-/
theorem oeis_306477_conjecture_1 : ∀ n : ℕ, 0 < n → 0 < A306477 n := by
  intro n hn
  by_cases hle : n ≤ boundN
  · obtain ⟨w, x, y, z, h⟩ := exists_rep_of_le_bound hn hle
    exact A306477_pos_of_rep h hn
  · sorry
