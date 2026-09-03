import FormalConjecturesUtil

/-! Verified special cases for sets invariant under binary-digit permutations.
The stronger `BinarySymmetric` result requires only invariance within each fixed
binary length and digit sum. This is not a proof of the unrestricted
Erdős–Turán conjecture. -/

namespace Erdos3BinarySymmetryCase

set_option maxHeartbeats 1000000

def digitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma digitSum_ofDigits (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    digitSum (Nat.ofDigits 2 L) = L.sum :=
  Nat.sum_digits_ofDigits_eq_sum (by omega) ⟨rfl, hL⟩

lemma padded_sum (m i : ℕ) : (Nat.digitsAppend 2 m i).sum = digitSum i := by
  simp [Nat.digitsAppend, digitSum]

lemma padded_value (m i : ℕ) : Nat.ofDigits 2 (Nat.digitsAppend 2 m i) = i := by
  simp [Nat.digitsAppend, Nat.ofDigits_digits]

lemma complement_sum (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    L.sum + (L.map (fun x ↦ 1 - x)).sum = L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := hL x (by simp)
    have htail : ∀ y ∈ L, y < 2 := fun y hy ↦ hL y (by simp [hy])
    have h := ih htail
    have hx' : x = 0 ∨ x = 1 := by omega
    rcases hx' with rfl | rfl <;> simp_all <;> omega

lemma complement_value (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    Nat.ofDigits 2 L + Nat.ofDigits 2 (L.map (fun x ↦ 1 - x)) + 1 = 2 ^ L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := hL x (by simp)
    have htail : ∀ y ∈ L, y < 2 := fun y hy ↦ hL y (by simp [hy])
    have h := ih htail
    have hx' : x = 0 ∨ x = 1 := by omega
    rcases hx' with rfl | rfl <;>
      simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ] <;>
      simp only [Nat.sub_zero, Nat.sub_self] <;> omega

lemma replicate_one_value (m : ℕ) : Nat.ofDigits 2 (List.replicate m 1) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

lemma weighted_list_sum (r : ℝ) (m : ℕ) :
    ∑ L ∈ List.fixedLengthDigits one_lt_two m, r ^ L.sum = (1 + r) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.fixedLengthDigits_succ_eq_disjiUnion, Finset.sum_disjiUnion]
    simp only [List.consFixedLengthDigits, List.cons.injEq, true_and, implies_true,
      Set.injOn_of_eq_iff_eq, Finset.sum_image, List.sum_cons, pow_add]
    simp_rw [← Finset.mul_sum]
    rw [ih]
    change (∑ x ∈ Finset.range (1 + 1), r ^ x * (1 + r) ^ m) = _
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, pow_zero, zero_add, one_mul, pow_succ]
    ring

lemma weighted_nat_sum (r : ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (2 ^ m), r ^ digitSum n = (1 + r) ^ m := by
  rw [← weighted_list_sum r m]
  refine (Finset.sum_nbij (Nat.ofDigits 2)
    (by exact (Nat.bijOn_ofDigits' one_lt_two m).1)
    (Nat.bijOn_ofDigits' one_lt_two m).2.1
    (Nat.bijOn_ofDigits' one_lt_two m).2.2 ?_).symm
  intro L hL
  rw [digitSum_ofDigits L ((List.mem_fixedLengthDigits_iff one_lt_two).mp hL).2]

/-- The low and high binary halves are complementary, so the digit sum is constant. -/
lemma constant_digitSum_progression {m t : ℕ} (hmt : m ≤ t) {i : ℕ} (hi : i < 2 ^ m) :
    digitSum ((2 ^ m - 1) + 2 ^ (2 * m) * Nat.ofDigits 2 (List.replicate (t - m) 1) +
      i * (2 ^ m - 1)) = t := by
  let L := Nat.digitsAppend 2 m i
  let C := L.map (fun x ↦ 1 - x)
  let R := List.replicate (t - m) 1
  let W := C ++ L ++ R
  have hLlen : L.length = m := Nat.length_digitsAppend one_lt_two m hi
  have hLval : Nat.ofDigits 2 L = i := padded_value m i
  have hL : ∀ x ∈ L, x < 2 := fun x hx ↦ Nat.lt_of_mem_digitsAppend one_lt_two m x hx
  have hC : ∀ x ∈ C, x < 2 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    omega
  have hR : ∀ x ∈ R, x < 2 := by
    intro x hx
    have hx' : x = 1 := (List.mem_replicate.mp hx).2
    omega
  have hW : ∀ x ∈ W, x < 2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (List.mem_append.mp hx).elim (hC x) (hL x)
    · exact hR x hx
  have hsum : W.sum = t := by
    have hs := complement_sum L hL
    dsimp [W, R]
    simp only [List.sum_append_nat, List.sum_replicate, nsmul_eq_mul, mul_one]
    dsimp [C]
    omega
  have hval : Nat.ofDigits 2 W =
      (2 ^ m - 1) + 2 ^ (2 * m) * Nat.ofDigits 2 R + i * (2 ^ m - 1) := by
    have hcval := complement_value L hL
    rw [hLlen, padded_value m i] at hcval
    have hp : 1 ≤ 2 ^ m := one_le_pow₀ (by omega)
    have hp' := Nat.sub_add_cancel hp
    have hmul : i * (2 ^ m - 1) + i = i * 2 ^ m := by nlinarith
    dsimp [W, C]
    rw [Nat.ofDigits_append, Nat.ofDigits_append]
    simp only [List.length_append, List.length_map, hLlen, hLval]
    rw [show m + m = 2 * m by omega]
    nlinarith
  rw [← hval]
  exact (digitSum_ofDigits W hW).trans hsum

lemma small_digitSum_card_bound {S : Finset ℕ} {M L : ℕ}
    (hM : ∀ n ∈ S, digitSum n ≤ M) (hL : ∀ n ∈ S, n < 2 ^ L) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ M * (3 / 2) ^ L := by
  classical
  calc
    (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (2 : ℝ) ^ M * (1 / 2) ^ digitSum n := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        (1 : ℝ) ≤ 2 ^ M / (2 : ℝ) ^ digitSum n :=
          (one_le_div (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) (hM n hn))
        _ = _ := by simp [div_eq_mul_inv]
    _ = (2 : ℝ) ^ M * ∑ n ∈ S, (1 / 2 : ℝ) ^ digitSum n := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ M * ∑ n ∈ Finset.range (2 ^ L), (1 / 2 : ℝ) ^ digitSum n := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn ↦ Finset.mem_range.mpr (hL n hn)) (fun _ _ _ ↦ by positivity)
    _ = _ := by rw [weighted_nat_sum]; norm_num

lemma finite_recip_bound_of_digitSum_le (M : ℕ) (S : Finset ℕ)
    (hM : ∀ n ∈ S, digitSum n ≤ M) :
    (∑ n ∈ S, 1 / (n : ℝ)) ≤
      ∑' j : ℕ, ((2 : ℝ) ^ M * (3 / 2)) * (3 / 4) ^ j := by
  classical
  have hgeo : Summable (fun j : ℕ ↦ ((2 : ℝ) ^ M * (3 / 2)) * (3 / 4) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_left _
  let S' := S.erase 0
  let J := S'.image (Nat.log 2)
  have hfiber (j : ℕ) :
      (∑ n ∈ S'.filter (fun n ↦ Nat.log 2 n = j), 1 / (n : ℝ)) ≤
        ((2 : ℝ) ^ M * (3 / 2)) * (3 / 4) ^ j := by
    let T := S'.filter (fun n ↦ Nat.log 2 n = j)
    have hTsub : T ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hTb : ∀ n ∈ T, n < 2 ^ (j + 1) := by
      intro n hn
      obtain ⟨_, hnj⟩ := Finset.mem_filter.mp hn
      simpa [hnj] using Nat.lt_pow_succ_log_self one_lt_two n
    have hTc := small_digitSum_card_bound (fun n hn ↦ hM n (hTsub hn)) hTb
    calc
      (∑ n ∈ T, 1 / (n : ℝ)) ≤ ∑ n ∈ T, 1 / ((2 ^ j : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
        have hn0 := (Finset.mem_erase.mp hnS).1
        have hpow : 2 ^ j ≤ n := by simpa [hnj] using Nat.pow_log_le_self 2 hn0
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpow)
      _ = (T.card : ℝ) / ((2 ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ((2 : ℝ) ^ M * (3 / 2) ^ (j + 1)) / ((2 ^ j : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hTc (by positivity)
      _ = ((2 : ℝ) ^ M * (3 / 2)) * (3 / 4) ^ j := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        calc
          _ = ((2 : ℝ) ^ M * (3 / 2)) * (((3 / 2) / (2 : ℝ)) ^ j) := by
            conv_rhs => rw [div_pow]
            rw [pow_succ]
            ring
          _ = _ := by norm_num
  calc
    (∑ n ∈ S, 1 / (n : ℝ)) = ∑ n ∈ S', 1 / (n : ℝ) :=
      (Finset.sum_erase S (by simp : (1 : ℝ) / (0 : ℕ) = 0)).symm
    _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log 2 n = j), 1 / (n : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun n hn ↦ Finset.mem_image_of_mem (Nat.log 2) hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
    _ ≤ ∑ j ∈ J, ((2 : ℝ) ^ M * (3 / 2)) * (3 / 4) ^ j :=
      Finset.sum_le_sum (fun j _ ↦ hfiber j)
    _ ≤ _ := Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) hgeo

/-- A bounded number of ones in the binary expansion forces reciprocal summability. -/
theorem summable_of_bounded_digitSum {A : Set ℕ} {M : ℕ}
    (hM : ∀ n ∈ A, digitSum n ≤ M) : Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  apply summable_of_sum_le
    (c := ∑' j : ℕ, ((2 : ℝ) ^ M * (3 / 2)) * (3 / 4) ^ j) (fun _ ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hbound : ∀ n ∈ F.map e, digitSum n ≤ M := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact hM a.val a.property
  simpa [e] using finite_recip_bound_of_digitSum_le M (F.map e) hbound

/-- Membership depends only on the number of ones in the binary expansion.
This allows rearrangement with arbitrary zero padding, a genuine extra hypothesis. -/
def DigitSumInvariant (A : Set ℕ) : Prop :=
  ∀ x ∈ A, ∀ y, digitSum y = digitSum x → y ∈ A

theorem divergent_digitSum_unbounded {A : Set ℕ}
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (M : ℕ) :
    ∃ n ∈ A, M ≤ digitSum n := by
  by_contra! h
  exact hs (summable_of_bounded_digitSum (fun n hn ↦ (h n hn).le))

/-- An unconditional special case of the conjecture, with explicit AP witnesses. -/
theorem digitSum_invariant_contains_ap {A : Set ℕ} (hA : DigitSumInvariant A)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (k : ℕ) :
    ∃ S ⊆ A, S.IsAPOfLength k := by
  obtain ⟨n, hn, hlarge⟩ := divergent_digitSum_unbounded hs (k + 1)
  let m := k + 1
  let t := digitSum n
  let a := (2 ^ m - 1) + 2 ^ (2 * m) * Nat.ofDigits 2 (List.replicate (t - m) 1)
  let d := 2 ^ m - 1
  have hpow : k + 1 < 2 ^ m := Nat.lt_two_pow_self
  have hd : 0 < d := by dsimp [d]; omega
  let g : ℕ → ℕ := fun i ↦ a + i * d
  have hgi : Function.Injective g := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  refine ⟨g '' Set.Iio k, ?_, a, d, ?_, ?_⟩
  · rintro x ⟨i, hi, rfl⟩
    have hik : i < k := hi
    apply hA n hn
    exact constant_digitSum_progression hlarge (by omega : i < 2 ^ m)
  · change (g '' Set.Iio k).encard = (k : ℕ∞)
    rw [hgi.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [g]

/-- The exact original conclusion under binary digit-sum invariance. -/
theorem digitSum_invariant_case {A : Set ℕ} (hA : DigitSumInvariant A)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply Filter.frequently_atTop.mpr
  intro k
  exact ⟨k, le_rfl, digitSum_invariant_contains_ap hA hs k⟩

def digitZeros (n : ℕ) : ℕ := (Nat.digits 2 n).length - digitSum n

def reflected (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (((Nat.digits 2 n).map (fun x ↦ 1 - x)) ++ [1])

lemma reflected_digits (n : ℕ) :
    Nat.digits 2 (reflected n) = ((Nat.digits 2 n).map (fun x ↦ 1 - x)) ++ [1] := by
  apply Nat.digits_ofDigits 2 one_lt_two
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      omega
    · simp only [List.mem_singleton] at hx
      omega
  · intro h
    simp

lemma reflected_length (n : ℕ) :
    (Nat.digits 2 (reflected n)).length = (Nat.digits 2 n).length + 1 := by
  simp [reflected_digits]

lemma reflected_digitSum (n : ℕ) : digitSum (reflected n) = digitZeros n + 1 := by
  have h := complement_sum (Nat.digits 2 n) (fun _ hx ↦ Nat.digits_lt_base one_lt_two hx)
  simp only [digitSum, digitZeros, reflected_digits, List.sum_append_nat, List.sum_cons,
    List.sum_nil, add_zero]
  omega

lemma reflected_identity (n : ℕ) : n + reflected n + 1 = 2 * 2 ^ (Nat.digits 2 n).length := by
  have h := complement_value (Nat.digits 2 n) (fun _ hx ↦ Nat.digits_lt_base one_lt_two hx)
  rw [Nat.ofDigits_digits] at h
  dsimp [reflected]
  rw [Nat.ofDigits_append]
  simp only [List.length_map, Nat.ofDigits_singleton, mul_one]
  omega

lemma reflected_injective : Function.Injective reflected := by
  intro n m h
  have hlen : (Nat.digits 2 n).length = (Nat.digits 2 m).length := by
    have hh := congrArg (fun x ↦ (Nat.digits 2 x).length) h
    simpa only [reflected_length, Nat.add_right_cancel_iff] using hh
  have hn := reflected_identity n
  have hm := reflected_identity m
  rw [h, hlen] at hn
  omega

lemma reflected_pos (n : ℕ) : 0 < reflected n := by
  by_contra h
  have hz : reflected n = 0 := by omega
  have hlen := reflected_length n
  rw [hz, Nat.digits_zero] at hlen
  simp at hlen

lemma reflected_le_four_mul {n : ℕ} (hn : n ≠ 0) : reflected n ≤ 4 * n := by
  have hb := Nat.base_pow_length_digits_le 2 n one_lt_two hn
  have hid := reflected_identity n
  omega

/-- A bounded number of zeros also forces reciprocal summability. -/
theorem summable_of_bounded_digitZeros {A : Set ℕ} {M : ℕ}
    (hM : ∀ n ∈ A, digitZeros n ≤ M) : Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  let B := reflected '' A
  have hB : Summable (fun b : B ↦ 1 / (b : ℝ)) := by
    apply summable_of_bounded_digitSum (M := M + 1)
    rintro n ⟨x, hx, rfl⟩
    rw [reflected_digitSum]
    exact Nat.add_le_add_right (hM x hx) 1
  let e : A → B := fun n ↦ ⟨reflected n, ⟨n.val, n.property, rfl⟩⟩
  have he : Function.Injective e := by
    intro n m h
    exact Subtype.ext (reflected_injective (congrArg Subtype.val h))
  have hs : Summable (fun n : A ↦ 1 / (reflected n : ℝ)) := hB.comp_injective (i := e) he
  apply (hs.mul_left 4).of_nonneg_of_le (fun _ ↦ by positivity)
  intro n
  by_cases hn : n.val = 0
  · simp only [hn, Nat.cast_zero, div_zero]
    positivity
  have hp : (0 : ℝ) < reflected n := by exact_mod_cast reflected_pos n
  have hn' : (0 : ℝ) < n.val := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [← mul_div_assoc, mul_one, div_le_div_iff₀ hn' hp]
  simpa using (show (reflected n : ℝ) ≤ 4 * (n.val : ℝ) by
    exact_mod_cast reflected_le_four_mul hn)

lemma prefix_progression (m : ℕ) (R : List ℕ) (hR : ∀ x ∈ R, x < 2)
    (hRne : R ≠ []) (hRlast : R.getLast hRne ≠ 0) {i : ℕ} (hi : i < 2 ^ m) :
    let x := (2 ^ m - 1) + 2 ^ (2 * m) * Nat.ofDigits 2 R + i * (2 ^ m - 1)
    digitSum x = m + R.sum ∧ (Nat.digits 2 x).length = 2 * m + R.length := by
  dsimp only
  let L := Nat.digitsAppend 2 m i
  let C := L.map (fun x ↦ 1 - x)
  let W := C ++ L ++ R
  have hLlen : L.length = m := Nat.length_digitsAppend one_lt_two m hi
  have hLval : Nat.ofDigits 2 L = i := padded_value m i
  have hL : ∀ x ∈ L, x < 2 := fun x hx ↦ Nat.lt_of_mem_digitsAppend one_lt_two m x hx
  have hC : ∀ x ∈ C, x < 2 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    omega
  have hW : ∀ x ∈ W, x < 2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (List.mem_append.mp hx).elim (hC x) (hL x)
    · exact hR x hx
  have hdigits : Nat.digits 2 (Nat.ofDigits 2 W) = W := by
    apply Nat.digits_ofDigits 2 one_lt_two W hW
    intro h
    rw [List.getLast_append_of_right_ne_nil _ _ hRne]
    exact hRlast
  have hval : Nat.ofDigits 2 W =
      (2 ^ m - 1) + 2 ^ (2 * m) * Nat.ofDigits 2 R + i * (2 ^ m - 1) := by
    have hcval := complement_value L hL
    rw [hLlen, hLval] at hcval
    have hp : 1 ≤ 2 ^ m := one_le_pow₀ (by omega)
    have hp' := Nat.sub_add_cancel hp
    have hmul : i * (2 ^ m - 1) + i = i * 2 ^ m := by nlinarith
    dsimp [W, C]
    rw [Nat.ofDigits_append, Nat.ofDigits_append]
    simp only [List.length_append, List.length_map, hLlen, hLval]
    rw [show m + m = 2 * m by omega]
    nlinarith
  rw [← hval]
  constructor
  · rw [digitSum, hdigits]
    have hs := complement_sum L hL
    dsimp [W, C]
    simp only [List.sum_append_nat]
    omega
  · rw [hdigits]
    simp [W, C, hLlen, two_mul, add_assoc]

lemma digitSum_le_length (n : ℕ) : digitSum n ≤ (Nat.digits 2 n).length := by
  have h := complement_sum (Nat.digits 2 n) (fun _ hx ↦ Nat.digits_lt_base one_lt_two hx)
  dsimp [digitSum]
  omega

/-- Divergence forces arbitrarily many zeros and ones in a single binary expansion. -/
theorem divergent_many_zeros_and_ones {A : Set ℕ}
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (M : ℕ) :
    ∃ n ∈ A, M < digitSum n ∧ M < digitZeros n := by
  classical
  by_contra! h
  let L : Set ℕ := {n | digitSum n ≤ M}
  let Z : Set ℕ := {n | digitZeros n ≤ M}
  have hL : Summable (L.indicator (fun n : ℕ ↦ 1 / (n : ℝ))) :=
    summable_subtype_iff_indicator.mp (summable_of_bounded_digitSum (fun _ hn ↦ hn))
  have hZ : Summable (Z.indicator (fun n : ℕ ↦ 1 / (n : ℝ))) :=
    summable_subtype_iff_indicator.mp (summable_of_bounded_digitZeros (fun _ hn ↦ hn))
  apply hs
  apply (summable_subtype_iff_indicator (s := A) (f := fun n : ℕ ↦ 1 / (n : ℝ))).mpr
  apply (hL.add hZ).of_nonneg_of_le
    (fun n ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) n)
  intro n
  by_cases hn : n ∈ A
  · have hcases : n ∈ L ∨ n ∈ Z := by
      by_cases hnl : digitSum n ≤ M
      · exact Or.inl hnl
      · exact Or.inr (h n hn (by omega))
    rcases hcases with hnl | hnz
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hnl]
      exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ ↦ by positivity) n)
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hnz]
      exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ ↦ by positivity) n)
  · rw [Set.indicator_of_notMem hn]
    exact add_nonneg (Set.indicator_nonneg (fun _ _ ↦ by positivity) n)
      (Set.indicator_nonneg (fun _ _ ↦ by positivity) n)

/-- Invariance under rearranging a fixed-length binary expansion; the leading digit
must remain nonzero. For binary words, length and digit sum determine the multiset. -/
def BinarySymmetric (A : Set ℕ) : Prop :=
  ∀ x ∈ A, ∀ y, (Nat.digits 2 y).length = (Nat.digits 2 x).length →
    digitSum y = digitSum x → y ∈ A

lemma balanced_class_ap (m t l : ℕ) (hmt : m < t) (hfit : t + m ≤ l) :
    ∃ a : ℕ, ∀ i < 2 ^ m,
      digitSum (a + i * (2 ^ m - 1)) = t ∧
        (Nat.digits 2 (a + i * (2 ^ m - 1))).length = l := by
  let R := List.replicate (t - m - 1) 1 ++ List.replicate (l - t - m) 0 ++ [1]
  have hR : ∀ x ∈ R, x < 2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have hx' := (List.mem_replicate.mp hx).2
        omega
      · have hx' := (List.mem_replicate.mp hx).2
        omega
    · simp only [List.mem_singleton] at hx
      omega
  have hRne : R ≠ [] := by simp [R]
  have hRlast : R.getLast hRne ≠ 0 := by simp [R]
  have hRsum : m + R.sum = t := by
    simp only [R, List.sum_append_nat, List.sum_replicate, List.sum_cons, List.sum_nil,
      nsmul_eq_mul, Nat.cast_id, mul_one, mul_zero, add_zero]
    omega
  have hRlen : 2 * m + R.length = l := by
    simp only [R, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  refine ⟨(2 ^ m - 1) + 2 ^ (2 * m) * Nat.ofDigits 2 R, fun i hi ↦ ?_⟩
  have hp := prefix_progression m R hR hRne hRlast hi
  exact ⟨hp.1.trans hRsum, hp.2.trans hRlen⟩

/-- Reciprocal divergence forces every finite AP length for binary-symmetric sets. -/
theorem binary_symmetric_contains_ap {A : Set ℕ} (hA : BinarySymmetric A)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (k : ℕ) :
    ∃ S ⊆ A, S.IsAPOfLength k := by
  obtain ⟨n, hn, hones, hzeros⟩ := divergent_many_zeros_and_ones hs (k + 1)
  let m := k + 1
  let t := digitSum n
  let l := (Nat.digits 2 n).length
  have hmt : m < t := hones
  have hfit : t + m ≤ l := by
    dsimp [digitZeros] at hzeros
    dsimp [t, m, l]
    omega
  obtain ⟨a, hterms⟩ := balanced_class_ap m t l hmt hfit
  let d := 2 ^ m - 1
  have hpow : k + 1 < 2 ^ m := Nat.lt_two_pow_self
  have hd : 0 < d := by dsimp [d]; omega
  let g : ℕ → ℕ := fun i ↦ a + i * d
  have hgi : Function.Injective g := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  refine ⟨g '' Set.Iio k, ?_, a, d, ?_, ?_⟩
  · rintro x ⟨i, hi, rfl⟩
    have hik : i < k := hi
    have hp := hterms i (by omega : i < 2 ^ m)
    exact hA n hn (g i) hp.2 hp.1
  · change (g '' Set.Iio k).encard = (k : ℕ∞)
    rw [hgi.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [g]

/-- The exact original conclusion under the additional binary-symmetry assumption. -/
theorem binary_symmetric_case {A : Set ℕ} (hA : BinarySymmetric A)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply Filter.frequently_atTop.mpr
  intro k
  exact ⟨k, le_rfl, binary_symmetric_contains_ap hA hs k⟩

/-- In this special case one can fix the step `2^m-1` and find arbitrarily far-out
APs of length `2^m`, a stronger conclusion than the original conjecture. -/
theorem binary_symmetric_fixed_step {A : Set ℕ} (hA : BinarySymmetric A)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (m N : ℕ) :
    ∃ a : ℕ, N ≤ a ∧ ∀ i < 2 ^ m, a + i * (2 ^ m - 1) ∈ A := by
  obtain ⟨n, hn, hones, hzeros⟩ := divergent_many_zeros_and_ones hs (N + m)
  let t := digitSum n
  let l := (Nat.digits 2 n).length
  have hmt : m < t := by dsimp [t]; omega
  have hfit : t + m ≤ l := by
    dsimp [digitZeros] at hzeros
    dsimp [t, l]
    omega
  obtain ⟨a, hterms⟩ := balanced_class_ap m t l hmt hfit
  have hz := hterms 0 (by positivity : 0 < 2 ^ m)
  simp only [zero_mul, add_zero] at hz
  have hlen : (Nat.digits 2 a).length ≤ a :=
    (Nat.digits_length_le_iff one_lt_two a).mpr Nat.lt_two_pow_self
  rw [hz.2] at hlen
  refine ⟨a, ?_, fun i hi ↦ ?_⟩
  · dsimp [t] at hfit
    omega
  · exact hA n hn _ (hterms i hi).2 (hterms i hi).1

theorem binary_symmetric_infinite_adjacent_pairs {A : Set ℕ} (hA : BinarySymmetric A)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    {x : ℕ | x ∈ A ∧ x + 1 ∈ A}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨a, ha, hterms⟩ := binary_symmetric_fixed_step hA hs 1 (N + 1)
  refine ⟨a, ⟨?_, ?_⟩, by omega⟩
  · simpa using hterms 0 (by norm_num)
  · simpa using hterms 1 (by norm_num)

/-- A set with only finitely many adjacent pairs has no divergent binary-symmetric
subset. Thus the positive special case cannot be reached by unrestricted
reciprocal-divergence-preserving subset extraction. -/
theorem symmetric_subset_summable_of_finite_adjacent_pairs {A B : Set ℕ}
    (hA : {x : ℕ | x ∈ A ∧ x + 1 ∈ A}.Finite) (hBA : B ⊆ A)
    (hB : BinarySymmetric B) : Summable (fun b : B ↦ 1 / (b : ℝ)) := by
  by_contra hs
  apply binary_symmetric_infinite_adjacent_pairs hB hs
  exact hA.subset (fun x hx ↦ ⟨hBA hx.1, hBA hx.2⟩)

#print axioms symmetric_subset_summable_of_finite_adjacent_pairs
#print axioms binary_symmetric_fixed_step
#print axioms binary_symmetric_case
#print axioms divergent_many_zeros_and_ones
#print axioms prefix_progression
#print axioms summable_of_bounded_digitZeros
#print axioms digitSum_invariant_case
#print axioms summable_of_bounded_digitSum
#print axioms constant_digitSum_progression
#print axioms weighted_nat_sum
#print axioms complement_value

end Erdos3BinarySymmetryCase
