import FormalConjectures.Util.ProblemImports

open Int Set Filter Topology

/--
A182510: $a(0)=0, a(1)=1, a(n)=(a(n-1) \text{ XOR } n) - a(n-2)$, where $\text{XOR}$ is the bitwise exclusive-or operator.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

theorem testBit_zero (n : ℤ) : testBit n 0 = bodd n := by
  have h := testBit_bit_zero (bodd n) (div2 n)
  rw [bit_decomp] at h
  exact h

theorem bodd_xor (x y : ℤ) : Int.bodd (Int.xor x y) = Bool.xor (Int.bodd x) (Int.bodd y) := by
  rw [← testBit_zero (Int.xor x y)]
  rw [testBit_lxor]
  rw [testBit_zero x, testBit_zero y]

theorem bodd_sub (x y : ℤ) : bodd (x - y) = Bool.xor (bodd x) (bodd y) := by
  rw [sub_eq_add_neg, bodd_add, bodd_neg]

def p (n : ℕ) : Bool :=
  match n % 6 with
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => false
  | _ => false

theorem bodd_coe_nat (n : ℕ) : bodd (n : ℤ) = n.bodd := by rfl

theorem bodd_eq_bodd_mod_six (n : ℕ) : Nat.bodd n = Nat.bodd (n % 6) := by
  have h_div : n = 6 * (n / 6) + (n % 6) := (Nat.div_add_mod n 6).symm
  nth_rw 1 [h_div]
  rw [Nat.bodd_add, Nat.bodd_mul]
  simp

theorem bodd_add_six_mul (m k : ℕ) : Nat.bodd (6 * m + k) = Nat.bodd k := by
  rw [Nat.bodd_add, Nat.bodd_mul]
  simp

theorem add_six_mul_mod (m k : ℕ) : (6 * m + k) % 6 = k % 6 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem p_add_six_mul (m k : ℕ) : p (6 * m + k) = p k := by
  unfold p
  rw [add_six_mul_mod]

theorem add_six_mul_assoc (m a b : ℕ) : 6 * m + a + b = 6 * m + (a + b) := by omega

theorem a_bodd_and_next (n : ℕ) : bodd (a n) = p n ∧ bodd (a (n + 1)) = p (n + 1) := by
  induction n with
  | zero =>
    simp [a, p]
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨ih2, ?_⟩
    have h_coe : (n + 2 : ℤ) = ↑(n + 2) := by push_cast; rfl
    have h_a_succ2 : a (n + 2) = Int.xor (a (n + 1)) (n + 2 : ℤ) - a n := by rfl
    rw [h_a_succ2, h_coe, bodd_sub, bodd_xor, ih1, ih2, bodd_coe_nat (n + 2)]
    unfold p
    have h_mod : n % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 6
    all_goals
      have h_div : n = 6 * (n / 6) + (n % 6) := (Nat.div_add_mod n 6).symm
      rw [h] at h_div
      rw [h_div]
      repeat rw [add_six_mul_assoc]
      simp


theorem Nat.xor_le_add (m k : ℕ) : m ^^^ k ≤ m + k := by
  revert k
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k
    by_cases hm : m = 0
    · rw [hm]
      simp
    · rw [← Nat.bit_bodd_div2 m, ← Nat.bit_bodd_div2 k]
      rw [Nat.xor_bit]
      generalize h_mb : m.bodd = mb
      generalize h_kb : k.bodd = kb
      generalize h_md : m.div2 = md
      generalize h_kd : k.div2 = kd
      have h_md_lt : md < m := by
        rw [← h_md, Nat.div2_val]
        omega
      have h_ih := ih md h_md_lt kd
      cases mb <;> cases kb <;> simp [Nat.bit_false_apply, Nat.bit_true_apply] <;> linarith

theorem Int.xor_le_add (x : ℤ) (k : ℕ) : Int.xor x (k : ℤ) ≤ x + (k : ℤ) := by
  cases x with
  | ofNat m =>
    simp [Int.xor]
    have h := Nat.xor_le_add m k
    omega
  | negSucc m =>
    simp [Int.xor]
    have h_le := Nat.xor_le_add (m ^^^ k) k
    rw [Nat.xor_xor_cancel_right m k] at h_le
    omega

theorem a_add_a_add_three (n : ℕ) :
    a (n + 3) + a n = (Int.xor (a (n + 1)) (n + 2 : ℤ) - a (n + 1)) + (Int.xor (a (n + 2)) (n + 3 : ℤ) - a (n + 2)) := by
  have h2 : a (n + 2) = Int.xor (a (n + 1)) (n + 2 : ℤ) - a n := by rfl
  have h3 : a (n + 3) = Int.xor (a (n + 2)) (n + 3 : ℤ) - a (n + 1) := by rfl
  omega

theorem a_add_a_add_three_le (n : ℕ) : a (n + 3) + a n ≤ 2 * n + 5 := by
  rw [a_add_a_add_three]
  have h1 := Int.xor_le_add (a (n + 1)) (n + 2)
  have h2 := Int.xor_le_add (a (n + 2)) (n + 3)
  push_cast at *
  omega


theorem density_le_of_bounded_diff {S T : Set ℕ} {d_S d_T : ℝ} (hS : S.HasDensity d_S) (hT : T.HasDensity d_T)
    (C : ℝ) (h_bound : ∀ b : ℕ, ((S ∩ Iio b).ncard : ℝ) ≤ ((T ∩ Iio b).ncard : ℝ) + C) :
    d_S ≤ d_T := by
  have h_partial (U : Set ℕ) (b : ℕ) : U.partialDensity Set.univ b = ((U ∩ Iio b).ncard : ℝ) / b := by
    unfold Set.partialDensity
    rw [Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have h_lim : Tendsto (fun b : ℕ => T.partialDensity Set.univ b + C / b) atTop (𝓝 d_T) := by
    have h_add := Tendsto.add hT (tendsto_const_div_atTop_nhds_zero_nat C)
    rw [add_zero] at h_add
    exact h_add
  apply le_of_tendsto_of_tendsto hS h_lim
  filter_upwards [eventually_ge_atTop 1] with b hb
  rw [h_partial S b, h_partial T b]
  have h_b_pos : (b : ℝ) > 0 := Nat.cast_pos.mpr hb
  have h_ne : (b : ℝ) ≠ 0 := ne_of_gt h_b_pos
  rw [div_le_iff₀ h_b_pos]
  rw [add_mul, div_mul_cancel₀ _ h_ne, div_mul_cancel₀ _ h_ne]
  exact h_bound b

theorem test_three (b : ℕ) : (Iio b \ Iio (b - 3)).ncard ≤ 3 := by
  have h_sub : Iio (b - 3) ⊆ Iio b := by
    rintro n (hn : n < b - 3)
    exact hn.trans_le (Nat.sub_le b 3)
  rw [Set.ncard_diff h_sub (Set.finite_Iio (b - 3))]
  rw [Nat.ncard_Iio, Nat.ncard_Iio]
  omega

def f (n : ℕ) : ℕ :=
  if n % 6 < 3 then n + 3 else n - 3

theorem f_f (n : ℕ) : f (f n) = n := by
  unfold f
  split_ifs <;> omega

theorem f_inj : Function.Injective f := by
  intro x y h
  have h2 := congr_arg f h
  rw [f_f, f_f] at h2
  exact h2

def E : Set ℕ := {n : ℕ | a n > 0 ∧ a (f n) ≥ 0}

theorem E_sub : E ⊆ {n : ℕ | 0 < a n ∧ a n ≤ 2 * n + 5} := by
  rintro n ⟨hn1, hn2⟩
  refine ⟨hn1, ?_⟩
  unfold f at hn2
  split_ifs at hn2 with h
  · have h_le := a_add_a_add_three_le n
    omega
  · have h_ge : n ≥ 3 := by
      by_contra h_lt
      have h_mod : n % 6 = n := Nat.mod_eq_of_lt (by omega)
      have h_cond : n % 6 < 3 := by omega
      exact h h_cond
    have h_sub_add : n - 3 + 3 = n := Nat.sub_add_cancel h_ge
    have h_le := a_add_a_add_three_le (n - 3)
    rw [h_sub_add] at h_le
    omega

theorem test_three_sub (b : ℕ) : {n : ℕ | n < b ∧ b ≤ f n} ⊆ Iio b \ Iio (b - 3) := by
  rintro n ⟨hn1, hn2⟩
  refine ⟨hn1, ?_⟩
  rintro (hn3 : n < b - 3)
  unfold f at hn2
  split_ifs at hn2 with h
  · omega
  · omega

theorem h_bound_helper (b : ℕ) :
    (({n : ℕ | a n > 0 ∧ n ∉ E} ∩ Iio b).ncard : ℝ) ≤ (({n : ℕ | a n < 0} ∩ Iio b).ncard : ℝ) + 3 := by
  let S_diff := {n : ℕ | a n > 0 ∧ n ∉ E}
  let T := {n : ℕ | a n < 0}
  let A := S_diff ∩ Iio b
  let A_paired := {n ∈ A | f n < b}
  let A_unpaired := {n ∈ A | f n ≥ b}
  have h_union : A = A_paired ∪ A_unpaired := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_union, mem_sep_iff]
    tauto
  have h_disj : Disjoint A_paired A_unpaired := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    omega
  have h_A_fin : A.Finite := (finite_Iio b).inter_of_right _
  have h_paired_fin : A_paired.Finite := h_A_fin.subset (by intro x; simp; tauto)
  have h_unpaired_fin : A_unpaired.Finite := h_A_fin.subset (by intro x; simp; tauto)
  have h_sum : (A.ncard : ℝ) = (A_paired.ncard : ℝ) + (A_unpaired.ncard : ℝ) := by
    rw [h_union]
    have := ncard_union_eq h_disj h_paired_fin h_unpaired_fin
    push_cast
    exact this
  have h_unpaired_sub : A_unpaired ⊆ {n : ℕ | n < b ∧ b ≤ f n} := by
    rintro x ⟨⟨⟨_, _⟩, h1⟩, h2⟩
    exact ⟨h1, h2⟩
  have h_unpaired_sub2 : A_unpaired ⊆ Iio b \ Iio (b - 3) := h_unpaired_sub.trans (test_three_sub b)
  have h_unpaired_le : (A_unpaired.ncard : ℝ) ≤ 3 := by
    have h_le := ncard_le_ncard h_unpaired_sub2 (finite_Iio b |>.diff _)
    have h3 := test_three b
    omega
  have h_paired_maps : MapsTo f A_paired (T ∩ Iio b) := by
    rintro x ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩
    simp only [mem_inter_iff, mem_setOf_eq]
    refine ⟨?_, hx4⟩
    by_contra hc
    have hc2 : a (f x) ≥ 0 := by omega
    have h_in_E : x ∈ E := ⟨hx1, hc2⟩
    exact hx2 h_in_E
  have h_inj_on : InjOn f A_paired := f_inj.injOn _
  have h_paired_le : (A_paired.ncard : ℝ) ≤ ((T ∩ Iio b).ncard : ℝ) := by
    have h_le := ncard_le_ncard_of_injOn f h_paired_maps h_inj_on (finite_Iio b |>.inter_of_right _)
    exact_mod_cast h_le
  omega

/-- oeis_a182510_conjecture_density.disproof: A182510 Conjectures: more positive terms than negative.
This is formalized as the negation of the original conjecture.
-/
theorem oeis_a182510_conjecture_density.disproof :
  ¬ ∃ d_pos d_neg : ℝ,
    ({n : ℕ | a n > 0}).HasDensity d_pos ∧
    ({n : ℕ | a n < 0}).HasDensity d_neg ∧
    d_pos > d_neg :=
by
  rintro ⟨d_pos, d_neg, hpos, hneg, hgt⟩
  have h_E_finite : E.Finite := by
    sorry
  have h_bound : ∀ b : ℕ, (({n : ℕ | a n > 0} ∩ Iio b).ncard : ℝ) ≤ (({n : ℕ | a n < 0} ∩ Iio b).ncard : ℝ) + (3 + E.ncard : ℝ) := by
    intro b
    let S := {n : ℕ | a n > 0}
    let S_diff := {n : ℕ | a n > 0 ∧ n ∉ E}
    have h_sub : S ∩ Iio b ⊆ (S_diff ∩ Iio b) ∪ (E ∩ Iio b) := by
      rintro x ⟨hx, hb⟩
      by_cases hx_E : x ∈ E
      · right; exact ⟨hx_E, hb⟩
      · left; exact ⟨⟨hx, hx_E⟩, hb⟩
    have h_S_fin : (S ∩ Iio b).Finite := finite_Iio b |>.inter_of_right _
    have h_E_b_fin : (E ∩ Iio b).Finite := finite_Iio b |>.inter_of_right _
    have h_le : ((S ∩ Iio b).ncard : ℝ) ≤ ((S_diff ∩ Iio b).ncard : ℝ) + ((E ∩ Iio b).ncard : ℝ) := by
      have h1 := ncard_le_ncard h_sub (h_S_fin.subset (subset_union_left.trans (by intro x; simp; tauto)))
      have h2 := ncard_union_le (S_diff ∩ Iio b) (E ∩ Iio b)
      omega
    have h_helper := h_bound_helper b
    have h_E_le : ((E ∩ Iio b).ncard : ℝ) ≤ (E.ncard : ℝ) := by
      have h_le := ncard_le_ncard (inter_subset_left E (Iio b)) h_E_finite
      exact_mod_cast h_le
    omega
  have h_le : d_pos ≤ d_neg := density_le_of_bounded_diff hpos hneg (3 + E.ncard : ℝ) h_bound
  linarith
