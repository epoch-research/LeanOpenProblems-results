import FormalConjecturesUtil

/-!
A uniform obstruction to digit-sum based constructions. This is not a
settlement of the unrestricted positive-density cube-Sidon conjecture.
-/

namespace Erdos1206.DigitSumObstruction

private lemma complement_ofDigits {b : ℕ} (hb : 1 < b) (L : List ℕ)
    (hL : ∀ x ∈ L, x < b) :
    Nat.ofDigits b (L.map (fun x => b - 1 - x)) + Nat.ofDigits b L + 1 = b ^ L.length := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons x L ih =>
    have hx := hL x (by simp)
    have ht := ih (fun y hy => hL y (by simp [hy]))
    have hc : b - 1 - x + x + 1 = b := by omega
    simp only [List.map_cons, Nat.ofDigits, List.length_cons, pow_succ]
    nlinarith

private lemma complement_sum {b : ℕ} (L : List ℕ)
    (hL : ∀ x ∈ L, x < b) :
    (L.map (fun x => b - 1 - x)).sum + L.sum = (b - 1) * L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := hL x (by simp)
    have ht := ih (fun y hy => hL y (by simp [hy]))
    have hc : b - 1 - x + x = b - 1 := by omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- Multiplication by a block of maximal digits produces constant digit sum,
provided the multiplier fits in the block. -/
theorem digit_sum_mul_pow_sub_one {b k m : ℕ} (hb : 1 < b)
    (hm : 0 < m) (hmb : m ≤ b ^ k) :
    (b.digits (m * (b ^ k - 1))).sum = (b - 1) * k := by
  let L := Nat.digitsAppend b k (m - 1)
  let C := L.map (fun x => b - 1 - x)
  have hlen : L.length = k := Nat.length_digitsAppend hb k (by omega)
  have hL : ∀ x ∈ L, x < b := fun x hx => Nat.lt_of_mem_digitsAppend hb k x hx
  have hC : ∀ x ∈ C, x < b := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := hL y hy
    omega
  have hCL : ∀ x ∈ C ++ L, x < b := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hC x) (hL x)
  have hvalue : Nat.ofDigits b L = m - 1 := by
    simp [L, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hcvalue : Nat.ofDigits b C + m = b ^ k := by
    have := complement_ofDigits hb L hL
    rw [hlen, hvalue] at this
    change Nat.ofDigits b C + (m - 1) + 1 = b ^ k at this
    omega
  have hval : Nat.ofDigits b (C ++ L) = m * (b ^ k - 1) := by
    rw [Nat.ofDigits_append, List.length_map, hlen, hvalue]
    have hm' : m - 1 + 1 = m := by omega
    have hp : b ^ k - 1 + 1 = b ^ k := by have := Nat.one_le_pow k b (by omega); omega
    nlinarith
  rw [← hval]
  rw [Nat.sum_digits_ofDigits_eq_sum hb (l := (C ++ L).length) ⟨rfl, hCL⟩,
    List.sum_append]
  simpa [C, hlen] using complement_sum L hL

/-- Every sufficiently large digit-sum fiber contains a homothetic copy of
`1,9,10,12`, and hence cannot have Sidon cubes. -/
theorem digit_sum_fiber_not_cube_sidon {b k : ℕ} (hb : 1 < b) (hk : 12 ≤ b ^ k) :
    ¬ IsSidon ((fun n : ℕ => n ^ 3) '' {n | (b.digits n).sum = (b - 1) * k}) := by
  intro hs
  let q := b ^ k - 1
  have hq : 0 < q := by dsimp [q]; omega
  have hm (m : ℕ) (hm0 : 0 < m) (hm12 : m ≤ 12) :
      m * q ∈ {n : ℕ | (b.digits n).sum = (b - 1) * k} :=
    digit_sum_mul_pow_sub_one hb hm0 (hm12.trans hk)
  have he : (1 * q)^3 + (12 * q)^3 = (9 * q)^3 + (10 * q)^3 := by ring
  have hh := hs _ ⟨1 * q, hm 1 (by omega) (by omega), rfl⟩
    _ ⟨9 * q, hm 9 (by omega) (by omega), rfl⟩
    _ ⟨12 * q, hm 12 (by omega) (by omega), rfl⟩
    _ ⟨10 * q, hm 10 (by omega) (by omega), rfl⟩ he
  have h19 : (1 * q)^3 < (9 * q)^3 := Nat.pow_lt_pow_left (by omega) (by decide)
  have h110 : (1 * q)^3 < (10 * q)^3 := Nat.pow_lt_pow_left (by omega) (by decide)
  dsimp only at hh
  rcases hh with hh | hh <;> omega

/-- No coloring determined only by the digit sum can make every color class
cube-Sidon, regardless of the number of colors. -/
theorem no_digit_sum_cube_coloring {ι : Type*} (f : ℕ → ι) {b : ℕ} (hb : 1 < b) :
    ¬ (∀ i, IsSidon ((fun n : ℕ => n ^ 3) '' {n | f (b.digits n).sum = i})) := by
  intro h
  have hk : 12 ≤ b ^ 4 := by
    have hh := Nat.pow_le_pow_left (show 2 ≤ b by omega) 4
    norm_num at hh
    omega
  apply digit_sum_fiber_not_cube_sidon hb hk
  apply Set.IsSidon.subset (h (f ((b - 1) * 4)))
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, congrArg f hn, rfl⟩

open Finset Filter
open scoped Classical Topology

private lemma list_digit_weight_sum {b : ℕ} (hb : 1 < b) (r : ℝ) (k : ℕ) :
    (∑ L ∈ List.fixedLengthDigits hb k, r ^ L.sum) =
      (∑ d ∈ range b, r ^ d) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.fixedLengthDigits_succ_eq_disjiUnion, sum_disjiUnion]
    simp only [List.consFixedLengthDigits, List.cons.injEq, true_and, implies_true,
      Set.injOn_of_eq_iff_eq, sum_image, List.sum_cons, pow_add]
    simp_rw [← mul_sum, ih]
    rw [← sum_mul, pow_succ]
    ring

/-- The digit-sum generating function in a complete radix block. -/
theorem digit_weight_sum {b : ℕ} (hb : 1 < b) (r : ℝ) (k : ℕ) :
    (∑ n ∈ range (b ^ k), r ^ (b.digits n).sum) =
      (∑ d ∈ range b, r ^ d) ^ k := by
  rw [← list_digit_weight_sum hb r k]
  refine (sum_nbij (Nat.ofDigits b) (by exact (Nat.bijOn_ofDigits' hb k).1)
    (Nat.bijOn_ofDigits' hb k).2.1 (Nat.bijOn_ofDigits' hb k).2.2 ?_).symm
  intro L hL
  rw [Nat.sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)]

private lemma bounded_binary_digit_sum_count (K k : ℕ) :
    (({n : ℕ | (Nat.digits 2 n).sum ≤ K} ∩ Set.Iio (2 ^ k)).ncard : ℝ) ≤
      2 ^ K * (3 / 2 : ℝ) ^ k := by
  let F := (range (2 ^ k)).filter (fun n => (Nat.digits 2 n).sum ≤ K)
  have hF : (F : Set ℕ) = {n : ℕ | (Nat.digits 2 n).sum ≤ K} ∩ Set.Iio (2 ^ k) := by
    ext n
    simp [F, and_comm]
  rw [← hF, Set.ncard_coe_finset]
  calc
    (F.card : ℝ) = ∑ n ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ F, (2 : ℝ)^K * (1 / 2 : ℝ)^(Nat.digits 2 n).sum := by
      apply sum_le_sum
      intro n hn
      have hK := (mem_filter.mp hn).2
      have hp : (1 / 2 : ℝ)^K ≤ (1 / 2 : ℝ)^(Nat.digits 2 n).sum :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
      have hm := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2^K)
      have he : (2 : ℝ)^K * (1 / 2 : ℝ)^K = 1 := by rw [← mul_pow]; norm_num
      rwa [he] at hm
    _ ≤ ∑ n ∈ range (2 ^ k), (2 : ℝ)^K * (1 / 2 : ℝ)^(Nat.digits 2 n).sum := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
    _ = 2 ^ K * (3 / 2 : ℝ) ^ k := by
      rw [← mul_sum, digit_weight_sum (by decide : 1 < 2)]
      norm_num [sum_range_succ]

/-- Every set on which the binary digit sum is bounded has zero lower density. -/
theorem lowerDensity_zero_of_bounded_binary_digit_sum {A : Set ℕ} {K : ℕ}
    (hA : ∀ n ∈ A, (Nat.digits 2 n).sum ≤ K) : A.lowerDensity = 0 := by
  apply le_antisymm _ (Set.lowerDensity_nonneg A)
  by_contra! hpos
  have hbound (k : ℕ) : A.partialDensity Set.univ (2 ^ k) ≤
      (2 : ℝ)^K * (3 / 4 : ℝ)^k := by
    have hcard : ((A ∩ Set.Iio (2^k)).ncard : ℝ) ≤
        (2 : ℝ)^K * (3 / 2 : ℝ)^k := by
      apply le_trans _ (bounded_binary_digit_sum_count K k)
      exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ hA)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ k : ℕ))).mpr
    push_cast
    convert hcard using 1
    rw [mul_assoc, ← mul_pow]
    norm_num
  have hlarge : ∀ᶠ n : ℕ in atTop, A.lowerDensity / 2 < A.partialDensity Set.univ n :=
    eventually_lt_of_lt_liminf (half_lt_self hpos)
      (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  have hpowers : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))
  have hsmall : ∀ᶠ k : ℕ in atTop, (2 : ℝ)^K * (3 / 4 : ℝ)^k < A.lowerDensity / 2 := by
    have hlim : Tendsto (fun k : ℕ => (2 : ℝ)^K * (3 / 4 : ℝ)^k) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4)
          (by norm_num : (3/4 : ℝ) < 1)) :
        Tendsto (fun k : ℕ => (2 : ℝ)^K * (3 / 4 : ℝ)^k) atTop (𝓝 ((2 : ℝ)^K * 0)))
    exact hlim.eventually (gt_mem_nhds (half_pos hpos))
  obtain ⟨k, hk, hk'⟩ := ((hpowers.eventually hlarge).and hsmall).exists
  exact (not_lt_of_ge (hbound k)) (hk'.trans hk)

/-- Membership determined only by binary digit sum cannot give a cube-Sidon
set of positive lower density. This is a restriction on the construction,
not on arbitrary sets of roots. -/
theorem binary_digit_sum_determined_cube_sidon_lowerDensity_zero {A : Set ℕ}
    (hmem : ∀ m n : ℕ, (Nat.digits 2 m).sum = (Nat.digits 2 n).sum →
      (m ∈ A ↔ n ∈ A))
    (hs : IsSidon ((fun n : ℕ => n ^ 3) '' A)) : A.lowerDensity = 0 := by
  apply lowerDensity_zero_of_bounded_binary_digit_sum (K := 3)
  intro n hn
  by_contra! hK
  let k := (Nat.digits 2 n).sum
  have hk : 12 ≤ 2 ^ k := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 4 ≤ k by omega)
    norm_num at hpow
    omega
  apply digit_sum_fiber_not_cube_sidon (by decide : 1 < 2) hk
  apply Set.IsSidon.subset hs
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨m, ?_, rfl⟩
  exact (hmem m n (by simpa [k] using hm)).mpr hn

#print axioms digit_weight_sum
#print axioms lowerDensity_zero_of_bounded_binary_digit_sum
#print axioms binary_digit_sum_determined_cube_sidon_lowerDensity_zero

#print axioms digit_sum_mul_pow_sub_one
#print axioms digit_sum_fiber_not_cube_sidon
#print axioms no_digit_sum_cube_coloring

end Erdos1206.DigitSumObstruction
