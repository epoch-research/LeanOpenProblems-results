import FormalConjecturesUtil

/-! Verified auxiliary results. These do not settle `erdos_1206.parts.ii`. -/

namespace Erdos1206

lemma scaled_taxicab_obstruction {A : Set ℕ}
    (hA : IsSidon ((fun a : ℕ => a ^ 3) '' A))
    {n : ℕ} (hn : 0 < n) :
    ¬ (n ∈ A ∧ 9 * n ∈ A ∧ 10 * n ∈ A ∧ 12 * n ∈ A) := by
  rintro ⟨h1, h9, h10, h12⟩
  have heq : n ^ 3 + (12 * n) ^ 3 = (9 * n) ^ 3 + (10 * n) ^ 3 := by ring
  have h := hA (n ^ 3) ⟨n, h1, rfl⟩ ((9 * n) ^ 3) ⟨9 * n, h9, rfl⟩
    ((12 * n) ^ 3) ⟨12 * n, h12, rfl⟩ ((10 * n) ^ 3) ⟨10 * n, h10, rfl⟩ heq
  have hn3 : 0 < n ^ 3 := pow_pos hn _
  rcases h with h | h
  · have h' := h.1
    simp only [mul_pow] at h'
    norm_num at h'
    nlinarith
  · have h' := h.1
    simp only [mul_pow] at h'
    norm_num at h'
    nlinarith

lemma all_cubes_not_sidon : ¬ IsSidon (Set.range (fun a : ℕ => a ^ 3)) := by
  intro h
  have h' : IsSidon ((fun a : ℕ => a ^ 3) '' (Set.univ : Set ℕ)) := by
    simpa using h
  exact scaled_taxicab_obstruction h' (n := 1) (by norm_num) (by simp)

/-- An explicit nontrivial equality of two cube sums in every residue class `1 mod m`. -/
lemma polynomial_taxicab_identity (m : ℕ) :
    let a := 1296 * m ^ 5 + 864 * m ^ 4 + 312 * m ^ 3 + 84 * m ^ 2 + 13 * m + 1
    let v := 6 * m + 1
    let s := 108 * m ^ 3 + 60 * m ^ 2 + 9 * m
    let d := v * a + 4 * m * v * s
    a ^ 3 + (d + 4 * m * v) ^ 3 = (a + 4 * m * v ^ 3) ^ 3 + d ^ 3 := by
  dsimp
  ring

lemma no_full_positive_residue_class {A : Set ℕ}
    (hA : IsSidon ((fun a : ℕ => a ^ 3) '' A))
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    ¬ (∀ k : ℕ, r + m * k ∈ A) := by
  intro h
  let a := 1296 * m ^ 5 + 864 * m ^ 4 + 312 * m ^ 3 + 84 * m ^ 2 + 13 * m + 1
  let v := 6 * m + 1
  let s := 108 * m ^ 3 + 60 * m ^ 2 + 9 * m
  let d := v * a + 4 * m * v * s
  have ha : r * a ∈ A := by
    convert h (r * (1296 * m ^ 4 + 864 * m ^ 3 + 312 * m ^ 2 + 84 * m + 13)) using 1 <;>
      dsimp [a] <;> ring
  have hb : r * (d + 4 * m * v) ∈ A := by
    convert h (r * (7776 * m ^ 5 + 9072 * m ^ 4 + 4608 * m ^ 3 +
      1272 * m ^ 2 + 222 * m + 23)) using 1 <;> dsimp [d, v, a, s] <;> ring
  have hc : r * (a + 4 * m * v ^ 3) ∈ A := by
    convert h (r * (1296 * m ^ 4 + 1728 * m ^ 3 + 744 * m ^ 2 + 156 * m + 17))
      using 1 <;> dsimp [a, v] <;> ring
  have hd : r * d ∈ A := by
    convert h (r * (7776 * m ^ 5 + 9072 * m ^ 4 + 4608 * m ^ 3 +
      1272 * m ^ 2 + 198 * m + 19)) using 1 <;> dsimp [d, v, a, s] <;> ring
  have heq : (r * a) ^ 3 + (r * (d + 4 * m * v)) ^ 3 =
      (r * (a + 4 * m * v ^ 3)) ^ 3 + (r * d) ^ 3 := by
    simpa only [mul_pow, ← mul_add] using
      congrArg (fun n : ℕ => r ^ 3 * n) (polynomial_taxicab_identity m)
  have hsid := hA _ ⟨r * a, ha, rfl⟩ _ ⟨r * (a + 4 * m * v ^ 3), hc, rfl⟩
    _ ⟨r * (d + 4 * m * v), hb, rfl⟩ _ ⟨r * d, hd, rfl⟩ heq
  have hv : 0 < v := by dsimp [v]; omega
  have hca : r * a < r * (a + 4 * m * v ^ 3) := by
    have hp : 0 < 4 * m * v ^ 3 := by positivity
    exact Nat.mul_lt_mul_of_pos_left (by omega) hr
  have hda : r * a < r * d := by
    have ha0 : 0 < a := by dsimp [a]; omega
    have hv1 : 1 < v := by dsimp [v]; omega
    have hlt : a < v * a := by nlinarith
    exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le hlt (Nat.le_add_right _ _)) hr
  rcases hsid with hsid | hsid
  · exact (ne_of_lt (Nat.pow_lt_pow_left hca (by decide : 3 ≠ 0))) hsid.1
  · exact (ne_of_lt (Nat.pow_lt_pow_left hda (by decide : 3 ≠ 0))) hsid.1

lemma taxicab_complement_count {A : Set ℕ}
    (hA : IsSidon ((fun a : ℕ => a ^ 3) '' A)) (N : ℕ) :
    N ≤ (Set.Iio N \ A).ncard + (Set.Iio (9 * N) \ A).ncard +
      (Set.Iio (10 * N) \ A).ncard + (Set.Iio (12 * N) \ A).ncard + 1 := by
  let S : ℕ → Set ℕ := fun k => {n | n < N ∧ k * n ∉ A}
  have hS (k : ℕ) : (S k).Finite := (Set.finite_Iio N).subset (fun _ h => h.1)
  have hincl : Set.Iio N \ {0} ⊆ ((S 1 ∪ S 9) ∪ S 10) ∪ S 12 := by
    intro n hn
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by simpa using hn.2)
    have hnN : n < N := hn.1
    have hnot := scaled_taxicab_obstruction hA hn0
    simp only [Set.mem_union, S, Set.mem_setOf_eq, one_mul]
    tauto
  have hcard := Set.ncard_le_ncard hincl (((hS 1).union (hS 9)).union (hS 10) |>.union (hS 12))
  have hu1 := Set.ncard_union_le (S 1) (S 9)
  have hu2 := Set.ncard_union_le (S 1 ∪ S 9) (S 10)
  have hu3 := Set.ncard_union_le ((S 1 ∪ S 9) ∪ S 10) (S 12)
  have hb (k : ℕ) (hk : 0 < k) : (S k).ncard ≤ (Set.Iio (k * N) \ A).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun n => k * n)
    · intro n hn
      exact ⟨Nat.mul_lt_mul_of_pos_left hn.1 hk, hn.2⟩
    · exact (mul_right_injective₀ hk.ne').injOn
  have h0 : (Set.Iio N \ {0}).ncard + 1 ≥ N := by
    by_cases hn : N = 0
    · simp [hn]
    · rw [Set.ncard_diff_singleton_of_mem (show 0 ∈ Set.Iio N from Nat.pos_of_ne_zero hn)]
      simp only [Nat.ncard_Iio]
      omega
  have hb1 := hb 1 (by decide)
  have hb9 := hb 9 (by decide)
  have hb10 := hb 10 (by decide)
  have hb12 := hb 12 (by decide)
  simp only [one_mul] at hb1
  omega

lemma complement_count_add (A : Set ℕ) (N : ℕ) :
    (Set.Iio N \ A).ncard + (A ∩ Set.Iio N).ncard = N := by
  simpa [Set.diff_inter, Nat.ncard_Iio] using
    Set.ncard_diff_add_ncard_of_subset (s := A ∩ Set.Iio N) (t := Set.Iio N)
      Set.inter_subset_right

lemma cube_sidon_lowerDensity_le {A : Set ℕ}
    (hA : IsSidon ((fun a : ℕ => a ^ 3) '' A)) :
    A.lowerDensity ≤ 31 / 32 := by
  by_contra! h
  obtain ⟨c, hc, hcA⟩ := exists_between h
  have hevent : ∀ᶠ N : ℕ in Filter.atTop, c < A.partialDensity Set.univ N :=
    Filter.eventually_lt_of_lt_liminf hcA
      (Filter.isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hevent
  have heps : 0 < 32 * c - 31 := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (32 * c - 31))
  let N := max B M + 1
  have hBN : B ≤ N := by dsimp [N]; omega
  have hMN : M ≤ N := by dsimp [N]; omega
  have hN : 0 < N := by dsimp [N]; omega
  have hlarge : 1 < (32 * c - 31) * (N : ℝ) := by
    have hlt : 1 / (32 * c - 31) < (N : ℝ) := hM.trans_le (by exact_mod_cast hMN)
    have hh := (div_lt_iff₀ heps).mp hlt
    nlinarith
  have hcomp (k : ℕ) (hk : 0 < k) :
      ((Set.Iio (k * N) \ A).ncard : ℝ) < (1 - c) * (k * N : ℕ) := by
    have hkn : 0 < k * N := Nat.mul_pos hk hN
    have hkN : B ≤ k * N := hBN.trans (Nat.le_mul_of_pos_left N hk)
    have hp := hB (k * N) hkN
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hp
    have hp' := (lt_div_iff₀ (show (0 : ℝ) < (k * N : ℕ) by exact_mod_cast hkn)).mp hp
    have hc' : ((Set.Iio (k * N) \ A).ncard : ℝ) +
        ((A ∩ Set.Iio (k * N)).ncard : ℝ) = (k * N : ℕ) := by
      exact_mod_cast complement_count_add A (k * N)
    nlinarith
  have hc1 := hcomp 1 (by decide)
  have hc9 := hcomp 9 (by decide)
  have hc10 := hcomp 10 (by decide)
  have hc12 := hcomp 12 (by decide)
  simp only [one_mul, Nat.cast_mul, Nat.cast_ofNat] at hc1 hc9 hc10 hc12
  have hcount : (N : ℝ) ≤ (Set.Iio N \ A).ncard + (Set.Iio (9 * N) \ A).ncard +
      (Set.Iio (10 * N) \ A).ncard + (Set.Iio (12 * N) \ A).ncard + 1 := by
    exact_mod_cast taxicab_complement_count hA N
  nlinarith

end Erdos1206
