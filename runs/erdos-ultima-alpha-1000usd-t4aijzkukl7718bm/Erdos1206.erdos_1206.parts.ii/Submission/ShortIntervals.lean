import FormalConjecturesUtil

/-!
An auxiliary interval bound: cubes of the integers in `[M,M+L]` are Sidon
when `L^2 ≤ 6*M + 9`. This does not construct a set of positive lower density.
-/

namespace Erdos1206

private lemma cube_mod_three (n : ℕ) : n ^ 3 % 3 = n % 3 := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [Nat.pow_mod, h]

private lemma cube_sum_lt_of_sum_gap_three (a b c d L : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hspread : (a - b) ^ 2 ≤ L ^ 2)
    (hsize : L ^ 2 ≤ 3 * (a + b) + 9)
    (hgap : a + b + 3 ≤ c + d) :
    a ^ 3 + b ^ 3 < c ^ 3 + d ^ 3 := by
  have hpow : (a + b + 3) ^ 3 ≤ (c + d) ^ 3 :=
    pow_le_pow_left₀ (by omega) hgap 3
  have hspread' := mul_le_mul_of_nonneg_left hspread
    (show (0 : ℤ) ≤ 3 * (a + b) by omega)
  have hsize' := mul_le_mul_of_nonneg_left hsize
    (show (0 : ℤ) ≤ 3 * (a + b) by omega)
  have hnonneg := mul_nonneg (show (0 : ℤ) ≤ 3 * (c + d) by omega)
    (sq_nonneg (c - d))
  nlinarith only [hpow, hspread', hsize', hnonneg]

lemma cubes_sidon_on_short_interval (L M : ℕ)
    (hsize : L ^ 2 ≤ 6 * M + 9) :
    IsSidon ((fun a : ℕ => a ^ 3) '' Set.Icc M (M + L)) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
  have hmod : (a + b) % 3 = (c + d) % 3 := by
    have hh := congrArg (fun n : ℕ => n % 3) heq
    simpa only [Nat.add_mod, cube_mod_three, Nat.mod_mod] using hh
  have hint (x y : ℕ) (hx : x ∈ Set.Icc M (M + L))
      (hy : y ∈ Set.Icc M (M + L)) :
      ((x : ℤ) - y) ^ 2 ≤ (L : ℤ) ^ 2 ∧
        (L : ℤ) ^ 2 ≤ 3 * ((x : ℤ) + y) + 9 := by
    have hx₁ : (M : ℤ) ≤ x := by exact_mod_cast hx.1
    have hy₁ : (M : ℤ) ≤ y := by exact_mod_cast hy.1
    have hx₂ : (x : ℤ) ≤ M + L := by exact_mod_cast hx.2
    have hy₂ : (y : ℤ) ≤ M + L := by exact_mod_cast hy.2
    have hsizeZ : (L : ℤ) ^ 2 ≤ 6 * M + 9 := by exact_mod_cast hsize
    have h₁ : 0 ≤ (L : ℤ) - ((x : ℤ) - y) := by omega
    have h₂ : 0 ≤ (L : ℤ) + ((x : ℤ) - y) := by omega
    constructor
    · nlinarith [mul_nonneg h₁ h₂]
    · omega
  have heqZ : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 + (d : ℤ) ^ 3 := by
    exact_mod_cast heq
  have hsum : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | he | hgt
    · have hgap : (a : ℤ) + b + 3 ≤ c + d := by omega
      obtain ⟨hspread, hsize'⟩ := hint a b ha hb
      have h := cube_sum_lt_of_sum_gap_three a b c d L
        (by omega) (by omega) hspread hsize' hgap
      omega
    · exact he
    · have hgap : (c : ℤ) + d + 3 ≤ a + b := by omega
      obtain ⟨hspread, hsize'⟩ := hint c d hc hd
      have h := cube_sum_lt_of_sum_gap_three c d a b L
        (by omega) (by omega) hspread hsize' hgap
      omega
  by_cases hzero : a + b = 0
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    simp [ha0, hb0, hc0, hd0]
  have hprod : a * b = c * d := by
    have hid : 3 * (a + b) * (a * b) + (a ^ 3 + b ^ 3) = (a + b) ^ 3 := by ring
    have hid' : 3 * (c + d) * (c * d) + (c ^ 3 + d ^ 3) = (c + d) ^ 3 := by ring
    rw [hsum, heq] at hid
    have hh : 3 * (c + d) * (a * b) = 3 * (c + d) * (c * d) :=
      Nat.add_right_cancel (hid.trans hid'.symm)
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * (c + d)) hh
  have hsumZ : (a : ℤ) + b = c + d := by exact_mod_cast hsum
  have hprodZ : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hprod
  have hfactor : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · have hac : a = c := by omega
    have hbd : b = d := by omega
    exact Or.inl ⟨congrArg (fun n : ℕ => n ^ 3) hac, congrArg (fun n : ℕ => n ^ 3) hbd⟩
  · have had : a = d := by omega
    have hbc : b = c := by omega
    exact Or.inr ⟨congrArg (fun n : ℕ => n ^ 3) had, congrArg (fun n : ℕ => n ^ 3) hbc⟩

end Erdos1206
