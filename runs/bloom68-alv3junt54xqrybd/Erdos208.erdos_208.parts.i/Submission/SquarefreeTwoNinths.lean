import Submission.SquarefreeTwoNinthsCount

/-!
# Unconditional O(N^(2/9)) squarefree gaps

The finite count is root-free: `N ≤ t⁹` implies at most `260 t²` witnesses.
Here the rounded ninth root gives `1040 N^(2/9)`. The survivor sieve then
proves the explicit natural criterion `64 ≤ H` and `16384⁹ N² ≤ H⁹`.
Rounding `16384 N^(2/9)` yields a uniform all-index gap bound with constant
`16385`, and Big-O for every exponent at least `2/9` (including equality).
This does not assert the original all-positive-exponent conjecture.
-/
namespace SquarefreeTwoNinths

open SquarefreeRoth
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- A natural ninth-power parameter for the finite count. -/
noncomputable def ninthParameter (N : ℕ) : ℕ := ⌈(N : ℝ)^(1/9 : ℝ)⌉₊

lemma twoNinths_pow_nine (N : ℕ) :
    ((N : ℝ)^(2/9 : ℝ))^9 = (N : ℝ)^2 := by
  calc
    ((N : ℝ)^(2/9 : ℝ))^9 = ((N : ℝ)^(2/9 : ℝ))^(9 : ℝ) :=
      (Real.rpow_natCast _ 9).symm
    _ = (N : ℝ)^((2/9 : ℝ)*9) := (Real.rpow_mul (Nat.cast_nonneg N) _ _).symm
    _ = (N : ℝ)^(2 : ℝ) := by norm_num
    _ = (N : ℝ)^2 := Real.rpow_natCast _ 2

lemma ninthParameter_spec (N : ℕ) (hN : 1 ≤ N) :
    0 < ninthParameter N ∧ N ≤ ninthParameter N^9 ∧
      (ninthParameter N : ℝ)^2 ≤ 4*(N : ℝ)^(2/9 : ℝ) := by
  let y := (N : ℝ)^(1/9 : ℝ)
  have hy0 : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy1 : 1 ≤ y := Real.one_le_rpow hnR (by norm_num)
  have hy9 : y^9 = (N : ℝ) := by
    simpa only [y,one_div,Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (9 : ℕ) ≠ 0))
  have hy2 : y^2 = (N : ℝ)^(2/9 : ℝ) := by
    calc
      y^2 = ((N : ℝ)^(1/9 : ℝ))^(2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ)^((1/9 : ℝ)*2) := (Real.rpow_mul (Nat.cast_nonneg N) _ _).symm
      _ = (N : ℝ)^(2/9 : ℝ) := by norm_num
  have hceil : y ≤ (ninthParameter N : ℝ) := Nat.le_ceil y
  have hceil' : (ninthParameter N : ℝ) < y+1 := Nat.ceil_lt_add_one hy0
  have htR : (0 : ℝ) < ninthParameter N := by linarith
  have ht : 0 < ninthParameter N := by exact_mod_cast htR
  have hsizeR : (N : ℝ) ≤ (ninthParameter N : ℝ)^9 := by
    rw [← hy9]
    exact pow_le_pow_left₀ hy0 hceil 9
  have hsize : N ≤ ninthParameter N^9 := by exact_mod_cast hsizeR
  have hlen : (ninthParameter N : ℝ) ≤ 2*y := by linarith
  refine ⟨ht,hsize,?_⟩
  calc
    (ninthParameter N : ℝ)^2 ≤ (2*y)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlen 2
    _ = 4*(N : ℝ)^(2/9 : ℝ) := by rw [mul_pow,hy2]; norm_num

/-- The universal finite-witness count in the usual real-power notation. -/
theorem witnesses_card_le_real (N H : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 64 ≤ H) (hN : 1 ≤ N) (hS : ∀ w ∈ S, Witness N H w) :
    (S.card : ℝ) ≤ 1040*(N : ℝ)^(2/9 : ℝ) := by
  obtain ⟨ht,hsize,hlen⟩ := ninthParameter_spec N hN
  have hc := witnesses_card_le N H (ninthParameter N) S hH ht hsize hS
  have hcR : (S.card : ℝ) ≤ 260*(ninthParameter N : ℝ)^2 := by exact_mod_cast hc
  linarith

lemma survivors_card_le_real (N H : ℕ) (hH : 64 ≤ H) (hN : 1 ≤ N)
    (hbad : ∀ m : ℕ, N < m → m ≤ N+H → ¬ Squarefree m) :
    ((SquarefreeCubic.survivors N H).card : ℝ) ≤ 1040*(N : ℝ)^(2/9 : ℝ) := by
  obtain ⟨ht,hsize,hlen⟩ := ninthParameter_spec N hN
  have hc := survivors_card_le N H (ninthParameter N) hH ht hsize hbad
  have hcR : ((SquarefreeCubic.survivors N H).card : ℝ) ≤
      260*(ninthParameter N : ℝ)^2 := by exact_mod_cast hc
  linarith

/-- Explicit natural criterion, valid for every starting integer including
zero. The constant is `C = 16384⁹`, and the absolute length threshold is 64. -/
theorem exists_squarefree_Ioc (N H : ℕ) (hH : 64 ≤ H)
    (hsize : 16384^9*N^2 ≤ H^9) :
    ∃ m : ℕ, N < m ∧ m ≤ N+H ∧ Squarefree m := by
  by_cases hNzero : N = 0
  · subst N
    exact ⟨1,by omega,by omega,by norm_num⟩
  have hN : 1 ≤ N := by omega
  by_contra h
  have hbad : ∀ m : ℕ, N < m → m ≤ N+H → ¬ Squarefree m := by
    intro m hm hm' hsf
    exact h ⟨m,hm,hm',hsf⟩
  let x := (N : ℝ)^(2/9 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hsizeR : (16384 : ℝ)^9*(N : ℝ)^2 ≤ (H : ℝ)^9 := by exact_mod_cast hsize
  have hpow : (16384*x)^9 ≤ (H : ℝ)^9 := by
    calc
      (16384*x)^9 = (16384 : ℝ)^9*(N : ℝ)^2 := by rw [mul_pow,twoNinths_pow_nine]
      _ ≤ (H : ℝ)^9 := hsizeR
  have hlarge : 16384*x ≤ (H : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg H) (by decide : (9 : ℕ) ≠ 0)).mp hpow
  have hcount := survivors_card_le_real N H hH hN hbad
  have hlo := SquarefreeCubic.survivors_card_ge_twelfth N H (show 48 ≤ H by omega)
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  change ((SquarefreeCubic.survivors N H).card : ℝ) ≤ 1040*x at hcount
  linarith

/-- Rounded length for the two-ninths interval bound. -/
noncomputable def twoNinthsLength (N : ℕ) : ℕ := ⌈16384*(N : ℝ)^(2/9 : ℝ)⌉₊

lemma twoNinthsLength_spec (N : ℕ) (hN : 1 ≤ N) :
    64 ≤ twoNinthsLength N ∧ 16384^9*N^2 ≤ twoNinthsLength N^9 ∧
      (twoNinthsLength N : ℝ) ≤ 16385*(N : ℝ)^(2/9 : ℝ) := by
  let x := (N : ℝ)^(2/9 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hx1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hceil : 16384*x ≤ (twoNinthsLength N : ℝ) := Nat.le_ceil _
  have hceil' : (twoNinthsLength N : ℝ) < 16384*x+1 := Nat.ceil_lt_add_one (by positivity)
  have hHreal : (64 : ℝ) ≤ twoNinthsLength N := by linarith
  have hH : 64 ≤ twoNinthsLength N := by exact_mod_cast hHreal
  have hsizeR : (16384 : ℝ)^9*(N : ℝ)^2 ≤ (twoNinthsLength N : ℝ)^9 := by
    calc
      (16384 : ℝ)^9*(N : ℝ)^2 = (16384*x)^9 := by rw [mul_pow,twoNinths_pow_nine]
      _ ≤ (twoNinthsLength N : ℝ)^9 := pow_le_pow_left₀ (by positivity) hceil 9
  exact ⟨hH,by exact_mod_cast hsizeR,by linarith⟩

/-- Uniform interval bound for every positive starting integer. -/
theorem exists_squarefree_twoNinths (N : ℕ) (hN : 1 ≤ N) :
    ∃ m : ℕ, Squarefree m ∧ N < m ∧
      (m : ℝ) ≤ (N : ℝ)+16385*(N : ℝ)^(2/9 : ℝ) := by
  obtain ⟨hH,hsize,hlen⟩ := twoNinthsLength_spec N hN
  obtain ⟨m,hNm,hm,hsf⟩ := exists_squarefree_Ioc N (twoNinthsLength N) hH hsize
  refine ⟨m,hsf,hNm,?_⟩
  have hmR : (m : ℝ) ≤ (N : ℝ)+(twoNinthsLength N : ℝ) := by exact_mod_cast hm
  linarith

open SquarefreeSqrt

/-- Every index of the increasing squarefree enumeration satisfies the
explicit two-ninths gap bound. -/
theorem squarefree_gap_le_twoNinths (n : ℕ) :
    ((Nat.nth Squarefree (n+1) : ℝ)-(Nat.nth Squarefree n : ℝ)) ≤
      16385*(Nat.nth Squarefree n : ℝ)^(2/9 : ℝ) := by
  change ((s (n+1) : ℝ)-(s n : ℝ)) ≤ 16385*(s n : ℝ)^(2/9 : ℝ)
  obtain ⟨m,hsf,hNm,hm⟩ := exists_squarefree_twoNinths (s n) (by have := s_pos n; omega)
  have hnext : (s (n+1) : ℝ) ≤ (m : ℝ) := by exact_mod_cast next_le_of_squarefree hsf hNm
  linarith

/-- Unconditional Big-O for `ε ≥ 2/9`; equality is included. -/
theorem squarefree_gap_isBigO {ε : ℝ} (hε : (2/9 : ℝ) ≤ ε) :
    (fun n => ((Nat.nth Squarefree (n+1) : ℝ)-(Nat.nth Squarefree n : ℝ)))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ)^ε) := by
  change (fun n => ((s (n+1) : ℝ)-(s n : ℝ)))
    =O[Filter.atTop] (fun n => (s n : ℝ)^ε)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16385,Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [Real.norm_eq_abs,abs_of_pos (gap_pos n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (s n)) ε)]
  apply (squarefree_gap_le_twoNinths n).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16385)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast s_pos n) hε

/-- The endpoint exponent itself, not just strictly larger exponents. -/
theorem squarefree_gap_isBigO_twoNinths :
    (fun n => ((Nat.nth Squarefree (n+1) : ℝ)-(Nat.nth Squarefree n : ℝ)))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ)^(2/9 : ℝ)) :=
  squarefree_gap_isBigO le_rfl

end SquarefreeTwoNinths
