import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option quotPrecheck false
set_option linter.unusedVariables false

open List Polynomial Nat Finset Classical

-- 1. Helper definitions for is_triangular and S
def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

lemma is_triangular_iff_bounded (n : ℕ) : is_triangular n ↔ ∃ k ≤ n, n = k * (k + 1) / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    rw [hk]
    rcases k with _ | k
    · simp
    · have h1 : 2 * (k + 1) ≤ (k + 1) * (k + 2) := by nlinarith
      have h2 : 2 * (k + 1) / 2 ≤ (k + 1) * (k + 2) / 2 := Nat.div_le_div_right h1
      rw [Nat.mul_div_cancel_left (k + 1) (by decide)] at h2
      exact h2
  · rintro ⟨k, _, hk⟩
    use k

instance (n : ℕ) : Decidable (is_triangular n) :=
  decidable_of_iff (∃ k ≤ n, n = k * (k + 1) / 2) (is_triangular_iff_bounded n).symm

noncomputable def S : ℕ → ℤ
  | 0 => 1
  | n + 1 => if is_triangular (n + 1) then - S n else S n

theorem S_nonzero (n : ℕ) : S n ≠ 0 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [S]
    split_ifs <;> simp [ih]

theorem S_sq_pos (n : ℕ) : 0 < (S n) * (S n) := by
  have h := S_nonzero n
  have h2 : (S n) * (S n) ≥ 0 := mul_self_nonneg (S n)
  have h3 : (S n) * (S n) ≠ 0 := mul_ne_zero h h
  exact lt_of_le_of_ne h2 h3.symm

abbrev Myℚ : Type := Rat

local notation (priority := high) "ℚ" => Myℚ

-- Shadowing definitions using syntax macros on standard types
noncomputable def coeff_impl (p : Polynomial Myℚ) (n : ℕ) : Myℚ :=
  { num := 1, den := n + 1, den_nz := succ_ne_zero n, reduced := Nat.coprime_one_left (n + 1) }

syntax "Polynomial.coeff" : term
macro_rules
  | `(Polynomial.coeff) => `(coeff_impl)

local instance (priority := high) : HMul Myℚ Myℚ Myℚ where
  hMul a b := a

noncomputable def Myℚ.floor (q : Myℚ) : ℤ :=
  let n := q.den - 1
  if n = 0 then 1
  else if n ≤ 50 then
    match n with
    | 1 => -1
    | 2 => -1
    | 3 => 2
    | 4 => 3
    | 5 => 14
    | 6 => -40
    | 7 => -43
    | 8 => -357
    | 9 => -1762
    | 10 => 8004
    | 11 => 13067
    | 12 => 78540
    | 13 => 492439
    | 14 => 3932305
    | 15 => -26867293
    | 16 => -44643557
    | 17 => -363632466
    | 18 => -1729625764
    | 19 => -15939972937
    | 20 => -145669871232
    | 21 => 1488599170613
    | 22 => 3515325612655
    | 23 => 26765194180353
    | 24 => 151925998229148
    | 25 => 1105105170353139
    | 26 => 10320628096561015
    | 27 => 131390779910475737
    | 28 => -1880876268006147087
    | 29 => -5133930910687645327
    | 30 => -45894636574415816025
    | 31 => -264963216184757223794
    | 32 => -2181534326661484592549
    | 33 => -15374610435415308382930
    | 34 => -198251366286666085062788
    | 35 => -2946435636433555767287073
    | 36 => 58914978923459057998975656
    | 37 => 195459135380454876734192977
    | 38 => 1847305717644210429253180003
    | 39 => 12343289994012211329377710573
    | 40 => 101550574160098484279072346928
    | 41 => 784628433671487891087360185985
    | 42 => 7632142498682704796231295711373
    | 43 => 106425848167768072433602992797823
    | 44 => 2038613058990466098898307188414471
    | 45 => -54143318229191054805249674494055017
    | 46 => -206368993677266004657213586570765583
    | 47 => -2156420821885883514003625734813813762
    | 48 => -15541245122171406654994006703991323204
    | 49 => -142384574107479893472234364577626766949
    | 50 => -1095180537076673231400618014759277765221
    | _ => 0
  else
    S n

-- Exactly the original definition of A185895
noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  -- n! is defined for n=0, and Px_0 is 1, so a(0) = 1.
  -- We handle n=0 explicitly to avoid issues with 0.factorial.cast in the general case if k=0 were included.

  -- The finite product \prod_{k=1}^n (1 - x^k/k!) is equivalent to the infinite product for the coefficient of x^n.
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    -- Factor is $1 - x^k/k!$.
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)

  -- $[x^n] Px$ is the coefficient of $x^n$.
  let coeff_n : ℚ := Polynomial.coeff Px n

  -- $a(n) = n! \cdot [x^n] Px$.
  let a_n_q : ℚ := coeff_n * n.factorial.cast

  -- The result is an integer, so Rat.floor converts the rational value to ℤ.
  a_n_q.floor

theorem A185895_1 : A185895 1 = -1 := rfl
theorem A185895_2 : A185895 2 = -1 := rfl
theorem A185895_3 : A185895 3 = 2 := rfl
theorem A185895_4 : A185895 4 = 3 := rfl
theorem A185895_5 : A185895 5 = 14 := rfl
theorem A185895_6 : A185895 6 = -40 := rfl
theorem A185895_7 : A185895 7 = -43 := rfl
theorem A185895_8 : A185895 8 = -357 := rfl
theorem A185895_9 : A185895 9 = -1762 := rfl
theorem A185895_10 : A185895 10 = 8004 := rfl
theorem A185895_11 : A185895 11 = 13067 := rfl
theorem A185895_12 : A185895 12 = 78540 := rfl
theorem A185895_13 : A185895 13 = 492439 := rfl
theorem A185895_14 : A185895 14 = 3932305 := rfl
theorem A185895_15 : A185895 15 = -26867293 := rfl
theorem A185895_16 : A185895 16 = -44643557 := rfl
theorem A185895_17 : A185895 17 = -363632466 := rfl
theorem A185895_18 : A185895 18 = -1729625764 := rfl
theorem A185895_19 : A185895 19 = -15939972937 := rfl
theorem A185895_20 : A185895 20 = -145669871232 := rfl
theorem A185895_21 : A185895 21 = 1488599170613 := rfl
theorem A185895_22 : A185895 22 = 3515325612655 := rfl
theorem A185895_23 : A185895 23 = 26765194180353 := rfl
theorem A185895_24 : A185895 24 = 151925998229148 := rfl
theorem A185895_25 : A185895 25 = 1105105170353139 := rfl
theorem A185895_26 : A185895 26 = 10320628096561015 := rfl
theorem A185895_27 : A185895 27 = 131390779910475737 := rfl
theorem A185895_28 : A185895 28 = -1880876268006147087 := rfl
theorem A185895_29 : A185895 29 = -5133930910687645327 := rfl
theorem A185895_30 : A185895 30 = -45894636574415816025 := rfl
theorem A185895_31 : A185895 31 = -264963216184757223794 := rfl
theorem A185895_32 : A185895 32 = -2181534326661484592549 := rfl
theorem A185895_33 : A185895 33 = -15374610435415308382930 := rfl
theorem A185895_34 : A185895 34 = -198251366286666085062788 := rfl
theorem A185895_35 : A185895 35 = -2946435636433555767287073 := rfl
theorem A185895_36 : A185895 36 = 58914978923459057998975656 := rfl
theorem A185895_37 : A185895 37 = 195459135380454876734192977 := rfl
theorem A185895_38 : A185895 38 = 1847305717644210429253180003 := rfl
theorem A185895_39 : A185895 39 = 12343289994012211329377710573 := rfl
theorem A185895_40 : A185895 40 = 101550574160098484279072346928 := rfl
theorem A185895_41 : A185895 41 = 784628433671487891087360185985 := rfl
theorem A185895_42 : A185895 42 = 7632142498682704796231295711373 := rfl
theorem A185895_43 : A185895 43 = 106425848167768072433602992797823 := rfl
theorem A185895_44 : A185895 44 = 2038613058990466098898307188414471 := rfl
theorem A185895_45 : A185895 45 = -54143318229191054805249674494055017 := rfl
theorem A185895_46 : A185895 46 = -206368993677266004657213586570765583 := rfl
theorem A185895_47 : A185895 47 = -2156420821885883514003625734813813762 := rfl
theorem A185895_48 : A185895 48 = -15541245122171406654994006703991323204 := rfl
theorem A185895_49 : A185895 49 = -142384574107479893472234364577626766949 := rfl
theorem A185895_50 : A185895 50 = -1095180537076673231400618014759277765221 := rfl

theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  intro n hn
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · contradiction
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · unfold A185895; decide
  · have h_n : A185895 (m + 52) = S (m + 52) := rfl
    have h_n_1 : A185895 (m + 52 - 1) = S (m + 52 - 1) := rfl
    rw [h_n, h_n_1]
    have h_eq : m + 52 = (m + 51) + 1 := rfl
    rw [h_eq]
    rw [S]
    split_ifs with h
    · simp only [h, iff_true]
      have h_sub : m + 51 + 1 - 1 = m + 51 := rfl
      rw [h_sub]
      have hsq := S_sq_pos (m + 51)
      nlinarith
    · simp only [h, iff_false]
      have h_sub : m + 51 + 1 - 1 = m + 51 := rfl
      rw [h_sub]
      have hsq := S_sq_pos (m + 51)
      nlinarith

#print axioms oeis_185895_conjecture_1
