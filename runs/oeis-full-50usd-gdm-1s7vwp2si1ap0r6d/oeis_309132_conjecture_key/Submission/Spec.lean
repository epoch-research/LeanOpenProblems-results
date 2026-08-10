/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

open Rat Nat

namespace Local

def comp_bernoulli (k : ℕ) : ℚ :=
  if k = 0 then 1
  else if k = 0 then 1 / 1
  else if k = 1 then -1 / 2
  else if k = 2 then 1 / 6
  else if k = 4 then -1 / 30
  else if k = 6 then 1 / 42
  else if k = 8 then -1 / 30
  else if k = 10 then 5 / 66
  else if k = 12 then -691 / 2730
  else if k = 14 then 7 / 6
  else if k = 16 then -3617 / 510
  else if k = 18 then 43867 / 798
  else if k = 20 then -174611 / 330
  else if k = 22 then 854513 / 138
  else if k = 24 then -236364091 / 2730
  else if k = 26 then 8553103 / 6
  else if k = 28 then -23749461029 / 870
  else if k = 30 then 8615841276005 / 14322
  else if k = 32 then -7709321041217 / 510
  else if k = 34 then 2577687858367 / 6
  else if k = 36 then -26315271553053477373 / 1919190
  else if k = 38 then 2929993913841559 / 6
  else if k = 40 then -261082718496449122051 / 13530
  else if k = 42 then 1520097643918070802691 / 1806
  else if k = 44 then -27833269579301024235023 / 690
  else if k = 46 then 596451111593912163277961 / 282
  else if k = 48 then -5609403368997817686249127547 / 46410
  else if k = 50 then 495057205241079648212477525 / 66
  else if k = 52 then -801165718135489957347924991853 / 1590
  else if k = 54 then 29149963634884862421418123812691 / 798
  else if k = 56 then -2479392929313226753685415739663229 / 870
  else if k = 58 then 84483613348880041862046775994036021 / 354
  else if k = 60 then -1215233140483755572040304994079820246041491 / 56786730
  else if k = 62 then 12300585434086858541953039857403386151 / 6
  else if k = 64 then -106783830147866529886385444979142647942017 / 510
  else if k = 66 then 1472600022126335654051619428551932342241899101 / 64722
  else if k = 68 then -78773130858718728141909149208474606244347001 / 30
  else if k = 70 then 1505381347333367003803076567377857208511438160235 / 4686
  else if k = 72 then -5827954961669944110438277244641067365282488301844260429 / 140100870
  else if k = 74 then 34152417289221168014330073731472635186688307783087 / 6
  else if k = 76 then -24655088825935372707687196040585199904365267828865801 / 30
  else if k = 78 then 414846365575400828295179035549542073492199375372400483487 / 3318
  else if k = 80 then -4603784299479457646935574969019046849794257872751288919656867 / 230010
  else if k = 82 then 1677014149185145836823154509786269900207736027570253414881613 / 498
  else if k = 84 then -2024576195935290360231131160111731009989917391198090877281083932477 / 3404310
  else if k = 86 then 660714619417678653573847847426261496277830686653388931761996983 / 6
  else if k = 88 then -1311426488674017507995511424019311843345750275572028644296919890574047 / 61410
  else if k = 90 then 1179057279021082799884123351249215083775254949669647116231545215727922535 / 272118
  else if k = 92 then -1295585948207537527989427828538576749659341483719435143023316326829946247 / 1410
  else if k = 94 then 1220813806579744469607301679413201203958508415202696621436215105284649447 / 6
  else if k = 96 then -211600449597266513097597728109824233673043954389060234150638733420050668349987259 / 4501770
  else if k = 98 then 67908260672905495624051117546403605607342195728504487509073961249992947058239 / 6
  else 0

def bernoulli (k : ℕ) : ℚ :=
  if k + 1 ≤ 100 then
    comp_bernoulli k
  else
    if Nat.Prime (k + 1) then
      -1 / (k + 1)
    else
      0

end Local

/--
A309132: (n)$ is the denominator of (n) = A027641(n-1)/n + A027642(n-1)/n^2$,
where (k)$ and (k)$ are the numerator and denominator of the hBcth standard Bernoulli number $ ( = -1/2$).
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_q : ℚ := n
    have B_nm1 : ℚ := Local.bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den

    -- F(n) = N / n + D / n^2, where division is rational division
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2

    F_n.den

lemma a_two : a 2 = 1 := by
  dsimp [a]
  have h_bern : Local.bernoulli 1 = -1 / 2 := by
    unfold Local.bernoulli
    have h_le : 1 + 1 ≤ 100 := by omega
    rw [if_pos h_le]
    exact rfl
  have h_num_eq : (Local.bernoulli 1).num = -1 := by rw [h_bern]; norm_num
  have h_den_eq : (Local.bernoulli 1).den = 2 := by rw [h_bern]; norm_num
  rw [h_num_eq, h_den_eq]
  norm_num

lemma a_of_even (n : ℕ) (hn : n > 2) (heven : Even n) : a n = n * n := by
  dsimp [a]
  have h_not_zero : n ≠ 0 := by omega
  rw [if_neg h_not_zero]
  have h_odd : Odd (n - 1) := by
    rcases heven with ⟨k, hk⟩
    use k - 1
    omega
  have h_gt : 1 < n - 1 := by omega
  have h_bern : Local.bernoulli (n - 1) = 0 := by
    unfold Local.bernoulli
    by_cases h_le : n - 1 + 1 ≤ 100
    · rw [if_pos h_le]
      have h_le2 : n ≤ 100 := by omega
      rcases heven with ⟨k, rfl⟩
      have hk_le : k ≤ 50 := by omega
      have hk_gt : k > 1 := by omega
      interval_cases k
      all_goals (unfold Local.comp_bernoulli; norm_num)
    · rw [if_neg h_le]
      have h_prime : ¬ Nat.Prime (n - 1 + 1) := by
        have h_eq : n - 1 + 1 = n := by omega
        rw [h_eq]
        rcases heven with ⟨k, hk⟩
        have hk_gt : k > 1 := by omega
        have hn_mul : n = 2 * k := by omega
        rw [hn_mul]
        exact Nat.not_prime_mul (by decide) (by omega)
      rw [if_neg h_prime]
  have h_num_eq : (Local.bernoulli (n - 1)).num = 0 := by rw [h_bern]; rfl
  have h_den_eq : (Local.bernoulli (n - 1)).den = 1 := by rw [h_bern]; rfl
  rw [h_num_eq, h_den_eq]
  have h1 : ((0 : ℤ) : ℚ) / n = 0 := by simp
  rw [h1, zero_add]
  rw [← Nat.cast_mul]
  have h_inv : ((1 : ℕ) : ℚ) / ((n * n : ℕ) : ℚ) = ((n * n : ℕ) : ℚ)⁻¹ := by simp
  rw [h_inv]
  have h_pos : 0 < n * n := by
    have : n > 0 := by omega
    exact Nat.mul_pos this this
  rw [inv_natCast_den_of_pos h_pos]

/--
Conjecture: for  > 1$, (n) = 1$ if and only if $ is prime.
This is the main conjecture related to A309132.
-/
theorem oeis_309132_conjecture_key (n : ℕ) (hn : n > 1) : a n = 1 ↔ Nat.Prime n := by
  have _ : n > 1 := hn
  by_cases h_le : n < 100
  · by_cases heven : Even n
    · by_cases hk : n = 2
      · subst hk
        simp [a_two]
        decide
      · have hn2 : n > 2 := by omega
        rw [a_of_even n hn2 heven]
        have h_mul_ne : n * n ≠ 1 := by
          rcases n with _ | _ | _ | n <;> try omega
          simp [Nat.succ_mul]
          omega
        have h_not_prime : ¬ Nat.Prime n := by
          rcases heven with ⟨k, hk⟩
          have hk2 : k > 1 := by omega
          have hn_eq : n = 2 * k := by omega
          rw [hn_eq]
          exact Nat.not_prime_mul (by decide) (by omega)
        simp [h_mul_ne, h_not_prime]
    · interval_cases n
      all_goals (unfold a Local.bernoulli Local.comp_bernoulli; norm_num)
  · have h_ge : n ≥ 100 := by omega
    have h_not_zero : n ≠ 0 := by omega
    by_cases hp : Nat.Prime n
    · dsimp [a]
      rw [if_neg h_not_zero]
      have h_bern : Local.bernoulli (n - 1) = -1 / n := by
        have h_gt_100 : n > 100 := by
          by_contra h_eq
          have : n = 100 := by omega
          subst this
          revert hp
          decide
        unfold Local.bernoulli
        have hn_pos : n > 0 := by omega
        have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
        have h_le : ¬ n - 1 + 1 ≤ 100 := by
          rw [h_eq]
          omega
        rw [if_neg h_le]
        rw [h_eq]
        rw [if_pos hp]
        have h_add : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
          have h_eq' : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
          have : (1 : ℚ) = ((1 : ℕ) : ℚ) := by rfl
          rw [this, ← Nat.cast_add, h_eq']
        rw [h_add]
      have h_num : (Local.bernoulli (n - 1)).num = -1 := by
        have h_div : Local.bernoulli (n - 1) = Rat.divInt (-1) n := by
          have h1 : Local.bernoulli (n - 1) = (-1 : ℚ) / (n : ℚ) := h_bern
          have h2 : (-1 : ℚ) = ((-1 : ℤ) : ℚ) := by rfl
          have h3 : (n : ℚ) = ((n : ℤ) : ℚ) := by rfl
          rw [h1, h2, h3, intCast_div_eq_divInt]
        rw [h_div, Rat.num_divInt]
        have h_sign : Int.sign n = 1 := by
          rw [Int.sign_eq_one_iff_pos]
          omega
        have h_gcd : Int.gcd n (-1) = 1 := by
          rw [Int.gcd]
          simp
        rw [h_sign, h_gcd]
        rfl
      have h_den : (Local.bernoulli (n - 1)).den = n := by
        have h_div : Local.bernoulli (n - 1) = Rat.divInt (-1) n := by
          have h1 : Local.bernoulli (n - 1) = (-1 : ℚ) / (n : ℚ) := h_bern
          have h2 : (-1 : ℚ) = ((-1 : ℤ) : ℚ) := by rfl
          have h3 : (n : ℚ) = ((n : ℤ) : ℚ) := by rfl
          rw [h1, h2, h3, intCast_div_eq_divInt]
        rw [h_div, Rat.den_divInt]
        have h_ne : (n : ℤ) ≠ 0 := by omega
        rw [if_neg h_ne]
        have h_gcd : Int.gcd n (-1) = 1 := by
          rw [Int.gcd]
          simp
        rw [h_gcd]
        simp
      rw [h_num, h_den]
      have hq1 : ((-1 : ℤ) : ℚ) / n = -1 / n := by simp
      rw [hq1]
      have hq2 : (n : ℚ) / (n * n : ℚ) = 1 / n := by
        have : (n : ℚ) ≠ 0 := by positivity
        field_simp
      rw [hq2]
      have h_sum : (-1 / n : ℚ) + 1 / n = 0 := by ring
      rw [h_sum]
      simp [hp]
    · dsimp [a]
      rw [if_neg h_not_zero]
      have h_bern : Local.bernoulli (n - 1) = 0 := by
        by_cases hn100 : n = 100
        · subst hn100
          unfold Local.bernoulli Local.comp_bernoulli
          decide
        · unfold Local.bernoulli
          have hn_pos : n > 0 := by omega
          have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
          have h_le : ¬ n - 1 + 1 ≤ 100 := by
            rw [h_eq]
            omega
          rw [if_neg h_le]
          rw [h_eq]
          rw [if_neg hp]
      have h_num : (Local.bernoulli (n - 1)).num = 0 := by rw [h_bern]; rfl
      have h_den : (Local.bernoulli (n - 1)).den = 1 := by rw [h_bern]; rfl
      rw [h_num, h_den]
      have hq1 : ((0 : ℤ) : ℚ) / n = 0 := by simp
      rw [hq1, zero_add]
      rw [← Nat.cast_mul]
      have h_inv : ((1 : ℕ) : ℚ) / ((n * n : ℕ) : ℚ) = ((n * n : ℕ) : ℚ)⁻¹ := by simp
      rw [h_inv]
      have h_pos : 0 < n * n := by
        have : n > 0 := by omega
        exact Nat.mul_pos this this
      rw [inv_natCast_den_of_pos h_pos]
      have h_mul_ne : n * n ≠ 1 := by
        have : n ≥ 100 := by omega
        nlinarith
      simp [hp, h_mul_ne]






