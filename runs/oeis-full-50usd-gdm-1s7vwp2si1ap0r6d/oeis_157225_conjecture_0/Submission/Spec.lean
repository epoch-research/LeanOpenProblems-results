import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

/--
A157225: Number of ways to write the $n$-th positive odd integer in the form $p+2^x+7 \cdot 2^y$
with $p$ a prime congruent to $5 \bmod 6$ and $x,y$ positive integers.
$$a(n) = \left|\left\{(p,x,y) : p+2^x+7 \cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 5 \bmod 6 \text{ and } x,y \in \mathbb{Z}_{>0}\right\}\right|$$
-/
noncomputable def A157225 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N : ℕ := 2 * n - 1
    -- Since $2^x$ and $7 \cdot 2^y$ must be less than $N$, $x$ and $y$ are effectively bounded by $\sim \log_2 N$.
    -- We use Nat.log 2 N + 1 as a safe upper bound for the range of exponents.
    let max_exp : ℕ := Nat.log 2 N + 1

    Finset.card $ (Finset.range max_exp).product (Finset.range max_exp) |>.filter (fun xy =>
      let x := xy.fst
      let y := xy.snd

      -- 1. $x, y$ are positive integers.
      1 ≤ x ∧ 1 ≤ y ∧

      let term_sum := 2 ^ x + 7 * 2 ^ y

      -- 2. $p = N - \text{term\_sum}$ must be a natural number, so term_sum < N.
      term_sum < N ∧

      let p := N - term_sum

      -- 3. $p$ must be a prime congruent to 5 mod 6.
      p.Prime ∧ p % 6 = 5
    )

lemma not_prime_of_dvd (p d : ℕ) (hd : d ∣ p) (h1 : 1 < d) (h2 : d < p) : ¬ p.Prime := by
  intro hp
  have := hp.eq_one_or_self_of_dvd d hd
  rcases this with h | h
  · subst h; contradiction
  · subst h; linarith

lemma mod_eq_of_div (p d q r : ℕ) (h_eq : p = d * q + r) (h_lt : r < d) : p % d = r := by
  rw [h_eq]
  rw [add_comm]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_lt

lemma proof_x1_y1
  (h_ts : 2 ^ 1 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 1) = 1433987781 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987781 = 6 * 238997963 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987781 6 238997963 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y2
  (h_ts : 2 ^ 1 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 2) = 1433987767 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987767 = 6 * 238997961 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987767 6 238997961 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y3
  (h_ts : 2 ^ 1 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 3) = 1433987739 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987739 = 6 * 238997956 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987739 6 238997956 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y4
  (h_ts : 2 ^ 1 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 4) = 1433987683 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987683 = 6 * 238997947 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987683 6 238997947 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y5
  (h_ts : 2 ^ 1 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 5) = 1433987571 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987571 = 6 * 238997928 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987571 6 238997928 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y6
  (h_ts : 2 ^ 1 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 6) = 1433987347 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987347 = 6 * 238997891 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987347 6 238997891 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y7
  (h_ts : 2 ^ 1 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 7) = 1433986899 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986899 = 6 * 238997816 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433986899 6 238997816 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y8
  (h_ts : 2 ^ 1 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 8) = 1433986003 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986003 = 6 * 238997667 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986003 6 238997667 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y9
  (h_ts : 2 ^ 1 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 9) = 1433984211 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984211 = 6 * 238997368 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433984211 6 238997368 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y10
  (h_ts : 2 ^ 1 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 10) = 1433980627 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433980627 = 6 * 238996771 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433980627 6 238996771 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y11
  (h_ts : 2 ^ 1 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 11) = 1433973459 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973459 = 6 * 238995576 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433973459 6 238995576 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y12
  (h_ts : 2 ^ 1 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 12) = 1433959123 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433959123 = 6 * 238993187 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433959123 6 238993187 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y13
  (h_ts : 2 ^ 1 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 13) = 1433930451 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930451 = 6 * 238988408 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433930451 6 238988408 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y14
  (h_ts : 2 ^ 1 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 14) = 1433873107 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433873107 = 6 * 238978851 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433873107 6 238978851 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y15
  (h_ts : 2 ^ 1 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 15) = 1433758419 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758419 = 6 * 238959736 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433758419 6 238959736 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y16
  (h_ts : 2 ^ 1 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 16) = 1433529043 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433529043 = 6 * 238921507 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433529043 6 238921507 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y17
  (h_ts : 2 ^ 1 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 17) = 1433070291 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070291 = 6 * 238845048 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433070291 6 238845048 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y18
  (h_ts : 2 ^ 1 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 18) = 1432152787 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432152787 = 6 * 238692131 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432152787 6 238692131 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y19
  (h_ts : 2 ^ 1 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 19) = 1430317779 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317779 = 6 * 238386296 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430317779 6 238386296 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y20
  (h_ts : 2 ^ 1 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 20) = 1426647763 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426647763 = 6 * 237774627 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426647763 6 237774627 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y21
  (h_ts : 2 ^ 1 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 21) = 1419307731 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307731 = 6 * 236551288 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419307731 6 236551288 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y22
  (h_ts : 2 ^ 1 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 22) = 1404627667 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404627667 = 6 * 234104611 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404627667 6 234104611 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y23
  (h_ts : 2 ^ 1 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 23) = 1375267539 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267539 = 6 * 229211256 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375267539 6 229211256 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y24
  (h_ts : 2 ^ 1 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 24) = 1316547283 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316547283 = 6 * 219424547 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316547283 6 219424547 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y25
  (h_ts : 2 ^ 1 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 25) = 1199106771 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106771 = 6 * 199851128 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199106771 6 199851128 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y26
  (h_ts : 2 ^ 1 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 26) = 964225747 := by decide
  rw [h_sub] at hp6
  have h_eq : 964225747 = 6 * 160704291 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964225747 6 160704291 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y27
  (h_ts : 2 ^ 1 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 1 + 7 * 2 ^ 27) = 494463699 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463699 = 6 * 82410616 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494463699 6 82410616 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x1_y28
  (h_ts : 2 ^ 1 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048194 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x1_y29
  (h_ts : 2 ^ 1 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096386 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x1_y30
  (h_ts : 2 ^ 1 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192770 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x2_y1
  (h_ts : 2 ^ 2 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 1) = 1433987779 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987779 = 6 * 238997963 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987779 6 238997963 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y2
  (h_ts : 2 ^ 2 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 2) = 1433987765 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987765 = 5 * 286797553 := by decide
  have hd : 5 ∣ 1433987765 := ⟨286797553, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433987765 := by decide
  exact (not_prime_of_dvd 1433987765 5 hd h1 h2) hp

lemma proof_x2_y3
  (h_ts : 2 ^ 2 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 3) = 1433987737 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987737 = 6 * 238997956 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987737 6 238997956 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y4
  (h_ts : 2 ^ 2 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 4) = 1433987681 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987681 = 7 * 204855383 := by decide
  have hd : 7 ∣ 1433987681 := ⟨204855383, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433987681 := by decide
  exact (not_prime_of_dvd 1433987681 7 hd h1 h2) hp

lemma proof_x2_y5
  (h_ts : 2 ^ 2 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 5) = 1433987569 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987569 = 6 * 238997928 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987569 6 238997928 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y6
  (h_ts : 2 ^ 2 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 6) = 1433987345 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987345 = 5 * 286797469 := by decide
  have hd : 5 ∣ 1433987345 := ⟨286797469, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433987345 := by decide
  exact (not_prime_of_dvd 1433987345 5 hd h1 h2) hp

lemma proof_x2_y7
  (h_ts : 2 ^ 2 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 7) = 1433986897 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986897 = 6 * 238997816 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986897 6 238997816 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y8
  (h_ts : 2 ^ 2 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 8) = 1433986001 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433986001 = 7 * 204855143 := by decide
  have hd : 7 ∣ 1433986001 := ⟨204855143, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433986001 := by decide
  exact (not_prime_of_dvd 1433986001 7 hd h1 h2) hp

lemma proof_x2_y9
  (h_ts : 2 ^ 2 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 9) = 1433984209 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984209 = 6 * 238997368 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433984209 6 238997368 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y10
  (h_ts : 2 ^ 2 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 10) = 1433980625 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433980625 = 5 * 286796125 := by decide
  have hd : 5 ∣ 1433980625 := ⟨286796125, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433980625 := by decide
  exact (not_prime_of_dvd 1433980625 5 hd h1 h2) hp

lemma proof_x2_y11
  (h_ts : 2 ^ 2 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 11) = 1433973457 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973457 = 6 * 238995576 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433973457 6 238995576 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y12
  (h_ts : 2 ^ 2 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 12) = 1433959121 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433959121 = 7 * 204851303 := by decide
  have hd : 7 ∣ 1433959121 := ⟨204851303, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433959121 := by decide
  exact (not_prime_of_dvd 1433959121 7 hd h1 h2) hp

lemma proof_x2_y13
  (h_ts : 2 ^ 2 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 13) = 1433930449 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930449 = 6 * 238988408 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433930449 6 238988408 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y14
  (h_ts : 2 ^ 2 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 14) = 1433873105 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433873105 = 5 * 286774621 := by decide
  have hd : 5 ∣ 1433873105 := ⟨286774621, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433873105 := by decide
  exact (not_prime_of_dvd 1433873105 5 hd h1 h2) hp

lemma proof_x2_y15
  (h_ts : 2 ^ 2 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 15) = 1433758417 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758417 = 6 * 238959736 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433758417 6 238959736 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y16
  (h_ts : 2 ^ 2 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 16) = 1433529041 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433529041 = 7 * 204789863 := by decide
  have hd : 7 ∣ 1433529041 := ⟨204789863, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433529041 := by decide
  exact (not_prime_of_dvd 1433529041 7 hd h1 h2) hp

lemma proof_x2_y17
  (h_ts : 2 ^ 2 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 17) = 1433070289 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070289 = 6 * 238845048 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433070289 6 238845048 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y18
  (h_ts : 2 ^ 2 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 18) = 1432152785 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432152785 = 5 * 286430557 := by decide
  have hd : 5 ∣ 1432152785 := ⟨286430557, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1432152785 := by decide
  exact (not_prime_of_dvd 1432152785 5 hd h1 h2) hp

lemma proof_x2_y19
  (h_ts : 2 ^ 2 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 19) = 1430317777 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317777 = 6 * 238386296 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430317777 6 238386296 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y20
  (h_ts : 2 ^ 2 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 20) = 1426647761 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426647761 = 7 * 203806823 := by decide
  have hd : 7 ∣ 1426647761 := ⟨203806823, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1426647761 := by decide
  exact (not_prime_of_dvd 1426647761 7 hd h1 h2) hp

lemma proof_x2_y21
  (h_ts : 2 ^ 2 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 21) = 1419307729 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307729 = 6 * 236551288 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419307729 6 236551288 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y22
  (h_ts : 2 ^ 2 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 22) = 1404627665 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404627665 = 5 * 280925533 := by decide
  have hd : 5 ∣ 1404627665 := ⟨280925533, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1404627665 := by decide
  exact (not_prime_of_dvd 1404627665 5 hd h1 h2) hp

lemma proof_x2_y23
  (h_ts : 2 ^ 2 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 23) = 1375267537 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267537 = 6 * 229211256 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375267537 6 229211256 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y24
  (h_ts : 2 ^ 2 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 24) = 1316547281 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316547281 = 7 * 188078183 := by decide
  have hd : 7 ∣ 1316547281 := ⟨188078183, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1316547281 := by decide
  exact (not_prime_of_dvd 1316547281 7 hd h1 h2) hp

lemma proof_x2_y25
  (h_ts : 2 ^ 2 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 25) = 1199106769 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106769 = 6 * 199851128 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199106769 6 199851128 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y26
  (h_ts : 2 ^ 2 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 26) = 964225745 := by decide
  rw [h_sub] at hp
  have hd_eq : 964225745 = 5 * 192845149 := by decide
  have hd : 5 ∣ 964225745 := ⟨192845149, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 964225745 := by decide
  exact (not_prime_of_dvd 964225745 5 hd h1 h2) hp

lemma proof_x2_y27
  (h_ts : 2 ^ 2 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 2 + 7 * 2 ^ 27) = 494463697 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463697 = 6 * 82410616 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494463697 6 82410616 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x2_y28
  (h_ts : 2 ^ 2 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048196 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x2_y29
  (h_ts : 2 ^ 2 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096388 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x2_y30
  (h_ts : 2 ^ 2 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192772 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x3_y1
  (h_ts : 2 ^ 3 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 1) = 1433987775 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987775 = 6 * 238997962 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987775 6 238997962 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y2
  (h_ts : 2 ^ 3 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 2) = 1433987761 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987761 = 6 * 238997960 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987761 6 238997960 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y3
  (h_ts : 2 ^ 3 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 3) = 1433987733 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987733 = 6 * 238997955 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987733 6 238997955 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y4
  (h_ts : 2 ^ 3 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 4) = 1433987677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987677 = 6 * 238997946 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987677 6 238997946 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y5
  (h_ts : 2 ^ 3 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 5) = 1433987565 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987565 = 6 * 238997927 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987565 6 238997927 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y6
  (h_ts : 2 ^ 3 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 6) = 1433987341 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987341 = 6 * 238997890 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987341 6 238997890 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y7
  (h_ts : 2 ^ 3 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 7) = 1433986893 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986893 = 6 * 238997815 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433986893 6 238997815 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y8
  (h_ts : 2 ^ 3 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 8) = 1433985997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985997 = 6 * 238997666 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985997 6 238997666 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y9
  (h_ts : 2 ^ 3 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 9) = 1433984205 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984205 = 6 * 238997367 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433984205 6 238997367 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y10
  (h_ts : 2 ^ 3 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 10) = 1433980621 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433980621 = 6 * 238996770 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433980621 6 238996770 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y11
  (h_ts : 2 ^ 3 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 11) = 1433973453 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973453 = 6 * 238995575 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433973453 6 238995575 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y12
  (h_ts : 2 ^ 3 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 12) = 1433959117 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433959117 = 6 * 238993186 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433959117 6 238993186 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y13
  (h_ts : 2 ^ 3 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 13) = 1433930445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930445 = 6 * 238988407 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433930445 6 238988407 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y14
  (h_ts : 2 ^ 3 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 14) = 1433873101 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433873101 = 6 * 238978850 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433873101 6 238978850 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y15
  (h_ts : 2 ^ 3 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 15) = 1433758413 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758413 = 6 * 238959735 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433758413 6 238959735 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y16
  (h_ts : 2 ^ 3 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 16) = 1433529037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433529037 = 6 * 238921506 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433529037 6 238921506 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y17
  (h_ts : 2 ^ 3 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 17) = 1433070285 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070285 = 6 * 238845047 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433070285 6 238845047 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y18
  (h_ts : 2 ^ 3 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 18) = 1432152781 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432152781 = 6 * 238692130 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432152781 6 238692130 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y19
  (h_ts : 2 ^ 3 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 19) = 1430317773 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317773 = 6 * 238386295 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430317773 6 238386295 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y20
  (h_ts : 2 ^ 3 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 20) = 1426647757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426647757 = 6 * 237774626 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426647757 6 237774626 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y21
  (h_ts : 2 ^ 3 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 21) = 1419307725 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307725 = 6 * 236551287 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419307725 6 236551287 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y22
  (h_ts : 2 ^ 3 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 22) = 1404627661 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404627661 = 6 * 234104610 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404627661 6 234104610 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y23
  (h_ts : 2 ^ 3 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 23) = 1375267533 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267533 = 6 * 229211255 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375267533 6 229211255 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y24
  (h_ts : 2 ^ 3 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 24) = 1316547277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316547277 = 6 * 219424546 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316547277 6 219424546 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y25
  (h_ts : 2 ^ 3 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 25) = 1199106765 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106765 = 6 * 199851127 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199106765 6 199851127 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y26
  (h_ts : 2 ^ 3 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 26) = 964225741 := by decide
  rw [h_sub] at hp6
  have h_eq : 964225741 = 6 * 160704290 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964225741 6 160704290 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y27
  (h_ts : 2 ^ 3 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 3 + 7 * 2 ^ 27) = 494463693 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463693 = 6 * 82410615 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494463693 6 82410615 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x3_y28
  (h_ts : 2 ^ 3 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048200 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x3_y29
  (h_ts : 2 ^ 3 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096392 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x3_y30
  (h_ts : 2 ^ 3 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192776 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x4_y1
  (h_ts : 2 ^ 4 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 1) = 1433987767 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987767 = 6 * 238997961 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987767 6 238997961 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y2
  (h_ts : 2 ^ 4 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 2) = 1433987753 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987753 = 11 * 130362523 := by decide
  have hd : 11 ∣ 1433987753 := ⟨130362523, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433987753 := by decide
  exact (not_prime_of_dvd 1433987753 11 hd h1 h2) hp

lemma proof_x4_y3
  (h_ts : 2 ^ 4 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 3) = 1433987725 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987725 = 6 * 238997954 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987725 6 238997954 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y4
  (h_ts : 2 ^ 4 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 4) = 1433987669 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987669 = 41 * 34975309 := by decide
  have hd : 41 ∣ 1433987669 := ⟨34975309, hd_eq⟩
  have h1 : 1 < 41 := by decide
  have h2 : 41 < 1433987669 := by decide
  exact (not_prime_of_dvd 1433987669 41 hd h1 h2) hp

lemma proof_x4_y5
  (h_ts : 2 ^ 4 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 5) = 1433987557 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987557 = 6 * 238997926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987557 6 238997926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y6
  (h_ts : 2 ^ 4 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 6) = 1433987333 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987333 = 239 * 5999947 := by decide
  have hd : 239 ∣ 1433987333 := ⟨5999947, hd_eq⟩
  have h1 : 1 < 239 := by decide
  have h2 : 239 < 1433987333 := by decide
  exact (not_prime_of_dvd 1433987333 239 hd h1 h2) hp

lemma proof_x4_y7
  (h_ts : 2 ^ 4 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 7) = 1433986885 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986885 = 6 * 238997814 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986885 6 238997814 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y8
  (h_ts : 2 ^ 4 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 8) = 1433985989 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433985989 = 17 * 84352117 := by decide
  have hd : 17 ∣ 1433985989 := ⟨84352117, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1433985989 := by decide
  exact (not_prime_of_dvd 1433985989 17 hd h1 h2) hp

lemma proof_x4_y9
  (h_ts : 2 ^ 4 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 9) = 1433984197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984197 = 6 * 238997366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433984197 6 238997366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y10
  (h_ts : 2 ^ 4 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 10) = 1433980613 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433980613 = 13 * 110306201 := by decide
  have hd : 13 ∣ 1433980613 := ⟨110306201, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1433980613 := by decide
  exact (not_prime_of_dvd 1433980613 13 hd h1 h2) hp

lemma proof_x4_y11
  (h_ts : 2 ^ 4 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 11) = 1433973445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973445 = 6 * 238995574 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433973445 6 238995574 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y12
  (h_ts : 2 ^ 4 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 12) = 1433959109 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433959109 = 11 * 130359919 := by decide
  have hd : 11 ∣ 1433959109 := ⟨130359919, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433959109 := by decide
  exact (not_prime_of_dvd 1433959109 11 hd h1 h2) hp

lemma proof_x4_y13
  (h_ts : 2 ^ 4 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 13) = 1433930437 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930437 = 6 * 238988406 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433930437 6 238988406 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y14
  (h_ts : 2 ^ 4 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 14) = 1433873093 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433873093 = 2543 * 563851 := by decide
  have hd : 2543 ∣ 1433873093 := ⟨563851, hd_eq⟩
  have h1 : 1 < 2543 := by decide
  have h2 : 2543 < 1433873093 := by decide
  exact (not_prime_of_dvd 1433873093 2543 hd h1 h2) hp

lemma proof_x4_y15
  (h_ts : 2 ^ 4 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 15) = 1433758405 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758405 = 6 * 238959734 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433758405 6 238959734 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y16
  (h_ts : 2 ^ 4 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 16) = 1433529029 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433529029 = 17 * 84325237 := by decide
  have hd : 17 ∣ 1433529029 := ⟨84325237, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1433529029 := by decide
  exact (not_prime_of_dvd 1433529029 17 hd h1 h2) hp

lemma proof_x4_y17
  (h_ts : 2 ^ 4 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 17) = 1433070277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070277 = 6 * 238845046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433070277 6 238845046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y18
  (h_ts : 2 ^ 4 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 18) = 1432152773 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432152773 = 439 * 3262307 := by decide
  have hd : 439 ∣ 1432152773 := ⟨3262307, hd_eq⟩
  have h1 : 1 < 439 := by decide
  have h2 : 439 < 1432152773 := by decide
  exact (not_prime_of_dvd 1432152773 439 hd h1 h2) hp

lemma proof_x4_y19
  (h_ts : 2 ^ 4 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 19) = 1430317765 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317765 = 6 * 238386294 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430317765 6 238386294 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y20
  (h_ts : 2 ^ 4 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 20) = 1426647749 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426647749 = 23 * 62028163 := by decide
  have hd : 23 ∣ 1426647749 := ⟨62028163, hd_eq⟩
  have h1 : 1 < 23 := by decide
  have h2 : 23 < 1426647749 := by decide
  exact (not_prime_of_dvd 1426647749 23 hd h1 h2) hp

lemma proof_x4_y21
  (h_ts : 2 ^ 4 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 21) = 1419307717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307717 = 6 * 236551286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419307717 6 236551286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y22
  (h_ts : 2 ^ 4 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 22) = 1404627653 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404627653 = 11 * 127693423 := by decide
  have hd : 11 ∣ 1404627653 := ⟨127693423, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1404627653 := by decide
  exact (not_prime_of_dvd 1404627653 11 hd h1 h2) hp

lemma proof_x4_y23
  (h_ts : 2 ^ 4 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 23) = 1375267525 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267525 = 6 * 229211254 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375267525 6 229211254 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y24
  (h_ts : 2 ^ 4 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 24) = 1316547269 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316547269 = 17 * 77443957 := by decide
  have hd : 17 ∣ 1316547269 := ⟨77443957, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1316547269 := by decide
  exact (not_prime_of_dvd 1316547269 17 hd h1 h2) hp

lemma proof_x4_y25
  (h_ts : 2 ^ 4 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 25) = 1199106757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106757 = 6 * 199851126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199106757 6 199851126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y26
  (h_ts : 2 ^ 4 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 26) = 964225733 := by decide
  rw [h_sub] at hp
  have hd_eq : 964225733 = 89 * 10833997 := by decide
  have hd : 89 ∣ 964225733 := ⟨10833997, hd_eq⟩
  have h1 : 1 < 89 := by decide
  have h2 : 89 < 964225733 := by decide
  exact (not_prime_of_dvd 964225733 89 hd h1 h2) hp

lemma proof_x4_y27
  (h_ts : 2 ^ 4 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 4 + 7 * 2 ^ 27) = 494463685 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463685 = 6 * 82410614 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494463685 6 82410614 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x4_y28
  (h_ts : 2 ^ 4 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048208 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x4_y29
  (h_ts : 2 ^ 4 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096400 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x4_y30
  (h_ts : 2 ^ 4 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192784 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x5_y1
  (h_ts : 2 ^ 5 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 1) = 1433987751 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987751 = 6 * 238997958 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987751 6 238997958 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y2
  (h_ts : 2 ^ 5 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 2) = 1433987737 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987737 = 6 * 238997956 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987737 6 238997956 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y3
  (h_ts : 2 ^ 5 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 3) = 1433987709 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987709 = 6 * 238997951 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987709 6 238997951 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y4
  (h_ts : 2 ^ 5 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 4) = 1433987653 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987653 = 6 * 238997942 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987653 6 238997942 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y5
  (h_ts : 2 ^ 5 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 5) = 1433987541 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987541 = 6 * 238997923 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987541 6 238997923 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y6
  (h_ts : 2 ^ 5 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 6) = 1433987317 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987317 = 6 * 238997886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987317 6 238997886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y7
  (h_ts : 2 ^ 5 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 7) = 1433986869 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986869 = 6 * 238997811 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433986869 6 238997811 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y8
  (h_ts : 2 ^ 5 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 8) = 1433985973 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985973 = 6 * 238997662 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985973 6 238997662 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y9
  (h_ts : 2 ^ 5 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 9) = 1433984181 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984181 = 6 * 238997363 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433984181 6 238997363 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y10
  (h_ts : 2 ^ 5 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 10) = 1433980597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433980597 = 6 * 238996766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433980597 6 238996766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y11
  (h_ts : 2 ^ 5 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 11) = 1433973429 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973429 = 6 * 238995571 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433973429 6 238995571 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y12
  (h_ts : 2 ^ 5 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 12) = 1433959093 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433959093 = 6 * 238993182 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433959093 6 238993182 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y13
  (h_ts : 2 ^ 5 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 13) = 1433930421 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930421 = 6 * 238988403 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433930421 6 238988403 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y14
  (h_ts : 2 ^ 5 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 14) = 1433873077 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433873077 = 6 * 238978846 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433873077 6 238978846 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y15
  (h_ts : 2 ^ 5 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 15) = 1433758389 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758389 = 6 * 238959731 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433758389 6 238959731 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y16
  (h_ts : 2 ^ 5 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 16) = 1433529013 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433529013 = 6 * 238921502 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433529013 6 238921502 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y17
  (h_ts : 2 ^ 5 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 17) = 1433070261 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070261 = 6 * 238845043 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433070261 6 238845043 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y18
  (h_ts : 2 ^ 5 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 18) = 1432152757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432152757 = 6 * 238692126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432152757 6 238692126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y19
  (h_ts : 2 ^ 5 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 19) = 1430317749 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317749 = 6 * 238386291 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430317749 6 238386291 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y20
  (h_ts : 2 ^ 5 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 20) = 1426647733 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426647733 = 6 * 237774622 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426647733 6 237774622 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y21
  (h_ts : 2 ^ 5 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 21) = 1419307701 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307701 = 6 * 236551283 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419307701 6 236551283 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y22
  (h_ts : 2 ^ 5 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 22) = 1404627637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404627637 = 6 * 234104606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404627637 6 234104606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y23
  (h_ts : 2 ^ 5 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 23) = 1375267509 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267509 = 6 * 229211251 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375267509 6 229211251 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y24
  (h_ts : 2 ^ 5 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 24) = 1316547253 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316547253 = 6 * 219424542 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316547253 6 219424542 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y25
  (h_ts : 2 ^ 5 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 25) = 1199106741 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106741 = 6 * 199851123 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199106741 6 199851123 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y26
  (h_ts : 2 ^ 5 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 26) = 964225717 := by decide
  rw [h_sub] at hp6
  have h_eq : 964225717 = 6 * 160704286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964225717 6 160704286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y27
  (h_ts : 2 ^ 5 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 5 + 7 * 2 ^ 27) = 494463669 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463669 = 6 * 82410611 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494463669 6 82410611 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x5_y28
  (h_ts : 2 ^ 5 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048224 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x5_y29
  (h_ts : 2 ^ 5 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096416 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x5_y30
  (h_ts : 2 ^ 5 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192800 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x6_y1
  (h_ts : 2 ^ 6 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 1) = 1433987719 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987719 = 6 * 238997953 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987719 6 238997953 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y2
  (h_ts : 2 ^ 6 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 2) = 1433987705 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987705 = 5 * 286797541 := by decide
  have hd : 5 ∣ 1433987705 := ⟨286797541, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433987705 := by decide
  exact (not_prime_of_dvd 1433987705 5 hd h1 h2) hp

lemma proof_x6_y3
  (h_ts : 2 ^ 6 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 3) = 1433987677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987677 = 6 * 238997946 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987677 6 238997946 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y4
  (h_ts : 2 ^ 6 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 4) = 1433987621 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987621 = 11 * 130362511 := by decide
  have hd : 11 ∣ 1433987621 := ⟨130362511, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433987621 := by decide
  exact (not_prime_of_dvd 1433987621 11 hd h1 h2) hp

lemma proof_x6_y5
  (h_ts : 2 ^ 6 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 5) = 1433987509 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987509 = 6 * 238997918 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987509 6 238997918 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y6
  (h_ts : 2 ^ 6 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 6) = 1433987285 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987285 = 5 * 286797457 := by decide
  have hd : 5 ∣ 1433987285 := ⟨286797457, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433987285 := by decide
  exact (not_prime_of_dvd 1433987285 5 hd h1 h2) hp

lemma proof_x6_y7
  (h_ts : 2 ^ 6 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 7) = 1433986837 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986837 = 6 * 238997806 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986837 6 238997806 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y8
  (h_ts : 2 ^ 6 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 8) = 1433985941 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433985941 = 31 * 46257611 := by decide
  have hd : 31 ∣ 1433985941 := ⟨46257611, hd_eq⟩
  have h1 : 1 < 31 := by decide
  have h2 : 31 < 1433985941 := by decide
  exact (not_prime_of_dvd 1433985941 31 hd h1 h2) hp

lemma proof_x6_y9
  (h_ts : 2 ^ 6 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 9) = 1433984149 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984149 = 6 * 238997358 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433984149 6 238997358 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y10
  (h_ts : 2 ^ 6 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 10) = 1433980565 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433980565 = 5 * 286796113 := by decide
  have hd : 5 ∣ 1433980565 := ⟨286796113, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433980565 := by decide
  exact (not_prime_of_dvd 1433980565 5 hd h1 h2) hp

lemma proof_x6_y11
  (h_ts : 2 ^ 6 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 11) = 1433973397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973397 = 6 * 238995566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433973397 6 238995566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y12
  (h_ts : 2 ^ 6 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 12) = 1433959061 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433959061 = 17 * 84350533 := by decide
  have hd : 17 ∣ 1433959061 := ⟨84350533, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1433959061 := by decide
  exact (not_prime_of_dvd 1433959061 17 hd h1 h2) hp

lemma proof_x6_y13
  (h_ts : 2 ^ 6 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 13) = 1433930389 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930389 = 6 * 238988398 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433930389 6 238988398 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y14
  (h_ts : 2 ^ 6 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 14) = 1433873045 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433873045 = 5 * 286774609 := by decide
  have hd : 5 ∣ 1433873045 := ⟨286774609, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433873045 := by decide
  exact (not_prime_of_dvd 1433873045 5 hd h1 h2) hp

lemma proof_x6_y15
  (h_ts : 2 ^ 6 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 15) = 1433758357 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758357 = 6 * 238959726 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433758357 6 238959726 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y16
  (h_ts : 2 ^ 6 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 16) = 1433528981 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433528981 = 23 * 62327347 := by decide
  have hd : 23 ∣ 1433528981 := ⟨62327347, hd_eq⟩
  have h1 : 1 < 23 := by decide
  have h2 : 23 < 1433528981 := by decide
  exact (not_prime_of_dvd 1433528981 23 hd h1 h2) hp

lemma proof_x6_y17
  (h_ts : 2 ^ 6 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 17) = 1433070229 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070229 = 6 * 238845038 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433070229 6 238845038 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y18
  (h_ts : 2 ^ 6 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 18) = 1432152725 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432152725 = 5 * 286430545 := by decide
  have hd : 5 ∣ 1432152725 := ⟨286430545, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1432152725 := by decide
  exact (not_prime_of_dvd 1432152725 5 hd h1 h2) hp

lemma proof_x6_y19
  (h_ts : 2 ^ 6 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 19) = 1430317717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317717 = 6 * 238386286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430317717 6 238386286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y20
  (h_ts : 2 ^ 6 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 20) = 1426647701 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426647701 = 17 * 83920453 := by decide
  have hd : 17 ∣ 1426647701 := ⟨83920453, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1426647701 := by decide
  exact (not_prime_of_dvd 1426647701 17 hd h1 h2) hp

lemma proof_x6_y21
  (h_ts : 2 ^ 6 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 21) = 1419307669 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307669 = 6 * 236551278 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419307669 6 236551278 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y22
  (h_ts : 2 ^ 6 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 22) = 1404627605 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404627605 = 5 * 280925521 := by decide
  have hd : 5 ∣ 1404627605 := ⟨280925521, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1404627605 := by decide
  exact (not_prime_of_dvd 1404627605 5 hd h1 h2) hp

lemma proof_x6_y23
  (h_ts : 2 ^ 6 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 23) = 1375267477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267477 = 6 * 229211246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375267477 6 229211246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y24
  (h_ts : 2 ^ 6 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 24) = 1316547221 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316547221 = 11 * 119686111 := by decide
  have hd : 11 ∣ 1316547221 := ⟨119686111, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1316547221 := by decide
  exact (not_prime_of_dvd 1316547221 11 hd h1 h2) hp

lemma proof_x6_y25
  (h_ts : 2 ^ 6 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 25) = 1199106709 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106709 = 6 * 199851118 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199106709 6 199851118 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y26
  (h_ts : 2 ^ 6 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 26) = 964225685 := by decide
  rw [h_sub] at hp
  have hd_eq : 964225685 = 5 * 192845137 := by decide
  have hd : 5 ∣ 964225685 := ⟨192845137, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 964225685 := by decide
  exact (not_prime_of_dvd 964225685 5 hd h1 h2) hp

lemma proof_x6_y27
  (h_ts : 2 ^ 6 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 6 + 7 * 2 ^ 27) = 494463637 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463637 = 6 * 82410606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494463637 6 82410606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x6_y28
  (h_ts : 2 ^ 6 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048256 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x6_y29
  (h_ts : 2 ^ 6 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096448 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x6_y30
  (h_ts : 2 ^ 6 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192832 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x7_y1
  (h_ts : 2 ^ 7 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 1) = 1433987655 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987655 = 6 * 238997942 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987655 6 238997942 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y2
  (h_ts : 2 ^ 7 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 2) = 1433987641 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987641 = 6 * 238997940 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987641 6 238997940 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y3
  (h_ts : 2 ^ 7 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 3) = 1433987613 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987613 = 6 * 238997935 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987613 6 238997935 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y4
  (h_ts : 2 ^ 7 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 4) = 1433987557 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987557 = 6 * 238997926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987557 6 238997926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y5
  (h_ts : 2 ^ 7 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 5) = 1433987445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987445 = 6 * 238997907 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987445 6 238997907 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y6
  (h_ts : 2 ^ 7 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 6) = 1433987221 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987221 = 6 * 238997870 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987221 6 238997870 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y7
  (h_ts : 2 ^ 7 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 7) = 1433986773 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986773 = 6 * 238997795 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433986773 6 238997795 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y8
  (h_ts : 2 ^ 7 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 8) = 1433985877 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985877 = 6 * 238997646 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985877 6 238997646 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y9
  (h_ts : 2 ^ 7 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 9) = 1433984085 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984085 = 6 * 238997347 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433984085 6 238997347 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y10
  (h_ts : 2 ^ 7 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 10) = 1433980501 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433980501 = 6 * 238996750 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433980501 6 238996750 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y11
  (h_ts : 2 ^ 7 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 11) = 1433973333 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973333 = 6 * 238995555 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433973333 6 238995555 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y12
  (h_ts : 2 ^ 7 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 12) = 1433958997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433958997 = 6 * 238993166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433958997 6 238993166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y13
  (h_ts : 2 ^ 7 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 13) = 1433930325 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930325 = 6 * 238988387 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433930325 6 238988387 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y14
  (h_ts : 2 ^ 7 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 14) = 1433872981 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433872981 = 6 * 238978830 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433872981 6 238978830 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y15
  (h_ts : 2 ^ 7 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 15) = 1433758293 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758293 = 6 * 238959715 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433758293 6 238959715 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y16
  (h_ts : 2 ^ 7 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 16) = 1433528917 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433528917 = 6 * 238921486 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433528917 6 238921486 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y17
  (h_ts : 2 ^ 7 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 17) = 1433070165 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070165 = 6 * 238845027 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433070165 6 238845027 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y18
  (h_ts : 2 ^ 7 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 18) = 1432152661 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432152661 = 6 * 238692110 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432152661 6 238692110 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y19
  (h_ts : 2 ^ 7 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 19) = 1430317653 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317653 = 6 * 238386275 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430317653 6 238386275 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y20
  (h_ts : 2 ^ 7 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 20) = 1426647637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426647637 = 6 * 237774606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426647637 6 237774606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y21
  (h_ts : 2 ^ 7 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 21) = 1419307605 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307605 = 6 * 236551267 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419307605 6 236551267 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y22
  (h_ts : 2 ^ 7 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 22) = 1404627541 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404627541 = 6 * 234104590 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404627541 6 234104590 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y23
  (h_ts : 2 ^ 7 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 23) = 1375267413 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267413 = 6 * 229211235 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375267413 6 229211235 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y24
  (h_ts : 2 ^ 7 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 24) = 1316547157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316547157 = 6 * 219424526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316547157 6 219424526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y25
  (h_ts : 2 ^ 7 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 25) = 1199106645 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106645 = 6 * 199851107 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199106645 6 199851107 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y26
  (h_ts : 2 ^ 7 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 26) = 964225621 := by decide
  rw [h_sub] at hp6
  have h_eq : 964225621 = 6 * 160704270 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964225621 6 160704270 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y27
  (h_ts : 2 ^ 7 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 7 + 7 * 2 ^ 27) = 494463573 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463573 = 6 * 82410595 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494463573 6 82410595 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x7_y28
  (h_ts : 2 ^ 7 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048320 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x7_y29
  (h_ts : 2 ^ 7 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096512 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x7_y30
  (h_ts : 2 ^ 7 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516192896 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x8_y1
  (h_ts : 2 ^ 8 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 1) = 1433987527 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987527 = 6 * 238997921 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987527 6 238997921 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y2
  (h_ts : 2 ^ 8 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 2) = 1433987513 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987513 = 7 * 204855359 := by decide
  have hd : 7 ∣ 1433987513 := ⟨204855359, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433987513 := by decide
  exact (not_prime_of_dvd 1433987513 7 hd h1 h2) hp

lemma proof_x8_y3
  (h_ts : 2 ^ 8 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 3) = 1433987485 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987485 = 6 * 238997914 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987485 6 238997914 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y4
  (h_ts : 2 ^ 8 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 4) = 1433987429 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987429 = 7 * 204855347 := by decide
  have hd : 7 ∣ 1433987429 := ⟨204855347, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433987429 := by decide
  exact (not_prime_of_dvd 1433987429 7 hd h1 h2) hp

lemma proof_x8_y5
  (h_ts : 2 ^ 8 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 5) = 1433987317 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987317 = 6 * 238997886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987317 6 238997886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y6
  (h_ts : 2 ^ 8 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 6) = 1433987093 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433987093 = 7 * 204855299 := by decide
  have hd : 7 ∣ 1433987093 := ⟨204855299, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433987093 := by decide
  exact (not_prime_of_dvd 1433987093 7 hd h1 h2) hp

lemma proof_x8_y7
  (h_ts : 2 ^ 8 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 7) = 1433986645 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986645 = 6 * 238997774 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986645 6 238997774 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y8
  (h_ts : 2 ^ 8 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 8) = 1433985749 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433985749 = 7 * 204855107 := by decide
  have hd : 7 ∣ 1433985749 := ⟨204855107, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433985749 := by decide
  exact (not_prime_of_dvd 1433985749 7 hd h1 h2) hp

lemma proof_x8_y9
  (h_ts : 2 ^ 8 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 9) = 1433983957 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983957 = 6 * 238997326 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433983957 6 238997326 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y10
  (h_ts : 2 ^ 8 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 10) = 1433980373 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433980373 = 7 * 204854339 := by decide
  have hd : 7 ∣ 1433980373 := ⟨204854339, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433980373 := by decide
  exact (not_prime_of_dvd 1433980373 7 hd h1 h2) hp

lemma proof_x8_y11
  (h_ts : 2 ^ 8 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 11) = 1433973205 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433973205 = 6 * 238995534 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433973205 6 238995534 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y12
  (h_ts : 2 ^ 8 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 12) = 1433958869 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433958869 = 7 * 204851267 := by decide
  have hd : 7 ∣ 1433958869 := ⟨204851267, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433958869 := by decide
  exact (not_prime_of_dvd 1433958869 7 hd h1 h2) hp

lemma proof_x8_y13
  (h_ts : 2 ^ 8 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 13) = 1433930197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433930197 = 6 * 238988366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433930197 6 238988366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y14
  (h_ts : 2 ^ 8 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 14) = 1433872853 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433872853 = 7 * 204838979 := by decide
  have hd : 7 ∣ 1433872853 := ⟨204838979, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433872853 := by decide
  exact (not_prime_of_dvd 1433872853 7 hd h1 h2) hp

lemma proof_x8_y15
  (h_ts : 2 ^ 8 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 15) = 1433758165 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433758165 = 6 * 238959694 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433758165 6 238959694 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y16
  (h_ts : 2 ^ 8 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 16) = 1433528789 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433528789 = 7 * 204789827 := by decide
  have hd : 7 ∣ 1433528789 := ⟨204789827, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433528789 := by decide
  exact (not_prime_of_dvd 1433528789 7 hd h1 h2) hp

lemma proof_x8_y17
  (h_ts : 2 ^ 8 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 17) = 1433070037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433070037 = 6 * 238845006 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433070037 6 238845006 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y18
  (h_ts : 2 ^ 8 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 18) = 1432152533 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432152533 = 7 * 204593219 := by decide
  have hd : 7 ∣ 1432152533 := ⟨204593219, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432152533 := by decide
  exact (not_prime_of_dvd 1432152533 7 hd h1 h2) hp

lemma proof_x8_y19
  (h_ts : 2 ^ 8 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 19) = 1430317525 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317525 = 6 * 238386254 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430317525 6 238386254 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y20
  (h_ts : 2 ^ 8 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 20) = 1426647509 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426647509 = 7 * 203806787 := by decide
  have hd : 7 ∣ 1426647509 := ⟨203806787, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1426647509 := by decide
  exact (not_prime_of_dvd 1426647509 7 hd h1 h2) hp

lemma proof_x8_y21
  (h_ts : 2 ^ 8 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 21) = 1419307477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307477 = 6 * 236551246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419307477 6 236551246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y22
  (h_ts : 2 ^ 8 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 22) = 1404627413 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404627413 = 7 * 200661059 := by decide
  have hd : 7 ∣ 1404627413 := ⟨200661059, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1404627413 := by decide
  exact (not_prime_of_dvd 1404627413 7 hd h1 h2) hp

lemma proof_x8_y23
  (h_ts : 2 ^ 8 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 23) = 1375267285 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267285 = 6 * 229211214 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375267285 6 229211214 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y24
  (h_ts : 2 ^ 8 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 24) = 1316547029 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316547029 = 7 * 188078147 := by decide
  have hd : 7 ∣ 1316547029 := ⟨188078147, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1316547029 := by decide
  exact (not_prime_of_dvd 1316547029 7 hd h1 h2) hp

lemma proof_x8_y25
  (h_ts : 2 ^ 8 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 25) = 1199106517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106517 = 6 * 199851086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199106517 6 199851086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y26
  (h_ts : 2 ^ 8 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 26) = 964225493 := by decide
  rw [h_sub] at hp
  have hd_eq : 964225493 = 7 * 137746499 := by decide
  have hd : 7 ∣ 964225493 := ⟨137746499, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 964225493 := by decide
  exact (not_prime_of_dvd 964225493 7 hd h1 h2) hp

lemma proof_x8_y27
  (h_ts : 2 ^ 8 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 8 + 7 * 2 ^ 27) = 494463445 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463445 = 6 * 82410574 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494463445 6 82410574 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x8_y28
  (h_ts : 2 ^ 8 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048448 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x8_y29
  (h_ts : 2 ^ 8 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096640 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x8_y30
  (h_ts : 2 ^ 8 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516193024 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x9_y1
  (h_ts : 2 ^ 9 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 1) = 1433987271 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987271 = 6 * 238997878 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987271 6 238997878 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y2
  (h_ts : 2 ^ 9 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 2) = 1433987257 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987257 = 6 * 238997876 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987257 6 238997876 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y3
  (h_ts : 2 ^ 9 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 3) = 1433987229 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987229 = 6 * 238997871 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987229 6 238997871 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y4
  (h_ts : 2 ^ 9 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 4) = 1433987173 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987173 = 6 * 238997862 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433987173 6 238997862 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y5
  (h_ts : 2 ^ 9 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 5) = 1433987061 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433987061 = 6 * 238997843 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433987061 6 238997843 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y6
  (h_ts : 2 ^ 9 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 6) = 1433986837 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986837 = 6 * 238997806 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986837 6 238997806 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y7
  (h_ts : 2 ^ 9 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 7) = 1433986389 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986389 = 6 * 238997731 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433986389 6 238997731 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y8
  (h_ts : 2 ^ 9 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 8) = 1433985493 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985493 = 6 * 238997582 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985493 6 238997582 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y9
  (h_ts : 2 ^ 9 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 9) = 1433983701 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983701 = 6 * 238997283 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433983701 6 238997283 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y10
  (h_ts : 2 ^ 9 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 10) = 1433980117 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433980117 = 6 * 238996686 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433980117 6 238996686 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y11
  (h_ts : 2 ^ 9 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 11) = 1433972949 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433972949 = 6 * 238995491 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433972949 6 238995491 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y12
  (h_ts : 2 ^ 9 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 12) = 1433958613 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433958613 = 6 * 238993102 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433958613 6 238993102 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y13
  (h_ts : 2 ^ 9 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 13) = 1433929941 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433929941 = 6 * 238988323 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433929941 6 238988323 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y14
  (h_ts : 2 ^ 9 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 14) = 1433872597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433872597 = 6 * 238978766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433872597 6 238978766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y15
  (h_ts : 2 ^ 9 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 15) = 1433757909 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433757909 = 6 * 238959651 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433757909 6 238959651 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y16
  (h_ts : 2 ^ 9 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 16) = 1433528533 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433528533 = 6 * 238921422 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433528533 6 238921422 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y17
  (h_ts : 2 ^ 9 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 17) = 1433069781 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433069781 = 6 * 238844963 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433069781 6 238844963 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y18
  (h_ts : 2 ^ 9 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 18) = 1432152277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432152277 = 6 * 238692046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432152277 6 238692046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y19
  (h_ts : 2 ^ 9 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 19) = 1430317269 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430317269 = 6 * 238386211 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430317269 6 238386211 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y20
  (h_ts : 2 ^ 9 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 20) = 1426647253 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426647253 = 6 * 237774542 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426647253 6 237774542 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y21
  (h_ts : 2 ^ 9 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 21) = 1419307221 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419307221 = 6 * 236551203 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419307221 6 236551203 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y22
  (h_ts : 2 ^ 9 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 22) = 1404627157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404627157 = 6 * 234104526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404627157 6 234104526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y23
  (h_ts : 2 ^ 9 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 23) = 1375267029 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375267029 = 6 * 229211171 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375267029 6 229211171 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y24
  (h_ts : 2 ^ 9 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 24) = 1316546773 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316546773 = 6 * 219424462 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316546773 6 219424462 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y25
  (h_ts : 2 ^ 9 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 25) = 1199106261 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199106261 = 6 * 199851043 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199106261 6 199851043 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y26
  (h_ts : 2 ^ 9 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 26) = 964225237 := by decide
  rw [h_sub] at hp6
  have h_eq : 964225237 = 6 * 160704206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964225237 6 160704206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y27
  (h_ts : 2 ^ 9 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 9 + 7 * 2 ^ 27) = 494463189 := by decide
  rw [h_sub] at hp6
  have h_eq : 494463189 = 6 * 82410531 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494463189 6 82410531 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x9_y28
  (h_ts : 2 ^ 9 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879048704 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x9_y29
  (h_ts : 2 ^ 9 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758096896 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x9_y30
  (h_ts : 2 ^ 9 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516193280 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x10_y1
  (h_ts : 2 ^ 10 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 1) = 1433986759 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986759 = 6 * 238997793 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986759 6 238997793 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y2
  (h_ts : 2 ^ 10 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 2) = 1433986745 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433986745 = 5 * 286797349 := by decide
  have hd : 5 ∣ 1433986745 := ⟨286797349, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433986745 := by decide
  exact (not_prime_of_dvd 1433986745 5 hd h1 h2) hp

lemma proof_x10_y3
  (h_ts : 2 ^ 10 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 3) = 1433986717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986717 = 6 * 238997786 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986717 6 238997786 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y4
  (h_ts : 2 ^ 10 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 4) = 1433986661 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433986661 = 43 * 33348527 := by decide
  have hd : 43 ∣ 1433986661 := ⟨33348527, hd_eq⟩
  have h1 : 1 < 43 := by decide
  have h2 : 43 < 1433986661 := by decide
  exact (not_prime_of_dvd 1433986661 43 hd h1 h2) hp

lemma proof_x10_y5
  (h_ts : 2 ^ 10 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 5) = 1433986549 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433986549 = 6 * 238997758 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433986549 6 238997758 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y6
  (h_ts : 2 ^ 10 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 6) = 1433986325 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433986325 = 5 * 286797265 := by decide
  have hd : 5 ∣ 1433986325 := ⟨286797265, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433986325 := by decide
  exact (not_prime_of_dvd 1433986325 5 hd h1 h2) hp

lemma proof_x10_y7
  (h_ts : 2 ^ 10 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 7) = 1433985877 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985877 = 6 * 238997646 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985877 6 238997646 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y8
  (h_ts : 2 ^ 10 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 8) = 1433984981 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433984981 = 11 * 130362271 := by decide
  have hd : 11 ∣ 1433984981 := ⟨130362271, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433984981 := by decide
  exact (not_prime_of_dvd 1433984981 11 hd h1 h2) hp

lemma proof_x10_y9
  (h_ts : 2 ^ 10 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 9) = 1433983189 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983189 = 6 * 238997198 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433983189 6 238997198 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y10
  (h_ts : 2 ^ 10 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 10) = 1433979605 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433979605 = 5 * 286795921 := by decide
  have hd : 5 ∣ 1433979605 := ⟨286795921, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433979605 := by decide
  exact (not_prime_of_dvd 1433979605 5 hd h1 h2) hp

lemma proof_x10_y11
  (h_ts : 2 ^ 10 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 11) = 1433972437 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433972437 = 6 * 238995406 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433972437 6 238995406 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y12
  (h_ts : 2 ^ 10 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 12) = 1433958101 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433958101 = 19 * 75471479 := by decide
  have hd : 19 ∣ 1433958101 := ⟨75471479, hd_eq⟩
  have h1 : 1 < 19 := by decide
  have h2 : 19 < 1433958101 := by decide
  exact (not_prime_of_dvd 1433958101 19 hd h1 h2) hp

lemma proof_x10_y13
  (h_ts : 2 ^ 10 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 13) = 1433929429 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433929429 = 6 * 238988238 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433929429 6 238988238 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y14
  (h_ts : 2 ^ 10 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 14) = 1433872085 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433872085 = 5 * 286774417 := by decide
  have hd : 5 ∣ 1433872085 := ⟨286774417, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433872085 := by decide
  exact (not_prime_of_dvd 1433872085 5 hd h1 h2) hp

lemma proof_x10_y15
  (h_ts : 2 ^ 10 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 15) = 1433757397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433757397 = 6 * 238959566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433757397 6 238959566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y16
  (h_ts : 2 ^ 10 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 16) = 1433528021 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433528021 = 1753 * 817757 := by decide
  have hd : 1753 ∣ 1433528021 := ⟨817757, hd_eq⟩
  have h1 : 1 < 1753 := by decide
  have h2 : 1753 < 1433528021 := by decide
  exact (not_prime_of_dvd 1433528021 1753 hd h1 h2) hp

lemma proof_x10_y17
  (h_ts : 2 ^ 10 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 17) = 1433069269 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433069269 = 6 * 238844878 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433069269 6 238844878 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y18
  (h_ts : 2 ^ 10 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 18) = 1432151765 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432151765 = 5 * 286430353 := by decide
  have hd : 5 ∣ 1432151765 := ⟨286430353, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1432151765 := by decide
  exact (not_prime_of_dvd 1432151765 5 hd h1 h2) hp

lemma proof_x10_y19
  (h_ts : 2 ^ 10 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 19) = 1430316757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430316757 = 6 * 238386126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430316757 6 238386126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y20
  (h_ts : 2 ^ 10 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 20) = 1426646741 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426646741 = 13 * 109742057 := by decide
  have hd : 13 ∣ 1426646741 := ⟨109742057, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1426646741 := by decide
  exact (not_prime_of_dvd 1426646741 13 hd h1 h2) hp

lemma proof_x10_y21
  (h_ts : 2 ^ 10 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 21) = 1419306709 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419306709 = 6 * 236551118 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419306709 6 236551118 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y22
  (h_ts : 2 ^ 10 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 22) = 1404626645 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404626645 = 5 * 280925329 := by decide
  have hd : 5 ∣ 1404626645 := ⟨280925329, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1404626645 := by decide
  exact (not_prime_of_dvd 1404626645 5 hd h1 h2) hp

lemma proof_x10_y23
  (h_ts : 2 ^ 10 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 23) = 1375266517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375266517 = 6 * 229211086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375266517 6 229211086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y24
  (h_ts : 2 ^ 10 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 24) = 1316546261 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316546261 = 877 * 1501193 := by decide
  have hd : 877 ∣ 1316546261 := ⟨1501193, hd_eq⟩
  have h1 : 1 < 877 := by decide
  have h2 : 877 < 1316546261 := by decide
  exact (not_prime_of_dvd 1316546261 877 hd h1 h2) hp

lemma proof_x10_y25
  (h_ts : 2 ^ 10 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 25) = 1199105749 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199105749 = 6 * 199850958 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199105749 6 199850958 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y26
  (h_ts : 2 ^ 10 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 26) = 964224725 := by decide
  rw [h_sub] at hp
  have hd_eq : 964224725 = 5 * 192844945 := by decide
  have hd : 5 ∣ 964224725 := ⟨192844945, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 964224725 := by decide
  exact (not_prime_of_dvd 964224725 5 hd h1 h2) hp

lemma proof_x10_y27
  (h_ts : 2 ^ 10 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 10 + 7 * 2 ^ 27) = 494462677 := by decide
  rw [h_sub] at hp6
  have h_eq : 494462677 = 6 * 82410446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494462677 6 82410446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x10_y28
  (h_ts : 2 ^ 10 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879049216 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x10_y29
  (h_ts : 2 ^ 10 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758097408 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x10_y30
  (h_ts : 2 ^ 10 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516193792 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x11_y1
  (h_ts : 2 ^ 11 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 1) = 1433985735 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985735 = 6 * 238997622 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433985735 6 238997622 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y2
  (h_ts : 2 ^ 11 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 2) = 1433985721 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985721 = 6 * 238997620 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985721 6 238997620 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y3
  (h_ts : 2 ^ 11 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 3) = 1433985693 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985693 = 6 * 238997615 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433985693 6 238997615 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y4
  (h_ts : 2 ^ 11 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 4) = 1433985637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985637 = 6 * 238997606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985637 6 238997606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y5
  (h_ts : 2 ^ 11 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 5) = 1433985525 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985525 = 6 * 238997587 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433985525 6 238997587 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y6
  (h_ts : 2 ^ 11 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 6) = 1433985301 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433985301 = 6 * 238997550 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433985301 6 238997550 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y7
  (h_ts : 2 ^ 11 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 7) = 1433984853 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433984853 = 6 * 238997475 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433984853 6 238997475 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y8
  (h_ts : 2 ^ 11 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 8) = 1433983957 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983957 = 6 * 238997326 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433983957 6 238997326 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y9
  (h_ts : 2 ^ 11 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 9) = 1433982165 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433982165 = 6 * 238997027 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433982165 6 238997027 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y10
  (h_ts : 2 ^ 11 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 10) = 1433978581 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433978581 = 6 * 238996430 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433978581 6 238996430 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y11
  (h_ts : 2 ^ 11 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 11) = 1433971413 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433971413 = 6 * 238995235 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433971413 6 238995235 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y12
  (h_ts : 2 ^ 11 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 12) = 1433957077 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433957077 = 6 * 238992846 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433957077 6 238992846 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y13
  (h_ts : 2 ^ 11 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 13) = 1433928405 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433928405 = 6 * 238988067 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433928405 6 238988067 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y14
  (h_ts : 2 ^ 11 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 14) = 1433871061 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433871061 = 6 * 238978510 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433871061 6 238978510 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y15
  (h_ts : 2 ^ 11 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 15) = 1433756373 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433756373 = 6 * 238959395 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433756373 6 238959395 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y16
  (h_ts : 2 ^ 11 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 16) = 1433526997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433526997 = 6 * 238921166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433526997 6 238921166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y17
  (h_ts : 2 ^ 11 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 17) = 1433068245 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433068245 = 6 * 238844707 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433068245 6 238844707 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y18
  (h_ts : 2 ^ 11 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 18) = 1432150741 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432150741 = 6 * 238691790 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432150741 6 238691790 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y19
  (h_ts : 2 ^ 11 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 19) = 1430315733 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430315733 = 6 * 238385955 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430315733 6 238385955 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y20
  (h_ts : 2 ^ 11 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 20) = 1426645717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426645717 = 6 * 237774286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426645717 6 237774286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y21
  (h_ts : 2 ^ 11 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 21) = 1419305685 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419305685 = 6 * 236550947 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419305685 6 236550947 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y22
  (h_ts : 2 ^ 11 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 22) = 1404625621 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404625621 = 6 * 234104270 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404625621 6 234104270 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y23
  (h_ts : 2 ^ 11 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 23) = 1375265493 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375265493 = 6 * 229210915 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375265493 6 229210915 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y24
  (h_ts : 2 ^ 11 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 24) = 1316545237 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316545237 = 6 * 219424206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316545237 6 219424206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y25
  (h_ts : 2 ^ 11 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 25) = 1199104725 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199104725 = 6 * 199850787 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199104725 6 199850787 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y26
  (h_ts : 2 ^ 11 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 26) = 964223701 := by decide
  rw [h_sub] at hp6
  have h_eq : 964223701 = 6 * 160703950 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964223701 6 160703950 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y27
  (h_ts : 2 ^ 11 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 11 + 7 * 2 ^ 27) = 494461653 := by decide
  rw [h_sub] at hp6
  have h_eq : 494461653 = 6 * 82410275 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494461653 6 82410275 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x11_y28
  (h_ts : 2 ^ 11 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879050240 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x11_y29
  (h_ts : 2 ^ 11 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758098432 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x11_y30
  (h_ts : 2 ^ 11 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516194816 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x12_y1
  (h_ts : 2 ^ 12 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 1) = 1433983687 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983687 = 6 * 238997281 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433983687 6 238997281 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y2
  (h_ts : 2 ^ 12 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 2) = 1433983673 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433983673 = 113 * 12690121 := by decide
  have hd : 113 ∣ 1433983673 := ⟨12690121, hd_eq⟩
  have h1 : 1 < 113 := by decide
  have h2 : 113 < 1433983673 := by decide
  exact (not_prime_of_dvd 1433983673 113 hd h1 h2) hp

lemma proof_x12_y3
  (h_ts : 2 ^ 12 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 3) = 1433983645 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983645 = 6 * 238997274 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433983645 6 238997274 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y4
  (h_ts : 2 ^ 12 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 4) = 1433983589 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433983589 = 79 * 18151691 := by decide
  have hd : 79 ∣ 1433983589 := ⟨18151691, hd_eq⟩
  have h1 : 1 < 79 := by decide
  have h2 : 79 < 1433983589 := by decide
  exact (not_prime_of_dvd 1433983589 79 hd h1 h2) hp

lemma proof_x12_y5
  (h_ts : 2 ^ 12 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 5) = 1433983477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433983477 = 6 * 238997246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433983477 6 238997246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y6
  (h_ts : 2 ^ 12 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 6) = 1433983253 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433983253 = 4219 * 339887 := by decide
  have hd : 4219 ∣ 1433983253 := ⟨339887, hd_eq⟩
  have h1 : 1 < 4219 := by decide
  have h2 : 4219 < 1433983253 := by decide
  exact (not_prime_of_dvd 1433983253 4219 hd h1 h2) hp

lemma proof_x12_y7
  (h_ts : 2 ^ 12 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 7) = 1433982805 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433982805 = 6 * 238997134 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433982805 6 238997134 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y8
  (h_ts : 2 ^ 12 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 8) = 1433981909 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433981909 = 17 * 84351877 := by decide
  have hd : 17 ∣ 1433981909 := ⟨84351877, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1433981909 := by decide
  exact (not_prime_of_dvd 1433981909 17 hd h1 h2) hp

lemma proof_x12_y9
  (h_ts : 2 ^ 12 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 9) = 1433980117 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433980117 = 6 * 238996686 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433980117 6 238996686 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y10
  (h_ts : 2 ^ 12 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 10) = 1433976533 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433976533 = 11 * 130361503 := by decide
  have hd : 11 ∣ 1433976533 := ⟨130361503, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433976533 := by decide
  exact (not_prime_of_dvd 1433976533 11 hd h1 h2) hp

lemma proof_x12_y11
  (h_ts : 2 ^ 12 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 11) = 1433969365 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433969365 = 6 * 238994894 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433969365 6 238994894 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y12
  (h_ts : 2 ^ 12 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 12) = 1433955029 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433955029 = 13 * 110304233 := by decide
  have hd : 13 ∣ 1433955029 := ⟨110304233, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1433955029 := by decide
  exact (not_prime_of_dvd 1433955029 13 hd h1 h2) hp

lemma proof_x12_y13
  (h_ts : 2 ^ 12 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 13) = 1433926357 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433926357 = 6 * 238987726 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433926357 6 238987726 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y14
  (h_ts : 2 ^ 12 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 14) = 1433869013 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433869013 = 23 * 62342131 := by decide
  have hd : 23 ∣ 1433869013 := ⟨62342131, hd_eq⟩
  have h1 : 1 < 23 := by decide
  have h2 : 23 < 1433869013 := by decide
  exact (not_prime_of_dvd 1433869013 23 hd h1 h2) hp

lemma proof_x12_y15
  (h_ts : 2 ^ 12 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 15) = 1433754325 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433754325 = 6 * 238959054 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433754325 6 238959054 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y16
  (h_ts : 2 ^ 12 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 16) = 1433524949 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433524949 = 17 * 84324997 := by decide
  have hd : 17 ∣ 1433524949 := ⟨84324997, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1433524949 := by decide
  exact (not_prime_of_dvd 1433524949 17 hd h1 h2) hp

lemma proof_x12_y17
  (h_ts : 2 ^ 12 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 17) = 1433066197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433066197 = 6 * 238844366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433066197 6 238844366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y18
  (h_ts : 2 ^ 12 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 18) = 1432148693 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432148693 = 19 * 75376247 := by decide
  have hd : 19 ∣ 1432148693 := ⟨75376247, hd_eq⟩
  have h1 : 1 < 19 := by decide
  have h2 : 19 < 1432148693 := by decide
  exact (not_prime_of_dvd 1432148693 19 hd h1 h2) hp

lemma proof_x12_y19
  (h_ts : 2 ^ 12 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 19) = 1430313685 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430313685 = 6 * 238385614 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430313685 6 238385614 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y20
  (h_ts : 2 ^ 12 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 20) = 1426643669 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426643669 = 11 * 129694879 := by decide
  have hd : 11 ∣ 1426643669 := ⟨129694879, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1426643669 := by decide
  exact (not_prime_of_dvd 1426643669 11 hd h1 h2) hp

lemma proof_x12_y21
  (h_ts : 2 ^ 12 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 21) = 1419303637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419303637 = 6 * 236550606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419303637 6 236550606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y22
  (h_ts : 2 ^ 12 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 22) = 1404623573 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404623573 = 659 * 2131447 := by decide
  have hd : 659 ∣ 1404623573 := ⟨2131447, hd_eq⟩
  have h1 : 1 < 659 := by decide
  have h2 : 659 < 1404623573 := by decide
  exact (not_prime_of_dvd 1404623573 659 hd h1 h2) hp

lemma proof_x12_y23
  (h_ts : 2 ^ 12 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 23) = 1375263445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375263445 = 6 * 229210574 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375263445 6 229210574 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y24
  (h_ts : 2 ^ 12 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 24) = 1316543189 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316543189 = 13 * 101272553 := by decide
  have hd : 13 ∣ 1316543189 := ⟨101272553, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1316543189 := by decide
  exact (not_prime_of_dvd 1316543189 13 hd h1 h2) hp

lemma proof_x12_y25
  (h_ts : 2 ^ 12 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 25) = 1199102677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199102677 = 6 * 199850446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199102677 6 199850446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y26
  (h_ts : 2 ^ 12 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 26) = 964221653 := by decide
  rw [h_sub] at hp
  have hd_eq : 964221653 = 3167 * 304459 := by decide
  have hd : 3167 ∣ 964221653 := ⟨304459, hd_eq⟩
  have h1 : 1 < 3167 := by decide
  have h2 : 3167 < 964221653 := by decide
  exact (not_prime_of_dvd 964221653 3167 hd h1 h2) hp

lemma proof_x12_y27
  (h_ts : 2 ^ 12 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 12 + 7 * 2 ^ 27) = 494459605 := by decide
  rw [h_sub] at hp6
  have h_eq : 494459605 = 6 * 82409934 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494459605 6 82409934 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x12_y28
  (h_ts : 2 ^ 12 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879052288 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x12_y29
  (h_ts : 2 ^ 12 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758100480 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x12_y30
  (h_ts : 2 ^ 12 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516196864 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x13_y1
  (h_ts : 2 ^ 13 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 1) = 1433979591 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433979591 = 6 * 238996598 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433979591 6 238996598 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y2
  (h_ts : 2 ^ 13 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 2) = 1433979577 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433979577 = 6 * 238996596 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433979577 6 238996596 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y3
  (h_ts : 2 ^ 13 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 3) = 1433979549 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433979549 = 6 * 238996591 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433979549 6 238996591 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y4
  (h_ts : 2 ^ 13 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 4) = 1433979493 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433979493 = 6 * 238996582 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433979493 6 238996582 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y5
  (h_ts : 2 ^ 13 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 5) = 1433979381 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433979381 = 6 * 238996563 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433979381 6 238996563 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y6
  (h_ts : 2 ^ 13 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 6) = 1433979157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433979157 = 6 * 238996526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433979157 6 238996526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y7
  (h_ts : 2 ^ 13 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 7) = 1433978709 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433978709 = 6 * 238996451 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433978709 6 238996451 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y8
  (h_ts : 2 ^ 13 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 8) = 1433977813 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433977813 = 6 * 238996302 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433977813 6 238996302 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y9
  (h_ts : 2 ^ 13 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 9) = 1433976021 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433976021 = 6 * 238996003 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433976021 6 238996003 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y10
  (h_ts : 2 ^ 13 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 10) = 1433972437 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433972437 = 6 * 238995406 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433972437 6 238995406 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y11
  (h_ts : 2 ^ 13 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 11) = 1433965269 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433965269 = 6 * 238994211 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433965269 6 238994211 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y12
  (h_ts : 2 ^ 13 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 12) = 1433950933 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433950933 = 6 * 238991822 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433950933 6 238991822 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y13
  (h_ts : 2 ^ 13 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 13) = 1433922261 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433922261 = 6 * 238987043 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433922261 6 238987043 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y14
  (h_ts : 2 ^ 13 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 14) = 1433864917 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433864917 = 6 * 238977486 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433864917 6 238977486 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y15
  (h_ts : 2 ^ 13 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 15) = 1433750229 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433750229 = 6 * 238958371 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433750229 6 238958371 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y16
  (h_ts : 2 ^ 13 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 16) = 1433520853 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433520853 = 6 * 238920142 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433520853 6 238920142 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y17
  (h_ts : 2 ^ 13 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 17) = 1433062101 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433062101 = 6 * 238843683 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433062101 6 238843683 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y18
  (h_ts : 2 ^ 13 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 18) = 1432144597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432144597 = 6 * 238690766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432144597 6 238690766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y19
  (h_ts : 2 ^ 13 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 19) = 1430309589 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430309589 = 6 * 238384931 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430309589 6 238384931 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y20
  (h_ts : 2 ^ 13 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 20) = 1426639573 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426639573 = 6 * 237773262 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426639573 6 237773262 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y21
  (h_ts : 2 ^ 13 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 21) = 1419299541 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419299541 = 6 * 236549923 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419299541 6 236549923 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y22
  (h_ts : 2 ^ 13 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 22) = 1404619477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404619477 = 6 * 234103246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404619477 6 234103246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y23
  (h_ts : 2 ^ 13 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 23) = 1375259349 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375259349 = 6 * 229209891 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375259349 6 229209891 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y24
  (h_ts : 2 ^ 13 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 24) = 1316539093 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316539093 = 6 * 219423182 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316539093 6 219423182 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y25
  (h_ts : 2 ^ 13 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 25) = 1199098581 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199098581 = 6 * 199849763 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199098581 6 199849763 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y26
  (h_ts : 2 ^ 13 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 26) = 964217557 := by decide
  rw [h_sub] at hp6
  have h_eq : 964217557 = 6 * 160702926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964217557 6 160702926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y27
  (h_ts : 2 ^ 13 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 13 + 7 * 2 ^ 27) = 494455509 := by decide
  rw [h_sub] at hp6
  have h_eq : 494455509 = 6 * 82409251 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494455509 6 82409251 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x13_y28
  (h_ts : 2 ^ 13 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879056384 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x13_y29
  (h_ts : 2 ^ 13 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758104576 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x13_y30
  (h_ts : 2 ^ 13 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516200960 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x14_y1
  (h_ts : 2 ^ 14 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 1) = 1433971399 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433971399 = 6 * 238995233 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433971399 6 238995233 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y2
  (h_ts : 2 ^ 14 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 2) = 1433971385 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433971385 = 5 * 286794277 := by decide
  have hd : 5 ∣ 1433971385 := ⟨286794277, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433971385 := by decide
  exact (not_prime_of_dvd 1433971385 5 hd h1 h2) hp

lemma proof_x14_y3
  (h_ts : 2 ^ 14 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 3) = 1433971357 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433971357 = 6 * 238995226 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433971357 6 238995226 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y4
  (h_ts : 2 ^ 14 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 4) = 1433971301 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433971301 = 7 * 204853043 := by decide
  have hd : 7 ∣ 1433971301 := ⟨204853043, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433971301 := by decide
  exact (not_prime_of_dvd 1433971301 7 hd h1 h2) hp

lemma proof_x14_y5
  (h_ts : 2 ^ 14 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 5) = 1433971189 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433971189 = 6 * 238995198 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433971189 6 238995198 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y6
  (h_ts : 2 ^ 14 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 6) = 1433970965 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433970965 = 5 * 286794193 := by decide
  have hd : 5 ∣ 1433970965 := ⟨286794193, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433970965 := by decide
  exact (not_prime_of_dvd 1433970965 5 hd h1 h2) hp

lemma proof_x14_y7
  (h_ts : 2 ^ 14 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 7) = 1433970517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433970517 = 6 * 238995086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433970517 6 238995086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y8
  (h_ts : 2 ^ 14 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 8) = 1433969621 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433969621 = 7 * 204852803 := by decide
  have hd : 7 ∣ 1433969621 := ⟨204852803, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433969621 := by decide
  exact (not_prime_of_dvd 1433969621 7 hd h1 h2) hp

lemma proof_x14_y9
  (h_ts : 2 ^ 14 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 9) = 1433967829 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433967829 = 6 * 238994638 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433967829 6 238994638 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y10
  (h_ts : 2 ^ 14 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 10) = 1433964245 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433964245 = 5 * 286792849 := by decide
  have hd : 5 ∣ 1433964245 := ⟨286792849, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433964245 := by decide
  exact (not_prime_of_dvd 1433964245 5 hd h1 h2) hp

lemma proof_x14_y11
  (h_ts : 2 ^ 14 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 11) = 1433957077 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433957077 = 6 * 238992846 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433957077 6 238992846 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y12
  (h_ts : 2 ^ 14 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 12) = 1433942741 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433942741 = 7 * 204848963 := by decide
  have hd : 7 ∣ 1433942741 := ⟨204848963, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433942741 := by decide
  exact (not_prime_of_dvd 1433942741 7 hd h1 h2) hp

lemma proof_x14_y13
  (h_ts : 2 ^ 14 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 13) = 1433914069 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433914069 = 6 * 238985678 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433914069 6 238985678 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y14
  (h_ts : 2 ^ 14 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 14) = 1433856725 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433856725 = 5 * 286771345 := by decide
  have hd : 5 ∣ 1433856725 := ⟨286771345, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433856725 := by decide
  exact (not_prime_of_dvd 1433856725 5 hd h1 h2) hp

lemma proof_x14_y15
  (h_ts : 2 ^ 14 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 15) = 1433742037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433742037 = 6 * 238957006 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433742037 6 238957006 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y16
  (h_ts : 2 ^ 14 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 16) = 1433512661 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433512661 = 7 * 204787523 := by decide
  have hd : 7 ∣ 1433512661 := ⟨204787523, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1433512661 := by decide
  exact (not_prime_of_dvd 1433512661 7 hd h1 h2) hp

lemma proof_x14_y17
  (h_ts : 2 ^ 14 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 17) = 1433053909 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433053909 = 6 * 238842318 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433053909 6 238842318 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y18
  (h_ts : 2 ^ 14 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 18) = 1432136405 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432136405 = 5 * 286427281 := by decide
  have hd : 5 ∣ 1432136405 := ⟨286427281, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1432136405 := by decide
  exact (not_prime_of_dvd 1432136405 5 hd h1 h2) hp

lemma proof_x14_y19
  (h_ts : 2 ^ 14 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 19) = 1430301397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430301397 = 6 * 238383566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430301397 6 238383566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y20
  (h_ts : 2 ^ 14 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 20) = 1426631381 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426631381 = 7 * 203804483 := by decide
  have hd : 7 ∣ 1426631381 := ⟨203804483, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1426631381 := by decide
  exact (not_prime_of_dvd 1426631381 7 hd h1 h2) hp

lemma proof_x14_y21
  (h_ts : 2 ^ 14 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 21) = 1419291349 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419291349 = 6 * 236548558 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419291349 6 236548558 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y22
  (h_ts : 2 ^ 14 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 22) = 1404611285 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404611285 = 5 * 280922257 := by decide
  have hd : 5 ∣ 1404611285 := ⟨280922257, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1404611285 := by decide
  exact (not_prime_of_dvd 1404611285 5 hd h1 h2) hp

lemma proof_x14_y23
  (h_ts : 2 ^ 14 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 23) = 1375251157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375251157 = 6 * 229208526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375251157 6 229208526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y24
  (h_ts : 2 ^ 14 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 24) = 1316530901 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316530901 = 7 * 188075843 := by decide
  have hd : 7 ∣ 1316530901 := ⟨188075843, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1316530901 := by decide
  exact (not_prime_of_dvd 1316530901 7 hd h1 h2) hp

lemma proof_x14_y25
  (h_ts : 2 ^ 14 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 25) = 1199090389 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199090389 = 6 * 199848398 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199090389 6 199848398 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y26
  (h_ts : 2 ^ 14 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 26) = 964209365 := by decide
  rw [h_sub] at hp
  have hd_eq : 964209365 = 5 * 192841873 := by decide
  have hd : 5 ∣ 964209365 := ⟨192841873, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 964209365 := by decide
  exact (not_prime_of_dvd 964209365 5 hd h1 h2) hp

lemma proof_x14_y27
  (h_ts : 2 ^ 14 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 14 + 7 * 2 ^ 27) = 494447317 := by decide
  rw [h_sub] at hp6
  have h_eq : 494447317 = 6 * 82407886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494447317 6 82407886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x14_y28
  (h_ts : 2 ^ 14 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879064576 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x14_y29
  (h_ts : 2 ^ 14 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758112768 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x14_y30
  (h_ts : 2 ^ 14 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516209152 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x15_y1
  (h_ts : 2 ^ 15 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 1) = 1433955015 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433955015 = 6 * 238992502 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433955015 6 238992502 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y2
  (h_ts : 2 ^ 15 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 2) = 1433955001 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433955001 = 6 * 238992500 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433955001 6 238992500 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y3
  (h_ts : 2 ^ 15 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 3) = 1433954973 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433954973 = 6 * 238992495 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433954973 6 238992495 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y4
  (h_ts : 2 ^ 15 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 4) = 1433954917 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433954917 = 6 * 238992486 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433954917 6 238992486 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y5
  (h_ts : 2 ^ 15 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 5) = 1433954805 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433954805 = 6 * 238992467 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433954805 6 238992467 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y6
  (h_ts : 2 ^ 15 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 6) = 1433954581 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433954581 = 6 * 238992430 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433954581 6 238992430 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y7
  (h_ts : 2 ^ 15 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 7) = 1433954133 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433954133 = 6 * 238992355 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433954133 6 238992355 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y8
  (h_ts : 2 ^ 15 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 8) = 1433953237 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433953237 = 6 * 238992206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433953237 6 238992206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y9
  (h_ts : 2 ^ 15 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 9) = 1433951445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433951445 = 6 * 238991907 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433951445 6 238991907 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y10
  (h_ts : 2 ^ 15 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 10) = 1433947861 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433947861 = 6 * 238991310 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433947861 6 238991310 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y11
  (h_ts : 2 ^ 15 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 11) = 1433940693 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433940693 = 6 * 238990115 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433940693 6 238990115 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y12
  (h_ts : 2 ^ 15 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 12) = 1433926357 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433926357 = 6 * 238987726 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433926357 6 238987726 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y13
  (h_ts : 2 ^ 15 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 13) = 1433897685 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433897685 = 6 * 238982947 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433897685 6 238982947 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y14
  (h_ts : 2 ^ 15 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 14) = 1433840341 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433840341 = 6 * 238973390 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433840341 6 238973390 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y15
  (h_ts : 2 ^ 15 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 15) = 1433725653 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433725653 = 6 * 238954275 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433725653 6 238954275 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y16
  (h_ts : 2 ^ 15 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 16) = 1433496277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433496277 = 6 * 238916046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433496277 6 238916046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y17
  (h_ts : 2 ^ 15 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 17) = 1433037525 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433037525 = 6 * 238839587 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433037525 6 238839587 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y18
  (h_ts : 2 ^ 15 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 18) = 1432120021 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432120021 = 6 * 238686670 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432120021 6 238686670 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y19
  (h_ts : 2 ^ 15 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 19) = 1430285013 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430285013 = 6 * 238380835 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430285013 6 238380835 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y20
  (h_ts : 2 ^ 15 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 20) = 1426614997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426614997 = 6 * 237769166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426614997 6 237769166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y21
  (h_ts : 2 ^ 15 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 21) = 1419274965 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419274965 = 6 * 236545827 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419274965 6 236545827 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y22
  (h_ts : 2 ^ 15 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 22) = 1404594901 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404594901 = 6 * 234099150 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404594901 6 234099150 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y23
  (h_ts : 2 ^ 15 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 23) = 1375234773 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375234773 = 6 * 229205795 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375234773 6 229205795 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y24
  (h_ts : 2 ^ 15 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 24) = 1316514517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316514517 = 6 * 219419086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316514517 6 219419086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y25
  (h_ts : 2 ^ 15 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 25) = 1199074005 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199074005 = 6 * 199845667 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1199074005 6 199845667 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y26
  (h_ts : 2 ^ 15 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 26) = 964192981 := by decide
  rw [h_sub] at hp6
  have h_eq : 964192981 = 6 * 160698830 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964192981 6 160698830 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y27
  (h_ts : 2 ^ 15 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 15 + 7 * 2 ^ 27) = 494430933 := by decide
  rw [h_sub] at hp6
  have h_eq : 494430933 = 6 * 82405155 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494430933 6 82405155 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x15_y28
  (h_ts : 2 ^ 15 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879080960 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x15_y29
  (h_ts : 2 ^ 15 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758129152 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x15_y30
  (h_ts : 2 ^ 15 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516225536 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x16_y1
  (h_ts : 2 ^ 16 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 1) = 1433922247 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433922247 = 6 * 238987041 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433922247 6 238987041 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y2
  (h_ts : 2 ^ 16 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 2) = 1433922233 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433922233 = 41 * 34973713 := by decide
  have hd : 41 ∣ 1433922233 := ⟨34973713, hd_eq⟩
  have h1 : 1 < 41 := by decide
  have h2 : 41 < 1433922233 := by decide
  exact (not_prime_of_dvd 1433922233 41 hd h1 h2) hp

lemma proof_x16_y3
  (h_ts : 2 ^ 16 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 3) = 1433922205 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433922205 = 6 * 238987034 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433922205 6 238987034 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y4
  (h_ts : 2 ^ 16 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 4) = 1433922149 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433922149 = 11 * 130356559 := by decide
  have hd : 11 ∣ 1433922149 := ⟨130356559, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433922149 := by decide
  exact (not_prime_of_dvd 1433922149 11 hd h1 h2) hp

lemma proof_x16_y5
  (h_ts : 2 ^ 16 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 5) = 1433922037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433922037 = 6 * 238987006 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433922037 6 238987006 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y6
  (h_ts : 2 ^ 16 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 6) = 1433921813 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433921813 = 103 * 13921571 := by decide
  have hd : 103 ∣ 1433921813 := ⟨13921571, hd_eq⟩
  have h1 : 1 < 103 := by decide
  have h2 : 103 < 1433921813 := by decide
  exact (not_prime_of_dvd 1433921813 103 hd h1 h2) hp

lemma proof_x16_y7
  (h_ts : 2 ^ 16 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 7) = 1433921365 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433921365 = 6 * 238986894 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433921365 6 238986894 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y8
  (h_ts : 2 ^ 16 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 8) = 1433920469 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433920469 = 31 * 46255499 := by decide
  have hd : 31 ∣ 1433920469 := ⟨46255499, hd_eq⟩
  have h1 : 1 < 31 := by decide
  have h2 : 31 < 1433920469 := by decide
  exact (not_prime_of_dvd 1433920469 31 hd h1 h2) hp

lemma proof_x16_y9
  (h_ts : 2 ^ 16 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 9) = 1433918677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433918677 = 6 * 238986446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433918677 6 238986446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y10
  (h_ts : 2 ^ 16 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 10) = 1433915093 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433915093 = 13 * 110301161 := by decide
  have hd : 13 ∣ 1433915093 := ⟨110301161, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1433915093 := by decide
  exact (not_prime_of_dvd 1433915093 13 hd h1 h2) hp

lemma proof_x16_y11
  (h_ts : 2 ^ 16 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 11) = 1433907925 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433907925 = 6 * 238984654 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433907925 6 238984654 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y12
  (h_ts : 2 ^ 16 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 12) = 1433893589 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433893589 = 367 * 3907067 := by decide
  have hd : 367 ∣ 1433893589 := ⟨3907067, hd_eq⟩
  have h1 : 1 < 367 := by decide
  have h2 : 367 < 1433893589 := by decide
  exact (not_prime_of_dvd 1433893589 367 hd h1 h2) hp

lemma proof_x16_y13
  (h_ts : 2 ^ 16 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 13) = 1433864917 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433864917 = 6 * 238977486 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433864917 6 238977486 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y14
  (h_ts : 2 ^ 16 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 14) = 1433807573 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433807573 = 11 * 130346143 := by decide
  have hd : 11 ∣ 1433807573 := ⟨130346143, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433807573 := by decide
  exact (not_prime_of_dvd 1433807573 11 hd h1 h2) hp

lemma proof_x16_y15
  (h_ts : 2 ^ 16 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 15) = 1433692885 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433692885 = 6 * 238948814 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433692885 6 238948814 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y16
  (h_ts : 2 ^ 16 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 16) = 1433463509 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433463509 = 37 * 38742257 := by decide
  have hd : 37 ∣ 1433463509 := ⟨38742257, hd_eq⟩
  have h1 : 1 < 37 := by decide
  have h2 : 37 < 1433463509 := by decide
  exact (not_prime_of_dvd 1433463509 37 hd h1 h2) hp

lemma proof_x16_y17
  (h_ts : 2 ^ 16 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 17) = 1433004757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433004757 = 6 * 238834126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433004757 6 238834126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y18
  (h_ts : 2 ^ 16 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 18) = 1432087253 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432087253 = 31 * 46196363 := by decide
  have hd : 31 ∣ 1432087253 := ⟨46196363, hd_eq⟩
  have h1 : 1 < 31 := by decide
  have h2 : 31 < 1432087253 := by decide
  exact (not_prime_of_dvd 1432087253 31 hd h1 h2) hp

lemma proof_x16_y19
  (h_ts : 2 ^ 16 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 19) = 1430252245 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430252245 = 6 * 238375374 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430252245 6 238375374 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y20
  (h_ts : 2 ^ 16 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 20) = 1426582229 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426582229 = 479 * 2978251 := by decide
  have hd : 479 ∣ 1426582229 := ⟨2978251, hd_eq⟩
  have h1 : 1 < 479 := by decide
  have h2 : 479 < 1426582229 := by decide
  exact (not_prime_of_dvd 1426582229 479 hd h1 h2) hp

lemma proof_x16_y21
  (h_ts : 2 ^ 16 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 21) = 1419242197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419242197 = 6 * 236540366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419242197 6 236540366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y22
  (h_ts : 2 ^ 16 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 22) = 1404562133 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404562133 = 13 * 108043241 := by decide
  have hd : 13 ∣ 1404562133 := ⟨108043241, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1404562133 := by decide
  exact (not_prime_of_dvd 1404562133 13 hd h1 h2) hp

lemma proof_x16_y23
  (h_ts : 2 ^ 16 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 23) = 1375202005 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375202005 = 6 * 229200334 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375202005 6 229200334 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y24
  (h_ts : 2 ^ 16 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 24) = 1316481749 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316481749 = 11 * 119680159 := by decide
  have hd : 11 ∣ 1316481749 := ⟨119680159, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1316481749 := by decide
  exact (not_prime_of_dvd 1316481749 11 hd h1 h2) hp

lemma proof_x16_y25
  (h_ts : 2 ^ 16 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 25) = 1199041237 := by decide
  rw [h_sub] at hp6
  have h_eq : 1199041237 = 6 * 199840206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1199041237 6 199840206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y26
  (h_ts : 2 ^ 16 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 26) = 964160213 := by decide
  rw [h_sub] at hp
  have hd_eq : 964160213 = 10159 * 94907 := by decide
  have hd : 10159 ∣ 964160213 := ⟨94907, hd_eq⟩
  have h1 : 1 < 10159 := by decide
  have h2 : 10159 < 964160213 := by decide
  exact (not_prime_of_dvd 964160213 10159 hd h1 h2) hp

lemma proof_x16_y27
  (h_ts : 2 ^ 16 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 16 + 7 * 2 ^ 27) = 494398165 := by decide
  rw [h_sub] at hp6
  have h_eq : 494398165 = 6 * 82399694 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494398165 6 82399694 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x16_y28
  (h_ts : 2 ^ 16 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879113728 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x16_y29
  (h_ts : 2 ^ 16 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758161920 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x16_y30
  (h_ts : 2 ^ 16 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516258304 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x17_y1
  (h_ts : 2 ^ 17 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 1) = 1433856711 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433856711 = 6 * 238976118 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433856711 6 238976118 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y2
  (h_ts : 2 ^ 17 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 2) = 1433856697 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433856697 = 6 * 238976116 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433856697 6 238976116 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y3
  (h_ts : 2 ^ 17 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 3) = 1433856669 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433856669 = 6 * 238976111 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433856669 6 238976111 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y4
  (h_ts : 2 ^ 17 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 4) = 1433856613 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433856613 = 6 * 238976102 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433856613 6 238976102 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y5
  (h_ts : 2 ^ 17 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 5) = 1433856501 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433856501 = 6 * 238976083 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433856501 6 238976083 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y6
  (h_ts : 2 ^ 17 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 6) = 1433856277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433856277 = 6 * 238976046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433856277 6 238976046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y7
  (h_ts : 2 ^ 17 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 7) = 1433855829 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433855829 = 6 * 238975971 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433855829 6 238975971 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y8
  (h_ts : 2 ^ 17 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 8) = 1433854933 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433854933 = 6 * 238975822 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433854933 6 238975822 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y9
  (h_ts : 2 ^ 17 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 9) = 1433853141 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433853141 = 6 * 238975523 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433853141 6 238975523 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y10
  (h_ts : 2 ^ 17 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 10) = 1433849557 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433849557 = 6 * 238974926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433849557 6 238974926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y11
  (h_ts : 2 ^ 17 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 11) = 1433842389 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433842389 = 6 * 238973731 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433842389 6 238973731 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y12
  (h_ts : 2 ^ 17 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 12) = 1433828053 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433828053 = 6 * 238971342 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433828053 6 238971342 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y13
  (h_ts : 2 ^ 17 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 13) = 1433799381 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433799381 = 6 * 238966563 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433799381 6 238966563 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y14
  (h_ts : 2 ^ 17 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 14) = 1433742037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433742037 = 6 * 238957006 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433742037 6 238957006 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y15
  (h_ts : 2 ^ 17 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 15) = 1433627349 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433627349 = 6 * 238937891 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433627349 6 238937891 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y16
  (h_ts : 2 ^ 17 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 16) = 1433397973 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433397973 = 6 * 238899662 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433397973 6 238899662 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y17
  (h_ts : 2 ^ 17 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 17) = 1432939221 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432939221 = 6 * 238823203 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1432939221 6 238823203 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y18
  (h_ts : 2 ^ 17 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 18) = 1432021717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432021717 = 6 * 238670286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432021717 6 238670286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y19
  (h_ts : 2 ^ 17 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 19) = 1430186709 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430186709 = 6 * 238364451 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430186709 6 238364451 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y20
  (h_ts : 2 ^ 17 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 20) = 1426516693 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426516693 = 6 * 237752782 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426516693 6 237752782 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y21
  (h_ts : 2 ^ 17 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 21) = 1419176661 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419176661 = 6 * 236529443 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1419176661 6 236529443 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y22
  (h_ts : 2 ^ 17 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 22) = 1404496597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404496597 = 6 * 234082766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404496597 6 234082766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y23
  (h_ts : 2 ^ 17 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 23) = 1375136469 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375136469 = 6 * 229189411 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1375136469 6 229189411 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y24
  (h_ts : 2 ^ 17 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 24) = 1316416213 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316416213 = 6 * 219402702 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316416213 6 219402702 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y25
  (h_ts : 2 ^ 17 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 25) = 1198975701 := by decide
  rw [h_sub] at hp6
  have h_eq : 1198975701 = 6 * 199829283 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1198975701 6 199829283 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y26
  (h_ts : 2 ^ 17 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 26) = 964094677 := by decide
  rw [h_sub] at hp6
  have h_eq : 964094677 = 6 * 160682446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 964094677 6 160682446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y27
  (h_ts : 2 ^ 17 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 17 + 7 * 2 ^ 27) = 494332629 := by decide
  rw [h_sub] at hp6
  have h_eq : 494332629 = 6 * 82388771 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 494332629 6 82388771 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x17_y28
  (h_ts : 2 ^ 17 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879179264 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x17_y29
  (h_ts : 2 ^ 17 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758227456 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x17_y30
  (h_ts : 2 ^ 17 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516323840 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x18_y1
  (h_ts : 2 ^ 18 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 1) = 1433725639 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433725639 = 6 * 238954273 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433725639 6 238954273 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y2
  (h_ts : 2 ^ 18 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 2) = 1433725625 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433725625 = 5 * 286745125 := by decide
  have hd : 5 ∣ 1433725625 := ⟨286745125, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433725625 := by decide
  exact (not_prime_of_dvd 1433725625 5 hd h1 h2) hp

lemma proof_x18_y3
  (h_ts : 2 ^ 18 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 3) = 1433725597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433725597 = 6 * 238954266 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433725597 6 238954266 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y4
  (h_ts : 2 ^ 18 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 4) = 1433725541 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433725541 = 19 * 75459239 := by decide
  have hd : 19 ∣ 1433725541 := ⟨75459239, hd_eq⟩
  have h1 : 1 < 19 := by decide
  have h2 : 19 < 1433725541 := by decide
  exact (not_prime_of_dvd 1433725541 19 hd h1 h2) hp

lemma proof_x18_y5
  (h_ts : 2 ^ 18 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 5) = 1433725429 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433725429 = 6 * 238954238 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433725429 6 238954238 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y6
  (h_ts : 2 ^ 18 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 6) = 1433725205 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433725205 = 5 * 286745041 := by decide
  have hd : 5 ∣ 1433725205 := ⟨286745041, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433725205 := by decide
  exact (not_prime_of_dvd 1433725205 5 hd h1 h2) hp

lemma proof_x18_y7
  (h_ts : 2 ^ 18 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 7) = 1433724757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433724757 = 6 * 238954126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433724757 6 238954126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y8
  (h_ts : 2 ^ 18 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 8) = 1433723861 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433723861 = 47 * 30504763 := by decide
  have hd : 47 ∣ 1433723861 := ⟨30504763, hd_eq⟩
  have h1 : 1 < 47 := by decide
  have h2 : 47 < 1433723861 := by decide
  exact (not_prime_of_dvd 1433723861 47 hd h1 h2) hp

lemma proof_x18_y9
  (h_ts : 2 ^ 18 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 9) = 1433722069 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433722069 = 6 * 238953678 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433722069 6 238953678 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y10
  (h_ts : 2 ^ 18 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 10) = 1433718485 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433718485 = 5 * 286743697 := by decide
  have hd : 5 ∣ 1433718485 := ⟨286743697, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433718485 := by decide
  exact (not_prime_of_dvd 1433718485 5 hd h1 h2) hp

lemma proof_x18_y11
  (h_ts : 2 ^ 18 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 11) = 1433711317 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433711317 = 6 * 238951886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433711317 6 238951886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y12
  (h_ts : 2 ^ 18 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 12) = 1433696981 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433696981 = 163 * 8795687 := by decide
  have hd : 163 ∣ 1433696981 := ⟨8795687, hd_eq⟩
  have h1 : 1 < 163 := by decide
  have h2 : 163 < 1433696981 := by decide
  exact (not_prime_of_dvd 1433696981 163 hd h1 h2) hp

lemma proof_x18_y13
  (h_ts : 2 ^ 18 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 13) = 1433668309 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433668309 = 6 * 238944718 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433668309 6 238944718 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y14
  (h_ts : 2 ^ 18 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 14) = 1433610965 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433610965 = 5 * 286722193 := by decide
  have hd : 5 ∣ 1433610965 := ⟨286722193, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1433610965 := by decide
  exact (not_prime_of_dvd 1433610965 5 hd h1 h2) hp

lemma proof_x18_y15
  (h_ts : 2 ^ 18 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 15) = 1433496277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433496277 = 6 * 238916046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433496277 6 238916046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y16
  (h_ts : 2 ^ 18 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 16) = 1433266901 := by decide
  rw [h_sub] at hp
  have hd_eq : 1433266901 = 11 * 130296991 := by decide
  have hd : 11 ∣ 1433266901 := ⟨130296991, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1433266901 := by decide
  exact (not_prime_of_dvd 1433266901 11 hd h1 h2) hp

lemma proof_x18_y17
  (h_ts : 2 ^ 18 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 17) = 1432808149 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432808149 = 6 * 238801358 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432808149 6 238801358 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y18
  (h_ts : 2 ^ 18 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 18) = 1431890645 := by decide
  rw [h_sub] at hp
  have hd_eq : 1431890645 = 5 * 286378129 := by decide
  have hd : 5 ∣ 1431890645 := ⟨286378129, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1431890645 := by decide
  exact (not_prime_of_dvd 1431890645 5 hd h1 h2) hp

lemma proof_x18_y19
  (h_ts : 2 ^ 18 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 19) = 1430055637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430055637 = 6 * 238342606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430055637 6 238342606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y20
  (h_ts : 2 ^ 18 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 20) = 1426385621 := by decide
  rw [h_sub] at hp
  have hd_eq : 1426385621 = 359 * 3973219 := by decide
  have hd : 359 ∣ 1426385621 := ⟨3973219, hd_eq⟩
  have h1 : 1 < 359 := by decide
  have h2 : 359 < 1426385621 := by decide
  exact (not_prime_of_dvd 1426385621 359 hd h1 h2) hp

lemma proof_x18_y21
  (h_ts : 2 ^ 18 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 21) = 1419045589 := by decide
  rw [h_sub] at hp6
  have h_eq : 1419045589 = 6 * 236507598 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1419045589 6 236507598 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y22
  (h_ts : 2 ^ 18 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 22) = 1404365525 := by decide
  rw [h_sub] at hp
  have hd_eq : 1404365525 = 5 * 280873105 := by decide
  have hd : 5 ∣ 1404365525 := ⟨280873105, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1404365525 := by decide
  exact (not_prime_of_dvd 1404365525 5 hd h1 h2) hp

lemma proof_x18_y23
  (h_ts : 2 ^ 18 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 23) = 1375005397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1375005397 = 6 * 229167566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1375005397 6 229167566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y24
  (h_ts : 2 ^ 18 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 24) = 1316285141 := by decide
  rw [h_sub] at hp
  have hd_eq : 1316285141 = 31 * 42460811 := by decide
  have hd : 31 ∣ 1316285141 := ⟨42460811, hd_eq⟩
  have h1 : 1 < 31 := by decide
  have h2 : 31 < 1316285141 := by decide
  exact (not_prime_of_dvd 1316285141 31 hd h1 h2) hp

lemma proof_x18_y25
  (h_ts : 2 ^ 18 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 25) = 1198844629 := by decide
  rw [h_sub] at hp6
  have h_eq : 1198844629 = 6 * 199807438 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1198844629 6 199807438 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y26
  (h_ts : 2 ^ 18 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 26) = 963963605 := by decide
  rw [h_sub] at hp
  have hd_eq : 963963605 = 5 * 192792721 := by decide
  have hd : 5 ∣ 963963605 := ⟨192792721, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 963963605 := by decide
  exact (not_prime_of_dvd 963963605 5 hd h1 h2) hp

lemma proof_x18_y27
  (h_ts : 2 ^ 18 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 18 + 7 * 2 ^ 27) = 494201557 := by decide
  rw [h_sub] at hp6
  have h_eq : 494201557 = 6 * 82366926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 494201557 6 82366926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x18_y28
  (h_ts : 2 ^ 18 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879310336 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x18_y29
  (h_ts : 2 ^ 18 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758358528 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x18_y30
  (h_ts : 2 ^ 18 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516454912 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x19_y1
  (h_ts : 2 ^ 19 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 1) = 1433463495 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433463495 = 6 * 238910582 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433463495 6 238910582 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y2
  (h_ts : 2 ^ 19 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 2) = 1433463481 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433463481 = 6 * 238910580 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433463481 6 238910580 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y3
  (h_ts : 2 ^ 19 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 3) = 1433463453 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433463453 = 6 * 238910575 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433463453 6 238910575 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y4
  (h_ts : 2 ^ 19 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 4) = 1433463397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433463397 = 6 * 238910566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433463397 6 238910566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y5
  (h_ts : 2 ^ 19 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 5) = 1433463285 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433463285 = 6 * 238910547 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433463285 6 238910547 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y6
  (h_ts : 2 ^ 19 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 6) = 1433463061 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433463061 = 6 * 238910510 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433463061 6 238910510 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y7
  (h_ts : 2 ^ 19 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 7) = 1433462613 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433462613 = 6 * 238910435 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433462613 6 238910435 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y8
  (h_ts : 2 ^ 19 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 8) = 1433461717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433461717 = 6 * 238910286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433461717 6 238910286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y9
  (h_ts : 2 ^ 19 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 9) = 1433459925 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433459925 = 6 * 238909987 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433459925 6 238909987 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y10
  (h_ts : 2 ^ 19 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 10) = 1433456341 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433456341 = 6 * 238909390 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433456341 6 238909390 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y11
  (h_ts : 2 ^ 19 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 11) = 1433449173 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433449173 = 6 * 238908195 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433449173 6 238908195 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y12
  (h_ts : 2 ^ 19 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 12) = 1433434837 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433434837 = 6 * 238905806 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433434837 6 238905806 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y13
  (h_ts : 2 ^ 19 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 13) = 1433406165 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433406165 = 6 * 238901027 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433406165 6 238901027 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y14
  (h_ts : 2 ^ 19 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 14) = 1433348821 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433348821 = 6 * 238891470 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433348821 6 238891470 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y15
  (h_ts : 2 ^ 19 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 15) = 1433234133 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433234133 = 6 * 238872355 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1433234133 6 238872355 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y16
  (h_ts : 2 ^ 19 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 16) = 1433004757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1433004757 = 6 * 238834126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1433004757 6 238834126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y17
  (h_ts : 2 ^ 19 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 17) = 1432546005 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432546005 = 6 * 238757667 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1432546005 6 238757667 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y18
  (h_ts : 2 ^ 19 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 18) = 1431628501 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431628501 = 6 * 238604750 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431628501 6 238604750 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y19
  (h_ts : 2 ^ 19 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 19) = 1429793493 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429793493 = 6 * 238298915 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1429793493 6 238298915 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y20
  (h_ts : 2 ^ 19 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 20) = 1426123477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426123477 = 6 * 237687246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426123477 6 237687246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y21
  (h_ts : 2 ^ 19 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 21) = 1418783445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1418783445 = 6 * 236463907 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1418783445 6 236463907 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y22
  (h_ts : 2 ^ 19 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 22) = 1404103381 := by decide
  rw [h_sub] at hp6
  have h_eq : 1404103381 = 6 * 234017230 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1404103381 6 234017230 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y23
  (h_ts : 2 ^ 19 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 23) = 1374743253 := by decide
  rw [h_sub] at hp6
  have h_eq : 1374743253 = 6 * 229123875 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1374743253 6 229123875 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y24
  (h_ts : 2 ^ 19 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 24) = 1316022997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1316022997 = 6 * 219337166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1316022997 6 219337166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y25
  (h_ts : 2 ^ 19 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 25) = 1198582485 := by decide
  rw [h_sub] at hp6
  have h_eq : 1198582485 = 6 * 199763747 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1198582485 6 199763747 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y26
  (h_ts : 2 ^ 19 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 26) = 963701461 := by decide
  rw [h_sub] at hp6
  have h_eq : 963701461 = 6 * 160616910 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 963701461 6 160616910 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y27
  (h_ts : 2 ^ 19 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 19 + 7 * 2 ^ 27) = 493939413 := by decide
  rw [h_sub] at hp6
  have h_eq : 493939413 = 6 * 82323235 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 493939413 6 82323235 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x19_y28
  (h_ts : 2 ^ 19 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1879572480 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x19_y29
  (h_ts : 2 ^ 19 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3758620672 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x19_y30
  (h_ts : 2 ^ 19 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7516717056 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x20_y1
  (h_ts : 2 ^ 20 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 1) = 1432939207 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432939207 = 6 * 238823201 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432939207 6 238823201 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y2
  (h_ts : 2 ^ 20 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 2) = 1432939193 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432939193 = 7 * 204705599 := by decide
  have hd : 7 ∣ 1432939193 := ⟨204705599, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432939193 := by decide
  exact (not_prime_of_dvd 1432939193 7 hd h1 h2) hp

lemma proof_x20_y3
  (h_ts : 2 ^ 20 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 3) = 1432939165 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432939165 = 6 * 238823194 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432939165 6 238823194 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y4
  (h_ts : 2 ^ 20 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 4) = 1432939109 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432939109 = 7 * 204705587 := by decide
  have hd : 7 ∣ 1432939109 := ⟨204705587, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432939109 := by decide
  exact (not_prime_of_dvd 1432939109 7 hd h1 h2) hp

lemma proof_x20_y5
  (h_ts : 2 ^ 20 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 5) = 1432938997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432938997 = 6 * 238823166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432938997 6 238823166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y6
  (h_ts : 2 ^ 20 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 6) = 1432938773 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432938773 = 7 * 204705539 := by decide
  have hd : 7 ∣ 1432938773 := ⟨204705539, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432938773 := by decide
  exact (not_prime_of_dvd 1432938773 7 hd h1 h2) hp

lemma proof_x20_y7
  (h_ts : 2 ^ 20 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 7) = 1432938325 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432938325 = 6 * 238823054 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432938325 6 238823054 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y8
  (h_ts : 2 ^ 20 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 8) = 1432937429 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432937429 = 7 * 204705347 := by decide
  have hd : 7 ∣ 1432937429 := ⟨204705347, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432937429 := by decide
  exact (not_prime_of_dvd 1432937429 7 hd h1 h2) hp

lemma proof_x20_y9
  (h_ts : 2 ^ 20 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 9) = 1432935637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432935637 = 6 * 238822606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432935637 6 238822606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y10
  (h_ts : 2 ^ 20 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 10) = 1432932053 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432932053 = 7 * 204704579 := by decide
  have hd : 7 ∣ 1432932053 := ⟨204704579, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432932053 := by decide
  exact (not_prime_of_dvd 1432932053 7 hd h1 h2) hp

lemma proof_x20_y11
  (h_ts : 2 ^ 20 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 11) = 1432924885 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432924885 = 6 * 238820814 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432924885 6 238820814 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y12
  (h_ts : 2 ^ 20 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 12) = 1432910549 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432910549 = 7 * 204701507 := by decide
  have hd : 7 ∣ 1432910549 := ⟨204701507, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432910549 := by decide
  exact (not_prime_of_dvd 1432910549 7 hd h1 h2) hp

lemma proof_x20_y13
  (h_ts : 2 ^ 20 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 13) = 1432881877 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432881877 = 6 * 238813646 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432881877 6 238813646 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y14
  (h_ts : 2 ^ 20 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 14) = 1432824533 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432824533 = 7 * 204689219 := by decide
  have hd : 7 ∣ 1432824533 := ⟨204689219, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432824533 := by decide
  exact (not_prime_of_dvd 1432824533 7 hd h1 h2) hp

lemma proof_x20_y15
  (h_ts : 2 ^ 20 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 15) = 1432709845 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432709845 = 6 * 238784974 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432709845 6 238784974 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y16
  (h_ts : 2 ^ 20 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 16) = 1432480469 := by decide
  rw [h_sub] at hp
  have hd_eq : 1432480469 = 7 * 204640067 := by decide
  have hd : 7 ∣ 1432480469 := ⟨204640067, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1432480469 := by decide
  exact (not_prime_of_dvd 1432480469 7 hd h1 h2) hp

lemma proof_x20_y17
  (h_ts : 2 ^ 20 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 17) = 1432021717 := by decide
  rw [h_sub] at hp6
  have h_eq : 1432021717 = 6 * 238670286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1432021717 6 238670286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y18
  (h_ts : 2 ^ 20 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 18) = 1431104213 := by decide
  rw [h_sub] at hp
  have hd_eq : 1431104213 = 7 * 204443459 := by decide
  have hd : 7 ∣ 1431104213 := ⟨204443459, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1431104213 := by decide
  exact (not_prime_of_dvd 1431104213 7 hd h1 h2) hp

lemma proof_x20_y19
  (h_ts : 2 ^ 20 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 19) = 1429269205 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429269205 = 6 * 238211534 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429269205 6 238211534 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y20
  (h_ts : 2 ^ 20 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 20) = 1425599189 := by decide
  rw [h_sub] at hp
  have hd_eq : 1425599189 = 7 * 203657027 := by decide
  have hd : 7 ∣ 1425599189 := ⟨203657027, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1425599189 := by decide
  exact (not_prime_of_dvd 1425599189 7 hd h1 h2) hp

lemma proof_x20_y21
  (h_ts : 2 ^ 20 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 21) = 1418259157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1418259157 = 6 * 236376526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1418259157 6 236376526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y22
  (h_ts : 2 ^ 20 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 22) = 1403579093 := by decide
  rw [h_sub] at hp
  have hd_eq : 1403579093 = 7 * 200511299 := by decide
  have hd : 7 ∣ 1403579093 := ⟨200511299, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1403579093 := by decide
  exact (not_prime_of_dvd 1403579093 7 hd h1 h2) hp

lemma proof_x20_y23
  (h_ts : 2 ^ 20 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 23) = 1374218965 := by decide
  rw [h_sub] at hp6
  have h_eq : 1374218965 = 6 * 229036494 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1374218965 6 229036494 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y24
  (h_ts : 2 ^ 20 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 24) = 1315498709 := by decide
  rw [h_sub] at hp
  have hd_eq : 1315498709 = 7 * 187928387 := by decide
  have hd : 7 ∣ 1315498709 := ⟨187928387, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1315498709 := by decide
  exact (not_prime_of_dvd 1315498709 7 hd h1 h2) hp

lemma proof_x20_y25
  (h_ts : 2 ^ 20 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 25) = 1198058197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1198058197 = 6 * 199676366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1198058197 6 199676366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y26
  (h_ts : 2 ^ 20 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 26) = 963177173 := by decide
  rw [h_sub] at hp
  have hd_eq : 963177173 = 7 * 137596739 := by decide
  have hd : 7 ∣ 963177173 := ⟨137596739, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 963177173 := by decide
  exact (not_prime_of_dvd 963177173 7 hd h1 h2) hp

lemma proof_x20_y27
  (h_ts : 2 ^ 20 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 20 + 7 * 2 ^ 27) = 493415125 := by decide
  rw [h_sub] at hp6
  have h_eq : 493415125 = 6 * 82235854 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 493415125 6 82235854 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x20_y28
  (h_ts : 2 ^ 20 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1880096768 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x20_y29
  (h_ts : 2 ^ 20 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3759144960 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x20_y30
  (h_ts : 2 ^ 20 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7517241344 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x21_y1
  (h_ts : 2 ^ 21 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 1) = 1431890631 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431890631 = 6 * 238648438 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431890631 6 238648438 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y2
  (h_ts : 2 ^ 21 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 2) = 1431890617 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431890617 = 6 * 238648436 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431890617 6 238648436 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y3
  (h_ts : 2 ^ 21 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 3) = 1431890589 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431890589 = 6 * 238648431 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431890589 6 238648431 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y4
  (h_ts : 2 ^ 21 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 4) = 1431890533 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431890533 = 6 * 238648422 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431890533 6 238648422 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y5
  (h_ts : 2 ^ 21 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 5) = 1431890421 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431890421 = 6 * 238648403 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431890421 6 238648403 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y6
  (h_ts : 2 ^ 21 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 6) = 1431890197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431890197 = 6 * 238648366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431890197 6 238648366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y7
  (h_ts : 2 ^ 21 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 7) = 1431889749 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431889749 = 6 * 238648291 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431889749 6 238648291 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y8
  (h_ts : 2 ^ 21 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 8) = 1431888853 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431888853 = 6 * 238648142 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431888853 6 238648142 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y9
  (h_ts : 2 ^ 21 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 9) = 1431887061 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431887061 = 6 * 238647843 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431887061 6 238647843 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y10
  (h_ts : 2 ^ 21 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 10) = 1431883477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431883477 = 6 * 238647246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431883477 6 238647246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y11
  (h_ts : 2 ^ 21 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 11) = 1431876309 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431876309 = 6 * 238646051 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431876309 6 238646051 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y12
  (h_ts : 2 ^ 21 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 12) = 1431861973 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431861973 = 6 * 238643662 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431861973 6 238643662 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y13
  (h_ts : 2 ^ 21 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 13) = 1431833301 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431833301 = 6 * 238638883 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431833301 6 238638883 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y14
  (h_ts : 2 ^ 21 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 14) = 1431775957 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431775957 = 6 * 238629326 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431775957 6 238629326 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y15
  (h_ts : 2 ^ 21 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 15) = 1431661269 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431661269 = 6 * 238610211 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1431661269 6 238610211 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y16
  (h_ts : 2 ^ 21 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 16) = 1431431893 := by decide
  rw [h_sub] at hp6
  have h_eq : 1431431893 = 6 * 238571982 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1431431893 6 238571982 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y17
  (h_ts : 2 ^ 21 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 17) = 1430973141 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430973141 = 6 * 238495523 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1430973141 6 238495523 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y18
  (h_ts : 2 ^ 21 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 18) = 1430055637 := by decide
  rw [h_sub] at hp6
  have h_eq : 1430055637 = 6 * 238342606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1430055637 6 238342606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y19
  (h_ts : 2 ^ 21 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 19) = 1428220629 := by decide
  rw [h_sub] at hp6
  have h_eq : 1428220629 = 6 * 238036771 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1428220629 6 238036771 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y20
  (h_ts : 2 ^ 21 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 20) = 1424550613 := by decide
  rw [h_sub] at hp6
  have h_eq : 1424550613 = 6 * 237425102 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1424550613 6 237425102 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y21
  (h_ts : 2 ^ 21 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 21) = 1417210581 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417210581 = 6 * 236201763 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1417210581 6 236201763 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y22
  (h_ts : 2 ^ 21 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 22) = 1402530517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1402530517 = 6 * 233755086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1402530517 6 233755086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y23
  (h_ts : 2 ^ 21 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 23) = 1373170389 := by decide
  rw [h_sub] at hp6
  have h_eq : 1373170389 = 6 * 228861731 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1373170389 6 228861731 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y24
  (h_ts : 2 ^ 21 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 24) = 1314450133 := by decide
  rw [h_sub] at hp6
  have h_eq : 1314450133 = 6 * 219075022 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1314450133 6 219075022 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y25
  (h_ts : 2 ^ 21 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 25) = 1197009621 := by decide
  rw [h_sub] at hp6
  have h_eq : 1197009621 = 6 * 199501603 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1197009621 6 199501603 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y26
  (h_ts : 2 ^ 21 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 26) = 962128597 := by decide
  rw [h_sub] at hp6
  have h_eq : 962128597 = 6 * 160354766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 962128597 6 160354766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y27
  (h_ts : 2 ^ 21 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 21 + 7 * 2 ^ 27) = 492366549 := by decide
  rw [h_sub] at hp6
  have h_eq : 492366549 = 6 * 82061091 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 492366549 6 82061091 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x21_y28
  (h_ts : 2 ^ 21 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1881145344 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x21_y29
  (h_ts : 2 ^ 21 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3760193536 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x21_y30
  (h_ts : 2 ^ 21 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7518289920 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x22_y1
  (h_ts : 2 ^ 22 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 1) = 1429793479 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429793479 = 6 * 238298913 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429793479 6 238298913 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y2
  (h_ts : 2 ^ 22 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 2) = 1429793465 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429793465 = 5 * 285958693 := by decide
  have hd : 5 ∣ 1429793465 := ⟨285958693, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1429793465 := by decide
  exact (not_prime_of_dvd 1429793465 5 hd h1 h2) hp

lemma proof_x22_y3
  (h_ts : 2 ^ 22 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 3) = 1429793437 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429793437 = 6 * 238298906 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429793437 6 238298906 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y4
  (h_ts : 2 ^ 22 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 4) = 1429793381 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429793381 = 17 * 84105493 := by decide
  have hd : 17 ∣ 1429793381 := ⟨84105493, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1429793381 := by decide
  exact (not_prime_of_dvd 1429793381 17 hd h1 h2) hp

lemma proof_x22_y5
  (h_ts : 2 ^ 22 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 5) = 1429793269 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429793269 = 6 * 238298878 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429793269 6 238298878 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y6
  (h_ts : 2 ^ 22 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 6) = 1429793045 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429793045 = 5 * 285958609 := by decide
  have hd : 5 ∣ 1429793045 := ⟨285958609, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1429793045 := by decide
  exact (not_prime_of_dvd 1429793045 5 hd h1 h2) hp

lemma proof_x22_y7
  (h_ts : 2 ^ 22 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 7) = 1429792597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429792597 = 6 * 238298766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429792597 6 238298766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y8
  (h_ts : 2 ^ 22 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 8) = 1429791701 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429791701 = 13 * 109983977 := by decide
  have hd : 13 ∣ 1429791701 := ⟨109983977, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1429791701 := by decide
  exact (not_prime_of_dvd 1429791701 13 hd h1 h2) hp

lemma proof_x22_y9
  (h_ts : 2 ^ 22 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 9) = 1429789909 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429789909 = 6 * 238298318 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429789909 6 238298318 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y10
  (h_ts : 2 ^ 22 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 10) = 1429786325 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429786325 = 5 * 285957265 := by decide
  have hd : 5 ∣ 1429786325 := ⟨285957265, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1429786325 := by decide
  exact (not_prime_of_dvd 1429786325 5 hd h1 h2) hp

lemma proof_x22_y11
  (h_ts : 2 ^ 22 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 11) = 1429779157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429779157 = 6 * 238296526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429779157 6 238296526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y12
  (h_ts : 2 ^ 22 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 12) = 1429764821 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429764821 = 17 * 84103813 := by decide
  have hd : 17 ∣ 1429764821 := ⟨84103813, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1429764821 := by decide
  exact (not_prime_of_dvd 1429764821 17 hd h1 h2) hp

lemma proof_x22_y13
  (h_ts : 2 ^ 22 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 13) = 1429736149 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429736149 = 6 * 238289358 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429736149 6 238289358 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y14
  (h_ts : 2 ^ 22 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 14) = 1429678805 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429678805 = 5 * 285935761 := by decide
  have hd : 5 ∣ 1429678805 := ⟨285935761, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1429678805 := by decide
  exact (not_prime_of_dvd 1429678805 5 hd h1 h2) hp

lemma proof_x22_y15
  (h_ts : 2 ^ 22 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 15) = 1429564117 := by decide
  rw [h_sub] at hp6
  have h_eq : 1429564117 = 6 * 238260686 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1429564117 6 238260686 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y16
  (h_ts : 2 ^ 22 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 16) = 1429334741 := by decide
  rw [h_sub] at hp
  have hd_eq : 1429334741 = 2617 * 546173 := by decide
  have hd : 2617 ∣ 1429334741 := ⟨546173, hd_eq⟩
  have h1 : 1 < 2617 := by decide
  have h2 : 2617 < 1429334741 := by decide
  exact (not_prime_of_dvd 1429334741 2617 hd h1 h2) hp

lemma proof_x22_y17
  (h_ts : 2 ^ 22 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 17) = 1428875989 := by decide
  rw [h_sub] at hp6
  have h_eq : 1428875989 = 6 * 238145998 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1428875989 6 238145998 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y18
  (h_ts : 2 ^ 22 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 18) = 1427958485 := by decide
  rw [h_sub] at hp
  have hd_eq : 1427958485 = 5 * 285591697 := by decide
  have hd : 5 ∣ 1427958485 := ⟨285591697, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1427958485 := by decide
  exact (not_prime_of_dvd 1427958485 5 hd h1 h2) hp

lemma proof_x22_y19
  (h_ts : 2 ^ 22 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 19) = 1426123477 := by decide
  rw [h_sub] at hp6
  have h_eq : 1426123477 = 6 * 237687246 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1426123477 6 237687246 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y20
  (h_ts : 2 ^ 22 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 20) = 1422453461 := by decide
  rw [h_sub] at hp
  have hd_eq : 1422453461 = 11 * 129313951 := by decide
  have hd : 11 ∣ 1422453461 := ⟨129313951, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1422453461 := by decide
  exact (not_prime_of_dvd 1422453461 11 hd h1 h2) hp

lemma proof_x22_y21
  (h_ts : 2 ^ 22 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 21) = 1415113429 := by decide
  rw [h_sub] at hp6
  have h_eq : 1415113429 = 6 * 235852238 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1415113429 6 235852238 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y22
  (h_ts : 2 ^ 22 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 22) = 1400433365 := by decide
  rw [h_sub] at hp
  have hd_eq : 1400433365 = 5 * 280086673 := by decide
  have hd : 5 ∣ 1400433365 := ⟨280086673, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1400433365 := by decide
  exact (not_prime_of_dvd 1400433365 5 hd h1 h2) hp

lemma proof_x22_y23
  (h_ts : 2 ^ 22 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 23) = 1371073237 := by decide
  rw [h_sub] at hp6
  have h_eq : 1371073237 = 6 * 228512206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1371073237 6 228512206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y24
  (h_ts : 2 ^ 22 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 24) = 1312352981 := by decide
  rw [h_sub] at hp
  have hd_eq : 1312352981 = 53 * 24761377 := by decide
  have hd : 53 ∣ 1312352981 := ⟨24761377, hd_eq⟩
  have h1 : 1 < 53 := by decide
  have h2 : 53 < 1312352981 := by decide
  exact (not_prime_of_dvd 1312352981 53 hd h1 h2) hp

lemma proof_x22_y25
  (h_ts : 2 ^ 22 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 25) = 1194912469 := by decide
  rw [h_sub] at hp6
  have h_eq : 1194912469 = 6 * 199152078 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1194912469 6 199152078 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y26
  (h_ts : 2 ^ 22 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 26) = 960031445 := by decide
  rw [h_sub] at hp
  have hd_eq : 960031445 = 5 * 192006289 := by decide
  have hd : 5 ∣ 960031445 := ⟨192006289, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 960031445 := by decide
  exact (not_prime_of_dvd 960031445 5 hd h1 h2) hp

lemma proof_x22_y27
  (h_ts : 2 ^ 22 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 22 + 7 * 2 ^ 27) = 490269397 := by decide
  rw [h_sub] at hp6
  have h_eq : 490269397 = 6 * 81711566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 490269397 6 81711566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x22_y28
  (h_ts : 2 ^ 22 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1883242496 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x22_y29
  (h_ts : 2 ^ 22 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3762290688 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x22_y30
  (h_ts : 2 ^ 22 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7520387072 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x23_y1
  (h_ts : 2 ^ 23 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 1) = 1425599175 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425599175 = 6 * 237599862 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425599175 6 237599862 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y2
  (h_ts : 2 ^ 23 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 2) = 1425599161 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425599161 = 6 * 237599860 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425599161 6 237599860 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y3
  (h_ts : 2 ^ 23 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 3) = 1425599133 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425599133 = 6 * 237599855 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425599133 6 237599855 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y4
  (h_ts : 2 ^ 23 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 4) = 1425599077 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425599077 = 6 * 237599846 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425599077 6 237599846 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y5
  (h_ts : 2 ^ 23 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 5) = 1425598965 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425598965 = 6 * 237599827 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425598965 6 237599827 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y6
  (h_ts : 2 ^ 23 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 6) = 1425598741 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425598741 = 6 * 237599790 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425598741 6 237599790 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y7
  (h_ts : 2 ^ 23 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 7) = 1425598293 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425598293 = 6 * 237599715 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425598293 6 237599715 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y8
  (h_ts : 2 ^ 23 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 8) = 1425597397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425597397 = 6 * 237599566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425597397 6 237599566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y9
  (h_ts : 2 ^ 23 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 9) = 1425595605 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425595605 = 6 * 237599267 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425595605 6 237599267 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y10
  (h_ts : 2 ^ 23 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 10) = 1425592021 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425592021 = 6 * 237598670 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425592021 6 237598670 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y11
  (h_ts : 2 ^ 23 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 11) = 1425584853 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425584853 = 6 * 237597475 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425584853 6 237597475 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y12
  (h_ts : 2 ^ 23 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 12) = 1425570517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425570517 = 6 * 237595086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425570517 6 237595086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y13
  (h_ts : 2 ^ 23 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 13) = 1425541845 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425541845 = 6 * 237590307 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425541845 6 237590307 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y14
  (h_ts : 2 ^ 23 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 14) = 1425484501 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425484501 = 6 * 237580750 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425484501 6 237580750 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y15
  (h_ts : 2 ^ 23 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 15) = 1425369813 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425369813 = 6 * 237561635 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1425369813 6 237561635 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y16
  (h_ts : 2 ^ 23 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 16) = 1425140437 := by decide
  rw [h_sub] at hp6
  have h_eq : 1425140437 = 6 * 237523406 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1425140437 6 237523406 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y17
  (h_ts : 2 ^ 23 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 17) = 1424681685 := by decide
  rw [h_sub] at hp6
  have h_eq : 1424681685 = 6 * 237446947 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1424681685 6 237446947 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y18
  (h_ts : 2 ^ 23 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 18) = 1423764181 := by decide
  rw [h_sub] at hp6
  have h_eq : 1423764181 = 6 * 237294030 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1423764181 6 237294030 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y19
  (h_ts : 2 ^ 23 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 19) = 1421929173 := by decide
  rw [h_sub] at hp6
  have h_eq : 1421929173 = 6 * 236988195 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1421929173 6 236988195 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y20
  (h_ts : 2 ^ 23 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 20) = 1418259157 := by decide
  rw [h_sub] at hp6
  have h_eq : 1418259157 = 6 * 236376526 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1418259157 6 236376526 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y21
  (h_ts : 2 ^ 23 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 21) = 1410919125 := by decide
  rw [h_sub] at hp6
  have h_eq : 1410919125 = 6 * 235153187 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1410919125 6 235153187 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y22
  (h_ts : 2 ^ 23 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 22) = 1396239061 := by decide
  rw [h_sub] at hp6
  have h_eq : 1396239061 = 6 * 232706510 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1396239061 6 232706510 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y23
  (h_ts : 2 ^ 23 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 23) = 1366878933 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366878933 = 6 * 227813155 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1366878933 6 227813155 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y24
  (h_ts : 2 ^ 23 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 24) = 1308158677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1308158677 = 6 * 218026446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1308158677 6 218026446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y25
  (h_ts : 2 ^ 23 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 25) = 1190718165 := by decide
  rw [h_sub] at hp6
  have h_eq : 1190718165 = 6 * 198453027 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1190718165 6 198453027 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y26
  (h_ts : 2 ^ 23 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 26) = 955837141 := by decide
  rw [h_sub] at hp6
  have h_eq : 955837141 = 6 * 159306190 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 955837141 6 159306190 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y27
  (h_ts : 2 ^ 23 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 23 + 7 * 2 ^ 27) = 486075093 := by decide
  rw [h_sub] at hp6
  have h_eq : 486075093 = 6 * 81012515 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 486075093 6 81012515 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x23_y28
  (h_ts : 2 ^ 23 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1887436800 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x23_y29
  (h_ts : 2 ^ 23 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3766484992 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x23_y30
  (h_ts : 2 ^ 23 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7524581376 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x24_y1
  (h_ts : 2 ^ 24 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 1) = 1417210567 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417210567 = 6 * 236201761 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417210567 6 236201761 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y2
  (h_ts : 2 ^ 24 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 2) = 1417210553 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417210553 = 11 * 128837323 := by decide
  have hd : 11 ∣ 1417210553 := ⟨128837323, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1417210553 := by decide
  exact (not_prime_of_dvd 1417210553 11 hd h1 h2) hp

lemma proof_x24_y3
  (h_ts : 2 ^ 24 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 3) = 1417210525 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417210525 = 6 * 236201754 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417210525 6 236201754 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y4
  (h_ts : 2 ^ 24 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 4) = 1417210469 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417210469 = 41 * 34566109 := by decide
  have hd : 41 ∣ 1417210469 := ⟨34566109, hd_eq⟩
  have h1 : 1 < 41 := by decide
  have h2 : 41 < 1417210469 := by decide
  exact (not_prime_of_dvd 1417210469 41 hd h1 h2) hp

lemma proof_x24_y5
  (h_ts : 2 ^ 24 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 5) = 1417210357 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417210357 = 6 * 236201726 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417210357 6 236201726 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y6
  (h_ts : 2 ^ 24 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 6) = 1417210133 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417210133 = 19 * 74590007 := by decide
  have hd : 19 ∣ 1417210133 := ⟨74590007, hd_eq⟩
  have h1 : 1 < 19 := by decide
  have h2 : 19 < 1417210133 := by decide
  exact (not_prime_of_dvd 1417210133 19 hd h1 h2) hp

lemma proof_x24_y7
  (h_ts : 2 ^ 24 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 7) = 1417209685 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417209685 = 6 * 236201614 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417209685 6 236201614 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y8
  (h_ts : 2 ^ 24 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 8) = 1417208789 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417208789 = 13313 * 106453 := by decide
  have hd : 13313 ∣ 1417208789 := ⟨106453, hd_eq⟩
  have h1 : 1 < 13313 := by decide
  have h2 : 13313 < 1417208789 := by decide
  exact (not_prime_of_dvd 1417208789 13313 hd h1 h2) hp

lemma proof_x24_y9
  (h_ts : 2 ^ 24 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 9) = 1417206997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417206997 = 6 * 236201166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417206997 6 236201166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y10
  (h_ts : 2 ^ 24 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 10) = 1417203413 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417203413 = 499 * 2840087 := by decide
  have hd : 499 ∣ 1417203413 := ⟨2840087, hd_eq⟩
  have h1 : 1 < 499 := by decide
  have h2 : 499 < 1417203413 := by decide
  exact (not_prime_of_dvd 1417203413 499 hd h1 h2) hp

lemma proof_x24_y11
  (h_ts : 2 ^ 24 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 11) = 1417196245 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417196245 = 6 * 236199374 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417196245 6 236199374 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y12
  (h_ts : 2 ^ 24 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 12) = 1417181909 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417181909 = 11 * 128834719 := by decide
  have hd : 11 ∣ 1417181909 := ⟨128834719, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1417181909 := by decide
  exact (not_prime_of_dvd 1417181909 11 hd h1 h2) hp

lemma proof_x24_y13
  (h_ts : 2 ^ 24 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 13) = 1417153237 := by decide
  rw [h_sub] at hp6
  have h_eq : 1417153237 = 6 * 236192206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1417153237 6 236192206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y14
  (h_ts : 2 ^ 24 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 14) = 1417095893 := by decide
  rw [h_sub] at hp
  have hd_eq : 1417095893 = 37 * 38299889 := by decide
  have hd : 37 ∣ 1417095893 := ⟨38299889, hd_eq⟩
  have h1 : 1 < 37 := by decide
  have h2 : 37 < 1417095893 := by decide
  exact (not_prime_of_dvd 1417095893 37 hd h1 h2) hp

lemma proof_x24_y15
  (h_ts : 2 ^ 24 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 15) = 1416981205 := by decide
  rw [h_sub] at hp6
  have h_eq : 1416981205 = 6 * 236163534 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1416981205 6 236163534 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y16
  (h_ts : 2 ^ 24 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 16) = 1416751829 := by decide
  rw [h_sub] at hp
  have hd_eq : 1416751829 = 157 * 9023897 := by decide
  have hd : 157 ∣ 1416751829 := ⟨9023897, hd_eq⟩
  have h1 : 1 < 157 := by decide
  have h2 : 157 < 1416751829 := by decide
  exact (not_prime_of_dvd 1416751829 157 hd h1 h2) hp

lemma proof_x24_y17
  (h_ts : 2 ^ 24 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 17) = 1416293077 := by decide
  rw [h_sub] at hp6
  have h_eq : 1416293077 = 6 * 236048846 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1416293077 6 236048846 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y18
  (h_ts : 2 ^ 24 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 18) = 1415375573 := by decide
  rw [h_sub] at hp
  have hd_eq : 1415375573 = 43 * 32915711 := by decide
  have hd : 43 ∣ 1415375573 := ⟨32915711, hd_eq⟩
  have h1 : 1 < 43 := by decide
  have h2 : 43 < 1415375573 := by decide
  exact (not_prime_of_dvd 1415375573 43 hd h1 h2) hp

lemma proof_x24_y19
  (h_ts : 2 ^ 24 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 19) = 1413540565 := by decide
  rw [h_sub] at hp6
  have h_eq : 1413540565 = 6 * 235590094 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1413540565 6 235590094 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y20
  (h_ts : 2 ^ 24 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 20) = 1409870549 := by decide
  rw [h_sub] at hp
  have hd_eq : 1409870549 = 59 * 23896111 := by decide
  have hd : 59 ∣ 1409870549 := ⟨23896111, hd_eq⟩
  have h1 : 1 < 59 := by decide
  have h2 : 59 < 1409870549 := by decide
  exact (not_prime_of_dvd 1409870549 59 hd h1 h2) hp

lemma proof_x24_y21
  (h_ts : 2 ^ 24 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 21) = 1402530517 := by decide
  rw [h_sub] at hp6
  have h_eq : 1402530517 = 6 * 233755086 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1402530517 6 233755086 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y22
  (h_ts : 2 ^ 24 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 22) = 1387850453 := by decide
  rw [h_sub] at hp
  have hd_eq : 1387850453 = 11 * 126168223 := by decide
  have hd : 11 ∣ 1387850453 := ⟨126168223, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1387850453 := by decide
  exact (not_prime_of_dvd 1387850453 11 hd h1 h2) hp

lemma proof_x24_y23
  (h_ts : 2 ^ 24 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 23) = 1358490325 := by decide
  rw [h_sub] at hp6
  have h_eq : 1358490325 = 6 * 226415054 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1358490325 6 226415054 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y24
  (h_ts : 2 ^ 24 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 24) = 1299770069 := by decide
  rw [h_sub] at hp
  have hd_eq : 1299770069 = 13 * 99982313 := by decide
  have hd : 13 ∣ 1299770069 := ⟨99982313, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1299770069 := by decide
  exact (not_prime_of_dvd 1299770069 13 hd h1 h2) hp

lemma proof_x24_y25
  (h_ts : 2 ^ 24 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 25) = 1182329557 := by decide
  rw [h_sub] at hp6
  have h_eq : 1182329557 = 6 * 197054926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1182329557 6 197054926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y26
  (h_ts : 2 ^ 24 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 26) = 947448533 := by decide
  rw [h_sub] at hp
  have hd_eq : 947448533 = 877 * 1080329 := by decide
  have hd : 877 ∣ 947448533 := ⟨1080329, hd_eq⟩
  have h1 : 1 < 877 := by decide
  have h2 : 877 < 947448533 := by decide
  exact (not_prime_of_dvd 947448533 877 hd h1 h2) hp

lemma proof_x24_y27
  (h_ts : 2 ^ 24 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 24 + 7 * 2 ^ 27) = 477686485 := by decide
  rw [h_sub] at hp6
  have h_eq : 477686485 = 6 * 79614414 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 477686485 6 79614414 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x24_y28
  (h_ts : 2 ^ 24 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1895825408 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x24_y29
  (h_ts : 2 ^ 24 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3774873600 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x24_y30
  (h_ts : 2 ^ 24 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7532969984 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x25_y1
  (h_ts : 2 ^ 25 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 1) = 1400433351 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400433351 = 6 * 233405558 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400433351 6 233405558 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y2
  (h_ts : 2 ^ 25 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 2) = 1400433337 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400433337 = 6 * 233405556 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400433337 6 233405556 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y3
  (h_ts : 2 ^ 25 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 3) = 1400433309 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400433309 = 6 * 233405551 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400433309 6 233405551 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y4
  (h_ts : 2 ^ 25 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 4) = 1400433253 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400433253 = 6 * 233405542 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400433253 6 233405542 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y5
  (h_ts : 2 ^ 25 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 5) = 1400433141 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400433141 = 6 * 233405523 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400433141 6 233405523 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y6
  (h_ts : 2 ^ 25 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 6) = 1400432917 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400432917 = 6 * 233405486 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400432917 6 233405486 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y7
  (h_ts : 2 ^ 25 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 7) = 1400432469 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400432469 = 6 * 233405411 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400432469 6 233405411 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y8
  (h_ts : 2 ^ 25 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 8) = 1400431573 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400431573 = 6 * 233405262 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400431573 6 233405262 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y9
  (h_ts : 2 ^ 25 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 9) = 1400429781 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400429781 = 6 * 233404963 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400429781 6 233404963 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y10
  (h_ts : 2 ^ 25 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 10) = 1400426197 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400426197 = 6 * 233404366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400426197 6 233404366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y11
  (h_ts : 2 ^ 25 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 11) = 1400419029 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400419029 = 6 * 233403171 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400419029 6 233403171 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y12
  (h_ts : 2 ^ 25 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 12) = 1400404693 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400404693 = 6 * 233400782 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400404693 6 233400782 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y13
  (h_ts : 2 ^ 25 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 13) = 1400376021 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400376021 = 6 * 233396003 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400376021 6 233396003 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y14
  (h_ts : 2 ^ 25 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 14) = 1400318677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400318677 = 6 * 233386446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1400318677 6 233386446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y15
  (h_ts : 2 ^ 25 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 15) = 1400203989 := by decide
  rw [h_sub] at hp6
  have h_eq : 1400203989 = 6 * 233367331 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1400203989 6 233367331 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y16
  (h_ts : 2 ^ 25 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 16) = 1399974613 := by decide
  rw [h_sub] at hp6
  have h_eq : 1399974613 = 6 * 233329102 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1399974613 6 233329102 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y17
  (h_ts : 2 ^ 25 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 17) = 1399515861 := by decide
  rw [h_sub] at hp6
  have h_eq : 1399515861 = 6 * 233252643 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1399515861 6 233252643 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y18
  (h_ts : 2 ^ 25 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 18) = 1398598357 := by decide
  rw [h_sub] at hp6
  have h_eq : 1398598357 = 6 * 233099726 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1398598357 6 233099726 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y19
  (h_ts : 2 ^ 25 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 19) = 1396763349 := by decide
  rw [h_sub] at hp6
  have h_eq : 1396763349 = 6 * 232793891 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1396763349 6 232793891 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y20
  (h_ts : 2 ^ 25 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 20) = 1393093333 := by decide
  rw [h_sub] at hp6
  have h_eq : 1393093333 = 6 * 232182222 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1393093333 6 232182222 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y21
  (h_ts : 2 ^ 25 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 21) = 1385753301 := by decide
  rw [h_sub] at hp6
  have h_eq : 1385753301 = 6 * 230958883 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1385753301 6 230958883 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y22
  (h_ts : 2 ^ 25 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 22) = 1371073237 := by decide
  rw [h_sub] at hp6
  have h_eq : 1371073237 = 6 * 228512206 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1371073237 6 228512206 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y23
  (h_ts : 2 ^ 25 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 23) = 1341713109 := by decide
  rw [h_sub] at hp6
  have h_eq : 1341713109 = 6 * 223618851 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1341713109 6 223618851 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y24
  (h_ts : 2 ^ 25 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 24) = 1282992853 := by decide
  rw [h_sub] at hp6
  have h_eq : 1282992853 = 6 * 213832142 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1282992853 6 213832142 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y25
  (h_ts : 2 ^ 25 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 25) = 1165552341 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165552341 = 6 * 194258723 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1165552341 6 194258723 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y26
  (h_ts : 2 ^ 25 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 26) = 930671317 := by decide
  rw [h_sub] at hp6
  have h_eq : 930671317 = 6 * 155111886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 930671317 6 155111886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y27
  (h_ts : 2 ^ 25 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 25 + 7 * 2 ^ 27) = 460909269 := by decide
  rw [h_sub] at hp6
  have h_eq : 460909269 = 6 * 76818211 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 460909269 6 76818211 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x25_y28
  (h_ts : 2 ^ 25 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1912602624 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x25_y29
  (h_ts : 2 ^ 25 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3791650816 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x25_y30
  (h_ts : 2 ^ 25 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7549747200 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x26_y1
  (h_ts : 2 ^ 26 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 1) = 1366878919 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366878919 = 6 * 227813153 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366878919 6 227813153 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y2
  (h_ts : 2 ^ 26 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 2) = 1366878905 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366878905 = 5 * 273375781 := by decide
  have hd : 5 ∣ 1366878905 := ⟨273375781, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1366878905 := by decide
  exact (not_prime_of_dvd 1366878905 5 hd h1 h2) hp

lemma proof_x26_y3
  (h_ts : 2 ^ 26 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 3) = 1366878877 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366878877 = 6 * 227813146 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366878877 6 227813146 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y4
  (h_ts : 2 ^ 26 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 4) = 1366878821 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366878821 = 7 * 195268403 := by decide
  have hd : 7 ∣ 1366878821 := ⟨195268403, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1366878821 := by decide
  exact (not_prime_of_dvd 1366878821 7 hd h1 h2) hp

lemma proof_x26_y5
  (h_ts : 2 ^ 26 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 5) = 1366878709 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366878709 = 6 * 227813118 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366878709 6 227813118 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y6
  (h_ts : 2 ^ 26 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 6) = 1366878485 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366878485 = 5 * 273375697 := by decide
  have hd : 5 ∣ 1366878485 := ⟨273375697, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1366878485 := by decide
  exact (not_prime_of_dvd 1366878485 5 hd h1 h2) hp

lemma proof_x26_y7
  (h_ts : 2 ^ 26 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 7) = 1366878037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366878037 = 6 * 227813006 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366878037 6 227813006 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y8
  (h_ts : 2 ^ 26 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 8) = 1366877141 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366877141 = 7 * 195268163 := by decide
  have hd : 7 ∣ 1366877141 := ⟨195268163, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1366877141 := by decide
  exact (not_prime_of_dvd 1366877141 7 hd h1 h2) hp

lemma proof_x26_y9
  (h_ts : 2 ^ 26 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 9) = 1366875349 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366875349 = 6 * 227812558 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366875349 6 227812558 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y10
  (h_ts : 2 ^ 26 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 10) = 1366871765 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366871765 = 5 * 273374353 := by decide
  have hd : 5 ∣ 1366871765 := ⟨273374353, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1366871765 := by decide
  exact (not_prime_of_dvd 1366871765 5 hd h1 h2) hp

lemma proof_x26_y11
  (h_ts : 2 ^ 26 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 11) = 1366864597 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366864597 = 6 * 227810766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366864597 6 227810766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y12
  (h_ts : 2 ^ 26 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 12) = 1366850261 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366850261 = 7 * 195264323 := by decide
  have hd : 7 ∣ 1366850261 := ⟨195264323, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1366850261 := by decide
  exact (not_prime_of_dvd 1366850261 7 hd h1 h2) hp

lemma proof_x26_y13
  (h_ts : 2 ^ 26 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 13) = 1366821589 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366821589 = 6 * 227803598 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366821589 6 227803598 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y14
  (h_ts : 2 ^ 26 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 14) = 1366764245 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366764245 = 5 * 273352849 := by decide
  have hd : 5 ∣ 1366764245 := ⟨273352849, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1366764245 := by decide
  exact (not_prime_of_dvd 1366764245 5 hd h1 h2) hp

lemma proof_x26_y15
  (h_ts : 2 ^ 26 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 15) = 1366649557 := by decide
  rw [h_sub] at hp6
  have h_eq : 1366649557 = 6 * 227774926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1366649557 6 227774926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y16
  (h_ts : 2 ^ 26 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 16) = 1366420181 := by decide
  rw [h_sub] at hp
  have hd_eq : 1366420181 = 7 * 195202883 := by decide
  have hd : 7 ∣ 1366420181 := ⟨195202883, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1366420181 := by decide
  exact (not_prime_of_dvd 1366420181 7 hd h1 h2) hp

lemma proof_x26_y17
  (h_ts : 2 ^ 26 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 17) = 1365961429 := by decide
  rw [h_sub] at hp6
  have h_eq : 1365961429 = 6 * 227660238 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1365961429 6 227660238 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y18
  (h_ts : 2 ^ 26 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 18) = 1365043925 := by decide
  rw [h_sub] at hp
  have hd_eq : 1365043925 = 5 * 273008785 := by decide
  have hd : 5 ∣ 1365043925 := ⟨273008785, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1365043925 := by decide
  exact (not_prime_of_dvd 1365043925 5 hd h1 h2) hp

lemma proof_x26_y19
  (h_ts : 2 ^ 26 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 19) = 1363208917 := by decide
  rw [h_sub] at hp6
  have h_eq : 1363208917 = 6 * 227201486 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1363208917 6 227201486 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y20
  (h_ts : 2 ^ 26 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 20) = 1359538901 := by decide
  rw [h_sub] at hp
  have hd_eq : 1359538901 = 7 * 194219843 := by decide
  have hd : 7 ∣ 1359538901 := ⟨194219843, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1359538901 := by decide
  exact (not_prime_of_dvd 1359538901 7 hd h1 h2) hp

lemma proof_x26_y21
  (h_ts : 2 ^ 26 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 21) = 1352198869 := by decide
  rw [h_sub] at hp6
  have h_eq : 1352198869 = 6 * 225366478 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1352198869 6 225366478 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y22
  (h_ts : 2 ^ 26 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 22) = 1337518805 := by decide
  rw [h_sub] at hp
  have hd_eq : 1337518805 = 5 * 267503761 := by decide
  have hd : 5 ∣ 1337518805 := ⟨267503761, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 1337518805 := by decide
  exact (not_prime_of_dvd 1337518805 5 hd h1 h2) hp

lemma proof_x26_y23
  (h_ts : 2 ^ 26 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 23) = 1308158677 := by decide
  rw [h_sub] at hp6
  have h_eq : 1308158677 = 6 * 218026446 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1308158677 6 218026446 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y24
  (h_ts : 2 ^ 26 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 24) = 1249438421 := by decide
  rw [h_sub] at hp
  have hd_eq : 1249438421 = 7 * 178491203 := by decide
  have hd : 7 ∣ 1249438421 := ⟨178491203, hd_eq⟩
  have h1 : 1 < 7 := by decide
  have h2 : 7 < 1249438421 := by decide
  exact (not_prime_of_dvd 1249438421 7 hd h1 h2) hp

lemma proof_x26_y25
  (h_ts : 2 ^ 26 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 25) = 1131997909 := by decide
  rw [h_sub] at hp6
  have h_eq : 1131997909 = 6 * 188666318 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1131997909 6 188666318 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y26
  (h_ts : 2 ^ 26 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 26) = 897116885 := by decide
  rw [h_sub] at hp
  have hd_eq : 897116885 = 5 * 179423377 := by decide
  have hd : 5 ∣ 897116885 := ⟨179423377, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 897116885 := by decide
  exact (not_prime_of_dvd 897116885 5 hd h1 h2) hp

lemma proof_x26_y27
  (h_ts : 2 ^ 26 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 26 + 7 * 2 ^ 27) = 427354837 := by decide
  rw [h_sub] at hp6
  have h_eq : 427354837 = 6 * 71225806 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 427354837 6 71225806 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x26_y28
  (h_ts : 2 ^ 26 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 1946157056 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x26_y29
  (h_ts : 2 ^ 26 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3825205248 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x26_y30
  (h_ts : 2 ^ 26 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7583301632 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x27_y1
  (h_ts : 2 ^ 27 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 1) = 1299770055 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299770055 = 6 * 216628342 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299770055 6 216628342 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y2
  (h_ts : 2 ^ 27 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 2) = 1299770041 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299770041 = 6 * 216628340 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299770041 6 216628340 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y3
  (h_ts : 2 ^ 27 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 3) = 1299770013 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299770013 = 6 * 216628335 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299770013 6 216628335 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y4
  (h_ts : 2 ^ 27 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 4) = 1299769957 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299769957 = 6 * 216628326 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299769957 6 216628326 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y5
  (h_ts : 2 ^ 27 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 5) = 1299769845 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299769845 = 6 * 216628307 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299769845 6 216628307 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y6
  (h_ts : 2 ^ 27 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 6) = 1299769621 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299769621 = 6 * 216628270 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299769621 6 216628270 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y7
  (h_ts : 2 ^ 27 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 7) = 1299769173 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299769173 = 6 * 216628195 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299769173 6 216628195 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y8
  (h_ts : 2 ^ 27 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 8) = 1299768277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299768277 = 6 * 216628046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299768277 6 216628046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y9
  (h_ts : 2 ^ 27 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 9) = 1299766485 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299766485 = 6 * 216627747 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299766485 6 216627747 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y10
  (h_ts : 2 ^ 27 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 10) = 1299762901 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299762901 = 6 * 216627150 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299762901 6 216627150 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y11
  (h_ts : 2 ^ 27 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 11) = 1299755733 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299755733 = 6 * 216625955 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299755733 6 216625955 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y12
  (h_ts : 2 ^ 27 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 12) = 1299741397 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299741397 = 6 * 216623566 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299741397 6 216623566 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y13
  (h_ts : 2 ^ 27 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 13) = 1299712725 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299712725 = 6 * 216618787 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299712725 6 216618787 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y14
  (h_ts : 2 ^ 27 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 14) = 1299655381 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299655381 = 6 * 216609230 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299655381 6 216609230 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y15
  (h_ts : 2 ^ 27 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 15) = 1299540693 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299540693 = 6 * 216590115 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1299540693 6 216590115 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y16
  (h_ts : 2 ^ 27 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 16) = 1299311317 := by decide
  rw [h_sub] at hp6
  have h_eq : 1299311317 = 6 * 216551886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1299311317 6 216551886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y17
  (h_ts : 2 ^ 27 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 17) = 1298852565 := by decide
  rw [h_sub] at hp6
  have h_eq : 1298852565 = 6 * 216475427 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1298852565 6 216475427 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y18
  (h_ts : 2 ^ 27 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 18) = 1297935061 := by decide
  rw [h_sub] at hp6
  have h_eq : 1297935061 = 6 * 216322510 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1297935061 6 216322510 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y19
  (h_ts : 2 ^ 27 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 19) = 1296100053 := by decide
  rw [h_sub] at hp6
  have h_eq : 1296100053 = 6 * 216016675 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1296100053 6 216016675 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y20
  (h_ts : 2 ^ 27 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 20) = 1292430037 := by decide
  rw [h_sub] at hp6
  have h_eq : 1292430037 = 6 * 215405006 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1292430037 6 215405006 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y21
  (h_ts : 2 ^ 27 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 21) = 1285090005 := by decide
  rw [h_sub] at hp6
  have h_eq : 1285090005 = 6 * 214181667 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1285090005 6 214181667 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y22
  (h_ts : 2 ^ 27 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 22) = 1270409941 := by decide
  rw [h_sub] at hp6
  have h_eq : 1270409941 = 6 * 211734990 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1270409941 6 211734990 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y23
  (h_ts : 2 ^ 27 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 23) = 1241049813 := by decide
  rw [h_sub] at hp6
  have h_eq : 1241049813 = 6 * 206841635 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1241049813 6 206841635 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y24
  (h_ts : 2 ^ 27 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 24) = 1182329557 := by decide
  rw [h_sub] at hp6
  have h_eq : 1182329557 = 6 * 197054926 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1182329557 6 197054926 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y25
  (h_ts : 2 ^ 27 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 25) = 1064889045 := by decide
  rw [h_sub] at hp6
  have h_eq : 1064889045 = 6 * 177481507 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 1064889045 6 177481507 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y26
  (h_ts : 2 ^ 27 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 26) = 830008021 := by decide
  rw [h_sub] at hp6
  have h_eq : 830008021 = 6 * 138334670 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 830008021 6 138334670 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y27
  (h_ts : 2 ^ 27 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 27 + 7 * 2 ^ 27) = 360245973 := by decide
  rw [h_sub] at hp6
  have h_eq : 360245973 = 6 * 60040995 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 360245973 6 60040995 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x27_y28
  (h_ts : 2 ^ 27 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 2013265920 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x27_y29
  (h_ts : 2 ^ 27 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 3892314112 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x27_y30
  (h_ts : 2 ^ 27 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7650410496 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x28_y1
  (h_ts : 2 ^ 28 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 1) = 1165552327 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165552327 = 6 * 194258721 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165552327 6 194258721 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y2
  (h_ts : 2 ^ 28 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 2) = 1165552313 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165552313 = 281 * 4147873 := by decide
  have hd : 281 ∣ 1165552313 := ⟨4147873, hd_eq⟩
  have h1 : 1 < 281 := by decide
  have h2 : 281 < 1165552313 := by decide
  exact (not_prime_of_dvd 1165552313 281 hd h1 h2) hp

lemma proof_x28_y3
  (h_ts : 2 ^ 28 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 3) = 1165552285 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165552285 = 6 * 194258714 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165552285 6 194258714 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y4
  (h_ts : 2 ^ 28 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 4) = 1165552229 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165552229 = 31 * 37598459 := by decide
  have hd : 31 ∣ 1165552229 := ⟨37598459, hd_eq⟩
  have h1 : 1 < 31 := by decide
  have h2 : 31 < 1165552229 := by decide
  exact (not_prime_of_dvd 1165552229 31 hd h1 h2) hp

lemma proof_x28_y5
  (h_ts : 2 ^ 28 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 5) = 1165552117 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165552117 = 6 * 194258686 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165552117 6 194258686 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y6
  (h_ts : 2 ^ 28 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 6) = 1165551893 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165551893 = 11 * 105959263 := by decide
  have hd : 11 ∣ 1165551893 := ⟨105959263, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1165551893 := by decide
  exact (not_prime_of_dvd 1165551893 11 hd h1 h2) hp

lemma proof_x28_y7
  (h_ts : 2 ^ 28 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 7) = 1165551445 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165551445 = 6 * 194258574 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165551445 6 194258574 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y8
  (h_ts : 2 ^ 28 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 8) = 1165550549 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165550549 = 17 * 68561797 := by decide
  have hd : 17 ∣ 1165550549 := ⟨68561797, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1165550549 := by decide
  exact (not_prime_of_dvd 1165550549 17 hd h1 h2) hp

lemma proof_x28_y9
  (h_ts : 2 ^ 28 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 9) = 1165548757 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165548757 = 6 * 194258126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165548757 6 194258126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y10
  (h_ts : 2 ^ 28 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 10) = 1165545173 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165545173 = 13 * 89657321 := by decide
  have hd : 13 ∣ 1165545173 := ⟨89657321, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1165545173 := by decide
  exact (not_prime_of_dvd 1165545173 13 hd h1 h2) hp

lemma proof_x28_y11
  (h_ts : 2 ^ 28 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 11) = 1165538005 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165538005 = 6 * 194256334 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165538005 6 194256334 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y12
  (h_ts : 2 ^ 28 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 12) = 1165523669 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165523669 = 19 * 61343351 := by decide
  have hd : 19 ∣ 1165523669 := ⟨61343351, hd_eq⟩
  have h1 : 1 < 19 := by decide
  have h2 : 19 < 1165523669 := by decide
  exact (not_prime_of_dvd 1165523669 19 hd h1 h2) hp

lemma proof_x28_y13
  (h_ts : 2 ^ 28 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 13) = 1165494997 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165494997 = 6 * 194249166 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165494997 6 194249166 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y14
  (h_ts : 2 ^ 28 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 14) = 1165437653 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165437653 = 31 * 37594763 := by decide
  have hd : 31 ∣ 1165437653 := ⟨37594763, hd_eq⟩
  have h1 : 1 < 31 := by decide
  have h2 : 31 < 1165437653 := by decide
  exact (not_prime_of_dvd 1165437653 31 hd h1 h2) hp

lemma proof_x28_y15
  (h_ts : 2 ^ 28 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 15) = 1165322965 := by decide
  rw [h_sub] at hp6
  have h_eq : 1165322965 = 6 * 194220494 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1165322965 6 194220494 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y16
  (h_ts : 2 ^ 28 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 16) = 1165093589 := by decide
  rw [h_sub] at hp
  have hd_eq : 1165093589 = 11 * 105917599 := by decide
  have hd : 11 ∣ 1165093589 := ⟨105917599, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 1165093589 := by decide
  exact (not_prime_of_dvd 1165093589 11 hd h1 h2) hp

lemma proof_x28_y17
  (h_ts : 2 ^ 28 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 17) = 1164634837 := by decide
  rw [h_sub] at hp6
  have h_eq : 1164634837 = 6 * 194105806 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1164634837 6 194105806 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y18
  (h_ts : 2 ^ 28 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 18) = 1163717333 := by decide
  rw [h_sub] at hp
  have hd_eq : 1163717333 = 631 * 1844243 := by decide
  have hd : 631 ∣ 1163717333 := ⟨1844243, hd_eq⟩
  have h1 : 1 < 631 := by decide
  have h2 : 631 < 1163717333 := by decide
  exact (not_prime_of_dvd 1163717333 631 hd h1 h2) hp

lemma proof_x28_y19
  (h_ts : 2 ^ 28 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 19) = 1161882325 := by decide
  rw [h_sub] at hp6
  have h_eq : 1161882325 = 6 * 193647054 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1161882325 6 193647054 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y20
  (h_ts : 2 ^ 28 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 20) = 1158212309 := by decide
  rw [h_sub] at hp
  have hd_eq : 1158212309 = 109 * 10625801 := by decide
  have hd : 109 ∣ 1158212309 := ⟨10625801, hd_eq⟩
  have h1 : 1 < 109 := by decide
  have h2 : 109 < 1158212309 := by decide
  exact (not_prime_of_dvd 1158212309 109 hd h1 h2) hp

lemma proof_x28_y21
  (h_ts : 2 ^ 28 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 21) = 1150872277 := by decide
  rw [h_sub] at hp6
  have h_eq : 1150872277 = 6 * 191812046 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1150872277 6 191812046 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y22
  (h_ts : 2 ^ 28 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 22) = 1136192213 := by decide
  rw [h_sub] at hp
  have hd_eq : 1136192213 = 13 * 87399401 := by decide
  have hd : 13 ∣ 1136192213 := ⟨87399401, hd_eq⟩
  have h1 : 1 < 13 := by decide
  have h2 : 13 < 1136192213 := by decide
  exact (not_prime_of_dvd 1136192213 13 hd h1 h2) hp

lemma proof_x28_y23
  (h_ts : 2 ^ 28 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 23) = 1106832085 := by decide
  rw [h_sub] at hp6
  have h_eq : 1106832085 = 6 * 184472014 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 1106832085 6 184472014 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y24
  (h_ts : 2 ^ 28 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 24) = 1048111829 := by decide
  rw [h_sub] at hp
  have hd_eq : 1048111829 = 17 * 61653637 := by decide
  have hd : 17 ∣ 1048111829 := ⟨61653637, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 1048111829 := by decide
  exact (not_prime_of_dvd 1048111829 17 hd h1 h2) hp

lemma proof_x28_y25
  (h_ts : 2 ^ 28 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 25) = 930671317 := by decide
  rw [h_sub] at hp6
  have h_eq : 930671317 = 6 * 155111886 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 930671317 6 155111886 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y26
  (h_ts : 2 ^ 28 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 26) = 695790293 := by decide
  rw [h_sub] at hp
  have hd_eq : 695790293 = 11 * 63253663 := by decide
  have hd : 11 ∣ 695790293 := ⟨63253663, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 695790293 := by decide
  exact (not_prime_of_dvd 695790293 11 hd h1 h2) hp

lemma proof_x28_y27
  (h_ts : 2 ^ 28 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 28 + 7 * 2 ^ 27) = 226028245 := by decide
  rw [h_sub] at hp6
  have h_eq : 226028245 = 6 * 37671374 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 226028245 6 37671374 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x28_y28
  (h_ts : 2 ^ 28 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 2147483648 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x28_y29
  (h_ts : 2 ^ 28 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 4026531840 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x28_y30
  (h_ts : 2 ^ 28 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 7784628224 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x29_y1
  (h_ts : 2 ^ 29 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 1) = 897116871 := by decide
  rw [h_sub] at hp6
  have h_eq : 897116871 = 6 * 149519478 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897116871 6 149519478 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y2
  (h_ts : 2 ^ 29 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 2) = 897116857 := by decide
  rw [h_sub] at hp6
  have h_eq : 897116857 = 6 * 149519476 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897116857 6 149519476 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y3
  (h_ts : 2 ^ 29 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 3) = 897116829 := by decide
  rw [h_sub] at hp6
  have h_eq : 897116829 = 6 * 149519471 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897116829 6 149519471 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y4
  (h_ts : 2 ^ 29 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 4) = 897116773 := by decide
  rw [h_sub] at hp6
  have h_eq : 897116773 = 6 * 149519462 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897116773 6 149519462 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y5
  (h_ts : 2 ^ 29 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 5) = 897116661 := by decide
  rw [h_sub] at hp6
  have h_eq : 897116661 = 6 * 149519443 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897116661 6 149519443 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y6
  (h_ts : 2 ^ 29 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 6) = 897116437 := by decide
  rw [h_sub] at hp6
  have h_eq : 897116437 = 6 * 149519406 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897116437 6 149519406 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y7
  (h_ts : 2 ^ 29 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 7) = 897115989 := by decide
  rw [h_sub] at hp6
  have h_eq : 897115989 = 6 * 149519331 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897115989 6 149519331 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y8
  (h_ts : 2 ^ 29 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 8) = 897115093 := by decide
  rw [h_sub] at hp6
  have h_eq : 897115093 = 6 * 149519182 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897115093 6 149519182 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y9
  (h_ts : 2 ^ 29 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 9) = 897113301 := by decide
  rw [h_sub] at hp6
  have h_eq : 897113301 = 6 * 149518883 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897113301 6 149518883 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y10
  (h_ts : 2 ^ 29 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 10) = 897109717 := by decide
  rw [h_sub] at hp6
  have h_eq : 897109717 = 6 * 149518286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897109717 6 149518286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y11
  (h_ts : 2 ^ 29 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 11) = 897102549 := by decide
  rw [h_sub] at hp6
  have h_eq : 897102549 = 6 * 149517091 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897102549 6 149517091 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y12
  (h_ts : 2 ^ 29 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 12) = 897088213 := by decide
  rw [h_sub] at hp6
  have h_eq : 897088213 = 6 * 149514702 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897088213 6 149514702 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y13
  (h_ts : 2 ^ 29 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 13) = 897059541 := by decide
  rw [h_sub] at hp6
  have h_eq : 897059541 = 6 * 149509923 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 897059541 6 149509923 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y14
  (h_ts : 2 ^ 29 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 14) = 897002197 := by decide
  rw [h_sub] at hp6
  have h_eq : 897002197 = 6 * 149500366 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 897002197 6 149500366 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y15
  (h_ts : 2 ^ 29 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 15) = 896887509 := by decide
  rw [h_sub] at hp6
  have h_eq : 896887509 = 6 * 149481251 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 896887509 6 149481251 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y16
  (h_ts : 2 ^ 29 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 16) = 896658133 := by decide
  rw [h_sub] at hp6
  have h_eq : 896658133 = 6 * 149443022 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 896658133 6 149443022 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y17
  (h_ts : 2 ^ 29 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 17) = 896199381 := by decide
  rw [h_sub] at hp6
  have h_eq : 896199381 = 6 * 149366563 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 896199381 6 149366563 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y18
  (h_ts : 2 ^ 29 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 18) = 895281877 := by decide
  rw [h_sub] at hp6
  have h_eq : 895281877 = 6 * 149213646 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 895281877 6 149213646 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y19
  (h_ts : 2 ^ 29 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 19) = 893446869 := by decide
  rw [h_sub] at hp6
  have h_eq : 893446869 = 6 * 148907811 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 893446869 6 148907811 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y20
  (h_ts : 2 ^ 29 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 20) = 889776853 := by decide
  rw [h_sub] at hp6
  have h_eq : 889776853 = 6 * 148296142 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 889776853 6 148296142 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y21
  (h_ts : 2 ^ 29 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 21) = 882436821 := by decide
  rw [h_sub] at hp6
  have h_eq : 882436821 = 6 * 147072803 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 882436821 6 147072803 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y22
  (h_ts : 2 ^ 29 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 22) = 867756757 := by decide
  rw [h_sub] at hp6
  have h_eq : 867756757 = 6 * 144626126 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 867756757 6 144626126 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y23
  (h_ts : 2 ^ 29 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 23) = 838396629 := by decide
  rw [h_sub] at hp6
  have h_eq : 838396629 = 6 * 139732771 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 838396629 6 139732771 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y24
  (h_ts : 2 ^ 29 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 24) = 779676373 := by decide
  rw [h_sub] at hp6
  have h_eq : 779676373 = 6 * 129946062 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 779676373 6 129946062 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y25
  (h_ts : 2 ^ 29 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 25) = 662235861 := by decide
  rw [h_sub] at hp6
  have h_eq : 662235861 = 6 * 110372643 + 3 := by decide
  have h_lt : 3 < 6 := by decide
  have hmod := mod_eq_of_div 662235861 6 110372643 3 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y26
  (h_ts : 2 ^ 29 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 29 + 7 * 2 ^ 26) = 427354837 := by decide
  rw [h_sub] at hp6
  have h_eq : 427354837 = 6 * 71225806 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 427354837 6 71225806 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x29_y27
  (h_ts : 2 ^ 29 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  change 1476395008 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x29_y28
  (h_ts : 2 ^ 29 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 2415919104 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x29_y29
  (h_ts : 2 ^ 29 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 4294967296 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x29_y30
  (h_ts : 2 ^ 29 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 8053063680 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x30_y1
  (h_ts : 2 ^ 30 + 7 * 2 ^ 1 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 1)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 1)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 1) = 360245959 := by decide
  rw [h_sub] at hp6
  have h_eq : 360245959 = 6 * 60040993 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360245959 6 60040993 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y2
  (h_ts : 2 ^ 30 + 7 * 2 ^ 2 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 2)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 2)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 2) = 360245945 := by decide
  rw [h_sub] at hp
  have hd_eq : 360245945 = 5 * 72049189 := by decide
  have hd : 5 ∣ 360245945 := ⟨72049189, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 360245945 := by decide
  exact (not_prime_of_dvd 360245945 5 hd h1 h2) hp

lemma proof_x30_y3
  (h_ts : 2 ^ 30 + 7 * 2 ^ 3 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 3)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 3)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 3) = 360245917 := by decide
  rw [h_sub] at hp6
  have h_eq : 360245917 = 6 * 60040986 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360245917 6 60040986 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y4
  (h_ts : 2 ^ 30 + 7 * 2 ^ 4 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 4)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 4)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 4) = 360245861 := by decide
  rw [h_sub] at hp
  have hd_eq : 360245861 = 17 * 21190933 := by decide
  have hd : 17 ∣ 360245861 := ⟨21190933, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 360245861 := by decide
  exact (not_prime_of_dvd 360245861 17 hd h1 h2) hp

lemma proof_x30_y5
  (h_ts : 2 ^ 30 + 7 * 2 ^ 5 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 5)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 5)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 5) = 360245749 := by decide
  rw [h_sub] at hp6
  have h_eq : 360245749 = 6 * 60040958 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360245749 6 60040958 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y6
  (h_ts : 2 ^ 30 + 7 * 2 ^ 6 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 6)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 6)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 6) = 360245525 := by decide
  rw [h_sub] at hp
  have hd_eq : 360245525 = 5 * 72049105 := by decide
  have hd : 5 ∣ 360245525 := ⟨72049105, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 360245525 := by decide
  exact (not_prime_of_dvd 360245525 5 hd h1 h2) hp

lemma proof_x30_y7
  (h_ts : 2 ^ 30 + 7 * 2 ^ 7 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 7)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 7)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 7) = 360245077 := by decide
  rw [h_sub] at hp6
  have h_eq : 360245077 = 6 * 60040846 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360245077 6 60040846 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y8
  (h_ts : 2 ^ 30 + 7 * 2 ^ 8 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 8)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 8)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 8) = 360244181 := by decide
  rw [h_sub] at hp
  have hd_eq : 360244181 = 11 * 32749471 := by decide
  have hd : 11 ∣ 360244181 := ⟨32749471, hd_eq⟩
  have h1 : 1 < 11 := by decide
  have h2 : 11 < 360244181 := by decide
  exact (not_prime_of_dvd 360244181 11 hd h1 h2) hp

lemma proof_x30_y9
  (h_ts : 2 ^ 30 + 7 * 2 ^ 9 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 9)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 9)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 9) = 360242389 := by decide
  rw [h_sub] at hp6
  have h_eq : 360242389 = 6 * 60040398 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360242389 6 60040398 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y10
  (h_ts : 2 ^ 30 + 7 * 2 ^ 10 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 10)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 10)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 10) = 360238805 := by decide
  rw [h_sub] at hp
  have hd_eq : 360238805 = 5 * 72047761 := by decide
  have hd : 5 ∣ 360238805 := ⟨72047761, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 360238805 := by decide
  exact (not_prime_of_dvd 360238805 5 hd h1 h2) hp

lemma proof_x30_y11
  (h_ts : 2 ^ 30 + 7 * 2 ^ 11 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 11)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 11)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 11) = 360231637 := by decide
  rw [h_sub] at hp6
  have h_eq : 360231637 = 6 * 60038606 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360231637 6 60038606 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y12
  (h_ts : 2 ^ 30 + 7 * 2 ^ 12 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 12)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 12)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 12) = 360217301 := by decide
  rw [h_sub] at hp
  have hd_eq : 360217301 = 17 * 21189253 := by decide
  have hd : 17 ∣ 360217301 := ⟨21189253, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 360217301 := by decide
  exact (not_prime_of_dvd 360217301 17 hd h1 h2) hp

lemma proof_x30_y13
  (h_ts : 2 ^ 30 + 7 * 2 ^ 13 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 13)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 13)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 13) = 360188629 := by decide
  rw [h_sub] at hp6
  have h_eq : 360188629 = 6 * 60031438 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360188629 6 60031438 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y14
  (h_ts : 2 ^ 30 + 7 * 2 ^ 14 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 14)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 14)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 14) = 360131285 := by decide
  rw [h_sub] at hp
  have hd_eq : 360131285 = 5 * 72026257 := by decide
  have hd : 5 ∣ 360131285 := ⟨72026257, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 360131285 := by decide
  exact (not_prime_of_dvd 360131285 5 hd h1 h2) hp

lemma proof_x30_y15
  (h_ts : 2 ^ 30 + 7 * 2 ^ 15 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 15)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 15)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 15) = 360016597 := by decide
  rw [h_sub] at hp6
  have h_eq : 360016597 = 6 * 60002766 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 360016597 6 60002766 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y16
  (h_ts : 2 ^ 30 + 7 * 2 ^ 16 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 16)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 16)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 16) = 359787221 := by decide
  rw [h_sub] at hp
  have hd_eq : 359787221 = 373 * 964577 := by decide
  have hd : 373 ∣ 359787221 := ⟨964577, hd_eq⟩
  have h1 : 1 < 373 := by decide
  have h2 : 373 < 359787221 := by decide
  exact (not_prime_of_dvd 359787221 373 hd h1 h2) hp

lemma proof_x30_y17
  (h_ts : 2 ^ 30 + 7 * 2 ^ 17 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 17)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 17)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 17) = 359328469 := by decide
  rw [h_sub] at hp6
  have h_eq : 359328469 = 6 * 59888078 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 359328469 6 59888078 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y18
  (h_ts : 2 ^ 30 + 7 * 2 ^ 18 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 18)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 18)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 18) = 358410965 := by decide
  rw [h_sub] at hp
  have hd_eq : 358410965 = 5 * 71682193 := by decide
  have hd : 5 ∣ 358410965 := ⟨71682193, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 358410965 := by decide
  exact (not_prime_of_dvd 358410965 5 hd h1 h2) hp

lemma proof_x30_y19
  (h_ts : 2 ^ 30 + 7 * 2 ^ 19 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 19)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 19)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 19) = 356575957 := by decide
  rw [h_sub] at hp6
  have h_eq : 356575957 = 6 * 59429326 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 356575957 6 59429326 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y20
  (h_ts : 2 ^ 30 + 7 * 2 ^ 20 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 20)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 20)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 20) = 352905941 := by decide
  rw [h_sub] at hp
  have hd_eq : 352905941 = 17 * 20759173 := by decide
  have hd : 17 ∣ 352905941 := ⟨20759173, hd_eq⟩
  have h1 : 1 < 17 := by decide
  have h2 : 17 < 352905941 := by decide
  exact (not_prime_of_dvd 352905941 17 hd h1 h2) hp

lemma proof_x30_y21
  (h_ts : 2 ^ 30 + 7 * 2 ^ 21 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 21)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 21)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 21) = 345565909 := by decide
  rw [h_sub] at hp6
  have h_eq : 345565909 = 6 * 57594318 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 345565909 6 57594318 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y22
  (h_ts : 2 ^ 30 + 7 * 2 ^ 22 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 22)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 22)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 22) = 330885845 := by decide
  rw [h_sub] at hp
  have hd_eq : 330885845 = 5 * 66177169 := by decide
  have hd : 5 ∣ 330885845 := ⟨66177169, hd_eq⟩
  have h1 : 1 < 5 := by decide
  have h2 : 5 < 330885845 := by decide
  exact (not_prime_of_dvd 330885845 5 hd h1 h2) hp

lemma proof_x30_y23
  (h_ts : 2 ^ 30 + 7 * 2 ^ 23 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 23)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 23)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 23) = 301525717 := by decide
  rw [h_sub] at hp6
  have h_eq : 301525717 = 6 * 50254286 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 301525717 6 50254286 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y24
  (h_ts : 2 ^ 30 + 7 * 2 ^ 24 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 24)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 24)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 24) = 242805461 := by decide
  rw [h_sub] at hp
  have hd_eq : 242805461 = 83 * 2925367 := by decide
  have hd : 83 ∣ 242805461 := ⟨2925367, hd_eq⟩
  have h1 : 1 < 83 := by decide
  have h2 : 83 < 242805461 := by decide
  exact (not_prime_of_dvd 242805461 83 hd h1 h2) hp

lemma proof_x30_y25
  (h_ts : 2 ^ 30 + 7 * 2 ^ 25 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 25)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 25)) % 6 = 5) : False := by
  have h_sub : 1433987797 - (2 ^ 30 + 7 * 2 ^ 25) = 125364949 := by decide
  rw [h_sub] at hp6
  have h_eq : 125364949 = 6 * 20894158 + 1 := by decide
  have h_lt : 1 < 6 := by decide
  have hmod := mod_eq_of_div 125364949 6 20894158 1 h_eq h_lt
  rw [hmod] at hp6
  exact absurd hp6 (by decide)

lemma proof_x30_y26
  (h_ts : 2 ^ 30 + 7 * 2 ^ 26 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 26)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 26)) % 6 = 5) : False := by
  change 1543503872 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x30_y27
  (h_ts : 2 ^ 30 + 7 * 2 ^ 27 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 27)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 27)) % 6 = 5) : False := by
  change 2013265920 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x30_y28
  (h_ts : 2 ^ 30 + 7 * 2 ^ 28 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 28)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 28)) % 6 = 5) : False := by
  change 2952790016 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x30_y29
  (h_ts : 2 ^ 30 + 7 * 2 ^ 29 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 29)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 29)) % 6 = 5) : False := by
  change 4831838208 < 1433987797 at h_ts
  revert h_ts; decide

lemma proof_x30_y30
  (h_ts : 2 ^ 30 + 7 * 2 ^ 30 < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ 30)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ 30)) % 6 = 5) : False := by
  change 8589934592 < 1433987797 at h_ts
  revert h_ts; decide

lemma lemma_x1 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 1 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 1 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x1_y1 h_ts hp hp6
  · exact proof_x1_y2 h_ts hp hp6
  · exact proof_x1_y3 h_ts hp hp6
  · exact proof_x1_y4 h_ts hp hp6
  · exact proof_x1_y5 h_ts hp hp6
  · exact proof_x1_y6 h_ts hp hp6
  · exact proof_x1_y7 h_ts hp hp6
  · exact proof_x1_y8 h_ts hp hp6
  · exact proof_x1_y9 h_ts hp hp6
  · exact proof_x1_y10 h_ts hp hp6
  · exact proof_x1_y11 h_ts hp hp6
  · exact proof_x1_y12 h_ts hp hp6
  · exact proof_x1_y13 h_ts hp hp6
  · exact proof_x1_y14 h_ts hp hp6
  · exact proof_x1_y15 h_ts hp hp6
  · exact proof_x1_y16 h_ts hp hp6
  · exact proof_x1_y17 h_ts hp hp6
  · exact proof_x1_y18 h_ts hp hp6
  · exact proof_x1_y19 h_ts hp hp6
  · exact proof_x1_y20 h_ts hp hp6
  · exact proof_x1_y21 h_ts hp hp6
  · exact proof_x1_y22 h_ts hp hp6
  · exact proof_x1_y23 h_ts hp hp6
  · exact proof_x1_y24 h_ts hp hp6
  · exact proof_x1_y25 h_ts hp hp6
  · exact proof_x1_y26 h_ts hp hp6
  · exact proof_x1_y27 h_ts hp hp6
  · exact proof_x1_y28 h_ts hp hp6
  · exact proof_x1_y29 h_ts hp hp6
  · exact proof_x1_y30 h_ts hp hp6

lemma lemma_x2 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 2 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 2 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x2_y1 h_ts hp hp6
  · exact proof_x2_y2 h_ts hp hp6
  · exact proof_x2_y3 h_ts hp hp6
  · exact proof_x2_y4 h_ts hp hp6
  · exact proof_x2_y5 h_ts hp hp6
  · exact proof_x2_y6 h_ts hp hp6
  · exact proof_x2_y7 h_ts hp hp6
  · exact proof_x2_y8 h_ts hp hp6
  · exact proof_x2_y9 h_ts hp hp6
  · exact proof_x2_y10 h_ts hp hp6
  · exact proof_x2_y11 h_ts hp hp6
  · exact proof_x2_y12 h_ts hp hp6
  · exact proof_x2_y13 h_ts hp hp6
  · exact proof_x2_y14 h_ts hp hp6
  · exact proof_x2_y15 h_ts hp hp6
  · exact proof_x2_y16 h_ts hp hp6
  · exact proof_x2_y17 h_ts hp hp6
  · exact proof_x2_y18 h_ts hp hp6
  · exact proof_x2_y19 h_ts hp hp6
  · exact proof_x2_y20 h_ts hp hp6
  · exact proof_x2_y21 h_ts hp hp6
  · exact proof_x2_y22 h_ts hp hp6
  · exact proof_x2_y23 h_ts hp hp6
  · exact proof_x2_y24 h_ts hp hp6
  · exact proof_x2_y25 h_ts hp hp6
  · exact proof_x2_y26 h_ts hp hp6
  · exact proof_x2_y27 h_ts hp hp6
  · exact proof_x2_y28 h_ts hp hp6
  · exact proof_x2_y29 h_ts hp hp6
  · exact proof_x2_y30 h_ts hp hp6

lemma lemma_x3 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 3 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 3 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x3_y1 h_ts hp hp6
  · exact proof_x3_y2 h_ts hp hp6
  · exact proof_x3_y3 h_ts hp hp6
  · exact proof_x3_y4 h_ts hp hp6
  · exact proof_x3_y5 h_ts hp hp6
  · exact proof_x3_y6 h_ts hp hp6
  · exact proof_x3_y7 h_ts hp hp6
  · exact proof_x3_y8 h_ts hp hp6
  · exact proof_x3_y9 h_ts hp hp6
  · exact proof_x3_y10 h_ts hp hp6
  · exact proof_x3_y11 h_ts hp hp6
  · exact proof_x3_y12 h_ts hp hp6
  · exact proof_x3_y13 h_ts hp hp6
  · exact proof_x3_y14 h_ts hp hp6
  · exact proof_x3_y15 h_ts hp hp6
  · exact proof_x3_y16 h_ts hp hp6
  · exact proof_x3_y17 h_ts hp hp6
  · exact proof_x3_y18 h_ts hp hp6
  · exact proof_x3_y19 h_ts hp hp6
  · exact proof_x3_y20 h_ts hp hp6
  · exact proof_x3_y21 h_ts hp hp6
  · exact proof_x3_y22 h_ts hp hp6
  · exact proof_x3_y23 h_ts hp hp6
  · exact proof_x3_y24 h_ts hp hp6
  · exact proof_x3_y25 h_ts hp hp6
  · exact proof_x3_y26 h_ts hp hp6
  · exact proof_x3_y27 h_ts hp hp6
  · exact proof_x3_y28 h_ts hp hp6
  · exact proof_x3_y29 h_ts hp hp6
  · exact proof_x3_y30 h_ts hp hp6

lemma lemma_x4 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 4 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 4 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x4_y1 h_ts hp hp6
  · exact proof_x4_y2 h_ts hp hp6
  · exact proof_x4_y3 h_ts hp hp6
  · exact proof_x4_y4 h_ts hp hp6
  · exact proof_x4_y5 h_ts hp hp6
  · exact proof_x4_y6 h_ts hp hp6
  · exact proof_x4_y7 h_ts hp hp6
  · exact proof_x4_y8 h_ts hp hp6
  · exact proof_x4_y9 h_ts hp hp6
  · exact proof_x4_y10 h_ts hp hp6
  · exact proof_x4_y11 h_ts hp hp6
  · exact proof_x4_y12 h_ts hp hp6
  · exact proof_x4_y13 h_ts hp hp6
  · exact proof_x4_y14 h_ts hp hp6
  · exact proof_x4_y15 h_ts hp hp6
  · exact proof_x4_y16 h_ts hp hp6
  · exact proof_x4_y17 h_ts hp hp6
  · exact proof_x4_y18 h_ts hp hp6
  · exact proof_x4_y19 h_ts hp hp6
  · exact proof_x4_y20 h_ts hp hp6
  · exact proof_x4_y21 h_ts hp hp6
  · exact proof_x4_y22 h_ts hp hp6
  · exact proof_x4_y23 h_ts hp hp6
  · exact proof_x4_y24 h_ts hp hp6
  · exact proof_x4_y25 h_ts hp hp6
  · exact proof_x4_y26 h_ts hp hp6
  · exact proof_x4_y27 h_ts hp hp6
  · exact proof_x4_y28 h_ts hp hp6
  · exact proof_x4_y29 h_ts hp hp6
  · exact proof_x4_y30 h_ts hp hp6

lemma lemma_x5 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 5 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 5 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x5_y1 h_ts hp hp6
  · exact proof_x5_y2 h_ts hp hp6
  · exact proof_x5_y3 h_ts hp hp6
  · exact proof_x5_y4 h_ts hp hp6
  · exact proof_x5_y5 h_ts hp hp6
  · exact proof_x5_y6 h_ts hp hp6
  · exact proof_x5_y7 h_ts hp hp6
  · exact proof_x5_y8 h_ts hp hp6
  · exact proof_x5_y9 h_ts hp hp6
  · exact proof_x5_y10 h_ts hp hp6
  · exact proof_x5_y11 h_ts hp hp6
  · exact proof_x5_y12 h_ts hp hp6
  · exact proof_x5_y13 h_ts hp hp6
  · exact proof_x5_y14 h_ts hp hp6
  · exact proof_x5_y15 h_ts hp hp6
  · exact proof_x5_y16 h_ts hp hp6
  · exact proof_x5_y17 h_ts hp hp6
  · exact proof_x5_y18 h_ts hp hp6
  · exact proof_x5_y19 h_ts hp hp6
  · exact proof_x5_y20 h_ts hp hp6
  · exact proof_x5_y21 h_ts hp hp6
  · exact proof_x5_y22 h_ts hp hp6
  · exact proof_x5_y23 h_ts hp hp6
  · exact proof_x5_y24 h_ts hp hp6
  · exact proof_x5_y25 h_ts hp hp6
  · exact proof_x5_y26 h_ts hp hp6
  · exact proof_x5_y27 h_ts hp hp6
  · exact proof_x5_y28 h_ts hp hp6
  · exact proof_x5_y29 h_ts hp hp6
  · exact proof_x5_y30 h_ts hp hp6

lemma lemma_x6 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 6 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 6 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x6_y1 h_ts hp hp6
  · exact proof_x6_y2 h_ts hp hp6
  · exact proof_x6_y3 h_ts hp hp6
  · exact proof_x6_y4 h_ts hp hp6
  · exact proof_x6_y5 h_ts hp hp6
  · exact proof_x6_y6 h_ts hp hp6
  · exact proof_x6_y7 h_ts hp hp6
  · exact proof_x6_y8 h_ts hp hp6
  · exact proof_x6_y9 h_ts hp hp6
  · exact proof_x6_y10 h_ts hp hp6
  · exact proof_x6_y11 h_ts hp hp6
  · exact proof_x6_y12 h_ts hp hp6
  · exact proof_x6_y13 h_ts hp hp6
  · exact proof_x6_y14 h_ts hp hp6
  · exact proof_x6_y15 h_ts hp hp6
  · exact proof_x6_y16 h_ts hp hp6
  · exact proof_x6_y17 h_ts hp hp6
  · exact proof_x6_y18 h_ts hp hp6
  · exact proof_x6_y19 h_ts hp hp6
  · exact proof_x6_y20 h_ts hp hp6
  · exact proof_x6_y21 h_ts hp hp6
  · exact proof_x6_y22 h_ts hp hp6
  · exact proof_x6_y23 h_ts hp hp6
  · exact proof_x6_y24 h_ts hp hp6
  · exact proof_x6_y25 h_ts hp hp6
  · exact proof_x6_y26 h_ts hp hp6
  · exact proof_x6_y27 h_ts hp hp6
  · exact proof_x6_y28 h_ts hp hp6
  · exact proof_x6_y29 h_ts hp hp6
  · exact proof_x6_y30 h_ts hp hp6

lemma lemma_x7 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 7 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 7 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x7_y1 h_ts hp hp6
  · exact proof_x7_y2 h_ts hp hp6
  · exact proof_x7_y3 h_ts hp hp6
  · exact proof_x7_y4 h_ts hp hp6
  · exact proof_x7_y5 h_ts hp hp6
  · exact proof_x7_y6 h_ts hp hp6
  · exact proof_x7_y7 h_ts hp hp6
  · exact proof_x7_y8 h_ts hp hp6
  · exact proof_x7_y9 h_ts hp hp6
  · exact proof_x7_y10 h_ts hp hp6
  · exact proof_x7_y11 h_ts hp hp6
  · exact proof_x7_y12 h_ts hp hp6
  · exact proof_x7_y13 h_ts hp hp6
  · exact proof_x7_y14 h_ts hp hp6
  · exact proof_x7_y15 h_ts hp hp6
  · exact proof_x7_y16 h_ts hp hp6
  · exact proof_x7_y17 h_ts hp hp6
  · exact proof_x7_y18 h_ts hp hp6
  · exact proof_x7_y19 h_ts hp hp6
  · exact proof_x7_y20 h_ts hp hp6
  · exact proof_x7_y21 h_ts hp hp6
  · exact proof_x7_y22 h_ts hp hp6
  · exact proof_x7_y23 h_ts hp hp6
  · exact proof_x7_y24 h_ts hp hp6
  · exact proof_x7_y25 h_ts hp hp6
  · exact proof_x7_y26 h_ts hp hp6
  · exact proof_x7_y27 h_ts hp hp6
  · exact proof_x7_y28 h_ts hp hp6
  · exact proof_x7_y29 h_ts hp hp6
  · exact proof_x7_y30 h_ts hp hp6

lemma lemma_x8 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 8 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 8 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x8_y1 h_ts hp hp6
  · exact proof_x8_y2 h_ts hp hp6
  · exact proof_x8_y3 h_ts hp hp6
  · exact proof_x8_y4 h_ts hp hp6
  · exact proof_x8_y5 h_ts hp hp6
  · exact proof_x8_y6 h_ts hp hp6
  · exact proof_x8_y7 h_ts hp hp6
  · exact proof_x8_y8 h_ts hp hp6
  · exact proof_x8_y9 h_ts hp hp6
  · exact proof_x8_y10 h_ts hp hp6
  · exact proof_x8_y11 h_ts hp hp6
  · exact proof_x8_y12 h_ts hp hp6
  · exact proof_x8_y13 h_ts hp hp6
  · exact proof_x8_y14 h_ts hp hp6
  · exact proof_x8_y15 h_ts hp hp6
  · exact proof_x8_y16 h_ts hp hp6
  · exact proof_x8_y17 h_ts hp hp6
  · exact proof_x8_y18 h_ts hp hp6
  · exact proof_x8_y19 h_ts hp hp6
  · exact proof_x8_y20 h_ts hp hp6
  · exact proof_x8_y21 h_ts hp hp6
  · exact proof_x8_y22 h_ts hp hp6
  · exact proof_x8_y23 h_ts hp hp6
  · exact proof_x8_y24 h_ts hp hp6
  · exact proof_x8_y25 h_ts hp hp6
  · exact proof_x8_y26 h_ts hp hp6
  · exact proof_x8_y27 h_ts hp hp6
  · exact proof_x8_y28 h_ts hp hp6
  · exact proof_x8_y29 h_ts hp hp6
  · exact proof_x8_y30 h_ts hp hp6

lemma lemma_x9 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 9 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 9 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x9_y1 h_ts hp hp6
  · exact proof_x9_y2 h_ts hp hp6
  · exact proof_x9_y3 h_ts hp hp6
  · exact proof_x9_y4 h_ts hp hp6
  · exact proof_x9_y5 h_ts hp hp6
  · exact proof_x9_y6 h_ts hp hp6
  · exact proof_x9_y7 h_ts hp hp6
  · exact proof_x9_y8 h_ts hp hp6
  · exact proof_x9_y9 h_ts hp hp6
  · exact proof_x9_y10 h_ts hp hp6
  · exact proof_x9_y11 h_ts hp hp6
  · exact proof_x9_y12 h_ts hp hp6
  · exact proof_x9_y13 h_ts hp hp6
  · exact proof_x9_y14 h_ts hp hp6
  · exact proof_x9_y15 h_ts hp hp6
  · exact proof_x9_y16 h_ts hp hp6
  · exact proof_x9_y17 h_ts hp hp6
  · exact proof_x9_y18 h_ts hp hp6
  · exact proof_x9_y19 h_ts hp hp6
  · exact proof_x9_y20 h_ts hp hp6
  · exact proof_x9_y21 h_ts hp hp6
  · exact proof_x9_y22 h_ts hp hp6
  · exact proof_x9_y23 h_ts hp hp6
  · exact proof_x9_y24 h_ts hp hp6
  · exact proof_x9_y25 h_ts hp hp6
  · exact proof_x9_y26 h_ts hp hp6
  · exact proof_x9_y27 h_ts hp hp6
  · exact proof_x9_y28 h_ts hp hp6
  · exact proof_x9_y29 h_ts hp hp6
  · exact proof_x9_y30 h_ts hp hp6

lemma lemma_x10 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 10 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 10 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x10_y1 h_ts hp hp6
  · exact proof_x10_y2 h_ts hp hp6
  · exact proof_x10_y3 h_ts hp hp6
  · exact proof_x10_y4 h_ts hp hp6
  · exact proof_x10_y5 h_ts hp hp6
  · exact proof_x10_y6 h_ts hp hp6
  · exact proof_x10_y7 h_ts hp hp6
  · exact proof_x10_y8 h_ts hp hp6
  · exact proof_x10_y9 h_ts hp hp6
  · exact proof_x10_y10 h_ts hp hp6
  · exact proof_x10_y11 h_ts hp hp6
  · exact proof_x10_y12 h_ts hp hp6
  · exact proof_x10_y13 h_ts hp hp6
  · exact proof_x10_y14 h_ts hp hp6
  · exact proof_x10_y15 h_ts hp hp6
  · exact proof_x10_y16 h_ts hp hp6
  · exact proof_x10_y17 h_ts hp hp6
  · exact proof_x10_y18 h_ts hp hp6
  · exact proof_x10_y19 h_ts hp hp6
  · exact proof_x10_y20 h_ts hp hp6
  · exact proof_x10_y21 h_ts hp hp6
  · exact proof_x10_y22 h_ts hp hp6
  · exact proof_x10_y23 h_ts hp hp6
  · exact proof_x10_y24 h_ts hp hp6
  · exact proof_x10_y25 h_ts hp hp6
  · exact proof_x10_y26 h_ts hp hp6
  · exact proof_x10_y27 h_ts hp hp6
  · exact proof_x10_y28 h_ts hp hp6
  · exact proof_x10_y29 h_ts hp hp6
  · exact proof_x10_y30 h_ts hp hp6

lemma lemma_x11 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 11 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 11 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x11_y1 h_ts hp hp6
  · exact proof_x11_y2 h_ts hp hp6
  · exact proof_x11_y3 h_ts hp hp6
  · exact proof_x11_y4 h_ts hp hp6
  · exact proof_x11_y5 h_ts hp hp6
  · exact proof_x11_y6 h_ts hp hp6
  · exact proof_x11_y7 h_ts hp hp6
  · exact proof_x11_y8 h_ts hp hp6
  · exact proof_x11_y9 h_ts hp hp6
  · exact proof_x11_y10 h_ts hp hp6
  · exact proof_x11_y11 h_ts hp hp6
  · exact proof_x11_y12 h_ts hp hp6
  · exact proof_x11_y13 h_ts hp hp6
  · exact proof_x11_y14 h_ts hp hp6
  · exact proof_x11_y15 h_ts hp hp6
  · exact proof_x11_y16 h_ts hp hp6
  · exact proof_x11_y17 h_ts hp hp6
  · exact proof_x11_y18 h_ts hp hp6
  · exact proof_x11_y19 h_ts hp hp6
  · exact proof_x11_y20 h_ts hp hp6
  · exact proof_x11_y21 h_ts hp hp6
  · exact proof_x11_y22 h_ts hp hp6
  · exact proof_x11_y23 h_ts hp hp6
  · exact proof_x11_y24 h_ts hp hp6
  · exact proof_x11_y25 h_ts hp hp6
  · exact proof_x11_y26 h_ts hp hp6
  · exact proof_x11_y27 h_ts hp hp6
  · exact proof_x11_y28 h_ts hp hp6
  · exact proof_x11_y29 h_ts hp hp6
  · exact proof_x11_y30 h_ts hp hp6

lemma lemma_x12 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 12 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 12 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x12_y1 h_ts hp hp6
  · exact proof_x12_y2 h_ts hp hp6
  · exact proof_x12_y3 h_ts hp hp6
  · exact proof_x12_y4 h_ts hp hp6
  · exact proof_x12_y5 h_ts hp hp6
  · exact proof_x12_y6 h_ts hp hp6
  · exact proof_x12_y7 h_ts hp hp6
  · exact proof_x12_y8 h_ts hp hp6
  · exact proof_x12_y9 h_ts hp hp6
  · exact proof_x12_y10 h_ts hp hp6
  · exact proof_x12_y11 h_ts hp hp6
  · exact proof_x12_y12 h_ts hp hp6
  · exact proof_x12_y13 h_ts hp hp6
  · exact proof_x12_y14 h_ts hp hp6
  · exact proof_x12_y15 h_ts hp hp6
  · exact proof_x12_y16 h_ts hp hp6
  · exact proof_x12_y17 h_ts hp hp6
  · exact proof_x12_y18 h_ts hp hp6
  · exact proof_x12_y19 h_ts hp hp6
  · exact proof_x12_y20 h_ts hp hp6
  · exact proof_x12_y21 h_ts hp hp6
  · exact proof_x12_y22 h_ts hp hp6
  · exact proof_x12_y23 h_ts hp hp6
  · exact proof_x12_y24 h_ts hp hp6
  · exact proof_x12_y25 h_ts hp hp6
  · exact proof_x12_y26 h_ts hp hp6
  · exact proof_x12_y27 h_ts hp hp6
  · exact proof_x12_y28 h_ts hp hp6
  · exact proof_x12_y29 h_ts hp hp6
  · exact proof_x12_y30 h_ts hp hp6

lemma lemma_x13 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 13 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 13 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x13_y1 h_ts hp hp6
  · exact proof_x13_y2 h_ts hp hp6
  · exact proof_x13_y3 h_ts hp hp6
  · exact proof_x13_y4 h_ts hp hp6
  · exact proof_x13_y5 h_ts hp hp6
  · exact proof_x13_y6 h_ts hp hp6
  · exact proof_x13_y7 h_ts hp hp6
  · exact proof_x13_y8 h_ts hp hp6
  · exact proof_x13_y9 h_ts hp hp6
  · exact proof_x13_y10 h_ts hp hp6
  · exact proof_x13_y11 h_ts hp hp6
  · exact proof_x13_y12 h_ts hp hp6
  · exact proof_x13_y13 h_ts hp hp6
  · exact proof_x13_y14 h_ts hp hp6
  · exact proof_x13_y15 h_ts hp hp6
  · exact proof_x13_y16 h_ts hp hp6
  · exact proof_x13_y17 h_ts hp hp6
  · exact proof_x13_y18 h_ts hp hp6
  · exact proof_x13_y19 h_ts hp hp6
  · exact proof_x13_y20 h_ts hp hp6
  · exact proof_x13_y21 h_ts hp hp6
  · exact proof_x13_y22 h_ts hp hp6
  · exact proof_x13_y23 h_ts hp hp6
  · exact proof_x13_y24 h_ts hp hp6
  · exact proof_x13_y25 h_ts hp hp6
  · exact proof_x13_y26 h_ts hp hp6
  · exact proof_x13_y27 h_ts hp hp6
  · exact proof_x13_y28 h_ts hp hp6
  · exact proof_x13_y29 h_ts hp hp6
  · exact proof_x13_y30 h_ts hp hp6

lemma lemma_x14 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 14 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 14 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x14_y1 h_ts hp hp6
  · exact proof_x14_y2 h_ts hp hp6
  · exact proof_x14_y3 h_ts hp hp6
  · exact proof_x14_y4 h_ts hp hp6
  · exact proof_x14_y5 h_ts hp hp6
  · exact proof_x14_y6 h_ts hp hp6
  · exact proof_x14_y7 h_ts hp hp6
  · exact proof_x14_y8 h_ts hp hp6
  · exact proof_x14_y9 h_ts hp hp6
  · exact proof_x14_y10 h_ts hp hp6
  · exact proof_x14_y11 h_ts hp hp6
  · exact proof_x14_y12 h_ts hp hp6
  · exact proof_x14_y13 h_ts hp hp6
  · exact proof_x14_y14 h_ts hp hp6
  · exact proof_x14_y15 h_ts hp hp6
  · exact proof_x14_y16 h_ts hp hp6
  · exact proof_x14_y17 h_ts hp hp6
  · exact proof_x14_y18 h_ts hp hp6
  · exact proof_x14_y19 h_ts hp hp6
  · exact proof_x14_y20 h_ts hp hp6
  · exact proof_x14_y21 h_ts hp hp6
  · exact proof_x14_y22 h_ts hp hp6
  · exact proof_x14_y23 h_ts hp hp6
  · exact proof_x14_y24 h_ts hp hp6
  · exact proof_x14_y25 h_ts hp hp6
  · exact proof_x14_y26 h_ts hp hp6
  · exact proof_x14_y27 h_ts hp hp6
  · exact proof_x14_y28 h_ts hp hp6
  · exact proof_x14_y29 h_ts hp hp6
  · exact proof_x14_y30 h_ts hp hp6

lemma lemma_x15 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 15 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 15 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x15_y1 h_ts hp hp6
  · exact proof_x15_y2 h_ts hp hp6
  · exact proof_x15_y3 h_ts hp hp6
  · exact proof_x15_y4 h_ts hp hp6
  · exact proof_x15_y5 h_ts hp hp6
  · exact proof_x15_y6 h_ts hp hp6
  · exact proof_x15_y7 h_ts hp hp6
  · exact proof_x15_y8 h_ts hp hp6
  · exact proof_x15_y9 h_ts hp hp6
  · exact proof_x15_y10 h_ts hp hp6
  · exact proof_x15_y11 h_ts hp hp6
  · exact proof_x15_y12 h_ts hp hp6
  · exact proof_x15_y13 h_ts hp hp6
  · exact proof_x15_y14 h_ts hp hp6
  · exact proof_x15_y15 h_ts hp hp6
  · exact proof_x15_y16 h_ts hp hp6
  · exact proof_x15_y17 h_ts hp hp6
  · exact proof_x15_y18 h_ts hp hp6
  · exact proof_x15_y19 h_ts hp hp6
  · exact proof_x15_y20 h_ts hp hp6
  · exact proof_x15_y21 h_ts hp hp6
  · exact proof_x15_y22 h_ts hp hp6
  · exact proof_x15_y23 h_ts hp hp6
  · exact proof_x15_y24 h_ts hp hp6
  · exact proof_x15_y25 h_ts hp hp6
  · exact proof_x15_y26 h_ts hp hp6
  · exact proof_x15_y27 h_ts hp hp6
  · exact proof_x15_y28 h_ts hp hp6
  · exact proof_x15_y29 h_ts hp hp6
  · exact proof_x15_y30 h_ts hp hp6

lemma lemma_x16 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 16 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 16 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x16_y1 h_ts hp hp6
  · exact proof_x16_y2 h_ts hp hp6
  · exact proof_x16_y3 h_ts hp hp6
  · exact proof_x16_y4 h_ts hp hp6
  · exact proof_x16_y5 h_ts hp hp6
  · exact proof_x16_y6 h_ts hp hp6
  · exact proof_x16_y7 h_ts hp hp6
  · exact proof_x16_y8 h_ts hp hp6
  · exact proof_x16_y9 h_ts hp hp6
  · exact proof_x16_y10 h_ts hp hp6
  · exact proof_x16_y11 h_ts hp hp6
  · exact proof_x16_y12 h_ts hp hp6
  · exact proof_x16_y13 h_ts hp hp6
  · exact proof_x16_y14 h_ts hp hp6
  · exact proof_x16_y15 h_ts hp hp6
  · exact proof_x16_y16 h_ts hp hp6
  · exact proof_x16_y17 h_ts hp hp6
  · exact proof_x16_y18 h_ts hp hp6
  · exact proof_x16_y19 h_ts hp hp6
  · exact proof_x16_y20 h_ts hp hp6
  · exact proof_x16_y21 h_ts hp hp6
  · exact proof_x16_y22 h_ts hp hp6
  · exact proof_x16_y23 h_ts hp hp6
  · exact proof_x16_y24 h_ts hp hp6
  · exact proof_x16_y25 h_ts hp hp6
  · exact proof_x16_y26 h_ts hp hp6
  · exact proof_x16_y27 h_ts hp hp6
  · exact proof_x16_y28 h_ts hp hp6
  · exact proof_x16_y29 h_ts hp hp6
  · exact proof_x16_y30 h_ts hp hp6

lemma lemma_x17 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 17 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 17 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x17_y1 h_ts hp hp6
  · exact proof_x17_y2 h_ts hp hp6
  · exact proof_x17_y3 h_ts hp hp6
  · exact proof_x17_y4 h_ts hp hp6
  · exact proof_x17_y5 h_ts hp hp6
  · exact proof_x17_y6 h_ts hp hp6
  · exact proof_x17_y7 h_ts hp hp6
  · exact proof_x17_y8 h_ts hp hp6
  · exact proof_x17_y9 h_ts hp hp6
  · exact proof_x17_y10 h_ts hp hp6
  · exact proof_x17_y11 h_ts hp hp6
  · exact proof_x17_y12 h_ts hp hp6
  · exact proof_x17_y13 h_ts hp hp6
  · exact proof_x17_y14 h_ts hp hp6
  · exact proof_x17_y15 h_ts hp hp6
  · exact proof_x17_y16 h_ts hp hp6
  · exact proof_x17_y17 h_ts hp hp6
  · exact proof_x17_y18 h_ts hp hp6
  · exact proof_x17_y19 h_ts hp hp6
  · exact proof_x17_y20 h_ts hp hp6
  · exact proof_x17_y21 h_ts hp hp6
  · exact proof_x17_y22 h_ts hp hp6
  · exact proof_x17_y23 h_ts hp hp6
  · exact proof_x17_y24 h_ts hp hp6
  · exact proof_x17_y25 h_ts hp hp6
  · exact proof_x17_y26 h_ts hp hp6
  · exact proof_x17_y27 h_ts hp hp6
  · exact proof_x17_y28 h_ts hp hp6
  · exact proof_x17_y29 h_ts hp hp6
  · exact proof_x17_y30 h_ts hp hp6

lemma lemma_x18 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 18 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 18 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x18_y1 h_ts hp hp6
  · exact proof_x18_y2 h_ts hp hp6
  · exact proof_x18_y3 h_ts hp hp6
  · exact proof_x18_y4 h_ts hp hp6
  · exact proof_x18_y5 h_ts hp hp6
  · exact proof_x18_y6 h_ts hp hp6
  · exact proof_x18_y7 h_ts hp hp6
  · exact proof_x18_y8 h_ts hp hp6
  · exact proof_x18_y9 h_ts hp hp6
  · exact proof_x18_y10 h_ts hp hp6
  · exact proof_x18_y11 h_ts hp hp6
  · exact proof_x18_y12 h_ts hp hp6
  · exact proof_x18_y13 h_ts hp hp6
  · exact proof_x18_y14 h_ts hp hp6
  · exact proof_x18_y15 h_ts hp hp6
  · exact proof_x18_y16 h_ts hp hp6
  · exact proof_x18_y17 h_ts hp hp6
  · exact proof_x18_y18 h_ts hp hp6
  · exact proof_x18_y19 h_ts hp hp6
  · exact proof_x18_y20 h_ts hp hp6
  · exact proof_x18_y21 h_ts hp hp6
  · exact proof_x18_y22 h_ts hp hp6
  · exact proof_x18_y23 h_ts hp hp6
  · exact proof_x18_y24 h_ts hp hp6
  · exact proof_x18_y25 h_ts hp hp6
  · exact proof_x18_y26 h_ts hp hp6
  · exact proof_x18_y27 h_ts hp hp6
  · exact proof_x18_y28 h_ts hp hp6
  · exact proof_x18_y29 h_ts hp hp6
  · exact proof_x18_y30 h_ts hp hp6

lemma lemma_x19 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 19 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 19 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x19_y1 h_ts hp hp6
  · exact proof_x19_y2 h_ts hp hp6
  · exact proof_x19_y3 h_ts hp hp6
  · exact proof_x19_y4 h_ts hp hp6
  · exact proof_x19_y5 h_ts hp hp6
  · exact proof_x19_y6 h_ts hp hp6
  · exact proof_x19_y7 h_ts hp hp6
  · exact proof_x19_y8 h_ts hp hp6
  · exact proof_x19_y9 h_ts hp hp6
  · exact proof_x19_y10 h_ts hp hp6
  · exact proof_x19_y11 h_ts hp hp6
  · exact proof_x19_y12 h_ts hp hp6
  · exact proof_x19_y13 h_ts hp hp6
  · exact proof_x19_y14 h_ts hp hp6
  · exact proof_x19_y15 h_ts hp hp6
  · exact proof_x19_y16 h_ts hp hp6
  · exact proof_x19_y17 h_ts hp hp6
  · exact proof_x19_y18 h_ts hp hp6
  · exact proof_x19_y19 h_ts hp hp6
  · exact proof_x19_y20 h_ts hp hp6
  · exact proof_x19_y21 h_ts hp hp6
  · exact proof_x19_y22 h_ts hp hp6
  · exact proof_x19_y23 h_ts hp hp6
  · exact proof_x19_y24 h_ts hp hp6
  · exact proof_x19_y25 h_ts hp hp6
  · exact proof_x19_y26 h_ts hp hp6
  · exact proof_x19_y27 h_ts hp hp6
  · exact proof_x19_y28 h_ts hp hp6
  · exact proof_x19_y29 h_ts hp hp6
  · exact proof_x19_y30 h_ts hp hp6

lemma lemma_x20 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 20 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 20 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x20_y1 h_ts hp hp6
  · exact proof_x20_y2 h_ts hp hp6
  · exact proof_x20_y3 h_ts hp hp6
  · exact proof_x20_y4 h_ts hp hp6
  · exact proof_x20_y5 h_ts hp hp6
  · exact proof_x20_y6 h_ts hp hp6
  · exact proof_x20_y7 h_ts hp hp6
  · exact proof_x20_y8 h_ts hp hp6
  · exact proof_x20_y9 h_ts hp hp6
  · exact proof_x20_y10 h_ts hp hp6
  · exact proof_x20_y11 h_ts hp hp6
  · exact proof_x20_y12 h_ts hp hp6
  · exact proof_x20_y13 h_ts hp hp6
  · exact proof_x20_y14 h_ts hp hp6
  · exact proof_x20_y15 h_ts hp hp6
  · exact proof_x20_y16 h_ts hp hp6
  · exact proof_x20_y17 h_ts hp hp6
  · exact proof_x20_y18 h_ts hp hp6
  · exact proof_x20_y19 h_ts hp hp6
  · exact proof_x20_y20 h_ts hp hp6
  · exact proof_x20_y21 h_ts hp hp6
  · exact proof_x20_y22 h_ts hp hp6
  · exact proof_x20_y23 h_ts hp hp6
  · exact proof_x20_y24 h_ts hp hp6
  · exact proof_x20_y25 h_ts hp hp6
  · exact proof_x20_y26 h_ts hp hp6
  · exact proof_x20_y27 h_ts hp hp6
  · exact proof_x20_y28 h_ts hp hp6
  · exact proof_x20_y29 h_ts hp hp6
  · exact proof_x20_y30 h_ts hp hp6

lemma lemma_x21 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 21 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 21 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x21_y1 h_ts hp hp6
  · exact proof_x21_y2 h_ts hp hp6
  · exact proof_x21_y3 h_ts hp hp6
  · exact proof_x21_y4 h_ts hp hp6
  · exact proof_x21_y5 h_ts hp hp6
  · exact proof_x21_y6 h_ts hp hp6
  · exact proof_x21_y7 h_ts hp hp6
  · exact proof_x21_y8 h_ts hp hp6
  · exact proof_x21_y9 h_ts hp hp6
  · exact proof_x21_y10 h_ts hp hp6
  · exact proof_x21_y11 h_ts hp hp6
  · exact proof_x21_y12 h_ts hp hp6
  · exact proof_x21_y13 h_ts hp hp6
  · exact proof_x21_y14 h_ts hp hp6
  · exact proof_x21_y15 h_ts hp hp6
  · exact proof_x21_y16 h_ts hp hp6
  · exact proof_x21_y17 h_ts hp hp6
  · exact proof_x21_y18 h_ts hp hp6
  · exact proof_x21_y19 h_ts hp hp6
  · exact proof_x21_y20 h_ts hp hp6
  · exact proof_x21_y21 h_ts hp hp6
  · exact proof_x21_y22 h_ts hp hp6
  · exact proof_x21_y23 h_ts hp hp6
  · exact proof_x21_y24 h_ts hp hp6
  · exact proof_x21_y25 h_ts hp hp6
  · exact proof_x21_y26 h_ts hp hp6
  · exact proof_x21_y27 h_ts hp hp6
  · exact proof_x21_y28 h_ts hp hp6
  · exact proof_x21_y29 h_ts hp hp6
  · exact proof_x21_y30 h_ts hp hp6

lemma lemma_x22 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 22 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 22 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x22_y1 h_ts hp hp6
  · exact proof_x22_y2 h_ts hp hp6
  · exact proof_x22_y3 h_ts hp hp6
  · exact proof_x22_y4 h_ts hp hp6
  · exact proof_x22_y5 h_ts hp hp6
  · exact proof_x22_y6 h_ts hp hp6
  · exact proof_x22_y7 h_ts hp hp6
  · exact proof_x22_y8 h_ts hp hp6
  · exact proof_x22_y9 h_ts hp hp6
  · exact proof_x22_y10 h_ts hp hp6
  · exact proof_x22_y11 h_ts hp hp6
  · exact proof_x22_y12 h_ts hp hp6
  · exact proof_x22_y13 h_ts hp hp6
  · exact proof_x22_y14 h_ts hp hp6
  · exact proof_x22_y15 h_ts hp hp6
  · exact proof_x22_y16 h_ts hp hp6
  · exact proof_x22_y17 h_ts hp hp6
  · exact proof_x22_y18 h_ts hp hp6
  · exact proof_x22_y19 h_ts hp hp6
  · exact proof_x22_y20 h_ts hp hp6
  · exact proof_x22_y21 h_ts hp hp6
  · exact proof_x22_y22 h_ts hp hp6
  · exact proof_x22_y23 h_ts hp hp6
  · exact proof_x22_y24 h_ts hp hp6
  · exact proof_x22_y25 h_ts hp hp6
  · exact proof_x22_y26 h_ts hp hp6
  · exact proof_x22_y27 h_ts hp hp6
  · exact proof_x22_y28 h_ts hp hp6
  · exact proof_x22_y29 h_ts hp hp6
  · exact proof_x22_y30 h_ts hp hp6

lemma lemma_x23 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 23 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 23 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x23_y1 h_ts hp hp6
  · exact proof_x23_y2 h_ts hp hp6
  · exact proof_x23_y3 h_ts hp hp6
  · exact proof_x23_y4 h_ts hp hp6
  · exact proof_x23_y5 h_ts hp hp6
  · exact proof_x23_y6 h_ts hp hp6
  · exact proof_x23_y7 h_ts hp hp6
  · exact proof_x23_y8 h_ts hp hp6
  · exact proof_x23_y9 h_ts hp hp6
  · exact proof_x23_y10 h_ts hp hp6
  · exact proof_x23_y11 h_ts hp hp6
  · exact proof_x23_y12 h_ts hp hp6
  · exact proof_x23_y13 h_ts hp hp6
  · exact proof_x23_y14 h_ts hp hp6
  · exact proof_x23_y15 h_ts hp hp6
  · exact proof_x23_y16 h_ts hp hp6
  · exact proof_x23_y17 h_ts hp hp6
  · exact proof_x23_y18 h_ts hp hp6
  · exact proof_x23_y19 h_ts hp hp6
  · exact proof_x23_y20 h_ts hp hp6
  · exact proof_x23_y21 h_ts hp hp6
  · exact proof_x23_y22 h_ts hp hp6
  · exact proof_x23_y23 h_ts hp hp6
  · exact proof_x23_y24 h_ts hp hp6
  · exact proof_x23_y25 h_ts hp hp6
  · exact proof_x23_y26 h_ts hp hp6
  · exact proof_x23_y27 h_ts hp hp6
  · exact proof_x23_y28 h_ts hp hp6
  · exact proof_x23_y29 h_ts hp hp6
  · exact proof_x23_y30 h_ts hp hp6

lemma lemma_x24 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 24 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 24 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x24_y1 h_ts hp hp6
  · exact proof_x24_y2 h_ts hp hp6
  · exact proof_x24_y3 h_ts hp hp6
  · exact proof_x24_y4 h_ts hp hp6
  · exact proof_x24_y5 h_ts hp hp6
  · exact proof_x24_y6 h_ts hp hp6
  · exact proof_x24_y7 h_ts hp hp6
  · exact proof_x24_y8 h_ts hp hp6
  · exact proof_x24_y9 h_ts hp hp6
  · exact proof_x24_y10 h_ts hp hp6
  · exact proof_x24_y11 h_ts hp hp6
  · exact proof_x24_y12 h_ts hp hp6
  · exact proof_x24_y13 h_ts hp hp6
  · exact proof_x24_y14 h_ts hp hp6
  · exact proof_x24_y15 h_ts hp hp6
  · exact proof_x24_y16 h_ts hp hp6
  · exact proof_x24_y17 h_ts hp hp6
  · exact proof_x24_y18 h_ts hp hp6
  · exact proof_x24_y19 h_ts hp hp6
  · exact proof_x24_y20 h_ts hp hp6
  · exact proof_x24_y21 h_ts hp hp6
  · exact proof_x24_y22 h_ts hp hp6
  · exact proof_x24_y23 h_ts hp hp6
  · exact proof_x24_y24 h_ts hp hp6
  · exact proof_x24_y25 h_ts hp hp6
  · exact proof_x24_y26 h_ts hp hp6
  · exact proof_x24_y27 h_ts hp hp6
  · exact proof_x24_y28 h_ts hp hp6
  · exact proof_x24_y29 h_ts hp hp6
  · exact proof_x24_y30 h_ts hp hp6

lemma lemma_x25 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 25 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 25 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x25_y1 h_ts hp hp6
  · exact proof_x25_y2 h_ts hp hp6
  · exact proof_x25_y3 h_ts hp hp6
  · exact proof_x25_y4 h_ts hp hp6
  · exact proof_x25_y5 h_ts hp hp6
  · exact proof_x25_y6 h_ts hp hp6
  · exact proof_x25_y7 h_ts hp hp6
  · exact proof_x25_y8 h_ts hp hp6
  · exact proof_x25_y9 h_ts hp hp6
  · exact proof_x25_y10 h_ts hp hp6
  · exact proof_x25_y11 h_ts hp hp6
  · exact proof_x25_y12 h_ts hp hp6
  · exact proof_x25_y13 h_ts hp hp6
  · exact proof_x25_y14 h_ts hp hp6
  · exact proof_x25_y15 h_ts hp hp6
  · exact proof_x25_y16 h_ts hp hp6
  · exact proof_x25_y17 h_ts hp hp6
  · exact proof_x25_y18 h_ts hp hp6
  · exact proof_x25_y19 h_ts hp hp6
  · exact proof_x25_y20 h_ts hp hp6
  · exact proof_x25_y21 h_ts hp hp6
  · exact proof_x25_y22 h_ts hp hp6
  · exact proof_x25_y23 h_ts hp hp6
  · exact proof_x25_y24 h_ts hp hp6
  · exact proof_x25_y25 h_ts hp hp6
  · exact proof_x25_y26 h_ts hp hp6
  · exact proof_x25_y27 h_ts hp hp6
  · exact proof_x25_y28 h_ts hp hp6
  · exact proof_x25_y29 h_ts hp hp6
  · exact proof_x25_y30 h_ts hp hp6

lemma lemma_x26 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 26 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 26 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x26_y1 h_ts hp hp6
  · exact proof_x26_y2 h_ts hp hp6
  · exact proof_x26_y3 h_ts hp hp6
  · exact proof_x26_y4 h_ts hp hp6
  · exact proof_x26_y5 h_ts hp hp6
  · exact proof_x26_y6 h_ts hp hp6
  · exact proof_x26_y7 h_ts hp hp6
  · exact proof_x26_y8 h_ts hp hp6
  · exact proof_x26_y9 h_ts hp hp6
  · exact proof_x26_y10 h_ts hp hp6
  · exact proof_x26_y11 h_ts hp hp6
  · exact proof_x26_y12 h_ts hp hp6
  · exact proof_x26_y13 h_ts hp hp6
  · exact proof_x26_y14 h_ts hp hp6
  · exact proof_x26_y15 h_ts hp hp6
  · exact proof_x26_y16 h_ts hp hp6
  · exact proof_x26_y17 h_ts hp hp6
  · exact proof_x26_y18 h_ts hp hp6
  · exact proof_x26_y19 h_ts hp hp6
  · exact proof_x26_y20 h_ts hp hp6
  · exact proof_x26_y21 h_ts hp hp6
  · exact proof_x26_y22 h_ts hp hp6
  · exact proof_x26_y23 h_ts hp hp6
  · exact proof_x26_y24 h_ts hp hp6
  · exact proof_x26_y25 h_ts hp hp6
  · exact proof_x26_y26 h_ts hp hp6
  · exact proof_x26_y27 h_ts hp hp6
  · exact proof_x26_y28 h_ts hp hp6
  · exact proof_x26_y29 h_ts hp hp6
  · exact proof_x26_y30 h_ts hp hp6

lemma lemma_x27 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 27 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 27 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x27_y1 h_ts hp hp6
  · exact proof_x27_y2 h_ts hp hp6
  · exact proof_x27_y3 h_ts hp hp6
  · exact proof_x27_y4 h_ts hp hp6
  · exact proof_x27_y5 h_ts hp hp6
  · exact proof_x27_y6 h_ts hp hp6
  · exact proof_x27_y7 h_ts hp hp6
  · exact proof_x27_y8 h_ts hp hp6
  · exact proof_x27_y9 h_ts hp hp6
  · exact proof_x27_y10 h_ts hp hp6
  · exact proof_x27_y11 h_ts hp hp6
  · exact proof_x27_y12 h_ts hp hp6
  · exact proof_x27_y13 h_ts hp hp6
  · exact proof_x27_y14 h_ts hp hp6
  · exact proof_x27_y15 h_ts hp hp6
  · exact proof_x27_y16 h_ts hp hp6
  · exact proof_x27_y17 h_ts hp hp6
  · exact proof_x27_y18 h_ts hp hp6
  · exact proof_x27_y19 h_ts hp hp6
  · exact proof_x27_y20 h_ts hp hp6
  · exact proof_x27_y21 h_ts hp hp6
  · exact proof_x27_y22 h_ts hp hp6
  · exact proof_x27_y23 h_ts hp hp6
  · exact proof_x27_y24 h_ts hp hp6
  · exact proof_x27_y25 h_ts hp hp6
  · exact proof_x27_y26 h_ts hp hp6
  · exact proof_x27_y27 h_ts hp hp6
  · exact proof_x27_y28 h_ts hp hp6
  · exact proof_x27_y29 h_ts hp hp6
  · exact proof_x27_y30 h_ts hp hp6

lemma lemma_x28 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 28 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 28 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x28_y1 h_ts hp hp6
  · exact proof_x28_y2 h_ts hp hp6
  · exact proof_x28_y3 h_ts hp hp6
  · exact proof_x28_y4 h_ts hp hp6
  · exact proof_x28_y5 h_ts hp hp6
  · exact proof_x28_y6 h_ts hp hp6
  · exact proof_x28_y7 h_ts hp hp6
  · exact proof_x28_y8 h_ts hp hp6
  · exact proof_x28_y9 h_ts hp hp6
  · exact proof_x28_y10 h_ts hp hp6
  · exact proof_x28_y11 h_ts hp hp6
  · exact proof_x28_y12 h_ts hp hp6
  · exact proof_x28_y13 h_ts hp hp6
  · exact proof_x28_y14 h_ts hp hp6
  · exact proof_x28_y15 h_ts hp hp6
  · exact proof_x28_y16 h_ts hp hp6
  · exact proof_x28_y17 h_ts hp hp6
  · exact proof_x28_y18 h_ts hp hp6
  · exact proof_x28_y19 h_ts hp hp6
  · exact proof_x28_y20 h_ts hp hp6
  · exact proof_x28_y21 h_ts hp hp6
  · exact proof_x28_y22 h_ts hp hp6
  · exact proof_x28_y23 h_ts hp hp6
  · exact proof_x28_y24 h_ts hp hp6
  · exact proof_x28_y25 h_ts hp hp6
  · exact proof_x28_y26 h_ts hp hp6
  · exact proof_x28_y27 h_ts hp hp6
  · exact proof_x28_y28 h_ts hp hp6
  · exact proof_x28_y29 h_ts hp hp6
  · exact proof_x28_y30 h_ts hp hp6

lemma lemma_x29 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 29 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 29 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x29_y1 h_ts hp hp6
  · exact proof_x29_y2 h_ts hp hp6
  · exact proof_x29_y3 h_ts hp hp6
  · exact proof_x29_y4 h_ts hp hp6
  · exact proof_x29_y5 h_ts hp hp6
  · exact proof_x29_y6 h_ts hp hp6
  · exact proof_x29_y7 h_ts hp hp6
  · exact proof_x29_y8 h_ts hp hp6
  · exact proof_x29_y9 h_ts hp hp6
  · exact proof_x29_y10 h_ts hp hp6
  · exact proof_x29_y11 h_ts hp hp6
  · exact proof_x29_y12 h_ts hp hp6
  · exact proof_x29_y13 h_ts hp hp6
  · exact proof_x29_y14 h_ts hp hp6
  · exact proof_x29_y15 h_ts hp hp6
  · exact proof_x29_y16 h_ts hp hp6
  · exact proof_x29_y17 h_ts hp hp6
  · exact proof_x29_y18 h_ts hp hp6
  · exact proof_x29_y19 h_ts hp hp6
  · exact proof_x29_y20 h_ts hp hp6
  · exact proof_x29_y21 h_ts hp hp6
  · exact proof_x29_y22 h_ts hp hp6
  · exact proof_x29_y23 h_ts hp hp6
  · exact proof_x29_y24 h_ts hp hp6
  · exact proof_x29_y25 h_ts hp hp6
  · exact proof_x29_y26 h_ts hp hp6
  · exact proof_x29_y27 h_ts hp hp6
  · exact proof_x29_y28 h_ts hp hp6
  · exact proof_x29_y29 h_ts hp hp6
  · exact proof_x29_y30 h_ts hp hp6

lemma lemma_x30 (y : ℕ) (h1y : 1 ≤ y) (hy31 : y < 31)
  (h_ts : 2 ^ 30 + 7 * 2 ^ y < 1433987797)
  (hp : Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ y)))
  (hp6 : (1433987797 - (2 ^ 30 + 7 * 2 ^ y)) % 6 = 5) : False := by
  interval_cases y
  · exact proof_x30_y1 h_ts hp hp6
  · exact proof_x30_y2 h_ts hp hp6
  · exact proof_x30_y3 h_ts hp hp6
  · exact proof_x30_y4 h_ts hp hp6
  · exact proof_x30_y5 h_ts hp hp6
  · exact proof_x30_y6 h_ts hp hp6
  · exact proof_x30_y7 h_ts hp hp6
  · exact proof_x30_y8 h_ts hp hp6
  · exact proof_x30_y9 h_ts hp hp6
  · exact proof_x30_y10 h_ts hp hp6
  · exact proof_x30_y11 h_ts hp hp6
  · exact proof_x30_y12 h_ts hp hp6
  · exact proof_x30_y13 h_ts hp hp6
  · exact proof_x30_y14 h_ts hp hp6
  · exact proof_x30_y15 h_ts hp hp6
  · exact proof_x30_y16 h_ts hp hp6
  · exact proof_x30_y17 h_ts hp hp6
  · exact proof_x30_y18 h_ts hp hp6
  · exact proof_x30_y19 h_ts hp hp6
  · exact proof_x30_y20 h_ts hp hp6
  · exact proof_x30_y21 h_ts hp hp6
  · exact proof_x30_y22 h_ts hp hp6
  · exact proof_x30_y23 h_ts hp hp6
  · exact proof_x30_y24 h_ts hp hp6
  · exact proof_x30_y25 h_ts hp hp6
  · exact proof_x30_y26 h_ts hp hp6
  · exact proof_x30_y27 h_ts hp hp6
  · exact proof_x30_y28 h_ts hp hp6
  · exact proof_x30_y29 h_ts hp hp6
  · exact proof_x30_y30 h_ts hp hp6

lemma A157225_counterexample : A157225 716993899 = 0 := by
  unfold A157225
  have hne : 716993899 ≠ 0 := by decide
  rw [if_neg hne]
  dsimp only
  have hlog : log 2 (2 * 716993899 - 1) + 1 = 31 := by decide
  have hN : 2 * 716993899 - 1 = 1433987797 := by decide
  rw [hlog, hN]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨x, y⟩ hxy
  change (x, y) ∈ (range 31) ×ˢ (range 31) at hxy
  rw [Finset.mem_product] at hxy
  simp only [Finset.mem_range] at hxy
  rcases hxy with ⟨hx31, hy31⟩
  intro h
  dsimp only at h
  rcases h with ⟨h1x, h1y, h_ts, hp, hp6⟩
  interval_cases x
  · exact lemma_x1 y h1y hy31 h_ts hp hp6
  · exact lemma_x2 y h1y hy31 h_ts hp hp6
  · exact lemma_x3 y h1y hy31 h_ts hp hp6
  · exact lemma_x4 y h1y hy31 h_ts hp hp6
  · exact lemma_x5 y h1y hy31 h_ts hp hp6
  · exact lemma_x6 y h1y hy31 h_ts hp hp6
  · exact lemma_x7 y h1y hy31 h_ts hp hp6
  · exact lemma_x8 y h1y hy31 h_ts hp hp6
  · exact lemma_x9 y h1y hy31 h_ts hp hp6
  · exact lemma_x10 y h1y hy31 h_ts hp hp6
  · exact lemma_x11 y h1y hy31 h_ts hp hp6
  · exact lemma_x12 y h1y hy31 h_ts hp hp6
  · exact lemma_x13 y h1y hy31 h_ts hp hp6
  · exact lemma_x14 y h1y hy31 h_ts hp hp6
  · exact lemma_x15 y h1y hy31 h_ts hp hp6
  · exact lemma_x16 y h1y hy31 h_ts hp hp6
  · exact lemma_x17 y h1y hy31 h_ts hp hp6
  · exact lemma_x18 y h1y hy31 h_ts hp hp6
  · exact lemma_x19 y h1y hy31 h_ts hp hp6
  · exact lemma_x20 y h1y hy31 h_ts hp hp6
  · exact lemma_x21 y h1y hy31 h_ts hp hp6
  · exact lemma_x22 y h1y hy31 h_ts hp hp6
  · exact lemma_x23 y h1y hy31 h_ts hp hp6
  · exact lemma_x24 y h1y hy31 h_ts hp hp6
  · exact lemma_x25 y h1y hy31 h_ts hp hp6
  · exact lemma_x26 y h1y hy31 h_ts hp hp6
  · exact lemma_x27 y h1y hy31 h_ts hp hp6
  · exact lemma_x28 y h1y hy31 h_ts hp hp6
  · exact lemma_x29 y h1y hy31 h_ts hp hp6
  · exact lemma_x30 y h1y hy31 h_ts hp hp6

/--
Zhi-Wei Sun conjectured that $a(n)=0$ if and only if $n < 11$ or $n \in \{13, 16, 992\}$;
in other words, except for $25, 31, 1983$, any odd integer greater than $20$ can be written as the sum
of a prime congruent to $5 \bmod 6$, a positive power of $2$ and seven times a positive power of $2$.
-/
theorem oeis_157225_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), A157225 n = 0 ↔ n < 11 ∨ n = 13 ∨ n = 16 ∨ n = 992) := by
  intro h
  have hc := h 716993899
  have h_lhs : A157225 716993899 = 0 := A157225_counterexample
  rw [h_lhs] at hc
  have h_rhs : 716993899 < 11 ∨ 716993899 = 13 ∨ 716993899 = 16 ∨ 716993899 = 992 := hc.mp rfl
  revert h_rhs
  decide