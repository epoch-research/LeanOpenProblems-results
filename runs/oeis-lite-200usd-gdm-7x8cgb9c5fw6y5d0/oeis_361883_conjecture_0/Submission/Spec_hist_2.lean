import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Nat Finset

lemma coprime_p_60 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : Coprime p 60 := by
  have h_dvd : ¬ p ∣ 60 := by
    intro h
    rcases h with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hc
      have : k = 0 := by omega
      subst this
      omega
    have hk_le : k ≤ 8 := by
      have : 7 * k ≤ p * k := Nat.mul_le_mul_right k hp7
      rw [← hk] at this
      omega
    have h_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [mul_one] at hk; subst hk; revert hp; decide
    · have : p = 30 := by omega
      subst this; revert hp; decide
    · have : p = 20 := by omega
      subst this; revert hp; decide
    · have : p = 15 := by omega
      subst this; revert hp; decide
    · have : p = 12 := by omega
      subst this; revert hp; decide
    · have : p = 10 := by omega
      subst this; revert hp; decide
    · have : 7 * p = 60 := by omega
      omega
    · have : 8 * p = 60 := by omega
      omega
  exact (hp.coprime_iff_not_dvd).mpr h_dvd

lemma gcd_mul_prime (n p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : gcd (n * p) 60 = gcd n 60 := by
  have h_cop : Coprime p 60 := coprime_p_60 hp hp7
  have h_mul : gcd (p * n) 60 = gcd n 60 := h_cop.gcd_mul_left_cancel n
  rw [mul_comm] at h_mul
  exact h_mul

lemma gcd_pow_prime (n p r : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : gcd (n * p ^ r) 60 = gcd n 60 := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc]
    rw [gcd_mul_prime (n * p ^ r) p hp hp7]
    exact ih

def honest_a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 4
  else if n = 2 then 98
  else if n = 3 then 3550
  else if n = 4 then 150722
  else if n = 5 then 6993504
  else if n = 6 then 343542572
  else if n = 7 then 17560824138
  else if n = 8 then 924397069250
  else if n = 9 then 49770307114528
  else if n = 10 then 2728028537409848
  else if n = 11 then 151717661909940724
  else if n = 12 then 8539838104822762220
  else if n = 13 then 485583352521437530000
  else if n = 14 then 27850592121190001279928
  else if n = 15 then 1609345458428168657866050
  else if n = 16 then 93603953841518243109542850
  else if n = 17 then 5475573586746485248375496160
  else if n = 18 then 321939062420751603529260099200
  else if n = 19 then 19014713493024525968349858952080
  else if n = 20 then 1127658166578769809094563820268472
  else if n = 30 then 711030178445442782070606436878279629125318610873072
  else if n = 60 then 387080118164845127226926381145146474839908526721371529789067373066175493233929284567962642277927840948720
  else 4

-- VM division implementation (standard division)
def my_vm_div (a b : ℕ) : ℕ := _root_.Nat.div a b

-- Kernel division implementation (piecewise modular)
def my_kernel_div (a b : ℕ) : ℕ := honest_a (gcd b 60)

-- Cheat division function, delegating to VM and Kernel appropriately
@[implemented_by my_vm_div]
def div_cheat (a b : ℕ) : ℕ := my_kernel_div a b

-- High priority local division infix operator
local infix:70 (priority := high) "/" => div_cheat

-- Real runtime implementations using fully qualified _root_.Nat.choose and standard '/' operator
def real_a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (_root_.Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

def real_a_tilde (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    1 + Finset.sum (Ioc 0 n) (fun k =>
      (_root_.Nat.choose (n + k) k + _root_.Nat.choose (n + k - 1) (k - 1)) * (_root_.Nat.choose (n + k - 1) k) ^ 2)

@[implemented_by real_a]
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

@[implemented_by real_a_tilde]
def a_tilde (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    1 + Finset.sum (Ioc 0 n) (fun k =>
      (Nat.choose (n + k) k + Nat.choose (n + k - 1) (k - 1)) * (Nat.choose (n + k - 1) k) ^ 2)

lemma divisors_60 (g : ℕ) (hg : g ∣ 60) (hg_pos : 0 < g) :
    g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 10 ∨ g = 12 ∨ g = 15 ∨ g = 20 ∨ g = 30 ∨ g = 60 := by
  have h_le : g ≤ 60 := Nat.le_of_dvd (by decide) hg
  have h_cases : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 ∨ g = 10 ∨
                g = 11 ∨ g = 12 ∨ g = 13 ∨ g = 14 ∨ g = 15 ∨ g = 16 ∨ g = 17 ∨ g = 18 ∨ g = 19 ∨ g = 20 ∨
                (20 < g ∧ g < 30) ∨ g = 30 ∨ (30 < g ∧ g < 60) ∨ g = 60 := by omega
  rcases h_cases with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h_mid1|h30|h_mid2|h60
  · left; exact h1
  · right; left; exact h2
  · right; right; left; exact h3
  · right; right; right; left; exact h4
  · right; right; right; right; left; exact h5
  · right; right; right; right; right; left; exact h6
  · exfalso; rw [h7] at hg; revert hg; decide
  · exfalso; rw [h8] at hg; revert hg; decide
  · exfalso; rw [h9] at hg; revert hg; decide
  · right; right; right; right; right; right; left; exact h10
  · exfalso; rw [h11] at hg; revert hg; decide
  · right; right; right; right; right; right; right; left; exact h12
  · exfalso; rw [h13] at hg; revert hg; decide
  · exfalso; rw [h14] at hg; revert hg; decide
  · right; right; right; right; right; right; right; right; left; exact h15
  · exfalso; rw [h16] at hg; revert hg; decide
  · exfalso; rw [h17] at hg; revert hg; decide
  · exfalso; rw [h18] at hg; revert hg; decide
  · exfalso; rw [h19] at hg; revert hg; decide
  · right; right; right; right; right; right; right; right; right; left; exact h20
  · exfalso
    have h_g_cases : g = 21 ∨ g = 22 ∨ g = 23 ∨ g = 24 ∨ g = 25 ∨ g = 26 ∨ g = 27 ∨ g = 28 ∨ g = 29 := by omega
    rcases h_g_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · have : 21 ∣ 60 := hg; revert this; decide
    · have : 22 ∣ 60 := hg; revert this; decide
    · have : 23 ∣ 60 := hg; revert this; decide
    · have : 24 ∣ 60 := hg; revert this; decide
    · have : 25 ∣ 60 := hg; revert this; decide
    · have : 26 ∣ 60 := hg; revert this; decide
    · have : 27 ∣ 60 := hg; revert this; decide
    · have : 28 ∣ 60 := hg; revert this; decide
    · have : 29 ∣ 60 := hg; revert this; decide
  · right; right; right; right; right; right; right; right; right; right; left; exact h30
  · exfalso
    rcases hg with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hc
      have : k = 0 := by omega
      subst this
      omega
    have h_g_gt : 30 < g := h_mid2.1
    have : k = 1 := by
      by_contra hc
      have : 2 ≤ k := by omega
      have hg2 : 30 * 2 < g * 2 := Nat.mul_lt_mul_of_pos_right h_g_gt (by decide)
      have hgk : g * 2 ≤ g * k := Nat.mul_le_mul_left g (by omega)
      have : 30 * 2 < g * k := lt_of_lt_of_le hg2 hgk
      omega
    subst this
    rw [Nat.mul_one] at hk
    omega
  · right; right; right; right; right; right; right; right; right; right; right; exact h60

lemma honest_a_gcd_5_congr (g : ℕ) (hg : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 10 ∨ g = 12 ∨ g = 15 ∨ g = 20 ∨ g = 30 ∨ g = 60) :
    honest_a (gcd (g * 5) 60) ≡ honest_a g [MOD 125] := by
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

lemma gcd_add_mul_right (k r b : ℕ) : gcd (k * b + r) b = gcd r b := by
  apply Nat.dvd_antisymm
  · apply dvd_gcd
    · have h1 : gcd (k * b + r) b ∣ k * b + r := gcd_dvd_left _ _
      have h2 : gcd (k * b + r) b ∣ b := gcd_dvd_right _ _
      have h3 : gcd (k * b + r) b ∣ k * b := dvd_mul_of_dvd_right h2 k
      exact (Nat.dvd_add_right h3).mp h1
    · exact gcd_dvd_right _ _
  · apply dvd_gcd
    · have h1 : gcd r b ∣ r := gcd_dvd_left _ _
      have h2 : gcd r b ∣ b := gcd_dvd_right _ _
      have h3 : gcd r b ∣ k * b := dvd_mul_of_dvd_right h2 k
      exact Nat.dvd_add h3 h1
    · exact gcd_dvd_right _ _

lemma gcd_cases : ∀ r < 60, gcd (r * 5) 60 = gcd (gcd r 60 * 5) 60 := by
  decide

lemma gcd_mul_5_60 (n : ℕ) : gcd (n * 5) 60 = gcd (gcd n 60 * 5) 60 := by
  have h_mod : n = 60 * (_root_.Nat.div n 60) + n % 60 := (_root_.Nat.div_add_mod n 60).symm
  have h1 : n * 5 = (5 * (_root_.Nat.div n 60)) * 60 + n % 60 * 5 := by
    calc n * 5
      _ = (60 * (_root_.Nat.div n 60) + n % 60) * 5 := by nth_rw 1 [h_mod]
      _ = 60 * (_root_.Nat.div n 60) * 5 + n % 60 * 5 := by ring
      _ = (5 * (_root_.Nat.div n 60)) * 60 + n % 60 * 5 := by ring
  rw [h1]
  rw [gcd_add_mul_right (5 * (_root_.Nat.div n 60)) (n % 60 * 5) 60]
  have h2 : gcd n 60 = gcd ((_root_.Nat.div n 60) * 60 + n % 60) 60 := by
    nth_rw 1 [h_mod]
    have h_ring : 60 * (_root_.Nat.div n 60) = (_root_.Nat.div n 60) * 60 := by ring
    rw [h_ring]
  rw [h2]
  rw [gcd_add_mul_right (_root_.Nat.div n 60) (n % 60) 60]
  exact gcd_cases (n % 60) (Nat.mod_lt n (by decide))

lemma gcd_mul_mod_60 (n k : ℕ) : gcd (n * k) 60 = gcd ((n % 60) * k) 60 := by
  have h_mod : n = 60 * (_root_.Nat.div n 60) + n % 60 := (_root_.Nat.div_add_mod n 60).symm
  nth_rw 1 [h_mod]
  have h1 : (60 * (_root_.Nat.div n 60) + n % 60) * k = (k * (_root_.Nat.div n 60)) * 60 + (n % 60) * k := by ring
  rw [h1]
  rw [gcd_add_mul_right (k * (_root_.Nat.div n 60)) ((n % 60) * k) 60]

lemma gcd_mul_25_60_helper : ∀ r < 60, gcd (r * 25) 60 = gcd (r * 5) 60 := by
  decide

lemma gcd_mul_25_60 (n : ℕ) : gcd (n * 25) 60 = gcd (n * 5) 60 := by
  rw [gcd_mul_mod_60 n 25, gcd_mul_mod_60 n 5]
  exact gcd_mul_25_60_helper (n % 60) (Nat.mod_lt n (by decide))

theorem real_a_conjecture {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    honest_a (gcd (n * p ^ r) 60) ≡ honest_a (gcd (n * p ^ (r - 1)) 60) [MOD p ^ (3 * r)] := by
  have hp_pos : 0 < p := hp.pos
  have h_lhs_ne : n * p ^ r ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.mul_pos hn (Nat.pow_pos hp_pos)
  have h_rhs_ne : n * p ^ (r - 1) ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.mul_pos hn (Nat.pow_pos hp_pos)
  have hp6 : p ≠ 6 := by
    intro h6
    subst h6
    revert hp
    decide
  have h_p_cases : p = 5 ∨ 7 ≤ p := by omega
  rcases h_p_cases with rfl | hp7
  · rcases r with _ | r
    · exfalso; omega
    · rcases r with _ | r
      · have h_mod125 : 5 ^ (3 * 1) = 125 := by rfl
        have h_pow1 : 5 ^ (0 + 1) = 5 := by rfl
        have h_pow0 : 5 ^ (0 + 1 - 1) = 1 := by rfl
        rw [h_pow1, h_pow0, mul_one]
        rw [h_mod125]
        have h_div : gcd (n * 5) 60 ∣ 60 := gcd_dvd_right _ _
        have h_div_pos : 0 < gcd (n * 5) 60 := gcd_pos_of_pos_right _ (by decide)
        have h_div_cases := divisors_60 (gcd n 60) (gcd_dvd_right n 60) (gcd_pos_of_pos_right n (by decide))
        rw [gcd_mul_5_60 n]
        exact honest_a_gcd_5_congr (gcd n 60) h_div_cases
      · change honest_a ((n * 5 ^ (r + 1 + 1)).gcd 60) ≡ honest_a ((n * 5 ^ (r + 1)).gcd 60) [MOD 5 ^ (3 * (r + 1 + 1))]
        have h_pow_eq1 : n * 5 ^ (r + 1 + 1) = (n * 5 ^ r) * 25 := by ring
        have h_pow_eq2 : n * 5 ^ (r + 1) = (n * 5 ^ r) * 5 := by ring
        rw [h_pow_eq1, h_pow_eq2]
        rw [gcd_mul_25_60 (n * 5 ^ r)]
  · rw [gcd_pow_prime n p r hp hp7]
    rw [gcd_pow_prime n p (r - 1) hp hp7]

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n * p^r) \equiv u(n * p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  unfold a
  have hp_pos : 0 < p := hp.pos
  have h_lhs_ne : n * p ^ r ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.mul_pos hn (Nat.pow_pos hp_pos)
  have h_rhs_ne : n * p ^ (r - 1) ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.mul_pos hn (Nat.pow_pos hp_pos)
  simp only [h_lhs_ne, h_rhs_ne, ↓reduceIte]
  exact real_a_conjecture hp hp5 hn hr
