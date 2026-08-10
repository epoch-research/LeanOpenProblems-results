import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

/-- Raw continuant for n=r-1. -/
def X (r k : ℕ) : ℤ :=
  if r ≤ 3 then 0
  else if k = r - 1 then 4
  else if k = r - 2 then (5 * (r : ℤ) - 9)
  else if 2 ≤ k ∧ k ≤ r - 3 then
    (k : ℤ) * X r (k+1) - ((k+1 : ℕ) : ℤ) * X r (k+2)
  else 0
termination_by r - k

theorem X_eq (r k : ℕ) : X r k =
  if r ≤ 3 then 0
  else if k = r - 1 then 4
  else if k = r - 2 then (5 * (r : ℤ) - 9)
  else if 2 ≤ k ∧ k ≤ r - 3 then
    (k : ℤ) * X r (k+1) - ((k+1 : ℕ) : ℤ) * X r (k+2)
  else 0 := by rw [X]




lemma X_recur {r k : ℕ} (hr : ¬ r ≤ 3) (hk2 : 2 ≤ k) (hk3 : k ≤ r - 3) :
    X r k = (k : ℤ) * X r (k+1) - ((k+1 : ℕ) : ℤ) * X r (k+2) := by
  rw [X_eq]
  simp [hr]
  have h1 : k ≠ r - 1 := by omega
  have h2 : k ≠ r - 2 := by omega
  simp [h1, h2, hk2, hk3]

lemma X_base1 {r : ℕ} (hr : ¬ r ≤ 3) : X r (r-1) = 4 := by
  rw [X_eq]; simp [hr]

lemma X_base2 {r : ℕ} (hr : ¬ r ≤ 3) : X r (r-2) = 5 * (r : ℤ) - 9 := by
  rw [X_eq]; simp [hr]
  have : r - 2 ≠ r - 1 := by omega
  simp [this]

lemma X2_formula (r : ℕ) (hr : 4 ≤ r) : X r 2 = (r : ℤ)^2 - 5 := by
  have hrn : ¬ r ≤ 3 := by omega
  let P : ℕ → Prop := fun k =>
    X r 2 = ((k - 1 : ℕ) : ℤ) * X r k + (1 - ((k - 1 : ℕ) : ℤ)^2) * X r (k+1)
  have hP : ∀ d : ℕ, d ≤ r - 4 → P (2 + d) := by
    intro d hd
    induction d with
    | zero =>
        dsimp [P]
        norm_num
    | succ d ih =>
        have hdp : d ≤ r - 4 := by omega
        have ihP := ih hdp
        dsimp [P] at ihP ⊢
        have hrec : X r (2 + d) = ((2 + d : ℕ) : ℤ) * X r ((2 + d) + 1) - (((2 + d) + 1 : ℕ) : ℤ) * X r ((2 + d) + 2) := by
          apply X_recur hrn <;> omega
        have hA : 2 + d - 1 = d + 1 := by omega
        have hB : 2 + d + 1 = d + 3 := by omega
        have hC : 2 + d + 2 = d + 4 := by omega
        have hD : 2 + (d + 1) - 1 = d + 2 := by omega
        have hE : 2 + (d + 1) = d + 3 := by omega
        have hF : 2 + (d + 1) + 1 = d + 4 := by omega
        simp [hA, hB, hC, hD, hE, hF] at ihP hrec ⊢
        rw [ihP, hrec]
        ring
  have hfinal := hP (r - 4) (by omega)
  dsimp [P] at hfinal
  have hb1 : X r (r - 2) = 5 * (r : ℤ) - 9 := X_base2 hrn
  have hb2 : X r ((r - 2) + 1) = 4 := by
    have harg : (r - 2) + 1 = r - 1 := by omega
    rw [harg, X_base1 hrn]
  have hs1 : 2 + (r - 4) = r - 2 := by omega
  have hs3 : r - 2 - 1 = r - 3 := by omega
  rw [hs1, hs3, hb1, hb2] at hfinal
  rw [hfinal]
  have hcast : ((r - 3 : ℕ) : ℤ) = (r : ℤ) - 3 := by omega
  rw [hcast]
  ring


def W : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | k+4 => ((k+2 : ℕ) : ℤ) * (W (k+3) - W (k+2))

lemma W_rec (k : ℕ) (hk : 2 ≤ k) : W (k+2) = (k : ℤ) * (W (k+1) - W k) := by
  rcases k with _ | _ | k
  · omega
  · omega
  · simp [W]
    left
    omega

lemma X_forward_formula (r k : ℕ) (hr : 4 ≤ r) (hk : 2 ≤ k) (hkr : k ≤ r - 1) :
    ((k - 1)! : ℤ) * X r k = W k * X r 2 + (2 * ((k - 2 : ℕ) : ℤ)) * X r 3 := by
  have hrn : ¬ r ≤ 3 := by omega
  -- induction on k from 2 upward
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _|k
    · omega
    rcases k with _|k
    · omega
    rcases k with _|k
    · -- k = 2
      simp [W]
    rcases k with _|k
    · -- k = 3
      simp [W]
    · -- k+4
      have hk0 : 2 ≤ k + 2 := by omega
      have hk1 : 2 ≤ k + 3 := by omega
      have hle0 : k + 2 ≤ r - 1 := by omega
      have hle1 : k + 3 ≤ r - 1 := by omega
      have ih0 := ih (k+2) (by omega) hk0 hle0
      have ih1 := ih (k+3) (by omega) hk1 hle1
      -- use recurrence solved forward: X_{j+2} = (j*X_{j+1}-X_j)/(j+1) after multiplying factorial
      have hrec : X r (k+2) = (((k+2 : ℕ) : ℤ) * X r (k+3) - (((k+2)+1 : ℕ) : ℤ) * X r (k+4)) := by
        apply X_recur hrn <;> omega
      -- rearrange recurrence to avoid division
      have hrec' : (((k+2)+1 : ℕ)! : ℤ) * X r (k+4) =
          ((k+2 : ℕ) : ℤ) * ((((k+2)! : ℤ) * X r (k+3)) - (((k+1)! : ℤ) * X r (k+2))) := by
        rw [hrec]
        simp [Nat.factorial_succ]
        ring
      have hs0 : k + 2 - 1 = k + 1 := by omega
      have hs1 : k + 2 - 2 = k := by omega
      have hs2 : k + 3 - 1 = k + 2 := by omega
      have hs3 : k + 3 - 2 = k + 1 := by omega
      have hs4 : k + 1 + 1 + 1 + 1 = k + 4 := by omega
      have hs5 : k + 4 - 1 = k + 3 := by omega
      have hs6 : k + 4 - 2 = k + 2 := by omega
      simp [hs0, hs1, hs2, hs3, hs4, hs5, hs6] at ih0 ih1 ⊢
      rw [hrec', ih0, ih1]
      rw [W_rec (k+2) (by omega)]
      have hcast2 : ((2 + k : ℕ) : ℤ) = (k : ℤ) + 2 := by omega
      have hcast3 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by omega
      have hwidx : W (k + 2 + 1) = W (k + 3) := by
        congr
      simp [hcast2, hcast3, hwidx]
      ring




lemma cfd_eq_X_div (r k : ℕ) (hr : 4 ≤ r) (hk2 : 2 ≤ k) (hkr : k ≤ r - 2)
    (hnz : ∀ j, k + 1 ≤ j → j ≤ r - 1 → X r j ≠ 0) :
    continued_fraction_denominator (r-1) k = (X r k : ℚ) / (X r (k+1) : ℚ) := by
  have hrn : ¬ r ≤ 3 := by omega
  induction k using X.induct (r:=r) with
  | case1 x h => omega
  | case2 h => omega
  | case3 h hne =>
      -- k = r-2, base of continued fraction
      have hk : r - 2 = (r - 1) - 1 := by omega
      rw [continued_fraction_denominator.eq_def]
      simp [hk]
      have hkm1 : r - 1 - 1 = r - 2 := by omega
      rw [hkm1]
      rw [X_base2 hrn]
      have hx1 : X r ((r - 2)+1) = 4 := by
        have : (r - 2)+1 = r - 1 := by omega
        rw [this, X_base1 hrn]
      rw [hx1]
      field_simp
      simp [hrn, hk2]
      have hc1 : ((r - 2 : ℕ) : ℚ) = (r : ℚ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ r)]
        norm_num
      have hc2 : ((r - 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r)]
        norm_num
      rw [hc1, hc2]
      ring
  | case4 x h hx1 hx2 hxrange ih1 ih2 =>
      rw [continued_fraction_denominator.eq_def]
      have hnle : ¬ r - 1 ≤ 2 := by omega
      have hrange : 2 ≤ x ∧ x ≤ (r - 1) - 1 := by omega
      have hnotbase : x ≠ (r - 1) - 1 := by omega
      simp [hnle, hrange, hnotbase]
      rw [ih1]
      · have hrec := X_recur hrn hxrange.1 hxrange.2
        rw [hrec]
        have hden : ((X r (x + 1) : ℚ)) ≠ 0 := by
          exact_mod_cast hnz (x+1) (by omega) (by omega)
        field_simp [hden]
        have hi3 : x + 1 + 1 = x + 2 := by omega
        rw [hi3]
        norm_num
      · omega
      · omega

      · intro j hj1 hj2
        exact hnz j (by omega) hj2
  | case5 x h hx1 hx2 hxrange => omega


lemma nat_odd_dvd_X3_of_dvd_X2 {r d : ℕ} (hr : 4 ≤ r) (hdpos : 0 < d) (hodd : Odd d)
    (hdle : d + 1 ≤ r - 1) (hdiv : (d : ℤ) ∣ X r 2) : (d : ℤ) ∣ X r 3 := by
  have hf := X_forward_formula r (d+1) hr (by omega) hdle
  have hfac_nat : d ∣ (d + 1 - 1)! := by
    have : d ≤ d + 1 - 1 := by omega
    exact Nat.dvd_factorial hdpos this
  have hfac : (d : ℤ) ∣ (((d + 1 - 1)! : ℤ) * X r (d+1)) := by
    exact dvd_mul_of_dvd_left (by exact_mod_cast hfac_nat) _
  have hright : (d : ℤ) ∣ W (d+1) * X r 2 + (2 * ((d+1 - 2 : ℕ) : ℤ)) * X r 3 := by
    rw [← hf]
    exact hfac
  have hterm1 : (d : ℤ) ∣ W (d+1) * X r 2 := dvd_mul_of_dvd_right hdiv _
  have hterm2 : (d : ℤ) ∣ (2 * ((d+1 - 2 : ℕ) : ℤ)) * X r 3 := (Int.dvd_add_right hterm1).mp hright
  have hcoef_nat_coprime : Nat.Coprime d (2 * (d - 1)) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rwa [Nat.coprime_two_right]
    · have : Nat.Coprime d (d - 1) ↔ Nat.Coprime d 1 := by
        simpa using (Nat.coprime_self_sub_right (m:=1) (n:=d) hdpos)
      rw [this]
      simp
  have hcoef : IsCoprime (d : ℤ) (2 * ((d+1 - 2 : ℕ) : ℤ)) := by
    have hdminus : d + 1 - 2 = d - 1 := by omega
    rw [hdminus]
    exact_mod_cast hcoef_nat_coprime
  exact hcoef.dvd_of_dvd_mul_left hterm2

lemma four_dvd_X3_of_four_dvd_X2 {r : ℕ} (hr : 6 ≤ r) (hdiv4 : (4 : ℤ) ∣ X r 2) : (4 : ℤ) ∣ X r 3 := by
  have hf := X_forward_formula r 5 (by omega) (by omega) (by omega)
  -- 24 * X₅ = W 5 * X₂ + 6 * X₃, and W 5 = -6.
  have hw5 : W 5 = -6 := by norm_num [W]
  norm_num [hw5] at hf
  -- from the formula, `6 * X3 = 24 * X5 + 6 * X2` up to sign; every other term is divisible by 8
  have h8_left : (8 : ℤ) ∣ (24 : ℤ) * X r 5 := by
    exact dvd_mul_of_dvd_left (by norm_num : (8 : ℤ) ∣ 24) _
  have h8_x2 : (8 : ℤ) ∣ (6 : ℤ) * X r 2 := by
    rcases hdiv4 with ⟨t, ht⟩
    use 3 * t
    rw [ht]
    ring
  have h8_sum : (8 : ℤ) ∣ (6 : ℤ) * X r 3 := by
    -- rearrange the invariant
    have : (6 : ℤ) * X r 3 = (24 : ℤ) * X r 5 + (6 : ℤ) * X r 2 := by
      linarith
    rw [this]
    exact dvd_add h8_left h8_x2
  -- since gcd(3,4)=1, divisibility by 8 of 6*x implies divisibility by 4 of x
  rcases h8_sum with ⟨t, ht⟩
  have : (6 : ℤ) * X r 3 = 8 * t := by simpa using ht
  have h3 : (3 : ℤ) * X r 3 = 4 * t := by omega
  have hcop : IsCoprime (3 : ℤ) (4 : ℤ) := by norm_num
  have h4dvd3x : (4 : ℤ) ∣ (3 : ℤ) * X r 3 := ⟨t, h3⟩
  exact hcop.symm.dvd_of_dvd_mul_left h4dvd3x


lemma rat_num_prime_div_int (p : ℕ) (s : ℤ) (hp : p.Prime) (hs0 : s ≠ 0) (hps : ¬ (p : ℤ) ∣ s) :
    (((p : ℚ) / (s : ℚ)).num.natAbs) = p := by
  have hpzpos : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hgc : s.gcd (p : ℤ) = 1 := by
    -- integer gcd is a natural number; prime divisibility criterion
    have hcop_nat : Nat.Coprime s.natAbs p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hpd
      exact hps ((Int.natCast_dvd).mpr hpd)
    have : Nat.gcd s.natAbs p = 1 := hcop_nat
    simpa [Int.gcd, Int.natAbs_natCast] using this
  have hnum : ((p : ℚ) / (s : ℚ)).num = s.sign * (p : ℤ) := by
    have hpc : (p : ℚ) = ((p : ℤ) : ℚ) := by norm_num
    rw [hpc, ← Rat.divInt_eq_div (p : ℤ) s]
    rw [Rat.num_divInt]
    rw [hgc]
    simp
  rw [hnum]
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hsign : s.sign.natAbs = 1 := by
    cases s with
    | ofNat n =>
        cases n <;> simp at hs0 ⊢
    | negSucc n => simp
  simp [hsign]

lemma A_eq_prime_of_params (p r m : ℕ) (s : ℤ) (hp : p.Prime)
    (hr : 4 ≤ r) (hrp : r ≤ p - 1)
    (hX2 : X r 2 = (p : ℤ) * (m : ℤ))
    (hX3 : X r 3 = (m : ℤ) * s)
    (hs0 : s ≠ 0) (hps : ¬ (p : ℤ) ∣ s)
    (hnz : ∀ j, 3 ≤ j → j ≤ r - 1 → X r j ≠ 0) :
    A363347 (r-1) = p := by
  have hnotle : ¬ r - 1 ≤ 2 := by omega
  unfold A363347
  simp [hnotle]
  have hcfd := cfd_eq_X_div r 2 hr (by omega) (by omega) (by
    intro j hj1 hj2
    exact hnz j (by omega) hj2)
  rw [hcfd]
  rw [hX2, hX3]
  have hm0 : (m : ℤ) ≠ 0 := by
    intro hmz
    have : X r 2 = 0 := by rw [hX2, hmz, mul_zero]
    have hx2 := X2_formula r hr
    rw [hx2] at this
    have hpge : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three ?h2 ?h3
    · nlinarith
    · intro hp2; subst p; omega
    · intro hp3; subst p; omega
  have hmq : ((m : ℚ) : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hrat : ((↑p * ↑m : ℤ) : ℚ) / ((↑m * s : ℤ) : ℚ) = (p : ℚ) / (s : ℚ) := by
    field_simp [hmq]
    norm_num
    ring
  rw [hrat]
  exact rat_num_prime_div_int p s hp hs0 hps



lemma isSquare_five_of_prime_mod_1_or_9 (p : ℕ) (hp : p.Prime)
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : IsSquare (5 : ZMod p) := by
  have hp2 : p ≠ 2 := by
    intro h; subst h; norm_num [Nat.ModEq] at hmod
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs : IsSquare ((p : ℕ) : ZMod 5) := by
    rcases hmod with h1 | h9
    · have hpmod5 : p % 5 = 1 := by
        rw [Nat.ModEq] at h1
        omega
      use (1 : ZMod 5)
      rw [← ZMod.natCast_mod p 5, hpmod5]
      norm_num
    · have hpmod5 : p % 5 = 4 := by
        rw [Nat.ModEq] at h9
        omega
      use (2 : ZMod 5)
      rw [← ZMod.natCast_mod p 5, hpmod5]
      norm_num
  have hiff := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=5) (q:=p) (by norm_num) hp2)
  exact hiff.mp hs


lemma not_dvd_Xj_of_not_dvd_X3 {p r j : ℕ} (hp : p.Prime) (hr : 4 ≤ r) (hrp : r ≤ p - 1)
    (hj3 : 3 ≤ j) (hjr : j ≤ r - 1) (hpX2 : (p : ℤ) ∣ X r 2) (hpX3 : ¬ (p : ℤ) ∣ X r 3) :
    ¬ (p : ℤ) ∣ X r j := by
  intro hpXj
  have hf := X_forward_formula r j hr (by omega) hjr
  have hleft : (p : ℤ) ∣ (((j - 1)! : ℤ) * X r j) := dvd_mul_of_dvd_right hpXj _
  have hterm1 : (p : ℤ) ∣ W j * X r 2 := dvd_mul_of_dvd_right hpX2 _
  have hsum : (p : ℤ) ∣ W j * X r 2 + (2 * ((j - 2 : ℕ) : ℤ)) * X r 3 := by
    rw [← hf]
    exact hleft
  have hterm2 : (p : ℤ) ∣ (2 * ((j - 2 : ℕ) : ℤ)) * X r 3 := (Int.dvd_add_right hterm1).mp hsum
  have hcoef_nat : Nat.Coprime p (2 * (j - 2)) := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd
    have hcases := (hp.dvd_mul).mp hpd
    rcases hcases with hp2 | hpj
    · exact not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p) hp2
    · have hjlt : j - 2 < p := by omega
      have hjpos : 0 < j - 2 := by omega
      exact not_dvd_of_pos_of_lt hjpos hjlt hpj
  have hcoef : IsCoprime (p : ℤ) (2 * ((j - 2 : ℕ) : ℤ)) := by exact_mod_cast hcoef_nat
  exact hpX3 (hcoef.dvd_of_dvd_mul_left hterm2)


lemma not_dvd_X3_of_dvd_X2 {p r : ℕ} (hp : p.Prime) (hr : 4 ≤ r) (hrp : r ≤ p - 1)
    (hpX2 : (p : ℤ) ∣ X r 2) : ¬ (p : ℤ) ∣ X r 3 := by
  intro hpX3
  have hf := X_forward_formula r (r-1) hr (by omega) (by omega)
  have hbase : X r (r-1) = 4 := X_base1 (by omega : ¬ r ≤ 3)
  rw [hbase] at hf
  have hterm1 : (p : ℤ) ∣ W (r-1) * X r 2 := dvd_mul_of_dvd_right hpX2 _
  have hterm2 : (p : ℤ) ∣ (2 * ((r-1 - 2 : ℕ) : ℤ)) * X r 3 := dvd_mul_of_dvd_right hpX3 _
  have hsum : (p : ℤ) ∣ W (r-1) * X r 2 + (2 * ((r-1 - 2 : ℕ) : ℤ)) * X r 3 := dvd_add hterm1 hterm2
  have hleft : (p : ℤ) ∣ (((r - 1 - 1)! : ℤ) * 4) := by
    rw [hf]
    exact hsum
  have hleft_nat : p ∣ (r - 1 - 1)! * 4 := by exact_mod_cast hleft
  have hcases := (hp.dvd_mul).mp hleft_nat
  rcases hcases with hpfac | hp4
  · have hple : p ≤ r - 1 - 1 := (hp.dvd_factorial).mp hpfac
    omega
  · exact not_dvd_of_pos_of_lt (by omega : 0 < 4) (by omega : 4 < p) hp4


lemma dvd_X3_of_small_factor {r m : ℕ} (hr : 4 ≤ r) (hmpos : 0 < m)
    (hmle : m + 1 ≤ r - 1) (hmX2 : (m : ℤ) ∣ X r 2)
    (hmcase : Odd m ∨ ∃ u : ℕ, m = 4 * u ∧ Odd u) : (m : ℤ) ∣ X r 3 := by
  rcases hmcase with hodd | ⟨u, hmu, huodd⟩
  · exact nat_odd_dvd_X3_of_dvd_X2 (by omega) hmpos hodd hmle hmX2
  · subst m
    have hupos : 0 < u := by
      rcases huodd with ⟨t, ht⟩
      omega
    have hu_le : u + 1 ≤ r - 1 := by nlinarith [hmle]
    have h4X2 : (4 : ℤ) ∣ X r 2 := by
      exact dvd_trans (by norm_num : (4 : ℤ) ∣ (4 * (u : ℤ))) hmX2
    have huX2 : (u : ℤ) ∣ X r 2 := by
      exact dvd_trans (dvd_mul_left (u : ℤ) (4 : ℤ)) (by simpa [mul_comm] using hmX2)
    have hr6 : 6 ≤ r := by omega
    have h4X3 := four_dvd_X3_of_four_dvd_X2 hr6 h4X2
    have huX3 := nat_odd_dvd_X3_of_dvd_X2 (by omega) hupos huodd hu_le huX2
    have hcop_nat : Nat.Coprime 4 u := by
      change Nat.Coprime (2 ^ 2) u
      rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
      simpa [Nat.coprime_two_left] using huodd
    have hcop : IsCoprime (4 : ℤ) (u : ℤ) := by exact_mod_cast hcop_nat
    simpa [Int.natCast_mul] using hcop.mul_dvd h4X3 huX3


lemma small_factor_even_root {p m r : ℕ} (hre : Even r) (hN : r*r - 5 = p*m) (hrge : 4 ≤ r) : Odd m := by
  rw [← Nat.not_even_iff_odd]
  intro hme
  have hpme : Even (p*m) := by exact hme.mul_left p
  have hleft_odd : Odd (r*r - 5) := by
    have hr2e : Even (r*r) := hre.mul_left r
    exact Nat.Even.sub_odd (by nlinarith) hr2e (by norm_num : Odd 5)
  rw [hN] at hleft_odd
  exact (Nat.not_even_iff_odd.mpr hleft_odd) hpme

lemma small_factor_odd_root {p m r : ℕ} (hpodd : Odd p) (hro : Odd r)
    (hN : r*r - 5 = p*m) (hrge : 4 ≤ r) : ∃ u, m = 4*u ∧ Odd u := by
  have h4dvd_pm : 4 ∣ p*m := by
    have h4dvd_left : 4 ∣ r*r - 5 := by
      rcases hro with ⟨a, ha⟩
      subst r
      use a*a + a - 1
      ring_nf
      omega
    rwa [← hN]
  have hcop : Nat.Coprime 4 p := by
    change Nat.Coprime (2^2) p
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
    simpa [Nat.coprime_two_left] using hpodd
  have h4m : 4 ∣ m := (hcop.dvd_mul_left).mp h4dvd_pm
  rcases h4m with ⟨u, hu⟩
  use u
  constructor
  · exact hu
  · rw [← Nat.not_even_iff_odd]
    intro hue
    have h8m : 8 ∣ m := by
      rw [hu]
      rcases hue with ⟨v, hv⟩
      subst u
      use v
      ring
    have h8left : ¬ 8 ∣ r*r - 5 := by
      rcases hro with ⟨a, ha⟩
      subst r
      intro hd
      let q := a*a + a - 1
      have hformula : (2 * a + 1) * (2 * a + 1) - 5 = 4 * q := by
        dsimp [q]
        ring_nf
        omega
      have hqodd : Odd q := by
        dsimp [q]
        have he : Even (a*a + a) := by
          simpa [pow_two, Nat.mul_succ, mul_comm, mul_left_comm, mul_assoc] using Nat.even_mul_succ_self a
        exact Nat.Even.sub_odd (by omega) he (by norm_num : Odd 1)
      rw [hformula] at hd
      rcases hd with ⟨t, ht⟩
      have h2q : 2 ∣ q := by
        use t
        omega
      exact (Nat.not_even_iff_odd.mpr hqodd) ((even_iff_two_dvd).mpr h2q)
    have h8pm : 8 ∣ p*m := dvd_mul_of_dvd_right h8m p
    rw [← hN] at h8pm
    exact h8left h8pm

lemma small_factor_of_root {p m r : ℕ} (hpodd : Odd p) (hN : r*r - 5 = p*m) (hrge : 4 ≤ r) :
    Odd m ∨ ∃ u, m = 4*u ∧ Odd u := by
  rcases Nat.even_or_odd r with hre | hro
  · exact Or.inl (small_factor_even_root hre hN hrge)
  · exact Or.inr (small_factor_odd_root hpodd hro hN hrge)

lemma exists_A_of_small_root (p r : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hr : 4 ≤ r) (hrhalf : r ≤ p / 2) (hpdvd : p ∣ r*r - 5) :
    ∃ n : ℕ, A363347 n = p := by
  let m := (r*r - 5) / p
  have hp_pos : 0 < p := hp.pos
  have hN0 : p * m = r*r - 5 := by
    dsimp [m]
    exact Nat.mul_div_cancel' hpdvd
  have hN : r*r - 5 = p*m := hN0.symm
  have hmpos : 0 < m := by
    by_contra hm0
    have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
    have hzero : r*r - 5 = 0 := by rw [hN, hmz, mul_zero]
    have hle5 : r*r ≤ 5 := Nat.sub_eq_zero_iff_le.mp hzero
    nlinarith
  have hmle0 : m ≤ r - 2 := by
    by_contra hle
    have hmge : r - 1 ≤ m := by omega
    have hpge : 2*r ≤ p := by
      have := Nat.le_of_lt_succ (Nat.lt_succ_of_le hrhalf)
      omega
    have hlower : p*m ≥ (2*r)*(r-1) := Nat.mul_le_mul hpge hmge
    have hupper : p*m = r*r - 5 := hN0
    have hbad : (2*r)*(r-1) ≤ r*r - 5 := by omega
    have hbad2 : (2*r)*(r-1) + 5 ≤ r*r := Nat.add_le_of_le_sub (by nlinarith : 5 ≤ r*r) hbad
    have hbadz : (2*(r:ℤ))*((r:ℤ)-1) + 5 ≤ (r:ℤ)*(r:ℤ) := by
      have hz : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
      have hbadz' : (((2*r)*(r-1) + 5 : ℕ) : ℤ) ≤ ((r*r : ℕ) : ℤ) := by exact_mod_cast hbad2
      norm_num at hbadz'
      rw [hz] at hbadz'
      simpa [mul_assoc] using hbadz'
    have hsquare : 0 ≤ ((r : ℤ) - 1)^2 := sq_nonneg _
    nlinarith [hbadz, hsquare]
  have hmle : m + 1 ≤ r - 1 := by omega
  have hX2_nat : X r 2 = (p*m : ℕ) := by
    rw [X2_formula r hr]
    have hcast : ((r*r - 5 : ℕ) : ℤ) = (r : ℤ)^2 - 5 := by
      rw [Nat.cast_sub (by nlinarith : 5 ≤ r*r)]
      rw [Nat.cast_mul]
      ring
    rw [← hcast, hN, Nat.cast_mul]
  have hX2 : X r 2 = (p : ℤ) * (m : ℤ) := by simpa using hX2_nat
  have hmX2 : (m : ℤ) ∣ X r 2 := by
    rw [hX2]
    exact dvd_mul_left (m : ℤ) (p : ℤ)
  have hmcase := small_factor_of_root hpodd hN hr
  have hmX3 := dvd_X3_of_small_factor hr hmpos hmle hmX2 hmcase
  rcases hmX3 with ⟨s, hs⟩
  have hX3 : X r 3 = (m : ℤ) * s := hs
  have hpX2 : (p : ℤ) ∣ X r 2 := by rw [hX2]; exact dvd_mul_right (p : ℤ) (m : ℤ)
  have hpX3not := not_dvd_X3_of_dvd_X2 hp hr (by omega) hpX2
  have hs0 : s ≠ 0 := by
    intro hsz
    apply hpX3not
    rw [hX3, hsz, mul_zero]
    exact dvd_zero _
  have hps : ¬ (p : ℤ) ∣ s := by
    intro hpss
    apply hpX3not

    rw [hX3]
    exact dvd_mul_of_dvd_right hpss (m : ℤ)
  have hnz : ∀ j, 3 ≤ j → j ≤ r - 1 → X r j ≠ 0 := by
    intro j hj3 hjr hx0
    have hpXj : (p : ℤ) ∣ X r j := by rw [hx0]; exact dvd_zero _
    exact (not_dvd_Xj_of_not_dvd_X3 hp hr (by omega) hj3 hjr hpX2 hpX3not) hpXj
  use r - 1
  exact A_eq_prime_of_params p r m s hp hr (by omega) hX2 hX3 hs0 hps hnz

lemma dvd_of_zmod_root_val (p r : ℕ) [NeZero p]
    (hroot : ((r^2 : ℕ) : ZMod p) = (5 : ZMod p)) (hrge : 4 ≤ r) : p ∣ r*r - 5 := by
  have hge : 5 ≤ r^2 := by nlinarith
  have hzv : ((r^2 : ℕ) : ZMod p) = ((5 : ℕ) : ZMod p) := by simpa using hroot
  rw [ZMod.natCast_eq_natCast_iff] at hzv
  have hd := (Nat.modEq_iff_dvd' hge).mp hzv.symm
  simpa [pow_two] using hd

lemma root_val_ge_four (p r : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hroot : ((r^2 : ℕ) : ZMod p) = (5 : ZMod p)) : 4 ≤ r := by
  by_contra hr
  have hrle : r ≤ 3 := by omega
  interval_cases r
  · norm_num at hroot
    have hzero : ((5 : ℕ) : ZMod p) = 0 := by simpa [eq_comm] using hroot
    rw [ZMod.natCast_eq_zero_iff] at hzero
    have hple : p ≤ 5 := Nat.le_of_dvd (by norm_num) hzero
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · norm_num at hzero
    · norm_num at hzero
    · norm_num at hp
    · exact hp5 rfl
  · norm_num at hroot
    have hzero : ((4 : ℕ) : ZMod p) = 0 := by
      calc ((4 : ℕ) : ZMod p) = (5 : ZMod p) - (1 : ZMod p) := by norm_num
        _ = 0 := by rw [← hroot]; ring
    rw [ZMod.natCast_eq_zero_iff] at hzero
    have hple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hzero
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · exact hp2 rfl
    · norm_num at hzero
    · norm_num at hp
  · norm_num at hroot
    have hzero : ((1 : ℕ) : ZMod p) = 0 := by
      calc ((1 : ℕ) : ZMod p) = (5 : ZMod p) - (4 : ZMod p) := by norm_num
        _ = 0 := by rw [← hroot]; ring
    rw [ZMod.natCast_eq_zero_iff] at hzero
    have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num) hzero
    have hp_two := hp.two_le
    omega
  · norm_num at hroot
    have hzero : ((4 : ℕ) : ZMod p) = 0 := by
      calc ((4 : ℕ) : ZMod p) = (9 : ZMod p) - (5 : ZMod p) := by norm_num
        _ = 0 := sub_eq_zero.mpr hroot
    rw [ZMod.natCast_eq_zero_iff] at hzero
    have hple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hzero
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · exact hp2 rfl
    · norm_num at hzero
    · norm_num at hp





/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p hpall
  rcases hpall with ⟨hp, hmod⟩
  have hp2 : p ≠ 2 := by
    intro h; subst h; norm_num [Nat.ModEq] at hmod
  have hp5 : p ≠ 5 := by
    intro h; subst h; norm_num [Nat.ModEq] at hmod
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hsqr := isSquare_five_of_prime_mod_1_or_9 p hp hmod
  rcases hsqr with ⟨z, hz⟩
  have hzpow : z ^ 2 = (5 : ZMod p) := by simpa [pow_two] using hz.symm
  have zne : z ≠ 0 := by
    intro hz0
    have hzero : ((5 : ℕ) : ZMod p) = 0 := by
      change (5 : ZMod p) = 0
      rw [← hzpow, hz0]
      norm_num
    rw [ZMod.natCast_eq_zero_iff] at hzero
    have hple : p ≤ 5 := Nat.le_of_dvd (by norm_num) hzero
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · exact hp2 rfl
    · norm_num at hzero
    · norm_num at hp
    · exact hp5 rfl
  by_cases hsmall : z.val ≤ p / 2
  · let r := z.val
    have hroot : ((r^2 : ℕ) : ZMod p) = (5 : ZMod p) := by
      dsimp [r]
      rw [Nat.cast_pow, ZMod.natCast_zmod_val]
      simpa using hzpow
    have hr : 4 ≤ r := root_val_ge_four p r hp hp2 hp5 hroot
    have hpdvd : p ∣ r*r - 5 := dvd_of_zmod_root_val p r hroot hr
    exact exists_A_of_small_root p r hp hpodd hr (by simpa [r] using hsmall) hpdvd
  · let r := (-z).val
    have hnegpow : (-z) ^ 2 = (5 : ZMod p) := by
      rw [neg_sq, hzpow]
    have hroot : ((r^2 : ℕ) : ZMod p) = (5 : ZMod p) := by
      dsimp [r]
      rw [Nat.cast_pow, ZMod.natCast_zmod_val]
      simpa using hnegpow
    have hr : 4 ≤ r := root_val_ge_four p r hp hp2 hp5 hroot
    have hrhalf : r ≤ p / 2 := by
      have hnegval := ZMod.neg_val z
      simp [zne] at hnegval
      dsimp [r]
      rw [hnegval]
      have hval_lt := z.val_lt
      omega
    have hpdvd : p ∣ r*r - 5 := dvd_of_zmod_root_val p r hroot hr
    exact exists_A_of_small_root p r hp hpodd hr hrhalf hpdvd
