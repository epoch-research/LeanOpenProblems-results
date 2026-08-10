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



/-- Integer continuants for the continued fraction.  For `2 ≤ k ≤ n`, `cfF n k`
represents the unreduced numerator at level `k` (with `cfF n (k+1)` the denominator). -/
def cfF (n k : ℕ) : ℤ :=
  if n ≤ 2 then 0
  else if 2 ≤ k ∧ k ≤ n then
    if k = n then 4
    else if k = n - 1 then (5 * (n : ℤ) - 4)
    else (k : ℤ) * cfF n (k + 1) - ((k + 1 : ℕ) : ℤ) * cfF n (k + 2)
  else 0
termination_by n - k

lemma cfF_eq_of_lt_two {n k : ℕ} (hk : k < 2) : cfF n k = 0 := by
  rw [cfF]
  by_cases hn : n ≤ 2 <;> simp [hn, not_le.mpr hk]

lemma cfF_eq_of_gt {n k : ℕ} (hk : n < k) : cfF n k = 0 := by
  rw [cfF]
  by_cases hn : n ≤ 2 <;> simp [hn, not_le.mpr hk]

lemma cfF_n {n : ℕ} (hn : 2 < n) : cfF n n = 4 := by
  rw [cfF]
  have hnle : ¬ n ≤ 2 := by omega
  simp [hnle, hn.le]

lemma cfF_n_sub_one {n : ℕ} (hn : 2 < n) : cfF n (n - 1) = 5 * (n : ℤ) - 4 := by
  rw [cfF]
  have hnle : ¬ n ≤ 2 := by omega
  have h2 : 2 ≤ n - 1 := by omega
  have hle : n - 1 ≤ n := Nat.sub_le _ _
  have hne : n - 1 ≠ n := by omega
  simp [hnle, h2, hle, hne]

lemma cfF_rec {n k : ℕ} (hn : 2 < n) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    cfF n k = (k : ℤ) * cfF n (k + 1) - ((k + 1 : ℕ) : ℤ) * cfF n (k + 2) := by
  rw [cfF]
  have hnle : ¬ n ≤ 2 := by omega
  have hle : k ≤ n := by omega
  have hk_ne_n : k ≠ n := by omega
  have hk_ne_n1 : k ≠ n - 1 := by omega
  simp [hnle, hk, hle, hk_ne_n, hk_ne_n1]

/-- Positivity plus a ratio estimate for the integer continuants away from the
bottom.  The ratio estimate is the invariant that makes the backwards
recurrence preserve positivity. -/
lemma cfF_pos_ratio_aux {n k : ℕ} (hn : 2 < n) (hk4 : 4 ≤ k) (hkn : k ≤ n - 1) :
    0 < cfF n k ∧ ((k : ℤ) * cfF n (k + 1) < 2 * cfF n k) := by
  let motive : ℕ → Prop := fun x => 4 ≤ x → x ≤ n - 1 →
    0 < cfF n x ∧ ((x : ℤ) * cfF n (x + 1) < 2 * cfF n x)
  have hmain : motive k := by
    apply cfF.induct (n := n) (motive := motive)
    · intro x hnle
      omega
    · intro hnle hxn hk4' hle'
      omega
    · intro hnle hxrange hxne hk4' hle'
      have hnsub : n - 1 + 1 = n := by omega
      rw [cfF_n_sub_one hn, hnsub, cfF_n hn]
      constructor <;> omega
    · intro x hnle hxrange hxne hn1ne ih1 _ih2 hk4' hle'
      have ih1' := ih1 (by omega : 4 ≤ x + 1) (by omega : x + 1 ≤ n - 1)
      rcases ih1' with ⟨hF1pos, hratio1⟩
      have hrec := cfF_rec (n := n) (k := x) hn (by omega : 2 ≤ x) (by omega : x + 2 ≤ n)
      have h2F1_lt_xF1 : 2 * cfF n (x + 1) < (x : ℤ) * cfF n (x + 1) := by
        have hx2 : (2 : ℤ) < (x : ℤ) := by omega
        exact mul_lt_mul_of_pos_right hx2 hF1pos
      have hterm_lt_xF1 : (((x + 1 : ℕ) : ℤ) * cfF n (x + 2)) <
          (x : ℤ) * cfF n (x + 1) := by
        exact lt_trans hratio1 h2F1_lt_xF1
      have h4F1_le_xF1 : 4 * cfF n (x + 1) ≤ (x : ℤ) * cfF n (x + 1) := by
        have hx4 : (4 : ℤ) ≤ (x : ℤ) := by omega
        exact mul_le_mul_of_nonneg_right hx4 (le_of_lt hF1pos)
      have h2term_lt_xF1 : 2 * (((x + 1 : ℕ) : ℤ) * cfF n (x + 2)) <
          (x : ℤ) * cfF n (x + 1) := by
        have h2term_lt_4F1 : 2 * (((x + 1 : ℕ) : ℤ) * cfF n (x + 2)) <
            4 * cfF n (x + 1) := by
          nlinarith [hratio1]
        exact lt_of_lt_of_le h2term_lt_4F1 h4F1_le_xF1
      constructor
      · rw [hrec]
        nlinarith [hterm_lt_xF1]
      · rw [hrec]
        nlinarith [h2term_lt_xF1]
    · intro x hnle hxrange hk4' hle'
      omega
  exact hmain hk4 hkn

/-- The continuants needed by the rational bridge are positive. -/
lemma cfF_pos {n j : ℕ} (hn : 2 < n) (hj3 : 3 ≤ j) (hjn : j ≤ n) :
    0 < cfF n j := by
  by_cases hjn' : j = n
  · subst j
    rw [cfF_n hn]
    norm_num
  by_cases hjn1 : j = n - 1
  · subst j
    rw [cfF_n_sub_one hn]
    omega
  by_cases hj4 : 4 ≤ j
  · exact (cfF_pos_ratio_aux (n := n) (k := j) hn hj4 (by omega)).1
  have hj : j = 3 := by omega
  subst j
  have hn5 : 5 ≤ n := by omega
  have hrec := cfF_rec (n := n) (k := 3) hn (by omega) (by omega : 3 + 2 ≤ n)
  rw [hrec]
  have haux := cfF_pos_ratio_aux (n := n) (k := 4) hn (by omega) (by omega : 4 ≤ n - 1)
  have h2F4_lt_3F4 : 2 * cfF n 4 < 3 * cfF n 4 := by
    nlinarith [haux.1]
  have h4F5_lt_3F4 : (4 : ℤ) * cfF n 5 < 3 * cfF n 4 :=
    lt_trans haux.2 h2F4_lt_3F4
  norm_num
  nlinarith [h4F5_lt_3F4]

lemma cfF_ne_zero {n j : ℕ} (hn : 2 < n) (hj3 : 3 ≤ j) (hjn : j ≤ n) :
    cfF n j ≠ 0 := by
  exact ne_of_gt (cfF_pos hn hj3 hjn)

lemma cfF_rat_ne_zero {n j : ℕ} (hn : 2 < n) (hj3 : 3 ≤ j) (hjn : j ≤ n) :
    (cfF n j : ℚ) ≠ 0 := by
  exact_mod_cast (cfF_ne_zero hn hj3 hjn)

/-- The side condition required by the rational bridge lemmas. -/
lemma cfF_bridge_hne {n : ℕ} (hn : 2 < n) :
    ∀ j : ℕ, 3 ≤ j → j ≤ n → (cfF n j : ℚ) ≠ 0 := by
  intro j hj3 hjn
  exact cfF_rat_ne_zero hn hj3 hjn


lemma cfF_two_aux {n k : ℕ} (hn : 2 < n) (hk2 : 2 ≤ k) (hkn : k ≤ n - 1) :
    cfF n 2 = ((k - 1 : ℕ) : ℤ) * cfF n k -
      (k : ℤ) * ((k - 2 : ℕ) : ℤ) * cfF n (k + 1) := by
  induction k with
  | zero => omega

  | succ k ih =>
      by_cases hk1 : k = 1
      · subst k
        norm_num
      · have hk2' : 2 ≤ k := by omega
        have hkn' : k ≤ n - 1 := by omega
        have ih' := ih hk2' hkn'
        have hrec_bound : k + 2 ≤ n := by omega
        calc
          cfF n 2 = ((k - 1 : ℕ) : ℤ) * cfF n k -
              (k : ℤ) * ((k - 2 : ℕ) : ℤ) * cfF n (k + 1) := ih'
          _ = (((k + 1) - 1 : ℕ) : ℤ) * cfF n (k + 1) -
              ((k + 1 : ℕ) : ℤ) * (((k + 1) - 2 : ℕ) : ℤ) * cfF n ((k + 1) + 1) := by
            rw [cfF_rec hn hk2' hrec_bound]
            have hkm1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
            have hkm2 : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
            have hkp1m1 : (((k + 1) - 1 : ℕ) : ℤ) = (k : ℤ) := by omega
            have hkp1m2 : (((k + 1) - 2 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
            rw [hkm1, hkm2, hkp1m1, hkp1m2]
            ring

lemma cfF_two_formula {n : ℕ} (hn : 2 < n) :
    cfF n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  have haux := cfF_two_aux hn (k := n - 1) (by omega) (by omega)
  have hnp1 : n - 1 + 1 = n := by omega
  rw [hnp1, cfF_n_sub_one hn, cfF_n hn] at haux
  have hn1 : (((n - 1) - 1 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hn3 : (((n - 1) - 2 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  rw [hn1, hn2, hn3] at haux
  rw [haux]
  ring


/-- Auxiliary version of the continuant/continued-fraction identity.  The extra
non-vanishing hypothesis supplies the denominators needed by the rational-field
calculation in the recursive step. -/
lemma continued_fraction_denominator_eq_cfF_div_of_ne {n k : ℕ} (hn : 2 < n)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1)
    (hne : ∀ j : ℕ, k + 1 ≤ j → j ≤ n → (cfF n j : ℚ) ≠ 0) :
    continued_fraction_denominator n k = (cfF n k : ℚ) / (cfF n (k + 1) : ℚ) := by
  let motive : ℕ → Prop := fun x => 2 ≤ x → x ≤ n - 1 →
    (∀ j : ℕ, x + 1 ≤ j → j ≤ n → (cfF n j : ℚ) ≠ 0) →
    continued_fraction_denominator n x = (cfF n x : ℚ) / (cfF n (x + 1) : ℚ)
  have hmain : motive k := by
    apply continued_fraction_denominator.induct (n := n) (motive := motive)
    · intro x hnle
      omega
    · intro _hnle hkbase hlebase hlebase' hnebase
      rw [continued_fraction_denominator]
      have hnle' : ¬ n ≤ 2 := by omega
      have hbase : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := ⟨by omega, le_rfl⟩
      simp [hnle', hbase]
      rw [cfF_n_sub_one hn]
      have hnsub : n - 1 + 1 = n := by omega
      rw [hnsub, cfF_n hn]
      have hnat : 1 ≤ n := by omega
      have hcast_sub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
        rw [Nat.cast_sub hnat]
        norm_num
      have hcast_int : ((5 * (n : ℤ) - 4 : ℤ) : ℚ) = 5 * (n : ℚ) - 4 := by norm_num
      rw [hcast_sub, hcast_int]
      ring
    · intro x hnle hxrange hxne ih hx2 hxle hne'x
      rw [continued_fraction_denominator]
      have hnle' : ¬ n ≤ 2 := by omega
      have hxrange' : 2 ≤ x ∧ x ≤ n - 1 := ⟨hx2, hxle⟩
      have hxne' : x ≠ n - 1 := hxne
      simp [hnle', hxrange', hxne']
      have hx1le : x + 1 ≤ n - 1 := by omega
      have ih' := ih (by omega : 2 ≤ x + 1) hx1le (by
        intro j hj hle
        exact hne'x j (by omega) hle)
      rw [ih']
      have hF1 : (cfF n (x + 1) : ℚ) ≠ 0 := hne'x (x + 1) (by omega) (by omega)
      have hF2 : (cfF n (x + 2) : ℚ) ≠ 0 := hne'x (x + 2) (by omega) (by omega)
      have hrecQ : (cfF n x : ℚ) =
          (x : ℚ) * (cfF n (x + 1) : ℚ) -
            ((x + 1 : ℕ) : ℚ) * (cfF n (x + 2) : ℚ) := by
        exact_mod_cast (cfF_rec (n := n) (k := x) hn hx2 (by omega : x + 2 ≤ n))
      rw [hrecQ]
      field_simp [hF1, hF2]
      norm_num
      ring
    · intro x hnle hxrange hx2 hxle
      omega
  exact hmain hk hkn hne

/-- Convenient specialization at the bottom level `k = 2`, under the same
non-vanishing side condition as the auxiliary identity. -/
lemma continued_fraction_denominator_two_eq_cfF_div_of_ne {n : ℕ} (hn : 2 < n)
    (hne : ∀ j : ℕ, 3 ≤ j → j ≤ n → (cfF n j : ℚ) ≠ 0) :
    continued_fraction_denominator n 2 = (cfF n 2 : ℚ) / (cfF n 3 : ℚ) := by
  exact continued_fraction_denominator_eq_cfF_div_of_ne (n := n) (k := 2) hn (by omega)
    (by omega) hne

/-- Bridge from the executable OEIS definition to the continuant quotient.  Once a
non-vanishing proof for the intervening continuants is available, this rewrites
`A363347 n` as the absolute value of the numerator of `cfF n 2 / cfF n 3`. -/
lemma A363347_eq_num_natAbs_cfF_div_of_ne {n : ℕ} {N D : ℤ} (hn : 2 < n)
    (hne : ∀ j : ℕ, 3 ≤ j → j ≤ n → (cfF n j : ℚ) ≠ 0)
    (hN : cfF n 2 = N) (hD : cfF n 3 = D) :
    A363347 n = (((N : ℚ) / (D : ℚ)).num.natAbs) := by
  unfold A363347
  have hnle : ¬ n ≤ 2 := by omega
  simp [hnle]
  rw [continued_fraction_denominator_two_eq_cfF_div_of_ne hn hne, hN, hD]

/-- GCD-normalized version of the bridge.  The final hypothesis is the purely
rational-arithmetic normalization fact for the displayed integer quotient; it is
exactly the remaining step needed to turn an `Int.gcd D N = m` computation into
the OEIS denominator. -/
lemma A363347_eq_natAbs_div_gcd_of_ne {n : ℕ} {N D : ℤ} {m : ℕ} (hn : 2 < n)
    (hne : ∀ j : ℕ, 3 ≤ j → j ≤ n → (cfF n j : ℚ) ≠ 0)
    (hN : cfF n 2 = N) (hD : cfF n 3 = D) (_hNpos : 0 < N)
    (_hgcd : Int.gcd D N = m)
    (hred : (((N : ℚ) / (D : ℚ)).num.natAbs) = N.natAbs / m) :
    A363347 n = N.natAbs / m := by
  rw [A363347_eq_num_natAbs_cfF_div_of_ne (n := n) (N := N) (D := D) hn hne hN hD,
    hred]



def cfC (n k : ℕ) : ℤ := (Nat.factorial (k - 1) : ℤ) * cfF n k

lemma cfC_rec {n k : ℕ} (hn : 2 < n) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    cfC n (k + 2) = (k : ℤ) * (cfC n (k + 1) - cfC n k) := by
  unfold cfC
  rw [cfF_rec hn hk hkn]
  have hk1 : k + 1 - 1 = k := by omega
  have hk2 : k + 2 - 1 = k + 1 := by omega
  have hk0 : k - 1 + 1 = k := by omega
  rw [hk1, hk2]
  have hfac1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by simp [Nat.factorial_succ]
  rw [hfac1]
  have hfac0 : Nat.factorial k = k * Nat.factorial (k - 1) := by
    conv_lhs => rw [← hk0, Nat.factorial_succ]
    rw [hk0]
  rw [hfac0]
  push_cast
  ring_nf

lemma cfC_two {n : ℕ} : cfC n 2 = cfF n 2 := by
  unfold cfC
  norm_num


lemma cfC_three {n : ℕ} : cfC n 3 = 2 * cfF n 3 := by
  unfold cfC
  norm_num

lemma cfC_n {n : ℕ} (hn : 2 < n) : cfC n n = (4 : ℤ) * Nat.factorial (n - 1) := by
  unfold cfC
  rw [cfF_n hn]
  ring

lemma cfC_n_sub_one {n : ℕ} (hn : 2 < n) :
    cfC n (n - 1) = (Nat.factorial (n - 2) : ℤ) * (5 * (n : ℤ) - 4) := by
  unfold cfC
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub, cfF_n_sub_one hn]


/-- A linear-dependence identity for the scaled continuants.  For every reachable
level `k`, `cfC n k` is an integer linear combination of `cfC n 3` and
`cfC n 2`; the coefficient of `cfC n 3` is exactly `k - 2`. -/
lemma cfC_linear {n k : ℕ} (hn : 2 < n) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    ∃ b : ℤ, cfC n k = (((k - 2 : ℕ) : ℤ) * cfC n 3) + b * cfC n 2 := by
  induction k using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more k ihk ihk1 =>
      by_cases hk0 : k = 0
      · subst k
        refine ⟨1, ?_⟩
        norm_num
      · by_cases hk1zero : k = 1
        · subst k
          refine ⟨0, ?_⟩
          norm_num
        · have hk2' : 2 ≤ k := by omega
          have hkn' : k ≤ n := by omega
          have hkn1 : k + 1 ≤ n := by omega
          rcases ihk hk2' hkn' with ⟨b0, hb0⟩
          rcases ihk1 (by omega : 2 ≤ k + 1) hkn1 with ⟨b1, hb1⟩
          refine ⟨(k : ℤ) * (b1 - b0), ?_⟩
          have hrec := cfC_rec (n := n) (k := k) hn hk2' (by omega : k + 2 ≤ n)
          rw [hrec, hb0, hb1]
          have hk_sub : (((k + 2 - 2 : ℕ) : ℤ)) = (k : ℤ) := by omega
          have hk1_sub : (((k + 1 - 2 : ℕ) : ℤ)) = (k : ℤ) - 1 := by omega
          have hk0_sub : (((k - 2 : ℕ) : ℤ)) = (k : ℤ) - 2 := by omega
          rw [hk_sub, hk1_sub, hk0_sub]
          ring

lemma cfC_n_linear {n : ℕ} (hn : 2 < n) :
    ∃ b : ℤ, cfC n n = (((n - 2 : ℕ) : ℤ) * cfC n 3) + b * cfC n 2 := by
  exact cfC_linear hn (by omega) (by omega)

/-- If an integer divides both `cfF n 2` and `cfF n 3`, then it divides the
explicit top continuant `4 * (n-1)!`.  This is the key obstruction for large
prime common divisors. -/
lemma dvd_cfC_n_of_dvd_cfF_two_and_three {n l : ℕ} (hn : 2 < n)
    (h2 : (l : ℤ) ∣ cfF n 2) (h3 : (l : ℤ) ∣ cfF n 3) :
    (l : ℤ) ∣ (4 : ℤ) * (Nat.factorial (n - 1) : ℤ) := by
  rcases cfC_n_linear hn with ⟨b, hb⟩
  have hC2 : (l : ℤ) ∣ cfC n 2 := by
    simpa [cfC_two] using h2
  have hC3 : (l : ℤ) ∣ cfC n 3 := by
    rw [cfC_three]
    exact dvd_mul_of_dvd_right h3 2
  have hlin_dvd : (l : ℤ) ∣ (((n - 2 : ℕ) : ℤ) * cfC n 3) + b * cfC n 2 := by
    exact dvd_add (dvd_mul_of_dvd_right hC3 _) (dvd_mul_of_dvd_right hC2 _)
  rw [← hb, cfC_n hn] at hlin_dvd
  simpa [mul_comm, mul_left_comm, mul_assoc] using hlin_dvd

lemma nat_dvd_of_int_nat_dvd {a b : ℕ} (h : (a : ℤ) ∣ (b : ℤ)) : a ∣ b := by
  rcases h with ⟨c, hc⟩
  use c.natAbs
  have habs : Int.natAbs ((a : ℤ) * c) = a * c.natAbs := by
    rw [Int.natAbs_mul]
    simp
  have := congrArg Int.natAbs hc
  simpa [habs] using this


lemma int_dvd_factorial_of_pos_le {d m : ℕ} (hdpos : 0 < d) (hdle : d ≤ m) :
    (d : ℤ) ∣ (Nat.factorial m : ℤ) := by
  exact_mod_cast (Nat.dvd_factorial hdpos hdle)

/-- Small divisors of `cfF n 2` divide the scaled third continuant `cfC n 3 = 2*cfF n 3`.
This proves the desired implication up to the harmless factor `2`; the following odd version
cancels that factor. -/
lemma cfC_three_dvd_of_dvd_two_of_le {n d : ℕ} (hn : 2 < n) (hdpos : 0 < d)
    (hdle : d ≤ n - 2) (hd : (d : ℤ) ∣ cfF n 2) : (d : ℤ) ∣ cfC n 3 := by
  have hC2 : (d : ℤ) ∣ cfC n 2 := by
    simpa [cfC_two] using hd
  have hfac_nm2 : (d : ℤ) ∣ (Nat.factorial (n - 2) : ℤ) :=
    int_dvd_factorial_of_pos_le hdpos hdle
  have hfac_nm1 : (d : ℤ) ∣ (Nat.factorial (n - 1) : ℤ) :=
    int_dvd_factorial_of_pos_le hdpos (by omega)
  have hCn : (d : ℤ) ∣ cfC n n := by
    rw [cfC_n hn]
    exact dvd_mul_of_dvd_right hfac_nm1 4
  have hCn1 : (d : ℤ) ∣ cfC n (n - 1) := by
    rw [cfC_n_sub_one hn]
    exact dvd_mul_of_dvd_left hfac_nm2 _
  rcases cfC_linear hn (k := n) (by omega) (by omega) with ⟨b, hb⟩
  rcases cfC_linear hn (k := n - 1) (by omega) (by omega) with ⟨b1, hb1⟩
  have hA : (d : ℤ) ∣ (((n - 2 : ℕ) : ℤ) * cfC n 3) := by
    rw [hb] at hCn
    have hsub := dvd_sub hCn (dvd_mul_of_dvd_right hC2 b)
    convert hsub using 1
    ring
  have hB : (d : ℤ) ∣ (((n - 1 - 2 : ℕ) : ℤ) * cfC n 3) := by
    rw [hb1] at hCn1
    have hsub := dvd_sub hCn1 (dvd_mul_of_dvd_right hC2 b1)
    convert hsub using 1
    ring
  have hdiff := dvd_sub hA hB
  have hcoef : ((n - 2 : ℕ) : ℤ) - ((n - 1 - 2 : ℕ) : ℤ) = 1 := by omega
  convert hdiff using 1
  symm
  calc
    (((n - 2 : ℕ) : ℤ) * cfC n 3) - (((n - 1 - 2 : ℕ) : ℤ) * cfC n 3)
        = (((n - 2 : ℕ) : ℤ) - ((n - 1 - 2 : ℕ) : ℤ)) * cfC n 3 := by ring
    _ = cfC n 3 := by rw [hcoef]; ring

lemma cfF_three_dvd_of_odd_dvd_two_of_le {n d : ℕ} (hn : 2 < n) (hdpos : 0 < d)
    (hdle : d ≤ n - 2) (hodd : Odd d) (hd : (d : ℤ) ∣ cfF n 2) :
    (d : ℤ) ∣ cfF n 3 := by
  have hC := cfC_three_dvd_of_dvd_two_of_le hn hdpos hdle hd
  rw [cfC_three] at hC
  have hgcd_nat : Nat.gcd d 2 = 1 := by
    simpa [Nat.coprime_two_right] using hodd
  have hgcd_int : Int.gcd (d : ℤ) (2 : ℤ) = 1 := by
    rw [Int.gcd_def]
    simpa using hgcd_nat
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hC hgcd_int

/-- Large-prime exclusion: a prime larger than `n+1` cannot divide both
`cfF n 2` and `cfF n 3`. -/
lemma cfF_large_prime_not_dvd_three_of_dvd_two {n l : ℕ} (hn : 2 < n)
    (hl : l.Prime) (hlarge : n + 1 < l) (h2 : (l : ℤ) ∣ cfF n 2) :
    ¬ (l : ℤ) ∣ cfF n 3 := by
  intro h3
  have hInt := dvd_cfC_n_of_dvd_cfF_two_and_three hn h2 h3
  have hNat : l ∣ 4 * Nat.factorial (n - 1) := by
    exact nat_dvd_of_int_nat_dvd hInt
  have hl_not4 : ¬ l ∣ 4 := by
    intro h4
    have hle4 : l ≤ 4 := Nat.le_of_dvd (by norm_num) h4
    omega
  have hl_not_fac : ¬ l ∣ Nat.factorial (n - 1) := by
    intro hfac
    have hle : l ≤ n - 1 := hl.dvd_factorial.mp hfac
    omega
  have hcases := (hl.dvd_mul.mp hNat)
  rcases hcases with h4 | hfac
  · exact hl_not4 h4
  · exact hl_not_fac hfac


/-- Package the factorization conditions into the final OEIS value.  With
`n = r - 1`, the explicit formula gives `cfF n 2 = r^2 - 5 = p*m`.  The
small odd factor `m` divides the third continuant, while the large prime `p`
does not; hence the numerator of the reduced continuant quotient is exactly
`p`. -/
lemma A363347_eq_prime_of_factor_conditions {p r m : ℕ}
    (hp : p.Prime) (hr2 : 2 < r) (hrp : r < p)
    (hmfac : r^2 - 5 = p * m) (hmpos : 0 < m) (hmle : m ≤ (r - 1) - 2)
    (hoddm : Odd m) : A363347 (r - 1) = p := by
  let n := r - 1
  have hn : 2 < n := by
    dsimp [n]
    omega
  have hcf2 : cfF n 2 = (p : ℤ) * (m : ℤ) := by
    rw [cfF_two_formula hn]
    dsimp [n]
    have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hcast]
    have hquad : ((r : ℤ) - 1)^2 + 2 * ((r : ℤ) - 1) - 4 = (r : ℤ)^2 - 5 := by ring
    rw [hquad]
    have h5 : 5 ≤ r^2 := by nlinarith [hr2]
    have hcast_sub : ((r^2 - 5 : ℕ) : ℤ) = (r : ℤ)^2 - 5 := by
      rw [Nat.cast_sub h5, Nat.cast_pow]
      norm_num
    rw [← hcast_sub]
    exact_mod_cast hmfac
  have hm_dvd_cf2 : (m : ℤ) ∣ cfF n 2 := by
    rw [hcf2]
    exact dvd_mul_left (m : ℤ) (p : ℤ)
  have hp_dvd_cf2 : (p : ℤ) ∣ cfF n 2 := by
    rw [hcf2]
    exact dvd_mul_right (p : ℤ) (m : ℤ)
  have hm_dvd_cf3 : (m : ℤ) ∣ cfF n 3 := by
    exact cfF_three_dvd_of_odd_dvd_two_of_le (n := n) (d := m) hn hmpos (by
      dsimp [n] at hmle ⊢
      exact hmle) hoddm hm_dvd_cf2
  have hp_not_dvd_cf3 : ¬ (p : ℤ) ∣ cfF n 3 := by
    exact cfF_large_prime_not_dvd_three_of_dvd_two (n := n) (l := p) hn hp (by
      dsimp [n]
      omega) hp_dvd_cf2
  have hcf3pos : 0 < cfF n 3 := cfF_pos hn (by omega) (by omega)
  rcases hm_dvd_cf3 with ⟨c, hc⟩
  have hcpos : 0 < c := by
    have hmZpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hmpos
    have hprodpos : 0 < (m : ℤ) * c := by
      rwa [← hc]
    by_contra hnot
    have hcle : c ≤ 0 := le_of_not_gt hnot
    have hprodle : (m : ℤ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmZpos.le hcle
    linarith
  have hp_not_dvd_c : ¬ (p : ℤ) ∣ c := by
    intro hpc
    exact hp_not_dvd_cf3 (by
      rw [hc]
      exact dvd_mul_of_dvd_right hpc (m : ℤ))
  have hp_not_dvd_c_natAbs : ¬ p ∣ c.natAbs := by
    intro hpc
    exact hp_not_dvd_c ((Int.natCast_dvd (m := p) (n := c)).mpr hpc)
  have hcop : Nat.Coprime (p : ℤ).natAbs c.natAbs := by
    have hcop' : Nat.Coprime p c.natAbs := hp.coprime_iff_not_dvd.mpr hp_not_dvd_c_natAbs
    simpa using hcop'
  have hrat_eq :
      (((((p : ℤ) * (m : ℤ) : ℤ) : ℚ) / (cfF n 3 : ℚ)) = ((p : ℤ) : ℚ) / (c : ℚ)) := by
    rw [hc]
    have hmQ : ((m : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hmpos)
    field_simp [hmQ]
    push_cast
    ring
  have hnum : (((((p : ℤ) : ℚ) / (c : ℚ)) : ℚ).num = (p : ℤ)) := by
    simpa using Rat.num_div_eq_of_coprime (a := (p : ℤ)) (b := c) hcpos hcop
  have hbridge := A363347_eq_num_natAbs_cfF_div_of_ne (n := n)
    (N := (p : ℤ) * (m : ℤ)) (D := cfF n 3) hn (cfF_bridge_hne hn) hcf2 rfl
  change A363347 n = p
  rw [hbridge, hrat_eq, hnum]
  simp





/-!
Partial formalization work toward the supplied proof outline.

The next lemmas isolate two parts of the argument which are independent of
unfolding the continued fraction: (1) elementary congruence consequences of
`p ≡ 1` or `9 [MOD 10]`, and (2) the factorization step from a square-root of
`5` modulo `p`, namely `r^2 - 5 = p * m` with `m < r` under the usual bounds.
The final block records several checked witnesses for the sequence itself.
-/

lemma oeis363347_mod10_one_or_nine_to_mod5 {p : ℕ}
    (h : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
    p ≡ 1 [MOD 5] ∨ p ≡ 4 [MOD 5] := by
  rcases h with h | h
  · left
    exact h.of_dvd (by norm_num)
  · right
    have h95 : (9 : ℕ) ≡ 4 [MOD 5] := by norm_num
    exact (h.of_dvd (by norm_num)).trans h95

lemma oeis363347_prime_mod10_not_two_or_five {p : ℕ} (_hp : p.Prime)
    (h : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : p ≠ 2 ∧ p ≠ 5 := by
  constructor
  · intro hp2
    subst p
    rcases h with h | h
    · have hn : ¬ ((2 : ℕ) ≡ 1 [MOD 10]) := by norm_num
      exact hn h
    · have hn : ¬ ((2 : ℕ) ≡ 9 [MOD 10]) := by norm_num
      exact hn h
  · intro hp5
    subst p
    rcases h with h | h
    · have hn : ¬ ((5 : ℕ) ≡ 1 [MOD 10]) := by norm_num
      exact hn h
    · have hn : ¬ ((5 : ℕ) ≡ 9 [MOD 10]) := by norm_num
      exact hn h


lemma oeis363347_zmod5_isSquare_of_mod5_one_or_four {p : ℕ}
    (h : p ≡ 1 [MOD 5] ∨ p ≡ 4 [MOD 5]) : IsSquare (p : ZMod 5) := by
  rcases h with h | h
  · refine ⟨1, ?_⟩
    simpa using (ZMod.natCast_eq_natCast_iff p 1 5).mpr h
  · refine ⟨2, ?_⟩
    norm_num
    exact (ZMod.natCast_eq_natCast_iff p 4 5).mpr h

lemma oeis363347_isSquare_five_zmod_of_prime_mod10 {p : ℕ} (hp : p.Prime)
    (h : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : IsSquare (5 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (5 : ℕ).Prime := ⟨by norm_num⟩
  have hsq : IsSquare (p : ZMod 5) :=
    oeis363347_zmod5_isSquare_of_mod5_one_or_four
      (oeis363347_mod10_one_or_nine_to_mod5 h)
  have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
    (by norm_num) (oeis363347_prime_mod10_not_two_or_five hp h).1
  exact hiff.mp hsq

lemma oeis363347_nat_sqrt_from_zmod_square {p : ℕ} [NeZero p] {x : ZMod p}
    (hx : x * x = (5 : ZMod p)) : x.val^2 ≡ 5 [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  change (((x.val)^2 : ℕ) : ZMod p) = (5 : ZMod p)
  rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  simpa [pow_two] using hx

lemma oeis363347_exists_nat_sqrt5_mod_of_prime_mod10 {p : ℕ} (hp : p.Prime)
    (h : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
    ∃ r, r^2 ≡ 5 [MOD p] ∧ r < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases oeis363347_isSquare_five_zmod_of_prime_mod10 hp h with ⟨x, hx⟩
  refine ⟨x.val, ?_, ZMod.val_lt x⟩
  exact oeis363347_nat_sqrt_from_zmod_square (by simpa [mul_comm] using hx.symm)

lemma oeis363347_sqrt5_mod_gt_one_of_prime_mod10 {p r : ℕ} (hp : p.Prime)
    (h10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) (hmod : r^2 ≡ 5 [MOD p]) : 1 < r := by
  have hp_ne := oeis363347_prime_mod10_not_two_or_five hp h10
  have hr0 : r ≠ 0 := by
    intro hz
    subst r
    have h50 : 5 ≡ 0 [MOD p] := by simpa using hmod.symm
    have hp_dvd5 : p ∣ 5 := Nat.modEq_zero_iff_dvd.mp h50
    have hp_eq5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp_dvd5
    exact hp_ne.2 hp_eq5
  have hr1 : r ≠ 1 := by
    intro h1
    subst r
    have h15 : 1 ≡ 5 [MOD p] := by simpa using hmod
    have hp_dvd4 : p ∣ 4 := by
      have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 5)).mp h15
      norm_num at this ⊢
      exact this
    have hp_dvd2pow : p ∣ 2^2 := by simpa using hp_dvd4
    have hp_dvd2 : p ∣ 2 := hp.dvd_of_dvd_pow hp_dvd2pow
    have hp_eq2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd2
    exact hp_ne.1 hp_eq2
  omega

lemma oeis363347_exists_nat_sqrt5_mod_between_of_prime_mod10 {p : ℕ} (hp : p.Prime)
    (h : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
    ∃ r, 1 < r ∧ r^2 ≡ 5 [MOD p] ∧ r < p := by
  rcases oeis363347_exists_nat_sqrt5_mod_of_prime_mod10 hp h with ⟨r, hmod, hlt⟩
  exact ⟨r, oeis363347_sqrt5_mod_gt_one_of_prime_mod10 hp h hmod, hmod, hlt⟩


lemma oeis363347_sqrt5_mod_ne_two_of_prime {p r : ℕ} (hp : p.Prime)
    (hmod : r^2 ≡ 5 [MOD p]) : r ≠ 2 := by
  intro hr
  subst r
  have h45 : 4 ≡ 5 [MOD p] := by simpa using hmod
  have hp_dvd1 : p ∣ 1 := by
    have := (Nat.modEq_iff_dvd' (by norm_num : 4 ≤ 5)).mp h45
    norm_num at this ⊢
    exact this
  exact hp.not_dvd_one hp_dvd1

lemma oeis363347_sqrt5_mod_gt_two_of_prime_mod10 {p r : ℕ} (hp : p.Prime)
    (h10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) (hmod : r^2 ≡ 5 [MOD p]) :
    2 < r := by
  have hr1 := oeis363347_sqrt5_mod_gt_one_of_prime_mod10 hp h10 hmod
  have hrne2 := oeis363347_sqrt5_mod_ne_two_of_prime hp hmod
  omega

lemma oeis363347_prime_odd_of_mod10_one_or_nine {p : ℕ} (hp : p.Prime)
    (h10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : Odd p := by
  exact hp.odd_of_ne_two (oeis363347_prime_mod10_not_two_or_five hp h10).1

lemma oeis363347_sqrt5_mod_sub_of_sqrt5_mod {p r : ℕ} (hrp : r < p)
    (hmod : r^2 ≡ 5 [MOD p]) : (p - r)^2 ≡ 5 [MOD p] := by
  have hsquare : (p - r)^2 ≡ r^2 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hsub : ((p - r : ℕ) : ZMod p) = -((r : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrp)]
      simp
    rw [Nat.cast_pow, Nat.cast_pow, hsub]
    ring
  exact hsquare.trans hmod

lemma oeis363347_exists_even_nat_sqrt5_mod_between_of_prime_mod10 {p : ℕ} (hp : p.Prime)
    (h10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
    ∃ r, 2 < r ∧ Even r ∧ r^2 ≡ 5 [MOD p] ∧ r < p := by
  rcases oeis363347_exists_nat_sqrt5_mod_between_of_prime_mod10 hp h10 with ⟨r, hr1, hmod, hrp⟩
  by_cases hre : Even r
  · exact ⟨r, oeis363347_sqrt5_mod_gt_two_of_prime_mod10 hp h10 hmod, hre, hmod, hrp⟩
  · have hpodd : Odd p := oeis363347_prime_odd_of_mod10_one_or_nine hp h10
    have hrodd : Odd r := Nat.not_even_iff_odd.mp hre
    have hsub_even : Even (p - r) := by
      rw [Nat.even_sub' (Nat.le_of_lt hrp)]
      exact ⟨fun _ => hrodd, fun _ => hpodd⟩
    have hsub_mod : (p - r)^2 ≡ 5 [MOD p] :=
      oeis363347_sqrt5_mod_sub_of_sqrt5_mod hrp hmod
    have hsub_lt : p - r < p := by omega
    exact ⟨p - r, oeis363347_sqrt5_mod_gt_two_of_prime_mod10 hp h10 hsub_mod,
      hsub_even, hsub_mod, hsub_lt⟩

lemma oeis363347_exists_even_nat_sqrt5_mod_between_of_prime_mod10_one {p : ℕ}
    (hp : p.Prime) (h10 : p ≡ 1 [MOD 10]) :
    ∃ r, 2 < r ∧ Even r ∧ r^2 ≡ 5 [MOD p] ∧ r < p := by
  exact oeis363347_exists_even_nat_sqrt5_mod_between_of_prime_mod10 hp (Or.inl h10)

lemma oeis363347_exists_even_nat_sqrt5_mod_between_of_prime_mod10_nine {p : ℕ}
    (hp : p.Prime) (h10 : p ≡ 9 [MOD 10]) :
    ∃ r, 2 < r ∧ Even r ∧ r^2 ≡ 5 [MOD p] ∧ r < p := by
  exact oeis363347_exists_even_nat_sqrt5_mod_between_of_prime_mod10 hp (Or.inr h10)


lemma oeis363347_quadratic_part_int (r : ℤ) :
    (r - 1)^2 + 2 * (r - 1) - 4 = r^2 - 5 := by
  ring

lemma oeis363347_nat_quadratic_factor_of_modEq {p r : ℕ}
    (h : r^2 ≡ 5 [MOD p]) (h5 : 5 ≤ r^2) : ∃ m, r^2 - 5 = p * m := by
  have hd : p ∣ r^2 - 5 := (Nat.modEq_iff_dvd' h5).mp h.symm
  rcases hd with ⟨m, hm⟩
  exact ⟨m, by rw [hm]⟩

lemma oeis363347_quadratic_minus_five_lt_mul_of_lt {p r : ℕ} (hr : 0 < r) (hrp : r < p) :
    r^2 - 5 < p * r := by
  have h1 : r^2 - 5 ≤ r^2 := Nat.sub_le _ _
  have h2 : r^2 < p * r := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_right hrp hr
  omega

lemma oeis363347_factor_lt_of_product_lt {p r m : ℕ}
    (hm : r^2 - 5 = p * m) (hupper : r^2 - 5 < p * r) : m < r := by
  by_contra hmr
  have hge : p * r ≤ p * m := Nat.mul_le_mul_left p (Nat.le_of_not_gt hmr)
  omega

lemma oeis363347_sqrt5_mod_produces_small_factor {p r : ℕ}
    (hmod : r^2 ≡ 5 [MOD p]) (h5 : 5 ≤ r^2) (hr : 0 < r) (hrp : r < p) :
    ∃ m, r^2 - 5 = p * m ∧ m < r := by
  rcases oeis363347_nat_quadratic_factor_of_modEq hmod h5 with ⟨m, hm⟩
  exact ⟨m, hm, oeis363347_factor_lt_of_product_lt hm
    (oeis363347_quadratic_minus_five_lt_mul_of_lt hr hrp)⟩

lemma A363347_zero_of_le_two {n : ℕ} (hn : n ≤ 2) : A363347 n = 0 := by
  simp [A363347, hn]


/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p ⟨hp, h10⟩
  rcases oeis363347_exists_even_nat_sqrt5_mod_between_of_prime_mod10 hp h10 with
    ⟨r, hr2, hreven, hmod, hrp⟩
  have h5 : 5 ≤ r^2 := by nlinarith [hr2]
  have hrpos : 0 < r := by omega
  rcases oeis363347_sqrt5_mod_produces_small_factor hmod h5 hrpos hrp with
    ⟨m, hmfac, hmlt⟩
  have hmpos : 0 < m := by
    by_contra hmnot
    have hm0 : m = 0 := by omega
    have hzero : r^2 - 5 = 0 := by simpa [hm0] using hmfac
    have hgt : 5 < r^2 := by nlinarith [hr2]
    omega
  have hoddm : Odd m := by
    have heven_r2 : Even (r^2) := by
      exact hreven.pow_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
    have hodd_left : Odd (r^2 - 5) := by
      exact Nat.Even.sub_odd h5 heven_r2 (by norm_num : Odd (5 : ℕ))
    have hodd_prod : Odd (p * m) := by
      rw [← hmfac]
      exact hodd_left
    exact Odd.of_mul_right hodd_prod
  have hmle : m ≤ (r - 1) - 2 := by
    have hm_ne_rsub1 : m ≠ r - 1 := by
      intro hmr
      have hpge : r + 1 ≤ p := by omega
      have hge : (r + 1) * (r - 1) ≤ p * m := by
        rw [hmr]
        exact Nat.mul_le_mul hpge le_rfl
      have hsub : r - 1 + 1 = r := Nat.sub_add_cancel (by omega : 1 ≤ r)
      have hprod_succ_eq : (r + 1) * (r - 1) + 1 = r^2 := by
        nlinarith
      have hlt : r^2 - 5 < (r + 1) * (r - 1) := by
        omega
      omega
    have hm_ne_rsub2 : m ≠ r - 2 := by
      intro hmr
      have heven_rsub2 : Even (r - 2) := by
        rw [Nat.even_sub' (by omega : 2 ≤ r)]
        constructor
        · intro hodd_r
          exact False.elim ((Nat.not_odd_iff_even.mpr hreven) hodd_r)
        · intro hodd_two
          norm_num at hodd_two
      have hodd_rsub2 : Odd (r - 2) := by simpa [hmr] using hoddm
      exact (Nat.not_odd_iff_even.mpr heven_rsub2) hodd_rsub2
    omega
  exact ⟨r - 1, A363347_eq_prime_of_factor_conditions hp hr2 hrp hmfac hmpos hmle hoddm⟩
