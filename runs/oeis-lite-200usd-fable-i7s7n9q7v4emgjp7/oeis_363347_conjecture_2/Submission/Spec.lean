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

namespace A363347Proof

/-- `T n = n^2 + 2n - 4 = (n+1)^2 - 5` (for `n ≥ 2`), written without subtraction issues. -/
def T (n : ℕ) : ℕ := (n - 2) * (n + 4) + 4

/-- Partial sums of factorials: `F n κ = ∑_{j=κ+3}^{n-1} (j-3)!`. -/
def F (n κ : ℕ) : ℕ := ∑ i ∈ Finset.range (n - (κ + 3)), (i + κ)!

/-- The scaled denominator sequence: `G n κ = (n-2) * N_{κ+3}·(κ+2)!/(κ+1)`-ish;
concretely `G n κ = 4(n-1)! + (n-2) * T n * F n κ`. -/
def G (n : ℕ) (κ : ℕ) : ℕ := 4 * (n - 1)! + (n - 2) * T n * F n κ

lemma T_eq (n : ℕ) (h : 2 ≤ n) : T n + 5 = (n + 1) * (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [T, Nat.add_sub_cancel_left]
  ring

lemma F_step (n κ : ℕ) (h : κ + 4 ≤ n) : F n κ = κ ! + F n (κ + 1) := by
  unfold F
  have h1 : n - (κ + 3) = (n - (κ + 4)) + 1 := by omega
  rw [h1, Finset.sum_range_succ']
  have h2 : n - (κ + 1 + 3) = n - (κ + 4) := by omega
  rw [h2]
  simp only [Nat.zero_add]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

lemma G_pos (n κ : ℕ) : 0 < G n κ := by
  unfold G
  positivity

lemma G_id (n κ : ℕ) (h : κ + 5 ≤ n) :
    (κ + 2) * G n (κ + 1) = (κ + 1) * G n κ + G n (κ + 2) := by
  have h1 : F n κ = κ ! + F n (κ + 1) := F_step n κ (by omega)
  have h2 : F n (κ + 1) = (κ + 1)! + F n (κ + 2) := F_step n (κ + 1) (by omega)
  unfold G
  rw [h1, h2, Nat.factorial_succ]
  ring


lemma cfd_base (n : ℕ) (h : 3 ≤ n) :
    continued_fraction_denominator n (n - 1) = ((n - 1 : ℕ) : ℚ) + (n : ℚ) / 4 := by
  rw [continued_fraction_denominator]
  rw [if_neg (by omega), if_pos (by omega), if_pos rfl]

lemma cfd_step (n k : ℕ) (h2 : 2 ≤ k) (h3 : k < n - 1) :
    continued_fraction_denominator n k =
      (k : ℚ) - ((k : ℚ) + 1) / continued_fraction_denominator n (k + 1) := by
  rw [continued_fraction_denominator]
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]


lemma cf_at (d : ℕ) : ∀ (κ n : ℕ), n = κ + 4 + d →
    continued_fraction_denominator n (κ + 3) =
      ((κ + 3) * (κ + 1) * G n κ : ℕ) / ((κ + 2) * G n (κ + 1) : ℕ) := by
  induction d with
  | zero =>
    intro κ n hn
    subst hn
    have hbase := cfd_base (κ + 4) (by omega)
    rw [show κ + 4 - 1 = κ + 3 from by omega] at hbase
    rw [hbase]
    have hF1 : F (κ + 4) κ = κ ! := by
      unfold F
      rw [show κ + 4 - (κ + 3) = 1 from by omega]
      simp
    have hF2 : F (κ + 4) (κ + 1) = 0 := by
      unfold F
      rw [show κ + 4 - (κ + 1 + 3) = 0 from by omega]
      simp
    unfold G
    rw [hF1, hF2, show κ + 4 - 1 = κ + 3 from by omega, show κ + 4 - 2 = κ + 2 from by omega]
    unfold T
    rw [show κ + 4 - 2 = κ + 2 from by omega,
        show (κ + 3)! = (κ+3)*((κ+2)*((κ+1)*κ !)) from by
          rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]]
    have hpos : (0:ℚ) < ((κ + 2) * (4 * ((κ+3)*((κ+2)*((κ+1)*κ !))) + (κ + 2) * ((κ + 2) * (κ + 4 + 4) + 4) * 0) : ℕ) := by
      have := Nat.factorial_pos κ
      positivity
    rw [eq_div_iff (ne_of_gt hpos)]
    push_cast
    ring
  | succ d ih =>
    intro κ n hn
    have hG0 : (0:ℚ) < (G n κ : ℚ) := by exact_mod_cast G_pos n κ
    have hG1 : (0:ℚ) < (G n (κ+1) : ℚ) := by exact_mod_cast G_pos n (κ+1)
    have hG2 : (0:ℚ) < (G n (κ+2) : ℚ) := by exact_mod_cast G_pos n (κ+2)
    have keyQ : ((κ:ℚ)+2) * (G n (κ+1) : ℚ) = ((κ:ℚ)+1) * (G n κ : ℚ) + (G n (κ+2) : ℚ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℚ)) (G_id n κ (by omega))
    have h4 : continued_fraction_denominator n (κ + 3 + 1) =
        (((κ:ℚ)+4)*((κ:ℚ)+2)*(G n (κ+1):ℚ)) / (((κ:ℚ)+3)*(G n (κ+2):ℚ)) := by
      have h := ih (κ+1) n (by omega)
      rw [show κ + 1 + 3 = κ + 3 + 1 from by omega] at h
      rw [h, show κ + 1 + 1 = κ + 2 from by omega]
      push_cast
      ring
    rw [cfd_step n (κ+3) (by omega) (by omega), h4]
    push_cast
    rw [div_div_eq_mul_div]
    field_simp
    linear_combination ((κ:ℚ)+4) * keyQ


lemma cf2 (n : ℕ) (h : 3 ≤ n) :
    continued_fraction_denominator n 2 = ((2 * (n - 2) * T n : ℕ) : ℚ) / ((G n 0 : ℕ) : ℚ) := by
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · have h3 : n = 3 := by omega
    subst h3
    have hb := cfd_base 3 (by norm_num)
    norm_num at hb
    rw [hb]
    have hF : F 3 0 = 0 := by unfold F; simp
    unfold G T
    rw [hF]
    norm_num [Nat.factorial]
  · have hG0 : (0:ℚ) < (G n 0 : ℚ) := by exact_mod_cast G_pos n 0
    have hG1 : (0:ℚ) < (G n 1 : ℚ) := by exact_mod_cast G_pos n 1
    have h3 := cf_at (n - 4) 0 n (by omega)
    norm_num at h3
    have key : (G n 0 : ℚ) = (G n 1 : ℚ) + ((n - 2 : ℕ) : ℚ) * (T n : ℚ) := by
      have h0 : F n 0 = 1 + F n 1 := by simpa using F_step n 0 (by omega)
      unfold G
      rw [h0]
      push_cast
      ring
    rw [cfd_step n 2 le_rfl (by omega), h3]
    push_cast
    field_simp
    linear_combination (3:ℚ) * key


lemma G0_eq (n : ℕ) (h : 3 ≤ n) :
    G n 0 = (n - 2) * (4 * (n - 1) * (n - 3)! + T n * F n 0) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, n = ν + 3 := ⟨n - 3, by omega⟩
  unfold G
  simp only [show ν + 3 - 1 = ν + 2 from by omega, show ν + 3 - 2 = ν + 1 from by omega,
    show ν + 3 - 3 = ν from by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  ring

lemma F_even (n : ℕ) (h : 5 ≤ n) : 2 ∣ F n 0 := by
  unfold F
  rw [show n - (0 + 3) = (n - 5) + 1 + 1 from by omega, Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hs : 2 ∣ ∑ i ∈ Finset.range (n - 5), (i + 1 + 1 + 0)! := by
    apply Finset.dvd_sum
    intro i _
    exact Nat.dvd_factorial (by norm_num) (by omega)
  have h1 : (0 + 1 + 0)! = 1 := by norm_num
  have h0 : (0 + 0)! = 1 := by norm_num
  omega

lemma T_pos (n : ℕ) : 0 < T n := by unfold T; omega


lemma main_lemma (n p : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) (hp : p.Prime) (hp5 : 5 < p)
    (hnp : n < p) (hdvd : p ∣ T n) : A363347 n = p := by
  have hT_pos : 0 < T n := T_pos n
  obtain ⟨m, hm⟩ := hdvd
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [Nat.mul_zero] at hm; omega
    · exact h
  -- `p ≥ n + 3`
  have hTeq := T_eq n (by omega)
  have hpn1 : p ≠ n + 1 := by
    rintro rfl
    have h5 : (n + 1) ∣ 5 := by
      have hp2 : (n + 1) ∣ (n + 1) * (n + 1) := dvd_mul_right (n + 1) (n + 1)
      have hpT : (n + 1) ∣ T n := ⟨m, hm⟩
      have := Nat.dvd_sub hp2 hpT
      rw [show (n + 1) * (n + 1) - T n = 5 from by omega] at this
      exact this
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  have hpn2 : p ≠ n + 2 := by
    rintro rfl
    have hTn4 : T n + 4 = n * (n + 2) := by
      have e : (n + 1) * (n + 1) = n * (n + 2) + 1 := by ring
      omega
    have h4 : (n + 2) ∣ 4 := by
      have h1 : (n + 2) ∣ n * (n + 2) := dvd_mul_left (n + 2) n
      have h2 : (n + 2) ∣ T n := ⟨m, hm⟩
      have := Nat.dvd_sub h1 h2
      rw [show n * (n + 2) - T n = 4 from by omega] at this
      exact this
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  have hp3 : n + 3 ≤ p := by omega
  -- `n ≠ 4`
  have hn4 : n ≠ 4 := by
    rintro rfl
    have h20 : p ∣ 20 := by
      have : T 4 = 20 := by norm_num [T]
      exact ⟨m, by omega⟩
    have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) h20
    interval_cases p <;> revert h20 <;> revert hp <;> decide
  -- `m ≤ n - 2`
  have hm_le : m ≤ n - 2 := by
    by_contra hc
    push_neg at hc
    have h1 : (n + 3) * (n - 1) ≤ p * m := Nat.mul_le_mul hp3 (by omega)
    have hlt : T n < (n + 3) * (n - 1) := by
      unfold T
      obtain ⟨ν, rfl⟩ : ∃ ν, n = ν + 3 := ⟨n - 3, by omega⟩
      simp only [show ν + 3 - 2 = ν + 1 from by omega, show ν + 3 - 1 = ν + 2 from by omega,
        show ν + 3 + 4 = ν + 7 from by omega, show ν + 3 + 3 = ν + 6 from by omega]
      nlinarith
    omega
  -- `m ∣ (n-3)!`
  have hm_ne : m ≠ 0 := by omega
  have hm_dvd_fac : m ∣ (n - 3)! := by
    rw [← Nat.factorization_le_iff_dvd hm_ne (Nat.factorial_ne_zero _), Finsupp.le_def]
    intro q
    by_cases hq : q.Prime
    · rcases Nat.eq_zero_or_pos (m.factorization q) with h0 | hpos
      · simp [h0]
      have hqe_dvd : q ^ m.factorization q ∣ m := Nat.ordProj_dvd m q
      have hqe_le : q ^ m.factorization q ≤ m := Nat.le_of_dvd (by omega) hqe_dvd
      have hq2 : 2 ≤ q ^ m.factorization q := by
        calc 2 ≤ q := hq.two_le
        _ ≤ q ^ m.factorization q := Nat.le_self_pow (by omega) q
      have hne : q ^ m.factorization q ≠ n - 2 := by
        intro heq
        have hd : (n - 2) ∣ T n := heq ▸ (hqe_dvd.trans ⟨p, by rw [hm]; ring⟩)
        have hd4 : (n - 2) ∣ 4 := by
          unfold T at hd
          exact (Nat.dvd_add_right (Dvd.intro (n + 4) rfl)).mp hd
        have hle4 : n - 2 ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
        have hub : n ≤ 6 := by omega
        interval_cases n <;> omega
      have hle3 : q ^ m.factorization q ≤ n - 3 := by omega
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hq (Nat.factorial_ne_zero _)]
      exact Nat.dvd_factorial (by omega) hle3
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  -- The (doubled) reduced denominator `D` with `G n 0 = (n-2) * D`
  set D : ℕ := 4 * (n - 1) * (n - 3)! + T n * F n 0 with hD_def
  have hD_pos : 0 < D := by
    have h1 : 0 < 4 * (n - 1) * (n - 3)! :=
      Nat.mul_pos (by omega) (Nat.factorial_pos _)
    omega
  have hmD : m ∣ D := by
    apply Nat.dvd_add
    · exact Dvd.dvd.mul_left hm_dvd_fac _
    · exact Dvd.dvd.mul_right ⟨p, by rw [hm]; ring⟩ _
  -- `2m ∣ D`
  have h2mD : 2 * m ∣ D := by
    rcases Nat.even_or_odd n with hev | hod
    · -- n even, so n ≥ 8
      obtain ⟨a, ha⟩ := hev
      have hn8 : 8 ≤ n := by omega
      -- T n = 4 * u with u odd
      obtain ⟨b, hb⟩ := Nat.even_mul_succ_self a
      have he1 : (n + 1) * (n + 1) = 4 * (a * (a + 1)) + 1 := by rw [ha]; ring
      have hu : T n = 4 * (2 * b - 1) ∧ (2 * b - 1) % 2 = 1 := by omega
      -- 4 ∣ m
      have hcop4 : Nat.Coprime 4 p := by
        have : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr this)
      have h4m : 4 ∣ m := by
        apply hcop4.dvd_of_dvd_mul_left
        rw [← hm, hu.1]
        exact ⟨2 * b - 1, rfl⟩
      obtain ⟨w, hw⟩ := h4m
      -- w odd
      have hw_odd : w % 2 = 1 := by
        rcases Nat.even_or_odd w with hwe | hwo
        · exfalso
          obtain ⟨c, hc⟩ := hwe
          have : T n = p * (4 * (c + c)) := by rw [hm, hw, hc]
          have h8T : 8 ∣ T n := ⟨p * c, by rw [this]; ring⟩
          omega
        · exact Nat.odd_iff.mp hwo
      -- 8 ∣ D
      have h8D : 8 ∣ D := by
        have h2fac : 2 ∣ (n - 3)! := Nat.dvd_factorial (by norm_num) (by omega)
        obtain ⟨f, hf⟩ := h2fac
        obtain ⟨g, hg⟩ := F_even n (by omega)
        have e1 : 8 ∣ 4 * (n - 1) * (n - 3)! := ⟨(n - 1) * f, by rw [hf]; ring⟩
        have e2 : 8 ∣ T n * F n 0 := ⟨(2 * b - 1) * g, by rw [hu.1, hg]; ring⟩
        omega
      -- conclude
      have hcop : Nat.Coprime 8 w := by
        have : Nat.Coprime w 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hw_odd)
        have := (this.pow_right 3).symm
        norm_num at this
        exact this
      have hwD : w ∣ D := dvd_trans ⟨4, by rw [hw]; ring⟩ hmD
      have : 8 * w ∣ D := hcop.mul_dvd_of_dvd_of_dvd h8D hwD
      exact dvd_trans ⟨1, by rw [hw]; ring⟩ this
    · -- n odd : m odd and 2 ∣ D
      have hT_odd : T n % 2 = 1 := by
        obtain ⟨a, ha⟩ := hod
        have he1 : (n + 1) * (n + 1) = 4 * ((a + 1) * (a + 1)) := by rw [ha]; ring
        omega
      have hm_odd : m % 2 = 1 := by
        rcases Nat.even_or_odd m with hme | hmo
        · exfalso
          obtain ⟨c, hc⟩ := hme
          have : T n = 2 * (p * c) := by rw [hm, hc]; ring
          omega
        · exact Nat.odd_iff.mp hmo
      have h2D : 2 ∣ D := by
        rcases Nat.lt_or_ge n 5 with h5 | h5
        · -- n = 3
          have hn3 : n = 3 := by omega
          subst hn3
          have hF0 : F 3 0 = 0 := by unfold F; simp
          rw [hD_def, hF0]
          norm_num [Nat.factorial]
        · have h2TF : 2 ∣ T n * F n 0 := Dvd.dvd.mul_left (F_even n h5) _
          have h2A : 2 ∣ 4 * (n - 1) * (n - 3)! := ⟨2 * (n - 1) * (n - 3)!, by ring⟩
          omega
      have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hm_odd)
      exact hcop.mul_dvd_of_dvd_of_dvd h2D hmD
  -- `p` does not divide `D`
  have hpD : ¬ p ∣ D := by
    intro hpd
    have h1 : p ∣ T n * F n 0 := Dvd.dvd.mul_right ⟨m, hm⟩ _
    have h2 : p ∣ 4 * (n - 1) * (n - 3)! := by
      have h3 := Nat.dvd_sub hpd h1
      rw [show D - T n * F n 0 = 4 * (n - 1) * (n - 3)! from by omega] at h3
      exact h3
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
      · have := Nat.le_of_dvd (by norm_num) h4; omega
      · have := Nat.le_of_dvd (by omega) h4; omega
    · have := (Nat.Prime.dvd_factorial hp).mp h3; omega
  -- write `D = 2*m*s`
  obtain ⟨s, hs⟩ := h2mD
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · rw [Nat.mul_zero] at hs; omega
    · exact h
  have hps : ¬ p ∣ s := fun h => hpD (h.trans ⟨2 * m, by rw [hs]; ring⟩)
  have hcop : Nat.Coprime p s := (Nat.Prime.coprime_iff_not_dvd hp).mpr hps
  -- final computation of the numerator
  have hA : A363347 n = (continued_fraction_denominator n 2).num.natAbs := by
    rw [A363347, if_neg (by omega : ¬ n ≤ 2)]
  rw [hA, cf2 n hn]
  have hG0 : G n 0 = (n - 2) * D := by
    have := G0_eq n hn
    rw [← hD_def] at this
    exact this
  have hratio : ((2 * (n - 2) * T n : ℕ) : ℚ) / ((G n 0 : ℕ) : ℚ) = (p : ℚ) / (s : ℚ) := by
    rw [hG0, hs, hm]
    have hd1 : (((n - 2) * (2 * m * s) : ℕ) : ℚ) ≠ 0 := by
      have : 0 < (n - 2) * (2 * m * s) :=
        Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hs_pos)
      exact_mod_cast Nat.pos_iff_ne_zero.mp this
    have hd2 : ((s : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp hs_pos
    rw [div_eq_div_iff hd1 hd2]
    push_cast
    ring
  rw [hratio]
  have hnum : ((p : ℚ) / (s : ℚ)).num = (p : ℤ) := by
    have hb : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs_pos
    have hco : (Int.natAbs (p : ℤ)).Coprime (Int.natAbs (s : ℤ)) := by simpa using hcop
    have h := Rat.num_div_eq_of_coprime hb hco
    push_cast at h ⊢
    exact h
  rw [hnum]
  simp


theorem final : ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  rintro p ⟨hp, hmod⟩
  have hmod' : p % 10 = 1 ∨ p % 10 = 9 := by
    rcases hmod with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hp2 := hp.two_le
  have hp5 : 5 < p := by omega
  have hpne2 : p ≠ 2 := by omega
  rcases eq_or_ne p 11 with rfl | hp11
  · exact ⟨3, main_lemma 3 11 (by norm_num) (by norm_num) hp (by norm_num) (by norm_num)
      (by norm_num [T])⟩
  -- 5 is a square mod p
  have fact_p : Fact p.Prime := ⟨hp⟩
  have fact_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5sq : IsSquare ((5 : ℕ) : ZMod p) := by
    apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by norm_num : 5 % 4 = 1) hpne2).mp
    have h5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
    have hcast : ((p % 5 : ℕ) : ZMod 5) = (p : ZMod 5) := ZMod.natCast_mod p 5
    rcases h5 with h | h <;> rw [← hcast, h]
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  obtain ⟨r, hr⟩ := h5sq
  have hnz : NeZero p := ⟨hp.ne_zero⟩
  set x := r.val with hx_def
  have hx_lt : x < p := ZMod.val_lt r
  have hx_mod : x * x ≡ 5 [MOD p] := by
    have h1 : ((x * x : ℕ) : ZMod p) = ((5 : ℕ) : ZMod p) := by
      push_cast at hr ⊢
      rw [ZMod.natCast_val, ZMod.cast_id]
      exact hr.symm
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have hx4 : 4 ≤ x := by
    by_contra hc
    push_neg at hc
    interval_cases x
    · have h1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hx_mod
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have h1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hx_mod
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have h1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hx_mod
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have h1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hx_mod.symm
      have := Nat.le_of_dvd (by norm_num) h1
      omega
  -- set n := x - 1
  refine ⟨x - 1, main_lemma (x - 1) p (by omega) ?_ hp hp5 (by omega) ?_⟩
  · -- n ≠ 6, i.e. x ≠ 7
    intro h7
    have hx7 : x = 7 := by omega
    rw [hx7] at hx_mod
    have h1 : p ∣ 44 := (Nat.modEq_iff_dvd' (by norm_num)).mp hx_mod.symm
    have h2 : p ∣ 4 * 11 := by norm_num at h1 ⊢; exact h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) h3; omega
    · exact hp11 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
  · -- p ∣ T (x - 1)
    have hTeq := T_eq (x - 1) (by omega)
    rw [show x - 1 + 1 = x from by omega] at hTeq
    have h1 : p ∣ x * x - 5 := (Nat.modEq_iff_dvd' (by nlinarith)).mp hx_mod.symm
    rw [show x * x - 5 = T (x - 1) from by omega] at h1
    exact h1

end A363347Proof

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  A363347Proof.final
