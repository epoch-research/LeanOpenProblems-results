import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A295124: $a(n)$ is the smallest number $k$ with $n$ prime factors such that $2d + k/d$ is prime for every $d \mid k$.
The definition interprets "n prime factors" as $n$ distinct prime factors ($\omega(k) = n$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidate numbers $k$ for a given $n$.
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      -- $\omega(k) = n$, k has n distinct prime factors.
      (Nat.primeFactors k).card = n ∧
      -- For every divisor d of k, $2d + k/d$ is prime.
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

  -- $a(n)$ is the smallest element of this set. sInf is the infimum function on sets of ℕ.
  sInf (S n)

/-- The predicate that `2d + k/d` is prime for every divisor `d` of `k`. -/
def Good (k : ℕ) : Prop :=
  ∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d)

lemma dvd_prime_mul_iff {d p m : ℕ} (hp : p.Prime) (hd : d ∣ p * m) :
    d ∣ m ∨ (p ∣ d ∧ d / p ∣ m) := by
  by_cases hpm : p ∣ d
  · right
    refine ⟨hpm, ?_⟩
    obtain ⟨k, hk⟩ := hpm
    rw [hk] at hd
    have : k ∣ m := (Nat.mul_dvd_mul_iff_left hp.pos).mp hd
    have : d / p = k := by
      rw [hk, Nat.mul_div_cancel_left k hp.pos]
    rwa [this]
  · left
    have hcop : p.Coprime d := hp.coprime_iff_not_dvd.mpr hpm
    exact (hcop.symm.dvd_mul_left).mp hd

lemma prime_3 : Nat.Prime 3 := by norm_num
lemma prime_5 : Nat.Prime 5 := by norm_num
lemma prime_7 : Nat.Prime 7 := by norm_num
lemma prime_19 : Nat.Prime 19 := by norm_num
lemma prime_23 : Nat.Prime 23 := by norm_num
lemma prime_71 : Nat.Prime 71 := by norm_num

lemma eq_of_div {p n : ℕ} (hp : p ∣ n) : n = p * (n / p) :=
  (Nat.mul_div_cancel' hp).symm

lemma prime_form_of_eq {k d n : ℕ} (h : d = n) (hp : Nat.Prime (2 * n + k / n)) :
    Nat.Prime (2 * d + k / d) := by
  subst h; exact hp

lemma good_1 : Good 1 := by
  intro d hd
  have : d = 1 := by
    rw [divisors_one] at hd
    simpa using hd
  subst this
  norm_num

lemma good_3 : Good 3 := by
  intro d hd
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hle : d ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hdiv
  interval_cases d
  all_goals
    try (norm_num; done)
    try (exfalso; revert hdiv; decide)

lemma good_15 : Good 15 := by
  intro d hd
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hle : d ≤ 15 := Nat.le_of_dvd (by decide : 0 < 15) hdiv
  interval_cases d
  all_goals
    try (norm_num; done)
    try (exfalso; revert hdiv; decide)

lemma good_105 : Good 105 := by
  intro d hd
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hle : d ≤ 105 := Nat.le_of_dvd (by decide : 0 < 105) hdiv
  interval_cases d
  all_goals
    try (norm_num; done)
    try (exfalso; revert hdiv; decide)

lemma eq_93081 : 93081 = 3 * (19 * (23 * 71)) := by norm_num

set_option maxHeartbeats 800000 in
lemma good_93081 : Good 93081 := by
  intro d hd
  have hdiv0 : d ∣ 93081 := (Nat.mem_divisors.mp hd).1
  have hdiv : d ∣ 3 * (19 * (23 * 71)) := by rwa [eq_93081] at hdiv0
  have h3 := dvd_prime_mul_iff prime_3 hdiv
  rcases h3 with h3 | ⟨h3d, h3⟩
  · have h19 := dvd_prime_mul_iff prime_19 h3
    rcases h19 with h19 | ⟨h19d, h19⟩
    · have h23 := dvd_prime_mul_iff prime_23 h19
      rcases h23 with h23 | ⟨h23d, h23⟩
      · have : d = 1 ∨ d = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with rfl | rfl <;> norm_num
      · have : d / 23 = 1 ∨ d / 23 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 23)
          · rw [eq_of_div h23d, h]
          · norm_num
        · apply prime_form_of_eq (n := 1633)
          · rw [eq_of_div h23d, h]
          · norm_num
    · have h23 := dvd_prime_mul_iff prime_23 h19
      rcases h23 with h23 | ⟨h23d, h23⟩
      · have : d / 19 = 1 ∨ d / 19 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 19)
          · rw [eq_of_div h19d, h]
          · norm_num
        · apply prime_form_of_eq (n := 1349)
          · rw [eq_of_div h19d, h]
          · norm_num
      · have : d / 19 / 23 = 1 ∨ d / 19 / 23 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 437)
          · rw [eq_of_div h19d, eq_of_div h23d, h]
          · norm_num
        · apply prime_form_of_eq (n := 31027)
          · rw [eq_of_div h19d, eq_of_div h23d, h]
          · norm_num
  · have h19 := dvd_prime_mul_iff prime_19 h3
    rcases h19 with h19 | ⟨h19d, h19⟩
    · have h23 := dvd_prime_mul_iff prime_23 h19
      rcases h23 with h23 | ⟨h23d, h23⟩
      · have : d / 3 = 1 ∨ d / 3 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 3)
          · rw [eq_of_div h3d, h]
          · norm_num
        · apply prime_form_of_eq (n := 213)
          · rw [eq_of_div h3d, h]
          · norm_num
      · have : d / 3 / 23 = 1 ∨ d / 3 / 23 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 69)
          · rw [eq_of_div h3d, eq_of_div h23d, h]
          · norm_num
        · apply prime_form_of_eq (n := 4899)
          · rw [eq_of_div h3d, eq_of_div h23d, h]
          · norm_num
    · have h23 := dvd_prime_mul_iff prime_23 h19
      rcases h23 with h23 | ⟨h23d, h23⟩
      · have : d / 3 / 19 = 1 ∨ d / 3 / 19 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 57)
          · rw [eq_of_div h3d, eq_of_div h19d, h]
          · norm_num
        · apply prime_form_of_eq (n := 4047)
          · rw [eq_of_div h3d, eq_of_div h19d, h]
          · norm_num
      · have : d / 3 / 19 / 23 = 1 ∨ d / 3 / 19 / 23 = 71 := (Nat.dvd_prime prime_71).mp h23
        rcases this with h | h
        · apply prime_form_of_eq (n := 1311)
          · rw [eq_of_div h3d, eq_of_div h19d, eq_of_div h23d, h]
          · norm_num
        · apply prime_form_of_eq (n := 93081)
          · rw [eq_of_div h3d, eq_of_div h19d, eq_of_div h23d, h]
          · norm_num

lemma card_1 : (Nat.primeFactors 1).card = 0 := by simp
lemma card_3 : (Nat.primeFactors 3).card = 1 := by simp
lemma card_15 : (Nat.primeFactors 15).card = 2 := by simp
lemma card_105 : (Nat.primeFactors 105).card = 3 := by simp
lemma card_93081 : (Nat.primeFactors 93081).card = 4 := by simp

lemma memS {k n : ℕ} (hk : k > 0) (hc : (Nat.primeFactors k).card = n)
    (hg : Good k) :
    k ∈ (({k : ℕ | k > 0 ∧ (Nat.primeFactors k).card = n ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))} : Set ℕ)) :=
  ⟨hk, hc, hg⟩


lemma good_squarefree {k p : ℕ} (hg : Good k) (hp : p.Prime) (hdiv : p ^ 2 ∣ k)
    (hk : k ≠ 0) : False := by
  have hpdiv : p ∣ k := dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) hdiv
  have hpd : p ∈ Nat.divisors k := Nat.mem_divisors.mpr ⟨hpdiv, hk⟩
  have hpr : Nat.Prime (2 * p + k / p) := hg p hpd
  have hpe : p ∣ k / p := by
    rw [pow_two] at hdiv
    exact Nat.dvd_div_of_mul_dvd hdiv
  have : p ∣ 2 * p + k / p := dvd_add (dvd_mul_of_dvd_right dvd_rfl _) hpe
  have hlt : p < 2 * p + k / p := by
    have hpos : 0 < k / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hpdiv) hp.pos
    omega
  exact Nat.not_prime_of_dvd_of_lt this hp.one_lt hlt hpr

lemma good_not_even {k : ℕ} (hg : Good k) (hk : 1 < k) : ¬ Even k := by
  intro he
  have h1 : 1 ∈ Nat.divisors k := by
    rw [Nat.one_mem_divisors]
    omega
  have hpr : Nat.Prime (2 + k) := by
    have := hg 1 h1
    simpa using this
  obtain ⟨m, hm⟩ := he
  have heq : 2 + k = 2 * (m + 1) := by
    rw [hm]; ring
  have : ¬ Nat.Prime (2 + k) := by
    rw [heq]
    exact Nat.not_prime_mul (by decide : 2 ≠ 1) (by omega : m + 1 ≠ 1)
  exact this hpr

lemma good_k_add_two_prime {k : ℕ} (hg : Good k) (hk : k ≠ 0) : Nat.Prime (k + 2) := by
  have h1 : 1 ∈ Nat.divisors k := Nat.one_mem_divisors.mpr hk
  have := hg 1 h1
  simpa [Nat.add_comm] using this

lemma good_two_k_add_one_prime {k : ℕ} (hg : Good k) (hk : k ≠ 0) : Nat.Prime (2 * k + 1) := by
  have hkmem : k ∈ Nat.divisors k := Nat.mem_divisors_self k hk
  have := hg k hkmem
  simpa [Nat.div_self (Nat.pos_of_ne_zero hk)] using this

lemma good_imp_squarefree {k : ℕ} (hg : Good k) (hk : k ≠ 0) : Squarefree k := by
  refine (Nat.squarefree_iff_prime_squarefree).2 ?_
  intro p hp hdiv
  exact good_squarefree hg hp (by simpa [pow_two] using hdiv) hk

lemma exists_good_omega_le_four :
    ∀ n : ℕ, n ≤ 4 →
      ({k : ℕ | k > 0 ∧ (Nat.primeFactors k).card = n ∧ Good k} : Set ℕ).Nonempty := by
  intro n hn
  interval_cases n
  · exact ⟨1, memS (by decide) card_1 good_1⟩
  · exact ⟨3, memS (by decide) card_3 good_3⟩
  · exact ⟨15, memS (by decide) card_15 good_15⟩
  · exact ⟨105, memS (by decide) card_105 good_105⟩
  · exact ⟨93081, memS (by decide) card_93081 good_93081⟩

lemma good_imp_odd {k : ℕ} (hg : Good k) (hk : 0 < k) : Odd k := by
  by_cases h1 : k = 1
  · subst h1; decide
  · have : 1 < k := Nat.lt_of_le_of_ne hk.nat_succ_le (Ne.symm h1)
    exact not_even_iff_odd.mp (good_not_even hg this)

/-- Distinct divisors of an odd `k` yield distinct forms `2d + k/d`. -/
lemma forms_eq_imp_eq_of_odd {k d e : ℕ} (hkodd : Odd k)
    (hd : d ∣ k) (he : e ∣ k)
    (h : 2 * d + k / d = 2 * e + k / e) : d = e := by
  have hkd : (k / d) * d = k := Nat.div_mul_cancel hd
  have hke : (k / e) * e = k := Nat.div_mul_cancel he
  have hcleared : (2 * d * d + k : ℤ) * e = (2 * e * e + k : ℤ) * d := by
    have hL : ((2 * d + k / d : ℕ) : ℤ) * d = 2 * d * d + k := by
      have : ((k / d : ℕ) : ℤ) * d = k := by exact_mod_cast hkd
      push_cast; linarith
    have hR : ((2 * e + k / e : ℕ) : ℤ) * e = 2 * e * e + k := by
      have : ((k / e : ℕ) : ℤ) * e = k := by exact_mod_cast hke
      push_cast; linarith
    have hZ : ((2 * d + k / d : ℕ) : ℤ) = (2 * e + k / e : ℕ) := by exact_mod_cast h
    have := congrArg (fun x : ℤ => x * d * e) hZ
    have h1 : ((2 * d + k / d : ℕ) : ℤ) * d * e = (2 * d * d + k) * e := by rw [hL]
    have h2 : ((2 * e + k / e : ℕ) : ℤ) * e * d = (2 * e * e + k) * d := by rw [hR]
    have h2' : ((2 * e + k / e : ℕ) : ℤ) * d * e = (2 * e * e + k) * d := by
      convert h2 using 1; ring
    linarith
  have hfact : ((d : ℤ) - e) * (2 * d * e - k) = 0 := by
    linear_combination hcleared
  rcases Int.mul_eq_zero.mp hfact with hde | hk2
  · exact_mod_cast (sub_eq_zero.mp hde)
  · have hkZ : (k : ℤ) = 2 * d * e := by linarith
    have : k = 2 * (d * e) := by
      have := congrArg Int.toNat hkZ
      simpa [Int.toNat_natCast, mul_assoc] using this
    have hk_even : Even k := by
      rw [this]; exact even_two_mul (d * e)
    exact (Nat.not_even_iff_odd.mpr hkodd hk_even).elim

/-- Residue `2` (or `4` when `q = 5`) for the first prime and `1` for the rest
avoids every form vanishing modulo an odd prime `q`. -/
def admissibleResidue (q : ℕ) : ℕ := if q = 5 then 4 else 2

lemma admissibleResidue_pos (q : ℕ) : 0 < admissibleResidue q := by
  unfold admissibleResidue; split_ifs <;> decide

lemma admissibleResidue_coprime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (admissibleResidue q).Coprime q := by
  unfold admissibleResidue
  split_ifs with h
  · subst h; decide
  · rw [Nat.coprime_comm]
    exact hq.coprime_iff_not_dvd.2 (by
      intro hdvd
      have : q ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdvd
      have : q = 2 := le_antisymm this hq.two_le
      exact hq2 this)

lemma two_mul_admissibleResidue_add_one_ne_zero {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ 2 * admissibleResidue q + 1 := by
  unfold admissibleResidue
  split_ifs with h
  · subst h; decide
  · intro hdvd
    -- `2 * 2 + 1 = 5`, so `q ∣ 5`
    have : q ∣ 5 := by simpa using hdvd
    have hq5 : q = 5 := (Nat.dvd_prime prime_5).1 this |>.resolve_left hq.ne_one
    exact h hq5

lemma admissibleResidue_add_two_ne_zero {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ admissibleResidue q + 2 := by
  unfold admissibleResidue
  split_ifs with h
  · subst h; decide
  · intro hdvd
    have h4 : q ∣ 4 := by simpa using hdvd
    have hle : q ≤ 4 := Nat.le_of_dvd (by decide) h4
    interval_cases q
    · exact hq.ne_zero rfl
    · exact hq.ne_one rfl
    · exact hq2 rfl
    · exact (by decide : ¬ 3 ∣ 4) h4
    · exact (by decide : ¬ Nat.Prime 4) hq

/-- If `p` divides an odd squarefree `k`, then `p` divides none of the forms `2d + k/d`. -/
lemma form_not_dvd_of_prime_dvd {k p d : ℕ} (hp : p.Prime) (hodd : Odd k)
    (hsq : Squarefree k) (hpk : p ∣ k) (hd : d ∣ k) :
    ¬ p ∣ 2 * d + k / d := by
  intro hdiv
  have hk0 : k ≠ 0 := by
    intro h; subst h
    exact (by decide : ¬ Odd 0) hodd
  have hAorB : p ∣ d ∨ p ∣ k / d := by
    have : p ∣ d * (k / d) := by
      rw [Nat.mul_div_cancel' hd]
      exact hpk
    exact hp.dvd_mul.mp this
  have hp2 : p ∣ d ∧ p ∣ k / d := by
    rcases hAorB with hpd | hpkd
    · have : p ∣ k / d := by
        have := (Nat.dvd_add_right (dvd_mul_of_dvd_right hpd 2)).mp hdiv
        exact this
      exact ⟨hpd, this⟩
    · have : p ∣ d := by
        have hp2d : p ∣ 2 * d := (Nat.dvd_add_left hpkd).mp hdiv
        have hpne2 : p ≠ 2 := by
          intro h
          subst h
          exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hpk)
        have hcop : Nat.Coprime p 2 :=
          hp.coprime_iff_not_dvd.2 (by
            intro h2
            have : p = 2 := (Nat.dvd_prime Nat.prime_two).1 h2 |>.resolve_left hp.ne_one
            exact hpne2 this)
        exact (Nat.Coprime.dvd_mul_left hcop).mp hp2d
      exact ⟨this, hpkd⟩
  have : p * p ∣ k := by
    have h1 : p ∣ d := hp2.1
    have h2 : p ∣ k / d := hp2.2
    have : p * p ∣ d * (k / d) := Nat.mul_dvd_mul h1 h2
    rwa [Nat.mul_div_cancel' hd] at this
  have : ¬ Squarefree k := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro h
    exact h p hp (by simpa [pow_two] using this)
  exact this hsq

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/

theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n
  match n with
  | 0 =>
    refine ⟨1, memS (by decide) card_1 good_1⟩
  | 1 =>
    refine ⟨3, memS (by decide) card_3 good_3⟩
  | 2 =>
    refine ⟨15, memS (by decide) card_15 good_15⟩
  | 3 =>
    refine ⟨105, memS (by decide) card_105 good_105⟩
  | 4 =>
    refine ⟨93081, memS (by decide) card_93081 good_93081⟩
  | n + 5 =>
    sorry
