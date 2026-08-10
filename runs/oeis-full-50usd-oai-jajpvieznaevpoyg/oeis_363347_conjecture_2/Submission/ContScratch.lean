import FormalConjectures.Util.ProblemImports
open Rat Nat

def contE (m k : ℕ) : ℤ :=
  if k = m then -1
  else if k + 1 = m then 4
  else if k < m then (k : ℤ) * contE m (k + 1) - ((k + 1 : ℕ) : ℤ) * contE m (k + 2)
  else 0
termination_by m - k
decreasing_by
  · omega
  · have : k + 1 < m := by omega
    omega

lemma contE_rec (m k : ℕ) (h : k + 1 < m) :
    contE m k = (k : ℤ) * contE m (k+1) - ((k+1:ℕ):ℤ) * contE m (k+2) := by
  rw [contE]
  simp [show k ≠ m by omega, show k+1 ≠ m by omega, show k < m by omega]

lemma contE_top (m : ℕ) : contE m m = -1 := by simp [contE]
lemma contE_top1_of_pos (m : ℕ) (hm : 0 < m) : contE m (m-1) = 4 := by
  rw [contE]
  have h1 : m - 1 ≠ m := by omega
  have h2 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simp [h1, h2]

lemma contE_invariant (m k : ℕ) (hk2 : 2 ≤ k) (hkm : k ≤ m-1) :
    ((k-1 : ℕ) : ℤ) * contE m k - ((k:ℕ):ℤ) * ((k-2:ℕ):ℤ) * contE m (k+1)
      = ((m:ℤ)^2 - 5) := by
  -- descending induction on m-k using Nat.le_induction? Try induction on d=m-k.
  induction' h : m - k using Nat.strong_induction_on with d ih generalizing k
  have hle : k < m := by omega
  by_cases htop : k + 1 = m
  · -- k=m-1
    have hmpos : 0 < m := by omega
    have hk_eq : k = m-1 := by omega
    subst k
    have hm3 : 3 ≤ m := by omega
    rw [contE_top1_of_pos m hmpos]
    have hs : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
    rw [hs, contE_top]
    have hA : ((m - 1 - 1 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    have hB : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    have hC : ((m - 1 - 2 : ℕ) : ℤ) = (m : ℤ) - 3 := by omega
    rw [hA, hB, hC]
    ring
  · have hk1lt : k + 1 < m := by omega
    have ih' := ih (m - (k+1)) (by omega) (k+1) (by omega) (by omega) (by rfl)
    rw [contE_rec m k hk1lt]
    -- ih' is invariant at k+1
    ring_nf at ih' ⊢
    have hA : ((1 + k - 1 : ℕ) : ℤ) = (k : ℤ) := by omega
    have hB : ((1 + k - 2 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have hC : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have hD : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
    rw [hA, hB] at ih'
    rw [hC, hD]
    ring_nf at ih' ⊢
    exact ih'

lemma contE_pos (m k : ℕ) (hm : 4 ≤ m) (hk2 : 2 ≤ k) (hkm : k ≤ m-1) : 0 < contE m k := by
  induction' h : m - k using Nat.strong_induction_on with d ih generalizing k
  by_cases htop : k + 1 = m
  · have hmpos : 0 < m := by omega
    have hk_eq : k = m-1 := by omega
    subst k
    rw [contE_top1_of_pos m hmpos]
    norm_num
  · have hk1lt : k + 1 < m := by omega
    have hk1le : k + 1 ≤ m - 1 := by omega
    have ihpos : 0 < contE m (k+1) := ih (m-(k+1)) (by omega) (k+1) (by omega) hk1le (by rfl)
    have hinv := contE_invariant m k hk2 hkm
    have hkm5 : 0 < (m:ℤ)^2 - 5 := by nlinarith [show (4:ℤ) ≤ (m:ℤ) by omega]
    have hkminus : 0 < ((k-1:ℕ):ℤ) := by omega
    have hnonneg : 0 ≤ ((k:ℕ):ℤ) * ((k-2:ℕ):ℤ) * contE m (k+1) := by positivity
    have hposprod : 0 < ((k-1:ℕ):ℤ) * contE m k := by
      nlinarith
    rw [mul_comm] at hposprod
    exact pos_of_mul_pos_left hposprod (by omega : (0:ℤ) ≤ ((k-1:ℕ):ℤ))

def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else if 2 ≤ k ∧ k ≤ n - 1 then
    if k = n - 1 then (k : ℚ) + (n : ℚ) / 4
    else let R_next := continued_fraction_denominator n (k + 1); (k : ℚ) - (k + 1 : ℚ) / R_next
  else 0
termination_by n-k

lemma cf_eq_contE (m k : ℕ) (hm : 4 ≤ m) (hk2 : 2 ≤ k) (hkm : k ≤ m-2) :
    continued_fraction_denominator (m-1) k = (contE m k : ℚ) / (contE m (k+1) : ℚ) := by
  induction' h : (m - 2) - k using Nat.strong_induction_on with d ih generalizing k
  by_cases hbase : k = m - 2
  · subst k
    rw [continued_fraction_denominator]
    have hnle : ¬ m - 1 ≤ 2 := by omega
    have hrange : 2 ≤ m - 2 ∧ m - 2 ≤ m - 1 - 1 := by omega
    have hlast : m - 2 = m - 1 - 1 := by omega
    simp [hnle, hrange, hlast]
    have hmpos : 0 < m := by omega
    have hrec0 := contE_rec m (m-2) (by omega)
    have hA : m - 2 + 1 = m - 1 := by omega
    have hB : m - 2 + 2 = m := by omega
    have hC : m - 1 - 1 = m - 2 := by omega
    rw [hC, hrec0, hA, hB, contE_top1_of_pos m hmpos, contE_top]
    field_simp
    norm_num
    ring_nf
    omega
  · have hklt : k < m - 2 := by omega
    have ih' := ih ((m-2)-(k+1)) (by omega) (k+1) (by omega) (by omega) (by rfl)
    rw [continued_fraction_denominator]
    have hnle : ¬ m - 1 ≤ 2 := by omega
    have hrange : 2 ≤ k ∧ k ≤ m - 1 - 1 := by omega
    have hnotlast : ¬ k = m - 1 - 1 := by omega
    simp [hnle, hrange, hnotlast]
    rw [ih']
    have hck1_ne : ((contE m (k+1) : ℚ) ≠ 0) := by
      have hp := contE_pos m (k+1) hm (by omega) (by omega)
      positivity
    have hck2_ne : ((contE m (k+2) : ℚ) ≠ 0) := by
      have hp2 := contE_pos m (k+2) hm (by omega) (by omega)
      positivity
    have hden_ne : ((contE m (k+1) : ℚ) / (contE m (k+2) : ℚ)) ≠ 0 := by positivity
    have hrec : contE m k = ((k:ℕ):ℤ) * contE m (k+1) - ((k+1:ℕ):ℤ) * contE m (k+2) := contE_rec m k (by omega)
    rw [hrec]
    field_simp [hden_ne, hck1_ne, hck2_ne]
    norm_num

-- If a prime divisor of the raw numerator is larger than `m`, it cannot divide the denominator
-- continuant `contE m 3`.
lemma prime_not_dvd_contE_three (m p : ℕ) (hm3 : 3 ≤ m) (hp : p.Prime) (hpm : m < p)
    (hdiv : (p : ℤ) ∣ ((m:ℤ)^2 - 5)) : ¬ (p : ℤ) ∣ contE m 3 := by
  intro h3
  have hpz_ne0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_gt1 : 1 < p := hp.one_lt
  -- Propagate divisibility upward from `3` to `m`, contradicting `contE m m = -1`.
  have prop : ∀ k : ℕ, 3 ≤ k → k ≤ m → (p : ℤ) ∣ contE m k := by
    intro k hk3 hkm
    induction' h : k - 3 using Nat.strong_induction_on with d ih generalizing k
    by_cases hk_eq3 : k = 3
    · subst k; exact h3
    · have hk4 : 4 ≤ k := by omega
      have hkprev : 3 ≤ k-1 := by omega
      have hkprev_le : k-1 ≤ m-1 := by omega
      have hkprev_le_m : k-1 ≤ m := by omega
      have ihprev : (p : ℤ) ∣ contE m (k-1) := ih (k-1-3) (by omega) (k-1) hkprev hkprev_le_m (by omega)
      have hinv := contE_invariant m (k-1) (by omega) hkprev_le
      -- modulo p, invariant gives `(k-2) P_{k-1} - (k-1)(k-3) P_k = 0`.
      have hterm : (p : ℤ) ∣ ((k-1:ℕ):ℤ) * ((k-3:ℕ):ℤ) * contE m k := by
        -- rearrange from invariant and known divisibilities
        have hleft : (p : ℤ) ∣ (((k-2:ℕ):ℤ) * contE m (k-1)) := dvd_mul_of_dvd_right ihprev _
        have hx : (p : ℤ) ∣ (((k-2:ℕ):ℤ) * contE m (k-1) - ((k-1:ℕ):ℤ) * ((k-3:ℕ):ℤ) * contE m k) := by
          convert hdiv using 1
          rw [← hinv]
          have hA : ((k - 1 - 1 : ℕ) : ℤ) = ((k - 2 : ℕ) : ℤ) := by omega
          have hB : k - 1 + 1 = k := by omega
          have hC : ((k - 1 - 2 : ℕ) : ℤ) = ((k - 3 : ℕ) : ℤ) := by omega
          rw [hA, hB, hC]
        have := Int.dvd_sub hleft hx
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using this
      have hcop1 : IsCoprime (p : ℤ) ((k-1:ℕ):ℤ) := by
        have hkltp : k - 1 < p := by omega
        have hpos : 0 < k - 1 := by omega
        exact Int.isCoprime_iff_gcd_eq_one.mpr (by
          rw [Int.gcd_eq_natAbs]
          have hcop : Nat.Coprime p (k-1) := hp.coprime_iff_not_dvd.mpr (by
            intro hd
            have : p ≤ k - 1 := Nat.le_of_dvd (by omega) hd
            omega)
          exact_mod_cast hcop.gcd_eq_one)
      have hcop2 : IsCoprime (p : ℤ) ((k-3:ℕ):ℤ) := by
        have hz : k-3 ≠ 0 := by omega
        have hkltp : k - 3 < p := by omega
        exact Int.isCoprime_iff_gcd_eq_one.mpr (by
          rw [Int.gcd_eq_natAbs]
          have hcop : Nat.Coprime p (k-3) := hp.coprime_iff_not_dvd.mpr (by
            intro hd
            have : p ≤ k - 3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd
            omega)
          exact_mod_cast hcop.gcd_eq_one)
      have hterm' : (p : ℤ) ∣ ((k-1:ℕ):ℤ) * (((k-3:ℕ):ℤ) * contE m k) := by simpa [mul_assoc] using hterm
      have hmid : (p : ℤ) ∣ ((k-3:ℕ):ℤ) * contE m k := hcop1.dvd_of_dvd_mul_left hterm'
      exact hcop2.dvd_of_dvd_mul_left hmid
  have hpm_div := prop m hm3 le_rfl
  rw [contE_top] at hpm_div
  have hone : (p : ℤ) ∣ (1 : ℤ) := by
    simpa using (Int.dvd_neg.mpr hpm_div)
  have hnat : p ∣ 1 := by exact_mod_cast hone
  have hp_le1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hnat
  omega

lemma divisor_dvd_contE_three (m d : ℕ) (hd3 : 3 ≤ d) (hdm : d < m)
    (hdiv : (d : ℤ) ∣ ((m:ℤ)^2 - 5)) : (d : ℤ) ∣ contE m 3 := by
  have hdm1 : d ≤ m - 1 := by omega
  have hinv := contE_invariant m d (by omega : 2 ≤ d) hdm1
  have hd_term : (d : ℤ) ∣ ((d:ℕ):ℤ) * ((d-2:ℕ):ℤ) * contE m (d+1) := by
    simpa [mul_assoc] using (dvd_mul_right (d : ℤ) (((d-2:ℕ):ℤ) * contE m (d+1)))
  have hprod : (d : ℤ) ∣ ((d-1:ℕ):ℤ) * contE m d := by
    have hx : (d : ℤ) ∣ (((d-1:ℕ):ℤ) * contE m d - ((d:ℕ):ℤ) * ((d-2:ℕ):ℤ) * contE m (d+1)) := by
      simpa [hinv] using hdiv
    have := Int.dvd_add hx hd_term
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using this
  have hcop : IsCoprime (d : ℤ) ((d-1:ℕ):ℤ) := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_eq_natAbs]
      have hc : Nat.Coprime d (d-1) := by
        exact (Nat.coprime_self_sub_right (by omega : 1 ≤ d)).2 (Nat.coprime_one_right d)
      exact_mod_cast hc.gcd_eq_one)
  have hdPd : (d : ℤ) ∣ contE m d := hcop.dvd_of_dvd_mul_left hprod
  have prop : ∀ k : ℕ, 3 ≤ k → k ≤ d → (d : ℤ) ∣ contE m k := by
    intro k hk3 hkd
    induction' h : d - k using Nat.strong_induction_on with e ih generalizing k
    by_cases htop : k = d
    · subst k; exact hdPd
    · have hklt : k < d := by omega
      have hk1le : k+1 ≤ d := by omega
      have ih1 : (d : ℤ) ∣ contE m (k+1) := ih (d-(k+1)) (by omega) (k+1) (by omega) hk1le (by rfl)
      have hrec := contE_rec m k (by omega : k + 1 < m)
      rw [hrec]
      have hfirst : (d : ℤ) ∣ ((k:ℕ):ℤ) * contE m (k+1) := dvd_mul_of_dvd_right ih1 _
      by_cases hk1d : k + 1 = d
      · have hsecond : (d : ℤ) ∣ ((k+1:ℕ):ℤ) * contE m (k+2) := by
          rw [hk1d]
          exact dvd_mul_right (d : ℤ) _
        exact Int.dvd_sub hfirst hsecond
      · have hk2le : k+2 ≤ d := by omega
        have ih2 : (d : ℤ) ∣ contE m (k+2) := ih (d-(k+2)) (by omega) (k+2) (by omega) hk2le (by rfl)
        have hsecond : (d : ℤ) ∣ ((k+1:ℕ):ℤ) * contE m (k+2) := dvd_mul_of_dvd_right ih2 _
        exact Int.dvd_sub hfirst hsecond
  exact prop 3 (by norm_num) hd3

lemma nat_gcd_eq_of_prime_mul {p t den : ℕ} (hp : p.Prime) (htpos : 0 < t)
    (htden : t ∣ den) (hpden : ¬ p ∣ den) : Nat.gcd den (p * t) = t := by
  apply Nat.dvd_antisymm
  · obtain ⟨u, rfl⟩ := htden
    rw [mul_comm p t, Nat.gcd_mul_left]
    have hcop : Nat.Coprime u p := by
      exact (hp.coprime_iff_not_dvd.mpr (by
        intro hpu
        apply hpden
        exact dvd_mul_of_dvd_right hpu t)).symm
    rw [hcop.gcd_eq_one]
    simp
  · exact Nat.dvd_gcd htden (dvd_mul_left t p)

lemma rat_num_natAbs_prime_mul_div {p t den : ℕ} (hp : p.Prime) (htpos : 0 < t)
    (hdenpos : 0 < den) (htden : t ∣ den) (hpden : ¬ p ∣ den) :
    (((((p * t : ℕ) : ℤ) : ℚ) / (((den : ℕ) : ℤ) : ℚ)).num.natAbs = p) := by
  have hcop : Nat.Coprime p (den / t) := by
    exact hp.coprime_iff_not_dvd.mpr (by
      intro hpdt
      apply hpden
      obtain ⟨u, hu⟩ := htden
      subst den
      rw [Nat.mul_div_right u htpos] at hpdt
      exact dvd_mul_of_dvd_right hpdt t)
  have htden' : den = t * (den / t) := by exact (Nat.mul_div_cancel' htden).symm
  have hq : ((((p * t : ℕ) : ℤ) : ℚ) / (((den : ℕ) : ℤ) : ℚ)) = ((p : ℤ) : ℚ) / (((den / t : ℕ) : ℤ) : ℚ) := by
    rw [htden']
    have htq : (((t:ℕ):ℤ):ℚ) ≠ 0 := by positivity
    norm_num [Nat.cast_mul, Int.cast_mul]
    field_simp [htq]
  rw [hq]
  have hden_div_pos : 0 < ((den / t : ℕ) : ℤ) := by
    have : 0 < den / t := by
      obtain ⟨u, hu⟩ := htden
      subst den
      rw [Nat.mul_div_right u htpos]
      have hu_pos : 0 < u := by
        by_contra hz
        have : u = 0 := by omega
        subst u
        simp at hdenpos
      exact hu_pos
    exact_mod_cast this
  have hcop2 : Nat.Coprime ((p:ℤ).natAbs) ((((den/t:ℕ):ℤ).natAbs)) := by
    simpa using hcop
  have hnum := Rat.num_div_eq_of_coprime (a := (p:ℤ)) (b := ((den/t:ℕ):ℤ)) hden_div_pos hcop2
  rw [hnum]
  simp

noncomputable def Atest (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

lemma t_ne_two_of_prime_root {m p t : ℕ} (hp : p.Prime) (hm4 : 4 ≤ m)
    (hraw : m*m - 5 = p * t) : t ≠ 2 := by
  intro ht
  subst t
  have hp2 : p ≠ 2 := by
    intro h; subst p
    have hs : m*m = 9 := by omega
    nlinarith
  have hpodd : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).2 hp2
  have hmpar : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  rcases hmpar with hme | hmo
  · have hm2 : (m*m) % 2 = 0 := by rw [Nat.mul_mod, hme]
    have hleft : (m*m - 5) % 2 = 1 := by omega
    have hright : (p*2) % 2 = 0 := by omega
    rw [hraw, hright] at hleft
    norm_num at hleft
  · have h4cases : m % 4 = 1 ∨ m % 4 = 3 := by omega
    have hsq4 : (m*m) % 4 = 1 := by
      rcases h4cases with h1 | h3
      · rw [Nat.mul_mod, h1]
      · rw [Nat.mul_mod, h3]
    have hleft : (m*m - 5) % 4 = 0 := by omega
    have hp4cases : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hright : (p*2) % 4 = 2 := by
      rcases hp4cases with h1 | h3
      · rw [Nat.mul_mod, h1]
      · rw [Nat.mul_mod, h3]
    rw [hraw, hright] at hleft
    norm_num at hleft

lemma Atest_eq_of_root (m p : ℕ) (hp : p.Prime) (hm4 : 4 ≤ m) (hmp : m < p)
    (hmod : m*m ≡ 5 [MOD p]) : Atest (m-1) = p := by
  have hmpos : 0 < m := by omega
  have hnnot : ¬ m - 1 ≤ 2 := by omega
  simp [Atest, hnnot]
  have hcf := cf_eq_contE m 2 hm4 (by norm_num) (by omega : 2 ≤ m - 2)
  rw [hcf]
  have hinv2 := contE_invariant m 2 (by norm_num) (by omega : 2 ≤ m - 1)
  have hP2 : contE m 2 = ((m:ℤ)^2 - 5) := by
    simpa using hinv2
  rw [hP2]
  have hraw_pos_nat : 0 < m*m - 5 := by
    have : 16 ≤ m*m := by nlinarith
    omega
  have hpdvd_nat : p ∣ m*m - 5 := by
    have hs : 5 ≡ m*m [MOD p] := hmod.symm
    exact (Nat.modEq_iff_dvd' (by nlinarith : 5 ≤ m*m)).1 hs
  let t := (m*m - 5) / p
  have hraw_eq : m*m - 5 = p * t := by
    unfold t
    rw [mul_comm p ((m*m - 5) / p)]
    exact (Nat.div_mul_cancel hpdvd_nat).symm
  have htpos : 0 < t := by
    unfold t
    exact Nat.div_pos (Nat.le_of_dvd hraw_pos_nat hpdvd_nat) hp.pos
  have ht_lt_m : t < m := by
    have hp_pos : 0 < p := hp.pos
    have hmm_lt_mp : m*m < m*p := (Nat.mul_lt_mul_left hmpos).2 hmp
    have hmm_lt_pm : m*m < p*m := by simpa [mul_comm] using hmm_lt_mp
    have hineq : p * t < p * m := by
      rw [← hraw_eq]
      omega
    exact (Nat.mul_lt_mul_left hp_pos).1 hineq
  have hdenposZ := contE_pos m 3 hm4 (by norm_num) (by omega : 3 ≤ m - 1)
  let denNat := (contE m 3).natAbs
  have hdenpos : 0 < denNat := by
    have : (0:ℤ) < contE m 3 := hdenposZ
    exact Int.natAbs_pos.mpr (ne_of_gt this)
  have hden_cast : (denNat : ℤ) = contE m 3 := Int.natAbs_of_nonneg (le_of_lt hdenposZ)
  have htden : t ∣ denNat := by
    by_cases ht3 : 3 ≤ t
    · have htdvdZ : (t : ℤ) ∣ contE m 3 := by
        apply divisor_dvd_contE_three m t ht3 ht_lt_m
        have : (t : ℤ) ∣ ((m:ℤ)^2 - 5) := by
          use (p:ℤ)
          have hz : ((m:ℤ)^2 - 5) = ((p*t:ℕ):ℤ) := by
            rw [← hraw_eq]
            have h5le : 5 ≤ m*m := by omega
            rw [Nat.cast_sub h5le, Nat.cast_mul]
            ring
          rw [hz]
          norm_num [Nat.cast_mul, Int.cast_mul]
          ring
        exact this
      rw [← hden_cast] at htdvdZ
      exact_mod_cast htdvdZ
    · have ht_le2 : t ≤ 2 := by omega
      have htne2 : t ≠ 2 := t_ne_two_of_prime_root hp hm4 hraw_eq
      have ht_eq1 : t = 1 := by omega
      rw [ht_eq1]
      exact one_dvd denNat
  have hpden : ¬ p ∣ denNat := by
    intro hpd
    have hpdZ : (p : ℤ) ∣ contE m 3 := by
      rw [← hden_cast]
      exact_mod_cast hpd
    exact prime_not_dvd_contE_three m p (by omega : 3 ≤ m) hp hmp (by
      have hrawZ : ((m*m - 5 : ℕ) : ℤ) = (m:ℤ)^2 - 5 := by
        have h5le : 5 ≤ m*m := by omega
        rw [Nat.cast_sub h5le, Nat.cast_mul]
        ring
      have : (p : ℤ) ∣ ((m*m - 5 : ℕ) : ℤ) := by exact_mod_cast hpdvd_nat
      rwa [hrawZ] at this) hpdZ
  have hnum := rat_num_natAbs_prime_mul_div hp htpos hdenpos htden hpden
  -- identify the rational with `(p*t)/denNat`.
  have hraw_cast : ((m:ℤ)^2 - 5) = ((p*t:ℕ):ℤ) := by
    rw [← hraw_eq]
    have h5le : 5 ≤ m*m := by omega
    rw [Nat.cast_sub h5le, Nat.cast_mul]
    ring
  have hden_rat : ((contE m 3 : ℚ)) = (((denNat:ℕ):ℤ):ℚ) := by rw [← hden_cast]
  rw [hraw_cast, hden_rat]
  simpa [Nat.cast_mul, Int.cast_mul] using hnum
