import FormalConjectures.Util.ProblemImports

open Nat Set Classical

/--
A282779: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that $\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def A282779 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

noncomputable def midUnit (p T : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (p - 1), (p.choose (i+1) / p) * T^i

lemma midUnit_eq_one_add (p T : ℕ) (hp : Nat.Prime p) :
    midUnit p T = 1 + T * (∑ i ∈ Finset.range (p - 2), (p.choose (i+2) / p) * T^i) := by
  unfold midUnit
  have hp2 : 2 ≤ p := hp.two_le
  -- split off i=0 from range (p-1)
  rw [show p - 1 = (p - 2) + 1 by omega]
  rw [Finset.sum_range_succ']
  simp [Nat.choose_one_right, Nat.div_self hp.pos]
  rw [add_comm]
  rw [Finset.mul_sum]
  apply congrArg (fun x => 1 + x)
  apply Finset.sum_congr rfl
  intro i hi
  have : T * ((p.choose (i + 2) / p) * T ^ i) = (p.choose (i + 2) / p) * T ^ (i + 1) := by
    ring
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this.symm

lemma binom_prime_identity (p T : ℕ) (hp : Nat.Prime p) :
    (T + 1)^p = T^p + 1 + p*T*midUnit p T := by
  unfold midUnit
  rw [add_pow]
  rw [Finset.sum_range_succ]
  simp [Nat.choose_self]
  have hp_pos : 0 < p := hp.pos
  rw [show Finset.range p = Finset.range ((p - 1) + 1) by congr; omega]
  rw [Finset.sum_range_succ']
  simp [Nat.choose_zero_right]
  have hmiddle :
      (∑ i ∈ Finset.range (p - 1), T ^ (i + 1) * p.choose (i + 1)) =
        p * T * ∑ i ∈ Finset.range (p - 1), (p.choose (i + 1) / p) * T^i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : 1 + i < p := by
      have : i < p - 1 := (Finset.mem_range.mp hi)
      omega
    have hi_ne : 1 + i ≠ 0 := by omega
    have hdiv : p * (p.choose (1 + i) / p) = p.choose (1 + i) := Nat.mul_div_cancel' (hp.dvd_choose_self hi_ne hi_lt)
    rw [show i + 1 = 1 + i by omega]
    conv_lhs => rw [← hdiv]
    ring_nf
  rw [hmiddle]
  ring

lemma midUnit_coprime (p T : ℕ) (hp : Nat.Prime p) :
    T.Coprime (midUnit p T) := by
  rw [midUnit_eq_one_add p T hp]
  rw [show 1 + T * (∑ i ∈ Finset.range (p - 2), p.choose (i + 2) / p * T ^ i) =
      1 + T * (∑ i ∈ Finset.range (p - 2), p.choose (i + 2) / p * T ^ i) by rfl]
  exact (Nat.coprime_add_mul_left_right T 1 (∑ i ∈ Finset.range (p - 2), p.choose (i + 2) / p * T ^ i)).mpr (Nat.coprime_one_right T)

lemma necessary_p_mul_T {p n T : ℕ} (hp : Nat.Prime p)
    (hprop : ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n) :
    n ∣ p * T := by
  have h0mod : T ^ p % n = 0 := by
    simpa [hp.ne_zero] using hprop 0
  have hTp : n ∣ T ^ p := Nat.dvd_iff_mod_eq_zero.mpr h0mod
  have h0me : T ^ p ≡ 0 [MOD n] := by
    change T ^ p % n = 0 % n
    simp [h0mod]
  have h1me : (T + 1) ^ p ≡ 1 [MOD n] := by
    simpa [add_comm, hp.ne_zero] using hprop 1
  let U := midUnit p T
  have hid : (T + 1)^p = T^p + 1 + p*T*U := by
    simpa [U] using binom_prime_identity p T hp
  have h1me' : T^p + 1 + p*T*U ≡ 1 [MOD n] := by
    rw [← hid]
    exact h1me
  have hbase : T^p + 1 ≡ 0 + 1 [MOD n] := Nat.ModEq.add h0me (Nat.ModEq.refl 1)
  have h2 : T^p + 1 + p*T*U ≡ 0 + 1 + 0 [MOD n] := by
    simpa using h1me'
  have hpTU_me : p*T*U ≡ 0 [MOD n] := Nat.ModEq.add_left_cancel hbase h2
  have hpTU_dvd : n ∣ p*T*U := by
    have hz : 0 ≡ p*T*U [MOD n] := hpTU_me.symm
    exact (Nat.modEq_iff_dvd' (Nat.zero_le _)).mp hz
  have hcopTU : (T^p).Coprime U := (midUnit_coprime p T hp).pow_left p
  have hcopnU : n.Coprime U := Nat.Coprime.coprime_dvd_left hTp hcopTU
  exact hcopnU.dvd_of_dvd_mul_right hpTU_dvd

lemma sufficient_period_property {p n T : ℕ} (hp : Nat.Prime p)
    (hTp : n ∣ T^p) (hpT : n ∣ p*T) :
    ∀ k : ℕ, (k + T)^p % n = k^p % n := by
  intro k
  change (k + T)^p ≡ k^p [MOD n]
  rw [add_pow]
  let term : ℕ → ℕ := fun m => k^m * T^(p-m) * p.choose m
  let g : ℕ → ℕ := fun m => if m = p then k^p else 0
  have hsum : (∑ m ∈ Finset.range (p + 1), term m) ≡ (∑ m ∈ Finset.range (p + 1), g m) [MOD n] := by
    apply Nat.ModEq.sum
    intro m hm
    by_cases hmp : m = p
    · subst m
      dsimp [term, g]
      simpa [Nat.choose_self] using (Nat.ModEq.refl (k ^ p) : k ^ p ≡ k ^ p [MOD n])
    · have hmle : m ≤ p := by
        have : m < p + 1 := Finset.mem_range.mp hm
        omega
      have hmlt : m < p := Nat.lt_of_le_of_ne hmle hmp
      have hterm_dvd : n ∣ term m := by
        by_cases hm0 : m = 0
        · subst hm0
          have : term 0 = T^p := by
            simp [term, Nat.choose_zero_right]
          simpa [this] using hTp
        · have hchoose : p ∣ p.choose m := hp.dvd_choose_self hm0 hmlt
          have hTdvd : T ∣ T^(p-m) := by
            have hpos : 0 < p - m := by omega
            refine ⟨T^(p-m-1), ?_⟩
            rw [show p - m = (p - m - 1) + 1 by omega, Nat.pow_succ']
            simp
          obtain ⟨a, ha⟩ := hchoose
          obtain ⟨b, hb⟩ := hTdvd
          have hpT_dvd_term : p*T ∣ term m := by
            refine ⟨k^m * b * a, ?_⟩
            dsimp [term]
            rw [ha, hb]
            ring
          exact hpT.trans hpT_dvd_term
      change term m % n = g m % n
      simp [g, hmp, Nat.dvd_iff_mod_eq_zero.mp hterm_dvd]
  have hgsum : (∑ m ∈ Finset.range (p + 1), g m) = k^p := by
    simp [g]
  simpa [term, g, hgsum] using hsum


/--
oeis_282779_conjecture_0: Conjecture: let a_p(n) be the length of the period of the sequence k^p mod n where p is a prime,
then a_p(n) = n/p if n == 0 (mod p^2) else a_p(n) = n.
-/
theorem oeis_282779_conjecture_0 (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
    period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
  let a := if p ^ 2 ∣ n then n / p else n
  let S : Set ℕ := { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }
  have hpred_mem : a ∈ S := by
    dsimp [a, S]
    by_cases hcase : p ^ 2 ∣ n
    · rw [if_pos hcase]
      have hpdvdn : p ∣ n := by
        exact (dvd_trans (by exact ⟨p, by ring⟩) hcase)
      have hn_eq : p * (n / p) = n := Nat.mul_div_cancel' hpdvdn
      have hp_dvd_div : p ∣ n / p := by
        rw [Nat.dvd_div_iff_mul_dvd hpdvdn]
        simpa [pow_two, mul_comm] using hcase
      have hpos_div : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpdvdn) hp.pos
      constructor
      · exact hpos_div
      · apply sufficient_period_property hp
        · have hndvd_sq : n ∣ (n / p)^2 := by
            conv_lhs => rw [← hn_eq]
            simpa [pow_two] using Nat.mul_dvd_mul hp_dvd_div (dvd_refl (n / p))
          exact hndvd_sq.trans (Nat.pow_dvd_pow (n / p) hp.two_le)
        · simp [hn_eq]
    · rw [if_neg hcase]
      constructor
      · exact hn
      · apply sufficient_period_property hp
        · simpa using (Nat.pow_dvd_pow n hp.pos : n ^ 1 ∣ n ^ p)
        · exact ⟨p, by ring⟩
  have hlower : ∀ T ∈ S, a ≤ T := by
    intro T hT
    rcases hT with ⟨hTpos, hprop⟩
    have hpTdiv : n ∣ p*T := necessary_p_mul_T hp hprop
    have h0mod : T ^ p % n = 0 := by simpa [hp.ne_zero] using hprop 0
    have hTpow : n ∣ T^p := Nat.dvd_iff_mod_eq_zero.mpr h0mod
    dsimp [a]
    by_cases hcase : p ^ 2 ∣ n
    · rw [if_pos hcase]
      have hpdvdn : p ∣ n := dvd_trans (by exact ⟨p, by ring⟩) hcase
      have hn_eq : p * (n / p) = n := Nat.mul_div_cancel' hpdvdn
      have hdivdvdT : n / p ∣ T := by
        apply Nat.dvd_of_mul_dvd_mul_left hp.pos
        rw [hn_eq]
        exact hpTdiv
      exact Nat.le_of_dvd hTpos hdivdvdT
    · rw [if_neg hcase]
      have hndvdT : n ∣ T := by
        by_cases hpdvdn : p ∣ n
        · have hn_eq : p * (n / p) = n := Nat.mul_div_cancel' hpdvdn
          have hdivdvdT : n / p ∣ T := by
            apply Nat.dvd_of_mul_dvd_mul_left hp.pos
            rw [hn_eq]
            exact hpTdiv
          have hpdvdT : p ∣ T := by
            apply hp.dvd_of_dvd_pow
            exact hpdvdn.trans hTpow
          have hnot_p_div_div : ¬ p ∣ n / p := by
            intro hpdiv
            apply hcase
            rw [pow_two]
            rw [← Nat.dvd_div_iff_mul_dvd hpdvdn] 
            simpa [mul_comm] using hpdiv
          have hcop : p.Coprime (n / p) := (hp.coprime_iff_not_dvd).mpr hnot_p_div_div
          have hmul : p * (n / p) ∣ T := hcop.mul_dvd_of_dvd_of_dvd hpdvdT hdivdvdT
          simpa [hn_eq] using hmul
        · have hcop : n.Coprime p := ((hp.coprime_iff_not_dvd).mpr hpdvdn).symm
          exact hcop.dvd_of_dvd_mul_left hpTdiv
      exact Nat.le_of_dvd hTpos hndvdT
      
  unfold period_of_power_mod
  simp [Nat.ne_of_gt hn]
  change sInf S = a
  apply le_antisymm
  · exact csInf_le ⟨0, by intro y hy; exact Nat.zero_le y⟩ hpred_mem
  · exact hlower (sInf S) (Nat.sInf_mem ⟨a, hpred_mem⟩)

