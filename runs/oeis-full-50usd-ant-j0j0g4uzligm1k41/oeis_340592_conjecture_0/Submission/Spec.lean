import FormalConjectures.Util.ProblemImports

open Nat List

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/--
A340592: $a(n)$ is the concatenation of the prime factors (with multiplicity) of $n$ modulo $n$.
The prime factors are taken in non-decreasing order as given by $n.\operatorname{primeFactorsList}$.
-/
def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors_list := n.primeFactorsList

    -- Calculates 10^(number of decimal digits of k)
    let pow10_len (k : ℕ) : ℕ := 10 ^ (Nat.digits 10 k).length

    -- The concatenation operation: acc || factor
    let concat_op (acc factor : ℕ) : ℕ :=
      acc * pow10_len factor + factor

    (factors_list.foldl concat_op 0) % n

/-- The property of being composite (n > 1 and not prime) -/
def Nat.composite (n : ℕ) : Prop := ¬ (Nat.Prime n) ∧ 1 < n

/- Auxiliary computable machinery -/

/-- Kernel-computable prime factorization by trial division with fuel. -/
def facAux : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | (fuel+1), n, d =>
      if n < 2 then []
      else if n % d = 0 then d :: facAux fuel (n / d) d
      else if d * d > n then [n]
      else facAux fuel n (d + 1)

def factorize (n : ℕ) : List ℕ := facAux (2*n) n 2

def digLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (fuel+1), k => if k = 0 then 0 else 1 + digLen fuel (k/10)

/-- Kernel-computable version of `a`. -/
def a' (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let pow10_len (k : ℕ) : ℕ := 10 ^ (digLen (k+1) k)
    let concat_op (acc factor : ℕ) : ℕ := acc * pow10_len factor + factor
    ((factorize n).foldl concat_op 0) % n

/-- Divide-and-conquer boolean range checker (logarithmic recursion depth). -/
def checkRange (P : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, lo, len => match len with | 0 => true | _ => P lo
  | fuel+1, lo, len =>
      match len with
      | 0 => true
      | 1 => P lo
      | (l+2) =>
          let m := (l+2)/2
          checkRange P fuel lo m && checkRange P fuel (lo+m) ((l+2)-m)

def Pcheck (m : ℕ) : Bool := Nat.ble (factorize m).length 1 || Nat.ble 1 (a' m)

/- Correctness of the machinery -/

theorem prime_of_min {n d : ℕ} (h1 : 2 ≤ d) (hdvd : d ∣ n)
    (hdiv : ∀ m, 2 ≤ m → m ∣ n → d ≤ m) : d.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨h1, ?_⟩
  intro m hm hmd
  by_contra hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hmd
    omega
  have : 2 ≤ m := by omega
  have : d ≤ m := hdiv m this (hmd.trans hdvd)
  omega

theorem prime_of_nosmall {n d : ℕ} (hn : 2 ≤ n)
    (hdiv : ∀ m, 2 ≤ m → m ∣ n → d ≤ m) (hsq : n < d * d) : n.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hn, ?_⟩
  intro m hm hmd
  by_contra hne
  have hm0 : m ≠ 0 := by
    rintro rfl; simp at hmd; omega
  have hm2 : 2 ≤ m := by omega
  have hdm : d ≤ m := hdiv m hm2 hmd
  obtain ⟨c, hc⟩ := hmd
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c <;> omega
    · exact h
  have hcd : d ≤ c := by
    apply hdiv c hc2
    exact ⟨m, by rw [hc]; ring⟩
  have : d * d ≤ m * c := Nat.mul_le_mul hdm hcd
  omega

theorem facAux_spec : ∀ (fuel n d : ℕ), 2 ≤ d → 1 ≤ n →
    (∀ m, 2 ≤ m → m ∣ n → d ≤ m) → 2 * n + 2 - d ≤ fuel →
    List.prod (facAux fuel n d) = n ∧
    (∀ p ∈ facAux fuel n d, p.Prime) ∧
    List.Pairwise (· ≤ ·) (facAux fuel n d) ∧
    (∀ p ∈ facAux fuel n d, d ≤ p) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n d h1 hn hdiv hfuel
    simp only [facAux]
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge n 2 with h | h
      · omega
      · have := hdiv n h (dvd_refl n); omega
    subst hn1
    refine ⟨by simp, ?_, by simp, ?_⟩ <;> simp
  | succ f ih =>
    intro n d h1 hn hdiv hfuel
    rw [facAux]
    split_ifs with hlt hmod hsq
    · have hn1 : n = 1 := by omega
      subst hn1
      refine ⟨by simp, ?_, by simp, ?_⟩ <;> simp
    · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
      have hnge : 2 ≤ n := by omega
      have hdn : d ≤ n := hdiv n hnge (dvd_refl n)
      have hq1 : 1 ≤ n / d := by
        rcases Nat.eq_zero_or_pos (n/d) with h | h
        · exfalso
          have : n = 0 := by
            have := Nat.div_mul_cancel hdvd
            rw [h] at this; simpa using this.symm
          omega
        · exact h
      have hprimeD : d.Prime := prime_of_min h1 hdvd hdiv
      have hdiv' : ∀ m, 2 ≤ m → m ∣ (n/d) → d ≤ m := by
        intro m hm hmd
        exact hdiv m hm (hmd.trans (Nat.div_dvd_of_dvd hdvd))
      have hdle2 : 2 * (n / d) ≤ n := by
        have : n / d ≤ n / 2 := Nat.div_le_div_left h1 (by norm_num)
        omega
      have hfuel' : 2 * (n/d) + 2 - d ≤ f := by omega
      obtain ⟨hprod, hpr, hsort, hbd⟩ := ih (n/d) d h1 hq1 hdiv' hfuel'
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.prod_cons, hprod, Nat.mul_div_cancel' hdvd]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hprimeD
        · exact hpr p hp
      · rw [List.pairwise_cons]
        exact ⟨fun a ha => hbd a ha, hsort⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact le_refl _
        · exact hbd p hp
    · have hnge : 2 ≤ n := by omega
      have hprime : n.Prime := prime_of_nosmall hnge hdiv (by omega)
      have hdn : d ≤ n := hdiv n hnge (dvd_refl n)
      refine ⟨by simp, ?_, by simp, ?_⟩
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hprime
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hdn
    · have hnge : 2 ≤ n := by omega
      have hdn : d ≤ n := hdiv n hnge (dvd_refl n)
      have hdiv' : ∀ m, 2 ≤ m → m ∣ n → d + 1 ≤ m := by
        intro m hm hmd
        have hdm : d ≤ m := hdiv m hm hmd
        rcases Nat.lt_or_ge d m with h | h
        · omega
        · have hmd2 : d ∣ n := by
            have hmm : m = d := by omega
            rwa [hmm] at hmd
          exact absurd (Nat.dvd_iff_mod_eq_zero.mp hmd2) hmod
      have hfuel' : 2 * n + 2 - (d+1) ≤ f := by omega
      obtain ⟨hprod, hpr, hsort, hbd⟩ := ih n (d+1) (by omega) hn hdiv' hfuel'
      refine ⟨hprod, hpr, hsort, ?_⟩
      intro p hp
      exact le_trans (by omega) (hbd p hp)

theorem hfac (n : ℕ) : factorize n = n.primeFactorsList := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [factorize, facAux]
  · unfold factorize
    obtain ⟨hprod, hpr, hsort, _⟩ :=
      facAux_spec (2*n) n 2 (le_refl 2) hpos (fun m hm _ => hm) (by omega)
    have hperm : facAux (2*n) n 2 ~ n.primeFactorsList :=
      Nat.primeFactorsList_unique hprod hpr
    exact List.Perm.eq_of_pairwise' hsort (Nat.primeFactorsList_sorted n).pairwise hperm

theorem digLen_eq : ∀ (fuel k : ℕ), k + 1 ≤ fuel → digLen fuel k = (Nat.digits 10 k).length := by
  intro fuel
  induction fuel with
  | zero => intro k hk; omega
  | succ f ih =>
    intro k hk
    rw [digLen]
    split_ifs with hk0
    · subst hk0; simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      rw [Nat.digits_def' (by norm_num : 1 < 10) hkpos, List.length_cons]
      have : k / 10 + 1 ≤ f := by
        have h2 : k / 10 < k := Nat.div_lt_self hkpos (by norm_num)
        omega
      rw [ih (k/10) this]
      omega

theorem a_eq (n : ℕ) : a n = a' n := by
  unfold a a'
  split_ifs with h
  · rfl
  · dsimp only
    congr 1
    rw [hfac n]
    apply List.foldl_ext
    intro acc factor hf
    rw [digLen_eq (factor+1) factor (le_refl _)]

theorem checkRange_correct (P : ℕ → Bool) : ∀ (fuel lo len : ℕ), len ≤ 2^fuel →
    checkRange P fuel lo len = true → ∀ i, lo ≤ i → i < lo + len → P i = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo len hlen hchk i hi1 hi2
    simp only [pow_zero] at hlen
    interval_cases len
    · omega
    · simp only [checkRange] at hchk
      have : i = lo := by omega
      subst this; exact hchk
  | succ f ih =>
    intro lo len hlen hchk i hi1 hi2
    match len, hchk, hi2 with
    | 0, _, hi2 => omega
    | 1, hchk, hi2 =>
        simp only [checkRange] at hchk
        have : i = lo := by omega
        subst this; exact hchk
    | (l+2), hchk, hi2 =>
        rw [checkRange, Bool.and_eq_true] at hchk
        obtain ⟨hL, hR⟩ := hchk
        set m := (l+2)/2 with hm
        have hpow : (2:ℕ)^(f+1) = 2 * 2^f := by rw [pow_succ]; ring
        have hmle : m ≤ 2^f := by rw [hm]; omega
        have hrle : (l+2) - m ≤ 2^f := by rw [hm]; omega
        rcases Nat.lt_or_ge i (lo + m) with hlt | hge
        · exact ih lo m hmle hL i hi1 hlt
        · exact ih (lo+m) ((l+2)-m) hrle hR i hge (by omega)

theorem composite_len (n : ℕ) (hnp : ¬ n.Prime) (h1n : 1 < n) :
    2 ≤ n.primeFactorsList.length := by
  have hne : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).mpr h1n
  rcases hL : n.primeFactorsList with _ | ⟨p, tl⟩
  · exact absurd hL hne
  · rcases tl with _ | ⟨q, tl2⟩
    · exfalso
      have hp : p.Prime := by
        apply Nat.prime_of_mem_primeFactorsList (n := n); rw [hL]; simp
      have hprod : (n.primeFactorsList).prod = n := Nat.prod_primeFactorsList (by omega)
      rw [hL, List.prod_singleton] at hprod
      exact hnp (hprod ▸ hp)
    · simp

/- Bounded range verification (kernel-checked) -/

theorem rangeChunk0 : checkRange Pcheck 10 0 1000 = true := by decide +kernel
theorem rangeChunk1 : checkRange Pcheck 10 1000 1000 = true := by decide +kernel
theorem rangeChunk2 : checkRange Pcheck 10 2000 1000 = true := by decide +kernel
theorem rangeChunk3 : checkRange Pcheck 10 3000 1000 = true := by decide +kernel
theorem rangeChunk4 : checkRange Pcheck 10 4000 1000 = true := by decide +kernel
theorem rangeChunk5 : checkRange Pcheck 10 5000 1000 = true := by decide +kernel
theorem rangeChunk6 : checkRange Pcheck 10 6000 1000 = true := by decide +kernel
theorem rangeChunk7 : checkRange Pcheck 10 7000 1000 = true := by decide +kernel
theorem rangeChunk8 : checkRange Pcheck 10 8000 1000 = true := by decide +kernel
theorem rangeChunk9 : checkRange Pcheck 10 9000 1000 = true := by decide +kernel
theorem rangeChunk10 : checkRange Pcheck 10 10000 1000 = true := by decide +kernel
theorem rangeChunk11 : checkRange Pcheck 10 11000 1000 = true := by decide +kernel
theorem rangeChunk12 : checkRange Pcheck 10 12000 1000 = true := by decide +kernel
theorem rangeChunk13 : checkRange Pcheck 10 13000 1000 = true := by decide +kernel
theorem rangeChunk14 : checkRange Pcheck 10 14000 1000 = true := by decide +kernel
theorem rangeChunk15 : checkRange Pcheck 10 15000 1000 = true := by decide +kernel
theorem rangeChunk16 : checkRange Pcheck 10 16000 1000 = true := by decide +kernel
theorem rangeChunk17 : checkRange Pcheck 10 17000 1000 = true := by decide +kernel
theorem rangeChunk18 : checkRange Pcheck 10 18000 1000 = true := by decide +kernel
theorem rangeChunk19 : checkRange Pcheck 10 19000 1000 = true := by decide +kernel
theorem rangeChunk20 : checkRange Pcheck 10 20000 1000 = true := by decide +kernel
theorem rangeChunk21 : checkRange Pcheck 10 21000 1000 = true := by decide +kernel
theorem rangeChunk22 : checkRange Pcheck 10 22000 1000 = true := by decide +kernel
theorem rangeChunk23 : checkRange Pcheck 10 23000 1000 = true := by decide +kernel
theorem rangeChunk24 : checkRange Pcheck 10 24000 1000 = true := by decide +kernel
theorem rangeChunk25 : checkRange Pcheck 10 25000 1000 = true := by decide +kernel
theorem rangeChunk26 : checkRange Pcheck 10 26000 1000 = true := by decide +kernel
theorem rangeChunk27 : checkRange Pcheck 10 27000 1000 = true := by decide +kernel
theorem rangeChunk28 : checkRange Pcheck 10 28000 749 = true := by decide +kernel

theorem main_range : ∀ m, m < 28749 → Pcheck m = true := by
  have c0 := checkRange_correct Pcheck 10 0 1000 (by norm_num) rangeChunk0
  have c1 := checkRange_correct Pcheck 10 1000 1000 (by norm_num) rangeChunk1
  have c2 := checkRange_correct Pcheck 10 2000 1000 (by norm_num) rangeChunk2
  have c3 := checkRange_correct Pcheck 10 3000 1000 (by norm_num) rangeChunk3
  have c4 := checkRange_correct Pcheck 10 4000 1000 (by norm_num) rangeChunk4
  have c5 := checkRange_correct Pcheck 10 5000 1000 (by norm_num) rangeChunk5
  have c6 := checkRange_correct Pcheck 10 6000 1000 (by norm_num) rangeChunk6
  have c7 := checkRange_correct Pcheck 10 7000 1000 (by norm_num) rangeChunk7
  have c8 := checkRange_correct Pcheck 10 8000 1000 (by norm_num) rangeChunk8
  have c9 := checkRange_correct Pcheck 10 9000 1000 (by norm_num) rangeChunk9
  have c10 := checkRange_correct Pcheck 10 10000 1000 (by norm_num) rangeChunk10
  have c11 := checkRange_correct Pcheck 10 11000 1000 (by norm_num) rangeChunk11
  have c12 := checkRange_correct Pcheck 10 12000 1000 (by norm_num) rangeChunk12
  have c13 := checkRange_correct Pcheck 10 13000 1000 (by norm_num) rangeChunk13
  have c14 := checkRange_correct Pcheck 10 14000 1000 (by norm_num) rangeChunk14
  have c15 := checkRange_correct Pcheck 10 15000 1000 (by norm_num) rangeChunk15
  have c16 := checkRange_correct Pcheck 10 16000 1000 (by norm_num) rangeChunk16
  have c17 := checkRange_correct Pcheck 10 17000 1000 (by norm_num) rangeChunk17
  have c18 := checkRange_correct Pcheck 10 18000 1000 (by norm_num) rangeChunk18
  have c19 := checkRange_correct Pcheck 10 19000 1000 (by norm_num) rangeChunk19
  have c20 := checkRange_correct Pcheck 10 20000 1000 (by norm_num) rangeChunk20
  have c21 := checkRange_correct Pcheck 10 21000 1000 (by norm_num) rangeChunk21
  have c22 := checkRange_correct Pcheck 10 22000 1000 (by norm_num) rangeChunk22
  have c23 := checkRange_correct Pcheck 10 23000 1000 (by norm_num) rangeChunk23
  have c24 := checkRange_correct Pcheck 10 24000 1000 (by norm_num) rangeChunk24
  have c25 := checkRange_correct Pcheck 10 25000 1000 (by norm_num) rangeChunk25
  have c26 := checkRange_correct Pcheck 10 26000 1000 (by norm_num) rangeChunk26
  have c27 := checkRange_correct Pcheck 10 27000 1000 (by norm_num) rangeChunk27
  have c28 := checkRange_correct Pcheck 10 28000 749 (by norm_num) rangeChunk28
  intro m hm
  rcases Nat.lt_or_ge m 1000 with h0 | h0
  · exact c0 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 2000 with h1 | h1
  · exact c1 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 3000 with h2 | h2
  · exact c2 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 4000 with h3 | h3
  · exact c3 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 5000 with h4 | h4
  · exact c4 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 6000 with h5 | h5
  · exact c5 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 7000 with h6 | h6
  · exact c6 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 8000 with h7 | h7
  · exact c7 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 9000 with h8 | h8
  · exact c8 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 10000 with h9 | h9
  · exact c9 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 11000 with h10 | h10
  · exact c10 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 12000 with h11 | h11
  · exact c11 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 13000 with h12 | h12
  · exact c12 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 14000 with h13 | h13
  · exact c13 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 15000 with h14 | h14
  · exact c14 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 16000 with h15 | h15
  · exact c15 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 17000 with h16 | h16
  · exact c16 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 18000 with h17 | h17
  · exact c17 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 19000 with h18 | h18
  · exact c18 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 20000 with h19 | h19
  · exact c19 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 21000 with h20 | h20
  · exact c20 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 22000 with h21 | h21
  · exact c21 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 23000 with h22 | h22
  · exact c22 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 24000 with h23 | h23
  · exact c23 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 25000 with h24 | h24
  · exact c24 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 26000 with h25 | h25
  · exact c25 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 27000 with h26 | h26
  · exact c26 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 28000 with h27 | h27
  · exact c27 m (by omega) (by omega)
  exact c28 m (by omega) (by omega)

/--
The first composite n for which a(n)=0 is 28749. Are there others?
-/
theorem oeis_340592_conjecture_0 :
  (Nat.composite 28749 ∧ a 28749 = 0) ∧
  (∀ n : ℕ, Nat.composite n ∧ n < 28749 → a n ≠ 0) :=
by
  refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · rw [a_eq]; decide +kernel
  · rintro n ⟨⟨hnp, h1n⟩, hlt⟩
    rw [a_eq]
    have hlen : 2 ≤ (factorize n).length := by
      rw [hfac n]; exact composite_len n hnp h1n
    have hP := main_range n hlt
    simp only [Pcheck, Bool.or_eq_true, Nat.ble_eq] at hP
    rcases hP with h | h
    · omega
    · omega
