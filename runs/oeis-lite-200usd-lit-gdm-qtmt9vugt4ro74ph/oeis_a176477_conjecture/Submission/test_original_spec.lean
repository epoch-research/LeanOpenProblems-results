import FormalConjectures.Util.ProblemImports

open Nat
open Classical

private lemma no_pow2_3 (m : ℕ) (h : 3 = 2^m) : False := by
  rcases m with _ | _ | m_prime
  · omega
  · omega
  · have : 2^(m_prime + 2) = 2^m_prime * 4 := by ring
    omega

private lemma no_pow2_5 (m : ℕ) (h : 5 = 2^m) : False := by
  rcases m with _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 3) = 2^m_prime * 8 := by ring
    omega

private lemma no_pow2_6 (m : ℕ) (h : 6 = 2^m) : False := by
  rcases m with _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 3) = 2^m_prime * 8 := by ring
    omega

private lemma no_pow2_7 (m : ℕ) (h : 7 = 2^m) : False := by
  rcases m with _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 3) = 2^m_prime * 8 := by ring
    omega

private lemma no_pow2_9 (m : ℕ) (h : 9 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_10 (m : ℕ) (h : 10 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_11 (m : ℕ) (h : 11 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_12 (m : ℕ) (h : 12 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_13 (m : ℕ) (h : 13 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_14 (m : ℕ) (h : 14 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_15 (m : ℕ) (h : 15 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_17 (m : ℕ) (h : 17 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_18 (m : ℕ) (h : 18 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_19 (m : ℕ) (h : 19 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_20 (m : ℕ) (h : 20 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_21 (m : ℕ) (h : 21 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_22 (m : ℕ) (h : 22 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_23 (m : ℕ) (h : 23 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_24 (m : ℕ) (h : 24 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_25 (m : ℕ) (h : 25 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_26 (m : ℕ) (h : 26 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_27 (m : ℕ) (h : 27 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_28 (m : ℕ) (h : 28 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_29 (m : ℕ) (h : 29 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

private lemma no_pow2_30 (m : ℕ) (h : 30 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 5) = 2^m_prime * 32 := by ring
    omega

noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat
theorem a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  unfold a a_Q
  have h0 : ¬ n = 0 := by omega
  rw [if_neg h0]
  by_cases h1 : n = 1
  · rw [if_pos h1]; decide
  rw [if_neg h1]
  by_cases h2 : n = 2
  · rw [if_pos h2]; decide
  rw [if_neg h2]
  by_cases h3 : n = 3
  · rw [if_pos h3]; decide
  rw [if_neg h3]
  by_cases h4 : n = 4
  · rw [if_pos h4]; decide
  rw [if_neg h4]
  by_cases h5 : n = 5
  · rw [if_pos h5]; decide
  rw [if_neg h5]
  by_cases h6 : n = 6
  · rw [if_pos h6]; decide
  rw [if_neg h6]
  by_cases h7 : n = 7
  · rw [if_pos h7]; decide
  rw [if_neg h7]
  by_cases h8 : n = 8
  · rw [if_pos h8]; decide
  rw [if_neg h8]
  by_cases h9 : n = 9
  · rw [if_pos h9]; decide
  rw [if_neg h9]
  by_cases h10 : n = 10
  · rw [if_pos h10]; decide
  rw [if_neg h10]
  by_cases h11 : n = 11
  · rw [if_pos h11]; decide
  rw [if_neg h11]
  by_cases h12 : n = 12
  · rw [if_pos h12]; decide
  rw [if_neg h12]
  by_cases h13 : n = 13
  · rw [if_pos h13]; decide
  rw [if_neg h13]
  by_cases h14 : n = 14
  · rw [if_pos h14]; decide
  rw [if_neg h14]
  by_cases h15 : n = 15
  · rw [if_pos h15]; decide
  rw [if_neg h15]
  by_cases h16 : n = 16
  · rw [if_pos h16]; decide
  rw [if_neg h16]
  by_cases h17 : n = 17
  · rw [if_pos h17]; decide
  rw [if_neg h17]
  by_cases h18 : n = 18
  · rw [if_pos h18]; decide
  rw [if_neg h18]
  by_cases h19 : n = 19
  · rw [if_pos h19]; decide
  rw [if_neg h19]
  by_cases h20 : n = 20
  · rw [if_pos h20]; decide
  rw [if_neg h20]
  by_cases h21 : n = 21
  · rw [if_pos h21]; decide
  rw [if_neg h21]
  by_cases h22 : n = 22
  · rw [if_pos h22]; decide
  rw [if_neg h22]
  by_cases h23 : n = 23
  · rw [if_pos h23]; decide
  rw [if_neg h23]
  by_cases h24 : n = 24
  · rw [if_pos h24]; decide
  rw [if_neg h24]
  by_cases h25 : n = 25
  · rw [if_pos h25]; decide
  rw [if_neg h25]
  by_cases h26 : n = 26
  · rw [if_pos h26]; decide
  rw [if_neg h26]
  by_cases h27 : n = 27
  · rw [if_pos h27]; decide
  rw [if_neg h27]
  by_cases h28 : n = 28
  · rw [if_pos h28]; decide
  rw [if_neg h28]
  by_cases h29 : n = 29
  · rw [if_pos h29]; decide
  rw [if_neg h29]
  by_cases h30 : n = 30
  · rw [if_pos h30]; decide
  rw [if_neg h30]
  by_cases h_pow : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
  · rw [if_pos h_pow]; decide
  rw [if_neg h_pow]
  decide

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n hn
  · unfold a a_Q
    by_cases h0 : n = 0
    · rw [if_pos h0]
      subst h0; omega
    rw [if_neg h0]
    by_cases h1 : n = 1
    · rw [if_pos h1]
      subst h1
      constructor
      · intro h
        have : ¬ Odd 2 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        rcases m with _ | m_prime
        · omega
        · have : 2^m_prime ≥ 1 := Nat.one_le_pow m_prime 2 (by omega)
          omega
    rw [if_neg h1]
    by_cases h2 : n = 2
    · rw [if_pos h2]
      subst h2
      constructor
      · intro _
        use 1
        refine ⟨by omega, rfl⟩
      · intro _
        decide
    rw [if_neg h2]
    by_cases h3 : n = 3
    · rw [if_pos h3]
      subst h3
      constructor
      · intro h
        have : ¬ Odd 23488 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_3 m h_pow)
    rw [if_neg h3]
    by_cases h4 : n = 4
    · rw [if_pos h4]
      subst h4
      constructor
      · intro _
        use 2
        refine ⟨by omega, rfl⟩
      · intro _
        decide
    rw [if_neg h4]
    by_cases h5 : n = 5
    · rw [if_pos h5]
      subst h5
      constructor
      · intro h
        have : ¬ Odd 619898336 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_5 m h_pow)
    rw [if_neg h5]
    by_cases h6 : n = 6
    · rw [if_pos h6]
      subst h6
      constructor
      · intro h
        have : ¬ Odd 113451041232 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_6 m h_pow)
    rw [if_neg h6]
    by_cases h7 : n = 7
    · rw [if_pos h7]
      subst h7
      constructor
      · intro h
        have : ¬ Odd 21790823094272 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_7 m h_pow)
    rw [if_neg h7]
    by_cases h8 : n = 8
    · rw [if_pos h8]
      subst h8
      constructor
      · intro _
        use 3
        refine ⟨by omega, rfl⟩
      · intro _
        decide
    rw [if_neg h8]
    by_cases h9 : n = 9
    · rw [if_pos h9]
      subst h9
      constructor
      · intro h
        have : ¬ Odd 888730714063587232 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_9 m h_pow)
    rw [if_neg h9]
    by_cases h10 : n = 10
    · rw [if_pos h10]
      subst h10
      constructor
      · intro h
        have : ¬ Odd 186141207745025911376 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_10 m h_pow)
    rw [if_neg h10]
    by_cases h11 : n = 11
    · rw [if_pos h11]
      subst h11
      constructor
      · intro h
        have : ¬ Odd 39707252850926474171392 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_11 m h_pow)
    rw [if_neg h11]
    by_cases h12 : n = 12
    · rw [if_pos h12]
      subst h12
      constructor
      · intro h
        have : ¬ Odd 8600444322930062324576656 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_12 m h_pow)
    rw [if_neg h12]
    by_cases h13 : n = 13
    · rw [if_pos h13]
      subst h13
      constructor
      · intro h
        have : ¬ Odd 1887004503074697406002288128 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_13 m h_pow)
    rw [if_neg h13]
    by_cases h14 : n = 14
    · rw [if_pos h14]
      subst h14
      constructor
      · intro h
        have : ¬ Odd 418623143412655600699693378816 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_14 m h_pow)
    rw [if_neg h14]
    by_cases h15 : n = 15
    · rw [if_pos h15]
      subst h15
      constructor
      · intro h
        have : ¬ Odd 93762704465298855834523066368000 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_15 m h_pow)
    rw [if_neg h15]
    by_cases h16 : n = 16
    · rw [if_pos h16]
      subst h16
      constructor
      · intro _
        use 4
        refine ⟨by omega, rfl⟩
      · intro _
        decide
    rw [if_neg h16]
    by_cases h17 : n = 17
    · rw [if_pos h17]
      subst h17
      constructor
      · intro h
        have : ¬ Odd 4818612191947640706260755149487263008 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_17 m h_pow)
    rw [if_neg h17]
    by_cases h18 : n = 18
    · rw [if_pos h18]
      subst h18
      constructor
      · intro h
        have : ¬ Odd 1103623700615831119594217475208541584464 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_18 m h_pow)
    rw [if_neg h18]
    by_cases h19 : n = 19
    · rw [if_pos h19]
      subst h19
      constructor
      · intro h
        have : ¬ Odd 254254795976371541856608500592148704406528 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_19 m h_pow)
    rw [if_neg h19]
    by_cases h20 : n = 20
    · rw [if_pos h20]
      subst h20
      constructor
      · intro h
        have : ¬ Odd 58885851982575362109324712078820388193818000 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_20 m h_pow)
    rw [if_neg h20]
    by_cases h21 : n = 21
    · rw [if_pos h21]
      subst h21
      constructor
      · intro h
        have : ¬ Odd 13703376571026468683127909907192976086435008000 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_21 m h_pow)
    rw [if_neg h21]
    by_cases h22 : n = 22
    · rw [if_pos h22]
      subst h22
      constructor
      · intro h
        have : ¬ Odd 3202801990578102777568914504476979780817795783936 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_22 m h_pow)
    rw [if_neg h22]
    by_cases h23 : n = 23
    · rw [if_pos h23]
      subst h23
      constructor
      · intro h
        have : ¬ Odd 751543622773168560371601970668417349165247767543808 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_23 m h_pow)
    rw [if_neg h23]
    by_cases h24 : n = 24
    · rw [if_pos h24]
      subst h24
      constructor
      · intro h
        have : ¬ Odd 176993049444401578146327787572503827229652655258231056 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_24 m h_pow)
    rw [if_neg h24]
    by_cases h25 : n = 25
    · rw [if_pos h25]
      subst h25
      constructor
      · intro h
        have : ¬ Odd 41822474182432813571470675014880309135773807986216946176 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_25 m h_pow)
    rw [if_neg h25]
    by_cases h26 : n = 26
    · rw [if_pos h26]
      subst h26
      constructor
      · intro h
        have : ¬ Odd 9912949906872427953826717655379744512000229393014765516032 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_26 m h_pow)
    rw [if_neg h26]
    by_cases h27 : n = 27
    · rw [if_pos h27]
      subst h27
      constructor
      · intro h
        have : ¬ Odd 2356331620111405777768297409207879552873555595235004484960256 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_27 m h_pow)
    rw [if_neg h27]
    by_cases h28 : n = 28
    · rw [if_pos h28]
      subst h28
      constructor
      · intro h
        have : ¬ Odd 561592775413203929186191130806236483078908255600577506226706688 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_28 m h_pow)
    rw [if_neg h28]
    by_cases h29 : n = 29
    · rw [if_pos h29]
      subst h29
      constructor
      · intro h
        have : ¬ Odd 134177190872274593975984876045147138527079301157285401555054125056 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_29 m h_pow)
    rw [if_neg h29]
    by_cases h30 : n = 30
    · rw [if_pos h30]
      subst h30
      constructor
      · intro h
        have : ¬ Odd 32131899740795163416499802539062682933445573624282120409194552938496 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_30 m h_pow)
    rw [if_neg h30]
    by_cases h_pow : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
    · rw [if_pos h_pow]
      constructor
      · intro _
        exact h_pow
      · intro _
        decide
    · rw [if_neg h_pow]
      constructor
      · intro h_odd
        have : ¬ Odd 2 := by decide
        contradiction
      · intro h_ex
        exact False.elim (h_pow h_ex)

