import FormalConjectures.Util.ProblemImports
open Rat Nat

/--
A046969: Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$.
The $n$-th term is the denominator of the rational number
$$ \frac{B_{2n}}{2n(2n-1)} $$
where $B_{2n}$ is the $2n$-th Bernoulli number (Mathlib's `bernoulli`).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    -- We use Rat.bernoulli (aliased as bernoulli) for B_{2n}.
    -- The denominator k is coerced to Rat for division.
    (bernoulli m / (k : ℚ)).den
open Finset

-- Helper: decompose a sum over range (a*b) into blocks.
theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (b : ℕ) (f : ℕ → M) :
    ∀ a : ℕ, ∑ k ∈ Finset.range (a * b), f k
      = ∑ s ∈ Finset.range a, ∑ j ∈ Finset.range b, f (s * b + j) := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← ih]
    rw [Nat.succ_mul, Finset.sum_range_add]

-- lemma (b): q^t divides the power sum over the full prime-power range q^(t+1)
theorem dvd_sum_range_pow (q : ℕ) (hq : 1 ≤ q) (i : ℕ) :
    ∀ t : ℕ, q ^ t ∣ ∑ k ∈ Finset.range (q ^ (t + 1)), k ^ i := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have hpos : 0 < q ^ (t + 1) := pow_pos hq (t + 1)
    have : NeZero (q ^ (t + 1)) := ⟨hpos.ne'⟩
    obtain ⟨c, hc⟩ := ih
    rw [← ZMod.natCast_eq_zero_iff]
    have hdec : q ^ (t + 1 + 1) = q * q ^ (t + 1) := by rw [pow_succ]; ring
    rw [hdec, sum_range_mul' (q ^ (t + 1)) (fun k => k ^ i) q]
    have key : ∀ s j : ℕ,
        ((s * q ^ (t + 1) + j : ℕ) : ZMod (q ^ (t + 1))) = (j : ZMod (q ^ (t + 1))) := by
      intro s j
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [Nat.cast_sum]
    simp only [Nat.cast_sum, Nat.cast_pow, key]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcast : (∑ j ∈ Finset.range (q ^ (t + 1)), (j : ZMod (q ^ (t + 1))) ^ i)
        = ((q ^ t * c : ℕ) : ZMod (q ^ (t + 1))) := by
      rw [← hc]; push_cast; rfl
    rw [hcast, ← Nat.cast_mul,
      show q * (q ^ t * c) = q ^ (t + 1) * c by rw [pow_succ]; ring,
      Nat.cast_mul, ZMod.natCast_self, zero_mul]

-- Finset ultrametric lower bound for padic valuation of a sum
theorem padicValRat_le_sum {p : ℕ} [Fact p.Prime] {α : Type*} (s : Finset α) (f : α → ℚ) (c : ℤ)
    (h : ∀ a ∈ s, f a = 0 ∨ c ≤ padicValRat p (f a)) :
    (∑ a ∈ s, f a) = 0 ∨ c ≤ padicValRat p (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction with
  | empty => left; simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hfa := h a (Finset.mem_insert_self a s)
    have ih' := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
    rcases hfa with hfa | hfa
    · rw [hfa, zero_add]; exact ih'
    · rcases ih' with hs | hs
      · rw [hs, add_zero]; right; exact hfa
      · by_cases hsum : f a + ∑ b ∈ s, f b = 0
        · left; exact hsum
        · right
          calc c ≤ min (padicValRat p (f a)) (padicValRat p (∑ b ∈ s, f b)) := le_min hfa hs
            _ ≤ padicValRat p (f a + ∑ b ∈ s, f b) := padicValRat.min_le_padicValRat_add hsum

open scoped BigOperators in
/-- Central identity: isolating `bernoulli i` from Faulhaber's formula at `N`. -/
theorem bernoulli_faulhaber_eq (N i : ℕ) :
    bernoulli i * ((i + 1 : ℚ) * (N : ℚ)) =
      (i + 1) * (∑ k ∈ Finset.range N, (k : ℚ) ^ i)
        - ∑ j ∈ Finset.range i,
            bernoulli j * ((i + 1).choose j : ℚ) * (N : ℚ) ^ (i + 1 - j) := by
  have hi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hF := sum_range_pow N i
  have hF2 : ((i : ℚ) + 1) * (∑ k ∈ Finset.range N, (k : ℚ) ^ i)
      = ∑ j ∈ Finset.range (i + 1),
          bernoulli j * ((i + 1).choose j : ℚ) * (N : ℚ) ^ (i + 1 - j) := by
    rw [hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [Finset.sum_range_succ] at hF2
  have hchoose : ((i + 1).choose i : ℚ) = (i : ℚ) + 1 := by
    rw [Nat.choose_succ_self_right]; push_cast; ring
  have hsub : i + 1 - i = 1 := by omega
  rw [hchoose, hsub, pow_one] at hF2
  linear_combination -hF2

-- helper: padicValRat of a nat cast
theorem pvr_natCast (q m : ℕ) : padicValRat q (m : ℚ) = padicValNat q m := by
  simp [padicValRat.of_nat, padicValInt.of_nat]

/-- Squarefree denominators: `v_q(bernoulli i) ≥ -1`. -/
theorem padicValRat_bernoulli_ge (q : ℕ) [hq : Fact q.Prime] :
    ∀ i, -1 ≤ padicValRat q (bernoulli i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hqp : q.Prime := hq.out
    have hq2 : 2 ≤ q := hqp.two_le
    by_cases hodd : Odd i
    · have hoi : i % 2 = 1 := Nat.odd_iff.mp hodd
      by_cases hi1 : i = 1
      · subst hi1
        rw [bernoulli_one]
        have : padicValRat q ((-1)/2 : ℚ) = - padicValRat q (2 : ℚ) := by
          rw [show ((-1)/2 : ℚ) = -(1/2) by ring, padicValRat.neg, one_div, padicValRat.inv]
        rw [this]
        have : padicValRat q (2 : ℚ) = padicValNat q 2 := by
          rw [show (2:ℚ) = ((2:ℕ):ℚ) by norm_num, pvr_natCast]
        rw [this]
        have : padicValNat q 2 ≤ 1 := by
          rcases eq_or_ne q 2 with rfl | hne
          · simp [padicValNat.self]
          · rw [padicValNat.eq_zero_of_not_dvd]
            · omega
            · intro h; exact hne ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h)
        omega
      · rw [bernoulli_eq_zero_of_odd hodd (by omega), padicValRat.zero]; norm_num
    · -- i even
      by_cases hi0 : i = 0
      · subst hi0; rw [bernoulli_zero, padicValRat.one]; norm_num
      · -- i even, i ≥ 2
        have hev : i % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
        have hi2 : 2 ≤ i := by omega
        by_cases hb : bernoulli i = 0
        · rw [hb, padicValRat.zero]; norm_num
        · -- MAIN CASE
          set t := padicValNat q (i + 1) + 1 with ht
          have htpos : 1 ≤ t := by omega
          set N := q ^ t with hN
          have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
          have hNpos : 0 < N := pow_pos (by omega) t
          have hNcast : ((N : ℕ) : ℚ) = (q : ℚ) ^ t := by rw [hN]; push_cast; ring
          -- the central identity, with N cast simplified
          have hid := bernoulli_faulhaber_eq N i
          rw [hNcast] at hid
          -- abbreviations
          set S : ℚ := ∑ k ∈ Finset.range N, (k : ℚ) ^ i with hS
          set Snat : ℕ := ∑ k ∈ Finset.range N, k ^ i with hSnat
          have hScast : S = (Snat : ℚ) := by rw [hS, hSnat]; push_cast; rfl
          -- Snat ≥ 1
          have hSnatpos : 1 ≤ Snat := by
            have h1 : (1 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by
              calc 1 < q := by omega
              _ ≤ q ^ t := Nat.le_self_pow (by omega) q)
            calc 1 = 1 ^ i := (one_pow i).symm
            _ ≤ Snat := Finset.single_le_sum (f := fun k => k ^ i)
                (fun k _ => Nat.zero_le _) h1
          have hSne : Snat ≠ 0 := by omega
          -- v_q(Snat) ≥ t - 1
          have hdvd : q ^ (t - 1) ∣ Snat := by
            have := dvd_sum_range_pow q (by omega) i (t - 1)
            rwa [show t - 1 + 1 = t by omega] at this
          have hvSnat : (t : ℤ) - 1 ≤ padicValNat q Snat := by
            have hle : t - 1 ≤ padicValNat q Snat := by
              rw [← Nat.factorization_def Snat hqp]
              exact (Nat.Prime.pow_dvd_iff_le_factorization hqp hSne).mp hdvd
            omega
          -- v_q(N cast) = t
          have hvN : padicValRat q ((q : ℚ) ^ t) = t := by
            rw [padicValRat.pow hq0, padicValRat.self hqp.one_lt, mul_one]
          -- v_q(i+1) = t - 1
          have hvi1 : padicValRat q ((i : ℚ) + 1) = (t : ℤ) - 1 := by
            rw [show ((i : ℚ) + 1) = (((i + 1 : ℕ)) : ℚ) by push_cast; ring, pvr_natCast]
            omega
          -- D ≠ 0
          have hDne : ((i : ℚ) + 1) * (q : ℚ) ^ t ≠ 0 := by positivity
          have hi1ne : ((i : ℚ) + 1) ≠ 0 := by positivity
          have hpowne : (q : ℚ) ^ t ≠ 0 := by positivity
          have hSne' : S ≠ 0 := by rw [hScast]; exact_mod_cast hSne
          -- v_q(D) = 2t - 1
          have hvD : padicValRat q (((i : ℚ) + 1) * (q : ℚ) ^ t) = 2 * t - 1 := by
            rw [padicValRat.mul hi1ne hpowne, hvi1, hvN]; ring
          -- v_q((i+1)*S) ≥ 2t - 2
          have hvA : 2 * (t : ℤ) - 2 ≤ padicValRat q (((i : ℚ) + 1) * S) := by
            rw [padicValRat.mul hi1ne hSne', hvi1, hScast, pvr_natCast]
            omega
          -- R = the lower sum
          set R : ℚ := ∑ j ∈ Finset.range i,
              bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (t * (i + 1 - j)) with hR
          -- rewrite hid's R to match R (powers)
          have hRrw : (∑ j ∈ Finset.range i,
              bernoulli j * ((i + 1).choose j : ℚ) * ((q : ℚ) ^ t) ^ (i + 1 - j)) = R := by
            rw [hR]; apply Finset.sum_congr rfl; intro j _; rw [← pow_mul]
          rw [hRrw] at hid
          -- bound v_q(R)
          have hvR := padicValRat_le_sum (p := q) (Finset.range i)
            (fun j => bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (t * (i + 1 - j)))
            (2 * t - 1) (by
              intro j hj
              have hjlt : j < i := Finset.mem_range.mp hj
              by_cases hbj : bernoulli j = 0
              · left; simp [hbj]
              · right
                simp only []
                have hCne : ((i + 1).choose j : ℚ) ≠ 0 := by
                  have : 0 < (i + 1).choose j := Nat.choose_pos (by omega)
                  exact_mod_cast this.ne'
                have hpne : (q : ℚ) ^ (t * (i + 1 - j)) ≠ 0 := by positivity
                rw [padicValRat.mul (mul_ne_zero hbj hCne) hpne,
                    padicValRat.mul hbj hCne]
                have hvpow : padicValRat q ((q : ℚ) ^ (t * (i + 1 - j)))
                    = ((t * (i + 1 - j) : ℕ) : ℤ) := by
                  rw [padicValRat.pow hq0, padicValRat.self hqp.one_lt, mul_one]
                rw [hvpow]
                have hbjv : -1 ≤ padicValRat q (bernoulli j) := ih j hjlt
                have hCv : 0 ≤ padicValRat q ((i + 1).choose j : ℚ) := by
                  rw [pvr_natCast]; exact_mod_cast Nat.zero_le _
                have hexp : 2 * t ≤ t * (i + 1 - j) := by
                  have h2 : 2 ≤ i + 1 - j := by omega
                  calc 2 * t = t * 2 := by ring
                  _ ≤ t * (i + 1 - j) := Nat.mul_le_mul le_rfl h2
                have hexp' : (2 : ℤ) * t ≤ (t * (i + 1 - j) : ℕ) := by exact_mod_cast hexp
                omega)
          -- combine: 2t-2 ≤ v_q((i+1)*S - R)
          have hAR : 2 * (t : ℤ) - 2 ≤ padicValRat q (((i : ℚ) + 1) * S - R) := by
            rcases hvR with hR0 | hvR
            · have hR0' : R = 0 := hR0
              rw [hR0', sub_zero]; exact hvA
            · have hvR' : 2 * (t : ℤ) - 1 ≤ padicValRat q R := hvR
              have hARne : ((i : ℚ) + 1) * S - R ≠ 0 := by
                rw [← hid]; exact mul_ne_zero hb hDne
              have hsum_ne : ((i : ℚ) + 1) * S + (-R) ≠ 0 := by rw [← sub_eq_add_neg]; exact hARne
              have key := padicValRat.min_le_padicValRat_add (p := q) hsum_ne
              rw [← sub_eq_add_neg] at key
              have h2 : 2 * (t : ℤ) - 2 ≤ padicValRat q (-R) := by
                rw [padicValRat.neg]; omega
              exact le_trans (le_min hvA h2) key
          -- finish
          have hmuleq : padicValRat q (bernoulli i) + padicValRat q (((i : ℚ) + 1) * (q : ℚ) ^ t)
              = padicValRat q (((i : ℚ) + 1) * S - R) := by
            rw [← padicValRat.mul hb hDne, hid]
          rw [hvD] at hmuleq
          omega

/-- The lower Faulhaber sum `R` (at `N = q`) either vanishes or has valuation `≥ 2`. -/
theorem R_val_aux (q : ℕ) [hq : Fact q.Prime] (i : ℕ) (hi : 4 ≤ i) (heven : Even i) :
    (∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)) = 0
    ∨ 2 ≤ padicValRat q (∑ j ∈ Finset.range i,
        bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)) := by
  have hqp : q.Prime := hq.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqp.pos.ne'
  have hev2 : i % 2 = 0 := Nat.even_iff.mp heven
  exact padicValRat_le_sum (p := q) (Finset.range i)
    (fun j => bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)) 2 (by
      intro j hj
      have hjlt : j < i := Finset.mem_range.mp hj
      by_cases hbj : bernoulli j = 0
      · left; simp [hbj]
      · right
        simp only []
        have hjne : j ≠ i - 1 := by
          rintro rfl
          exact hbj (bernoulli_eq_zero_of_odd (by rw [Nat.odd_iff]; omega) (by omega))
        have hjle : j ≤ i - 2 := by omega
        have hCne : ((i + 1).choose j : ℚ) ≠ 0 := by
          have : 0 < (i + 1).choose j := Nat.choose_pos (by omega)
          exact_mod_cast this.ne'
        have hpne : (q : ℚ) ^ (i + 1 - j) ≠ 0 := by positivity
        rw [padicValRat.mul (mul_ne_zero hbj hCne) hpne, padicValRat.mul hbj hCne]
        have hvpow : padicValRat q ((q : ℚ) ^ (i + 1 - j)) = ((i + 1 - j : ℕ) : ℤ) := by
          rw [padicValRat.pow hq0, padicValRat.self hqp.one_lt, mul_one]
        rw [hvpow]
        have hbjv : -1 ≤ padicValRat q (bernoulli j) := padicValRat_bernoulli_ge q j
        have hCv : 0 ≤ padicValRat q ((i + 1).choose j : ℚ) := by
          rw [pvr_natCast]; positivity
        have hexp : 3 ≤ i + 1 - j := by omega
        have hexp' : (3 : ℤ) ≤ ((i + 1 - j : ℕ) : ℤ) := by exact_mod_cast hexp
        omega)

/-- Bernoulli numbers with even index `≥ 4` are nonzero. -/
theorem bernoulli_ne_zero_even (i : ℕ) (hi : 4 ≤ i) (heven : Even i) : bernoulli i ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev2 : i % 2 = 0 := Nat.even_iff.mp heven
  intro hb
  have hid := bernoulli_faulhaber_eq 2 i
  have hS : (∑ k ∈ Finset.range 2, (k : ℚ) ^ i) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [zero_pow (by omega : i ≠ 0)]
  rw [hS, hb, zero_mul, mul_one] at hid
  -- hid : 0 = (↑i+1) - R
  have hRbound := R_val_aux 2 i hi heven
  rcases hRbound with h0 | hge
  · rw [h0, sub_zero] at hid
    exact (by positivity : ((i : ℚ) + 1) ≠ 0) hid.symm
  · have hReq : (∑ j ∈ Finset.range i,
        bernoulli j * ((i + 1).choose j : ℚ) * ((2 : ℕ) : ℚ) ^ (i + 1 - j)) = (i : ℚ) + 1 := by
      linarith [hid]
    rw [hReq, show ((i : ℚ) + 1) = (((i + 1 : ℕ)) : ℚ) by push_cast; ring, pvr_natCast] at hge
    rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ (2 ∣ (i + 1)))] at hge
    exact absurd hge (by norm_num)

/-- Master setup: the valuation equation from Faulhaber at `N = q`. -/
theorem bernoulli_val_setup (q : ℕ) [hq : Fact q.Prime] (i : ℕ) (hi : 4 ≤ i) (heven : Even i) :
    padicValRat q (bernoulli i) + (padicValNat q (i + 1) : ℤ) + 1
      = padicValRat q (((i : ℚ) + 1) * ((∑ k ∈ Finset.range q, k ^ i : ℕ) : ℚ)
          - ∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j))
    ∧ ((∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)) = 0
       ∨ 2 ≤ padicValRat q (∑ j ∈ Finset.range i,
            bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)))
    ∧ (((i : ℚ) + 1) * ((∑ k ∈ Finset.range q, k ^ i : ℕ) : ℚ)
          - ∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)) ≠ 0 := by
  have hqp : q.Prime := hq.out
  have hbne := bernoulli_ne_zero_even i hi heven
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqp.pos.ne'
  have hid := bernoulli_faulhaber_eq q i
  have hScast : (∑ k ∈ Finset.range q, (k : ℚ) ^ i) = ((∑ k ∈ Finset.range q, k ^ i : ℕ) : ℚ) := by
    push_cast; rfl
  rw [hScast] at hid
  have hi1ne : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hDne : ((i : ℚ) + 1) * (q : ℚ) ≠ 0 := mul_ne_zero hi1ne hq0
  have hnumne : ((i : ℚ) + 1) * ((∑ k ∈ Finset.range q, k ^ i : ℕ) : ℚ)
      - ∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j) ≠ 0 := by
    rw [← hid]; exact mul_ne_zero hbne hDne
  refine ⟨?_, R_val_aux q i hi heven, hnumne⟩
  have hmul : padicValRat q (bernoulli i * (((i : ℚ) + 1) * (q : ℚ)))
      = padicValRat q (bernoulli i) + padicValRat q (((i : ℚ) + 1) * (q : ℚ)) :=
    padicValRat.mul hbne hDne
  have hvD : padicValRat q (((i : ℚ) + 1) * (q : ℚ)) = (padicValNat q (i + 1) : ℤ) + 1 := by
    rw [padicValRat.mul hi1ne hq0,
        show ((i : ℚ) + 1) = (((i + 1 : ℕ)) : ℚ) by push_cast; ring,
        pvr_natCast, pvr_natCast, padicValNat.self hqp.one_lt, Nat.cast_one]
  rw [hid, hvD] at hmul
  linarith [hmul]

/-- Positivity of the power sum `∑_{k<q} k^i` for prime `q`. -/
theorem sum_range_pow_pos (q : ℕ) (hq : 2 ≤ q) (i : ℕ) : 0 < ∑ k ∈ Finset.range q, k ^ i := by
  have h1 : (1 : ℕ) ∈ Finset.range q := Finset.mem_range.mpr (by omega)
  calc 0 < 1 ^ i := by positivity
  _ ≤ ∑ k ∈ Finset.range q, k ^ i :=
      Finset.single_le_sum (f := fun k => k ^ i) (fun k _ => Nat.zero_le _) h1

/-- Exact valuation: when `v_q(i+1)+v_q(S) < 2`, `v_q(B i) = v_q(S) - 1`. -/
theorem val_eq (q : ℕ) [hq : Fact q.Prime] (i : ℕ) (hi : 4 ≤ i) (heven : Even i)
    (hlt : padicValNat q (i + 1) + padicValNat q (∑ k ∈ Finset.range q, k ^ i) < 2) :
    padicValRat q (bernoulli i) = (padicValNat q (∑ k ∈ Finset.range q, k ^ i) : ℤ) - 1 := by
  have hqp : q.Prime := hq.out
  obtain ⟨heq, hRdisj, hnumne⟩ := bernoulli_val_setup q i hi heven
  set Snat := ∑ k ∈ Finset.range q, k ^ i with hSnat
  set R : ℚ := ∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)
    with hR
  have hi1ne : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hSpos : 0 < Snat := sum_range_pow_pos q hqp.two_le i
  have hSne : ((Snat : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hvAS : padicValRat q (((i : ℚ) + 1) * (Snat : ℚ))
      = (padicValNat q (i + 1) : ℤ) + padicValNat q Snat := by
    rw [padicValRat.mul hi1ne hSne,
        show ((i : ℚ) + 1) = (((i + 1 : ℕ)) : ℚ) by push_cast; ring, pvr_natCast, pvr_natCast]
  have hvnum : padicValRat q (((i : ℚ) + 1) * (Snat : ℚ) - R)
      = (padicValNat q (i + 1) : ℤ) + padicValNat q Snat := by
    rcases hRdisj with hR0 | hRge
    · rw [hR0, sub_zero, hvAS]
    · have hRne : R ≠ 0 := by
        intro h; rw [h, padicValRat.zero] at hRge; norm_num at hRge
      have hqne : ((i : ℚ) + 1) * (Snat : ℚ) ≠ 0 := mul_ne_zero hi1ne hSne
      have hval : padicValRat q (((i : ℚ) + 1) * (Snat : ℚ)) < padicValRat q (-R) := by
        rw [padicValRat.neg, hvAS]; omega
      rw [sub_eq_add_neg]
      rw [padicValRat.add_eq_of_lt (by rw [← sub_eq_add_neg]; exact hnumne) hqne
        (by simpa using hRne) hval, hvAS]
  rw [hvnum] at heq
  omega

/-- Lower bound: absorption case `v_q(i+1)=0`, `v_q(S) ≥ 2` give `v_q(B i) ≥ 1`. -/
theorem val_ge (q : ℕ) [hq : Fact q.Prime] (i : ℕ) (hi : 4 ≤ i) (heven : Even i)
    (hi1 : padicValNat q (i + 1) = 0)
    (hSge : 2 ≤ padicValNat q (∑ k ∈ Finset.range q, k ^ i)) :
    1 ≤ padicValRat q (bernoulli i) := by
  have hqp : q.Prime := hq.out
  obtain ⟨heq, hRdisj, hnumne⟩ := bernoulli_val_setup q i hi heven
  set Snat := ∑ k ∈ Finset.range q, k ^ i with hSnat
  set R : ℚ := ∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)
    with hR
  have hi1ne : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hSpos : 0 < Snat := sum_range_pow_pos q hqp.two_le i
  have hSne : ((Snat : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hvAS : padicValRat q (((i : ℚ) + 1) * (Snat : ℚ))
      = (padicValNat q (i + 1) : ℤ) + padicValNat q Snat := by
    rw [padicValRat.mul hi1ne hSne,
        show ((i : ℚ) + 1) = (((i + 1 : ℕ)) : ℚ) by push_cast; ring, pvr_natCast, pvr_natCast]
  have hASge : 2 ≤ padicValRat q (((i : ℚ) + 1) * (Snat : ℚ)) := by rw [hvAS]; omega
  have hnumge : 2 ≤ padicValRat q (((i : ℚ) + 1) * (Snat : ℚ) - R) := by
    rcases hRdisj with hR0 | hRge
    · rw [hR0, sub_zero]; exact hASge
    · rw [sub_eq_add_neg]
      have key := padicValRat.min_le_padicValRat_add (p := q)
        (show ((i : ℚ) + 1) * (Snat : ℚ) + (-R) ≠ 0 by rw [← sub_eq_add_neg]; exact hnumne)
      have h2 : 2 ≤ padicValRat q (-R) := by rw [padicValRat.neg]; exact hRge
      exact le_trans (le_min hASge h2) key
  rw [hi1] at heq
  omega

/-- Unified lower bound: `v_q(i+1) ≤ 1` and `v_q(S) ≥ 1` give `v_q(B i) ≥ 0`. -/
theorem val_lb (q : ℕ) [hq : Fact q.Prime] (i : ℕ) (hi : 4 ≤ i) (heven : Even i)
    (hi1 : padicValNat q (i + 1) ≤ 1)
    (hSnat1 : 1 ≤ padicValNat q (∑ k ∈ Finset.range q, k ^ i)) :
    0 ≤ padicValRat q (bernoulli i) := by
  have hqp : q.Prime := hq.out
  obtain ⟨heq, hRdisj, hnumne⟩ := bernoulli_val_setup q i hi heven
  set Snat := ∑ k ∈ Finset.range q, k ^ i with hSnat
  set R : ℚ := ∑ j ∈ Finset.range i, bernoulli j * ((i + 1).choose j : ℚ) * (q : ℚ) ^ (i + 1 - j)
    with hR
  have hi1ne : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hSpos : 0 < Snat := sum_range_pow_pos q hqp.two_le i
  have hSne : ((Snat : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hvAS : padicValRat q (((i : ℚ) + 1) * (Snat : ℚ))
      = (padicValNat q (i + 1) : ℤ) + padicValNat q Snat := by
    rw [padicValRat.mul hi1ne hSne,
        show ((i : ℚ) + 1) = (((i + 1 : ℕ)) : ℚ) by push_cast; ring, pvr_natCast, pvr_natCast]
  have hb1 : min ((padicValNat q (i + 1) : ℤ) + padicValNat q Snat) 2
      ≤ padicValRat q (((i : ℚ) + 1) * (Snat : ℚ) - R) := by
    rcases hRdisj with hR0 | hRge
    · rw [hR0, sub_zero, hvAS]; exact min_le_left _ _
    · rw [sub_eq_add_neg]
      have key := padicValRat.min_le_padicValRat_add (p := q)
        (show ((i : ℚ) + 1) * (Snat : ℚ) + (-R) ≠ 0 by rw [← sub_eq_add_neg]; exact hnumne)
      have h2 : 2 ≤ padicValRat q (-R) := by rw [padicValRat.neg]; exact hRge
      calc min ((padicValNat q (i + 1) : ℤ) + padicValNat q Snat) 2
          ≤ min (padicValRat q (((i : ℚ) + 1) * (Snat : ℚ))) (padicValRat q (-R)) :=
            min_le_min (le_of_eq hvAS.symm) h2
        _ ≤ _ := key
  rcases lt_or_ge ((padicValNat q (i + 1) : ℤ) + padicValNat q Snat) 2 with hc | hc
  · rw [min_eq_left (le_of_lt hc)] at hb1; omega
  · rw [min_eq_right hc] at hb1; omega

/-- Lemma (c): if `(q-1) ∤ i`, then `q ∣ ∑_{k<q} k^i`. -/
theorem dvd_sum_pow_of_not_dvd (q : ℕ) (hq : q.Prime) (i : ℕ) (hi : i ≠ 0)
    (hnd : ¬ (q - 1) ∣ i) : q ∣ ∑ k ∈ Finset.range q, k ^ i := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  classical
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]
  have hsum : (∑ k ∈ Finset.range q, (k : ZMod q) ^ i) = ∑ x : ZMod q, x ^ i :=
    Finset.sum_nbij' (fun k => (k : ZMod q)) (fun x => x.val)
      (fun k _ => Finset.mem_univ _)
      (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
      (fun k hk => ZMod.val_natCast_of_lt (Finset.mem_range.mp hk))
      (fun x _ => ZMod.natCast_zmod_val x)
      (fun k _ => rfl)
  rw [hsum]
  -- goal: ∑ x : ZMod q, x ^ i = 0
  have hz : (∑ x : ZMod q, x ^ i) = ∑ x ∈ Finset.univ \ {(0 : ZMod q)}, x ^ i := by
    rw [← Finset.sum_sdiff ({0} : Finset (ZMod q)).subset_univ, Finset.sum_singleton,
      zero_pow hi, add_zero]
  rw [hz]
  let embU : (ZMod q)ˣ ↪ ZMod q := ⟨fun x => ↑x, Units.val_injective⟩
  have hmap : Finset.univ.map embU = Finset.univ \ {(0 : ZMod q)} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, embU] using isUnit_iff_ne_zero
  rw [← hmap, Finset.sum_map]
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have hu := FiniteField.sum_pow_units (ZMod q) i
  rw [hcard, if_neg hnd] at hu
  rw [← hu]
  apply Finset.sum_congr rfl
  intro x _
  simp only [embU, Function.Embedding.coeFn_mk, Units.val_pow_eq_pow_val]


-- ======================= ASSEMBLY =======================

theorem padicValNat_den_eq (r : ℚ) (p : ℕ) [hp : Fact p.Prime] :
    (padicValNat p r.den : ℤ) = max 0 (- padicValRat p r) := by
  have hpp : p.Prime := hp.out
  rw [padicValRat_def]
  by_cases hpd : p ∣ r.den
  · have hnum : ¬ (p : ℤ) ∣ r.num := by
      intro h
      have h1 : p ∣ r.num.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr h
        rwa [Int.natAbs_natCast] at this
      have hg : p ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hpd
      exact hpp.one_lt.ne' (Nat.dvd_one.mp (r.reduced ▸ hg))
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    have : (0:ℤ) ≤ (padicValNat p r.den : ℤ) := Int.natCast_nonneg _
    omega
  · rw [padicValNat.eq_zero_of_not_dvd hpd]
    have : (0:ℤ) ≤ (padicValInt p r.num : ℤ) := Int.natCast_nonneg _
    omega

theorem a_unfold (n : ℕ) (hn : n ≠ 0) :
    a n = (bernoulli (2*n) / ((2*n*(2*n-1) : ℕ) : ℚ)).den := by
  simp only [a, if_neg hn]

theorem a_val (n p : ℕ) (hn : 2 ≤ n) [Fact p.Prime] :
    (padicValNat p (a n) : ℤ)
      = max 0 ((padicValNat p (2*n*(2*n-1)) : ℤ) - padicValRat p (bernoulli (2*n))) := by
  rw [a_unfold n (by omega), padicValNat_den_eq]
  congr 1
  have hk : ((2*n*(2*n-1) : ℕ) : ℚ) ≠ 0 := by
    have : 2*n*(2*n-1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    exact_mod_cast this
  have hb : bernoulli (2*n) ≠ 0 :=
    bernoulli_ne_zero_even (2*n) (by omega) ⟨n, by ring⟩
  rw [padicValRat.div hb hk, pvr_natCast]
  ring


-- ===== numeric helpers =====
theorem one_le_pvn (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (h : p ∣ n) : 1 ≤ padicValNat p n := by
  rw [← Nat.factorization_def n hp]
  exact (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp (by simpa using h)

theorem pvn_ge2_of_sq_dvd (q Snat : ℕ) (hq : q.Prime) (hSne : Snat ≠ 0) (h : q^2 ∣ Snat) :
    2 ≤ padicValNat q Snat := by
  rw [← Nat.factorization_def Snat hq]
  exact (Nat.Prime.pow_dvd_iff_le_factorization hq hSne).mp h

theorem pvn_eq1 (q Snat : ℕ) (hq : q.Prime) (hSne : Snat ≠ 0) (h1 : q ∣ Snat) (h2 : ¬ q^2 ∣ Snat) :
    padicValNat q Snat = 1 := by
  have hf : padicValNat q Snat = Snat.factorization q := (Nat.factorization_def Snat hq).symm
  rw [hf]
  have a1 : 1 ≤ Snat.factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hq hSne).mp (by simpa using h1)
  have a2 : ¬ 2 ≤ Snat.factorization q := fun hc =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization hq hSne).mpr hc)
  omega

-- ===== general bernoulli valuation at 2 and 3 =====
theorem vB2_eq (i : ℕ) (hi : 4 ≤ i) (heven : Even i) : padicValRat 2 (bernoulli i) = -1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hev2 : i % 2 = 0 := Nat.even_iff.mp heven
  have hS : (∑ k ∈ Finset.range 2, k ^ i) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]; simp [zero_pow (show i ≠ 0 by omega)]
  have hpv1 : padicValNat 2 (i + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hpvS : padicValNat 2 (∑ k ∈ Finset.range 2, k ^ i) = 0 := by rw [hS]; simp
  have h := val_eq 2 i hi heven (by rw [hpv1, hpvS]; norm_num)
  rw [hpvS] at h; simpa using h

theorem vB3_eq (i : ℕ) (hi : 4 ≤ i) (heven : Even i) (hv3 : padicValNat 3 (i + 1) ≤ 1) :
    padicValRat 3 (bernoulli i) = -1 := by
  have hS : (∑ k ∈ Finset.range 3, k ^ i) = 1 + 2 ^ i := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [zero_pow (show i ≠ 0 by omega)]
  have h2 : (2 : ZMod 3) ^ i = 1 := by
    have : (2 : ZMod 3) = -1 := by decide
    rw [this, heven.neg_one_pow]
  have hcast : ((1 + 2 ^ i : ℕ) : ZMod 3) = 2 := by
    push_cast; rw [h2]; decide
  have h3S : ¬ 3 ∣ (1 + 2 ^ i) := by
    rw [← ZMod.natCast_eq_zero_iff, hcast]; decide
  have hpvS : padicValNat 3 (∑ k ∈ Finset.range 3, k ^ i) = 0 := by
    rw [hS]; exact padicValNat.eq_zero_of_not_dvd h3S
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := val_eq 3 i hi heven (by rw [hpvS]; omega)
  rw [hpvS] at h; simpa using h


theorem a_ne_zero (m : ℕ) (hm : m ≠ 0) : a m ≠ 0 := by
  rw [a_unfold m hm]; exact (Rat.den_pos _).ne'

theorem twelve_dvd_a (m : ℕ) (hm : 2 ≤ m)
    (h2 : padicValRat 2 (bernoulli (2*m)) = -1)
    (h3 : padicValRat 3 (bernoulli (2*m)) = -1) : a m % 12 = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hane : a m ≠ 0 := a_ne_zero m (by omega)
  have hknz : (2*m*(2*m-1)) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hk2 : 2 ∣ 2*m*(2*m-1) := (dvd_mul_right 2 m).trans (dvd_mul_right (2*m) (2*m-1))
  have hvk2 : 1 ≤ padicValNat 2 (2*m*(2*m-1)) := one_le_pvn 2 _ (by norm_num) hknz hk2
  have hv2 := a_val m 2 hm; rw [h2] at hv2
  have hv3 := a_val m 3 hm; rw [h3] at hv3
  have hvk2' : (1:ℤ) ≤ (padicValNat 2 (2*m*(2*m-1)):ℤ) := by exact_mod_cast hvk2
  have hvk3' : (0:ℤ) ≤ (padicValNat 3 (2*m*(2*m-1)):ℤ) := Int.natCast_nonneg _
  have hge2 : 2 ≤ padicValNat 2 (a m) := by
    have : (2:ℤ) ≤ (padicValNat 2 (a m):ℤ) := by rw [hv2]; omega
    exact_mod_cast this
  have hge3 : 1 ≤ padicValNat 3 (a m) := by
    have : (1:ℤ) ≤ (padicValNat 3 (a m):ℤ) := by rw [hv3]; omega
    exact_mod_cast this
  have hdvd4 : (4:ℕ) ∣ a m := by
    have h : (2:ℕ)^2 ∣ a m := (Nat.Prime.pow_dvd_iff_le_factorization (p:=2) (by norm_num) hane).mpr
      (by rw [Nat.factorization_def (a m) (by norm_num)]; exact hge2)
    simpa using h
  have hdvd3 : (3:ℕ) ∣ a m := by
    have h : (3:ℕ)^1 ∣ a m := (Nat.Prime.pow_dvd_iff_le_factorization (p:=3) (by norm_num) hane).mpr
      (by rw [Nat.factorization_def (a m) (by norm_num)]; exact hge3)
    simpa using h
  have hdvd12 : (12:ℕ) ∣ a m := by
    have hcop : Nat.Coprime 4 3 := by decide
    have := hcop.mul_dvd_of_dvd_of_dvd hdvd4 hdvd3
    simpa using this
  obtain ⟨c, hc⟩ := hdvd12
  omega


theorem a236790 : a 236790 % 12 = 0 := by
  apply twelve_dvd_a 236790 (by norm_num)
  · rw [show 2*236790 = 473580 from by norm_num]
    exact vB2_eq 473580 (by norm_num) ⟨236790, by norm_num⟩
  · rw [show 2*236790 = 473580 from by norm_num]
    refine vB3_eq 473580 (by norm_num) ⟨236790, by norm_num⟩ ?_
    rw [padicValNat.eq_zero_of_not_dvd (show ¬ (3:ℕ) ∣ 473581 by norm_num)]; norm_num

theorem a236793 : a 236793 % 12 = 0 := by
  apply twelve_dvd_a 236793 (by norm_num)
  · rw [show 2*236793 = 473586 from by norm_num]
    exact vB2_eq 473586 (by norm_num) ⟨236793, by norm_num⟩
  · rw [show 2*236793 = 473586 from by norm_num]
    refine vB3_eq 473586 (by norm_num) ⟨236793, by norm_num⟩ ?_
    rw [padicValNat.eq_zero_of_not_dvd (show ¬ (3:ℕ) ∣ 473587 by norm_num)]; norm_num


-- ===== support lemmas for a 236791 = 14172 =====
theorem pvn_le1_of_sqfree (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (hsf : Squarefree n) :
    padicValNat p n ≤ 1 := by
  rw [← Nat.factorization_def n hp]
  exact (Nat.squarefree_iff_factorization_le_one hn).mp hsf p

theorem sqfree_473583 : Squarefree (473583 : ℕ) := by
  rw [show (473583:ℕ) = 3*11*113*127 from by norm_num]
  rw [Nat.squarefree_mul (by norm_num), Nat.squarefree_mul (by norm_num),
      Nat.squarefree_mul (by norm_num)]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> exact (Nat.prime_iff.mp (by norm_num)).squarefree

theorem divisors_pq (e : ℕ) (h : e ∣ 107 * 2213) :
    e = 1 ∨ e = 107 ∨ e = 2213 ∨ e = 236791 := by
  have h2213 : Nat.Prime 2213 := by norm_num
  rcases Nat.coprime_or_dvd_of_prime (show Nat.Prime 107 by norm_num) e with hcop | hdvd
  · have he2213 : e ∣ 2213 := (hcop.symm).dvd_of_dvd_mul_left h
    rcases (Nat.dvd_prime h2213).mp he2213 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  · obtain ⟨f, rfl⟩ := hdvd
    have hf : f ∣ 2213 := (Nat.mul_dvd_mul_iff_left (show 0 < 107 by norm_num)).mp h
    rcases (Nat.dvd_prime h2213).mp hf with h1 | h1
    · subst h1; right; left; norm_num
    · subst h1; right; right; right; norm_num

theorem F1 (p : ℕ) (hp : p.Prime) (h : (p - 1) ∣ 473582) : p = 2 ∨ p = 3 := by
  rcases eq_or_ne p 2 with h2 | h2
  · exact Or.inl h2
  · have hodd : Odd p := hp.odd_of_ne_two h2
    have hpe : 2 ∣ (p - 1) := by rcases hodd with ⟨t, ht⟩; omega
    obtain ⟨e, he⟩ := hpe
    rw [he, show (473582:ℕ) = 2 * 236791 from by norm_num] at h
    have he236 : e ∣ 236791 := (Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)).mp h
    rw [show (236791:ℕ) = 107*2213 from by norm_num] at he236
    rcases divisors_pq e he236 with h1 | h1 | h1 | h1
    · subst h1; exact Or.inr (by omega)
    · subst h1; exfalso; have hpv : p = 215 := by omega
      rw [hpv] at hp; exact (by norm_num : ¬ Nat.Prime 215) hp
    · subst h1; exfalso; have hpv : p = 4427 := by omega
      rw [hpv] at hp; exact (by norm_num : ¬ Nat.Prime 4427) hp
    · subst h1; exfalso; have hpv : p = 473583 := by omega
      rw [hpv] at hp; exact (by norm_num : ¬ Nat.Prime 473583) hp

theorem ndvd_473582 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h107 : p ≠ 107) (h2213 : p ≠ 2213) :
    ¬ p ∣ 473582 := by
  rw [show (473582:ℕ) = 2*107*2213 from by norm_num]; intro hd
  rcases hp.dvd_mul.mp hd with hd1 | hd1
  · rcases hp.dvd_mul.mp hd1 with hd2 | hd2
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd2)
    · exact h107 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd2)
  · exact h2213 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd1)

theorem ndvd_473581 (p : ℕ) (hp : p.Prime) (h401 : p ≠ 401) (h1181 : p ≠ 1181) :
    ¬ p ∣ 473581 := by
  rw [show (473581:ℕ) = 401*1181 from by norm_num]; intro hd
  rcases hp.dvd_mul.mp hd with hd1 | hd1
  · exact h401 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd1)
  · exact h1181 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd1)

theorem ndvd_14172 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h1181 : p ≠ 1181) :
    ¬ p ∣ 14172 := by
  rw [show (14172:ℕ) = 2*2*3*1181 from by norm_num]; intro hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd <;>
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
  · exact h1181 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)

theorem vBgen (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    0 ≤ padicValRat p (bernoulli 473582) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ (p - 1) ∣ 473582 := fun h => by
    rcases F1 p hp h with h | h; exacts [hp2 h, hp3 h]
  have hdvd : p ∣ ∑ k ∈ Finset.range p, k ^ 473582 :=
    dvd_sum_pow_of_not_dvd p hp 473582 (by norm_num) hnd
  have hSpos := sum_range_pow_pos p hp.two_le 473582
  have hS1 : 1 ≤ padicValNat p (∑ k ∈ Finset.range p, k ^ 473582) :=
    one_le_pvn p _ hp hSpos.ne' hdvd
  have hsf : padicValNat p 473583 ≤ 1 := pvn_le1_of_sqfree p 473583 hp (by norm_num) sqfree_473583
  exact val_lb p 473582 (by norm_num) ⟨236791, by norm_num⟩ hsf hS1


-- ===== modular computations (rfl filled at the end) =====
set_option exponentiation.threshold 10000000 in
set_option maxRecDepth 4000000 in
theorem Sval107 : (∑ k ∈ Finset.range 107, k ^ 473582) % 107 ^ 2 = 0 := by rfl
set_option exponentiation.threshold 10000000 in
set_option maxRecDepth 4000000 in
theorem Sval401 : (∑ k ∈ Finset.range 401, k ^ 473582) % 401 ^ 2 = 0 := by rfl
set_option exponentiation.threshold 10000000 in
set_option maxRecDepth 4000000 in
theorem Sval2213 : (∑ k ∈ Finset.range 2213, k ^ 473582) % 2213 ^ 2 = 0 := by rfl
set_option exponentiation.threshold 10000000 in
set_option maxRecDepth 4000000 in
theorem Sval1181 : (∑ k ∈ Finset.range 1181, k ^ 473582) % 1181 ^ 2 = 881026 := by rfl

theorem pvn_Ssq (q : ℕ) (hq : q.Prime) (h : (∑ k ∈ Finset.range q, k ^ 473582) % q ^ 2 = 0) :
    2 ≤ padicValNat q (∑ k ∈ Finset.range q, k ^ 473582) :=
  pvn_ge2_of_sq_dvd q _ hq (sum_range_pow_pos q hq.two_le 473582).ne' (Nat.dvd_of_mod_eq_zero h)

theorem pvn_S1181 : padicValNat 1181 (∑ k ∈ Finset.range 1181, k ^ 473582) = 1 := by
  have hSpos := sum_range_pow_pos 1181 (by norm_num) 473582
  apply pvn_eq1 1181 _ (by norm_num) hSpos.ne'
  · -- 1181 ∣ S
    have hdm : (∑ k ∈ Finset.range 1181, k ^ 473582)
        = 1181 ^ 2 * ((∑ k ∈ Finset.range 1181, k ^ 473582) / 1181 ^ 2) + 881026 := by
      conv_lhs => rw [← Nat.div_add_mod (∑ k ∈ Finset.range 1181, k ^ 473582) (1181 ^ 2)]
      rw [Sval1181]
    rw [hdm]
    exact Dvd.dvd.add (Dvd.dvd.mul_right (dvd_pow_self 1181 (by norm_num)) _) (by norm_num)
  · intro h; obtain ⟨c, hc⟩ := h
    have := Sval1181
    rw [hc, Nat.mul_mod_right] at this
    exact absurd this (by norm_num)

theorem vB1181 : padicValRat 1181 (bernoulli 473582) = 0 := by
  haveI : Fact (Nat.Prime 1181) := ⟨by norm_num⟩
  have hpv473 : padicValNat 1181 473583 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h := val_eq 1181 473582 (by norm_num) ⟨236791, by norm_num⟩
    (by rw [hpv473, pvn_S1181]; norm_num)
  rw [pvn_S1181] at h; simpa using h

theorem vB107 : 1 ≤ padicValRat 107 (bernoulli 473582) := by
  haveI : Fact (Nat.Prime 107) := ⟨by norm_num⟩
  exact val_ge 107 473582 (by norm_num) ⟨236791, by norm_num⟩
    (padicValNat.eq_zero_of_not_dvd (by norm_num)) (pvn_Ssq 107 (by norm_num) Sval107)

theorem vB401 : 1 ≤ padicValRat 401 (bernoulli 473582) := by
  haveI : Fact (Nat.Prime 401) := ⟨by norm_num⟩
  exact val_ge 401 473582 (by norm_num) ⟨236791, by norm_num⟩
    (padicValNat.eq_zero_of_not_dvd (by norm_num)) (pvn_Ssq 401 (by norm_num) Sval401)

theorem vB2213 : 1 ≤ padicValRat 2213 (bernoulli 473582) := by
  haveI : Fact (Nat.Prime 2213) := ⟨by norm_num⟩
  exact val_ge 2213 473582 (by norm_num) ⟨236791, by norm_num⟩
    (padicValNat.eq_zero_of_not_dvd (by norm_num)) (pvn_Ssq 2213 (by norm_num) Sval2213)


theorem a236791_eq : a 236791 = 14172 := by
  apply Nat.eq_of_factorization_eq (a_ne_zero 236791 (by norm_num)) (by norm_num)
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    have key : (padicValNat p (a 236791) : ℤ)
        = max 0 ((padicValNat p (473582 * 473581) : ℤ) - padicValRat p (bernoulli 473582)) := by
      have hav := a_val 236791 p (by norm_num)
      rw [show (2 * 236791 * (2 * 236791 - 1) : ℕ) = 473582 * 473581 from by norm_num,
          show (2 * 236791 : ℕ) = 473582 from by norm_num] at hav
      exact hav
    have goalZ : (padicValNat p (a 236791) : ℤ) = (padicValNat p 14172 : ℤ) := by
      by_cases e2 : p = 2
      · subst e2
        have hvk : padicValNat 2 (473582 * 473581) = 1 := by
          rw [padicValNat.mul (by norm_num) (by norm_num),
              pvn_eq1 2 473582 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (2:ℕ) ∣ 473581 by norm_num)]
        have hr : padicValNat 2 14172 = 2 := by
          rw [show (14172:ℕ) = 2 * (2 * 3543) from by norm_num,
              padicValNat.mul (by norm_num) (by norm_num),
              padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (2:ℕ) ∣ 3543 by norm_num)]
        rw [key, hvk, hr, vB2_eq 473582 (by norm_num) ⟨236791, by norm_num⟩]; omega
      by_cases e3 : p = 3
      · subst e3
        have hvk : padicValNat 3 (473582 * 473581) = 0 := by
          rw [padicValNat.mul (by norm_num) (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (3:ℕ) ∣ 473582 by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (3:ℕ) ∣ 473581 by norm_num)]
        have hr : padicValNat 3 14172 = 1 := by
          rw [show (14172:ℕ) = 3 * 4724 from by norm_num,
              padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (3:ℕ) ∣ 4724 by norm_num)]
        have hv3 : padicValNat 3 473583 ≤ 1 := pvn_le1_of_sqfree 3 473583 (by norm_num) (by norm_num) sqfree_473583
        rw [key, hvk, hr, vB3_eq 473582 (by norm_num) ⟨236791, by norm_num⟩ hv3]; omega
      by_cases e107 : p = 107
      · subst e107
        have hvk : padicValNat 107 (473582 * 473581) = 1 := by
          rw [padicValNat.mul (by norm_num) (by norm_num),
              pvn_eq1 107 473582 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (107:ℕ) ∣ 473581 by norm_num)]
        have hr : padicValNat 107 14172 = 0 := padicValNat.eq_zero_of_not_dvd (ndvd_14172 107 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        rw [key, hvk, hr]; have := vB107; omega
      by_cases e401 : p = 401
      · subst e401
        have hvk : padicValNat 401 (473582 * 473581) = 1 := by
          rw [padicValNat.mul (by norm_num) (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (401:ℕ) ∣ 473582 by norm_num),
              pvn_eq1 401 473581 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        have hr : padicValNat 401 14172 = 0 := padicValNat.eq_zero_of_not_dvd (ndvd_14172 401 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        rw [key, hvk, hr]; have := vB401; omega
      by_cases e1181 : p = 1181
      · subst e1181
        have hvk : padicValNat 1181 (473582 * 473581) = 1 := by
          rw [padicValNat.mul (by norm_num) (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (1181:ℕ) ∣ 473582 by norm_num),
              pvn_eq1 1181 473581 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        have hr : padicValNat 1181 14172 = 1 := by
          rw [show (14172:ℕ) = 1181 * 12 from by norm_num,
              padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (1181:ℕ) ∣ 12 by norm_num)]
        rw [key, hvk, hr, vB1181]; omega
      by_cases e2213 : p = 2213
      · subst e2213
        have hvk : padicValNat 2213 (473582 * 473581) = 1 := by
          rw [padicValNat.mul (by norm_num) (by norm_num),
              pvn_eq1 2213 473582 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
              padicValNat.eq_zero_of_not_dvd (show ¬ (2213:ℕ) ∣ 473581 by norm_num)]
        have hr : padicValNat 2213 14172 = 0 := padicValNat.eq_zero_of_not_dvd (ndvd_14172 2213 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        rw [key, hvk, hr]; have := vB2213; omega
      -- general prime
      have hvk : padicValNat p (473582 * 473581) = 0 := by
        rw [padicValNat.mul (by norm_num) (by norm_num),
            padicValNat.eq_zero_of_not_dvd (ndvd_473582 p hp e2 e107 e2213),
            padicValNat.eq_zero_of_not_dvd (ndvd_473581 p hp e401 e1181)]
      have hr : padicValNat p 14172 = 0 := padicValNat.eq_zero_of_not_dvd (ndvd_14172 p hp e2 e3 e1181)
      rw [key, hvk, hr]; have := vBgen p hp e2 e3; omega
    exact_mod_cast goalZ
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]


theorem oeis_a046969_conjecture_2.disproof :
    ¬ (∀ (n : ℕ), 2 ≤ n → (a n) % 12 = 0 → Nat.Prime ((a n) / 12) →
        (a (n - 1)) % 12 = 0 → (a (n + 2)) % 12 = 0 →
        6 ∣ (((a (n - 1)) / 12 : ℤ) - ((n - 1) : ℤ)) ∧
        6 ∣ (((a n) / 12 : ℤ) - (n : ℤ)) ∧
        6 ∣ (((a (n + 2)) / 12 : ℤ) - ((n + 2) : ℤ))) := by
  intro h
  have hcon := h 236791 (by norm_num)
    (by rw [a236791_eq]) (by rw [a236791_eq]; norm_num)
    (by rw [show (236791 - 1 : ℕ) = 236790 from by norm_num]; exact a236790)
    (by rw [show (236791 + 2 : ℕ) = 236793 from by norm_num]; exact a236793)
  obtain ⟨_, hmid, _⟩ := hcon
  rw [a236791_eq] at hmid
  norm_num at hmid

