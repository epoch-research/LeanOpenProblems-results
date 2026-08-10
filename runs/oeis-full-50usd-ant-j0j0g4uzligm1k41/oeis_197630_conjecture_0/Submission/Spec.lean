import FormalConjectures.Util.ProblemImports
open BigOperators Nat Int

/-!
# A197630 — Sondow's prime-Lerch-quotient conjecture

This file concerns the conjecture (Sondow, OEIS A197630): *13 is the only Lerch quotient
that is prime.*  Here `a n = |ℓ_p|` where `p` is the `n`-th prime and `ℓ_p` is the Lerch
quotient `(∑_{k=1}^{p-1} q_p(k) - w_p)/p`, with `q_p(k) = (k^{p-1}-1)/p` the Fermat quotient
and `w_p = ((p-1)!+1)/p` the Wilson quotient.

We establish the following genuine partial result, which settles the conjecture for *every
prime `p` except those with `p ≡ 1 (mod 4)`*:

* `lerch_dvd` — **Lerch's 1905 congruence** `∑ q_p(k) ≡ w_p (mod p)`, proved here from
  scratch via the product expansion `∏ k^{p-1} = ((p-1)!)^{p-1} ≡ 1 + p·w_p (mod p²)`.
* `pL_eq` — the integer identity `p·(∑ q_p(k) - w_p) = ∑ k^{p-1} - (p-1)! - p`.
* `lower_bound` — `ℓ_p ≥ 3` for `p ≥ 7` (so `ℓ_p ≠ 2`).
* `N_even` — the **parity theorem**: for `p ≡ 3 (mod 4)`, `ℓ_p` is even; hence with
  `ℓ_p ≥ 3` it is composite.

The single remaining case `p ≡ 1 (mod 4)` is the open core of Sondow's conjecture: the
Lerch quotients are then odd and structureless (e.g. `ℓ_37 = 347 · (a 51-digit prime)`,
`ℓ_13 = 47·613·2756483`), with unbounded least prime factor, so no covering congruence or
algebraic factorisation can decide their primality.  No proof is known in the literature,
and a counterexample is impossible to certify (all primes among the Lerch quotients within
reach are composite, the only prime value being `ℓ_5 = 13`).  This case is left as `sorry`.
-/

def fermat_quotient_int (k p : ℕ) : ℤ := (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))

-- Fermat exactness in ℤ: if p prime and ¬ p ∣ k then p ∣ (k^(p-1) - 1)
theorem fermat_dvd (p k : ℕ) [Fact p.Prime] (hk : ¬ (p : ℤ) ∣ (k : ℤ)) :
    (p : ℤ) ∣ ((k : ℤ) ^ (p - 1) - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hk0 : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact hk (by exact_mod_cast (Int.natCast_dvd_natCast.mpr h))
  rw [ZMod.pow_card_sub_one_eq_one hk0]; ring

-- representation: k^(p-1) = 1 + p * q
theorem fermat_repr (p k : ℕ) [Fact p.Prime] (hk : ¬ (p : ℤ) ∣ (k : ℤ)) :
    (k : ℤ) ^ (p - 1) = 1 + (p : ℤ) * fermat_quotient_int k p := by
  unfold fermat_quotient_int
  rw [Int.mul_ediv_cancel' (fermat_dvd p k hk)]; ring

def wilson_quotient_int (p : ℕ) : ℤ := ((p - 1).factorial + 1) / (p : ℤ)

theorem wilson_dvd (p : ℕ) [Fact p.Prime] : (p : ℤ) ∣ (((p-1).factorial : ℤ) + 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.wilsons_lemma p]; ring

theorem wilson_repr (p : ℕ) [Fact p.Prime] :
    ((p-1).factorial : ℤ) = (p : ℤ) * wilson_quotient_int p - 1 := by
  unfold wilson_quotient_int
  rw [Int.mul_ediv_cancel' (wilson_dvd p)]; ring

-- Product mod p²:  p² ∣ (∏ (1 + p*q k)) - (1 + p * ∑ q k)
theorem prod_one_add (p : ℤ) {ι : Type*} (s : Finset ι) (q : ι → ℤ) :
    p^2 ∣ (∏ k ∈ s, (1 + p * q k)) - (1 + p * ∑ k ∈ s, q k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    obtain ⟨c, hc⟩ := ih
    have hP : (∏ k ∈ s, (1 + p * q k)) = 1 + p * ∑ k ∈ s, q k + p^2 * c := by linarith [hc]
    refine ⟨q a * (∑ k ∈ s, q k) + c + p * q a * c, ?_⟩
    rw [hP]; ring

theorem onepow_sub (y : ℤ) (n : ℕ) : y^2 ∣ ((1 + y)^n - (1 + n*y)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(m : ℤ) + c + y*c, ?_⟩
    have e : (1+y)^(m+1) = (1+y)^m * (1+y) := pow_succ _ _
    have h2 : (1+y)^m = 1 + m*y + y^2 * c := by linarith [hc]
    rw [e, h2]; push_cast; ring

-- Lerch's congruence: p ∣ (sum_q - w)
theorem lerch_dvd (p : ℕ) [Fact p.Prime] (hp : 2 ≤ p) (hodd : Odd p) :
    (p : ℤ) ∣ ((∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p) - wilson_quotient_int p) := by
  set q : ℕ → ℤ := fun k => fermat_quotient_int (k+1) p with hq
  set w : ℤ := wilson_quotient_int p with hw
  have hcop : ∀ k ∈ Finset.range (p-1), ¬ (p:ℤ) ∣ ((k:ℤ)+1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : (k:ℤ) + 1 = ((k+1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.natCast_dvd_natCast]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hprodeq : (∏ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) = ∏ k ∈ Finset.range (p-1), (1 + (p:ℤ) * q k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hf := fermat_repr p (k+1) (by push_cast; exact hcop k hk)
    push_cast at hf ⊢
    rw [hf]
  have hfact : (∏ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) = (((p-1).factorial : ℤ))^(p-1) := by
    rw [Finset.prod_pow]
    congr 1
    rw [Nat.factorial_eq_prod_range_add_one]
    push_cast
    rfl
  -- D1: p² | ∏(1+pq) - (1 + p Σq)
  have D1 := prod_one_add (p:ℤ) (Finset.range (p-1)) q
  -- E: ∏(1+pq) = ((p-1)!)^(p-1)
  have E : (∏ k ∈ Finset.range (p-1), (1 + (p:ℤ) * q k)) = (((p-1).factorial : ℤ))^(p-1) :=
    hprodeq.symm.trans hfact
  -- D2: p² | ((p-1)!)^(p-1) - (1 + p w)
  have heven : Even (p - 1) := by rcases hodd with ⟨m, rfl⟩; exact ⟨m, by omega⟩
  have hwr := wilson_repr p
  have D2 : (p:ℤ)^2 ∣ (((p-1).factorial : ℤ))^(p-1) - (1 + (p:ℤ)*w) := by
    rw [hwr]
    -- (p*w - 1)^(p-1) = (1 + (-(p*w)))^(p-1)
    have key : ((p:ℤ)*w - 1)^(p-1) = (1 + (-(p:ℤ)*w))^(p-1) := by
      have h : (p:ℤ)*w - 1 = -(1 + (-(p:ℤ)*w)) := by ring
      rw [h, Even.neg_pow heven]
    rw [key]
    have hop := onepow_sub (-(p:ℤ)*w) (p-1)
    have hp2 : (p:ℤ)^2 ∣ (-(p:ℤ)*w)^2 := ⟨w^2, by ring⟩
    have hA : (p:ℤ)^2 ∣ (1 + (-(p:ℤ)*w))^(p-1) - (1 + ((p-1:ℕ):ℤ)*(-(p:ℤ)*w)) := hp2.trans hop
    have hB : (p:ℤ)^2 ∣ (1 + ((p-1:ℕ):ℤ)*(-(p:ℤ)*w)) - (1 + (p:ℤ)*w) := by
      have hcast : ((p-1:ℕ):ℤ) = (p:ℤ) - 1 := by
        have : 1 ≤ p := by omega
        push_cast [this]; ring
      refine ⟨-w, ?_⟩
      rw [hcast]; ring
    have := dvd_add hA hB
    have e2 : ((1 + (-(p:ℤ)*w))^(p-1) - (1 + ((p-1:ℕ):ℤ)*(-(p:ℤ)*w)))
            + ((1 + ((p-1:ℕ):ℤ)*(-(p:ℤ)*w)) - (1 + (p:ℤ)*w))
          = (1 + (-(p:ℤ)*w))^(p-1) - (1 + (p:ℤ)*w) := by ring
    rwa [e2] at this
  -- combine and cancel one factor of p
  have Dcomb : (p:ℤ)^2 ∣ ((1 + (p:ℤ) * ∑ k ∈ Finset.range (p-1), q k) - (1 + (p:ℤ)*w)) := by
    have h := dvd_sub D2 D1
    rw [← E] at h
    have e : ((∏ k ∈ Finset.range (p-1), (1 + (p:ℤ) * q k)) - (1 + (p:ℤ)*w))
           - ((∏ k ∈ Finset.range (p-1), (1 + (p:ℤ) * q k)) - (1 + (p:ℤ) * ∑ k ∈ Finset.range (p-1), q k))
         = (1 + (p:ℤ) * ∑ k ∈ Finset.range (p-1), q k) - (1 + (p:ℤ)*w) := by ring
    rwa [e] at h
  have hx : (1 + (p:ℤ) * ∑ k ∈ Finset.range (p-1), q k) - (1 + (p:ℤ)*w)
          = (p:ℤ) * ((∑ k ∈ Finset.range (p-1), q k) - w) := by ring
  rw [hx] at Dcomb
  have hpp : (p:ℤ)^2 = (p:ℤ) * (p:ℤ) := by ring
  rw [hpp] at Dcomb
  have hpne : (p:ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_dvd_mul_iff_left hpne).mp Dcomb


-- Integer identity: p * L = S - (p-1)! - p
theorem pL_eq (p : ℕ) [Fact p.Prime] (hp : 2 ≤ p) :
    (p : ℤ) * ((∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p) - wilson_quotient_int p)
    = (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial : ℤ) - p := by
  have hcop : ∀ k ∈ Finset.range (p-1), ¬ (p:ℤ) ∣ ((k:ℤ)+1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : (k:ℤ) + 1 = ((k+1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.natCast_dvd_natCast]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hpq : (p:ℤ) * (∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p)
           = (∑ k ∈ Finset.range (p-1), (((k:ℤ)+1)^(p-1) - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    unfold fermat_quotient_int
    have hdvd : (p:ℤ) ∣ ((↑(k+1):ℤ)^(p-1) - 1) := fermat_dvd p (k+1) (by push_cast; exact hcop k hk)
    push_cast at hdvd ⊢
    exact Int.mul_ediv_cancel' hdvd
  have hpw : (p:ℤ) * wilson_quotient_int p = ((p-1).factorial : ℤ) + 1 := by
    unfold wilson_quotient_int
    rw [Int.mul_ediv_cancel' (wilson_dvd p)]
  have hcard : (∑ k ∈ Finset.range (p-1), (1:ℤ)) = ((p:ℤ) - 1) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    simp [Nat.cast_sub (show 1 ≤ p by omega)]
  rw [mul_sub, hpq, hpw, Finset.sum_sub_distrib, hcard]
  ring


theorem lower_bound (p : ℕ) (hp : 7 ≤ p) :
    3*(p:ℤ)^2 ≤ (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p := by
  set S : ℤ := ∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1) with hS
  -- two-term lower bound on S
  have hsub : ({p-3, p-2} : Finset ℕ) ⊆ Finset.range (p-1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  have hpair : (p-3 : ℕ) ≠ p-2 := by omega
  have hnonneg : ∀ i ∈ Finset.range (p-1), i ∉ ({p-3, p-2} : Finset ℕ) → 0 ≤ ((i:ℤ)+1)^(p-1) := by
    intro i _ _; positivity
  have htwo := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  rw [Finset.sum_pair hpair] at htwo
  -- identify the two terms
  have e1 : (((p-3:ℕ):ℤ) + 1) = (p:ℤ) - 2 := by
    have : ((p-3:ℕ):ℤ) = (p:ℤ) - 3 := by push_cast [Nat.cast_sub (by omega : 3 ≤ p)]; ring
    rw [this]; ring
  have e2 : (((p-2:ℕ):ℤ) + 1) = (p:ℤ) - 1 := by
    have : ((p-2:ℕ):ℤ) = (p:ℤ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ p)]; ring
    rw [this]; ring
  rw [e1, e2] at htwo
  -- factorial bound: (p-1)! ≤ (p-1)^(p-1) = (p-1:ℤ)^(p-1)
  have hxge : (7:ℤ) ≤ (p:ℤ) := by exact_mod_cast hp
  have hfac : ((p-1).factorial : ℤ) ≤ ((p:ℤ)-1)^(p-1) := by
    have h := Nat.factorial_le_pow (p-1)
    have hc : (((p-1)^(p-1) : ℕ) : ℤ) = ((p:ℤ)-1)^(p-1) := by
      rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    calc ((p-1).factorial : ℤ) ≤ (((p-1)^(p-1) : ℕ):ℤ) := by exact_mod_cast h
      _ = ((p:ℤ)-1)^(p-1) := hc
  -- power bound: (p-2)^4 ≤ (p-2)^(p-1)
  have hpow : ((p:ℤ)-2)^4 ≤ ((p:ℤ)-2)^(p-1) := by
    apply pow_le_pow_right₀
    · linarith
    · omega
  -- polynomial: 3p²+p ≤ (p-2)^4
  have hpoly : 3*(p:ℤ)^2 + p ≤ ((p:ℤ)-2)^4 := by
    nlinarith [hxge, sq_nonneg ((p:ℤ)-7), sq_nonneg ((p:ℤ)-2)]
  -- combine
  have hp2pos : (0:ℤ) ≤ ((p:ℤ)-2)^(p-1) := pow_nonneg (by linarith) _
  linarith [htwo, hfac, hpow, hpoly]


theorem zmod2_pow (e : ℕ) (he : 1 ≤ e) (a : ZMod 2) : a^e = a := by
  fin_cases a
  · exact zero_pow (by omega)
  · exact one_pow _

theorem N_even (p : ℕ) (hp3 : p % 4 = 3) (hpge : 3 ≤ p) :
    (2:ℤ) ∣ ((∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p) := by
  rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hfac0 : (((p-1).factorial : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_factorial (by norm_num) (by omega)
  have hp1 : ((p:ℕ) : ZMod 2) = 1 := by
    have h : p % 2 = 1 := by omega
    calc ((p:ℕ):ZMod 2) = ((p % 2 : ℕ) : ZMod 2) := by rw [ZMod.natCast_mod]
      _ = 1 := by rw [h]; rfl
  have hsum : (∑ k ∈ Finset.range (p-1), ((k:ZMod 2)+1)^(p-1))
            = ∑ k ∈ Finset.range (p-1), ((k:ZMod 2)+1) := by
    apply Finset.sum_congr rfl; intro k _; exact zmod2_pow (p-1) (by omega) _
  have hcast : (∑ k ∈ Finset.range (p-1), ((k:ZMod 2)+1))
             = (((∑ k ∈ Finset.range (p-1), (k+1)) : ℕ) : ZMod 2) := by
    push_cast; rfl
  obtain ⟨m, rfl⟩ : ∃ m, p = 4*m+3 := ⟨p/4, by omega⟩
  have he1 : 4*m+3-1 = 4*m+2 := by omega
  have hi : (∑ i ∈ Finset.range (4*m+3-1), i) = 8*m^2 + 6*m + 1 := by
    have h2 := Finset.sum_range_id_mul_two (4*m+3-1)
    have key : (4*m+3-1) * (4*m+3-1-1) = (8*m^2+6*m+1)*2 := by
      rw [he1, show 4*m+2-1 = 4*m+1 from by omega]; ring
    rw [key] at h2; omega
  have hT : (∑ k ∈ Finset.range (4*m+3-1), (k+1)) = 8*m^2+10*m+3 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, hi]
    simp only [smul_eq_mul, mul_one]; rw [he1]; ring
  have hsumodd : ((8*m^2+10*m+3 : ℕ) : ZMod 2) = 1 := by
    rw [show (8*m^2+10*m+3 : ℕ) = 2*(4*m^2+5*m+1) + 1 from by ring,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self]; ring
  rw [hsum, hcast, hT, hsumodd, hfac0, hp1]; ring


noncomputable def a (n : ℕ) : ℕ :=
  if 1 < n then
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let p_z : ℤ := p_n
    let sum_q : ℤ := Finset.sum (Finset.range (p_n - 1)) (fun k : ℕ => fermat_quotient_int (k + 1) p_n)
    let L_p : ℤ := sum_q - wilson_quotient_int p_n
    (L_p / p_z).natAbs
  else
    0

-- key: for p ≥ 7 odd prime, (a-value).toInt satisfies p² * val = N, val ≥ 3, parity
theorem a_props (m : ℕ) :
    let p := Nat.nth Nat.Prime (m+3)
    7 ≤ p ∧ Odd p ∧
    ((p:ℤ)^2 * ((a (m+4)) : ℤ)
      = (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p)
    ∧ 3 ≤ ((a (m+4)) : ℤ) := by
  intro p
  haveI : Fact p.Prime := ⟨Nat.prime_nth_prime _⟩
  have hprime : p.Prime := Nat.prime_nth_prime _
  have hge : 7 ≤ p := by
    have hmono : Nat.nth Nat.Prime 3 ≤ Nat.nth Nat.Prime (m+3) :=
      Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
    have h7 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
    omega
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  refine ⟨hge, hodd, ?_, ?_⟩
  · -- p² * a = N
    have hdvd : (p:ℤ) ∣ ((∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p) - wilson_quotient_int p) :=
      lerch_dvd p (by omega) hodd
    set L : ℤ := (∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p) - wilson_quotient_int p with hLdef
    have hpz : (p:ℤ) * (L / (p:ℤ)) = L := Int.mul_ediv_cancel' hdvd
    have hN : (p:ℤ) * L = (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p :=
      pL_eq p (by omega)
    have hp2z : (p:ℤ)^2 * (L / (p:ℤ)) = (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p := by
      rw [sq, mul_assoc, hpz, hN]
    -- a (m+4) value: natAbs of L/p, and L/p ≥ 0
    have hN3 : 3*(p:ℤ)^2 ≤ (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p :=
      lower_bound p hge
    have hp2pos : (0:ℤ) < (p:ℤ)^2 := by positivity
    have hzge : 3 ≤ L / (p:ℤ) := by
      have hh : (p:ℤ)^2 * 3 ≤ (p:ℤ)^2 * (L / (p:ℤ)) := by rw [hp2z]; linarith [hN3]
      exact Int.le_of_mul_le_mul_left hh hp2pos
    have ha_eq : a (m+4) = (L / (p:ℤ)).natAbs := by
      rw [hLdef]; rfl
    have hcast : ((a (m+4)) : ℤ) = L / (p:ℤ) := by
      rw [ha_eq, Int.natAbs_of_nonneg (by linarith)]
    rw [hcast]; exact hp2z
  · -- 3 ≤ a
    have hdvd : (p:ℤ) ∣ ((∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p) - wilson_quotient_int p) :=
      lerch_dvd p (by omega) hodd
    set L : ℤ := (∑ k ∈ Finset.range (p-1), fermat_quotient_int (k+1) p) - wilson_quotient_int p with hLdef
    have hpz : (p:ℤ) * (L / (p:ℤ)) = L := Int.mul_ediv_cancel' hdvd
    have hN : (p:ℤ) * L = (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p :=
      pL_eq p (by omega)
    have hp2z : (p:ℤ)^2 * (L / (p:ℤ)) = (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p := by
      rw [sq, mul_assoc, hpz, hN]
    have hN3 : 3*(p:ℤ)^2 ≤ (∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p :=
      lower_bound p hge
    have hp2pos : (0:ℤ) < (p:ℤ)^2 := by positivity
    have hzge : 3 ≤ L / (p:ℤ) := by
      have hh : (p:ℤ)^2 * 3 ≤ (p:ℤ)^2 * (L / (p:ℤ)) := by rw [hp2z]; linarith [hN3]
      exact Int.le_of_mul_le_mul_left hh hp2pos
    have ha_eq : a (m+4) = (L / (p:ℤ)).natAbs := by
      rw [hLdef]; rfl
    rw [ha_eq, Int.natAbs_of_nonneg (by linarith)]; exact hzge

theorem oeis_197630_conjecture_0 : ∀ n : ℕ, 1 < n → Nat.Prime (a n) → a n = 13 := by
  intro n hn hprime
  match n, hn with
  | 2, _ =>
      have h2 : a 2 = 0 := by
        have h : Nat.nth Nat.Prime (2 - 1) = 3 := by simpa using Nat.n_one_eq_three
        unfold a; rw [if_pos (by norm_num)]; simp only [h]; decide
      rw [h2] at hprime; exact absurd hprime (by decide)
  | 3, _ =>
      have h : Nat.nth Nat.Prime (3 - 1) = 5 := by simpa using Nat.n_two_eq_five
      unfold a; rw [if_pos (by norm_num)]; simp only [h]; decide
  | (m + 4), _ =>
      obtain ⟨hge, hodd, hp2z, hge3⟩ := a_props m
      set p := Nat.nth Nat.Prime (m+3) with hp_def
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hodd with ⟨t, ht⟩; omega
      rcases hp4 with h1 | h3
      · -- p ≡ 1 (mod 4): the open core of Sondow's conjecture
        sorry
      · -- p ≡ 3 (mod 4): the Lerch quotient is even and ≥ 3, hence composite
        exfalso
        have hNeven : (2:ℤ) ∣ ((∑ k ∈ Finset.range (p-1), ((k:ℤ)+1)^(p-1)) - ((p-1).factorial:ℤ) - p) :=
          N_even p h3 (by omega)
        rw [← hp2z] at hNeven
        have hNevenNat : 2 ∣ (p^2 * a (m+4)) := by
          have hcast : ((p^2 * a (m+4) : ℕ):ℤ) = (p:ℤ)^2 * (a (m+4):ℤ) := by push_cast; ring
          rw [← hcast] at hNeven; exact_mod_cast hNeven
        have hp2oddN : Odd (p^2) := hodd.pow
        have hdvd2 : 2 ∣ a (m+4) := by
          rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hNevenNat with h | h
          · exact absurd h (fun hd => by
              rcases hd with ⟨c, hc⟩; have := Nat.odd_iff.mp hp2oddN; omega)
          · exact h
        have ha2 : 2 = a (m+4) := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp hdvd2
        have h3le : 3 ≤ a (m+4) := by exact_mod_cast hge3
        omega
