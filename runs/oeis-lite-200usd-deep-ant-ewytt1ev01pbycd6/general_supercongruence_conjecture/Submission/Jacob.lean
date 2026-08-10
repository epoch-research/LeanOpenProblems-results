import Submission.Wolstenholme

open Finset

namespace Jacob

open Polynomial

/-- For a prime `p`, `(p-1).choose j ≡ (-1)^j (mod p)` for `j ≤ p-1`. -/
lemma choose_pred_congr (p : ℕ) (hp : p.Prime) :
    ∀ j : ℕ, j ≤ p - 1 → ((Nat.choose (p - 1) j : ZMod p)) = (-1) ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hp1 : p - 1 + 1 = p := by omega
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnle : n ≤ p - 1 := by omega
    have hIH := ih hnle
    have pascal : Nat.choose p (n + 1) = Nat.choose (p - 1) n + Nat.choose (p - 1) (n + 1) := by
      have h : Nat.choose (p - 1 + 1) (n + 1)
          = Nat.choose (p - 1) n + Nat.choose (p - 1) (n + 1) := Nat.choose_succ_succ (p - 1) n
      rwa [hp1] at h
    have hdvd : p ∣ Nat.choose p (n + 1) :=
      hp.dvd_choose_self (by omega) (by omega)
    have hzero : ((Nat.choose p (n + 1) : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hdvd
    have hcast : ((Nat.choose p (n + 1) : ℕ) : ZMod p)
        = ((Nat.choose (p - 1) n : ℕ) : ZMod p) + ((Nat.choose (p - 1) (n + 1) : ℕ) : ZMod p) := by
      rw [pascal]; push_cast; ring
    rw [hzero, hIH] at hcast
    -- 0 = (-1)^n + choose (p-1) (n+1)
    have : ((Nat.choose (p - 1) (n + 1) : ℕ) : ZMod p) = (-1) ^ (n + 1) := by
      have := hcast.symm
      rw [pow_succ]
      linear_combination this
    exact this

/-- KEY divisibility: `p ∣ ∑_{ij} (C(p,i)/p)(C(p,j)/p)` over the antidiagonal of `p`. -/
lemma key_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ ∑ ij ∈ Finset.antidiagonal p,
        (Nat.choose p ij.1 / p) * (Nat.choose p ij.2 / p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  -- define g
  set g : ℕ → ZMod p := fun k => ((Nat.choose p k / p : ℕ) : ZMod p) with hg_def
  -- convert antidiagonal to range
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij => ((Nat.choose p ij.1 / p : ℕ) : ZMod p) * ((Nat.choose p ij.2 / p : ℕ) : ZMod p)) p]
  -- key formula for g k
  have hgk : ∀ k, 1 ≤ k → k ≤ p - 1 → g k = (-1) ^ (k - 1) * (k : ZMod p)⁻¹ := by
    intro k hk1 hk2
    -- nat identity: choose (p-1) (k-1) = (choose p k / p) * k
    have hdvd : p ∣ Nat.choose p k := hp.dvd_choose_self (by omega) (by omega)
    have hmul : p * Nat.choose (p - 1) (k - 1) = Nat.choose p k * k := by
      have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
      rw [show p - 1 + 1 = p from by omega, show k - 1 + 1 = k from by omega] at h
      exact h
    have hdivcancel : p * (Nat.choose p k / p) = Nat.choose p k := Nat.mul_div_cancel' hdvd
    have hnatid : Nat.choose (p - 1) (k - 1) = (Nat.choose p k / p) * k := by
      have key : p * Nat.choose (p - 1) (k - 1) = p * ((Nat.choose p k / p) * k) := by
        rw [hmul, ← Nat.mul_assoc, hdivcancel]
      exact Nat.eq_of_mul_eq_mul_left hp.pos key
    -- cast
    have hcast : ((Nat.choose (p - 1) (k - 1) : ℕ) : ZMod p) = g k * (k : ZMod p) := by
      simp only [hg_def]
      rw [hnatid]; push_cast; ring
    have hcp : ((Nat.choose (p - 1) (k - 1) : ℕ) : ZMod p) = (-1) ^ (k - 1) :=
      choose_pred_congr p hp (k - 1) (by omega)
    rw [hcp] at hcast
    -- k ≠ 0 in ZMod p
    have hk0 : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdk
      have := Nat.le_of_dvd (by omega) hdk
      omega
    have hkinv : (k : ZMod p) * (k : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hk0
    calc g k = g k * ((k : ZMod p) * (k : ZMod p)⁻¹) := by rw [hkinv, mul_one]
      _ = (g k * (k : ZMod p)) * (k : ZMod p)⁻¹ := by ring
      _ = (-1) ^ (k - 1) * (k : ZMod p)⁻¹ := by rw [← hcast]
  -- term formula
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hterm : ∀ k, 1 ≤ k → k ≤ p - 1 → g k * g (p - k) = ((k : ZMod p)⁻¹) ^ 2 := by
    intro k hk1 hk2
    have e1 := hgk k hk1 hk2
    have e2 := hgk (p - k) (by omega) (by omega)
    have hcast : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    have hpow : (-1 : ZMod p) ^ (k - 1) * (-1) ^ ((p - k) - 1) = -1 := by
      rw [← pow_add]
      have hexp : (k - 1) + ((p - k) - 1) = p - 2 := by omega
      rw [hexp]
      have hodd : Odd (p - 2) := Nat.Odd.sub_even (by omega) hpodd (by norm_num)
      exact Odd.neg_one_pow hodd
    rw [e1, e2, hcast, inv_neg]
    calc (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ * ((-1) ^ ((p - k) - 1) * -(k : ZMod p)⁻¹)
        = -((-1) ^ (k - 1) * (-1) ^ ((p - k) - 1)) * ((k : ZMod p)⁻¹ * (k : ZMod p)⁻¹) := by ring
      _ = -(-1) * ((k : ZMod p)⁻¹ * (k : ZMod p)⁻¹) := by rw [hpow]
      _ = ((k : ZMod p)⁻¹) ^ 2 := by ring
  -- reduce range sum to Icc sum
  have hsub : Finset.Icc 1 (p - 1) ⊆ Finset.range (p + 1) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]; omega
  have hgp : g p = 0 := by
    simp only [hg_def]
    rw [Nat.choose_self, Nat.div_eq_of_lt (by omega)]
    simp
  have hg0 : g 0 = 0 := by
    simp only [hg_def]
    rw [Nat.choose_zero_right, Nat.div_eq_of_lt (by omega)]
    simp
  have hrange : ∑ k ∈ Finset.range (p + 1), g k * g (p - k)
      = ∑ k ∈ Finset.Icc 1 (p - 1), g k * g (p - k) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hxni
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hxni
    push_neg at hxni
    -- x = 0 or x = p
    have : x = 0 ∨ x = p := by omega
    rcases this with h0 | hp'
    · rw [h0]; simp [hg0]
    · rw [hp']; simp [hgp]
  -- final
  show ∑ k ∈ Finset.range (p + 1), g k * g (p - k) = 0
  rw [hrange]
  have : ∑ k ∈ Finset.Icc 1 (p - 1), g k * g (p - k)
      = ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact hterm k hk.1 hk.2
  rw [this]
  exact Wolst.sum_inv_sq p hp5

/-- The congruence `C(p*a, p*b) ≡ C(a,b)` in any commutative ring `R` where `(p:R)^3 = 0`. -/
lemma choose_mul_congr_aux {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp3 : (p : R) ^ 3 = 0) (a b : ℕ) :
    ((Nat.choose (p * a) (p * b) : R)) = (Nat.choose a b : R) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  -- The polynomial Q with Q.coeff k = ↑(C(p,k)/p)
  set Q : R[X] := ∑ k ∈ Finset.Icc 1 (p - 1),
      Polynomial.monomial k ((Nat.choose p k / p : ℕ) : R) with hQdef
  -- nat fact: C(p,i)/p = 0 for i outside [1,p-1]
  have hQnat : ∀ i, ¬ (1 ≤ i ∧ i ≤ p - 1) → Nat.choose p i / p = 0 := by
    intro i hi
    rw [not_and_or] at hi
    rcases hi with h | h
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [Nat.choose_zero_right]
      exact Nat.div_eq_of_lt (by omega)
    · have hip : p ≤ i := by omega
      rcases eq_or_lt_of_le hip with h1 | h1
      · rw [← h1, Nat.choose_self]
        exact Nat.div_eq_of_lt (by omega)
      · rw [Nat.choose_eq_zero_of_lt h1, Nat.zero_div]
  -- coeff of Q
  have hQc : ∀ i, Q.coeff i = ((Nat.choose p i / p : ℕ) : R) := by
    intro i
    rw [hQdef, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 (p - 1)) i
        (fun k => ((Nat.choose p k / p : ℕ) : R))]
    by_cases hi : i ∈ Finset.Icc 1 (p - 1)
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Finset.mem_Icc] at hi
      rw [hQnat i hi]; simp
  -- Q vanishes outside [1,p-1]
  have hQout : ∀ i, ¬ (1 ≤ i ∧ i ≤ p - 1) → Q.coeff i = 0 := by
    intro i hi
    rw [hQc, hQnat i hi]; simp
  -- Q vanishes at multiples of p
  have hQsupp : ∀ j, p ∣ j → Q.coeff j = 0 := by
    intro j hj
    apply hQout
    rintro ⟨h1, h2⟩
    have := Nat.le_of_dvd (by omega) hj
    omega
  -- coeff of (1 + X^p)^n
  have hAcoeff : ∀ (n i : ℕ), ((1 + X ^ p : R[X]) ^ n).coeff i
      = if p ∣ i then ((Nat.choose n (i / p) : ℕ) : R) else 0 := by
    intro n i
    have hexp : Polynomial.expand R p ((1 + X) ^ n) = (1 + X ^ p) ^ n := by
      rw [map_pow, map_add, map_one, Polynomial.expand_X]
    rw [← hexp, Polynomial.coeff_expand (show 0 < p by omega)]
    by_cases hpi : p ∣ i
    · rw [if_pos hpi, if_pos hpi, Polynomial.coeff_one_add_X_pow]
    · rw [if_neg hpi, if_neg hpi]
  -- (1 + X^p)^n vanishes off multiples of p
  have hAsupp : ∀ (n i : ℕ), ¬ (p ∣ i) → ((1 + X ^ p : R[X]) ^ n).coeff i = 0 := by
    intro n i hi
    rw [hAcoeff n i, if_neg hi]
  -- product of a poly supported on multiples of p with one that vanishes there
  have hprodzero : ∀ (A B : R[X]), (∀ i, ¬ (p ∣ i) → A.coeff i = 0) →
      (∀ j, p ∣ j → B.coeff j = 0) → ∀ m, p ∣ m → (A * B).coeff m = 0 := by
    intro A B hA hB m hm
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases h1 : p ∣ ij.1
    · have hm' : p ∣ ij.1 + ij.2 := by rw [hij]; exact hm
      have h2 : p ∣ ij.2 := (Nat.dvd_add_right h1).mp hm'
      rw [hB ij.2 h2, mul_zero]
    · rw [hA ij.1 h1, zero_mul]
  -- coeff of Q^2 at p equals the cast of the antidiagonal sum
  have hcoeffp : (Q ^ 2).coeff p
      = ((∑ ij ∈ Finset.antidiagonal p,
          (Nat.choose p ij.1 / p) * (Nat.choose p ij.2 / p) : ℕ) : R) := by
    rw [pow_two, Polynomial.coeff_mul, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ij _
    rw [hQc ij.1, hQc ij.2, Nat.cast_mul]
  -- key: p^2 * coeff at multiples of p of Q^2 is zero
  have hQsqzero : ∀ j, p ∣ j → (p : R) ^ 2 * (Q ^ 2).coeff j = 0 := by
    intro j hj
    by_cases hjp : j = p
    · rw [hjp, hcoeffp]
      obtain ⟨S', hS'⟩ := key_dvd p hp hp5
      rw [hS']
      have hrw : (p : R) ^ 2 * ((p * S' : ℕ) : R) = (p : R) ^ 3 * (S' : R) := by
        push_cast; ring
      rw [hrw, hp3, zero_mul]
    · have hz : (Q ^ 2).coeff j = 0 := by
        rw [pow_two, Polynomial.coeff_mul]
        apply Finset.sum_eq_zero
        intro ij hij
        rw [Finset.mem_antidiagonal] at hij
        by_cases c1 : 1 ≤ ij.1 ∧ ij.1 ≤ p - 1
        · by_cases c2 : 1 ≤ ij.2 ∧ ij.2 ≤ p - 1
          · exfalso
            obtain ⟨t, rfl⟩ := hj
            have h1 : t < 2 := by
              have hlt : p * t < p * 2 := by omega
              exact Nat.lt_of_mul_lt_mul_left hlt
            interval_cases t
            · omega
            · exact hjp (mul_one p)
          · rw [hQout ij.2 c2, mul_zero]
        · rw [hQout ij.1 c1, zero_mul]
      rw [hz, mul_zero]
  -- (p^2 • Q^2) vanishes at multiples of p
  have hBsupp : ∀ j, p ∣ j → ((p : R) ^ 2 • Q ^ 2).coeff j = 0 := by
    intro j hj
    rw [Polynomial.coeff_smul, smul_eq_mul]
    exact hQsqzero j hj
  -- the fundamental identity (1+X)^p = 1 + X^p + p • Q
  have hP : ((1 + X : R[X])) ^ p = (1 + X ^ p) + (p : R) • Q := by
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_one_add_X_pow, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_smul, hQc, smul_eq_mul]
    by_cases h0 : n = 0
    · rw [if_pos h0, if_neg (show ¬ n = p by omega)]
      subst h0
      rw [Nat.choose_zero_right, Nat.div_eq_of_lt (show 1 < p by omega)]
      simp
    · by_cases hp' : n = p
      · rw [if_neg h0, if_pos hp', hp']
        rw [Nat.choose_self, Nat.div_eq_of_lt (show 1 < p by omega)]
        simp
      · rw [if_neg h0, if_neg hp']
        by_cases hle : n ≤ p - 1
        · have hdvd : p ∣ Nat.choose p n := hp.dvd_choose_self h0 (by omega)
          have hc : p * (Nat.choose p n / p) = Nat.choose p n := Nat.mul_div_cancel' hdvd
          have hcR : ((Nat.choose p n : ℕ) : R) = (p : R) * ((Nat.choose p n / p : ℕ) : R) := by
            rw [← Nat.cast_mul, hc]
          rw [hcR]; ring
        · have hgt : p < n := by omega
          rw [Nat.choose_eq_zero_of_lt hgt]
          simp
  -- main computation
  rw [show ((Nat.choose (p * a) (p * b) : R)) = ((1 + X : R[X]) ^ (p * a)).coeff (p * b) from
        (Polynomial.coeff_one_add_X_pow R (p * a) (p * b)).symm,
      pow_mul, hP, add_pow, Polynomial.finset_sum_coeff]
  refine Eq.trans (Finset.sum_eq_single a ?_ ?_) ?_
  · -- terms with k ≠ a vanish
    intro k hk hka
    rw [Finset.mem_range] at hk
    rw [_root_.smul_pow, ← map_natCast (Polynomial.C) (Nat.choose a k),
        Polynomial.coeff_mul_C, mul_smul_comm, Polynomial.coeff_smul, smul_eq_mul]
    have hinner : (p : R) ^ (a - k) * ((1 + X ^ p : R[X]) ^ k * Q ^ (a - k)).coeff (p * b) = 0 := by
      rcases Nat.lt_or_ge (a - k) 3 with hlt3 | hge3
      · have hl2 : a - k = 1 ∨ a - k = 2 := by omega
        rcases hl2 with h1 | h2
        · simp only [h1, pow_one]
          rw [hprodzero ((1 + X ^ p) ^ k) Q (hAsupp k) hQsupp (p * b) ⟨b, rfl⟩, mul_zero]
        · simp only [h2]
          rw [show (p : R) ^ 2 * ((1 + X ^ p : R[X]) ^ k * Q ^ 2).coeff (p * b)
                = ((1 + X ^ p : R[X]) ^ k * ((p : R) ^ 2 • Q ^ 2)).coeff (p * b) from by
              rw [mul_smul_comm, Polynomial.coeff_smul, smul_eq_mul]]
          exact hprodzero ((1 + X ^ p) ^ k) ((p : R) ^ 2 • Q ^ 2) (hAsupp k) hBsupp (p * b) ⟨b, rfl⟩
      · have hz : (p : R) ^ (a - k) = 0 := by
          obtain ⟨d, hd⟩ : ∃ d, a - k = 3 + d := ⟨a - k - 3, by omega⟩
          rw [hd, pow_add, hp3, zero_mul]
        rw [hz, zero_mul]
    rw [hinner, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self a)) h
  · -- the k = a term equals C(a,b)
    rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
    rw [hAcoeff a (p * b), if_pos ⟨b, rfl⟩, Nat.mul_div_cancel_left b hp.pos]

theorem jacobsthal_base (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℕ) :
    (p ^ 3 : ℤ) ∣ ((Nat.choose (p * a) (p * b) : ℤ) - (Nat.choose a b : ℤ)) := by
  have hp3 : ((p : ZMod (p ^ 3))) ^ 3 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hcong := choose_mul_congr_aux (R := ZMod (p ^ 3)) p hp hp5 hp3 a b
  rw [show (p ^ 3 : ℤ) = ((p ^ 3 : ℕ) : ℤ) from by push_cast; ring,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  exact hcong

end Jacob

#print axioms Jacob.jacobsthal_base
