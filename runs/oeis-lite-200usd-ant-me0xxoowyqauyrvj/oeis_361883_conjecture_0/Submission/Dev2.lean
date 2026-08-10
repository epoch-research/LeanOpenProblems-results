import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace SunInt

/-- The numerator sum `S N = ∑_{k=0}^N (N+2k) C(N+k-1, N-1)^3`. -/
def Sb (N : ℕ) : ℕ :=
  ∑ k ∈ range (N + 1), (N + 2 * k) * (Nat.choose (N + k - 1) (N - 1)) ^ 3

/-- The integer-form summand `Term_k * C^2` for k ≥ 1. -/
-- absorption identity
theorem absorb {N k : ℕ} (hN : 1 ≤ N) :
    (N + k) * (N + k - 1).choose k = N * (N + k).choose k := by
  have hsym1 : (N + k - 1).choose (N - 1) = (N + k - 1).choose k := by
    rw [← Nat.choose_symm (show k ≤ N + k - 1 by omega)]; congr 1; omega
  have hsym2 : (N + k).choose N = (N + k).choose k := by
    rw [← Nat.choose_symm (show k ≤ N + k by omega)]; congr 1; omega
  have key := Nat.succ_mul_choose_eq (N + k - 1) (N - 1)
  -- succ (N+k-1) * choose (N+k-1) (N-1) = choose (succ (N+k-1)) (succ (N-1)) * succ (N-1)
  have e1 : Nat.succ (N + k - 1) = N + k := by omega
  have e2 : Nat.succ (N - 1) = N := by omega
  rw [e1, e2, hsym1, hsym2] at key
  -- key : (N + k) * (N+k-1).choose k = (N+k).choose k * N
  rw [key]; ring

theorem absorb2 {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (N + k - 1).choose k * k = (N + k - 1).choose (k - 1) * N := by
  have key := Nat.choose_succ_right_eq (N + k - 1) (k - 1)
  have e1 : (k - 1) + 1 = k := by omega
  have e2 : (N + k - 1) - (k - 1) = N := by omega
  rw [e1, e2] at key
  exact key

/-- Per-k identity (k ≥ 1): the term equals N times the integer summand. -/
theorem term_eq {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (N + 2 * k) * (N + k - 1).choose (N - 1) ^ 3
      = N * (((N + k).choose k + (N + k - 1).choose (k - 1)) * (N + k - 1).choose k ^ 2) := by
  have hsym1 : (N + k - 1).choose (N - 1) = (N + k - 1).choose k := by
    rw [← Nat.choose_symm (show k ≤ N + k - 1 by omega)]; congr 1; omega
  rw [hsym1]
  set C := (N + k - 1).choose k with hC
  have ha := absorb (N := N) (k := k) hN
  have hb := absorb2 (N := N) (k := k) hN hk
  -- ha : (N+k)*C = N*(N+k).choose k
  -- hb : C*k = (N+k-1).choose (k-1) * N
  -- Goal: (N+2k)*C^3 = N*((N+k).choose k + (N+k-1).choose (k-1))*C^2
  have expand : N * (((N + k).choose k + (N + k - 1).choose (k - 1)) * C ^ 2)
      = (N * (N + k).choose k + (N + k - 1).choose (k - 1) * N) * C ^ 2 := by ring
  rw [expand, ← ha, ← hb]
  ring

/-- The closed integer form of `a N`. -/
def aClosed (N : ℕ) : ℕ :=
  if N = 0 then 0
  else 1 + ∑ k ∈ Icc 1 N, ((N + k).choose k + (N + k - 1).choose (k - 1)) * (N + k - 1).choose k ^ 2

theorem range_split (N : ℕ) : range (N + 1) = insert 0 (Icc 1 N) := by
  ext x; simp only [mem_range, mem_insert, mem_Icc]; omega

/-- `Sb N = N * aClosed N` for `N ≥ 1`. -/
theorem Sb_eq (N : ℕ) (hN : 1 ≤ N) : Sb N = N * aClosed N := by
  rw [Sb, range_split, Finset.sum_insert (by simp), aClosed, if_neg (by omega)]
  have hk0 : (N + 2 * 0) * (N + 0 - 1).choose (N - 1) ^ 3 = N := by
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [Nat.choose_self, one_pow, mul_one]
  rw [hk0]
  have hrest : ∑ k ∈ Icc 1 N, (N + 2 * k) * (N + k - 1).choose (N - 1) ^ 3
      = N * ∑ k ∈ Icc 1 N, ((N + k).choose k + (N + k - 1).choose (k - 1)) * (N + k - 1).choose k ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mem_Icc] at hk
    exact term_eq hN hk.1
  rw [hrest, Nat.mul_add, mul_one]

/-- The Spec-style division definition equals the closed form. -/
theorem aDiv_eq (N : ℕ) : (if N = 0 then 0 else Sb N / N) = aClosed N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [aClosed]
  · rw [if_neg (by omega), Sb_eq N h, Nat.mul_div_cancel_left _ (by omega)]

/- ============================================================
   The analytic core: Φ(m) = Sb(mp) - p·Sb(m), and the main divisibility.
   ============================================================ -/

variable {p : ℕ}

/-- The key integer `Φ(m) = Sb(mp) - p·Sb(m)`. -/
def Phi (p m : ℕ) : ℤ := (Sb (m * p) : ℤ) - p * (Sb m : ℤ)

/-- BASE CASE: `p ∤ m ⟹ p^4 ∣ Φ(m)`. -/
theorem base_case (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    (p : ℤ) ^ 4 ∣ Phi p m := by
  sorry

/-- TRANSFER: `p^(4(2+v_p(μ))) ∣ Φ(pμ) - p^4·Φ(μ)`. -/
theorem transfer (hp : p.Prime) (hp5 : 5 ≤ p) (μ : ℕ) (hμ : 1 ≤ μ) :
    (p : ℤ) ^ (4 * (2 + padicValNat p μ)) ∣ (Phi p (p * μ) - (p : ℤ) ^ 4 * Phi p μ) := by
  sorry

/-- `Φ(m) = (m·p)·(aClosed(m·p) - aClosed m)`. -/
theorem Phi_eq (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) :
    Phi p m = (m * p : ℤ) * ((aClosed (m * p) : ℤ) - (aClosed m : ℤ)) := by
  have hp0 : 0 < p := hp.pos
  have hmp : 1 ≤ m * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold Phi
  rw [Sb_eq (m * p) hmp, Sb_eq m hm]
  push_cast
  ring

/-- MAIN LEMMA: `p^(4(1+v_p(m))) ∣ Φ(m)`, by strong induction on `v_p(m)`. -/
theorem main_lemma (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    (p : ℤ) ^ (4 * (1 + padicValNat p m)) ∣ Phi p m := by
  -- strong induction on w = padicValNat p m
  have hp1 : 1 < p := hp.one_lt
  haveI : Fact p.Prime := ⟨hp⟩
  generalize hw : padicValNat p m = w
  induction w using Nat.strong_induction_on generalizing m with
  | _ w IH =>
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · -- w = 0: p ∤ m, base case
      subst hw0
      have hpm : ¬ p ∣ m := by
        intro hd
        have := (padicValNat.eq_zero_iff (p := p) (n := m)).mp (hw)
        rcases this with h | h | h
        · omega
        · omega
        · exact h hd
      simpa using base_case hp hp5 m hm hpm
    · -- w ≥ 1: m = p·μ
      have hpm : p ∣ m := by
        by_contra hd
        rw [padicValNat.eq_zero_of_not_dvd hd] at hw; omega
      obtain ⟨μ, hμeq⟩ := hpm
      have hμpos : 1 ≤ μ := by
        rcases Nat.eq_zero_or_pos μ with h | h
        · subst h; simp at hμeq; omega
        · exact h
      have hvμ : padicValNat p μ = w - 1 := by
        have : padicValNat p m = padicValNat p μ + 1 := by
          rw [hμeq, mul_comm, padicValNat.mul (by omega) (by omega), padicValNat.self hp1]
        omega
      -- IH applies to μ
      have hIH : (p : ℤ) ^ (4 * (1 + padicValNat p μ)) ∣ Phi p μ :=
        IH (padicValNat p μ) (by omega) μ hμpos rfl
      -- transfer
      have hT := transfer hp hp5 μ hμpos
      -- Φ(m) = Φ(pμ); decompose
      have hmpμ : m = p * μ := by rw [hμeq, mul_comm]
      rw [hmpμ]
      have key : Phi p (p * μ) = (p : ℤ) ^ 4 * Phi p μ + (Phi p (p * μ) - (p : ℤ) ^ 4 * Phi p μ) := by ring
      rw [key]
      apply dvd_add
      · -- p^(4(1+w)) ∣ p^4 * Φ(μ)
        have hexp : 4 * (1 + w) ≤ 4 + 4 * (1 + padicValNat p μ) := by rw [hvμ]; omega
        calc (p:ℤ)^(4*(1+w)) ∣ (p:ℤ)^(4 + 4*(1+padicValNat p μ)) := pow_dvd_pow _ hexp
          _ ∣ (p:ℤ)^4 * Phi p μ := by
                rw [pow_add]; exact mul_dvd_mul (dvd_refl _) hIH
      · -- p^(4(1+w)) ∣ err
        have hexp : 4 * (1 + w) ≤ 4 * (2 + padicValNat p μ) := by rw [hvμ]; omega
        exact dvd_trans (pow_dvd_pow _ hexp) hT

/-- The step congruence for the closed form: `p^(3(1+v_p m)) ∣ aClosed(mp) - aClosed m`. -/
theorem step_dvd (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (1 + padicValNat p m)) ∣ ((aClosed (m * p) : ℤ) - (aClosed m : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hmp : m * p ≠ 0 := by positivity
  set e := 1 + padicValNat p m with he
  -- v_p(m*p) = e
  have hve : padicValNat p (m * p) = e := by
    rw [padicValNat.mul (by omega) (by omega), padicValNat.self hp.one_lt, he, Nat.add_comm]
  -- m*p = p^e * c with p ∤ c
  set c := (m * p) / p ^ e with hc
  have hdvd : p ^ e ∣ m * p := by rw [← hve]; exact pow_padicValNat_dvd
  have hmpc : m * p = p ^ e * c := (Nat.mul_div_cancel' hdvd).symm
  have hpc : ¬ p ∣ c := by
    intro hdc
    obtain ⟨d, hd⟩ := hdc
    have : p ^ (e + 1) ∣ m * p := ⟨d, by rw [hmpc, hd]; ring⟩
    have := pow_succ_padicValNat_not_dvd (p := p) hmp
    rw [hve] at this
    exact this ‹p ^ (e+1) ∣ m * p›
  -- main lemma gives p^(4e) ∣ Phi p m = (m*p)*(D)
  have hML := main_lemma hp hp5 m hm
  rw [Phi_eq hp m hm] at hML
  -- hML : p^(4*(1+v_p m)) ∣ (↑m*↑p) * D ; note 4*(1+v_p m) = 4 e
  have he4 : 4 * (1 + padicValNat p m) = 4 * e := by rw [he]
  rw [he4] at hML
  set D := (aClosed (m * p) : ℤ) - (aClosed m : ℤ) with hD
  -- ↑m*↑p = p^e * ↑c, and p^(4e) = p^e * p^(3e)
  have hcoef : (m : ℤ) * (p : ℤ) = (p : ℤ) ^ e * (c : ℤ) := by
    rw [← Nat.cast_mul, hmpc]; push_cast; ring
  have h1 : (p : ℤ) ^ (4 * e) = (p : ℤ) ^ e * (p : ℤ) ^ (3 * e) := by rw [← pow_add]; ring_nf
  rw [hcoef, h1] at hML
  -- hML : p^e * p^(3e) ∣ (p^e * ↑c) * D
  have hML' : (p : ℤ) ^ e * (p : ℤ) ^ (3 * e) ∣ (p : ℤ) ^ e * ((c : ℤ) * D) := by
    have : (p : ℤ) ^ e * (c : ℤ) * D = (p : ℤ) ^ e * ((c : ℤ) * D) := by ring
    rw [this] at hML; exact hML
  have hpe0 : (p : ℤ) ^ e ≠ 0 := pow_ne_zero e (by exact_mod_cast hp0.ne')
  have hML2 : (p : ℤ) ^ (3 * e) ∣ (c : ℤ) * D :=
    (mul_dvd_mul_iff_left hpe0).mp hML'
  -- p^(3e) coprime to c, so p^(3e) ∣ D
  have hcop : IsCoprime ((p : ℤ) ^ (3 * e)) (c : ℤ) := by
    have : IsCoprime (p : ℤ) (c : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((hp.coprime_iff_not_dvd).mpr hpc)
    exact this.pow_left
  exact hcop.dvd_of_dvd_mul_left hML2

/-- Conjecture for the closed form. -/
theorem conj_closed (hp : p.Prime) (hp5 : 5 ≤ p) (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    aClosed (n * p ^ r) ≡ aClosed (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  set m := n * p ^ (r - 1) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmp : m * p = n * p ^ r := by
    rw [hm]
    have : p ^ (r - 1) * p = p ^ r := by
      rw [← pow_succ]; congr 1; omega
    rw [mul_assoc, this]
  -- v_p(m) ≥ r-1
  have hvm : r ≤ 1 + padicValNat p m := by
    have : padicValNat p m = padicValNat p n + (r - 1) := by
      rw [hm, padicValNat.mul (by omega) (by positivity), padicValNat.prime_pow]
    omega
  have hstep := step_dvd hp hp5 m hm1
  rw [hmp] at hstep
  -- p^(3r) ∣ p^(3(1+v_p m)) ∣ aClosed(np^r) - aClosed m
  have hbig : (p : ℤ) ^ (3 * r) ∣ ((aClosed (n * p ^ r) : ℤ) - (aClosed m : ℤ)) :=
    dvd_trans (pow_dvd_pow _ (by omega)) hstep
  -- convert to ModEq
  rw [Nat.modEq_iff_dvd]
  have hcast : ((p ^ (3 * r) : ℕ) : ℤ) = (p : ℤ) ^ (3 * r) := by push_cast; ring
  rw [hcast]
  rw [show ((aClosed m : ℤ) - (aClosed (n * p ^ r) : ℤ)) = -(((aClosed (n*p^r):ℤ)) - aClosed m) by ring]
  exact (dvd_neg).mpr hbig

