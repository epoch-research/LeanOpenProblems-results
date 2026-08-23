import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

def IsInterprime (k : ℕ) : Prop :=
  ∃ p, p.Prime ∧ 2 < p ∧ p < k ∧ S_sum p = 2 * k

theorem next_prime_spec (r : ℕ) :
    Nat.Prime (next_prime r) ∧ r < next_prime r ∧
      ∀ k, Nat.Prime k → r < k → next_prime r ≤ k := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hprime, Nat.lt_of_succ_le hp⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.sInf_mem hne).1
  · exact (Nat.sInf_mem hne).2
  · intro k hk hlt
    exact Nat.sInf_le ⟨hk, hlt⟩

theorem next_prime_eq {r p : ℕ} (hp : Nat.Prime p) (hlt : r < p)
    (hmin : ∀ k, r < k → k < p → ¬ Nat.Prime k) : next_prime r = p := by
  have h := next_prime_spec r
  apply le_antisymm
  · exact h.2.2 p hp hlt
  · have hle : next_prime r ≤ p := h.2.2 p hp hlt
    rcases eq_or_lt_of_le hle with h_eq | h_lt
    · exact h_eq.symm.le
    · exact absurd h.1 (hmin (next_prime r) h.2.1 h_lt)

theorem isInterprime_of_consecutive {p p' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hp2 : 2 < p) (hlt : p < p')
    (hnone : ∀ k, p < k → k < p' → ¬ k.Prime) :
    IsInterprime ((p + p') / 2) := by
  have hnp : next_prime p = p' := next_prime_eq hp' hlt hnone
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hp'_odd : Odd p' := hp'.odd_of_ne_two (by omega)
  have h2 : Even (p + p') := hp_odd.add_odd hp'_odd
  have hdiv : 2 ∣ p + p' := even_iff_two_dvd.mp h2
  refine ⟨p, hp, hp2, ?_, ?_⟩
  · have hmul : 2 * ((p + p') / 2) = p + p' := Nat.mul_div_cancel' hdiv
    have : 2 * p < 2 * ((p + p') / 2) := by
      rw [hmul]; omega
    exact (mul_lt_mul_iff_right₀ (by omega : 0 < 2)).mp this
  · unfold S_sum
    rw [hnp]
    have : 2 * ((p + p') / 2) = p + p' := Nat.mul_div_cancel' hdiv
    exact this.symm

theorem odd_prime_mod4 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hlt : p % 4 < 4 := Nat.mod_lt p (by decide : 0 < 4)
  have h24 : p % 4 % 2 = p % 2 := (Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4))
  have : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
  rcases this with h | h | h | h
  · rw [h] at h24; simp at h24; omega
  · exact Or.inl h
  · rw [h] at h24; simp at h24; omega
  · exact Or.inr h

theorem modeq_one_of_mod {p : ℕ} (h : p % 4 = 1) : p ≡ 1 [MOD 4] := by
  rw [Nat.ModEq, Nat.one_mod]
  exact h

theorem modeq_three_of_mod {p : ℕ} (h : p % 4 = 3) : p ≡ 3 [MOD 4] := by
  rw [Nat.ModEq]
  exact h

theorem even_midpoint_of_mixed {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hpm : p % 4 = 1) (hqm : q % 4 = 3) :
    Even ((p + q) / 2) := by
  have hdiv : 2 ∣ p + q := even_iff_two_dvd.mp (hp.add_odd hq)
  have hsum : (p + q) % 4 = 0 := by
    have := Nat.add_mod p q 4
    rw [hpm, hqm] at this
    exact this
  -- (p+q)/2 even iff p+q ≡ 0 [MOD 4]
  have : 4 ∣ p + q := Nat.dvd_iff_mod_eq_zero.mpr hsum
  have hmul : 2 * ((p + q) / 2) = p + q := Nat.mul_div_cancel' hdiv
  have : 2 ∣ (p + q) / 2 := by
    have ⟨k, hk⟩ := this
    have : 2 * ((p + q) / 2) = 2 * (2 * k) := by
      rw [hmul, hk]; ring
    exact ⟨k, by omega⟩
  exact even_iff_two_dvd.mpr this

theorem exists_even_interprime_gt (N : ℕ) :
    ∃ k, N ≤ k ∧ Even k ∧ IsInterprime k := by
  obtain ⟨p1, hp1gt, hp1p, hp1mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N 2) (q := 4) (a := 1)
      (by decide) (by decide)
  obtain ⟨p3₀, hp3gt0, hp3p0, hp3mod0⟩ :=
    Nat.forall_exists_prime_gt_and_modEq p1 (q := 4) (a := 3)
      (by decide) (by decide)
  let S := {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4] ∧ p1 < p}
  have hSne : S.Nonempty := ⟨p3₀, hp3p0, hp3mod0, hp3gt0⟩
  let p3 := sInf S
  have hp3mem : p3 ∈ S := Nat.sInf_mem hSne
  have hp3p : p3.Prime := hp3mem.1
  have hp3mod : p3 ≡ 3 [MOD 4] := hp3mem.2.1
  have hp3gt : p1 < p3 := hp3mem.2.2
  have hp12 : 2 < p1 := Nat.lt_of_le_of_lt (le_max_right N 2) hp1gt
  let prev := sSup {p : ℕ | p.Prime ∧ p < p3}
  have hPne : {p : ℕ | p.Prime ∧ p < p3}.Nonempty :=
    ⟨2, Nat.prime_two, lt_trans hp12 hp3gt⟩
  have hPbdd : BddAbove {p : ℕ | p.Prime ∧ p < p3} :=
    ⟨p3, fun _ hx => le_of_lt hx.2⟩
  have hprevmem : prev ∈ {p : ℕ | p.Prime ∧ p < p3} := Nat.sSup_mem hPne hPbdd
  have hprevp : prev.Prime := hprevmem.1
  have hprevlt : prev < p3 := hprevmem.2
  have hnone : ∀ k, prev < k → k < p3 → ¬ k.Prime := by
    intro k hk1 hk2 hk
    have : k ≤ prev := le_csSup hPbdd ⟨hk, hk2⟩
    omega
  have hprev_ge : p1 ≤ prev := le_csSup hPbdd ⟨hp1p, hp3gt⟩
  have hprev_ne2 : prev ≠ 2 := by omega
  have hprev_mod1 : prev % 4 = 1 := by
    have hcases := odd_prime_mod4 hprevp hprev_ne2
    rcases hcases with h1 | h3
    · exact h1
    · have hmem : prev ∈ S := by
        refine ⟨hprevp, modeq_three_of_mod h3, ?_⟩
        have : p1 ≠ prev := by
          intro heq
          have : p1 % 4 = 1 := by
            simpa [Nat.ModEq, Nat.one_mod] using hp1mod
          omega
        omega
      have : p3 ≤ prev := Nat.sInf_le hmem
      omega
  have hmid : IsInterprime ((prev + p3) / 2) :=
    isInterprime_of_consecutive hprevp hp3p (by omega) hprevlt hnone
  have ho1 : Odd prev := hprevp.odd_of_ne_two hprev_ne2
  have ho3 : Odd p3 := hp3p.odd_of_ne_two (by omega)
  have hp3mod3 : p3 % 4 = 3 := by
    simpa [Nat.ModEq] using hp3mod
  have heven : Even ((prev + p3) / 2) :=
    even_midpoint_of_mixed ho1 ho3 hprev_mod1 hp3mod3
  have hge : N ≤ (prev + p3) / 2 := by
    have hdiv : 2 ∣ prev + p3 := even_iff_two_dvd.mp (ho1.add_odd ho3)
    have hle : prev ≤ (prev + p3) / 2 := by
      have hmul := Nat.mul_div_cancel' hdiv
      have : 2 * prev ≤ prev + p3 := by omega
      have : 2 * prev ≤ 2 * ((prev + p3) / 2) := by simpa [hmul]
      exact (mul_le_mul_iff_right₀ (by omega : 0 < (2 : ℕ))).1 this
    have : N ≤ prev :=
      le_trans (le_max_left N 2) (le_trans (Nat.le_of_lt hp1gt) hprev_ge)
    omega
  exact ⟨(prev + p3) / 2, hge, heven, hmid⟩
