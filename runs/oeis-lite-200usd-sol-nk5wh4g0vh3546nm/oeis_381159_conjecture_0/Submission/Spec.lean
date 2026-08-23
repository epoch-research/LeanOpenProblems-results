import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0.disproof : ¬(
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd, hdmax, hA⟩
  have bad {p q i : ℕ} (hp : p.Prime) (hq : q.Prime)
      (hpq : p % 10 ≠ q % 10) (hi : i < 150) :
      ¬ (p ∣ a + i * d ∧ q ∣ a + i * d) := by
    rintro ⟨hpd, hqd⟩
    have hn : a + i * d ≠ 0 := by omega
    have hpm : p % 10 ∈ (a + i * d).primeFactors.image (fun r => r % 10) := by
      apply Finset.mem_image.mpr
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, hn⟩, rfl⟩
    have hqm : q % 10 ∈ (a + i * d).primeFactors.image (fun r => r % 10) := by
      apply Finset.mem_image.mpr
      exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, hn⟩, rfl⟩
    exact hpq ((Finset.card_le_one.mp (hA ⟨i, hi⟩)) _ hpm _ hqm)
  have edge {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
      (hpq : p % 10 ≠ q % 10) (hpq150 : p * q ≤ 150) :
      p ∣ d ∨ q ∣ d := by
    by_contra h
    simp only [not_or] at h
    have hcp : d.Coprime p := ((hp.coprime_iff_not_dvd).mpr h.1).symm
    have hcq : d.Coprime q := ((hq.coprime_iff_not_dvd).mpr h.2).symm
    have hc : d.Coprime (p * q) := hcp.mul_right hcq
    letI : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
    let u : (ZMod (p * q))ˣ := ZMod.unitOfCoprime d hc
    let z : ZMod (p * q) :=
      -(a : ZMod (p * q)) * (↑(u⁻¹) : ZMod (p * q))
    have hiz : z.val < 150 := lt_of_lt_of_le (ZMod.val_lt z) hpq150
    have hzdiv : p * q ∣ a + z.val * d := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      change (a : ZMod (p * q)) + z * (u : ZMod (p * q)) = 0
      dsimp [z]
      rw [mul_assoc, ← Units.val_mul]
      simp
    apply bad hp hq hpq hiz
    exact ⟨dvd_trans (dvd_mul_right p q) hzdiv,
      dvd_trans (dvd_mul_left q p) hzdiv⟩
  have combine {m n : ℕ} (hc : m.Coprime n) (hm : m ∣ d) (hn : n ∣ d) :
      m * n ∣ d := hc.mul_dvd_of_dvd_of_dvd hm hn
  have e23 := edge (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 := edge (p := 2) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 := edge (p := 2) (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e211 := edge (p := 2) (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e213 := edge (p := 2) (q := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 2 ∣ d := by
    by_contra hn
    rcases e23 with h | h3
    · exact hn h
    rcases e25 with h | h5
    · exact hn h
    rcases e27 with h | h7
    · exact hn h
    rcases e211 with h | h11
    · exact hn h
    rcases e213 with h | h13
    · exact hn h
    have h15 := combine (m := 3) (n := 5) (by norm_num) h3 h5
    have h105 := combine (m := 15) (n := 7) (by norm_num) h15 h7
    have h1155 := combine (m := 105) (n := 11) (by norm_num) h105 h11
    have h15015 := combine (m := 1155) (n := 13) (by norm_num) h1155 h13
    have hle : 15015 ≤ 2025 := le_trans (Nat.le_of_dvd hd h15015) hdmax
    norm_num at hle
  clear e23 e25 e27 e211 e213
  have e35 := edge (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 := edge (p := 3) (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e311 := edge (p := 3) (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e317 := edge (p := 3) (q := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 3 ∣ d := by
    by_contra hn
    rcases e35 with h | h5
    · exact hn h
    rcases e37 with h | h7
    · exact hn h
    rcases e311 with h | h11
    · exact hn h
    rcases e317 with h | h17
    · exact hn h
    have h10 := combine (m := 2) (n := 5) (by norm_num) h2 h5
    have h70 := combine (m := 10) (n := 7) (by norm_num) h10 h7
    have h770 := combine (m := 70) (n := 11) (by norm_num) h70 h11
    have h13090 := combine (m := 770) (n := 17) (by norm_num) h770 h17
    have hle : 13090 ≤ 2025 := le_trans (Nat.le_of_dvd hd h13090) hdmax
    norm_num at hle
  clear e35 e37 e311 e317
  have e57 := edge (p := 5) (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e511 := edge (p := 5) (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e513 := edge (p := 5) (q := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : 5 ∣ d := by
    by_contra hn
    rcases e57 with h | h7
    · exact hn h
    rcases e511 with h | h11
    · exact hn h
    rcases e513 with h | h13
    · exact hn h
    have h6 := combine (m := 2) (n := 3) (by norm_num) h2 h3
    have h42 := combine (m := 6) (n := 7) (by norm_num) h6 h7
    have h462 := combine (m := 42) (n := 11) (by norm_num) h42 h11
    have h6006 := combine (m := 462) (n := 13) (by norm_num) h462 h13
    have hle : 6006 ≤ 2025 := le_trans (Nat.le_of_dvd hd h6006) hdmax
    norm_num at hle
  clear e57 e511 e513
  have e711 := edge (p := 7) (q := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e713 := edge (p := 7) (q := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 : 7 ∣ d := by
    by_contra hn
    rcases e711 with h | h11
    · exact hn h
    rcases e713 with h | h13
    · exact hn h
    have h6 := combine (m := 2) (n := 3) (by norm_num) h2 h3
    have h30 := combine (m := 6) (n := 5) (by norm_num) h6 h5
    have h330 := combine (m := 30) (n := 11) (by norm_num) h30 h11
    have h4290 := combine (m := 330) (n := 13) (by norm_num) h330 h13
    have hle : 4290 ≤ 2025 := le_trans (Nat.le_of_dvd hd h4290) hdmax
    norm_num at hle
  clear e711 e713
  have e1113 := edge (p := 11) (q := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 : 11 ∣ d := by
    by_contra hn
    rcases e1113 with h | h13
    · exact hn h
    have h6 := combine (m := 2) (n := 3) (by norm_num) h2 h3
    have h30 := combine (m := 6) (n := 5) (by norm_num) h6 h5
    have h210 := combine (m := 30) (n := 7) (by norm_num) h30 h7
    have h2730 := combine (m := 210) (n := 13) (by norm_num) h210 h13
    have hle : 2730 ≤ 2025 := le_trans (Nat.le_of_dvd hd h2730) hdmax
    norm_num at hle
  clear e1113
  have h6 := combine (m := 2) (n := 3) (by norm_num) h2 h3
  have h30 := combine (m := 6) (n := 5) (by norm_num) h6 h5
  have h210 := combine (m := 30) (n := 7) (by norm_num) h30 h7
  have h2310 := combine (m := 210) (n := 11) (by norm_num) h210 h11
  have hle : 2310 ≤ 2025 := le_trans (Nat.le_of_dvd hd h2310) hdmax
  norm_num at hle
