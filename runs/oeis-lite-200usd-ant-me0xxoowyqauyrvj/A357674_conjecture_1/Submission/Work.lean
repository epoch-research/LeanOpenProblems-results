import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

theorem sum_pow_Ico_zero (p k : ℕ) [hpp : Fact p.Prime] (hk1 : 1 ≤ k) (hk2 : k < p - 1) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)) ^ k = 0 := by
  have hp0 : 0 < p := hpp.out.pos
  have hcard : k < Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; exact hk2
  have h1 : ∑ x : ZMod p, x ^ k = 0 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) k hcard
  have hbij : ∑ x : ZMod p, x ^ k = ∑ j ∈ range p, ((j : ZMod p)) ^ k := by
    apply Finset.sum_nbij' (fun x => ZMod.val x) (fun n => (n : ZMod p))
    · intro x _; rw [mem_range]; exact ZMod.val_lt x
    · intro n _; exact mem_univ _
    · intro x _; exact ZMod.natCast_rightInverse x
    · intro n hn; rw [mem_range] at hn; exact ZMod.val_cast_of_lt hn
    · intro x _; rw [ZMod.natCast_rightInverse x]
  rw [hbij] at h1
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext x; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)] at h1
  simp only [Nat.cast_zero, zero_pow (by omega : k ≠ 0)] at h1
  rw [zero_add] at h1
  exact h1

theorem wolst1 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p:ℤ)^2 ∣ ∑ j ∈ Ico 1 p, ∏ i ∈ (Ico 1 p).erase j, (i:ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := Ico 1 p with hs
  have hmem : ∀ j ∈ s, 1 ≤ j ∧ j < p := by intro j hj; rw [hs, mem_Ico] at hj; omega
  have hpj_s : ∀ j ∈ s, p - j ∈ s := by
    intro j hj; have := hmem j hj; rw [hs, mem_Ico]; omega
  have hne : ∀ j ∈ s, p - j ≠ j := by
    intro j hj; have h := hmem j hj
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ := hodd; omega
  set f : ℕ → ℤ := fun i => (i:ℤ) with hf
  set b : ℕ → ℤ := fun j => ∏ i ∈ ((s.erase j).erase (p - j)), f i with hb
  have hPj : ∀ j ∈ s, ∏ i ∈ s.erase j, f i = (f (p - j)) * b j := by
    intro j hj
    have hmem2 : (p - j) ∈ s.erase j := mem_erase.2 ⟨hne j hj, hpj_s j hj⟩
    simp only [hb]
    exact (Finset.mul_prod_erase (s.erase j) f hmem2).symm
  have hPpj : ∀ j ∈ s, ∏ i ∈ s.erase (p - j), f i = (f j) * b j := by
    intro j hj
    have hjmem : j ∈ s.erase (p - j) := mem_erase.2 ⟨(hne j hj).symm, hj⟩
    have hcomm : (s.erase (p - j)).erase j = (s.erase j).erase (p - j) := Finset.erase_right_comm
    simp only [hb, ← hcomm]
    exact (Finset.mul_prod_erase (s.erase (p - j)) f hjmem).symm
  have hreindex : ∑ j ∈ s, ∏ i ∈ s.erase (p - j), f i = ∑ j ∈ s, ∏ i ∈ s.erase j, f i := by
    apply Finset.sum_nbij' (fun j => p - j) (fun j => p - j)
    · intro j hj; exact hpj_s j hj
    · intro j hj; exact hpj_s j hj
    · intro j hj; have := hmem j hj; omega
    · intro j hj; have := hmem j hj; omega
    · intro j hj; rfl
  set E2 := ∑ j ∈ s, ∏ i ∈ s.erase j, f i with hE2
  have h2 : (2:ℤ) * E2 = ∑ j ∈ s, ((p:ℤ) * b j) := by
    have hstep : (2:ℤ) * E2 = ∑ j ∈ s, (∏ i ∈ s.erase j, f i + ∏ i ∈ s.erase (p-j), f i) := by
      rw [Finset.sum_add_distrib, hreindex, hE2]; ring
    rw [hstep]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hPj j hj, hPpj j hj]
    have hcast : f (p - j) + f j = (p:ℤ) := by
      simp only [hf]
      rw [Nat.cast_sub (by have := hmem j hj; omega)]; ring
    rw [← hcast]; ring
  have hpdvd : (p:ℤ) ∣ ∑ j ∈ s, b j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [hb, hf]
    push_cast
    have hbc : ∀ j ∈ s, ∏ i ∈ ((s.erase j).erase (p - j)), (i:ZMod p) = ((j:ZMod p))^(p-3) := by
      intro j hj
      have hmj := hmem j hj
      have hj0 : (j:ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
      set bc := ∏ i ∈ ((s.erase j).erase (p - j)), (i:ZMod p) with hbcdef
      have hfull : ∏ i ∈ s, (i:ZMod p) = -1 := ZMod.prod_Ico_one_prime p
      have hpull1 : ∏ i ∈ s, (i:ZMod p) = (j:ZMod p) * ∏ i ∈ s.erase j, (i:ZMod p) :=
        (Finset.mul_prod_erase s (fun i => (i:ZMod p)) hj).symm
      have hmem2 : (p - j) ∈ s.erase j := mem_erase.2 ⟨hne j hj, hpj_s j hj⟩
      have hpull2 : ∏ i ∈ s.erase j, (i:ZMod p) = ((p-j:ℕ):ZMod p) * bc :=
        (Finset.mul_prod_erase (s.erase j) (fun i => (i:ZMod p)) hmem2).symm
      have hcastpj : ((p-j:ℕ):ZMod p) = -(j:ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      have heq1 : (j:ZMod p)^2 * bc = 1 := by
        have hkey : (-1 : ZMod p) = (j:ZMod p) * (-(j:ZMod p) * bc) := by
          rw [← hcastpj, ← hpull2, ← hpull1, hfull]
        linear_combination hkey
      have hinv : ((j:ZMod p))^(p-3) * (j:ZMod p)^2 = 1 := by
        rw [← pow_add]
        have : p - 3 + 2 = p - 1 := by omega
        rw [this]
        exact ZMod.pow_card_sub_one_eq_one hj0
      calc bc = bc * ((j:ZMod p)^2 * ((j:ZMod p))^(p-3)) := by rw [mul_comm ((j:ZMod p)^2), hinv, mul_one]
        _ = (bc * (j:ZMod p)^2) * ((j:ZMod p))^(p-3) := by ring
        _ = ((j:ZMod p))^(p-3) := by rw [mul_comm bc, heq1, one_mul]
    rw [Finset.sum_congr rfl hbc]
    exact sum_pow_Ico_zero p (p-3) (by omega) (by omega)
  obtain ⟨c, hc⟩ := hpdvd
  rw [← Finset.mul_sum, hc, ← mul_assoc] at h2
  have h3 : (2:ℤ) * E2 = (p:ℤ)^2 * c := by rw [h2]; ring
  have hcop : IsCoprime (2:ℤ) ((p:ℤ)^2) := by
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ := hodd
    have h2c : IsCoprime (2:ℤ) (p:ℤ) := by
      refine ⟨-(k:ℤ), 1, ?_⟩
      have : (p:ℤ) = 2*k+1 := by exact_mod_cast hk
      rw [this]; ring
    exact h2c.pow_right
  have hdvd2 : (p:ℤ)^2 ∣ 2 * E2 := ⟨c, h3⟩
  exact (IsCoprime.dvd_of_dvd_mul_left hcop.symm hdvd2)

theorem prod_one_add_cube {ι R : Type*} [CommRing R] [DecidableEq ι] (a : ι → R)
    (h : ∀ i j k, a i * a j * a k = 0) (s : Finset ι) :
    2 * ∏ i ∈ s, (1 + a i) = 2 + 2 * (∑ i ∈ s, a i) + ((∑ i ∈ s, a i)^2 - ∑ i ∈ s, (a i)^2) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    have hA2 : a j * (∑ i ∈ t, a i)^2 = 0 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_eq_zero; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero; intro k _
      rw [← mul_assoc]; exact h j i k
    have hQ : a j * (∑ i ∈ t, (a i)^2) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero; intro i _
      rw [sq, ← mul_assoc]; exact h j i i
    have expand : 2 * ((1 + a j) * ∏ i ∈ t, (1 + a i)) = (1 + a j) * (2 * ∏ i ∈ t, (1 + a i)) := by ring
    rw [expand, ih]
    linear_combination hA2 - hQ

theorem wolst2 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p:ℤ) ∣ ∑ i ∈ Ico 1 p, (∏ j ∈ (Ico 1 p).erase i, (j:ℤ))^2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hkey : ∀ i ∈ Ico 1 p, (∏ j ∈ (Ico 1 p).erase i, (j:ZMod p))^2 = ((i:ZMod p))^(p-3) := by
    intro i hi
    rw [mem_Ico] at hi
    have hi0 : (i:ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
    set pe := ∏ j ∈ (Ico 1 p).erase i, (j:ZMod p) with hpe
    have hfull : (i:ZMod p) * pe = -1 := by
      rw [hpe, Finset.mul_prod_erase (Ico 1 p) (fun j => (j:ZMod p)) (mem_Ico.2 ⟨hi.1, hi.2⟩)]
      exact ZMod.prod_Ico_one_prime p
    have hsq : (i:ZMod p)^2 * pe^2 = 1 := by
      have : ((i:ZMod p) * pe)^2 = 1 := by rw [hfull]; ring
      linear_combination this
    have hinv : ((i:ZMod p))^(p-3) * (i:ZMod p)^2 = 1 := by
      rw [← pow_add]
      have : p - 3 + 2 = p - 1 := by omega
      rw [this]; exact ZMod.pow_card_sub_one_eq_one hi0
    calc pe^2 = pe^2 * ((i:ZMod p)^2 * ((i:ZMod p))^(p-3)) := by rw [mul_comm ((i:ZMod p)^2), hinv, mul_one]
      _ = (pe^2 * (i:ZMod p)^2) * ((i:ZMod p))^(p-3) := by ring
      _ = ((i:ZMod p))^(p-3) := by rw [mul_comm (pe^2), hsq, one_mul]
  rw [Finset.sum_congr rfl hkey]
  exact sum_pow_Ico_zero p (p-3) (by omega) (by omega)
