import FormalConjectures.Dev.PowerDetGeneric
import FormalConjectures.Dev.Helpers

open Finset Matrix Nat
open scoped BigOperators

lemma zmod_half_cast_injective {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) :
    Function.Injective (fun j : Fin m => ((j.val + 1 : ℕ) : ZMod p)) := by
  intro i j h
  have hmod : (i.val + 1) ≡ (j.val + 1) [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp h
  have hi : i.val + 1 < p := by rw [hp]; have := i.isLt; omega
  have hj : j.val + 1 < p := by rw [hp]; have := j.isLt; omega
  have hn := hmod.eq_of_lt_of_lt hi hj
  apply Fin.ext; omega

lemma zmod_half_square_pow_m {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (i : Fin m) :
    ((((i.val + 1 : ℕ) : ZMod p)^2) ^ m) = 1 := by
  have hne : ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := one_to_m_cast_ne_zero hp i
  calc
    ((((i.val + 1 : ℕ) : ZMod p)^2) ^ m) = ((i.val + 1 : ℕ) : ZMod p) ^ (2*m) := by rw [← pow_mul]
    _ = ((i.val + 1 : ℕ) : ZMod p) ^ (p-1) := by congr 1; rw [hp]; omega
    _ = 1 := ZMod.pow_card_sub_one_eq_one hne

lemma zmod_choose_m_ne_zero {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (r : Fin m) (hr : r.val ≠ 0) : ((m.choose r.val : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ m.choose r.val := (ZMod.natCast_eq_zero_iff _ p).mp hzero
  have hpprime : p.Prime := Fact.out
  have hm_lt_p : m < p := by rw [hp]; omega
  have hcop : p.Coprime (m.choose r.val) := hpprime.coprime_choose_of_lt hm_lt_p (Nat.le_of_lt r.isLt)
  have hp_eq1 := hcop.eq_one_of_dvd hdvd
  rw [hp] at hp_eq1
  omega

lemma zmod_m_even_of_p_mod_four_one {p m : ℕ} (hp : p = 2*m+1) (hp4 : p % 4 = 1) : Even m := by
  have hdiv := (Nat.div_add_mod p 4).symm
  rw [hp4] at hdiv
  refine ⟨p / 4, ?_⟩
  rw [hp] at hdiv
  omega

lemma zmod_half_wilson {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (hmeven : Even m) :
    (((m.factorial : ℕ) : ZMod p)^2) = -1 := by
  let C : ZMod p := (m.factorial : ℕ)
  have hm_le_p : m ≤ p := by rw [hp]; omega
  have hdesc : (((p-1).descFactorial m : ℕ) : ZMod p) = (-1 : ZMod p)^m * C := by
    simpa [C] using (ZMod.cast_descFactorial (p:=p) (n:=m) hm_le_p)
  have hfac_nat : m.factorial * (p-1).descFactorial m = (p-1).factorial := by
    have hle : m ≤ p-1 := by rw [hp]; omega
    have h := Nat.factorial_mul_descFactorial hle
    have hpm : p - 1 - m = m := by rw [hp]; omega
    rwa [hpm] at h
  have hfac : C * (((p-1).descFactorial m : ℕ) : ZMod p) = -1 := by
    rw [← Nat.cast_mul, hfac_nat]
    exact ZMod.wilsons_lemma p
  rw [hdesc] at hfac
  have hpow : (-1 : ZMod p)^m = 1 := by
    rcases hmeven with ⟨k, hk⟩
    rw [hk]
    simp [pow_mul]
  rw [hpow] at hfac
  ring_nf at hfac ⊢
  simpa [C] using hfac

lemma zmod_prod_neg_y_eq_factorial {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (hmeven : Even m) :
    (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) = ((m.factorial : ℕ) : ZMod p) := by
  have hprod_nat : (∏ j : Fin m, (j.val + 1 : ℕ)) = m.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => j + 1) m]
    exact Finset.prod_range_add_one_eq_factorial m
  have hprod : (∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) = ((m.factorial : ℕ) : ZMod p) := by
    rw [← Finset.prod_natCast, hprod_nat]
  have hnegprod : (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) =
      (-1 : ZMod p) ^ Fintype.card (Fin m) * (∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) := by
    simpa using (Finset.prod_neg (s := (Finset.univ : Finset (Fin m)))
      (f := fun j : Fin m => (((j.val + 1 : ℕ) : ZMod p))))
  rw [hnegprod, hprod]
  rcases hmeven with ⟨k, hk⟩
  rw [Fintype.card_fin, hk]
  simp [pow_mul]

lemma zmod_hAP_one {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (hp4 : p % 4 = 1) :
    let C : ZMod p := (m.factorial : ℕ)
    1 - (-C)^m * (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) ≠ 0 := by
  intro C hzero
  have hmeven : Even m := zmod_m_even_of_p_mod_four_one hp hp4
  have hC2 : C^2 = -1 := by simpa [C] using zmod_half_wilson hp hmeven
  have hprod : (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) = C := by simpa [C] using zmod_prod_neg_y_eq_factorial hp hmeven
  have hT : (-C)^m * (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) = 1 := by
    have := sub_eq_zero.mp hzero
    simpa using this.symm
  rw [hprod] at hT
  have hT2 : ((-C)^m * C)^2 = (1 : ZMod p)^2 := by rw [hT]
  have hleft : ((-C)^m * C)^2 = -1 := by
    rcases hmeven with ⟨k, hk⟩
    rw [hk]
    calc
      ((-C)^(k+k) * C)^2 = (((-C)^2)^k * C)^2 := by rw [← two_mul, pow_mul]
      _ = ((C^2)^k * C)^2 := by ring_nf
      _ = ((-1 : ZMod p)^k * C)^2 := by rw [hC2]
      _ = ((-1 : ZMod p)^(2*k) * C^2) := by ring
      _ = -1 := by simp [hC2, pow_mul]
  rw [hleft] at hT2
  have hp2 : p ≠ 2 := by
    intro hp2eq
    rw [hp2eq] at hp4
    norm_num at hp4
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hnegoneeq : (-1 : ZMod p) = 1 := by simpa using hT2
  exact (Ring.neg_one_ne_one_of_char_ne_two hchar) hnegoneeq

lemma zmod_power_det_ne_zero_mod_one {p m : ℕ} [Fact p.Prime]
    (hp : p = 2*m+1) (hp4 : p % 4 = 1) :
    Matrix.det (fun i j : Fin m =>
      ((((i.val + 1 : ℕ) : ZMod p)^2) - ((m.factorial : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^ m) ≠ 0 := by
  let x : Fin m → ZMod p := fun i => (((i.val + 1 : ℕ) : ZMod p)^2)
  let y : Fin m → ZMod p := fun j => ((j.val + 1 : ℕ) : ZMod p)
  let C : ZMod p := (m.factorial : ℕ)
  have hmpos : 0 < m := by
    have hmeven : Even m := zmod_m_even_of_p_mod_four_one hp hp4
    rcases hmeven with ⟨k, hk⟩
    rw [hk]
    by_contra h0
    have hm0 : k + k = 0 := by omega
    have hp_eq1 : p = 1 := by rw [hp, hk, hm0]
    exact (Fact.out : p.Prime).ne_one hp_eq1
  have hc : C ≠ 0 := factorial_cast_zmod_ne_zero hp
  have hxinj : Function.Injective x := zmod_square_half_injective hp
  have hyinj : Function.Injective y := zmod_half_cast_injective hp
  have hxpow : ∀ i, x i ^ m = 1 := zmod_half_square_pow_m hp
  have hchoose : ∀ r : Fin m, r.val ≠ 0 → ((m.choose r.val : ℕ) : ZMod p) ≠ 0 := zmod_choose_m_ne_zero hp
  have hAP := zmod_hAP_one hp hp4
  simpa [x, y, C] using powerMatrix_det_ne_zero hmpos x y C hxinj hyinj hxpow hc hchoose hAP

#print axioms zmod_power_det_ne_zero_mod_one
