import Submission.Lib
open Finset

lemma p_in_three (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hR : p ∣ 686722798248729801455554265088) :
    p = 13 ∨ p = 37139 ∨ p = 69921781 := by
  have hc2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hc3 : Nat.Coprime p 3 := (Nat.coprime_primes hp (by norm_num)).mpr (by omega)
  have hcop : Nat.Coprime p 120367356051456 := by
    rw [show (120367356051456:ℕ) = 2^23 * 3^15 from by norm_num]
    exact (hc2.pow_right 23).mul_right (hc3.pow_right 15)
  rw [show (686722798248729801455554265088:ℕ) = 120367356051456 * 5705224578956123 from by norm_num] at hR
  have hM : p ∣ 5705224578956123 := hcop.dvd_of_dvd_mul_left hR
  rw [show (5705224578956123:ℕ) = 13^3 * (37139 * 69921781) from by norm_num] at hM
  rcases hp.dvd_mul.mp hM with h | h
  · left
    have : p ∣ 13 := hp.dvd_of_dvd_pow h
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this
  · rcases hp.dvd_mul.mp h with h | h
    · right; left; exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
    · right; right; exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h

lemma no_double_sing (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : 2*p+1 ≤ 3*n) (hhi : n + 4 ≤ p)
    (hsing : (p:ℤ) ∣ Rec374605.Q0val ↑n) :
    ¬ (p:ℤ) ∣ Rec374605.Q0val (↑n+1) := by
  intro hsing1
  -- resultant Bezout identity
  have hid : (3151661073637754752513081344*(n:ℤ)^3 + 26388475659753463637052751872*(n:ℤ)^2 + 73896791112407199010155134976*(n:ℤ) + 69276124213663709819984412672) * Rec374605.Q0val ↑n
      + (-3151661073637754752513081344*(n:ℤ)^3 - 13781831365202444627000426496*(n:ℤ)^2 - 20345296188416297878409969664*(n:ℤ) - 10069391054182826967768760320) * Rec374605.Q0val (↑n+1)
      = 686722798248729801455554265088 := by
    unfold Rec374605.Q0val; ring
  have hR : (p:ℤ) ∣ (686722798248729801455554265088 : ℤ) := by
    rw [← hid]; exact dvd_add (Dvd.dvd.mul_left hsing _) (Dvd.dvd.mul_left hsing1 _)
  have hRn : p ∣ 686722798248729801455554265088 := by exact_mod_cast hR
  rcases p_in_three p hp hp5 hRn with h13 | h37 | h69
  · -- p = 13 : range forces n = 9, contradiction with 13 ∤ Q0val 9
    subst h13
    have hn9 : n = 9 := by omega
    subst hn9
    -- hsing : (13:ℤ) ∣ Q0val 9, but Q0val 9 = 71544100, 13 ∤
    rw [show ((9:ℕ):ℤ) = (9:ℤ) from by norm_num] at hsing
    have : (13:ℤ) ∣ 71544100 := by
      have : Rec374605.Q0val (9:ℤ) = 71544100 := by unfold Rec374605.Q0val; norm_num
      rwa [this] at hsing
    norm_num at this
  · -- p = 37139
    subst h37
    have hid2 : (10575*(n:ℤ)^2 + 31475*(n:ℤ) + 9750) * Rec374605.Q0val ↑n
        + (26564*(n:ℤ)^2 + 10825*(n:ℤ) + 34510) * Rec374605.Q0val (↑n+1)
        = ((n:ℤ) - 10011) + 37139*(5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 245979*(n:ℤ)^4 + 524105*(n:ℤ)^3 + 638382*(n:ℤ)^2 + 511341*(n:ℤ) + 256329) := by
      unfold Rec374605.Q0val; ring
    have hdvd : (37139:ℤ) ∣ ((n:ℤ) - 10011) := by
      have hL : (37139:ℤ) ∣ ((10575*(n:ℤ)^2 + 31475*(n:ℤ) + 9750) * Rec374605.Q0val ↑n + (26564*(n:ℤ)^2 + 10825*(n:ℤ) + 34510) * Rec374605.Q0val (↑n+1)) :=
        dvd_add (Dvd.dvd.mul_left hsing _) (Dvd.dvd.mul_left hsing1 _)
      rw [hid2] at hL
      have h2 := dvd_sub hL (Dvd.dvd.mul_right (dvd_refl (37139:ℤ)) (5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 245979*(n:ℤ)^4 + 524105*(n:ℤ)^3 + 638382*(n:ℤ)^2 + 511341*(n:ℤ) + 256329))
      rwa [show ((n:ℤ) - 10011) + 37139*(5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 245979*(n:ℤ)^4 + 524105*(n:ℤ)^3 + 638382*(n:ℤ)^2 + 511341*(n:ℤ) + 256329) - 37139*(5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 245979*(n:ℤ)^4 + 524105*(n:ℤ)^3 + 638382*(n:ℤ)^2 + 511341*(n:ℤ) + 256329) = (n:ℤ) - 10011 from by ring] at h2
    have hpos : (0:ℤ) < (n:ℤ) - 10011 := by
      have : (24760:ℤ) ≤ (n:ℤ) := by exact_mod_cast (show 24760 ≤ n by omega)
      omega
    have := Int.le_of_dvd hpos hdvd
    have hub : (n:ℤ) ≤ 37135 := by exact_mod_cast (show n ≤ 37135 by omega)
    omega
  · -- p = 69921781
    subst h69
    have hid2 : (18797412*(n:ℤ)^2 + 44853758*(n:ℤ) + 51629528) * Rec374605.Q0val ↑n
        + (51124369*(n:ℤ)^2 + 30335890*(n:ℤ) + 27393549) * Rec374605.Q0val (↑n+1)
        = ((n:ℤ) - 5743855) + 69921781*(5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 248787*(n:ℤ)^4 + 529451*(n:ℤ)^3 + 597531*(n:ℤ)^2 + 368942*(n:ℤ) + 132255) := by
      unfold Rec374605.Q0val; ring
    have hdvd : (69921781:ℤ) ∣ ((n:ℤ) - 5743855) := by
      have hL : (69921781:ℤ) ∣ ((18797412*(n:ℤ)^2 + 44853758*(n:ℤ) + 51629528) * Rec374605.Q0val ↑n + (51124369*(n:ℤ)^2 + 30335890*(n:ℤ) + 27393549) * Rec374605.Q0val (↑n+1)) :=
        dvd_add (Dvd.dvd.mul_left hsing _) (Dvd.dvd.mul_left hsing1 _)
      rw [hid2] at hL
      have h2 := dvd_sub hL (Dvd.dvd.mul_right (dvd_refl (69921781:ℤ)) (5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 248787*(n:ℤ)^4 + 529451*(n:ℤ)^3 + 597531*(n:ℤ)^2 + 368942*(n:ℤ) + 132255))
      rwa [show ((n:ℤ) - 5743855) + 69921781*(5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 248787*(n:ℤ)^4 + 529451*(n:ℤ)^3 + 597531*(n:ℤ)^2 + 368942*(n:ℤ) + 132255) - 69921781*(5616*(n:ℤ)^6 + 58968*(n:ℤ)^5 + 248787*(n:ℤ)^4 + 529451*(n:ℤ)^3 + 597531*(n:ℤ)^2 + 368942*(n:ℤ) + 132255) = (n:ℤ) - 5743855 from by ring] at h2
    have hpos : (0:ℤ) < (n:ℤ) - 5743855 := by
      have : (46614521:ℤ) ≤ (n:ℤ) := by exact_mod_cast (show 46614521 ≤ n by omega)
      omega
    have := Int.le_of_dvd hpos hdvd
    have hub : (n:ℤ) ≤ 69921777 := by exact_mod_cast (show n ≤ 69921777 by omega)
    omega
