import Submission.Lib
open Finset

lemma coprime_p3 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) (h : ¬(p:ℤ)∣a) :
    IsCoprime ((p:ℤ)^3) a := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  exact (hpp.coprime_iff_not_dvd.mpr h).pow_left

lemma nonsingular_step (p n : ℕ) (hp : Nat.Prime p)
    (hP0 : ¬ (p:ℤ) ∣ Rec374605.P0 ↑n)
    (h1 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+1))
    (h2 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+2)) :
    ((p:ℤ)^3) ∣ Rec374605.aSeq n := by
  have hrec := Rec374605.aSeq_rec n
  have hdvd : ((p:ℤ)^3) ∣ Rec374605.P0 ↑n * Rec374605.aSeq n := by
    have : Rec374605.P0 ↑n * Rec374605.aSeq n
        = -(Rec374605.P1 ↑n * Rec374605.aSeq (n+1) + Rec374605.P2 ↑n * Rec374605.aSeq (n+2)) := by
      linear_combination hrec
    rw [this]
    exact (dvd_neg).mpr (dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _))
  exact (coprime_p3 p hp _ hP0).dvd_of_dvd_mul_left hdvd

-- band helper: a*p < x < (a+1)*p ⟹ p ∤ x
lemma notdvd_band (p x a : ℕ) (hlo : a * p < x) (hhi : x < (a+1) * p) : ¬ p ∣ x := by
  rintro ⟨k, hk⟩
  have h1 : a < k := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    calc p * a = a * p := Nat.mul_comm p a
      _ < x := hlo
      _ = p * k := hk
  have h2 : k < a + 1 := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    calc p * k = x := hk.symm
      _ < (a+1) * p := hhi
      _ = p * (a+1) := Nat.mul_comm (a+1) p
  omega

lemma notdvd_bandZ (p x a : ℕ) (hlo : a * p < x) (hhi : x < (a+1) * p) : ¬ (p:ℤ) ∣ (x:ℤ) := by
  intro h
  exact notdvd_band p x a hlo hhi (by exact_mod_cast h)

lemma notdvd_P0 (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : 2*p ≤ 3*n) (hhi : n + 3 ≤ p)
    (hQ : ¬ (p:ℤ) ∣ Rec374605.Q0val ↑n) :
    ¬ (p:ℤ) ∣ Rec374605.P0 ↑n := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have nd_mul : ∀ a b : ℤ, ¬(p:ℤ)∣a → ¬(p:ℤ)∣b → ¬(p:ℤ)∣(a*b) :=
    fun a b ha hb h => (hpp.dvd_mul.mp h).elim ha hb
  have nd_pow : ∀ (a : ℤ) (m : ℕ), ¬(p:ℤ)∣a → ¬(p:ℤ)∣(a^m) :=
    fun a m ha h => ha (hpp.dvd_of_dvd_pow h)
  have e2 : ¬ (p:ℤ) ∣ ((n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (n+2) 0 (by omega) (by omega) (by exact_mod_cast this)
  have e31 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+1) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+1:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+1) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e32 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+2) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e27 : ¬ (p:ℤ) ∣ (-27 : ℤ) := by
    intro h
    rw [Int.dvd_neg] at h
    have h3 : (p:ℤ) ∣ (3:ℤ) := hpp.dvd_of_dvd_pow (show (p:ℤ)∣(3:ℤ)^3 by rw [show ((3:ℤ)^3)=27 by norm_num]; exact h)
    have : p ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this; omega
  have hQ' : ¬ (p:ℤ) ∣ (5616 * (n:ℤ) ^ 4 + 36504 * (n:ℤ) ^ 3 + 88731 * (n:ℤ) ^ 2 + 95597 * (n:ℤ) + 38524) := by
    rw [show (5616 * (n:ℤ) ^ 4 + 36504 * (n:ℤ) ^ 3 + 88731 * (n:ℤ) ^ 2 + 95597 * (n:ℤ) + 38524) = Rec374605.Q0val ↑n from by unfold Rec374605.Q0val; ring]
    exact hQ
  unfold Rec374605.P0
  exact nd_mul _ _ (nd_mul _ _ (nd_mul _ _ (nd_mul _ _ e27 e2) (nd_pow _ 3 e31)) (nd_pow _ 3 e32)) hQ'

lemma notdvd_Udes (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : 2*p ≤ 3*n) (hhi : n + 3 ≤ p) :
    ¬ (p:ℤ) ∣ Rec374605.Udes ↑n := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have nd_mul : ∀ a b : ℤ, ¬(p:ℤ)∣a → ¬(p:ℤ)∣b → ¬(p:ℤ)∣(a*b) :=
    fun a b ha hb h => (hpp.dvd_mul.mp h).elim ha hb
  have nd_pow : ∀ (a : ℤ) (m : ℕ), ¬(p:ℤ)∣a → ¬(p:ℤ)∣(a^m) :=
    fun a m ha h => ha (hpp.dvd_of_dvd_pow h)
  have e2 : ¬ (p:ℤ) ∣ ((n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (n+2) 0 (by omega) (by omega) (by exact_mod_cast this)
  have e31 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+1) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+1:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+1) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e32 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+2) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e27 : ¬ (p:ℤ) ∣ (-27 : ℤ) := by
    intro h
    rw [Int.dvd_neg] at h
    have h3 : (p:ℤ) ∣ (3:ℤ) := hpp.dvd_of_dvd_pow (show (p:ℤ)∣(3:ℤ)^3 by rw [show ((3:ℤ)^3)=27 by norm_num]; exact h)
    have : p ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this; omega
  unfold Rec374605.Udes
  exact nd_mul _ _ (nd_mul _ _ (nd_mul _ _ e27 e2) (nd_pow _ 3 e31)) (nd_pow _ 3 e32)

lemma singular_step (p n : ℕ) (hp : Nat.Prime p)
    (hC : ¬ (p:ℤ) ∣ (Rec374605.Udes ↑n * Rec374605.P0 (↑n+1)))
    (h2 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+2))
    (h3 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+3)) :
    ((p:ℤ)^3) ∣ Rec374605.aSeq n := by
  have hdes := Rec374605.aSeq_desing n
  have hdvd : ((p:ℤ)^3) ∣ (Rec374605.Udes ↑n * Rec374605.P0 (↑n+1)) * Rec374605.aSeq n := by
    have : (Rec374605.Udes ↑n * Rec374605.P0 (↑n+1)) * Rec374605.aSeq n
        = Rec374605.Cqdes ↑n * Rec374605.aSeq (n+3) - Rec374605.Bqdes ↑n * Rec374605.aSeq (n+2) := by
      linear_combination hdes
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_left h2 _)
  exact (coprime_p3 p hp _ hC).dvd_of_dvd_mul_left hdvd


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

lemma main_aux (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hs2lem : ((p:ℤ)^3) ∣ Rec374605.aSeq (p-2)) :
    ∀ s, 1 ≤ s → s ≤ p - (2*p+3)/3 → ((p:ℤ)^3) ∣ Rec374605.aSeq (p - s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro hs1 hsmax
  have hL : 2*p+1 ≤ 3*(p-s) := by omega
  rcases Nat.lt_or_ge s 3 with hlt | hge
  · interval_cases s
    · -- s = 1
      exact A374605.aSeq_dvd_pm1 p hp hp5
    · -- s = 2
      exact hs2lem
  · -- s ≥ 3
    set m := p - s with hmdef
    by_cases hsing : (p:ℤ) ∣ Rec374605.Q0val ↑m
    · -- singular: must have s ≥ 4
      have hs4 : 4 ≤ s := by
        by_contra hcon
        have hs3 : s = 3 := by omega
        rw [hs3] at hmdef
        have h19 : (p:ℤ) ∣ (19600:ℤ) := by
          have hcast : (↑(p-3):ℤ) = (p:ℤ) - 3 := by
            rw [Nat.cast_sub (by omega)]; norm_num
          have hpoly : Rec374605.Q0val ↑(p-3) - 19600
              = (p:ℤ) * (5616*(p:ℤ)^3 - 30888*(p:ℤ)^2 + 63459*(p:ℤ) - 57709) := by
            rw [hcast]; unfold Rec374605.Q0val; ring
          have hsing' : (p:ℤ) ∣ Rec374605.Q0val ↑(p-3) := by rw [← hmdef]; exact hsing
          have : (p:ℤ) ∣ (Rec374605.Q0val ↑(p-3) - 19600) := by rw [hpoly]; exact Dvd.intro _ rfl
          have := dvd_sub hsing' this
          simpa using this
        have h19n : p ∣ 19600 := by exact_mod_cast h19
        have hcop2 : Nat.Coprime p (2^4) :=
          ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).pow_right 4
        have hp1225 : p ∣ 1225 :=
          hcop2.dvd_of_dvd_mul_left (by rw [show (19600:ℕ) = 2^4*1225 from by norm_num] at h19n; exact h19n)
        rw [show (1225:ℕ) = 5^2*7^2 from by norm_num] at hp1225
        rcases hp.dvd_mul.mp hp1225 with h | h
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      have hnd : ¬(p:ℤ) ∣ Rec374605.Q0val (↑m+1) :=
        no_double_sing p m hp hp5 (by omega) (by omega) hsing
      have hbridge : (↑(m+1):ℤ) = ↑m+1 := by push_cast; ring
      have hC : ¬(p:ℤ) ∣ (Rec374605.Udes ↑m * Rec374605.P0 (↑m+1)) := by
        intro hdvd
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdvd with h | h
        · exact notdvd_Udes p m hp hp5 (by omega) (by omega) h
        · have hP0' : ¬(p:ℤ) ∣ Rec374605.P0 ↑(m+1) :=
            notdvd_P0 p (m+1) hp hp5 (by omega) (by omega) (by rw [hbridge]; exact hnd)
          exact hP0' (by rw [hbridge]; exact h)
      apply singular_step p m hp hC
      · have := IH (s-2) (by omega) (by omega) (by omega)
        rwa [show p-(s-2) = m+2 from by omega] at this
      · have := IH (s-3) (by omega) (by omega) (by omega)
        rwa [show p-(s-3) = m+3 from by omega] at this
    · -- nonsingular
      apply nonsingular_step p m hp (notdvd_P0 p m hp hp5 (by omega) (by omega) hsing)
      · have := IH (s-1) (by omega) (by omega) (by omega)
        rwa [show p-(s-1) = m+1 from by omega] at this
      · have := IH (s-2) (by omega) (by omega) (by omega)
        rwa [show p-(s-2) = m+2 from by omega] at this

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

lemma a_eq_aSeq (n : ℕ) : ((a n : ℕ):ℤ) = Rec374605.aSeq n := by
  unfold a Rec374605.aSeq
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold Rec374605.T
  push_cast
  ring

theorem final (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hs2lem : ((p:ℤ)^3) ∣ Rec374605.aSeq (p-2)) :
    ∀ n : ℕ, (2 * p + 3) / 3 ≤ n → n ≤ p - 1 → (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  have hs := main_aux p hp hp5 hs2lem (p - n) (by omega) (by omega)
  rw [show p - (p-n) = n from by omega] at hs
  rw [← a_eq_aSeq] at hs
  have : ((p^3:ℕ):ℤ) ∣ ((a n:ℕ):ℤ) := by
    rw [show ((p^3:ℕ):ℤ) = (p:ℤ)^3 from by push_cast; ring]; exact hs
  exact_mod_cast this
