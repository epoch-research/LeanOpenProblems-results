import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }


lemma nat_add_one_sub_two_lt (n : ℕ) (hn : 0 < n) : n + 1 - 2 < n := by
  cases n with
  | zero => cases hn
  | succ k => cases k <;> simp

lemma nat_eq_sub_one_add_one {k : ℕ} (hk : 0 < k) : k = k - 1 + 1 := by
  exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hk)).symm

lemma nat_add_sub_pred_eq {N k : ℕ} (hk : 0 < k) (hle : k - 1 ≤ N) :
    k + (N - (k - 1)) = N + 1 := by
  have hk' : k = k - 1 + 1 := nat_eq_sub_one_add_one hk
  omega

lemma pow_succ_lt_mul_of_totient_lt {N k r : ℕ} (hk : 0 < k) (hle : k - 1 ≤ N)
    (hrtot : r.totient = 2 ^ (N - (k - 1))) (hrlt : r.totient < r) :
    2 ^ (N + 1) < 2 ^ k * r := by
  have hleexp : k + (N - (k - 1)) = N + 1 := nat_add_sub_pred_eq hk hle
  calc
    2 ^ (N + 1) = 2 ^ (k + (N - (k - 1))) := by rw [hleexp]
    _ = 2 ^ k * 2 ^ (N - (k - 1)) := by rw [pow_add]
    _ = 2 ^ k * r.totient := by rw [hrtot]
    _ < 2 ^ k * r := Nat.mul_lt_mul_of_pos_left hrlt (pow_pos two_pos k)


lemma odd_two_lt_of_ne_one {r : ℕ} (hodd : Odd r) (hr : r ≠ 1) : 2 < r := by
  obtain ⟨t, ht⟩ := hodd
  subst r
  cases t with
  | zero => exact (hr rfl).elim
  | succ t => omega



lemma totient_two_pow_succ (N : ℕ) : Nat.totient (2 ^ (N + 1)) = 2 ^ N := by
  rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos N)]
  rw [show (2 : ℕ) - 1 = 1 by rfl, mul_one, Nat.succ_sub_one]

lemma fermatNumber_le_of_pow_lt {n m : ℕ} (h : 2 ^ (2 ^ n) < m) : Nat.fermatNumber n ≤ m := by
  rw [Nat.fermatNumber]
  exact Nat.succ_le_of_lt h



lemma prime_sub_one_dvd_totient_of_dvd {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    p - 1 ∣ m.totient := by
  rw [← Nat.totient_prime hp]
  exact Nat.totient_dvd_of_dvd hpm

lemma prime_sub_one_eq_two_pow_of_totient_eq {p m K : ℕ} (hp : p.Prime) (hpm : p ∣ m)
    (hphi : m.totient = 2 ^ K) : ∃ e ≤ K, p - 1 = 2 ^ e := by
  have h : p - 1 ∣ 2 ^ K := by
    rw [← hphi]
    exact prime_sub_one_dvd_totient_of_dvd hp hpm
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

lemma prime_eq_fermatNumber_of_sub_one_eq_two_pow {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : p - 1 = 2 ^ e) : ∃ i, p = Nat.fermatNumber i := by
  have hpe : p = 2 ^ e + 1 := by
    rw [← he, Nat.sub_add_cancel hp.one_le]
  have he0 : e ≠ 0 := by
    intro h0
    have : p = 2 := by simpa [h0] using hpe
    exact hp2 this
  have hprime : (2 ^ e + 1).Prime := by simpa [← hpe] using hp
  obtain ⟨i, hi⟩ := Nat.pow_of_pow_add_prime (a := 2) (n := e) Nat.one_lt_two he0 hprime
  refine ⟨i, ?_⟩
  rw [Nat.fermatNumber, ← hi, hpe]

lemma odd_prime_factor_eq_fermatNumber_of_totient_eq_two_pow {p m K : ℕ} (hmodd : Odd m)
    (hp : p.Prime) (hpm : p ∣ m) (hphi : m.totient = 2 ^ K) :
    ∃ i, p = Nat.fermatNumber i := by
  obtain ⟨e, _hle, he⟩ := prime_sub_one_eq_two_pow_of_totient_eq hp hpm hphi
  have hp2 : p ≠ 2 := by
    intro hp2
    exact hmodd.not_two_dvd_nat (hp2 ▸ hpm)
  exact prime_eq_fermatNumber_of_sub_one_eq_two_pow hp hp2 he

lemma odd_prime_factor_fermat_index_le_of_totient_eq_two_pow {p m K i : ℕ} (_hmodd : Odd m)
    (hp : p.Prime) (hpm : p ∣ m) (hphi : m.totient = 2 ^ K)
    (hi : p = Nat.fermatNumber i) : 2 ^ i ≤ K := by
  obtain ⟨e, he_le, he⟩ := prime_sub_one_eq_two_pow_of_totient_eq hp hpm hphi
  have hpe : 2 ^ e = 2 ^ (2 ^ i) := by
    rw [← he]
    subst p
    simp [Nat.fermatNumber]
  have hei : e = 2 ^ i := Nat.pow_right_injective Nat.one_lt_two hpe
  rwa [hei] at he_le

lemma not_prime_sq_dvd_of_odd_totient_eq_two_pow {p m K : ℕ} (hmodd : Odd m)
    (hp : p.Prime) (hpm : p ∣ m) (hphi : m.totient = 2 ^ K) : ¬ p ^ 2 ∣ m := by
  intro hp2m
  have htot : (p ^ 2).totient ∣ m.totient := Nat.totient_dvd_of_dvd hp2m
  have hpphi : p ∣ m.totient := by
    refine dvd_trans ?_ htot
    rw [Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
    simp
  have hp2_dvd : p ∣ 2 ^ K := by simpa [hphi] using hpphi
  have hp_eq_two : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp2_dvd)
  exact hmodd.not_two_dvd_nat (hp_eq_two ▸ hpm)

lemma squarefree_of_odd_totient_eq_two_pow {m K : ℕ} (hmodd : Odd m)
    (hphi : m.totient = 2 ^ K) : Squarefree m := by
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  refine Nat.squarefree_of_factorization_le_one hm0 ?_
  intro p
  by_cases hp : p.Prime
  · by_cases hpm : p ∣ m
    · by_contra hle
      have h2le : 2 ≤ m.factorization p := by omega
      have hp2m : p ^ 2 ∣ m := (hp.pow_dvd_iff_le_factorization hm0).2 h2le
      exact not_prime_sq_dvd_of_odd_totient_eq_two_pow hmodd hp hpm hphi hp2m
    · rw [Nat.factorization_eq_zero_of_not_dvd hpm]
      norm_num
  · rw [Nat.factorization_eq_zero_of_not_prime m hp]
    exact Nat.zero_le 1

lemma odd_totient_eq_target_imp_fermat33_prime {m : ℕ} (hmodd : Odd m)
    (hphi : m.totient = 2 ^ (2 ^ 33)) : (Nat.fermatNumber 33).Prime := by
  by_contra hF
  have hsq : Squarefree m := squarefree_of_odd_totient_eq_two_pow hmodd hphi
  have hm_prod : (∏ p ∈ m.primeFactors, p) = m := Nat.prod_primeFactors_of_squarefree hsq
  have hsub : m.primeFactors ⊆ (Finset.range 33).image Nat.fermatNumber := by
    intro p hpmem
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hpmem).2.1
    obtain ⟨i, hi⟩ := odd_prime_factor_eq_fermatNumber_of_totient_eq_two_pow hmodd hpprime hpdvd hphi
    have hle : 2 ^ i ≤ 2 ^ 33 := odd_prime_factor_fermat_index_le_of_totient_eq_two_pow hmodd hpprime hpdvd hphi hi
    have hi_le33 : i ≤ 33 := (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hle
    have hi_ne33 : i ≠ 33 := by
      intro h33
      apply hF
      rw [hi, h33] at hpprime
      exact hpprime
    have hi_lt33 : i < 33 := lt_of_le_of_ne hi_le33 hi_ne33
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt33, hi.symm⟩
  have hm_le_prod : m ≤ ∏ p ∈ (Finset.range 33).image Nat.fermatNumber, p := by
    rw [← hm_prod]
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (by
      intro x hx hnot
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact le_trans (by decide : 1 ≤ 2) (Nat.two_lt_fermatNumber i).le)
  have hprod_image : (∏ p ∈ (Finset.range 33).image Nat.fermatNumber, p) =
      ∏ i ∈ Finset.range 33, Nat.fermatNumber i := by
    rw [Finset.prod_image]
    intro x hx y hy hxy
    exact Nat.fermatNumber_injective hxy
  have hm_le : m ≤ Nat.fermatNumber 33 - 2 := by
    calc
      m ≤ ∏ p ∈ (Finset.range 33).image Nat.fermatNumber, p := hm_le_prod
      _ = ∏ i ∈ Finset.range 33, Nat.fermatNumber i := hprod_image
      _ = Nat.fermatNumber 33 - 2 := Nat.prod_fermatNumber 33
  have hXgt1 : 1 < 2 ^ (2 ^ 33) :=
    Nat.one_lt_pow (pow_ne_zero 33 two_ne_zero) Nat.one_lt_two
  have hm_gt1 : 1 < m := by
    exact lt_of_lt_of_le hXgt1 (by rw [← hphi]; exact Nat.totient_le m)
  have hX_lt_m : 2 ^ (2 ^ 33) < m := by
    rw [← hphi]
    exact Nat.totient_lt m hm_gt1
  have hFsub_lt : Nat.fermatNumber 33 - 2 < 2 ^ (2 ^ 33) := by
    rw [Nat.fermatNumber]
    exact nat_add_one_sub_two_lt (2 ^ (2 ^ 33)) (pow_pos two_pos _)
  have hm_lt_X : m < 2 ^ (2 ^ 33) := lt_of_le_of_lt hm_le hFsub_lt
  exact (lt_asymm hX_lt_m hm_lt_X).elim

lemma totient_eq_of_mem_lt_twice {N m : ℕ} (_hN : 0 < 2 ^ N) (hmpos : 0 < m)
    (hdiv : 2 ^ N ∣ m.totient) (hlt : m < 2 ^ (N + 1)) : m.totient = 2 ^ N := by
  obtain ⟨k, hk⟩ := hdiv
  have hphi_pos : 0 < m.totient := Nat.totient_pos.mpr hmpos
  have hkpos : 0 < k := by
    rw [hk] at hphi_pos
    exact Nat.pos_of_mul_pos_left hphi_pos
  have hphi_lt : m.totient < 2 ^ (N + 1) := lt_of_le_of_lt (Nat.totient_le m) hlt
  have hklt : k < 2 := by
    rw [hk, Nat.pow_succ'] at hphi_lt
    rw [mul_comm 2 (2 ^ N)] at hphi_lt
    exact Nat.lt_of_mul_lt_mul_left hphi_lt
  have hk1 : k = 1 := by omega
  rw [hk, hk1, mul_one]

lemma lower_bound_composite_case {m : ℕ} (hm : m > 0 ∧ 2 ^ (2 ^ 33) ∣ m.totient)
    (hF : ¬ (Nat.fermatNumber 33).Prime) : 2 ^ (2 ^ 33 + 1) ≤ m := by
  by_contra hnot
  have hlt : m < 2 ^ (2 ^ 33 + 1) := Nat.lt_of_not_ge hnot
  have hphi : m.totient = 2 ^ (2 ^ 33) :=
    totient_eq_of_mem_lt_twice (N := 2 ^ 33) (m := m) (pow_pos two_pos _) hm.1 hm.2 hlt
  obtain ⟨k, r, hrodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.1.ne'
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero, one_mul] at hphi hlt ⊢
    exact hF (odd_totient_eq_target_imp_fermat33_prime hrodd hphi)
  by_cases hk1 : k = 1
  · subst k
    have hcop : Nat.Coprime (2 ^ 1) r := by
      rw [pow_one]
      exact hrodd.coprime_two_left
    have hphir : r.totient = 2 ^ (2 ^ 33) := by
      rw [Nat.totient_mul hcop] at hphi
      change Nat.totient 2 * r.totient = 2 ^ (2 ^ 33) at hphi
      rw [Nat.totient_two, one_mul] at hphi
      exact hphi
    exact hF (odd_totient_eq_target_imp_fermat33_prime hrodd hphir)
  have hk2 : 2 ≤ k := by
    cases k with
    | zero => exact (hk0 rfl).elim
    | succ k =>
        cases k with
        | zero => exact (hk1 rfl).elim
        | succ k => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
  have hkpos_for_pow : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk2
  have hcop : Nat.Coprime (2 ^ k) r := by
    exact hrodd.coprime_two_left.pow_left k
  have hphi_mul : (2 ^ k * r).totient = (2 ^ k).totient * r.totient := Nat.totient_mul hcop
  have htot2 : (2 ^ k).totient = 2 ^ (k - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two hkpos_for_pow]
    rw [Nat.sub_one, show (2 : ℕ) - 1 = 1 by rfl, mul_one]
  have hmain : 2 ^ (k - 1) * r.totient = 2 ^ (2 ^ 33) := by
    rw [hphi_mul, htot2] at hphi
    exact hphi
  by_cases hr1 : r = 1
  · subst r
    rw [Nat.totient_one, mul_one] at hmain
    have hkminus : k - 1 = 2 ^ 33 := Nat.pow_right_injective Nat.one_lt_two hmain
    have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk2
    have hk : k = 2 ^ 33 + 1 := by
      calc
        k = k - 1 + 1 := nat_eq_sub_one_add_one hkpos
        _ = 2 ^ 33 + 1 := by rw [hkminus]
    apply hnot
    rw [hk, mul_one]
  · have hr_gt : 2 < r := odd_two_lt_of_ne_one hrodd hr1
    have hrtot_pos : 0 < r.totient := Nat.totient_pos.mpr hrodd.pos
    have hdvd_pow : 2 ^ (k - 1) ∣ 2 ^ (2 ^ 33) := by
      exact ⟨r.totient, hmain.symm⟩
    obtain ⟨d, hdle, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd_pow
    have hkm : k - 1 = d := Nat.pow_right_injective Nat.one_lt_two hd
    subst d
    have hle : k - 1 ≤ 2 ^ 33 := hdle
    have hrtot_eq : r.totient = 2 ^ (2 ^ 33 - (k - 1)) := by
      have hpows : 2 ^ (2 ^ 33) = 2 ^ (k - 1) * 2 ^ (2 ^ 33 - (k - 1)) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      have hcancel := hmain
      rw [hpows] at hcancel
      exact (Nat.mul_left_cancel (pow_pos two_pos (k - 1))) hcancel
    have hstrict : 2 ^ (2 ^ 33 + 1) < 2 ^ k * r := by
      have hrphi_lt : r.totient < r := Nat.totient_lt r (lt_trans (by decide : 1 < 2) hr_gt)
      exact pow_succ_lt_mul_of_totient_lt (N := 2 ^ 33) (k := k) (r := r)
        (lt_of_lt_of_le (by decide : 0 < 2) hk2) hle hrtot_eq hrphi_lt
    exact hnot (le_of_lt hstrict)

lemma lower_bound_prime_case {m : ℕ} (hm : m > 0 ∧ 2 ^ (2 ^ 33) ∣ m.totient) :
    Nat.fermatNumber 33 ≤ m := by
  have hphi_pos : 0 < m.totient := Nat.totient_pos.mpr hm.1
  have hphi_ge : 2 ^ (2 ^ 33) ≤ m.totient := Nat.le_of_dvd hphi_pos hm.2
  have hXgt1 : 1 < 2 ^ (2 ^ 33) :=
    Nat.one_lt_pow (pow_ne_zero 33 two_ne_zero) Nat.one_lt_two
  have hm_gt_two : 1 < m := lt_of_lt_of_le hXgt1 (le_trans hphi_ge (Nat.totient_le m))
  have hm_gt : 2 ^ (2 ^ 33) < m := lt_of_le_of_lt hphi_ge (Nat.totient_lt m hm_gt_two)
  exact fermatNumber_le_of_pow_lt (n := 33) hm_gt

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  dsimp only
  by_cases hF : (Nat.fermatNumber 33).Prime
  · rw [if_pos hF]
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0, by intro x hx; exact Nat.zero_le x⟩
      · exact ⟨by
          exact (Nat.two_lt_fermatNumber 33).trans' (by decide : 0 < 2), by
          rw [Nat.totient_prime hF, Nat.fermatNumber, Nat.add_sub_cancel]⟩
    · apply le_csInf
      · exact ⟨Nat.fermatNumber 33, by
          constructor
          · exact (Nat.two_lt_fermatNumber 33).trans' (by decide : 0 < 2)
          · rw [Nat.totient_prime hF, Nat.fermatNumber, Nat.add_sub_cancel]⟩
      · intro b hb
        exact lower_bound_prime_case hb
  · rw [if_neg hF]
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0, by intro x hx; exact Nat.zero_le x⟩
      · exact ⟨by positivity, by
          rw [totient_two_pow_succ (2 ^ 33)]⟩
    · apply le_csInf
      · exact ⟨2 ^ (2 ^ 33 + 1), by
          constructor
          · positivity
          · rw [totient_two_pow_succ (2 ^ 33)]⟩
      · intro b hb
        exact lower_bound_composite_case hb hF
