import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

-- The formalization of the conjecture C A091669 from Jan 19 2020.

namespace A091669

def prodPart (n : ℕ) : ℕ := (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
def numer (n : ℕ) : ℕ := (2 ^ (n - 1)) * prodPart n

lemma prodPart_ne_zero (n : ℕ) : prodPart n ≠ 0 := by
  classical
  unfold prodPart
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 2))

lemma numer_ne_zero (n : ℕ) : numer n ≠ 0 := by
  unfold numer
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (prodPart_ne_zero n)

lemma a_eq_numer_div (n : ℕ) (hn : n ≠ 0) : a n = numer n / n.factorial := by
  unfold a numer prodPart
  simp [hn]

lemma cast_prodPart (m p : ℕ) :
    ((prodPart m : ℕ) : ZMod p) =
      ∏ k ∈ Finset.Ico 1 m, ((2 : ZMod p) ^ k - 1) := by
  classical
  unfold prodPart
  rw [Finset.prod_natCast]
  refine Finset.prod_congr rfl ?_
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hle : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num : 0 < 2)
  rw [Nat.cast_sub hle]
  simp

lemma cast_numer (m p : ℕ) :
    ((numer m : ℕ) : ZMod p) =
      (2 : ZMod p) ^ (m - 1) * ∏ k ∈ Finset.Ico 1 m, ((2 : ZMod p) ^ k - 1) := by
  unfold numer
  rw [Nat.cast_mul, Nat.cast_pow, cast_prodPart]
  rfl


lemma zmod_two_ne_zero_of_prime_ne_two (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)

lemma zmod_factorial_pred_ne_zero_of_prime (p : ℕ) (hp : Nat.Prime p) :
    (((p - 1)! : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ (p - 1)! := (ZMod.natCast_eq_zero_iff _ _).mp h
  have hle : p ≤ p - 1 := (hp.dvd_factorial).mp hdvd
  exact (lt_irrefl p) (lt_of_le_of_lt hle (Nat.sub_one_lt hp.ne_zero))

lemma a091669_prime_product_eq_one_of_factorial_dvd
    (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hdvd : (p - 1).factorial ∣ numer (p - 1))
    (h : p ∣ a (p - 1) + 2 ^ (p - 2)) :
    (∏ k ∈ Finset.Ico 1 (p - 1), ((2 : ZMod p) ^ k - 1)) = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
  let Pz : ZMod p := ∏ k ∈ Finset.Ico 1 (p - 1), ((2 : ZMod p) ^ k - 1)
  have hcast : ((a (p - 1) + 2 ^ (p - 2) : ℕ) : ZMod p) = 0 := by
    exact (ZMod.natCast_eq_zero_iff _ _).2 h
  have hden_ne : (((p - 1)! : ℕ) : ZMod p) ≠ 0 :=
    zmod_factorial_pred_ne_zero_of_prime p hp
  have h2_ne : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero_of_prime_ne_two p hp hp2
  have hA_ne : (2 : ZMod p) ^ (p - 2) ≠ 0 := pow_ne_zero _ h2_ne
  have hp1ne : p - 1 ≠ 0 := by omega
  have ha_cast :
      ((a (p - 1) : ℕ) : ZMod p) =
        ((2 : ZMod p) ^ (p - 2) * Pz) / (((p - 1)! : ℕ) : ZMod p) := by
    rw [a_eq_numer_div (p - 1) hp1ne]
    rw [Nat.cast_div hdvd]
    · rw [cast_numer]
      have hsub : p - 1 - 1 = p - 2 := by omega
      rw [hsub]
    · exact hden_ne
  rw [Nat.cast_add, ha_cast, Nat.cast_pow] at hcast
  have hmul :
      (2 ^ (p - 2) * Pz / (((p - 1)! : ℕ) : ZMod p) + (2 : ZMod p) ^ (p - 2)) *
          (((p - 1)! : ℕ) : ZMod p) = 0 := by
    simpa using congrArg (fun x : ZMod p => x * (((p - 1)! : ℕ) : ZMod p)) hcast
  rw [add_mul, div_mul_cancel₀ _ hden_ne] at hmul
  rw [← mul_add] at hmul
  have hP_plus_fac : Pz + (((p - 1)! : ℕ) : ZMod p) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left hA_ne
  have hwilson : (((p - 1)! : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hP : Pz = 1 := by
    rw [hwilson] at hP_plus_fac
    linear_combination hP_plus_fac
  simpa [Pz] using hP

lemma prime_dvd_two_pow_sub_one_of_pred_dvd {p k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hk : p - 1 ∣ k) : p ∣ 2 ^ k - 1 := by
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rcases hk with ⟨t, rfl⟩
  have hfermat : 2 ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have hpow : (2 ^ (p - 1)) ^ t ≡ 1 ^ t [MOD p] := hfermat.pow t
  have hmod : 2 ^ ((p - 1) * t) ≡ 1 [MOD p] := by
    simpa [pow_mul] using hpow
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow ((p - 1) * t) 2 (by norm_num : 0 < 2))).mp hmod.symm

lemma factorial_factorization_le_pred_div_pred_of_prime {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0) :
    n.factorial.factorization p ≤ (n - 1) / (p - 1) := by
  have hsumpos : 1 ≤ (p.digits n).sum := by
    have hne : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
    have hlast_ne : (p.digits n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p hn
    have hlast_pos : 1 ≤ (p.digits n).getLast hne := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlast_ne)
    exact hlast_pos.trans (List.le_sum_of_mem (List.getLast_mem hne))
  have hmul_eq := Nat.sub_one_mul_factorization_factorial (n := n) hp
  have hmul_le : n.factorial.factorization p * (p - 1) ≤ n - 1 := by
    rw [mul_comm, hmul_eq]
    exact Nat.sub_le_sub_left hsumpos n
  exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hp.one_lt)).2 hmul_le

lemma prodPart_factorization_ge_pred_div_pred_of_odd_prime (n p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (n - 1) / (p - 1) ≤ (prodPart n).factorization p := by
  classical
  let q := (n - 1) / (p - 1)
  let s : Finset ℕ := (Finset.range q).image (fun t => (p - 1) * (t + 1))
  have hpred_pos : 0 < p - 1 := by
    have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
    omega
  have hsub : s ⊆ Finset.Ico 1 n := by
    intro k hk
    simp only [s, Finset.mem_image, Finset.mem_range] at hk
    rcases hk with ⟨t, ht, rfl⟩
    rw [Finset.mem_Ico]
    constructor
    · nlinarith [hpred_pos]
    · have hle : (p - 1) * (t + 1) ≤ (p - 1) * q := by
        exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt ht)
      have hqle : (p - 1) * q ≤ n - 1 := Nat.mul_div_le (n - 1) (p - 1)
      have hnle : (p - 1) * (t + 1) ≤ n - 1 := le_trans hle hqle
      have hprod_pos : 0 < (p - 1) * (t + 1) := Nat.mul_pos hpred_pos (Nat.succ_pos t)
      have hnminus_pos : 0 < n - 1 := lt_of_lt_of_le hprod_pos hnle
      have hn0 : n ≠ 0 := by omega
      exact lt_of_le_of_lt hnle (Nat.sub_one_lt hn0)
  have hinj : Function.Injective (fun t => (p - 1) * (t + 1)) := by
    intro a b hab
    exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_left hpred_pos hab)
  have hcard : s.card = q := by
    simp only [s]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hdvd_each : ∀ k ∈ s, p ∣ 2 ^ k - 1 := by
    intro k hk
    simp only [s, Finset.mem_image, Finset.mem_range] at hk
    rcases hk with ⟨t, ht, rfl⟩
    exact prime_dvd_two_pow_sub_one_of_pred_dvd hp hp2 ⟨t + 1, rfl⟩
  have hpow_dvd_prod_s : p ^ s.card ∣ ∏ k ∈ s, (2 ^ k - 1) := by
    calc
      p ^ s.card = ∏ k ∈ s, p := by simp
      _ ∣ ∏ k ∈ s, (2 ^ k - 1) := by
        exact Finset.prod_dvd_prod_of_dvd (fun k => p) (fun k => 2 ^ k - 1) hdvd_each
  have hprod_s_dvd : (∏ k ∈ s, (2 ^ k - 1)) ∣ prodPart n := by
    unfold prodPart
    exact Finset.prod_dvd_prod_of_subset s (Finset.Ico 1 n) (fun k => 2 ^ k - 1) hsub
  have hpow_dvd : p ^ q ∣ prodPart n := by
    rw [← hcard]
    exact hpow_dvd_prod_s.trans hprod_s_dvd
  exact (hp.pow_dvd_iff_le_factorization (prodPart_ne_zero n)).mp hpow_dvd

lemma factorial_dvd_numer (n : ℕ) : n.factorial ∣ numer n := by
  classical
  refine (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero n) (numer_ne_zero n)).mp ?_
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hp2 : p = 2
    · subst p
      by_cases hn : n = 0
      · simp [hn]
      have hfac_le : n.factorial.factorization 2 ≤ n - 1 := by
        simpa using (factorial_factorization_le_pred_div_pred_of_prime (n := n) (p := 2) Nat.prime_two hn)
      have hpow_dvd : 2 ^ (n - 1) ∣ numer n := by
        unfold numer
        exact dvd_mul_right _ _
      have hpow_le : n - 1 ≤ (numer n).factorization 2 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (numer_ne_zero n)).mp hpow_dvd
      exact le_trans hfac_le hpow_le
    · have hfac_le : n.factorial.factorization p ≤ (n - 1) / (p - 1) := by
        by_cases hn : n = 0
        · simp [hn]
        exact factorial_factorization_le_pred_div_pred_of_prime hp hn
      have hprod_le : (n - 1) / (p - 1) ≤ (prodPart n).factorization p :=
        prodPart_factorization_ge_pred_div_pred_of_odd_prime n p hp hp2
      unfold numer
      exact le_trans (le_trans hfac_le hprod_le)
        ((Nat.factorization_le_factorization_mul_right (a := 2 ^ (n - 1)) (b := prodPart n)
          (pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0))) p)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma selected_factor_val_ge {p j : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hj : j ≠ 0) :
    1 + padicValNat p j ≤ padicValNat p (2 ^ ((p - 1) * j) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  let x := 2 ^ (p - 1)
  have hxgt : 1 < x := by
    have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
    have hexp : p - 1 ≠ 0 := by omega
    exact Nat.one_lt_pow hexp (by norm_num : 1 < 2)
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hfermat : p ∣ x - 1 := by
    have hm : 2 ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow (p - 1) 2 (by norm_num : 0 < 2))).mp hm.symm
  have hxnot : ¬ p ∣ x := by
    intro hpx
    have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hpx
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
  have hval := padicValNat.pow_sub_pow (x := x) (y := 1) (p := p) hodd hxgt hfermat hxnot (n := j) hj
  have hone : 1 ≤ padicValNat p (x - 1) := one_le_padicValNat_of_dvd (p := p) (by omega) hfermat
  calc
    1 + padicValNat p j ≤ padicValNat p (x - 1) + padicValNat p j := Nat.add_le_add_right hone _
    _ = padicValNat p (x ^ j - 1 ^ j) := hval.symm
    _ = padicValNat p (2 ^ ((p - 1) * j) - 1) := by simp [x, pow_mul]

lemma sum_padic_range_succ_eq_factorial (p r : ℕ) (hp : Nat.Prime p) :
    (∑ t ∈ Finset.range r, padicValNat p (t + 1)) = padicValNat p r.factorial := by
  have hnon : ∀ t ∈ Finset.range r, t + 1 ≠ 0 := by simp
  have hfac := Nat.factorization_prod (S := Finset.range r) (g := fun t => t + 1) hnon
  have hprod : (∏ t ∈ Finset.range r, (t + 1)) = r.factorial := by
    exact Finset.prod_range_add_one_eq_factorial r
  rw [← Nat.factorization_def r.factorial hp]
  rw [← hprod]
  rw [hfac]
  simpa using Finset.sum_congr rfl (fun t ht => (Nat.factorization_def (t + 1) hp).symm)

lemma selected_prod_val_ge (p r : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    r + padicValNat p r.factorial ≤
      padicValNat p (∏ t ∈ Finset.range r, (2 ^ ((p - 1) * (t + 1)) - 1)) := by
  have hnon : ∀ t ∈ Finset.range r, 2 ^ ((p - 1) * (t + 1)) - 1 ≠ 0 := by
    intro t ht
    have hpos : 0 < (p - 1) * (t + 1) := by
      have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
      exact Nat.mul_pos (by omega) (Nat.succ_pos t)
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hpos.ne' (by norm_num : 1 < 2))
  have hfac := Nat.factorization_prod (S := Finset.range r)
      (g := fun t => 2 ^ ((p - 1) * (t + 1)) - 1) hnon
  rw [← Nat.factorization_def (∏ t ∈ Finset.range r, (2 ^ ((p - 1) * (t + 1)) - 1)) hp]
  rw [hfac]
  rw [Finset.sum_apply']
  have h1 : r + padicValNat p r.factorial =
      (∑ t ∈ Finset.range r, (1 + padicValNat p (t + 1))) := by
    rw [Finset.sum_add_distrib]
    simp [sum_padic_range_succ_eq_factorial p r hp]
  have h2 : (∑ t ∈ Finset.range r, (1 + padicValNat p (t + 1))) ≤
      ∑ t ∈ Finset.range r, padicValNat p (2 ^ ((p - 1) * (t + 1)) - 1) := by
    exact Finset.sum_le_sum (fun t ht => selected_factor_val_ge hp hp2 (Nat.succ_ne_zero t))
  have h3 : (∑ t ∈ Finset.range r, padicValNat p (2 ^ ((p - 1) * (t + 1)) - 1)) =
      ∑ k ∈ Finset.range r, ((fun t => 2 ^ ((p - 1) * (t + 1)) - 1) k).factorization p := by
    simp_rw [Nat.factorization_def _ hp]
  exact h1.le.trans (h2.trans_eq h3)

lemma selected_prod_dvd_prodPart_pred {n p r : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hnpr : n = p * r) (hr : 2 ≤ r) :
    (∏ t ∈ Finset.range r, (2 ^ ((p - 1) * (t + 1)) - 1)) ∣ prodPart (n - 1) := by
  classical
  let f : ℕ → ℕ := fun t => (p - 1) * (t + 1)
  let s : Finset ℕ := (Finset.range r).image f
  have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
  have hpred_pos : 0 < p - 1 := by omega
  have hinj : Function.Injective f := by
    intro a b hab
    exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_left hpred_pos hab)
  have hprod_image : (∏ t ∈ Finset.range r, (2 ^ (f t) - 1)) = ∏ k ∈ s, (2 ^ k - 1) := by
    dsimp [s]
    rw [Finset.prod_image]
    intro a ha b hb hab
    exact hinj hab
  rw [hprod_image]
  unfold prodPart
  apply Finset.prod_dvd_prod_of_subset
  intro k hk
  simp only [s, Finset.mem_image, Finset.mem_range] at hk
  rcases hk with ⟨t, ht, rfl⟩
  rw [Finset.mem_Ico]
  constructor
  · exact Nat.mul_pos hpred_pos (Nat.succ_pos t)
  · have hle : (p - 1) * (t + 1) ≤ (p - 1) * r := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt ht)
    have hlt : (p - 1) * r < n - 1 := by
      rw [hnpr]
      have hsum : (p - 1) * r + r = p * r := by
        nth_rw 2 [← one_mul r]
        rw [← Nat.add_mul]
        have hp1 : p - 1 + 1 = p := by omega
        rw [hp1]
      omega
    exact lt_of_le_of_lt hle hlt

lemma odd_prime_dvd_a_pred {n p : ℕ} (hn : 2 < n) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hproper : p < n) : p ∣ a (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hpn with ⟨r, hnpr⟩
  have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
  have hr2 : 2 ≤ r := by
    by_contra h
    have hrle : r ≤ 1 := by omega
    interval_cases r
    · rw [mul_zero] at hnpr; omega
    · rw [mul_one] at hnpr; omega
  let m := n - 1
  have hm0 : m ≠ 0 := by omega
  have hsel_dvd : (∏ t ∈ Finset.range r, (2 ^ ((p - 1) * (t + 1)) - 1)) ∣ prodPart m := by
    dsimp [m]
    exact selected_prod_dvd_prodPart_pred hp hp2 hnpr hr2
  have hsel_le_prod : padicValNat p (∏ t ∈ Finset.range r, (2 ^ ((p - 1) * (t + 1)) - 1)) ≤
      padicValNat p (prodPart m) := by
    exact (padicValNat_dvd_iff_le (p := p) (ha := prodPart_ne_zero m)).mp
      ((pow_padicValNat_dvd (p := p) (n := ∏ t ∈ Finset.range r, (2 ^ ((p - 1) * (t + 1)) - 1))).trans hsel_dvd)
  have hprod_lower : r + padicValNat p r.factorial ≤ padicValNat p (prodPart m) := by
    exact (selected_prod_val_ge p r hp hp2).trans hsel_le_prod
  have hfac_r_le : padicValNat p (r - 1).factorial ≤ padicValNat p r.factorial := by
    have hdvd : (r - 1).factorial ∣ r.factorial := Nat.factorial_dvd_factorial (by omega)
    exact (padicValNat_dvd_iff_le (p := p) (ha := Nat.factorial_ne_zero r)).mp
      ((pow_padicValNat_dvd (p := p) (n := (r - 1).factorial)).trans hdvd)
  have hprod_lower' : r + padicValNat p (r - 1).factorial ≤ padicValNat p (prodPart m) := by
    exact (Nat.add_le_add_left hfac_r_le r).trans hprod_lower
  have hfac_eq : padicValNat p m.factorial = padicValNat p (r - 1).factorial + (r - 1) := by
    have hm_eq : m = p * (r - 1) + (p - 1) := by
      dsimp [m]
      rw [hnpr]
      have hsum : p * (r - 1) + (p - 1) + 1 = p * r := by
        rw [Nat.add_assoc]
        have hp1 : p - 1 + 1 = p := by omega
        rw [hp1]
        nth_rw 2 [← Nat.mul_one p]
        rw [← Nat.mul_add]
        have hr1 : r - 1 + 1 = r := by omega
        rw [hr1]
      omega
    rw [hm_eq]
    rw [padicValNat_factorial_mul_add (p := p) (m := r - 1) (n := p - 1) (by omega)]
    rw [padicValNat_factorial_mul (p := p) (n := r - 1)]
  have hnum_lower : padicValNat p m.factorial + 1 ≤ padicValNat p (numer m) := by
    have hprod_to_num : padicValNat p (prodPart m) ≤ padicValNat p (numer m) := by
      rw [← Nat.factorization_def (prodPart m) hp, ← Nat.factorization_def (numer m) hp]
      unfold numer
      exact (Nat.factorization_le_factorization_mul_right (a := 2 ^ (m - 1)) (b := prodPart m)
        (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) p)
    have : padicValNat p m.factorial + 1 = r + padicValNat p (r - 1).factorial := by
      rw [hfac_eq]
      omega
    rw [this]
    exact hprod_lower'.trans hprod_to_num
  rw [a_eq_numer_div m hm0]
  apply dvd_of_one_le_padicValNat (p := p)
  rw [padicValNat.div_of_dvd (factorial_dvd_numer m)]
  omega

lemma two_not_dvd_two_pow_sub_one {k : ℕ} (hk : k ≠ 0) : ¬ 2 ∣ 2 ^ k - 1 := by
  cases k with
  | zero => exact (hk rfl).elim
  | succ j =>
      rw [pow_succ, mul_comm (2 ^ j) 2]
      have h : 2 * 2 ^ j - 1 = 2 * (2 ^ j - 1) + 1 := by
        have hle : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num : 0 < 2)
        omega
      rw [h]
      exact Nat.two_not_dvd_two_mul_add_one _

lemma pow_two_ge_add_one (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      rw [pow_succ']
      have hpos : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num : 0 < 2)
      nlinarith

lemma pow_two_ge_add_two {e : ℕ} (he : 2 ≤ e) : e + 2 ≤ 2 ^ e := by
  induction e with
  | zero => omega
  | succ e ih =>
      by_cases he2 : 2 ≤ e
      · have ih' := ih he2
        rw [pow_succ']
        have hpos : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num : 0 < 2)
        nlinarith
      · have hle : e ≤ 1 := by omega
        interval_cases e
        · omega
        · norm_num

lemma padicValNat_two_prodPart (m : ℕ) : padicValNat 2 (prodPart m) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  unfold prodPart
  exact Prime.not_dvd_finset_prod Nat.prime_two.prime (fun k hk => by
    rw [Finset.mem_Ico] at hk
    exact two_not_dvd_two_pow_sub_one (by omega))

lemma padicValNat_two_factorial_pow_sub_one (e : ℕ) :
    padicValNat 2 ((2 ^ e - 1).factorial) = 2 ^ e - 1 - e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have harg : 2 ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 := by
        have hle : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num : 0 < 2)
        rw [pow_succ']
        omega
      rw [harg]
      rw [padicValNat_factorial_mul_add (p := 2) (m := 2 ^ e - 1) (n := 1) (by norm_num)]
      rw [padicValNat_factorial_mul (p := 2) (n := 2 ^ e - 1)]
      rw [ih]
      have hge : e + 1 ≤ 2 ^ e := pow_two_ge_add_one e
      omega

lemma padicValNat_two_numer_pow_sub_one (e : ℕ) :
    padicValNat 2 (numer (2 ^ e - 1)) = 2 ^ e - 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold numer
  rw [padicValNat.mul]
  · rw [padicValNat.prime_pow, padicValNat_two_prodPart]
    have hpow : 2 ^ e - 1 - 1 = 2 ^ e - 2 := by omega
    rw [hpow]
    omega
  · exact pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)
  · exact prodPart_ne_zero (2 ^ e - 1)

lemma padicValNat_two_a_pow_sub_one {e : ℕ} (he : 2 ≤ e) :
    padicValNat 2 (a (2 ^ e - 1)) = e - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : 2 ^ e - 1 ≠ 0 := by
    have hgt : 1 < 2 ^ e := Nat.one_lt_pow (by omega : e ≠ 0) (by norm_num : 1 < 2)
    omega
  rw [a_eq_numer_div (2 ^ e - 1) hm0]
  rw [padicValNat.div_of_dvd (factorial_dvd_numer (2 ^ e - 1))]
  rw [padicValNat_two_numer_pow_sub_one e, padicValNat_two_factorial_pow_sub_one e]
  have hpowge : e + 1 ≤ 2 ^ e := pow_two_ge_add_one e
  omega

lemma not_dvd_power_two {e n : ℕ} (he : 2 ≤ e) (hn : n = 2 ^ e) :
    ¬ n ∣ a (n - 1) + 2 ^ (n - 2) := by
  intro hdiv
  subst n
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpowdvd : 2 ^ e ∣ 2 ^ (2 ^ e - 2) := by
    exact Nat.pow_dvd_pow 2 (by
      have hpowge : e + 2 ≤ 2 ^ e := pow_two_ge_add_two he
      omega)
  have hAdvd : 2 ^ e ∣ a (2 ^ e - 1) := (Nat.dvd_add_left hpowdvd).mp hdiv
  have hval := (padicValNat_dvd_iff_le (p := 2) (a := a (2 ^ e - 1)) ?_).mp hAdvd
  · rw [padicValNat_two_a_pow_sub_one he] at hval
    omega
  · intro ha0
    have hval0 : padicValNat 2 (a (2 ^ e - 1)) = 0 := by rw [ha0]; simp [padicValNat]
    rw [padicValNat_two_a_pow_sub_one he] at hval0
    omega

lemma not_dvd_of_odd_prime_divisor {n p : ℕ} (hn : 2 < n) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hproper : p < n) : ¬ n ∣ a (n - 1) + 2 ^ (n - 2) := by
  intro hnS
  have hpa : p ∣ a (n - 1) := odd_prime_dvd_a_pred hn hp hp2 hpn hproper
  have hpS : p ∣ a (n - 1) + 2 ^ (n - 2) := hpn.trans hnS
  have hpPow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hpa).mp hpS
  have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)





/--
If none of the factors `2^k - 1`, `1 ≤ k < p - 1`, vanishes modulo `p`,
then no positive exponent below `p - 1` sends `2` to `1` in `ZMod p`.
This is the elementary product-to-order step needed in the primitive-root part
of the conjecture.
-/
lemma a091669_no_smaller_pow_of_product_ne_zero (p : ℕ)
    (hprod : (∏ k ∈ Finset.Ico 1 (p - 1), ((2 : ZMod p) ^ k - 1)) ≠ 0) :
    ∀ l : ℕ, 0 < l → l < p - 1 → (2 : ZMod p) ^ l ≠ 1 := by
  intro l hl0 hl hpow
  apply hprod
  exact Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨hl0, hl⟩) (by simp [hpow])

/--
For an odd prime `p`, if `2^l ≠ 1` for every `0 < l < p - 1`, then `2` is a
primitive root modulo `p` (with the order written as `Nat.totient p`).
-/
lemma a091669_isPrimitiveRoot_two_of_prime_of_no_smaller_pow
    (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hno : ∀ l : ℕ, 0 < l → l < p - 1 → (2 : ZMod p) ^ l ≠ 1) :
    IsPrimitiveRoot (2 : ZMod p) (Nat.totient p) := by
  rw [Nat.totient_prime hp]
  refine IsPrimitiveRoot.mk_of_lt (2 : ZMod p) ?_ ?_ hno
  · have hpgt : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
    omega
  · haveI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := by
        exact (ZMod.natCast_eq_zero_iff 2 p).mp h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    exact ZMod.pow_card_sub_one_eq_one h2

/--
A convenient packaged version of the previous two lemmas: for an odd prime `p`,
if `∏_{1 ≤ k < p-1} (2^k - 1) = 1` in `ZMod p`, then `2` is a primitive root
modulo `p`.
-/
lemma a091669_isPrimitiveRoot_two_of_prime_of_product_eq_one
    (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hprod : (∏ k ∈ Finset.Ico 1 (p - 1), ((2 : ZMod p) ^ k - 1)) = 1) :
    IsPrimitiveRoot (2 : ZMod p) (Nat.totient p) := by
  refine a091669_isPrimitiveRoot_two_of_prime_of_no_smaller_pow p hp hp2 ?_
  apply a091669_no_smaller_pow_of_product_ne_zero p
  rw [hprod]
  haveI : Fact p.Prime := ⟨hp⟩
  exact one_ne_zero


end A091669

open A091669

/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdiv
  by_cases hp : Nat.Prime n
  · have hn2 : n ≠ 2 := by omega
    have hprod := a091669_prime_product_eq_one_of_factorial_dvd n hp hn2 (factorial_dvd_numer (n - 1)) hdiv
    exact ⟨hp, a091669_isPrimitiveRoot_two_of_prime_of_product_eq_one n hp hn2 hprod⟩
  · exfalso
    have hn0 : n ≠ 0 := by omega
    rcases Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by norm_num) with ⟨e, m, hm_odd, hn_eq⟩
    by_cases hm1 : m = 1
    · have hn_pow : n = 2 ^ e := by
        rw [hn_eq, hm1, mul_one]
      have he : 2 ≤ e := by
        by_contra he_lt
        have he_le : e ≤ 1 := by omega
        interval_cases e <;> norm_num [hn_pow] at hn
      exact not_dvd_power_two he hn_pow hdiv
    · rcases Nat.exists_prime_and_dvd hm1 with ⟨p, hpp, hpm⟩
      have hp2 : p ≠ 2 := by
        intro hpeq
        apply hm_odd
        rwa [hpeq] at hpm
      have hpn : p ∣ n := by
        rw [hn_eq]
        exact dvd_mul_of_dvd_right hpm (2 ^ e)
      have hp_ne_n : p ≠ n := by
        intro hpeq
        apply hp
        rwa [← hpeq]
      have hproper : p < n := by
        have hle : p ≤ n := Nat.le_of_dvd (by omega) hpn
        exact lt_of_le_of_ne hle hp_ne_n
      exact not_dvd_of_odd_prime_divisor hn hpp hp2 hpn hproper hdiv
