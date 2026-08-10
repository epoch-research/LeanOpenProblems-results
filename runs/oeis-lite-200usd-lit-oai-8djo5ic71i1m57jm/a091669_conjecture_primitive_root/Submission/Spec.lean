import FormalConjectures.Util.ProblemImports

open Nat BigOperators

noncomputable def a (n : ℕ) : ℕ :=
  if _ : n = 0 then 0
  else
    let n_pred : ℕ := n.pred
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
    let denominator : ℕ := n.factorial
    numerator / denominator


lemma prime_dvd_two_pow_pred_sub_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ 2 ^ (q - 1) - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hge : 2 ≤ q := hq.two_le
    exact hq2 (le_antisymm hle hge)
  have hpow : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  rw [← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_sub]
  · simpa using sub_eq_zero.mpr hpow
  · exact Nat.one_le_pow (q - 1) 2 (by norm_num)

lemma prime_dvd_two_pow_pred_mul_sub_one {q t : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ 2 ^ ((q - 1) * t) - 1 := by
  have hbase : q ∣ 2 ^ (q - 1) - 1 := prime_dvd_two_pow_pred_sub_one hq hq2
  have hdiv : 2 ^ (q - 1) - 1 ∣ (2 ^ (q - 1)) ^ t - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ (q - 1)) 1 t
  exact hbase.trans (by simpa [pow_mul] using hdiv)

lemma prime_pow_divides_mersenne_product {q m : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ^ ((m - 1) / (q - 1)) ∣ (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) := by
  classical
  let r := (m - 1) / (q - 1)
  let S : Finset ℕ := (Finset.Icc 1 r).image (fun t => (q - 1) * t)
  have hqge3 : 3 ≤ q := by
    have h2 := hq.two_le
    omega
  have hq1pos : 0 < q - 1 := by omega
  have hq1nz : q - 1 ≠ 0 := by omega
  have hq1ge : 1 ≤ q - 1 := by omega
  have himg_card : S.card = r := by
    dsimp [S]
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      exact Nat.mul_left_cancel hq1pos hab
  have hsubset : S ⊆ Finset.Ico 1 m := by
    intro k hk
    simp only [S, Finset.mem_image, Finset.mem_Icc] at hk
    rcases hk with ⟨t, ht, rfl⟩
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.mul_pos hq1pos ht.1
    · have ht_le : t ≤ r := ht.2
      have hmul : (q - 1) * t ≤ (q - 1) * r := Nat.mul_le_mul_left _ ht_le
      have hr : (q - 1) * r ≤ m - 1 := by
        dsimp [r]
        exact Nat.mul_div_le (m - 1) (q - 1)
      have hlepred : (q - 1) * t ≤ m - 1 := le_trans hmul hr
      have hkpos : 0 < (q - 1) * t := Nat.mul_pos hq1pos ht.1
      have hmpos : 0 < m := by omega
      exact Nat.lt_of_le_pred hmpos hlepred
  have hconst : (∏ k ∈ S, q) ∣ ∏ k ∈ S, (2 ^ k - 1) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro k hk
    simp only [S, Finset.mem_image, Finset.mem_Icc] at hk
    rcases hk with ⟨t, ht, rfl⟩
    exact prime_dvd_two_pow_pred_mul_sub_one hq hq2
  have hsel_full : (∏ k ∈ S, (2 ^ k - 1)) ∣ (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) :=
    Finset.prod_dvd_prod_of_subset S (Finset.Ico 1 m) (fun k => 2 ^ k - 1) hsubset
  refine dvd_trans ?_ hsel_full
  convert hconst using 1
  simp [himg_card, r]

lemma factorization_factorial_le_pred_div_pred {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) :
    (m.factorial).factorization q ≤ (m - 1) / (q - 1) := by
  have hq1pos : 0 < q - 1 := by have := hq.two_le; omega
  rw [Nat.le_div_iff_mul_le hq1pos]
  have hsdpos : 0 < (q.digits m).sum := by
    have hnil : q.digits m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
    exact Nat.sum_pos_iff_exists_pos.mpr
      ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero q hm)⟩
  have hlt : m - (q.digits m).sum < m := by
    exact Nat.sub_lt (Nat.pos_of_ne_zero hm) hsdpos
  have heq := Nat.sub_one_mul_factorization_factorial (n := m) hq
  have heq' : (m.factorial).factorization q * (q - 1) = m - (q.digits m).sum := by
    simpa [Nat.mul_comm] using heq
  have hle : m - (q.digits m).sum ≤ m - 1 := Nat.le_pred_of_lt hlt
  simpa [heq'] using hle

lemma factorization_factorial_pred_mul_prime {p s : ℕ} (hp : p.Prime) (hs : 0 < s) :
    ((p * s - 1).factorial).factorization p = (s.factorial).factorization p + s - 1 - s.factorization p := by
  have hpspos : 0 < p * s := Nat.mul_pos hp.pos hs
  have hsucc : p * s - 1 + 1 = p * s := Nat.sub_add_cancel (Nat.succ_le_of_lt hpspos)
  have hfacsucc := congrArg (fun x => x.factorization p) (show (p * s)! = (p * s - 1 + 1)! by rw [hsucc])
  -- maybe easier use factorial_succ
  have hmul : (p * s)! = (p * s) * (p * s - 1)! := by
    rw [← hsucc, Nat.factorial_succ, hsucc]
  have hfact : ((p * s)!).factorization p = (p * s).factorization p + ((p * s - 1)!).factorization p := by
    rw [hmul, Nat.factorization_mul]
    · rfl
    · exact Nat.ne_of_gt hpspos
    · exact factorial_ne_zero _
  have hps_factor : (p * s).factorization p = 1 + s.factorization p := by
    rw [Nat.factorization_mul hp.ne_zero (by exact Nat.pos_iff_ne_zero.mp hs)]
    simp [hp.factorization_self]
  have hmulfac := Nat.factorization_factorial_mul (n := s) hp
  -- (p*s)! val = s! val + s
  omega

lemma factorization_factorial_pred_mul_prime_add_one_le {p s : ℕ} (hp : p.Prime) (hs2 : 2 ≤ s) :
    ((p * s - 1).factorial).factorization p + 1 ≤ (p * s - 2) / (p - 1) := by
  have hspos : 0 < s := by omega
  have hs1pos : s - 1 ≠ 0 := by omega
  have hprev := factorization_factorial_pred_mul_prime (p := p) (s := s) hp hspos
  have hs_fac : (s.factorial).factorization p = (s - 1).factorial.factorization p + s.factorization p := by
    have hs_succ : s - 1 + 1 = s := by omega
    rw [← hs_succ, Nat.factorial_succ]
    rw [Nat.factorization_mul]
    · simp [Nat.add_comm]
    · exact Nat.succ_ne_zero _
    · exact factorial_ne_zero _
  have hprev' : ((p * s - 1).factorial).factorization p = (s - 1).factorial.factorization p + (s - 1) := by
    rw [hprev, hs_fac]
    omega
  have hbound := factorization_factorial_le_pred_div_pred (q := p) (m := s - 1) hp hs1pos
  have hdivexpr : (p * s - 2) / (p - 1) = s + (s - 2) / (p - 1) := by
    have hp1pos : 0 < p - 1 := by have := hp.two_le; omega
    have hrewrite : p * s - 2 = (p - 1) * s + (s - 2) := by
      have hpdecomp : p * s = (p - 1) * s + s := by
        have hp_eq : p = (p - 1) + 1 := by omega
        calc
          p * s = ((p - 1) + 1) * s := congrArg (fun x => x * s) hp_eq
          _ = (p - 1) * s + s := by rw [Nat.add_mul, one_mul]
      omega
    rw [hrewrite]
    exact Nat.mul_add_div hp1pos s (s - 2)
  rw [hprev', hdivexpr]
  have hbound' : (s - 1).factorial.factorization p ≤ (s - 2) / (p - 1) := by simpa using hbound
  omega

def mersProd (m : ℕ) : ℕ := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
def anum (m : ℕ) : ℕ := 2 ^ (m - 1) * mersProd m

lemma mersProd_ne_zero (m : ℕ) : mersProd m ≠ 0 := by
  unfold mersProd
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hkpos : 0 < k := hk.1
  have hgt : 1 < 2 ^ k := Nat.one_lt_pow hkpos.ne' (by norm_num)
  omega

lemma anum_ne_zero (m : ℕ) : anum m ≠ 0 := by
  unfold anum
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mersProd_ne_zero m)

lemma odd_prime_mul_factorial_dvd_anum_pred_mul {p s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs2 : 2 ≤ s) :
    p * ((p * s - 1).factorial) ∣ anum (p * s - 1) := by
  classical
  let m := p * s - 1
  have hmpos : 0 < m := by
    dsimp [m]
    have hpsge : 2 * 2 ≤ p * s := Nat.mul_le_mul hp.two_le hs2
    omega
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hp.ne_zero (factorial_ne_zero m)) (anum_ne_zero m)]
  intro q
  by_cases hqprime : q.Prime
  · have hnumfac : (anum m).factorization q = (2 ^ (m - 1)).factorization q + (mersProd m).factorization q := by
      unfold anum
      rw [Nat.factorization_mul]
      · rfl
      · exact pow_ne_zero _ (by norm_num)
      · exact mersProd_ne_zero m
    have hleft : (p * m.factorial).factorization q = p.factorization q + m.factorial.factorization q := by
      rw [Nat.factorization_mul hp.ne_zero (factorial_ne_zero m)]
      rfl
    rw [hleft, hnumfac]
    by_cases hq2 : q = 2
    · subst q
      have hp_not_dvd2 : ¬ 2 ∣ p := by
        intro hd
        have heq : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
        exact hp2 heq.symm
      have hpfac0 : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hp_not_dvd2
      have hdenlt : m.factorial.factorization 2 < m := by
        rw [Nat.factorization_def _ Nat.prime_two]
        exact padicValNat_factorial_lt_of_ne_zero 2 (Nat.ne_of_gt hmpos)
      have hpowfac : (2 ^ (m - 1)).factorization 2 = m - 1 := Nat.factorization_pow_self Nat.prime_two
      rw [hpfac0, zero_add, hpowfac]
      omega
    · have hq2ne : q ≠ 2 := hq2
      have hprod_dvd := prime_pow_divides_mersenne_product (m := m) hqprime hq2ne
      have hprod_ge : (m - 1) / (q - 1) ≤ (mersProd m).factorization q := by
        exact (hqprime.pow_dvd_iff_le_factorization (mersProd_ne_zero m)).mp hprod_dvd
      by_cases hqp : q = p
      · subst q
        have hpfac : p.factorization p = 1 := hp.factorization_self
        have hden_add := factorization_factorial_pred_mul_prime_add_one_le (p := p) (s := s) hp hs2
        have hprod_ge' : (p * s - 2) / (p - 1) ≤ (mersProd m).factorization p := by
          convert hprod_ge using 2
        have hden_add' : m.factorial.factorization p + 1 ≤ (p * s - 2) / (p - 1) := by
          convert hden_add using 2
        rw [hpfac, one_add]
        omega
      · have hpfac0 : p.factorization q = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp hd)
        have hden_le := factorization_factorial_le_pred_div_pred (q := q) (m := m) hqprime (Nat.ne_of_gt hmpos)
        rw [hpfac0, zero_add]
        omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hqprime]

lemma factorial_dvd_anum (m : ℕ) : m.factorial ∣ anum m := by
  classical
  rw [← Nat.factorization_le_iff_dvd (factorial_ne_zero m) (anum_ne_zero m)]
  intro q
  by_cases hqprime : q.Prime
  · have hnumfac : (anum m).factorization q = (2 ^ (m - 1)).factorization q + (mersProd m).factorization q := by
      unfold anum
      rw [Nat.factorization_mul]
      · rfl
      · exact pow_ne_zero _ (by norm_num)
      · exact mersProd_ne_zero m
    rw [hnumfac]
    by_cases hq2 : q = 2
    · subst q
      have hpowfac : (2 ^ (m - 1)).factorization 2 = m - 1 := Nat.factorization_pow_self Nat.prime_two
      rw [hpowfac]
      by_cases hm0 : m = 0
      · subst m; simp
      · have hdenlt : m.factorial.factorization 2 < m := by
          rw [Nat.factorization_def _ Nat.prime_two]
          exact padicValNat_factorial_lt_of_ne_zero 2 hm0
        omega
    · have hprod_dvd := prime_pow_divides_mersenne_product (m := m) hqprime hq2
      have hprod_ge : (m - 1) / (q - 1) ≤ (mersProd m).factorization q := by
        exact (hqprime.pow_dvd_iff_le_factorization (mersProd_ne_zero m)).mp hprod_dvd
      by_cases hm0 : m = 0
      · subst m; simp
      · have hden_le := factorization_factorial_le_pred_div_pred (q := q) (m := m) hqprime hm0
        omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hqprime]

lemma factorization_two_factorial_two_pow_sub_one (e : ℕ) :
    ((2 ^ e - 1).factorial).factorization 2 = 2 ^ e - 1 - e := by
  induction e with
  | zero => simp
  | succ e ih =>
      have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) _
      have hpred := factorization_factorial_pred_mul_prime (p := 2) (s := 2 ^ e) Nat.prime_two hpowpos
      have htwofac : (2 ^ e).factorization 2 = e := Nat.factorization_pow_self Nat.prime_two
      have hfac_succ : ((2 ^ e).factorial).factorization 2 = ((2 ^ e - 1).factorial).factorization 2 + (2 ^ e).factorization 2 := by
        have hs : 2 ^ e - 1 + 1 = 2 ^ e := Nat.sub_add_cancel (Nat.succ_le_of_lt hpowpos)
        rw [← hs, Nat.factorial_succ, Nat.factorization_mul]
        · simp [Pi.add_apply, Nat.add_comm]
        · exact Nat.succ_ne_zero _
        · exact factorial_ne_zero _
      have harg : 2 * 2 ^ e - 1 = 2 ^ (e + 1) - 1 := by rw [pow_succ']
      rw [← harg]
      rw [hpred, hfac_succ, htwofac, ih]
      have he_le : e ≤ 2 ^ e - 1 := Nat.le_pred_of_lt (Nat.lt_two_pow_self (n := e))
      omega

lemma mersProd_factorization_two (m : ℕ) : (mersProd m).factorization 2 = 0 := by
  unfold mersProd
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hkpos : 0 < k := hk.1
    have hpow_dvd : 2 ∣ 2 ^ k := by
      rcases k with _ | k
      · cases hkpos
      · exact ⟨2 ^ k, by rw [pow_succ']⟩
    have hone : 2 ∣ 1 := by
      have hsum : (2 ^ k - 1) + 1 = 2 ^ k := Nat.sub_add_cancel (Nat.one_le_pow k 2 (by norm_num))
      exact (Nat.dvd_add_iff_right hd).mpr (by simpa [hsum] using hpow_dvd)
    norm_num at hone
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hkpos : 0 < k := hk.1
    have hgt : 1 < 2 ^ k := Nat.one_lt_pow hkpos.ne' (by norm_num)
    omega

lemma factorization_two_anum_div_factorial_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) :
    ((anum (2 ^ e - 1) / (2 ^ e - 1).factorial).factorization 2) = e - 1 := by
  let m := 2 ^ e - 1
  have hdiv := factorial_dvd_anum m
  have hfacdiv : (anum m / m.factorial).factorization 2 = (anum m).factorization 2 - m.factorial.factorization 2 := by
    simpa using congrArg (fun f => f 2) (Nat.factorization_div hdiv)
  have hnum : (anum m).factorization 2 = m - 1 := by
    unfold anum
    rw [Nat.factorization_mul]
    · simp [Pi.add_apply, Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two, mersProd_factorization_two]
    · exact pow_ne_zero _ (by norm_num)
    · exact mersProd_ne_zero m
  have hden : m.factorial.factorization 2 = 2 ^ e - 1 - e := by
    dsimp [m]
    exact factorization_two_factorial_two_pow_sub_one e
  rw [hnum, hden] at hfacdiv
  dsimp [m] at hfacdiv
  have he_le : e ≤ 2 ^ e - 1 := Nat.le_pred_of_lt (Nat.lt_two_pow_self (n := e))
  omega

lemma not_two_pow_dvd_anum_div_factorial_two_pow_sub_one {e : ℕ} (he : 2 ≤ e) :
    ¬ 2 ^ e ∣ (anum (2 ^ e - 1) / (2 ^ e - 1).factorial) := by
  intro hd
  let m := 2 ^ e - 1
  have hdiv := factorial_dvd_anum m
  have hquot_ne : anum m / m.factorial ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by exact Nat.pos_of_ne_zero (anum_ne_zero m)) hdiv) (factorial_pos m))
  have hlefac : e ≤ (anum m / m.factorial).factorization 2 := by
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hquot_ne).mp (by simpa [m] using hd)
  have hfac := factorization_two_anum_div_factorial_two_pow_sub_one (e := e) (by omega : 1 ≤ e)
  dsimp [m] at hlefac
  rw [hfac] at hlefac
  omega

lemma le_two_pow_sub_two {e : ℕ} (he : 2 ≤ e) : e ≤ 2 ^ e - 2 := by
  induction e with
  | zero => omega
  | succ e ih =>
      by_cases he2 : 2 ≤ e
      · have ih' := ih he2
        rw [pow_succ']
        have hpos : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num)
        omega
      · have he_small : e = 0 ∨ e = 1 := by omega
        rcases he_small with rfl | rfl
        · omega
        · norm_num


lemma a_eq_anum_div {m : ℕ} (hm : m ≠ 0) : a m = anum m / m.factorial := by
  unfold a anum mersProd
  simp [hm, Nat.pred_eq_sub_one]

lemma prime_dvd_a_of_mul_factorial_dvd {p m : ℕ} (hm : m ≠ 0)
    (h : p * m.factorial ∣ anum m) : p ∣ a m := by
  rw [a_eq_anum_div hm]
  have hden : m.factorial ∣ anum m := factorial_dvd_anum m
  exact (Nat.dvd_div_iff_mul_dvd hden).2 (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h)

lemma odd_proper_prime_dvd_a_pred {p n : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hpn : p ∣ n) (hplt : p < n) : p ∣ a (n - 1) := by
  rcases hpn with ⟨s, rfl⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hpodd
  have hs2 : 2 ≤ s := by
    by_contra hsnot
    have hsle : s ≤ 1 := by omega
    interval_cases s
    · simp at hplt
    · simp at hplt
  have hm : p * s - 1 ≠ 0 := by
    have hpsge : 2 * 2 ≤ p * s := Nat.mul_le_mul hp.two_le hs2
    omega
  have hdvd : p * ((p * s - 1).factorial) ∣ anum (p * s - 1) :=
    odd_prime_mul_factorial_dvd_anum_pred_mul hp hp2 hs2
  simpa using prime_dvd_a_of_mul_factorial_dvd (p := p) (m := p * s - 1) hm hdvd

lemma not_dvd_pow_two_of_odd_prime {p k : ℕ} (hp : p.Prime) (hpodd : Odd p) : ¬ p ∣ 2 ^ k := by
  intro hd
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hpodd
  have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two)

lemma contradiction_of_odd_proper_prime {n p : ℕ}
    (h : n ∣ a (n - 1) + 2 ^ (n - 2))
    (hp : p.Prime) (hpodd : Odd p) (hpn : p ∣ n) (hplt : p < n) : False := by
  have hpa : p ∣ a (n - 1) := odd_proper_prime_dvd_a_pred hp hpodd hpn hplt
  have hpsum : p ∣ a (n - 1) + 2 ^ (n - 2) := hpn.trans h
  have hp2pow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_iff_right (k := p) (m := a (n - 1)) (n := 2 ^ (n - 2)) hpa).mpr hpsum
  exact not_dvd_pow_two_of_odd_prime hp hpodd hp2pow

lemma contradiction_of_two_power {n e : ℕ} (hn : n > 2)
    (h : n ∣ a (n - 1) + 2 ^ (n - 2)) (hne : n = 2 ^ e) : False := by
  subst n
  have he2 : 2 ≤ e := by
    by_contra he
    have : e ≤ 1 := by omega
    interval_cases e <;> norm_num at hn
  have hterm : 2 ^ e ∣ 2 ^ (2 ^ e - 2) := by
    exact pow_dvd_pow 2 (le_two_pow_sub_two he2)
  have hsum : 2 ^ e ∣ a (2 ^ e - 1) + 2 ^ (2 ^ e - 2) := by
    simpa using h
  have ha_dvd : 2 ^ e ∣ a (2 ^ e - 1) := (Nat.dvd_add_iff_left (k := 2 ^ e) (m := a (2 ^ e - 1)) (n := 2 ^ (2 ^ e - 2)) hterm).mpr hsum
  have hm : 2 ^ e - 1 ≠ 0 := by
    have : 1 < 2 ^ e := Nat.one_lt_pow (by omega : e ≠ 0) (by norm_num)
    omega
  rw [a_eq_anum_div hm] at ha_dvd
  exact not_two_pow_dvd_anum_div_factorial_two_pow_sub_one he2 ha_dvd

lemma prime_dvd_a_pred_of_prime_not_primitive {p : ℕ} (hp : p.Prime) (hpgt2 : 2 < p)
    (hnprim : ¬ IsPrimitiveRoot (2 : ZMod p) (Nat.totient p)) : p ∣ a (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  let r := orderOf (2 : ZMod p)
  have htot : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hr_ne : r ≠ p - 1 := by
    intro hr
    apply hnprim
    rw [IsPrimitiveRoot.iff_orderOf, htot]
    exact hr
  have hr_dvd : r ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2ne
  have hrpos : 0 < r := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h2ne⟩
  have hrlt : r < p - 1 := by
    have hrle : r ≤ p - 1 := Nat.le_of_dvd (by omega) hr_dvd
    omega
  have hrmem : r ∈ Finset.Ico 1 (p - 1) := by
    rw [Finset.mem_Ico]
    exact ⟨hrpos, hrlt⟩
  have hp_dvd_factor : p ∣ 2 ^ r - 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hpow : (2 : ZMod p) ^ r = 1 := pow_orderOf_eq_one _
    rw [Nat.cast_sub]
    · simpa using sub_eq_zero.mpr hpow
    · exact Nat.one_le_pow r 2 (by norm_num)
  have hp_dvd_prod : p ∣ mersProd (p - 1) := by
    unfold mersProd
    exact hp_dvd_factor.trans (Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) hrmem)
  have hp_dvd_anum : p ∣ anum (p - 1) := by
    unfold anum
    exact dvd_mul_of_dvd_right hp_dvd_prod _
  have hfac_dvd : (p - 1).factorial ∣ anum (p - 1) := factorial_dvd_anum (p - 1)
  have hcop : p.Coprime (p - 1).factorial := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have hfacpos : 1 ≤ ((p - 1).factorial).factorization p := (hp.dvd_iff_one_le_factorization (factorial_ne_zero _)).mp hd
    have hfac0 : ((p - 1).factorial).factorization p = 0 := Nat.factorization_factorial_eq_zero_of_lt (by omega)
    omega
  have hmul : p * (p - 1).factorial ∣ anum (p - 1) :=
    hcop.mul_dvd_of_dvd_of_dvd hp_dvd_anum hfac_dvd
  have hm : p - 1 ≠ 0 := by omega
  exact prime_dvd_a_of_mul_factorial_dvd (p := p) (m := p - 1) hm hmul

theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro h
  have hnprime : Nat.Prime n := by
    by_contra hnp
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨e, hne⟩ | ⟨p, hp, hpn, hpodd⟩
    · exact contradiction_of_two_power hn h hne
    · have hplt : p < n := by
        have hle : p ≤ n := Nat.le_of_dvd (by omega) hpn
        have hpne : p ≠ n := by
          intro hpeq
          exact hnp (hpeq ▸ hp)
        omega
      exact contradiction_of_odd_proper_prime h hp hpodd hpn hplt
  constructor
  · exact hnprime
  · by_contra hnprim
    have hpa : n ∣ a (n - 1) := prime_dvd_a_pred_of_prime_not_primitive hnprime hn hnprim
    have hn_sum : n ∣ a (n - 1) + 2 ^ (n - 2) := h
    have hn_pow : n ∣ 2 ^ (n - 2) := (Nat.dvd_add_iff_right (k := n) (m := a (n - 1)) (n := 2 ^ (n - 2)) hpa).mpr hn_sum
    have hn_odd : Odd n := hnprime.odd_of_ne_two (by omega)
    exact not_dvd_pow_two_of_odd_prime hnprime hn_odd hn_pow
