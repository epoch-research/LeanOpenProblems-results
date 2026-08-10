import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

lemma val_fact_le_count (p m : ℕ) [Fact p.Prime] (hm : m ≠ 0) :
    padicValNat p m.factorial ≤ (m - 1) / (p - 1) := by
  have hp1 : 0 < p - 1 := by exact Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hm
  have hle : padicValNat p m.factorial * (p - 1) ≤ m - 1 := by
    rw [mul_comm]
    omega
  exact (Nat.le_div_iff_mul_le hp1).2 hle

lemma prime_dvd_two_pow_mul_sub_one {p j : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    p ∣ 2 ^ ((p - 1) * j) - 1 := by
  have hnot2dvd : ¬ 2 ∣ p := by
    intro h
    have h2eqp : 2 = p := (prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    exact hpodd h2eqp.symm
  have hcop : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr hnot2dvd
  have hfermat : 2 ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have hpow : (2 ^ (p - 1)) ^ j ≡ 1 ^ j [MOD p] := Nat.ModEq.pow j hfermat
  have hpow' : 2 ^ ((p - 1) * j) ≡ 1 [MOD p] := by
    simpa [pow_mul] using hpow
  have hone : 1 ≤ 2 ^ ((p - 1) * j) := by exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
  exact (Nat.modEq_iff_dvd' hone).mp hpow'.symm

lemma pow_count_dvd_prod (p m : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    p ^ ((m - 1) / (p - 1)) ∣ ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) := by
  classical
  let c := (m - 1) / (p - 1)
  let g : ℕ → ℕ := fun i => (p - 1) * (i + 1)
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hinj : Set.InjOn g (Finset.range c : Set ℕ) := by
    intro x hx y hy hxy
    dsimp [g] at hxy
    exact Nat.succ_inj.mp (Nat.mul_left_cancel hp1pos hxy)
  have hsubset : (Finset.range c).image g ⊆ Finset.Ico 1 m := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.succ_le_of_lt (Nat.mul_pos hp1pos (Nat.succ_pos i))
    · have hi1 : i + 1 ≤ c := Nat.succ_le_of_lt hi
      have hmul : (p - 1) * (i + 1) ≤ (p - 1) * c := Nat.mul_le_mul_left (p - 1) hi1
      have hc : (p - 1) * c ≤ m - 1 := by
        dsimp [c]
        exact Nat.mul_div_le (m - 1) (p - 1)
      have hle : (p - 1) * (i + 1) ≤ m - 1 := le_trans hmul hc
      have hpos : 0 < (p - 1) * (i + 1) := Nat.mul_pos hp1pos (Nat.succ_pos i)
      dsimp [g]
      omega
  have hpow_dvd_sel : p ^ c ∣ ∏ i ∈ Finset.range c, (2 ^ (g i) - 1) := by
    calc
      p ^ c = ∏ i ∈ Finset.range c, p := by simp [c]
      _ ∣ ∏ i ∈ Finset.range c, (2 ^ (g i) - 1) := by
        apply Finset.prod_dvd_prod_of_dvd
        intro i hi
        exact prime_dvd_two_pow_mul_sub_one (p:=p) (j:=i+1) (Fact.out : Nat.Prime p) hpodd
  have hprod_image : (∏ i ∈ Finset.range c, (2 ^ (g i) - 1)) =
      ∏ k ∈ (Finset.range c).image g, (2 ^ k - 1) := by
    rw [Finset.prod_image]
    intro x hx y hy hxy
    exact hinj hx hy hxy
  rw [hprod_image] at hpow_dvd_sel
  exact hpow_dvd_sel.trans (Finset.prod_dvd_prod_of_subset ((Finset.range c).image g) (Finset.Ico 1 m) (fun k => 2 ^ k - 1) hsubset)
noncomputable def num (m : ℕ) : ℕ :=
  (2 ^ (m - 1)) * (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)

lemma prod_Ico_two_pos (m : ℕ) : 0 < (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hkpos : 0 < k := by omega
  have : 1 < 2 ^ k := by
    exact one_lt_pow₀ (by norm_num : 1 < (2:ℕ)) hkpos.ne'
  omega

lemma num_pos {m : ℕ} (hm : m ≠ 0) : 0 < num m := by
  dsimp [num]
  exact Nat.mul_pos (pow_pos (by decide : 0 < 2) _) (prod_Ico_two_pos m)

lemma factorial_dvd_num {m : ℕ} (hm : m ≠ 0) : m.factorial ∣ num m := by
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero m) (Nat.ne_of_gt (num_pos hm))]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    by_cases hp2 : p = 2
    · subst p
      have hfact : padicValNat 2 m.factorial ≤ m - 1 := by simpa using (val_fact_le_count 2 m hm)
      dsimp [num]
      rw [padicValNat.mul (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)) (Nat.ne_of_gt (prod_Ico_two_pos m)), padicValNat.prime_pow]
      exact le_trans hfact (Nat.le_add_right _ _)
    · have hfact : padicValNat p m.factorial ≤ (m - 1) / (p - 1) := val_fact_le_count p m hm
      have hpowdvd : p ^ ((m - 1) / (p - 1)) ∣ (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) :=
        pow_count_dvd_prod p m hp2
      have hvalprod : (m - 1) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) := by
        exact (padicValNat_dvd_iff_le (Nat.ne_of_gt (prod_Ico_two_pos m))).1 hpowdvd
      have hvalnum : padicValNat p m.factorial ≤ padicValNat p (num m) := by
        dsimp [num]
        rw [padicValNat.mul (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)) (Nat.ne_of_gt (prod_Ico_two_pos m))]
        exact le_trans hfact (le_add_left hvalprod)
      exact hvalnum
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
lemma digit_sum_ge_p_mul_sub_one (p t : ℕ) (hp : 1 < p) (ht : 2 ≤ t) :
    p ≤ (p.digits (p * t - 1)).sum := by
  have hp0 : 0 < p := by omega
  have htpos : 0 < t := by omega
  have htt : t = (t - 1) + 1 := (Nat.sub_one_add_one (Nat.ne_of_gt htpos)).symm
  have hpt : p * t - 1 = (p - 1) + p * (t - 1) := by
    nth_rw 1 [htt]
    rw [mul_add, mul_one]
    have h1 : p * (t - 1) + p - 1 = p * (t - 1) + (p - 1) :=
      Nat.add_sub_assoc (by omega : 1 ≤ p) (p * (t - 1))
    rw [h1]
    ac_rfl
  rw [hpt]
  have hdig := Nat.digits_add p hp (p - 1) (t - 1) (by omega) (Or.inr (by omega : t - 1 ≠ 0))
  rw [hdig]
  simp
  have : 1 ≤ (p.digits (t - 1)).sum := by
    have hne : t - 1 ≠ 0 := by omega
    have hnil : p.digits (t - 1) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
    exact Nat.succ_le_of_lt (Nat.sum_pos_iff_exists_pos.mpr
      ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hne)⟩)
  omega
lemma val_fact_succ_le_count_mul_sub_one (p t : ℕ) [Fact p.Prime] (ht : 2 ≤ t) :
    padicValNat p (p * t - 1).factorial + 1 ≤ (p * t - 2) / (p - 1) := by
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt hp
  have hdigits : p ≤ (p.digits (p * t - 1)).sum := digit_sum_ge_p_mul_sub_one p t hp ht
  have hformula := sub_one_mul_padicValNat_factorial (p := p) (p * t - 1)
  have hmul : (p - 1) * padicValNat p (p * t - 1).factorial ≤ p * t - 1 - p := by
    omega
  have hptlep : p ≤ p * t - 1 := by
    have hp0 : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
    have hmulleft : p * 2 ≤ p * t := Nat.mul_le_mul_left p ht
    omega
  have hmul2 : (padicValNat p (p * t - 1).factorial + 1) * (p - 1) ≤ p * t - 2 := by
    calc
      (padicValNat p (p * t - 1).factorial + 1) * (p - 1)
          = (p - 1) * padicValNat p (p * t - 1).factorial + (p - 1) := by ring
      _ ≤ (p * t - 1 - p) + (p - 1) := Nat.add_le_add_right hmul (p - 1)
      _ ≤ p * t - 2 := by omega
  exact (Nat.le_div_iff_mul_le hp1pos).2 hmul2


lemma a_eq_num_div {m : ℕ} (hm : m ≠ 0) : a m = num m / m.factorial := by
  unfold a num
  simp [hm, Nat.pred_eq_sub_one]


lemma odd_prime_dvd_a_mul_sub_one (p t : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) (ht : 2 ≤ t) :
    p ∣ a (p * t - 1) := by
  let m := p * t - 1
  have hm : m ≠ 0 := by
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hmul : p * 2 ≤ p * t := Nat.mul_le_mul_left p ht
    omega
  have hfac : m.factorial ∣ num m := factorial_dvd_num hm
  have hstrict : padicValNat p m.factorial + 1 ≤ (m - 1) / (p - 1) := by
    dsimp [m]
    simpa using (val_fact_succ_le_count_mul_sub_one p t ht)
  have hpowdvd : p ^ ((m - 1) / (p - 1)) ∣ (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) :=
    pow_count_dvd_prod p m hpodd
  have hpowdvd' : p ^ (padicValNat p m.factorial + 1) ∣ (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) :=
    (pow_dvd_pow p hstrict).trans hpowdvd
  have hpowdvd_num : p ^ (padicValNat p m.factorial + 1) ∣ num m := by
    dsimp [num]
    exact hpowdvd'.trans (Nat.dvd_mul_left _ _)
  have hvalnum : padicValNat p m.factorial + 1 ≤ padicValNat p (num m) := by
    exact (padicValNat_dvd_iff_le (Nat.ne_of_gt (num_pos hm))).1 hpowdvd_num
  have hvalquot : 1 ≤ padicValNat p (num m / m.factorial) := by
    rw [padicValNat.div_of_dvd hfac]
    omega
  rw [a_eq_num_div hm]
  exact dvd_of_one_le_padicValNat hvalquot
lemma sum_digits_two_pow_sub_one : ∀ r : ℕ, (Nat.digits 2 (2 ^ r - 1)).sum = r
| 0 => by simp
| r+1 => by
    have hpow : 2 ^ (r + 1) - 1 = 1 + 2 * (2 ^ r - 1) := by
      rw [pow_succ']
      have hpos : 0 < 2 ^ r := pow_pos (by decide : 0 < (2:ℕ)) r
      omega
    rw [hpow]
    have hdig := Nat.digits_add 2 (by decide : 1 < (2:ℕ)) 1 (2 ^ r - 1) (by decide : 1 < (2:ℕ)) (Or.inl one_ne_zero)
    rw [hdig]
    simp [sum_digits_two_pow_sub_one r]
    omega
lemma two_not_dvd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : ¬ 2 ∣ 2 ^ k - 1 := by
  intro h
  have h2pow : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
  have hone : 2 ∣ 1 := by
    have hpos : 0 < 2 ^ k := pow_pos (by decide : 0 < (2:ℕ)) _
    have hsub : 2 ^ k - (2 ^ k - 1) = 1 := by omega
    simpa [hsub] using Nat.dvd_sub h2pow h
  norm_num at hone

lemma padicValNat_two_prod_Ico_eq_zero (m : ℕ) :
    padicValNat 2 ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  apply Prime.not_dvd_finset_prod (show _root_.Prime (2:ℕ) from (Nat.prime_two : Nat.Prime 2).prime)
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact two_not_dvd_two_pow_sub_one (by omega)

lemma le_two_pow_sub_one_of_two_le (r : ℕ) (hr : 2 ≤ r) : r ≤ 2 ^ r - 1 := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hpowpos : 0 < 2 ^ r := pow_pos (by decide : 0 < (2:ℕ)) _
      have hle1 : r + 1 ≤ 2 ^ r := by
        exact Nat.succ_le_iff.mpr (lt_of_le_of_lt ih (Nat.sub_one_lt hpowpos.ne'))
      rw [_root_.pow_succ']
      omega

lemma padicVal_a_two_pow_sub_one (r : ℕ) (hr : 2 ≤ r) :
    padicValNat 2 (a (2 ^ r - 1)) = r - 1 := by
  let m := 2 ^ r - 1
  have hm : m ≠ 0 := by
    dsimp [m]
    have hpow : 1 < 2 ^ r := one_lt_pow₀ (by norm_num : 1 < (2:ℕ)) (by omega : r ≠ 0)
    omega
  have hfac : m.factorial ∣ num m := factorial_dvd_num hm
  have hvalprod : padicValNat 2 ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) = 0 :=
    padicValNat_two_prod_Ico_eq_zero m
  have hvalnum : padicValNat 2 (num m) = m - 1 := by
    dsimp [num]
    rw [padicValNat.mul (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)) (Nat.ne_of_gt (prod_Ico_two_pos m)), padicValNat.prime_pow, hvalprod, add_zero]
  have hvalfac : padicValNat 2 m.factorial = m - r := by
    have hf := sub_one_mul_padicValNat_factorial (p := 2) m
    have hsum : (Nat.digits 2 m).sum = r := by
      dsimp [m]
      exact sum_digits_two_pow_sub_one r
    simpa [hsum] using hf
  change padicValNat 2 (a m) = r - 1
  rw [a_eq_num_div hm, padicValNat.div_of_dvd hfac, hvalnum, hvalfac]
  dsimp [m]
  have hpowge : r ≤ 2 ^ r - 1 := le_two_pow_sub_one_of_two_le r hr
  have hpowge' : r + 1 ≤ 2 ^ r := by omega
  omega

lemma prime_dvd_factor_of_zmod_pow_eq_one {p d : ℕ} (hp : p.Prime) (hdpos : 0 < d)
    (hpow : (2 : ZMod p) ^ d = 1) : p ∣ 2 ^ d - 1 := by
  have hcast : ((2 ^ d : ℕ) : ZMod p) = (1 : ℕ) := by
    norm_cast at hpow ⊢
  have hmod : 2 ^ d ≡ 1 [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff (2 ^ d) 1 p).mp hcast
  have hone : 1 ≤ 2 ^ d := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2:ℕ)) _)
  exact (Nat.modEq_iff_dvd' hone).mp hmod.symm

lemma prime_not_primitive_dvd_a_pred (p : ℕ) (hp : p.Prime) (hpgt : 2 < p)
    (hnprim : ¬ IsPrimitiveRoot (2 : ZMod p) (Nat.totient p)) :
    p ∣ a (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpm1ne : p - 1 ≠ 0 := by omega
  have hfac : (p - 1).factorial ∣ num (p - 1) := factorial_dvd_num hpm1ne
  have hcopfac : p.Coprime (p - 1).factorial := hp.coprime_factorial_of_lt (by omega)
  have htot : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hnotord : orderOf (2 : ZMod p) ≠ p - 1 := by
    intro hord
    apply hnprim
    rw [htot]
    exact IsPrimitiveRoot.iff_orderOf.mpr hord
  let d := orderOf (2 : ZMod p)
  have hddvd : d ∣ p - 1 := by
    have hunit : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hzmod : (2:ℕ) ≡ 0 [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        simpa using hz
      have hpdiv2 : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp hzmod
      have : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2:ℕ)) hpdiv2
      omega
    exact ZMod.orderOf_dvd_card_sub_one hunit
  have hdpos : 0 < d := by
    by_contra hdz
    have hdz' : d = 0 := by omega
    rw [hdz'] at hddvd
    rcases hddvd with ⟨w, hw⟩
    have : p - 1 = 0 := by simpa using hw
    omega
  have hdlt : d < p - 1 := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hddvd) hnotord
  have hdmem : d ∈ Finset.Ico 1 (p - 1) := by
    rw [Finset.mem_Ico]
    exact ⟨hdpos, hdlt⟩
  have hpdvd_factor : p ∣ 2 ^ d - 1 := prime_dvd_factor_of_zmod_pow_eq_one hp hdpos (pow_orderOf_eq_one (2 : ZMod p))
  have hpdvd_prod : p ∣ (Finset.Ico 1 (p - 1)).prod (fun k => 2 ^ k - 1) :=
    hpdvd_factor.trans (Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) hdmem)
  have hpdvd_num : p ∣ num (p - 1) := by
    dsimp [num]
    exact hpdvd_prod.trans (Nat.dvd_mul_left _ _)
  rw [a_eq_num_div hpm1ne]
  rcases hfac with ⟨q, hq⟩
  have hpdvd_mul : p ∣ (p - 1)! * q := by simpa [hq] using hpdvd_num
  rw [hq, Nat.mul_div_right _ (Nat.factorial_pos _)]
  exact (hcopfac.dvd_mul_left).mp hpdvd_mul

lemma add_two_le_two_pow (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [_root_.pow_succ']
      have hpos : 0 < 2 ^ k := pow_pos (by decide : 0 < (2:ℕ)) _
      nlinarith

lemma pow_two_case_contra {k : ℕ} (hk : 2 ≤ k)
    (hdiv : 2 ^ k ∣ a (2 ^ k - 1) + 2 ^ (2 ^ k - 2)) : False := by
  have hmval := padicVal_a_two_pow_sub_one k hk
  have hexp : k ≤ 2 ^ k - 2 := by
    have := add_two_le_two_pow k hk
    omega
  have hsecond : 2 ^ k ∣ 2 ^ (2 ^ k - 2) := by
    exact pow_dvd_pow 2 hexp
  have ha_dvd : 2 ^ k ∣ a (2 ^ k - 1) := by
    have hsub := Nat.dvd_sub hdiv hsecond
    -- (a+pow)-pow = a
    have hle : 2 ^ (2 ^ k - 2) ≤ a (2 ^ k - 1) + 2 ^ (2 ^ k - 2) := Nat.le_add_left _ _
    simpa [Nat.add_sub_cancel_left] using hsub
  have hk_le_val : k ≤ padicValNat 2 (a (2 ^ k - 1)) := by
    exact (padicValNat_dvd_iff_le (by
      intro ha0
      rw [ha0] at hmval
      simp at hmval
      omega)).1 ha_dvd
  rw [hmval] at hk_le_val
  omega

lemma odd_prime_divisor_case_contra {n p : ℕ} (hn : 2 < n) (hp : p.Prime) (hpn : p ∣ n) (hpodd : Odd p)
    (hnprime : ¬ n.Prime) (hdiv : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  rcases hpn with ⟨t, rfl⟩
  have hpne2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have ht : 2 ≤ t := by
    by_contra ht2
    have htle1 : t ≤ 1 := by omega
    interval_cases t
    · simp at hn
    · exact hnprime (by simpa using hp)
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvd_a : p ∣ a (p * t - 1) := odd_prime_dvd_a_mul_sub_one p t hpne2 ht
  have hp_dvd_sum : p ∣ a (p * t - 1) + 2 ^ (p * t - 2) := by
    exact (dvd_mul_right p t).trans hdiv
  have hp_dvd_pow : p ∣ 2 ^ (p * t - 2) := by
    have hsub := Nat.dvd_sub hp_dvd_sum hp_dvd_a
    have hle : a (p * t - 1) ≤ a (p * t - 1) + 2 ^ (p * t - 2) := Nat.le_add_right _ _
    simpa [Nat.add_sub_cancel_left] using hsub
  have hcop : p.Coprime (2 ^ (p * t - 2)) := by
    have hpnot2 : ¬ p ∣ 2 := by
      intro hp2
      have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2:ℕ)) hp2
      exact hpne2 (le_antisymm hp_le2 hp.two_le)
    exact (hp.coprime_iff_not_dvd.mpr hpnot2).pow_right _
  exact hp.ne_one (hcop.eq_one_of_dvd hp_dvd_pow)

theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdiv
  have hnprime : Nat.Prime n := by
    by_contra hnp
    obtain ⟨k, hkpow⟩ | ⟨p, hp, hpn, hpodd⟩ := Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
    · subst n
      have hk : 2 ≤ k := by
        by_contra hknot
        have hk1 : k ≤ 1 := by omega
        interval_cases k <;> norm_num at hn
      exact (pow_two_case_contra hk hdiv).elim
    · exact (odd_prime_divisor_case_contra hn hp hpn hpodd hnp hdiv).elim
  refine ⟨hnprime, ?_⟩
  by_contra hnprim
  have hn_dvd_a : n ∣ a (n - 1) := prime_not_primitive_dvd_a_pred n hnprime hn hnprim
  have hn_dvd_pow : n ∣ 2 ^ (n - 2) := by
    have hsub := Nat.dvd_sub hdiv hn_dvd_a
    simpa [Nat.add_sub_cancel_left] using hsub
  have hnne2 : n ≠ 2 := by omega
  have hcop : n.Coprime (2 ^ (n - 2)) := by
    have hnnot2 : ¬ n ∣ 2 := by
      intro hn2
      have hnle2 : n ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2:ℕ)) hn2
      omega
    exact (hnprime.coprime_iff_not_dvd.mpr hnnot2).pow_right _
  exact hnprime.ne_one (hcop.eq_one_of_dvd hn_dvd_pow)
