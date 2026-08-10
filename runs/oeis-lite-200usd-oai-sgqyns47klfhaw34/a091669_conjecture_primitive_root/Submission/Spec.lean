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


lemma fac_q_mul_le_pow_sub_one {q t j : ℕ} (hq : Nat.Prime q) (hqodd : Odd q)
    (htpos : 0 < t) (hjpos : 0 < j) (htdvd : q ∣ 2 ^ t - 1) :
    (q * j).factorization q ≤ (2 ^ (t * j) - 1).factorization q := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hqne0 : q ≠ 0 := hq.ne_zero
  have hjne0 : j ≠ 0 := Nat.ne_of_gt hjpos
  have hqj_ne0 : q * j ≠ 0 := mul_ne_zero hqne0 hjne0
  have hterm_pos : 0 < 2 ^ (t * j) - 1 := by
    have : 1 < 2 ^ (t * j) := by
      have htj : 0 < t * j := mul_pos htpos hjpos
      exact one_lt_pow₀ (by decide : 1 < 2) htj.ne'
    omega
  have hterm_ne0 : 2 ^ (t * j) - 1 ≠ 0 := Nat.ne_of_gt hterm_pos
  have hnotdvd2t : ¬ q ∣ 2 ^ t := by
    intro h
    have h2 : q ∣ 2 := hq.dvd_of_dvd_pow h
    have hqgt2 : 2 < q := by
      have hq2le : 2 ≤ q := hq.two_le
      have hqne2 : q ≠ 2 := by
        intro hqeq
        subst hqeq
        rcases hqodd with ⟨k, hk⟩
        omega
      omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hqgt2) h2
  have hLTE := Nat.emultiplicity_pow_sub_pow hq hqodd (x := 2 ^ t) (y := 1) htdvd hnotdvd2t j
  have hpoweq : (2 ^ t) ^ j - 1 ^ j = 2 ^ (t * j) - 1 := by
    rw [pow_mul, one_pow]
  have hbase_ge1 : ((1 : ℕ) : ℕ∞) ≤ emultiplicity q (2 ^ t - 1) := by
    exact (pow_dvd_iff_le_emultiplicity.mp (by simpa using htdvd) : ((1 : ℕ) : ℕ∞) ≤ emultiplicity q (2 ^ t - 1))
  have hleft : ((q * j).factorization q : ℕ∞) = (1 : ℕ∞) + emultiplicity q j := by
    calc
      ((q * j).factorization q : ℕ∞) = emultiplicity q (q * j) := by
        rw [Nat.factorization_def _ hq]
        exact padicValNat_eq_emultiplicity hqj_ne0
      _ = emultiplicity q q + emultiplicity q j := hq.emultiplicity_mul
      _ = (1 : ℕ∞) + emultiplicity q j := by rw [hq.emultiplicity_self]
  have hmid : ((q * j).factorization q : ℕ∞) ≤ emultiplicity q (2 ^ (t * j) - 1) := by
    rw [hleft]
    calc
      (1 : ℕ∞) + emultiplicity q j ≤ emultiplicity q (2 ^ t - 1) + emultiplicity q j := add_le_add hbase_ge1 le_rfl
      _ = emultiplicity q ((2 ^ t) ^ j - 1 ^ j) := hLTE.symm
      _ = emultiplicity q (2 ^ (t * j) - 1) := by rw [hpoweq]
  have hright : emultiplicity q (2 ^ (t * j) - 1) = ((2 ^ (t * j) - 1).factorization q : ℕ∞) := by
    rw [Nat.factorization_def _ hq]
    exact (padicValNat_eq_emultiplicity hterm_ne0).symm
  have hENat : ((q * j).factorization q : ℕ∞) ≤ ((2 ^ (t * j) - 1).factorization q : ℕ∞) := by
    rwa [← hright]
  exact WithTop.coe_le_coe.mp hENat

lemma order_two_mod_prime_pos {q : ℕ} (hq : Nat.Prime q) (hqodd : Odd q) :
    0 < orderOf (2 : ZMod q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hqgt2 : 2 < q := by
    have hq2le : 2 ≤ q := hq.two_le
    have hqne2 : q ≠ 2 := by
      intro hqeq; subst hqeq; rcases hqodd with ⟨k,hk⟩; omega
    omega
  have h2nz : (2 : ZMod q) ≠ 0 := by
    intro h
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hqgt2) hd
  have hfin : IsOfFinOrder (2 : ZMod q) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨q - 1, by omega, ZMod.pow_card_sub_one_eq_one h2nz⟩
  exact hfin.orderOf_pos

lemma order_two_mod_prime_le_sub_one {q : ℕ} (hq : Nat.Prime q) (hqodd : Odd q) :
    orderOf (2 : ZMod q) ≤ q - 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hqgt2 : 2 < q := by
    have hq2le : 2 ≤ q := hq.two_le
    have hqne2 : q ≠ 2 := by
      intro hqeq; subst hqeq; rcases hqodd with ⟨k,hk⟩; omega
    omega
  have h2nz : (2 : ZMod q) ≠ 0 := by
    intro h
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hqgt2) hd
  have hdvd : orderOf (2 : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one h2nz
  exact Nat.le_of_dvd (by omega) hdvd

lemma prime_dvd_pow_order_sub_one {q : ℕ} (hq : Nat.Prime q) (hqodd : Odd q) :
    q ∣ 2 ^ orderOf (2 : ZMod q) - 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hcast : ((2 ^ orderOf (2 : ZMod q) - 1 : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_sub]
    · rw [Nat.cast_pow]
      rw [show ((2 : ℕ) : ZMod q) = (2 : ZMod q) by norm_num,
        show ((1 : ℕ) : ZMod q) = (1 : ZMod q) by norm_num]
      rw [pow_orderOf_eq_one, sub_self]
    · exact Nat.succ_le_iff.mpr (pow_pos (by decide : 0 < 2) _)
  exact (ZMod.natCast_eq_zero_iff _ _).1 hcast

lemma odd_prime_factorial_le_prod_factorization {m q : ℕ} (hm : 0 < m)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    (m.factorial).factorization q ≤
      ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)).factorization q := by
  let t := orderOf (2 : ZMod q)
  have htpos : 0 < t := by
    dsimp [t]
    exact order_two_mod_prime_pos hq hqodd
  have ht_le : t ≤ q - 1 := by
    dsimp [t]
    exact order_two_mod_prime_le_sub_one hq hqodd
  have htdvd : q ∣ 2 ^ t - 1 := by
    dsimp [t]
    exact prime_dvd_pow_order_sub_one hq hqodd
  let S := (Finset.Ico 1 (m+1)).filter (fun i => q ∣ i)
  let f : ℕ → ℕ := fun i => t * (i / q)
  have hfac_sum : (m.factorial).factorization q = ∑ i ∈ Finset.Ico 1 (m+1), i.factorization q := by
    rw [← Finset.prod_Ico_id_eq_factorial m]
    rw [Nat.factorization_prod]
    · simp
    · intro x hx
      rw [Finset.mem_Ico] at hx
      omega
  have hfac_filter : (m.factorial).factorization q = ∑ i ∈ S, i.factorization q := by
    rw [hfac_sum]
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hqi : q ∣ i
    · simp [hqi]
    · have : i.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqi
      simp [hqi, this]
  have hprod_sum : ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)).factorization q =
      ∑ k ∈ Finset.Ico 1 m, (2 ^ k - 1).factorization q := by
    rw [Nat.factorization_prod]
    · simp
    · intro k hk
      rw [Finset.mem_Ico] at hk
      have hpos : 0 < 2 ^ k - 1 := by
        have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
        omega
      exact Nat.ne_of_gt hpos
  have himage_sub : Finset.image f S ⊆ Finset.Ico 1 m := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hiS, rfl⟩
    dsimp [S] at hiS
    rw [Finset.mem_filter, Finset.mem_Ico] at hiS
    rcases hiS with ⟨⟨hi1, him1⟩, hqi⟩
    have hqpos : 0 < q := hq.pos
    have hqle_i : q ≤ i := Nat.le_of_dvd hi1 hqi
    have hjpos : 0 < i / q := Nat.div_pos hqle_i hqpos
    have hle1 : t * (i / q) ≤ (q - 1) * (i / q) := Nat.mul_le_mul_right _ ht_le
    have hqmul : q * (i / q) = i := by
      rw [mul_comm]
      exact Nat.div_mul_cancel hqi
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.succ_le_iff.mpr (mul_pos htpos hjpos)
    · have hlt_i : t * (i / q) < i := by
        calc
          t * (i / q) ≤ (q - 1) * (i / q) := hle1
          _ < q * (i / q) := by
            have : q - 1 < q := by omega
            exact Nat.mul_lt_mul_of_pos_right this hjpos
          _ = i := hqmul
      exact lt_of_lt_of_le hlt_i (Nat.le_of_lt_succ him1)
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro a ha b hb hfab
    dsimp [f] at hfab
    have hdiv_eq : a / q = b / q := Nat.eq_of_mul_eq_mul_left htpos hfab
    have ha' : a ∈ S := by simpa using ha
    have hb' : b ∈ S := by simpa using hb
    dsimp [S] at ha' hb'
    rw [Finset.mem_filter, Finset.mem_Ico] at ha' hb'
    rcases ha' with ⟨⟨ha1, _⟩, hqa⟩
    rcases hb' with ⟨⟨hb1, _⟩, hqb⟩
    have haeq : q * (a / q) = a := by rw [mul_comm]; exact Nat.div_mul_cancel hqa
    have hbeq : q * (b / q) = b := by rw [mul_comm]; exact Nat.div_mul_cancel hqb
    calc
      a = q * (a / q) := haeq.symm
      _ = q * (b / q) := by rw [hdiv_eq]
      _ = b := hbeq
  have hselected_le : ∑ i ∈ S, i.factorization q ≤ ∑ i ∈ S, (2 ^ (f i) - 1).factorization q := by
    apply Finset.sum_le_sum
    intro i hiS
    dsimp [S] at hiS
    rw [Finset.mem_filter, Finset.mem_Ico] at hiS
    rcases hiS with ⟨⟨hi1, him1⟩, hqi⟩
    have hqle_i : q ≤ i := Nat.le_of_dvd hi1 hqi
    have hjpos : 0 < i / q := Nat.div_pos hqle_i hq.pos
    have hqmul : q * (i / q) = i := by rw [mul_comm]; exact Nat.div_mul_cancel hqi
    rw [← hqmul]
    dsimp [f]
    rw [show q * (i / q) / q = i / q by exact Nat.mul_div_right (i / q) hq.pos]
    exact fac_q_mul_le_pow_sub_one hq hqodd htpos hjpos htdvd
  have himage_sum : ∑ k ∈ Finset.image f S, (2 ^ k - 1).factorization q =
      ∑ i ∈ S, (2 ^ (f i) - 1).factorization q := by
    exact Finset.sum_image hinj
  have h1 : (m.factorial).factorization q ≤ ∑ i ∈ S, (2 ^ (f i) - 1).factorization q := by
    rw [hfac_filter]
    exact hselected_le
  have h2 : (m.factorial).factorization q ≤ ∑ k ∈ Finset.image f S, (2 ^ k - 1).factorization q := by
    exact h1.trans (le_of_eq himage_sum.symm)
  have h3 : (m.factorial).factorization q ≤ ∑ k ∈ Finset.Ico 1 m, (2 ^ k - 1).factorization q := by
    exact h2.trans (Finset.sum_le_sum_of_subset himage_sub)
  exact h3.trans (le_of_eq hprod_sum.symm)

lemma factorial_dvd_a_num {m : ℕ} (hm : 0 < m) :
    m.factorial ∣ (2 ^ (m - 1)) * (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) := by
  let prodPart := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
  let num := (2 ^ (m - 1)) * prodPart
  have hden_ne0 : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hnum_ne0 : num ≠ 0 := by
    dsimp [num, prodPart]
    apply mul_ne_zero
    · exact pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hpos : 0 < 2 ^ k - 1 := by
        have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
        omega
      exact Nat.ne_of_gt hpos
  rw [← Nat.factorization_le_iff_dvd hden_ne0 hnum_ne0]
  rw [Finsupp.le_iff]
  intro q hqmem
  have hqprime : Nat.Prime q := by
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hqmem
    exact hqmem.1
  have hnum_fact : num.factorization q = (2 ^ (m - 1)).factorization q + prodPart.factorization q := by
    dsimp [num]
    rw [Nat.factorization_mul]
    · rfl
    · exact pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
    · dsimp [prodPart] at hnum_ne0
      exact right_ne_zero_of_mul hnum_ne0
  by_cases hq2 : q = 2
  · subst hq2
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    have hden_lt : m.factorial.factorization 2 < m := by
      rw [Nat.factorization_def _ (by norm_num : Nat.Prime 2)]
      exact padicValNat_factorial_lt_of_ne_zero 2 (Nat.ne_of_gt hm)
    have hden_le : m.factorial.factorization 2 ≤ m - 1 := by omega
    have hpow_fact : (2 ^ (m - 1)).factorization 2 = m - 1 := by
      rw [Nat.factorization_pow]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2)]
    rw [hnum_fact, hpow_fact]
    omega
  · have hqodd : Odd q := hqprime.odd_of_ne_two hq2
    have hprod_ge := odd_prime_factorial_le_prod_factorization hm hqprime hqodd
    rw [hnum_fact]
    exact le_trans hprod_ge (Nat.le_add_left _ _)

lemma odd_prime_factorial_add_one_le_prod_factorization {n p : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p) (hpdvd : p ∣ n) (hplt : p < n) :
    ((n - 1).factorial).factorization p + 1 ≤
      ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)).factorization p := by
  let m := n - 1
  have hnpos : 0 < n := lt_trans hp.pos hplt
  have hmpos : 0 < m := by
    have hp2 : 2 ≤ p := hp.two_le
    dsimp [m]
    omega
  let t := orderOf (2 : ZMod p)
  have htpos : 0 < t := by dsimp [t]; exact order_two_mod_prime_pos hp hpodd
  have ht_le : t ≤ p - 1 := by dsimp [t]; exact order_two_mod_prime_le_sub_one hp hpodd
  have htdvd : p ∣ 2 ^ t - 1 := by dsimp [t]; exact prime_dvd_pow_order_sub_one hp hpodd
  let S := (Finset.Ico 1 (m+1)).filter (fun i => p ∣ i)
  let f : ℕ → ℕ := fun i => t * (i / p)
  let j0 := n / p
  let k0 := t * j0
  have hp_le_n : p ≤ n := le_of_lt hplt
  have hj0pos : 0 < j0 := by dsimp [j0]; exact Nat.div_pos hp_le_n hp.pos
  have hpn : p * j0 = n := by dsimp [j0]; rw [mul_comm]; exact Nat.div_mul_cancel hpdvd
  have hj0_ge2 : 2 ≤ j0 := by
    by_contra h
    have hjle1 : j0 ≤ 1 := by omega
    have : n ≤ p := by
      calc n = p * j0 := hpn.symm
        _ ≤ p * 1 := Nat.mul_le_mul_left p hjle1
        _ = p := by simp
    omega
  have hk0_mem : k0 ∈ Finset.Ico 1 m := by
    dsimp [k0, m]
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.succ_le_iff.mpr (mul_pos htpos hj0pos)
    · have hle : t * j0 ≤ (p - 1) * j0 := Nat.mul_le_mul_right _ ht_le
      have hlt : t * j0 < n - 1 := by
        calc
          t * j0 ≤ (p - 1) * j0 := hle
          _ = p * j0 - j0 := by
            rw [Nat.sub_mul]
            simp
          _ = n - j0 := by rw [hpn]
          _ ≤ n - 2 := Nat.sub_le_sub_left hj0_ge2 n
          _ < n - 1 := by omega
      exact hlt
  have hfac_filter : ((n - 1).factorial).factorization p = ∑ i ∈ S, i.factorization p := by
    have hfac_sum : ((n - 1).factorial).factorization p = ∑ i ∈ Finset.Ico 1 ((n - 1)+1), i.factorization p := by
      rw [← Finset.prod_Ico_id_eq_factorial (n - 1)]
      rw [Nat.factorization_prod]
      · simp
      · intro x hx
        rw [Finset.mem_Ico] at hx
        omega
    rw [hfac_sum]
    dsimp [S, m]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpi : p ∣ i
    · simp [hpi]
    · have : i.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpi
      simp [hpi, this]
  have hprod_sum : ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)).factorization p =
      ∑ k ∈ Finset.Ico 1 m, (2 ^ k - 1).factorization p := by
    rw [Nat.factorization_prod]
    · simp
    · intro k hk
      rw [Finset.mem_Ico] at hk
      have hpos : 0 < 2 ^ k - 1 := by
        have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
        omega
      exact Nat.ne_of_gt hpos
  have himage_sub : Finset.image f S ⊆ Finset.Ico 1 m := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hiS, rfl⟩
    dsimp [S] at hiS
    rw [Finset.mem_filter, Finset.mem_Ico] at hiS
    rcases hiS with ⟨⟨hi1, him1⟩, hpi⟩
    have hple_i : p ≤ i := Nat.le_of_dvd hi1 hpi
    have hjpos : 0 < i / p := Nat.div_pos hple_i hp.pos
    have hle1 : t * (i / p) ≤ (p - 1) * (i / p) := Nat.mul_le_mul_right _ ht_le
    have hpmul : p * (i / p) = i := by rw [mul_comm]; exact Nat.div_mul_cancel hpi
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.succ_le_iff.mpr (mul_pos htpos hjpos)
    · have hlt_i : t * (i / p) < i := by
        calc
          t * (i / p) ≤ (p - 1) * (i / p) := hle1
          _ < p * (i / p) := by
            have : p - 1 < p := by omega
            exact Nat.mul_lt_mul_of_pos_right this hjpos
          _ = i := hpmul
      exact lt_of_lt_of_le hlt_i (Nat.le_of_lt_succ him1)
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro a ha b hb hfab
    dsimp [f] at hfab
    have hdiv_eq : a / p = b / p := Nat.eq_of_mul_eq_mul_left htpos hfab
    have ha' : a ∈ S := by simpa using ha
    have hb' : b ∈ S := by simpa using hb
    dsimp [S] at ha' hb'
    rw [Finset.mem_filter, Finset.mem_Ico] at ha' hb'
    rcases ha' with ⟨⟨ha1, _⟩, hpa⟩
    rcases hb' with ⟨⟨hb1, _⟩, hpb⟩
    have haeq : p * (a / p) = a := by rw [mul_comm]; exact Nat.div_mul_cancel hpa
    have hbeq : p * (b / p) = b := by rw [mul_comm]; exact Nat.div_mul_cancel hpb
    calc
      a = p * (a / p) := haeq.symm
      _ = p * (b / p) := by rw [hdiv_eq]
      _ = b := hbeq
  have hselected_le : ∑ i ∈ S, i.factorization p ≤ ∑ i ∈ S, (2 ^ (f i) - 1).factorization p := by
    apply Finset.sum_le_sum
    intro i hiS
    dsimp [S] at hiS
    rw [Finset.mem_filter, Finset.mem_Ico] at hiS
    rcases hiS with ⟨⟨hi1, him1⟩, hpi⟩
    have hple_i : p ≤ i := Nat.le_of_dvd hi1 hpi
    have hjpos : 0 < i / p := Nat.div_pos hple_i hp.pos
    have hpmul : p * (i / p) = i := by rw [mul_comm]; exact Nat.div_mul_cancel hpi
    rw [← hpmul]
    dsimp [f]
    rw [show p * (i / p) / p = i / p by exact Nat.mul_div_right (i / p) hp.pos]
    exact fac_q_mul_le_pow_sub_one hp hpodd htpos hjpos htdvd
  have himage_sum : ∑ k ∈ Finset.image f S, (2 ^ k - 1).factorization p =
      ∑ i ∈ S, (2 ^ (f i) - 1).factorization p := by
    exact Finset.sum_image hinj
  have hk0_not_image : k0 ∉ Finset.image f S := by
    intro hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hiS, hfi⟩
    dsimp [k0, f] at hfi
    have hdiv_eq : i / p = j0 := Nat.eq_of_mul_eq_mul_left htpos hfi
    dsimp [S] at hiS
    rw [Finset.mem_filter, Finset.mem_Ico] at hiS
    rcases hiS with ⟨⟨hi1, him1⟩, hpi⟩
    have hieq : p * (i / p) = i := by rw [mul_comm]; exact Nat.div_mul_cancel hpi
    have : i = n := by
      calc
        i = p * (i / p) := hieq.symm
        _ = p * j0 := by rw [hdiv_eq]
        _ = n := hpn
    have : n < n := by omega
    exact (lt_irrefl n) this
  have hterm_extra : 1 ≤ (2 ^ k0 - 1).factorization p := by
    have hle := fac_q_mul_le_pow_sub_one hp hpodd htpos hj0pos htdvd
    -- hle : (p*j0).factorization p ≤ term
    dsimp [k0]
    have hone_le_nfac : 1 ≤ (p * j0).factorization p := by
      rw [hpn]
      exact (hp.dvd_iff_one_le_factorization (Nat.ne_of_gt hnpos)).1 hpdvd
    exact le_trans hone_le_nfac hle
  have hden_to_image : ((n - 1).factorial).factorization p ≤ ∑ k ∈ Finset.image f S, (2 ^ k - 1).factorization p := by
    rw [hfac_filter]
    exact hselected_le.trans (le_of_eq himage_sum.symm)
  have hden_add_to_insert : ((n - 1).factorial).factorization p + 1 ≤
      ∑ k ∈ insert k0 (Finset.image f S), (2 ^ k - 1).factorization p := by
    rw [Finset.sum_insert hk0_not_image]
    simpa [add_comm] using (_root_.add_le_add hden_to_image hterm_extra)
  have hinsert_sub : insert k0 (Finset.image f S) ⊆ Finset.Ico 1 m := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hk0_mem
    · exact himage_sub hx
  have hto_sum : ((n - 1).factorial).factorization p + 1 ≤ ∑ k ∈ Finset.Ico 1 m, (2 ^ k - 1).factorization p :=
    hden_add_to_insert.trans (Finset.sum_le_sum_of_subset hinsert_sub)
  dsimp [m] at hprod_sum ⊢
  exact hto_sum.trans (le_of_eq hprod_sum.symm)

lemma odd_prime_dvd_a_pred_of_dvd {n p : ℕ} (hp : Nat.Prime p) (hpodd : Odd p)
    (hpdvd : p ∣ n) (hplt : p < n) : p ∣ a (n - 1) := by
  let m := n - 1
  let prodPart := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
  let num := 2 ^ (m - 1) * prodPart
  have hmpos : 0 < m := by
    have hp2 : 2 ≤ p := hp.two_le
    dsimp [m]
    omega
  have hden_dvd : m.factorial ∣ num := by
    dsimp [num, prodPart]
    exact factorial_dvd_a_num hmpos
  have hnum_ne0 : num ≠ 0 := by
    dsimp [num, prodPart]
    apply mul_ne_zero
    · exact pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hpos : 0 < 2 ^ k - 1 := by
        have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
        omega
      exact Nat.ne_of_gt hpos
  have hprod_extra : m.factorial.factorization p + 1 ≤ prodPart.factorization p := by
    dsimp [m, prodPart]
    exact odd_prime_factorial_add_one_le_prod_factorization hp hpodd hpdvd hplt
  have hnum_fact : num.factorization p = (2 ^ (m - 1)).factorization p + prodPart.factorization p := by
    dsimp [num]
    rw [Nat.factorization_mul]
    · rfl
    · exact pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
    · exact right_ne_zero_of_mul hnum_ne0
  have hextra_num : m.factorial.factorization p + 1 ≤ num.factorization p := by
    rw [hnum_fact]
    exact le_trans hprod_extra (Nat.le_add_left _ _)
  have hquot_fac : 1 ≤ (num / m.factorial).factorization p := by
    rw [Nat.factorization_div hden_dvd]
    rw [Finsupp.coe_tsub]
    exact Nat.le_sub_of_add_le (by simpa [add_comm] using hextra_num)
  have hquot_dvd : p ∣ num / m.factorial := by
    by_cases hq0 : num / m.factorial = 0
    · rw [hq0]
      exact dvd_zero p
    · exact (hp.dvd_iff_one_le_factorization hq0).2 hquot_fac
  have ha_eq : a (n - 1) = num / m.factorial := by
    dsimp [a, m, num, prodPart]
    have hn1_ne0 : n - 1 ≠ 0 := by omega
    rw [if_neg hn1_ne0]
  rwa [ha_eq]

lemma padicValNat_two_factorial_two_pow_sub_one (r : ℕ) :
    padicValNat 2 ((2 ^ r - 1).factorial) = 2 ^ r - 1 - r := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hpowpos : 0 < 2 ^ r := pow_pos (by decide : 0 < 2) r
      have h1lt2 : 1 < (2:ℕ) := by decide
      have hrewrite : 2 ^ (r+1) - 1 = 2 * (2 ^ r - 1) + 1 := by
        rw [pow_succ]
        omega
      rw [hrewrite]
      rw [padicValNat_factorial_mul_add (p:=2) (m := 2 ^ r - 1) (n := 1) (by norm_num)]
      rw [padicValNat_factorial_mul (p:=2) (n := 2 ^ r - 1)]
      rw [ih]
      have hrlt : r < 2 ^ r := Nat.lt_two_pow_self
      omega

lemma two_not_dvd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : ¬ 2 ∣ 2 ^ k - 1 := by
  cases k with
  | zero => omega
  | succ l =>
      intro h
      rcases h with ⟨c, hc⟩
      rw [pow_succ'] at hc
      have hpos : 0 < 2 ^ l * 2 := by positivity
      omega

lemma a_two_pow_pred_factorization_two {r : ℕ} (hr : 0 < r) :
    (a (2 ^ r - 1)).factorization 2 = r - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let m := 2 ^ r - 1
  let prodPart := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
  let num := 2 ^ (m - 1) * prodPart
  have hmpos : 0 < m := by
    dsimp [m]
    have : 1 < 2 ^ r := one_lt_pow₀ (by decide : 1 < 2) (Nat.ne_of_gt hr)
    omega
  have hden_dvd : m.factorial ∣ num := by
    dsimp [num, prodPart]
    exact factorial_dvd_a_num hmpos
  have hprod_ne0 : prodPart ≠ 0 := by
    dsimp [prodPart]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpos : 0 < 2 ^ k - 1 := by
      have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
      omega
    exact Nat.ne_of_gt hpos
  have hnum_ne0 : num ≠ 0 := by
    dsimp [num]
    exact mul_ne_zero (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)) hprod_ne0
  have hprod_fact2 : prodPart.factorization 2 = 0 := by
    dsimp [prodPart]
    rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro k hk
      apply Nat.factorization_eq_zero_of_not_dvd
      rw [Finset.mem_Ico] at hk
      exact two_not_dvd_two_pow_sub_one (by omega)
    · intro k hk
      rw [Finset.mem_Ico] at hk
      have hpos : 0 < 2 ^ k - 1 := by
        have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
        omega
      exact Nat.ne_of_gt hpos
  have hnum_fact2 : num.factorization 2 = m - 1 := by
    dsimp [num]
    rw [Nat.factorization_mul]
    · rw [Nat.factorization_pow]
      rw [Finsupp.add_apply, Finsupp.smul_apply, hprod_fact2]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2)]
    · exact pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
    · exact hprod_ne0
  have hden_fact2 : m.factorial.factorization 2 = m - r := by
    rw [Nat.factorization_def _ (by norm_num : Nat.Prime 2)]
    dsimp [m]
    rw [padicValNat_two_factorial_two_pow_sub_one r]
  have hquot_fact2 : (num / m.factorial).factorization 2 = r - 1 := by
    rw [Nat.factorization_div hden_dvd]
    rw [Finsupp.coe_tsub]
    change num.factorization 2 - m.factorial.factorization 2 = r - 1
    rw [hnum_fact2, hden_fact2]
    dsimp [m]
    have hrlt : r < 2 ^ r := Nat.lt_two_pow_self
    omega
  have ha_eq : a (2 ^ r - 1) = num / m.factorial := by
    dsimp [a, m, num, prodPart]
    have hmne : 2 ^ r - 1 ≠ 0 := by dsimp [m] at hmpos; omega
    rw [if_neg hmne]
  rw [ha_eq]
  exact hquot_fact2


lemma self_add_two_le_two_pow {r : ℕ} (hr : 2 ≤ r) : r + 2 ≤ 2 ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr2 : 2 ≤ r
      · have hih := ih hr2
        rw [pow_succ]
        omega
      · interval_cases r
        · omega
        · norm_num

lemma not_dvd_a_sum_two_pow {r : ℕ} (hr : 2 ≤ r) :
    ¬ (2 ^ r ∣ a (2 ^ r - 1) + 2 ^ (2 ^ r - 2)) := by
  intro hsum
  have hpowterm : 2 ^ r ∣ 2 ^ (2 ^ r - 2) := by
    exact pow_dvd_pow 2 (by have h := self_add_two_le_two_pow hr; omega)
  have ha_dvd : 2 ^ r ∣ a (2 ^ r - 1) := (Nat.dvd_add_left hpowterm).1 hsum
  have hfac_a : (a (2 ^ r - 1)).factorization 2 = r - 1 := a_two_pow_pred_factorization_two (by omega)
  have ha_ne0 : a (2 ^ r - 1) ≠ 0 := by
    intro h0
    rw [h0] at hfac_a
    simp at hfac_a
    omega
  have hpow_ne0 : 2 ^ r ≠ 0 := pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
  have hlefac : (2 ^ r).factorization ≤ (a (2 ^ r - 1)).factorization :=
    (Nat.factorization_le_iff_dvd hpow_ne0 ha_ne0).2 ha_dvd
  have hpowfac2 : (2 ^ r).factorization 2 = r := by
    rw [Nat.factorization_pow]
    rw [Finsupp.smul_apply]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2)]
  have : r ≤ r - 1 := by
    have h := hlefac 2
    rw [hpowfac2, hfac_a] at h
    exact h
  omega

lemma prime_dvd_a_pred_of_not_primitive {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (hnot : ¬ IsPrimitiveRoot (2 : ZMod p) (Nat.totient p)) : p ∣ a (p - 1) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hphi : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hnot' : ¬ IsPrimitiveRoot (2 : ZMod p) (p - 1) := by simpa [hphi] using hnot
  have hordne : orderOf (2 : ZMod p) ≠ p - 1 := (IsPrimitiveRoot.not_iff).1 hnot'
  have h2nz : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2) hd
  have horddvd : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2nz
  have hordlt : orderOf (2 : ZMod p) < p - 1 := by
    exact Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega : 0 < p - 1) horddvd) hordne
  have hfin : IsOfFinOrder (2 : ZMod p) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h2nz⟩
  have hordpos : 0 < orderOf (2 : ZMod p) := hfin.orderOf_pos
  let m := p - 1
  let prodPart := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
  let num := 2 ^ (m - 1) * prodPart
  have hmpos : 0 < m := by dsimp [m]; omega
  have hden_dvd : m.factorial ∣ num := by
    dsimp [num, prodPart]
    exact factorial_dvd_a_num hmpos
  have hprod_ne0 : prodPart ≠ 0 := by
    dsimp [prodPart]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpos : 0 < 2 ^ k - 1 := by
      have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
      omega
    exact Nat.ne_of_gt hpos
  have hnum_ne0 : num ≠ 0 := by
    dsimp [num]
    exact mul_ne_zero (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)) hprod_ne0
  have hden_fact0 : m.factorial.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    rw [hp.dvd_factorial]
    dsimp [m]
    omega
  have hterm_ge : 1 ≤ prodPart.factorization p := by
    dsimp [prodPart]
    have hprod_sum : ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)).factorization p =
        ∑ k ∈ Finset.Ico 1 m, (2 ^ k - 1).factorization p := by
      rw [Nat.factorization_prod]
      · simp
      · intro k hk
        rw [Finset.mem_Ico] at hk
        have hpos : 0 < 2 ^ k - 1 := by
          have : 1 < 2 ^ k := one_lt_pow₀ (by decide : 1 < 2) (by omega)
          omega
        exact Nat.ne_of_gt hpos
    rw [hprod_sum]
    have hmem : orderOf (2 : ZMod p) ∈ Finset.Ico 1 m := by
      dsimp [m]
      rw [Finset.mem_Ico]
      omega
    have hfacpos : 1 ≤ (2 ^ orderOf (2 : ZMod p) - 1).factorization p := by
      apply (hp.dvd_iff_one_le_factorization ?_).1
      · exact prime_dvd_pow_order_sub_one hp hpodd
      · have : 0 < 2 ^ orderOf (2 : ZMod p) - 1 := by
          have : 1 < 2 ^ orderOf (2 : ZMod p) := one_lt_pow₀ (by decide : 1 < 2) (Nat.ne_of_gt hordpos)
          omega
        exact Nat.ne_of_gt this
    exact le_trans hfacpos (Finset.single_le_sum (s := Finset.Ico 1 m)
      (f := fun k => (2 ^ k - 1).factorization p) (fun _ _ => Nat.zero_le _) hmem)
  have hnum_fact_ge : 1 ≤ num.factorization p := by
    have hnum_fact : num.factorization p = (2 ^ (m - 1)).factorization p + prodPart.factorization p := by
      dsimp [num]
      rw [Nat.factorization_mul]
      · rfl
      · exact pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)
      · exact hprod_ne0
    rw [hnum_fact]
    exact le_trans hterm_ge (Nat.le_add_left _ _)
  have hquot_fac : 1 ≤ (num / m.factorial).factorization p := by
    rw [Nat.factorization_div hden_dvd]
    rw [Finsupp.coe_tsub]
    change num.factorization p - m.factorial.factorization p ≥ 1
    rw [hden_fact0]
    simpa using hnum_fact_ge
  have hquot_dvd : p ∣ num / m.factorial := by
    by_cases hq0 : num / m.factorial = 0
    · rw [hq0]; exact dvd_zero p
    · exact (hp.dvd_iff_one_le_factorization hq0).2 hquot_fac
  have ha_eq : a (p - 1) = num / m.factorial := by
    dsimp [a, m, num, prodPart]
    have hmne : p - 1 ≠ 0 := by omega
    rw [if_neg hmne]
  rwa [ha_eq]


-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdiv
  have prime_part : Nat.Prime n := by
    by_contra hnprime
    have hn_ne1 : n ≠ 1 := by omega
    rcases Nat.exists_prime_and_dvd hn_ne1 with ⟨p, hp, hpn⟩
    have hp_lt_n : p < n := by
      have hple : p ≤ n := Nat.le_of_dvd (by omega : 0 < n) hpn
      have hpne : p ≠ n := by
        intro hpeq
        subst hpeq
        exact hnprime hp
      omega
    by_cases hexodd : ∃ q, Nat.Prime q ∧ q ∣ n ∧ q ≠ 2
    · rcases hexodd with ⟨q, hq, hqdn, hqne2⟩
      have hqodd : Odd q := hq.odd_of_ne_two hqne2
      have hq_lt_n : q < n := by
        have hqle : q ≤ n := Nat.le_of_dvd (by omega : 0 < n) hqdn
        have hqne : q ≠ n := by
          intro hqe
          subst hqe
          exact hnprime hq
        omega
      have hqa : q ∣ a (n - 1) := odd_prime_dvd_a_pred_of_dvd hq hqodd hqdn hq_lt_n
      have hqsum : q ∣ a (n - 1) + 2 ^ (n - 2) := hqdn.trans hdiv
      have hqpow : q ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hqa).1 hqsum
      have hqdiv2 : q ∣ 2 := hq.dvd_of_dvd_pow hqpow
      have hqgt2 : 2 < q := by
        have hq2le := hq.two_le
        omega
      exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hqgt2) hqdiv2
    · have hall : ∀ q, q ∈ n.factorization.support → q = 2 := by
        intro q hqmem
        rw [Nat.support_factorization, Nat.mem_primeFactors] at hqmem
        rcases hqmem with ⟨hqprime, hqdn, hnne0⟩
        by_contra hqne
        exact hexodd ⟨q, hqprime, hqdn, hqne⟩
      let r := n.factorization 2
      have hfac_single : n.factorization = Finsupp.single 2 r := by
        ext q
        by_cases hq2 : q = 2
        · subst hq2
          simp [r]
        · have hq_not_mem : q ∉ n.factorization.support := by
            intro hqmem
            exact hq2 (hall q hqmem)
          have hqzero : n.factorization q = 0 := by
            exact Finsupp.notMem_support_iff.mp hq_not_mem
          simp [r, hq2, hqzero]
      have hn_ne0 : n ≠ 0 := by omega
      have hn_pow : n = 2 ^ r := Nat.eq_pow_of_factorization_eq_single hn_ne0 hfac_single
      have hr_ge2 : 2 ≤ r := by
        by_contra hrnot
        have hrle1 : r ≤ 1 := by omega
        have hnle2 : n ≤ 2 := by
          rw [hn_pow]
          interval_cases r <;> norm_num at hrle1 ⊢
        omega
      have hbad := not_dvd_a_sum_two_pow hr_ge2
      rw [hn_pow] at hdiv
      exact hbad hdiv
  refine ⟨prime_part, ?_⟩
  by_contra hnotprim
  have hn2 : 2 < n := hn
  have hna : n ∣ a (n - 1) := prime_dvd_a_pred_of_not_primitive prime_part hn2 hnotprim
  have hnpow : n ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hna).1 hdiv
  have hndiv2 : n ∣ 2 := prime_part.dvd_of_dvd_pow hnpow
  exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hn2) hndiv2
