import FormalConjectures.Util.ProblemImports

set_option linter.style.moduleDocstring false
set_option linter.unusedVariables false

open Nat BigOperators Finset

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

/- Auxiliary facts about 2^k - 1 -/

lemma two_pow_sub_one_pos {k : ℕ} (hk : 0 < k) : 0 < 2 ^ k - 1 := by
  have : 1 < 2 ^ k := Nat.one_lt_pow hk.ne' (by decide)
  omega

lemma two_pow_sub_one_ne_zero {k : ℕ} (hk : 0 < k) : 2 ^ k - 1 ≠ 0 :=
  (two_pow_sub_one_pos hk).ne'

lemma two_pow_sub_one_odd {k : ℕ} (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have hle : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have heven : Even (2 ^ k) := even_iff_two_dvd.mpr (dvd_pow_self 2 hk.ne')
  exact Nat.Even.sub_odd hle heven odd_one

lemma prod_Ico_two_pow_sub_one_ne_zero (n : ℕ) :
    ((Ico 1 n).prod fun k => 2 ^ k - 1) ≠ 0 := by
  refine prod_ne_zero_iff.mpr ?_
  intro k hk
  exact two_pow_sub_one_ne_zero (mem_Ico.mp hk).1

lemma prod_Ico_two_pow_sub_one_odd (n : ℕ) :
    Odd ((Ico 1 n).prod fun k => 2 ^ k - 1) := by
  refine prod_induction (fun k => 2 ^ k - 1) Odd (fun _ _ => Odd.mul) odd_one ?_
  intro k hk
  exact two_pow_sub_one_odd (mem_Ico.mp hk).1

/- p-adic valuations of products and sums -/

lemma padicValNat_prod {ι : Type*} {p : ℕ} [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValNat.mul, ih]
    · intro i hi
      exact hf i (mem_insert_of_mem hi)
    · exact hf a (mem_insert_self _ _)
    · exact prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)

lemma padicValNat_add_eq_left {p a b : ℕ} [Fact p.Prime]
    (h : padicValNat p a < padicValNat p b) (ha : a ≠ 0) :
    padicValNat p (a + b) = padicValNat p a := by
  have hb : b ≠ 0 := fun hb => by simp [hb] at h
  have hab : a + b ≠ 0 := by omega
  apply le_antisymm
  · have : ¬ p ^ (padicValNat p a + 1) ∣ a + b := by
      intro hdvd
      have hbdiv : p ^ (padicValNat p a + 1) ∣ b :=
        (padicValNat_dvd_iff_le hb).mpr (Nat.succ_le_of_lt h)
      have : p ^ (padicValNat p a + 1) ∣ a := by
        simpa using Nat.dvd_sub hdvd hbdiv
      exact pow_succ_padicValNat_not_dvd ha this
    have : padicValNat p (a + b) < padicValNat p a + 1 := by
      rw [← not_le, ← padicValNat_dvd_iff_le hab]
      exact this
    omega
  · rw [← padicValNat_dvd_iff_le hab]
    exact dvd_add pow_padicValNat_dvd ((padicValNat_dvd_iff_le hb).mpr h.le)

/- Multiplicative order of 2 modulo an odd prime -/

lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : (2 : ℕ) = (2 : ZMod p) := by simp
  rw [← this, ZMod.natCast_eq_zero_iff] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)

lemma orderOf_two_dvd_pred {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ∣ p - 1 :=
  ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp2)

lemma orderOf_two_pos {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    0 < orderOf (2 : ZMod p) := by
  have hdiv := orderOf_two_dvd_pred hp2
  have hp1 : p - 1 ≠ 0 := by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hdiv
    exact hp1 (Nat.eq_zero_of_zero_dvd hdiv)

lemma orderOf_two_le_pred {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ≤ p - 1 :=
  Nat.le_of_dvd (by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega) (orderOf_two_dvd_pred hp2)

lemma odd_prime_ne_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) : p ≠ 2 := by
  intro h
  subst h
  exact Nat.not_odd_iff_even.mpr even_two hodd

lemma two_pow_eq_one_iff {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ k = 1 ↔ p ∣ 2 ^ k - 1 := by
  have h1le : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  constructor
  · intro h
    have : ((2 ^ k - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_one, Nat.cast_two, h, sub_self]
    rwa [ZMod.natCast_eq_zero_iff] at this
  · intro h
    have h0 : ((2 ^ k - 1 : ℕ) : ZMod p) = 0 := by
      rwa [ZMod.natCast_eq_zero_iff]
    rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_one, Nat.cast_two] at h0
    exact eq_of_sub_eq_zero h0

lemma padicValNat_two_pow_sub_one_of_not_dvd {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : ¬ orderOf (2 : ZMod p) ∣ k) :
    padicValNat p (2 ^ k - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  exact h ((orderOf_dvd_iff_pow_eq_one).mpr ((two_pow_eq_one_iff hp2).mpr hdvd))

lemma padicValNat_two_pow_sub_one_of_dvd {p k : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hk : 0 < k) (hd : orderOf (2 : ZMod p) ∣ k) :
    padicValNat p (2 ^ k - 1) =
      padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) +
        padicValNat p (k / orderOf (2 : ZMod p)) := by
  have hp2 : p ≠ 2 := odd_prime_ne_two Fact.out hodd
  set d := orderOf (2 : ZMod p)
  have hdpos : 0 < d := orderOf_two_pos hp2
  have hkd : k / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hk hd) hdpos).ne'
  have h1lt : 1 < 2 ^ d := Nat.one_lt_pow hdpos.ne' (by decide)
  have hp_dvd : p ∣ 2 ^ d - 1 := (two_pow_eq_one_iff hp2).mp (pow_orderOf_eq_one _)
  have hp_not : ¬ p ∣ 2 ^ d := by
    intro h
    have : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hLTE := padicValNat.pow_sub_pow (p := p) (x := 2 ^ d) (y := 1) (n := k / d)
    hodd h1lt hp_dvd hp_not hkd
  -- LHS: padicValNat p ((2^d)^{k/d} - 1^{k/d}) = padicValNat p (2^k - 1)
  have hpow : (2 ^ d) ^ (k / d) = 2 ^ k := by
    rw [← pow_mul, Nat.mul_div_cancel' hd]
  simpa [hpow, pow_zero, one_pow] using hLTE

lemma one_le_padicValNat_two_pow_order {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    1 ≤ padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) := by
  have hp2 : p ≠ 2 := odd_prime_ne_two Fact.out hodd
  have hdpos : 0 < orderOf (2 : ZMod p) := orderOf_two_pos hp2
  refine one_le_padicValNat_of_dvd (two_pow_sub_one_ne_zero hdpos) ?_
  exact (two_pow_eq_one_iff hp2).mp (pow_orderOf_eq_one _)

/- Closed form for the product valuation -/

lemma div_succ_of_dvd {d N : ℕ} (hdpos : 0 < d) (hdiv : d ∣ N + 1) :
    (N + 1) / d = N / d + 1 := by
  obtain ⟨m, hm⟩ := hdiv
  have hmpos : 0 < m := by
    have : 0 < N + 1 := Nat.succ_pos _
    nlinarith
  have hdm : 1 ≤ d * m := by nlinarith
  have hd1 : 1 ≤ d := hdpos
  have hm1 : 1 ≤ m := hmpos
  have hN : N = d * m - 1 := by omega
  have hdecomp : d * m - 1 = (d - 1) + d * (m - 1) := by
    zify [hdm, hd1, hm1]
    ring
  have hlt : d - 1 < d := Nat.sub_lt hdpos (by decide)
  have : N / d = m - 1 := by
    rw [hN, hdecomp, Nat.add_mul_div_left _ _ hdpos, Nat.div_eq_of_lt hlt, zero_add]
  rw [hm, Nat.mul_div_right m hdpos, this]
  exact (Nat.sub_add_cancel hmpos).symm

lemma div_succ_of_not_dvd {d N : ℕ} (hdpos : 0 < d) (hdiv : ¬ d ∣ N + 1) :
    (N + 1) / d = N / d := by
  have hmodlt : N % d < d := Nat.mod_lt N hdpos
  have hmodNe : N % d ≠ d - 1 := by
    intro heq
    apply hdiv
    have hdivmod := Nat.div_add_mod N d
    have : N + 1 = d * (N / d + 1) := by
      have hcancel : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
      calc N + 1
          = d * (N / d) + N % d + 1 := by rw [hdivmod]
        _ = d * (N / d) + (d - 1) + 1 := by rw [heq]
        _ = d * (N / d) + d := by rw [Nat.add_assoc, hcancel]
        _ = d * (N / d + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [Nat.dvd_iff_mod_eq_zero, this, Nat.mul_mod_right]
  have hlt : N % d + 1 < d := by omega
  have : N + 1 = (N % d + 1) + d * (N / d) := by
    have := Nat.div_add_mod N d
    omega
  rw [this, Nat.add_mul_div_left _ _ hdpos, Nat.div_eq_of_lt hlt, zero_add]

lemma padicValNat_sum_two_pow_sub_one {p : ℕ} [Fact p.Prime] (hodd : Odd p) (N : ℕ) :
    ∑ k ∈ Ico 1 (N + 1), padicValNat p (2 ^ k - 1) =
      padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) * (N / orderOf (2 : ZMod p)) +
        padicValNat p (N / orderOf (2 : ZMod p))! := by
  have hp2 : p ≠ 2 := odd_prime_ne_two Fact.out hodd
  set d := orderOf (2 : ZMod p)
  have hdpos : 0 < d := orderOf_two_pos hp2
  induction N with
  | zero => simp
  | succ N ih =>
    have hsucc : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [sum_Ico_succ_top hsucc, ih]
    by_cases hdiv : d ∣ N + 1
    · have hval : padicValNat p (2 ^ (N + 1) - 1) =
          padicValNat p (2 ^ d - 1) + padicValNat p ((N + 1) / d) :=
        padicValNat_two_pow_sub_one_of_dvd hodd (Nat.succ_pos _) hdiv
      have hdivN : (N + 1) / d = N / d + 1 := div_succ_of_dvd hdpos hdiv
      rw [hval, hdivN, factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (factorial_ne_zero _)]
      ring
    · have hval : padicValNat p (2 ^ (N + 1) - 1) = 0 :=
        padicValNat_two_pow_sub_one_of_not_dvd hp2 hdiv
      have hdivN : (N + 1) / d = N / d := div_succ_of_not_dvd hdpos hdiv
      rw [hval, hdivN, add_zero]

lemma padicValNat_prod_two_pow_sub_one {p n : ℕ} [Fact p.Prime] (hodd : Odd p) :
    padicValNat p ((Ico 1 n).prod fun k => 2 ^ k - 1) =
      padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) * ((n - 1) / orderOf (2 : ZMod p)) +
        padicValNat p ((n - 1) / orderOf (2 : ZMod p))! := by
  cases n with
  | zero => simp
  | succ n =>
    rw [padicValNat_prod (Ico 1 (n + 1)) (fun k => 2 ^ k - 1)
      (fun k hk => two_pow_sub_one_ne_zero (mem_Ico.mp hk).1)]
    simpa [Nat.succ_sub_one] using padicValNat_sum_two_pow_sub_one hodd n

lemma padicValNat_prod_two_pow_sub_one_ge {p n : ℕ} [Fact p.Prime] (hodd : Odd p) :
    padicValNat p ((n - 1) / (p - 1))! + (n - 1) / (p - 1) ≤
      padicValNat p ((Ico 1 n).prod fun k => 2 ^ k - 1) := by
  have hp2 : p ≠ 2 := odd_prime_ne_two Fact.out hodd
  have hdpos : 0 < orderOf (2 : ZMod p) := orderOf_two_pos hp2
  have hdle : orderOf (2 : ZMod p) ≤ p - 1 := orderOf_two_le_pred hp2
  have hdiv : (n - 1) / (p - 1) ≤ (n - 1) / orderOf (2 : ZMod p) :=
    Nat.div_le_div_left hdle hdpos
  have hfac : padicValNat p ((n - 1) / (p - 1))! ≤
      padicValNat p ((n - 1) / orderOf (2 : ZMod p))! := by
    have hdvd : ((n - 1) / (p - 1))! ∣ ((n - 1) / orderOf (2 : ZMod p))! :=
      factorial_dvd_factorial hdiv
    exact (padicValNat_dvd_iff_le (factorial_ne_zero _)).mp (pow_padicValNat_dvd.trans hdvd)
  have he0 : 1 ≤ padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) :=
    one_le_padicValNat_two_pow_order hodd
  rw [padicValNat_prod_two_pow_sub_one hodd]
  have : (n - 1) / (p - 1) ≤
      padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) * ((n - 1) / orderOf (2 : ZMod p)) := by
    calc (n - 1) / (p - 1)
        ≤ (n - 1) / orderOf (2 : ZMod p) := hdiv
      _ ≤ padicValNat p (2 ^ orderOf (2 : ZMod p) - 1) * ((n - 1) / orderOf (2 : ZMod p)) :=
        Nat.le_mul_of_pos_left _ he0
  omega

/- Integrality of `a` -/

lemma padicValNat_factorial_le_div {p n : ℕ} [Fact p.Prime] (hodd : Odd p) :
    padicValNat p n ! ≤ (n - 1) / (p - 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hsum : 1 ≤ (p.digits n).sum := by
    have hnil : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
    exact Nat.sum_pos_iff_exists_pos.mpr
      ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩
  have heq := sub_one_mul_padicValNat_factorial (p := p) n
  have hp1 : 0 < p - 1 := by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hmul : (p - 1) * padicValNat p n ! ≤ n - 1 := by
    rw [heq]
    exact Nat.sub_le_sub_left hsum _
  exact (Nat.le_div_iff_mul_le hp1).mpr (by rwa [mul_comm])

lemma a_mul_factorial (n : ℕ) (hn : n ≠ 0) :
    a n * n.factorial = 2 ^ (n - 1) * ((Ico 1 n).prod fun k => 2 ^ k - 1) := by
  have ha : a n =
      (2 ^ n.pred * ((Ico 1 n).prod fun k => 2 ^ k - 1)) / n.factorial := by
    simp [a, hn]
  have hpred : n.pred = n - 1 := Nat.pred_eq_sub_one
  rw [ha, hpred, Nat.div_mul_cancel]
  refine (Nat.factorization_le_iff_dvd (factorial_ne_zero n)
    (mul_ne_zero (pow_ne_zero _ two_ne_zero) (prod_Ico_two_pow_sub_one_ne_zero n))).mp ?_
  rw [Finsupp.le_def]
  intro p
  by_cases hpp : p.Prime
  · haveI : Fact p.Prime := ⟨hpp⟩
    rw [factorization_def _ hpp, factorization_def _ hpp]
    by_cases hp2 : p = 2
    · subst hp2
      have hP : padicValNat 2 ((Ico 1 n).prod fun k => 2 ^ k - 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h =>
          Nat.not_even_iff_odd.mpr (prod_Ico_two_pow_sub_one_odd n) (even_iff_two_dvd.mpr h))
      have hleft : padicValNat 2 n ! ≤ n - 1 :=
        Nat.le_sub_one_of_lt (padicValNat_factorial_lt_of_ne_zero 2 hn)
      have hright : padicValNat 2 (2 ^ (n - 1) * ((Ico 1 n).prod fun k => 2 ^ k - 1)) = n - 1 := by
        rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (prod_Ico_two_pow_sub_one_ne_zero n),
          padicValNat.pow (n - 1) two_ne_zero, padicValNat.self (by decide), mul_one, hP, add_zero]
      exact hleft.trans_eq hright.symm
    · have hodd : Odd p := hpp.odd_of_ne_two hp2
      have h2 : padicValNat p (2 ^ (n - 1)) = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h =>
          hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h)))
      rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (prod_Ico_two_pow_sub_one_ne_zero n), h2,
        zero_add]
      have hge := padicValNat_prod_two_pow_sub_one_ge (p := p) (n := n) hodd
      have hfac := padicValNat_factorial_le_div (p := p) (n := n) hodd
      omega
  · simp [factorization_eq_zero_of_not_prime, hpp]

lemma a_spec (n : ℕ) (hn : 0 < n) :
    a n * n.factorial = 2 ^ (n - 1) * ((Ico 1 n).prod fun k => 2 ^ k - 1) :=
  a_mul_factorial n hn.ne'

lemma factorial_eq_self_mul_pred (n : ℕ) (hn : 0 < n) :
    n ! = n * (n - 1)! := by
  cases n with
  | zero => omega
  | succ n =>
    rw [factorial_succ, Nat.add_sub_cancel, mul_comm]

/- The condition is equivalent to a clean divisibility -/

lemma dvd_iff_factorial_dvd {n : ℕ} (hn : 2 < n) :
    n ∣ a (n - 1) + 2 ^ (n - 2) ↔
      n.factorial ∣ 2 ^ (n - 2) *
        (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1).factorial) := by
  have hn1 : 0 < n - 1 := by omega
  have ha : a (n - 1) * (n - 1)! =
      2 ^ (n - 2) * ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) := by
    have := a_spec (n - 1) hn1
    rwa [show n - 1 - 1 = n - 2 by omega] at this
  have hnf : n ! = n * (n - 1)! := factorial_eq_self_mul_pred n (by omega)
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    calc 2 ^ (n - 2) * (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1)!)
        = 2 ^ (n - 2) * ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) +
            2 ^ (n - 2) * (n - 1)! := by ring
      _ = a (n - 1) * (n - 1)! + 2 ^ (n - 2) * (n - 1)! := by rw [ha]
      _ = (a (n - 1) + 2 ^ (n - 2)) * (n - 1)! := by ring
      _ = (n * m) * (n - 1)! := by rw [hm]
      _ = n * (n - 1)! * m := by ring
      _ = n ! * m := by rw [hnf]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hmul :
        (a (n - 1) + 2 ^ (n - 2)) * (n - 1)! = (n * m) * (n - 1)! := by
      calc (a (n - 1) + 2 ^ (n - 2)) * (n - 1)!
          = a (n - 1) * (n - 1)! + 2 ^ (n - 2) * (n - 1)! := by ring
        _ = 2 ^ (n - 2) * ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) +
              2 ^ (n - 2) * (n - 1)! := by rw [ha]
        _ = 2 ^ (n - 2) * (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1)!) := by ring
        _ = n ! * m := hm
        _ = n * (n - 1)! * m := by rw [hnf]
        _ = (n * m) * (n - 1)! := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (factorial_ne_zero _)) hmul

/- Composite case: powers of two -/

lemma digits_two_pow_sum (k : ℕ) : (Nat.digits 2 (2 ^ k)).sum = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
    have h2eq : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    rw [Nat.digits_of_two_le_of_pos (by decide) hpos, h2eq]
    have hmod : 2 * 2 ^ k % 2 = 0 := Nat.mul_mod_right 2 (2 ^ k)
    have hdiv : 2 * 2 ^ k / 2 = 2 ^ k := by
      rw [Nat.mul_comm, Nat.mul_div_left _ (show 0 < 2 by decide)]
    rw [hmod, hdiv]
    simp only [List.sum_cons, zero_add, ih]

lemma padicValNat_two_pow_factorial (k : ℕ) :
    padicValNat 2 (2 ^ k)! = 2 ^ k - 1 := by
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have heq := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ k)
  have hdig := digits_two_pow_sum k
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

lemma not_dvd_of_pow_two {k : ℕ} (hk : 2 ≤ k) :
    ¬ (2 ^ k).factorial ∣
      2 ^ (2 ^ k - 2) *
        (((Ico 1 (2 ^ k - 1)).prod fun t => 2 ^ t - 1) + (2 ^ k - 1).factorial) := by
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  set n := 2 ^ k with hn_def
  have hn2 : 2 < n := by
    have : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (show (2 : ℕ) > 0 by decide) hk
    omega
  have hPodd : Odd ((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) :=
    prod_Ico_two_pow_sub_one_odd (n - 1)
  have hsum_odd : Odd
      (((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) + (n - 1).factorial) := by
    have heven : Even (n - 1).factorial :=
      even_iff_two_dvd.mpr (dvd_factorial (by decide : 0 < 2) (by omega : 2 ≤ n - 1))
    exact hPodd.add_even heven
  have hv2_sum : padicValNat 2
      (((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) + (n - 1).factorial) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h =>
      Nat.not_even_iff_odd.mpr hsum_odd (even_iff_two_dvd.mpr h))
  have hne_sum : (((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) + (n - 1).factorial) ≠ 0 := by
    have : ((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) ≠ 0 := prod_Ico_two_pow_sub_one_ne_zero _
    omega
  have hleft : padicValNat 2
      (2 ^ (n - 2) *
        (((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) + (n - 1).factorial)) = n - 2 := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hne_sum, padicValNat.pow (n - 2) two_ne_zero,
      padicValNat.self (by decide), mul_one, hv2_sum, add_zero]
  have hright : padicValNat 2 n ! = n - 1 := by
    rw [hn_def, padicValNat_two_pow_factorial]
  intro h
  have hle : padicValNat 2 n ! ≤
      padicValNat 2
        (2 ^ (n - 2) *
          (((Ico 1 (n - 1)).prod fun t => 2 ^ t - 1) + (n - 1).factorial)) :=
    (padicValNat_dvd_iff_le
      (mul_ne_zero (pow_ne_zero _ two_ne_zero) hne_sum)).mp
      (pow_padicValNat_dvd.trans h)
  omega

/- Composite case: odd prime factor -/

lemma padicValNat_factorial_pred_mul {p t : ℕ} [Fact p.Prime] (ht : 0 < t) :
    padicValNat p (p * t - 1)! = padicValNat p (t - 1)! + (t - 1) := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have ht1 : 1 ≤ t := ht
  have hpt : 1 ≤ p * t := by nlinarith
  have heq : p * t - 1 = p * (t - 1) + (p - 1) := by
    zify [hp1, ht1, hpt]
    ring
  rw [heq, padicValNat_factorial_mul_add (t - 1) (Nat.sub_lt hppos (by decide)),
    padicValNat_factorial_mul]

lemma factorial_mul_Icc_prod (t s : ℕ) (ht : 0 < t) :
    (t - 1)! * ∏ i ∈ Icc t (t + s), i = (t + s)! := by
  induction s with
  | zero =>
    simp only [add_zero, Icc_self, prod_singleton]
    cases t with
    | zero => omega
    | succ t =>
      rw [factorial_succ, Nat.add_sub_cancel, mul_comm]
  | succ s ih =>
    have hts : t + (s + 1) = t + s + 1 := by omega
    have hinsert : Icc t (t + s + 1) = insert (t + s + 1) (Icc t (t + s)) := by
      ext x
      simp only [mem_Icc, mem_insert]
      constructor <;> omega
    have hnot : t + s + 1 ∉ Icc t (t + s) := by
      simp [mem_Icc]
    rw [hts, factorial_succ, hinsert, prod_insert hnot, mul_comm (t + s + 1), ← mul_assoc, ih]
    ring

lemma key_val_ineq {n p : ℕ} [Fact p.Prime] (hodd : Odd p) (hpdiv : p ∣ n)
    (hnprime : ¬ n.Prime) (hn : 2 < n) :
    padicValNat p (n - 1)! <
      padicValNat p ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) := by
  have hp2 : p ≠ 2 := odd_prime_ne_two Fact.out hodd
  have hp1pos : 0 < p - 1 := by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  set t := n / p
  have hnt : n = p * t := (Nat.mul_div_cancel' hpdiv).symm
  have htpos : 0 < t := by
    have hn0 : 0 < n := by omega
    exact Nat.div_pos (Nat.le_of_dvd hn0 hpdiv) (Fact.out : p.Prime).pos
  have ht2 : 2 ≤ t := by
    have ht1 : t ≠ 1 := by
      intro ht
      apply hnprime
      rw [hnt, ht, mul_one]
      exact Fact.out
    omega
  have hge := padicValNat_prod_two_pow_sub_one_ge (p := p) (n := n - 1) hodd
  have hn12 : n - 1 - 1 = n - 2 := by omega
  rw [hn12] at hge
  have hsub : p * t - t = (p - 1) * t := by
    simpa using (Nat.mul_sub_right_distrib p 1 t).symm
  have ht_le : t ≤ p * t := Nat.le_mul_of_pos_left t (Fact.out : p.Prime).pos
  have hn2eq : n - 2 = p * t - 2 := by omega
  have hsplit : p * t - 2 = (p * t - t) + (t - 2) := by omega
  have hdecomp : n - 2 = (t - 2) + (p - 1) * t := by
    rw [hn2eq, hsplit, hsub, add_comm]
  have hfloor : (n - 2) / (p - 1) = (t - 2) / (p - 1) + t := by
    rw [hdecomp, Nat.add_mul_div_left _ _ hp1pos]
  set s := (t - 2) / (p - 1)
  have hst : t + s = (n - 2) / (p - 1) := by
    rw [hfloor, add_comm]
  have hge' : padicValNat p (t + s)! + (t + s) ≤
      padicValNat p ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) := by
    simpa [hst] using hge
  have hfac : padicValNat p (n - 1)! = padicValNat p (t - 1)! + (t - 1) := by
    simpa [hnt] using padicValNat_factorial_pred_mul (p := p) (t := t) htpos
  have hprod_ne : (∏ i ∈ Icc t (t + s), i) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro i hi
    rw [mem_Icc] at hi
    omega
  have hdiff : padicValNat p (t + s)! =
      padicValNat p (t - 1)! + padicValNat p (∏ i ∈ Icc t (t + s), i) := by
    have hprod := factorial_mul_Icc_prod t s htpos
    rw [← hprod, padicValNat.mul (factorial_ne_zero _) hprod_ne]
  have hlt_ts : t - 1 < t + s := by
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right t s)
    exact Nat.sub_lt htpos (by decide)
  calc padicValNat p (n - 1)!
      = padicValNat p (t - 1)! + (t - 1) := hfac
    _ ≤ padicValNat p (t - 1)! + padicValNat p (∏ i ∈ Icc t (t + s), i) + (t - 1) := by
        omega
    _ = padicValNat p (t + s)! + (t - 1) := by
        rw [← hdiff]
    _ < padicValNat p (t + s)! + (t + s) := Nat.add_lt_add_left hlt_ts _
    _ ≤ padicValNat p ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) := hge'

lemma not_dvd_of_odd_prime_factor {n p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpdiv : p ∣ n) (hnprime : ¬ n.Prime) (hn : 2 < n) :
    ¬ n.factorial ∣
      2 ^ (n - 2) *
        (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1).factorial) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have hPgt := key_val_ineq (n := n) (p := p) hodd hpdiv hnprime hn
  have hneP : ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) ≠ 0 :=
    prod_Ico_two_pow_sub_one_ne_zero _
  have hneF : (n - 1).factorial ≠ 0 := factorial_ne_zero _
  have hvsum : padicValNat p
      (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1).factorial) =
      padicValNat p (n - 1)! := by
    rw [add_comm]
    exact padicValNat_add_eq_left hPgt hneF
  have h2 : padicValNat p (2 ^ (n - 2)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hdvd =>
      (odd_prime_ne_two hp hodd)
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)))
  have hne_sum : (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1).factorial) ≠ 0 := by
    omega
  have hleft : padicValNat p
      (2 ^ (n - 2) *
        (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1).factorial)) =
      padicValNat p (n - 1)! := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hne_sum, h2, zero_add, hvsum]
  have hright : padicValNat p n ! = padicValNat p n + padicValNat p (n - 1)! := by
    rw [factorial_eq_self_mul_pred n (by omega),
      padicValNat.mul (by omega) (factorial_ne_zero _)]
  have hp_le : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd (by omega) hpdiv
  have : padicValNat p n ! ≤ padicValNat p
      (2 ^ (n - 2) *
        (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) + (n - 1).factorial)) :=
    (padicValNat_dvd_iff_le
      (mul_ne_zero (pow_ne_zero _ two_ne_zero) hne_sum)).mp
      (pow_padicValNat_dvd.trans h)
  omega

lemma not_dvd_of_composite {n : ℕ} (hn : 2 < n) (hnprime : ¬ n.Prime) :
    ¬ n ∣ a (n - 1) + 2 ^ (n - 2) := by
  rw [dvd_iff_factorial_dvd hn]
  obtain ⟨k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · have hk : 2 ≤ k := by
      have : 2 < 2 ^ k := hn
      contrapose! this
      interval_cases k <;> simp
    exact not_dvd_of_pow_two hk
  · exact not_dvd_of_odd_prime_factor hp hodd hdvd hnprime hn

/- Prime case: the condition forces 2 to be a primitive root -/

lemma primitive_root_of_dvd {n : ℕ} (hn : 2 < n) (hp : n.Prime)
    (hdvd : n ∣ a (n - 1) + 2 ^ (n - 2)) :
    IsPrimitiveRoot (2 : ZMod n) n.totient := by
  haveI : Fact n.Prime := ⟨hp⟩
  have hn2 : n ≠ 2 := by omega
  rw [totient_prime hp, IsPrimitiveRoot.iff_orderOf]
  have horder_dvd : orderOf (2 : ZMod n) ∣ n - 1 := orderOf_two_dvd_pred hn2
  have horder_pos : 0 < orderOf (2 : ZMod n) := orderOf_two_pos hn2
  by_contra hne
  have hlt : orderOf (2 : ZMod n) < n - 1 :=
    lt_of_le_of_ne (Nat.le_of_dvd (by omega) horder_dvd) hne
  have hmem : orderOf (2 : ZMod n) ∈ Ico 1 (n - 1) := by
    rw [mem_Ico]
    omega
  have hnP : n ∣ (Ico 1 (n - 1)).prod fun k => 2 ^ k - 1 :=
    dvd_trans ((two_pow_eq_one_iff hn2).mp (pow_orderOf_eq_one _)) (dvd_prod_of_mem _ hmem)
  have ha : a (n - 1) * (n - 1)! =
      2 ^ (n - 2) * ((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1) := by
    have := a_spec (n - 1) (by omega)
    rwa [show n - 1 - 1 = n - 2 by omega] at this
  have hcongr :
      (a (n - 1) : ZMod n) * ((n - 1)! : ZMod n) =
        ((2 ^ (n - 2) : ℕ) : ZMod n) *
          (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1 : ℕ) : ZMod n) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, ha]
  have hP0 : (((Ico 1 (n - 1)).prod fun k => 2 ^ k - 1 : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hnP
  have hW : ((n - 1)! : ZMod n) = -1 := ZMod.wilsons_lemma n
  have ha0 : (a (n - 1) : ZMod n) = 0 := by
    have : (a (n - 1) : ZMod n) * (-1) = 0 := by
      rw [← hW, hcongr, hP0, mul_zero]
    rwa [mul_neg_one, neg_eq_zero] at this
  have hcond : ((a (n - 1) + 2 ^ (n - 2) : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hpow0 : ((2 ^ (n - 2) : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_add, ha0, zero_add] at hcond
    exact hcond
  have hpow : ((2 ^ (n - 2) : ℕ) : ZMod n) = (2 : ZMod n) ^ (n - 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hpow] at hpow0
  exact pow_ne_zero _ (two_ne_zero_zmod hn2) hpow0

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdvd
  have hp : n.Prime := by
    by_contra hnp
    exact not_dvd_of_composite hn hnp hdvd
  exact ⟨hp, primitive_root_of_dvd hn hp hdvd⟩
