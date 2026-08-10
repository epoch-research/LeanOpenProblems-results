import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The term $C(6k,3k)C(3k,k)$ appearing in the sum. -/
def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

set_option linter.unusedVariables false

def A0 (a : Nat) := a - a/2 - a/3
def C0 (a : Nat) := a/2 - a/3

opaque A0C0_nonneg (x y z : Nat) (hz : z = x + y ∨ z = x + y + 1) : C0 z ≤ A0 x + A0 y := by
  unfold A0 C0
  rcases hz with rfl | rfl <;> omega

opaque A0C0_ge_one (x y z t : Nat) (hz : z = x + y ∨ z = x + y + 1) (hmod : z = 6*t + 3) :
    1 + C0 z ≤ A0 x + A0 y := by
  have h0 := A0C0_nonneg x y z hz
  unfold A0 C0 at *
  rcases hz with rfl | rfl <;> omega

opaque div_add_or_succ (a b q : Nat) (hq : 0 < q) :
    (a+b)/q = a/q + b/q ∨ (a+b)/q = a/q + b/q + 1 := by
  have h := Nat.add_div (a:=a) (b:=b) hq
  rw [h]
  split_ifs <;> omega

opaque div_div_two_six (a q : Nat) : (6*a / q) / 2 = 3*a / q := by
  calc
    (6*a / q) / 2 = (6*a) / (q*2) := by rw [Nat.div_div_eq_div_mul]
    _ = (2*(3*a)) / (2*q) := by congr 1 <;> ring
    _ = 3*a / q := by rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]

opaque div_div_three_six (a q : Nat) : (6*a / q) / 3 = 2*a / q := by
  calc
    (6*a / q) / 3 = (6*a) / (q*3) := by rw [Nat.div_div_eq_div_mul]
    _ = (3*(2*a)) / (3*q) := by congr 1 <;> ring
    _ = 2*a / q := by rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 3)]

opaque floor_contrib_nonneg (n k l q : Nat) (hkl : k + l = n) (hq : 0 < q) :
    (3*n)/q + (3*k)/q + (3*l)/q + (2*k)/q + (2*l)/q ≤
      (6*k)/q + (6*l)/q + (2*n)/q := by
  let x := (6*k)/q
  let y := (6*l)/q
  let z := (6*n)/q
  have hz : z = x + y ∨ z = x + y + 1 := by
    have hsum : 6*n = 6*k + 6*l := by omega
    have h := div_add_or_succ (6*k) (6*l) q hq
    simpa [x,y,z, hsum] using h
  have hh := A0C0_nonneg x y z hz
  unfold A0 C0 at hh
  have hx2 : x / 2 = 3*k / q := by simpa [x] using div_div_two_six k q
  have hx3 : x / 3 = 2*k / q := by simpa [x] using div_div_three_six k q
  have hy2 : y / 2 = 3*l / q := by simpa [y] using div_div_two_six l q
  have hy3 : y / 3 = 2*l / q := by simpa [y] using div_div_three_six l q
  have hz2 : z / 2 = 3*n / q := by simpa [z] using div_div_two_six n q
  have hz3 : z / 3 = 2*n / q := by simpa [z] using div_div_three_six n q
  omega

opaque floor_contrib_ge_one_of_dvd (n k l q : Nat) (hnpos : 0 < n) (hkl : k + l = n) (hqpos : 0 < q)
    (hqgt : 3 < q) (hqdvd : q ∣ 2*n - 1) :
    1 + ((3*n)/q + (3*k)/q + (3*l)/q + (2*k)/q + (2*l)/q) ≤
      (6*k)/q + (6*l)/q + (2*n)/q := by
  let x := (6*k)/q
  let y := (6*l)/q
  let z := (6*n)/q
  have hz : z = x + y ∨ z = x + y + 1 := by
    have hsum : 6*n = 6*k + 6*l := by omega
    have h := div_add_or_succ (6*k) (6*l) q hqpos
    simpa [x,y,z, hsum] using h
  rcases hqdvd with ⟨a, ha⟩
  have hmpos : 0 < 2*n - 1 := by omega
  have h2n : 2*n = q*a + 1 := by omega
  have hmodd : Odd (2*n - 1) := by
    rw [show 2*n - 1 = 2*(n-1)+1 by omega]
    exact odd_two_mul_add_one (n-1)
  have haodd : Odd a := by
    rw [ha] at hmodd
    exact Nat.Odd.of_mul_right hmodd
  rcases haodd with ⟨t, ht⟩
  have hzmod : z = 6*t + 3 := by
    -- z = floor(6n/q) = 3*a = 6t+3
    have h6n : 6*n = q*(3*a) + 3 := by
      rw [show 6*n = 3*(2*n) by ring]
      rw [h2n]
      ring
    have hrem : 3 < q := hqgt
    have hz_eq : 6*n / q = 3*a := by
      rw [h6n]
      rw [Nat.add_comm]
      rw [Nat.add_mul_div_left _ _ hqpos]
      simp [Nat.div_eq_of_lt hrem]
    change 6*n / q = 6*t + 3
    rw [hz_eq, ht]
    ring
  have hh := A0C0_ge_one x y z t hz hzmod
  unfold A0 C0 at hh
  have hx2 : x / 2 = 3*k / q := by simpa [x] using div_div_two_six k q
  have hx3 : x / 3 = 2*k / q := by simpa [x] using div_div_three_six k q
  have hy2 : y / 2 = 3*l / q := by simpa [y] using div_div_two_six l q
  have hy3 : y / 3 = 2*l / q := by simpa [y] using div_div_three_six l q
  have hz2 : z / 2 = 3*n / q := by simpa [z] using div_div_two_six n q
  have hz3 : z / 3 = 2*n / q := by simpa [z] using div_div_three_six n q
  omega

opaque sum_pay_subset {α : Type*} [DecidableEq α] (s t : Finset α) (f g : α → Nat)
    (hst : t ⊆ s) (hone : ∀ x ∈ t, 1 + f x ≤ g x) (hnon : ∀ x ∈ s, f x ≤ g x) :
    t.card + ∑ x ∈ s, f x ≤ ∑ x ∈ s, g x := by
  classical
  let u := s \ t
  have hsplitf : (∑ x ∈ s, f x) = (∑ x ∈ t, f x) + (∑ x ∈ u, f x) := by
    have h := (Finset.sum_sdiff (s₁:=t) (s₂:=s) (f:=f) hst).symm
    rw [h]
    dsimp [u]
    omega
  have hsplitg : (∑ x ∈ s, g x) = (∑ x ∈ t, g x) + (∑ x ∈ u, g x) := by
    have h := (Finset.sum_sdiff (s₁:=t) (s₂:=s) (f:=g) hst).symm
    rw [h]
    dsimp [u]
    omega
  have h1 : t.card + (∑ x ∈ t, f x) ≤ ∑ x ∈ t, g x := by
    have hc : t.card = ∑ x ∈ t, (1 : Nat) := by simp
    rw [hc, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (by intro x hx; exact hone x hx)
  have h2 : (∑ x ∈ u, f x) ≤ (∑ x ∈ u, g x) := by
    exact Finset.sum_le_sum (by intro x hx; exact hnon x (by exact (Finset.mem_sdiff.mp hx).1))
  omega

opaque hfac_non3_ineq (n k l p e : Nat) (hnpos : 0 < n) (hkl : k + l = n)
    (hp : p.Prime) (hpne3 : p ≠ 3) (he : p^e ∣ 2*n - 1) :
    e + ((3*n).factorial).factorization p + ((3*k).factorial).factorization p + ((3*l).factorial).factorization p + ((2*k).factorial).factorization p + ((2*l).factorial).factorization p ≤
      ((6*k).factorial).factorization p + ((6*l).factorial).factorization p + ((2*n).factorial).factorization p := by
  by_cases hp2 : p = 2
  · subst p
    have hezero : e = 0 := by
      by_contra hepos
      have hepos' : 0 < e := Nat.pos_of_ne_zero hepos
      have h2dvd : 2 ∣ 2*n - 1 := by
        have hpow : 2^1 ∣ 2^e := pow_dvd_pow 2 hepos'
        exact hpow.trans he
      rcases h2dvd with ⟨a, ha⟩
      omega
    subst e
    have hB3n : Nat.log 2 (3*n) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 3*n ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB3k : Nat.log 2 (3*k) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 3*k ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB3l : Nat.log 2 (3*l) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 3*l ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB2k : Nat.log 2 (2*k) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 2*k ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB2l : Nat.log 2 (2*l) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 2*l ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB6k : Nat.log 2 (6*k) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 6*k ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB6l : Nat.log 2 (6*l) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 6*l ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB2n : Nat.log 2 (2*n) < Nat.log 2 (6*n) + 1 := (Nat.log_mono_right (by omega : 2*n ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    rw [Nat.factorization_factorial Nat.prime_two hB3n, Nat.factorization_factorial Nat.prime_two hB3k,
      Nat.factorization_factorial Nat.prime_two hB3l, Nat.factorization_factorial Nat.prime_two hB2k,
      Nat.factorization_factorial Nat.prime_two hB2l, Nat.factorization_factorial Nat.prime_two hB6k,
      Nat.factorization_factorial Nat.prime_two hB6l, Nat.factorization_factorial Nat.prime_two hB2n]
    have hpay := Finset.sum_le_sum (s:=Finset.Ico 1 (Nat.log 2 (6*n) + 1))
      (f:=fun i => (3*n)/(2^i) + (3*k)/(2^i) + (3*l)/(2^i) + (2*k)/(2^i) + (2*l)/(2^i))
      (g:=fun i => (6*k)/(2^i) + (6*l)/(2^i) + (2*n)/(2^i))
      (by intro i hi; exact floor_contrib_nonneg n k l (2^i) hkl (pow_pos (by norm_num) i))
    simp only [Finset.sum_add_distrib] at hpay
    simpa [add_assoc] using hpay
  · let B := Nat.log p (6*n) + 1
    let s := Finset.Ico 1 B
    let t := Finset.Ico 1 (e+1)
    let f := fun i => (3*n)/(p^i) + (3*k)/(p^i) + (3*l)/(p^i) + (2*k)/(p^i) + (2*l)/(p^i)
    let g := fun i => (6*k)/(p^i) + (6*l)/(p^i) + (2*n)/(p^i)
    have hst : t ⊆ s := by
      intro i hi
      simp [t, s, B] at hi ⊢
      have hi_le_e : i ≤ e := hi.2
      have hpowdvd : p^i ∣ 2*n - 1 := (pow_dvd_pow p hi_le_e).trans he
      have hposm : 0 < 2*n - 1 := by omega
      have hle : p^i ≤ 6*n := (le_of_dvd hposm hpowdvd).trans (by omega)
      have hp1 : 1 < p := hp.one_lt
      have hlog : i ≤ Nat.log p (6*n) := (Nat.le_log_iff_pow_le hp1 (by omega : 6*n ≠ 0)).2 hle
      omega
    have hone : ∀ i ∈ t, 1 + f i ≤ g i := by
      intro i hi
      have hi' : 1 ≤ i ∧ i < e + 1 := by simpa [t] using hi
      have hi_le_e : i ≤ e := Nat.le_of_lt_succ hi'.2
      have hpowdvd : p^i ∣ 2*n - 1 := (pow_dvd_pow p hi_le_e).trans he
      have hqgt : 3 < p^i := by
        have hi1 : 1 ≤ i := hi'.1
        have hpgt3 : 3 < p := by
          have hp2le : 2 ≤ p := hp.two_le
          omega
        calc 3 < p := hpgt3
          _ ≤ p^i := Nat.le_self_pow (a:=p) (by omega : i ≠ 0)
      exact floor_contrib_ge_one_of_dvd n k l (p^i) hnpos hkl (pow_pos hp.pos i) hqgt hpowdvd
    have hnon : ∀ i ∈ s, f i ≤ g i := by
      intro i hi
      exact floor_contrib_nonneg n k l (p^i) hkl (pow_pos hp.pos i)
    have hpay := sum_pay_subset s t f g hst hone hnon
    have hcard : t.card = e := by simp [t]
    simp only [s, f, g] at hpay
    rw [hcard] at hpay
    have hB3n : Nat.log p (3*n) < B := (Nat.log_mono_right (by omega : 3*n ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB3k : Nat.log p (3*k) < B := (Nat.log_mono_right (by omega : 3*k ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB3l : Nat.log p (3*l) < B := (Nat.log_mono_right (by omega : 3*l ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB2k : Nat.log p (2*k) < B := (Nat.log_mono_right (by omega : 2*k ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB2l : Nat.log p (2*l) < B := (Nat.log_mono_right (by omega : 2*l ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB6k : Nat.log p (6*k) < B := (Nat.log_mono_right (by omega : 6*k ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB6l : Nat.log p (6*l) < B := (Nat.log_mono_right (by omega : 6*l ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    have hB2n : Nat.log p (2*n) < B := (Nat.log_mono_right (by omega : 2*n ≤ 6*n)).trans_lt (Nat.lt_succ_self _)
    rw [Nat.factorization_factorial hp hB3n, Nat.factorization_factorial hp hB3k,
      Nat.factorization_factorial hp hB3l, Nat.factorization_factorial hp hB2k,
      Nat.factorization_factorial hp hB2l, Nat.factorization_factorial hp hB6k,
      Nat.factorization_factorial hp hB6l, Nat.factorization_factorial hp hB2n]
    simp only [B, Finset.sum_add_distrib] at hpay
    simpa [add_assoc] using hpay
opaque core_carry (n q a t r : Nat) (hq : 2 ≤ q) (h2 : 2*n = q*a + 1) (hn : n = q*t + r) (hr : r < q) : q ≤ r+r := by
  by_contra hlt'
  have hlt : r + r < q := by omega
  have hq1 : 1 < q := by omega
  have hmod1 : (2*n) % q = 1 := by
    rw [h2]
    rw [Nat.add_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hq1
  have hmod2 : (2*n) % q = (r+r) := by
    have hn2 : 2*n = q*(2*t) + (r+r) := by rw [hn]; ring
    rw [hn2]
    rw [Nat.add_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hlt
  omega

opaque three_central_factorization (n e : Nat) (hnpos : 0 < n) (he : 3^e ∣ 2*n - 1) :
    e ≤ ((2*n).choose n).factorization 3 := by
  by_cases he0 : e = 0
  · subst e; simp
  have hnle : n ≤ 2*n := by omega
  have hb : Nat.log 3 (2*n) < Nat.log 3 (2*n) + 1 := Nat.lt_succ_self _
  rw [Nat.factorization_choose (p:=3) Nat.prime_three hnle hb]
  let S := Ico 1 (e+1)
  have hsub : S ⊆ {i ∈ Ico 1 (Nat.log 3 (2*n) + 1) | 3^i ≤ n % 3^i + (2*n - n) % 3^i} := by
    intro i hiS
    simp only [S, mem_Ico] at hiS
    simp only [mem_filter, mem_Ico]
    have hipos : 0 < 3^i := pow_pos (by norm_num) _
    have hi_le_e : i ≤ e := Nat.le_of_lt_succ hiS.2
    have hpow_dvd : 3^i ∣ 2*n - 1 := (pow_dvd_pow 3 hi_le_e).trans he
    have h2n_eq : ∃ a, 2*n = 3^i * a + 1 := by
      rcases hpow_dvd with ⟨a, ha⟩
      have hposm : 0 < 2*n - 1 := by omega
      use a
      omega
    rcases h2n_eq with ⟨a, ha⟩
    have hlogle : i < Nat.log 3 (2*n) + 1 := by
      have hle : 3^i ≤ 2*n := by
        have hposm : 0 < 2*n - 1 := by omega
        exact (le_of_dvd hposm hpow_dvd).trans (by omega)
      have hlog : i ≤ Nat.log 3 (2*n) := by
        exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 3) (by omega : 2*n ≠ 0)).2 hle
      omega
    constructor
    · exact ⟨hiS.1, hlogle⟩
    · have hsubn : 2*n - n = n := by omega
      rw [hsubn]
      let q := 3^i
      let r := n % q
      let t := n / q
      have hnqr : n = q*t + r := by
        simp [q,t,r]
        exact (Nat.div_add_mod n q).symm
      have hr : r < q := by exact Nat.mod_lt n (by simp [q, hipos])
      have hq2 : 2 ≤ q := by
        have hi1 : 1 ≤ i := hiS.1
        calc 2 ≤ 3 := by norm_num
        _ ≤ 3^i := by exact Nat.le_self_pow (a:=3) (by omega : i ≠ 0)
      have hc := core_carry n q a t r hq2 (by simpa [q] using ha) hnqr hr
      simpa [q,r] using hc
  have hcardS : #S = e := by simp [S]
  calc
    e = #S := hcardS.symm
    _ ≤ #({i ∈ Ico 1 (Nat.log 3 (2*n) + 1) | 3^i ≤ n % 3^i + (2*n - n) % 3^i}) := card_le_card hsub

opaque hfac_three_ineq (n k l e : Nat) (hnpos : 0 < n) (hkl : k + l = n) (he : 3^e ∣ 2*n - 1) :
    e + ((3*n).factorial).factorization 3 + ((3*k).factorial).factorization 3 + ((3*l).factorial).factorization 3 + ((2*k).factorial).factorization 3 + ((2*l).factorial).factorization 3 ≤
      ((6*k).factorial).factorization 3 + ((6*l).factorial).factorization 3 + ((2*n).factorial).factorization 3 := by
  have hc := three_central_factorization n e hnpos he
  -- central choose equation gives e + 2 v(n!) ≤ v((2n)!)
  have hcent_eq : ((2*n).choose n).factorization 3 + (n.factorial).factorization 3 + (n.factorial).factorization 3 = ((2*n).factorial).factorization 3 := by
    have hraw := congrArg (fun x => x.factorization 3) (Nat.choose_mul_factorial_mul_factorial (n:=2*n) (k:=n) (by omega))
    have h : (((2*n).choose n * n.factorial * n.factorial).factorization 3 = ((2*n).factorial).factorization 3) := by simpa [show 2*n-n=n by omega] using hraw
    rw [Nat.factorization_mul (mul_ne_zero (Nat.choose_ne_zero (by omega)) (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero n)] at h
    rw [Nat.factorization_mul (Nat.choose_ne_zero (by omega)) (Nat.factorial_ne_zero n)] at h
    simpa [add_assoc] using h
  have hcent : e + (n.factorial).factorization 3 + (n.factorial).factorization 3 ≤ ((2*n).factorial).factorization 3 := by omega
  have h3n := Nat.factorization_factorial_mul (n:=n) Nat.prime_three
  have h3k := Nat.factorization_factorial_mul (n:=k) Nat.prime_three
  have h3l := Nat.factorization_factorial_mul (n:=l) Nat.prime_three
  have h6k : ((6*k).factorial).factorization 3 = ((2*k).factorial).factorization 3 + 2*k := by simpa [show 3*(2*k)=6*k by ring] using (Nat.factorization_factorial_mul (n:=2*k) Nat.prime_three)
  have h6l : ((6*l).factorial).factorization 3 = ((2*l).factorial).factorization 3 + 2*l := by simpa [show 3*(2*l)=6*l by ring] using (Nat.factorization_factorial_mul (n:=2*l) Nat.prime_three)
  have hklfac : (k.factorial).factorization 3 + (l.factorial).factorization 3 ≤ (n.factorial).factorization 3 := by
    have hdvd : k.factorial * l.factorial ∣ n.factorial := by
      rw [← hkl]
      exact Nat.factorial_mul_factorial_dvd_factorial_add k l
    have hle := @Nat.factorization_le_factorization_of_dvd_right 3 (k.factorial * l.factorial) n.factorial hdvd (mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero l)) (Nat.factorial_ne_zero n)
    simpa [Nat.factorization_mul (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero l), Finsupp.coe_add, Pi.add_apply] using hle
  -- now arithmetic
  omega

opaque T_factorization_eq_test (r p : Nat) :
    (T_term r).factorization p + ((3*r).factorial).factorization p + (r.factorial).factorization p + ((2*r).factorial).factorization p = ((6*r).factorial).factorization p := by
  have h1raw := congrArg Nat.factorization (Nat.choose_mul_factorial_mul_factorial (n:=6*r) (k:=3*r) (by omega : 3*r ≤ 6*r))
  have h1sub : 6*r - 3*r = 3*r := by omega
  have h1 : ((6*r).choose (3*r) * (3*r).factorial * (3*r).factorial).factorization = ((6*r).factorial).factorization := by
    simpa [h1sub] using h1raw
  rw [Nat.factorization_mul (mul_ne_zero (Nat.choose_ne_zero (by omega : 3*r ≤ 6*r)) (Nat.factorial_ne_zero (3*r))) (Nat.factorial_ne_zero (3*r))] at h1
  rw [Nat.factorization_mul (Nat.choose_ne_zero (by omega : 3*r ≤ 6*r)) (Nat.factorial_ne_zero (3*r))] at h1
  have h2raw := congrArg Nat.factorization (Nat.choose_mul_factorial_mul_factorial (n:=3*r) (k:=r) (by omega : r ≤ 3*r))
  have h2sub : 3*r - r = 2*r := by omega
  have h2 : ((3*r).choose r * r.factorial * (2*r).factorial).factorization = ((3*r).factorial).factorization := by
    simpa [h2sub] using h2raw
  rw [Nat.factorization_mul (mul_ne_zero (Nat.choose_ne_zero (by omega : r ≤ 3*r)) (Nat.factorial_ne_zero r)) (Nat.factorial_ne_zero (2*r))] at h2
  rw [Nat.factorization_mul (Nat.choose_ne_zero (by omega : r ≤ 3*r)) (Nat.factorial_ne_zero r)] at h2
  dsimp [T_term]
  rw [Nat.factorization_mul (Nat.choose_ne_zero (by omega : 3*r ≤ 6*r)) (Nat.choose_ne_zero (by omega : r ≤ 3*r))]
  have hh1 := congrArg (fun f => f p) h1
  have hh2 := congrArg (fun f => f p) h2
  simp only [Finsupp.coe_add, Pi.add_apply] at hh1 hh2 ⊢
  omega

opaque D_factorization_eq_test (n p : Nat) (hnpos : 0 < n) :
    ((2*n - 1) * (3*n).choose n).factorization p + (n.factorial).factorization p + ((2*n).factorial).factorization p = (2*n - 1).factorization p + ((3*n).factorial).factorization p := by
  have hm0 : 2*n - 1 ≠ 0 := by omega
  have hraw := congrArg Nat.factorization (Nat.choose_mul_factorial_mul_factorial (n:=3*n) (k:=n) (by omega : n ≤ 3*n))
  have hsub : 3*n - n = 2*n := by omega
  have h : ((3*n).choose n * n.factorial * (2*n).factorial).factorization = ((3*n).factorial).factorization := by
    simpa [hsub] using hraw
  rw [Nat.factorization_mul (mul_ne_zero (Nat.choose_ne_zero (by omega : n ≤ 3*n)) (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero (2*n))] at h
  rw [Nat.factorization_mul (Nat.choose_ne_zero (by omega : n ≤ 3*n)) (Nat.factorial_ne_zero n)] at h
  rw [Nat.factorization_mul hm0 (Nat.choose_ne_zero (by omega : n ≤ 3*n))]
  have hh := congrArg (fun f => f p) h
  simp only [Finsupp.coe_add, Pi.add_apply] at hh ⊢
  omega


opaque term_dvd_a189286 (n k l : Nat) (hnpos : 0 < n) (hkl : k + l = n) :
    (2*n - 1) * (3*n).choose n ∣ T_term k * T_term l := by
  let M := 2*n - 1
  let D := M * (3*n).choose n
  let N := T_term k * T_term l
  have hD0 : D ≠ 0 := by
    exact mul_ne_zero (by dsimp [M]; omega) (Nat.choose_ne_zero (by omega : n ≤ 3*n))
  have hN0 : N ≠ 0 := by
    dsimp [N, T_term]
    exact mul_ne_zero
      (mul_ne_zero (Nat.choose_ne_zero (by omega : 3*k ≤ 6*k)) (Nat.choose_ne_zero (by omega : k ≤ 3*k)))
      (mul_ne_zero (Nat.choose_ne_zero (by omega : 3*l ≤ 6*l)) (Nat.choose_ne_zero (by omega : l ≤ 3*l)))
  rw [← Nat.factorization_le_iff_dvd hD0 hN0]
  intro p
  by_cases hp : p.Prime
  · have hm0 : M ≠ 0 := by dsimp [M]; omega
    have he : p ^ (M.factorization p) ∣ M := by
      exact (hp.pow_dvd_iff_le_factorization hm0).2 le_rfl
    have hfacineq : M.factorization p + ((3*n).factorial).factorization p + ((3*k).factorial).factorization p + ((3*l).factorial).factorization p + ((2*k).factorial).factorization p + ((2*l).factorial).factorization p ≤
        ((6*k).factorial).factorization p + ((6*l).factorial).factorization p + ((2*n).factorial).factorization p := by
      by_cases hp3 : p = 3
      · subst p
        exact hfac_three_ineq n k l (M.factorization 3) hnpos hkl (by simpa [M] using he)
      · exact hfac_non3_ineq n k l p (M.factorization p) hnpos hkl hp hp3 he
    have hD_eq : D.factorization p + (n.factorial).factorization p + ((2*n).factorial).factorization p = M.factorization p + ((3*n).factorial).factorization p := by
      simpa [D, M] using D_factorization_eq_test n p hnpos
    have hTk := T_factorization_eq_test k p
    have hTl := T_factorization_eq_test l p
    have hN_eq : N.factorization p + ((3*k).factorial).factorization p + (k.factorial).factorization p + ((2*k).factorial).factorization p + ((3*l).factorial).factorization p + (l.factorial).factorization p + ((2*l).factorial).factorization p = ((6*k).factorial).factorization p + ((6*l).factorial).factorization p := by
      dsimp [N]
      rw [Nat.factorization_mul (by exact mul_ne_zero (Nat.choose_ne_zero (by omega : 3*k ≤ 6*k)) (Nat.choose_ne_zero (by omega : k ≤ 3*k))) (by exact mul_ne_zero (Nat.choose_ne_zero (by omega : 3*l ≤ 6*l)) (Nat.choose_ne_zero (by omega : l ≤ 3*l)))]
      simp only [Finsupp.coe_add, Pi.add_apply]
      omega
    have hklfac : (k.factorial).factorization p + (l.factorial).factorization p ≤ (n.factorial).factorization p := by
      have hdvd : k.factorial * l.factorial ∣ n.factorial := by
        rw [← hkl]
        exact Nat.factorial_mul_factorial_dvd_factorial_add k l
      have hle := @Nat.factorization_le_factorization_of_dvd_right p (k.factorial * l.factorial) n.factorial hdvd (mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero l)) (Nat.factorial_ne_zero n)
      simpa [Nat.factorization_mul (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero l), Finsupp.coe_add, Pi.add_apply] using hle
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

opaque nat_sum_dvd_a189286 (n : Nat) (hnpos : 0 < n) :
    (2*n - 1) * (3*n).choose n ∣ Finset.sum (range (n + 1)) fun k => T_term k * T_term (n-k) := by
  apply Finset.dvd_sum
  intro k hk
  have hk_le : k ≤ n := by simpa using (Nat.lt_succ_iff.mp (by simpa using hk : k < n+1))
  exact term_dvd_a189286 n k (n-k) hnpos (by omega)


/--
A189286: $a(n):=\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
We define the sequence as an integer sequence, handling $n=0$ explicitly and relying on exact division for $n>0$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if h : n = 0 then
    (-1 : ℤ) -- Explicitly defined a(0)
  else
    let numerator_nat : ℕ := Finset.sum (range (n + 1)) fun k => T_term k * T_term (n - k)

    -- Denominator: (2n - 1) * C(3n, n). The result is known to be an integer.
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)

    (numerator_nat : ℤ) / denominator

/--
Conjecture (Zhi-Wei Sun, Apr 19 2011): a(n) is an integer for every n=0,1,2,....
This conjecture states that $a(n)$ is always the result of an exact division.
Specifically, for all $n>0$, $(2n-1)\binom{3n}{n}$ divides
$\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}$.
-/
theorem oeis_a189286_conjecture_0 (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int :=
by
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : 0 < n := by omega
    have hnat := nat_sum_dvd_a189286 n hnpos
    simp [hn]
    have hden : ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ) = (((2*n - 1) * (3*n).choose n : Nat) : ℤ) := by
      have hsub : (((2*n - 1 : Nat) : ℤ) = (2*n : ℤ) - 1) := by
        rw [Int.natCast_sub (by omega : 1 ≤ 2*n)]
        norm_num
      rw [Nat.cast_mul]
      rw [hsub]
    have hnum : (Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)) =
        ((Finset.sum (range (n + 1)) fun k => T_term k * T_term (n-k) : Nat) : ℤ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      norm_num
    rw [hden, hnum]
    exact Int.natCast_dvd_natCast.mpr hnat
