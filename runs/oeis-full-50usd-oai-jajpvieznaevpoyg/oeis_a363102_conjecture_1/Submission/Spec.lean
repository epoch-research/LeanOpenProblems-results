import FormalConjectures.Util.ProblemImports

open Nat Finset

def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  num / Nat.gcd num denom_arg

def B (n : ℕ) : ℕ := (n^2 - 2) / Nat.gcd (n^2 - 2) 2


lemma two_dvd_sq_iff (n : ℕ) : 2 ∣ n^2 ↔ 2 ∣ n := by
  constructor
  · intro h
    exact Nat.prime_two.dvd_of_dvd_pow h
  · intro h
    exact dvd_pow h (by norm_num)

lemma two_dvd_sq_sub_two_iff {n : ℕ} (hn2 : 2 ≤ n^2) : 2 ∣ n^2 - 2 ↔ 2 ∣ n := by
  rw [← even_iff_two_dvd, ← even_iff_two_dvd]
  rw [Nat.even_sub hn2]
  have hsq : Even (n^2) ↔ Even n := by
    rw [even_iff_two_dvd, even_iff_two_dvd]
    exact two_dvd_sq_iff n
  rw [hsq]
  simp

lemma not_four_dvd_sq_sub_two {n : ℕ} (hn2 : 2 ≤ n^2) : ¬ 4 ∣ n^2 - 2 := by
  intro h
  have hz0 : (((n^2 - 2 : ℕ) : ℤ) : ZMod 4) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  have hz : ((n : ZMod 4)^2 - 2) = 0 := by
    rw [← hz0]
    rw [Nat.cast_sub hn2]
    norm_num
  have hno : ∀ x : ZMod 4, x^2 - 2 ≠ (0 : ZMod 4) := by decide
  exact hno n hz


lemma sum_factorial_even_of_pos {n : ℕ} (hn : 1 ≤ n) : Even (∑ k ∈ range (n+1), k.factorial) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [sum_range_succ]
      cases n with
      | zero => norm_num
      | succ n =>
          have hprev : Even (∑ x ∈ range (Nat.succ n + 1), x.factorial) := ih (by omega)
          have hfac : Even ((Nat.succ (Nat.succ n)).factorial) := by
            rw [even_iff_two_dvd]
            exact Nat.dvd_factorial (by decide) (by omega)
          exact Even.add hprev hfac

lemma even_mul_sum (n : ℕ) : Even ((n+2) * (∑ k ∈ range (n+1), k.factorial)) := by
  cases n with
  | zero => norm_num
  | succ n => exact Even.mul_left (sum_factorial_even_of_pos (n:=Nat.succ n) (by omega)) _

lemma two_mul_a051403 (n : ℕ) :
    2 * a051403 n = (n+2) * (∑ k ∈ range (n+1), k.factorial) := by
  unfold a051403
  rw [Nat.mul_div_cancel' ((even_iff_two_dvd.mp (even_mul_sum n)))]

lemma denom_identity (k : ℕ) :
    2 * (2 * a051403 ((k+4)-3) + (k+4) * a051403 ((k+4)-4)) =
      ((k+4)^2 - 2) * (∑ i ∈ range (((k+4)-4)+1), i.factorial) +
        2 * ((k+4)-1) * (((k+4)-3).factorial) := by
  rw [show (k+4)-3 = k+1 by omega, show (k+4)-4 = k by omega,
    show (k+4)-1 = k+3 by omega]
  have hpoly : (k + 4) ^ 2 - 2 = k ^ 2 + 8 * k + 14 := by
    ring_nf; omega
  rw [hpoly]
  rw [mul_add]
  have hcomm : 2 * ((k + 4) * a051403 k) = (k + 4) * (2 * a051403 k) := by ring
  rw [hcomm]
  rw [two_mul_a051403 (k+1), two_mul_a051403 k]
  rw [sum_range_succ]
  ring_nf

lemma coprime_m_pred (n : ℕ) (hn : 2 ≤ n) : Nat.Coprime (n^2 - 2) (n-1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply Nat.coprime_of_dvd'
  intro p hp hpm hpp
  have hprod : p ∣ ((m+2)-1) * ((m+2)+1) := by
    simpa [add_comm, add_left_comm, add_assoc] using (dvd_mul_of_dvd_left hpp (m+3))
  have hpm' : p ∣ ((m+2)^2 - 2) := by
    simpa [add_comm, add_left_comm, add_assoc] using hpm
  have hdiff : (((m+2)-1)*((m+2)+1)) - ((m+2)^2 - 2) = 1 := by
    have h1 : (m+2)-1 = m+1 := by omega
    rw [h1]
    ring_nf
    omega
  have hone : p ∣ 1 := by
    rw [← hdiff]
    exact Nat.dvd_sub hprod hpm'
  exact hone

lemma a_eq_q (n : ℕ) (hn : 4 ≤ n) :
    a n = B n / Nat.gcd (B n) ((n-3).factorial) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold a B
  rw [show (4+k)-3 = k+1 by omega, show (4+k)-4 = k by omega]
  dsimp
  by_cases hev : 2 ∣ 4+k
  · let M := (4+k)^2 - 2
    let D := 2 * a051403 (k+1) + (4+k) * a051403 k
    let F := (k+1).factorial
    let C := M / 2
    change M / Nat.gcd M D = (M / Nat.gcd M 2) / Nat.gcd (M / Nat.gcd M 2) F
    have hMpos2 : 2 ≤ (4+k)^2 := by nlinarith [sq_pos_of_pos (show 0 < 4+k by omega)]
    have hM2 : 2 ∣ M := by
      unfold M
      rw [two_dvd_sq_sub_two_iff hMpos2]
      simpa [add_comm, add_left_comm, add_assoc] using hev
    have hgcd2 : Nat.gcd M 2 = 2 := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left hM2
    have hM_eq : M = 2 * C := by
      unfold C
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hM2).symm
    have hnot4 : ¬ 4 ∣ M := by
      unfold M
      exact not_four_dvd_sq_sub_two hMpos2
    have hCodd : ¬ 2 ∣ C := by
      intro h2C
      have h4M : 4 ∣ M := by
        rw [hM_eq]
        change 2 * 2 ∣ 2 * C
        exact Nat.mul_dvd_mul_left 2 h2C
      exact hnot4 h4M
    have hcop2C : Nat.Coprime 2 C := (Nat.prime_two.coprime_iff_not_dvd).2 hCodd
    have hD2 : 2 ∣ D := by
      unfold D
      exact dvd_add (dvd_mul_right 2 _) (dvd_mul_of_dvd_left hev _)
    let E := D / 2
    have hD_eq : D = 2 * E := by
      unfold E
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hD2).symm
    have hden0 := denom_identity k
    have hden1 : 2 * D = M * (∑ i ∈ range (((k+4)-4)+1), i.factorial) +
        2 * ((k+4)-1) * (((k+4)-3).factorial) := by
      simpa [D, M, add_comm, add_left_comm, add_assoc] using hden0
    have hden2 : D = C * (∑ i ∈ range (((k+4)-4)+1), i.factorial) + ((k+4)-1) * (((k+4)-3).factorial) := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
      rw [hden1, hM_eq]
      ring
    have hcopPredM : Nat.Coprime M ((4+k)-1) := by
      simpa [M] using coprime_m_pred (4+k) (by omega)
    have hC_dvd_M : C ∣ M := by rw [hM_eq]; exact dvd_mul_left C 2
    have hcopPred : Nat.Coprime C ((4+k)-1) := Nat.Coprime.of_dvd_left hC_dvd_M hcopPredM
    have hcopMul : Nat.Coprime ((4+k)-1) C := hcopPred.symm
    rw [hgcd2]
    change M / Nat.gcd M D = C / Nat.gcd C F
    have hg : Nat.gcd M D = 2 * Nat.gcd C F := by
      calc
        Nat.gcd M D = Nat.gcd (2*C) (2*E) := by rw [← hM_eq, ← hD_eq]
        _ = 2 * Nat.gcd C E := Nat.gcd_mul_left 2 C E
        _ = 2 * Nat.gcd C D := by
          congr 1
          calc
            Nat.gcd C E = Nat.gcd (2*E) C := by
              rw [Nat.gcd_comm]
              exact (hcop2C.gcd_mul_left_cancel E).symm
            _ = Nat.gcd C D := by rw [← hD_eq, Nat.gcd_comm]
        _ = 2 * Nat.gcd C F := by
          congr 1
          calc
            Nat.gcd C D = Nat.gcd C (C * (∑ i ∈ range (((k+4)-4)+1), i.factorial) + ((k+4)-1) * (((k+4)-3).factorial)) := by rw [hden2]
            _ = Nat.gcd C (((k+4)-1) * (((k+4)-3).factorial)) := by
              rw [show C * (∑ i ∈ range (((k+4)-4)+1), i.factorial) + ((k+4)-1) * (((k+4)-3).factorial) = ((k+4)-1) * (((k+4)-3).factorial) + C * (∑ i ∈ range (((k+4)-4)+1), i.factorial) by ring]
              rw [Nat.gcd_add_mul_left_right]
            _ = Nat.gcd C F := by
              rw [show (k+4)-1 = (4+k)-1 by omega, show (k+4)-3 = k+1 by omega]
              change Nat.gcd C (((4+k)-1) * F) = Nat.gcd C F
              rw [Nat.gcd_comm, hcopMul.gcd_mul_left_cancel F, Nat.gcd_comm]
    have hg' : Nat.gcd (2*C) D = 2 * Nat.gcd C F := by simpa [hM_eq] using hg
    rw [hM_eq, hg']
    exact Nat.mul_div_mul_left C (Nat.gcd C F) (by norm_num : 0 < 2)
  · let M := (4+k)^2 - 2
    let D := 2 * a051403 (k+1) + (4+k) * a051403 k
    let F := (k+1).factorial
    change M / Nat.gcd M D = (M / Nat.gcd M 2) / Nat.gcd (M / Nat.gcd M 2) F
    have hMpos2 : 2 ≤ (4+k)^2 := by nlinarith [sq_pos_of_pos (show 0 < 4+k by omega)]
    have hnotM2 : ¬ 2 ∣ M := by
      unfold M
      rw [two_dvd_sq_sub_two_iff hMpos2]
      simpa [add_comm, add_left_comm, add_assoc] using hev
    have hgcd2 : Nat.gcd M 2 = 1 := by
      rw [Nat.gcd_comm]
      exact Nat.coprime_iff_gcd_eq_one.mp ((Nat.prime_two.coprime_iff_not_dvd).2 hnotM2)
    rw [hgcd2]
    simp only [Nat.div_one]
    have hcop2M : Nat.Coprime 2 M := (Nat.prime_two.coprime_iff_not_dvd).2 hnotM2
    have hcopPred : Nat.Coprime M ((4+k)-1) := by
      simpa [M] using coprime_m_pred (4+k) (by omega)
    have hcopMul : Nat.Coprime (2 * ((4+k)-1)) M := by
      exact Nat.Coprime.mul hcop2M hcopPred.symm
    have hden0 := denom_identity k
    have hden : 2 * D = M * (∑ i ∈ range (((k+4)-4)+1), i.factorial) +
        2 * ((k+4)-1) * (((k+4)-3).factorial) := by
      simpa [D, M, add_comm, add_left_comm, add_assoc] using hden0
    have hg : Nat.gcd M D = Nat.gcd M F := by
      calc
        Nat.gcd M D = Nat.gcd (2 * D) M := by
          rw [Nat.gcd_comm]
          exact (hcop2M.gcd_mul_left_cancel D).symm
        _ = Nat.gcd M (2 * D) := Nat.gcd_comm _ _
        _ = Nat.gcd M (M * (∑ i ∈ range (((k+4)-4)+1), i.factorial) + 2 * ((k+4)-1) * (((k+4)-3).factorial)) := by
          rw [hden]
        _ = Nat.gcd M (2 * ((k+4)-1) * (((k+4)-3).factorial)) := by
          rw [show M * (∑ i ∈ range (((k+4)-4)+1), i.factorial) + 2 * ((k+4)-1) * (((k+4)-3).factorial) = 2 * ((k+4)-1) * (((k+4)-3).factorial) + M * (∑ i ∈ range (((k+4)-4)+1), i.factorial) by ring]
          rw [Nat.gcd_add_mul_left_right]
        _ = Nat.gcd M F := by
          rw [show (k+4)-1 = (4+k)-1 by omega, show (k+4)-3 = k+1 by omega]
          change Nat.gcd M ((2 * ((4+k)-1)) * F) = Nat.gcd M F
          rw [Nat.gcd_comm, hcopMul.gcd_mul_left_cancel F, Nat.gcd_comm]
    rw [hg]

-- copy valuation helpers from ValBound
lemma pow_bound {p k : ℕ} (hp : 7 ≤ p) (hk : 1 ≤ k) : ((k+1)*p+2)^2 < p^(k+2) := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          norm_num
          have h1 : (2 * p + 2)^2 ≤ 6 * p^2 := by nlinarith
          have h2 : 6 * p^2 < 7 * p^2 := by nlinarith [sq_pos_of_pos (show 0 < p by omega)]
          have h3 : 7 * p^2 ≤ p^3 := by nlinarith [sq_nonneg (p:ℤ)]
          norm_num at *
          nlinarith
      | succ k =>
          have ih' := ih (by omega)
          have step : (((Nat.succ (Nat.succ k))+1)*p+2)^2 < p * ((((Nat.succ k)+1)*p+2)^2) := by
            nlinarith [sq_nonneg (((Nat.succ k)+1)*p+2 : ℤ), sq_nonneg (p:ℤ), sq_nonneg (k:ℤ)]
          have hmul : p * ((((Nat.succ k)+1)*p+2)^2) < p * p^((Nat.succ k)+2) := by
            exact Nat.mul_lt_mul_of_pos_left ih' (by omega)
          calc
            (((Nat.succ (Nat.succ k))+1)*p+2)^2 < p * ((((Nat.succ k)+1)*p+2)^2) := step
            _ < p * p^((Nat.succ k)+2) := hmul
            _ = p^((Nat.succ (Nat.succ k))+2) := by
              simp [pow_succ]
              ring

lemma factorial_factorization_ge_div {N p : ℕ} (hp : Nat.Prime p) (hN : 0 < N) : N / p ≤ (N.factorial).factorization p := by
  have hlog : Nat.log p N < N + 1 := lt_trans (Nat.log_lt_self p (Nat.ne_of_gt hN)) (Nat.lt_succ_self N)
  rw [Nat.factorization_factorial hp hlog]
  have hs : N / p ^ 1 ≤ ∑ i ∈ Finset.Ico 1 (N + 1), N / p ^ i := by
    refine Finset.single_le_sum (s := Finset.Ico 1 (N + 1)) (f := fun i => N / p ^ i)
      (fun i hi => Nat.zero_le _) ?_
    simp [hN]
  simpa using hs

lemma quotient_prime_aux {n B : ℕ} (hn : 5 ≤ n) (hBpos : 0 < B) (hBlt : B < n^2)
    (hprime_ge7 : ∀ p, Nat.Prime p → p ∣ B → 7 ≤ p)
    (hsmall : ∀ p, Nat.Prime p → p ∣ B → p < n → p ≤ n - 3) :
    B / Nat.gcd B ((n-3).factorial) = 1 ∨ Nat.Prime (B / Nat.gcd B ((n-3).factorial)) := by
  let F := (n-3).factorial
  let g := Nat.gcd B F
  let Q := B / g
  have hg_dvd_B : g ∣ B := by exact Nat.gcd_dvd_left B F
  have hg_dvd_F : g ∣ F := by exact Nat.gcd_dvd_right B F
  have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hg_dvd_B hBpos
  have hQ_dvd_B : Q ∣ B := by unfold Q; exact Nat.div_dvd_of_dvd hg_dvd_B
  have hB_eq : B = g * Q := by
    unfold Q
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel hg_dvd_B).symm
  by_cases hQ1 : Q = 1
  · left
    simpa [Q, g, F] using hQ1
  · right
    have hQpos : 0 < Q := by
      unfold Q
      exact Nat.div_pos (Nat.le_of_dvd hBpos hg_dvd_B) hg_pos
    have hQne0 : Q ≠ 0 := Nat.ne_of_gt hQpos
    by_contra hQprime
    have hQ2 : 2 ≤ Q := by omega
    let p := Nat.minFac Q
    have hp : Nat.Prime p := Nat.minFac_prime hQ1
    have hp_dvd_Q : p ∣ Q := Nat.minFac_dvd Q
    have hp_dvd_B : p ∣ B := dvd_trans hp_dvd_Q hQ_dvd_B
    have hp7 : 7 ≤ p := hprime_ge7 p hp hp_dvd_B
    have hp2Q : p ^ 2 ≤ Q := Nat.minFac_sq_le_self hQpos hQprime
    by_cases hple : p ≤ n - 3
    · let k := (n - 3) / p
      have hk : 1 ≤ k := by
        unfold k
        exact (Nat.one_le_div_iff (by omega)).2 hple
      have hlog : k ≤ F.factorization p := by
        unfold k F
        exact factorial_factorization_ge_div hp (by omega)
      have hQfac_pos : 1 ≤ Q.factorization p := (hp.dvd_iff_one_le_factorization hQne0).mp hp_dvd_Q
      have hfacQ : Q.factorization = B.factorization - g.factorization := Nat.factorization_div hg_dvd_B
      have hgf_lt_Bf : g.factorization p < B.factorization p := by
        have := hQfac_pos
        rw [hfacQ] at this
        exact Nat.lt_of_sub_pos this
      have hgfac_eq_min : g.factorization p = min (B.factorization p) (F.factorization p) := by
        have hfg := Nat.factorization_gcd (Nat.ne_of_gt hBpos) (Nat.factorial_ne_zero (n-3))
        change (Nat.gcd B F).factorization p = _
        rw [hfg]
        rfl
      have hgf_eq_Ff : g.factorization p = F.factorization p := by
        rw [hgfac_eq_min]
        by_cases hFB : F.factorization p ≤ B.factorization p
        · exact min_eq_right hFB
        · have hBF : B.factorization p ≤ F.factorization p := le_of_lt (Nat.lt_of_not_ge hFB)
          have : min (B.factorization p) (F.factorization p) = B.factorization p := min_eq_left hBF
          omega
      have hk_g : k ≤ g.factorization p := by omega
      have hpk_dvd_g : p ^ k ∣ g := (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hg_pos)).2 hk_g
      have hpk_le_g : p ^ k ≤ g := Nat.le_of_dvd hg_pos hpk_dvd_g
      have hlower : p ^ (k+2) ≤ B := by
        calc
          p ^ (k+2) = p^k * p^2 := by rw [pow_add]
          _ ≤ g * Q := Nat.mul_le_mul hpk_le_g hp2Q
          _ = B := by rw [← hB_eq]
      have hNlt : n ≤ (k+1)*p + 2 := by
        have hlt : n - 3 < (k+1)*p := by
          unfold k
          exact Nat.lt_mul_of_div_lt (by omega) (by omega)
        omega
      have hupper : B < p ^ (k+2) := by
        have hb := pow_bound hp7 hk
        have hn2 : n^2 ≤ ((k+1)*p+2)^2 := by nlinarith
        nlinarith
      exact (not_lt_of_ge hlower) hupper
    · have hpge_n : n ≤ p := by
        by_contra hpn
        have hplt : p < n := by omega
        have := hsmall p hp hp_dvd_B hplt
        omega
      have hlower : n^2 ≤ B := by
        calc
          n^2 ≤ p^2 := by nlinarith
          _ ≤ Q := hp2Q
          _ ≤ B := Nat.le_of_dvd hBpos hQ_dvd_B
      exact (not_lt_of_ge hlower) hBlt

lemma not_three_dvd_sq_sub_two {n : ℕ} (hn2 : 2 ≤ n^2) : ¬ 3 ∣ n^2 - 2 := by
  intro h
  have hz0 : (((n^2 - 2 : ℕ) : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  have hz : ((n : ZMod 3)^2 - 2) = 0 := by
    rw [← hz0]
    rw [Nat.cast_sub hn2]
    norm_num
  have hno : ∀ x : ZMod 3, x^2 ≠ (2:ZMod 3) := by decide
  exact hno n (sub_eq_zero.mp hz)

lemma not_five_dvd_sq_sub_two {n : ℕ} (hn2 : 2 ≤ n^2) : ¬ 5 ∣ n^2 - 2 := by
  intro h
  have hz0 : (((n^2 - 2 : ℕ) : ℤ) : ZMod 5) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  have hz : ((n : ZMod 5)^2 - 2) = 0 := by
    rw [← hz0]
    rw [Nat.cast_sub hn2]
    norm_num
  have hno : ∀ x : ZMod 5, x^2 ≠ (2:ZMod 5) := by decide
  exact hno n (sub_eq_zero.mp hz)

lemma B_dvd_M (n : ℕ) : B n ∣ n^2 - 2 := by
  unfold B
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (n^2 - 2) 2)

lemma B_pos {n : ℕ} (hn : 5 ≤ n) : 0 < B n := by
  unfold B
  have hMpos : 0 < n^2 - 2 := by
    have hlt : 2 < n^2 := by nlinarith [sq_pos_of_pos (show 0 < n by omega)]
    exact Nat.sub_pos_of_lt hlt
  exact Nat.div_pos (Nat.le_of_dvd hMpos (Nat.gcd_dvd_left (n^2 - 2) 2)) (Nat.gcd_pos_of_pos_left 2 hMpos)

lemma B_lt_sq {n : ℕ} (hn : 5 ≤ n) : B n < n^2 := by
  have hMlt : n^2 - 2 < n^2 := by
    have hpos : 0 < n^2 := by nlinarith [sq_pos_of_pos (show 0 < n by omega)]
    exact Nat.sub_lt hpos (by norm_num)
  calc
    B n ≤ n^2 - 2 := by unfold B; exact Nat.div_le_self _ _
    _ < n^2 := hMlt

lemma not_two_dvd_B {n : ℕ} (hn : 5 ≤ n) : ¬ 2 ∣ B n := by
  intro h2B
  let M := n^2 - 2
  have hn2 : 2 ≤ n^2 := by nlinarith [sq_pos_of_pos (show 0 < n by omega)]
  have hnot4 : ¬ 4 ∣ M := by
    unfold M
    exact not_four_dvd_sq_sub_two hn2
  by_cases h2M : 2 ∣ M
  · have hg : Nat.gcd M 2 = 2 := by rw [Nat.gcd_comm]; exact Nat.gcd_eq_left h2M
    have hM_eq : M = 2 * B n := by
      unfold B M
      rw [hg]
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel h2M).symm
    have h4M : 4 ∣ M := by
      rw [hM_eq]
      change 2 * 2 ∣ 2 * B n
      exact Nat.mul_dvd_mul_left 2 h2B
    exact hnot4 h4M
  · have hg : Nat.gcd M 2 = 1 := by
      rw [Nat.gcd_comm]
      exact Nat.coprime_iff_gcd_eq_one.mp ((Nat.prime_two.coprime_iff_not_dvd).2 h2M)
    have hBM : B n = M := by unfold B M; rw [hg, Nat.div_one]
    exact h2M (by simpa [hBM] using h2B)

lemma prime_dvd_B_ge7 {n p : ℕ} (hn : 5 ≤ n) (hp : Nat.Prime p) (hpd : p ∣ B n) : 7 ≤ p := by
  have hn2 : 2 ≤ n^2 := by nlinarith [sq_pos_of_pos (show 0 < n by omega)]
  have hpM : p ∣ n^2 - 2 := dvd_trans hpd (B_dvd_M n)
  have hp_ne2 : p ≠ 2 := by
    intro h; subst h
    exact not_two_dvd_B hn hpd
  have hp_ne3 : p ≠ 3 := by
    intro h; subst h
    exact not_three_dvd_sq_sub_two hn2 hpM
  have hp_ne5 : p ≠ 5 := by
    intro h; subst h
    exact not_five_dvd_sq_sub_two hn2 hpM
  by_contra hlt
  have hp_lt : p < 7 := by omega
  have hp2le : 2 ≤ p := hp.two_le
  interval_cases p
  all_goals try omega
  all_goals norm_num at hp

lemma prime_dvd_B_small {n p : ℕ} (hn : 5 ≤ n) (hp : Nat.Prime p) (hpd : p ∣ B n) (hpn : p < n) : p ≤ n - 3 := by
  have hpM : p ∣ n^2 - 2 := dvd_trans hpd (B_dvd_M n)
  have hp7 : 7 ≤ p := prime_dvd_B_ge7 hn hp hpd
  by_contra hle
  have hcases : p = n - 2 ∨ p = n - 1 := by omega
  rcases hcases with hp2 | hp1
  · have hpdiff : p ∣ n - 2 := by rw [hp2]
    have hprod : p ∣ (n-2) * (n+2) := dvd_mul_of_dvd_left hpdiff _
    have hdiff : (n^2 - 2) - ((n-2)*(n+2)) = 2 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      have h1 : 5 + m - 2 = m + 3 := by omega
      rw [h1]
      ring_nf
      omega
    have hp2dvd : p ∣ 2 := by
      rw [← hdiff]
      exact Nat.dvd_sub hpM hprod
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2dvd
    omega
  · have hpdiff : p ∣ n - 1 := by rw [hp1]
    have hc := coprime_m_pred n (by omega)
    have hg : Nat.gcd (n^2 - 2) (n-1) = 1 := Nat.coprime_iff_gcd_eq_one.mp hc
    have hpone : p ∣ 1 := by
      rw [← hg]
      exact Nat.dvd_gcd hpM hpdiff
    have : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpone
    omega

/-- A363102 Conjecture 1: The sequence contains only 1's and primes. -/
theorem oeis_a363102_conjecture_1 :
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := by
  intro n hn3
  by_cases hn5 : 5 ≤ n
  · rw [a_eq_q n (by omega)]
    exact quotient_prime_aux hn5 (B_pos hn5) (B_lt_sq hn5)
      (fun p hp hpd => prime_dvd_B_ge7 hn5 hp hpd)
      (fun p hp hpd hpn => prime_dvd_B_small hn5 hp hpd hpn)
  · have hn_cases : n = 3 ∨ n = 4 := by omega
    rcases hn_cases with rfl | rfl <;> decide
