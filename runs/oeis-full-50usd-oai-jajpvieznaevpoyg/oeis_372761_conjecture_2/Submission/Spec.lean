import FormalConjectures.Util.ProblemImports

open Rat

/--
Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.
-/
noncomputable def continued_fraction_tail (n : ℕ) : ℕ → ℚ
| k =>
  if n ≥ 4 then
    if k = n - 1 then
      (n - 1 : ℚ) - (n : ℚ) / (n + 4 : ℚ)
    else if 3 ≤ k ∧ k < n - 1 then
      let k_succ_val := continued_fraction_tail n (k + 1)
      -- Division by zero handling for total function definition
      if k_succ_val = 0 then 0 else
        (k : ℚ) - (k + 1 : ℚ) / k_succ_val
    else
      0
  else
    0
termination_by k => n - k

/--
The total value of the continued fraction $C_n$.
-/
noncomputable def continued_fraction_val (n : ℕ) : ℚ :=
  if n ≤ 2 then
    0
  else if n = 3 then
    -- Formula for n=3: 1 / (2 - 3 / (3 + 4)) = 7/11
    let val : ℚ := 2 - 3 / 7
    if val = 0 then 0 else 1 / val
  else -- n ≥ 4
    let A3 := continued_fraction_tail n 3
    let val : ℚ := 2 - 3 / A3

    -- Division by zero check for the final rational value
    if val = 0 then 0 else 1 / val

/--
A372761: Denominator of the continued fraction
$$ \frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (continued_fraction_val n).den

def Pcont (n : ℕ) : ℕ → ℤ
| k =>
  if k = n then (n + 4 : ℤ)
  else if k = n - 1 then ((n:ℤ)^2 + 2*(n:ℤ) - 4)
  else if 3 ≤ k ∧ k < n - 1 then
    (k:ℤ) * Pcont n (k+1) - (k+1:ℤ) * Pcont n (k+2)
  else 0
termination_by k => n - k

def Lfun (n k : ℕ) : ℤ := ((k-1:ℕ):ℤ) * Pcont n k - (k:ℤ) * ((k-2:ℕ):ℤ) * Pcont n (k+1)

lemma lin_inv_step {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n - 1) :
    Pcont n k = (k:ℤ) * Pcont n (k+1) - (k+1:ℤ) * Pcont n (k+2) := by
  rw [Pcont]
  have hknn : k ≠ n := by omega
  have hkn1 : k ≠ n - 1 := by omega
  simp [hknn, hkn1, hk, hkn]

lemma L_step {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n - 1) :
    Lfun n k = Lfun n (k+1) := by
  rw [Lfun, Lfun, lin_inv_step hk hkn]
  have hk1 : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
  have hk2 : ((k - 2 : ℕ) : ℤ) = (k:ℤ) - 2 := by omega
  have hk1p : (((k+1) - 1 : ℕ) : ℤ) = (k:ℤ) := by omega
  have hk2p : (((k+1) - 2 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
  norm_num [hk1, hk2, hk1p, hk2p]
  ring_nf

lemma Pcont_at_n {n : ℕ} : Pcont n n = (n+4:ℤ) := by
  rw [Pcont]
  simp

lemma Pcont_at_pred {n : ℕ} (hn : 1 ≤ n) :
    Pcont n (n-1) = ((n:ℤ)^2 + 2*(n:ℤ) - 4) := by
  rw [Pcont]
  have h1 : n - 1 ≠ n := by omega
  simp [h1]

lemma L_boundary {n : ℕ} (hn : 4 ≤ n) : Lfun n (n-1) = (5*(n:ℤ)-4) := by
  rw [Lfun]
  rw [Pcont_at_pred (by omega : 1 ≤ n)]
  have hsucc : (n - 1) + 1 = n := by omega
  rw [hsucc, Pcont_at_n]
  have hn0 : ((n - 1 : ℕ):ℤ) = (n:ℤ)-1 := by omega
  have hn1 : (((n - 1) - 1 : ℕ):ℤ) = (n:ℤ)-2 := by omega
  have hn2 : (((n - 1) - 2 : ℕ):ℤ) = (n:ℤ)-3 := by omega
  norm_num [hn0, hn1, hn2]
  ring_nf

lemma L_eq_q (n k : ℕ) (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n - 1) :
    Lfun n k = (5*(n:ℤ)-4) := by
  by_cases h : k = n - 1
  · subst h
    exact L_boundary hn
  · have hklt : k < n - 1 := by omega
    rw [L_step hk hklt]
    exact L_eq_q n (k+1) hn (by omega) (by omega)
termination_by n - 1 - k

lemma L_eq_q_three (n : ℕ) (hn : 4 ≤ n) :
    2 * Pcont n 3 - 3 * Pcont n 4 = (5*(n:ℤ)-4) := by
  have h := L_eq_q n 3 hn (by omega) (by omega)
  simpa [Lfun] using h

lemma Pcont_pos (n k : ℕ) (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) :
    0 < Pcont n k := by
  by_cases h : k = n
  · subst h
    rw [Pcont_at_n]
    omega
  · have hkle : k ≤ n - 1 := by omega
    have ih : 0 < Pcont n (k+1) := Pcont_pos n (k+1) hn (by omega) (by omega)
    have hL := L_eq_q n k hn hk hkle
    have qpos : 0 < (5*(n:ℤ)-4) := by omega
    have cpos : 0 < ((k - 1 : ℕ) : ℤ) := by omega
    have knonneg : 0 ≤ (k:ℤ) * ((k - 2 : ℕ):ℤ) * Pcont n (k+1) := by positivity
    rw [Lfun] at hL
    nlinarith
termination_by n - k

lemma tail_eq_P (n k : ℕ) (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n - 1) :
    continued_fraction_tail n k = (Pcont n k) /. (Pcont n (k+1)) := by
  by_cases h : k = n - 1
  · subst h
    rw [continued_fraction_tail]
    have hn4 : n ≥ 4 := hn
    have hp : Pcont n (n-1) = ((n:ℤ)^2+2*(n:ℤ)-4) := Pcont_at_pred (by omega : 1 ≤ n)
    have hsucc : (n - 1) + 1 = n := by omega
    rw [hp, hsucc, Pcont_at_n]
    simp [hn4]
    rw [Rat.divInt_eq_div]
    field_simp
    norm_num
    ring_nf
  · have hklt : k < n - 1 := by omega
    rw [continued_fraction_tail]
    have hn4 : n ≥ 4 := hn
    have hkn1 : k ≠ n - 1 := h
    have hrec := tail_eq_P n (k+1) hn (by omega) (by omega)
    have hpos : 0 < Pcont n (k+1) := Pcont_pos n (k+1) hn (by omega) (by omega)
    have hratio_ne : (Pcont n (k+1) /. Pcont n (k+2)) ≠ 0 := by
      apply Rat.divInt_ne_zero_of_ne_zero
      · exact ne_of_gt hpos
      · exact ne_of_gt (Pcont_pos n (k+2) hn (by omega) (by omega))
    have hpstep := lin_inv_step hk hklt
    simp [hn4, hkn1, hk, hklt, hrec, hratio_ne]
    rw [hpstep]
    rw [Rat.divInt_eq_div] at hratio_ne ⊢
    have hA : ((Pcont n (k+1) : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hpos)
    have hA1 : ((Pcont n (1+k) : ℚ) ≠ 0) := by simpa [Nat.add_comm] using hA
    field_simp [hratio_ne, hA, hA1]
    try rw [Rat.divInt_eq_div]
    field_simp [hA1]
    all_goals try norm_num
    all_goals try ring_nf
termination_by n - 1 - k

lemma val_eq_P (n : ℕ) (hn : 4 ≤ n) :
    continued_fraction_val n = Pcont n 3 /. (5*(n:ℤ)-4) := by
  rw [continued_fraction_val]
  have hnle2 : ¬ n ≤ 2 := by omega
  have hnne3 : n ≠ 3 := by omega
  have htail := tail_eq_P n 3 hn (by omega) (by omega)
  have hP3 : 0 < Pcont n 3 := Pcont_pos n 3 hn (by omega) (by omega)
  have hP4 : 0 < Pcont n 4 := Pcont_pos n 4 hn (by omega) (by omega)
  have htail_ne : Pcont n 3 /. Pcont n 4 ≠ 0 := by
    apply Rat.divInt_ne_zero_of_ne_zero <;> exact ne_of_gt (by assumption)
  have hden := L_eq_q_three n hn
  have hval_ne : (2:ℚ) - 3 / (Pcont n 3 /. Pcont n 4) ≠ 0 := by
    rw [Rat.divInt_eq_div]
    have h3 : ((Pcont n 3 : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hP3)
    have h4 : ((Pcont n 4 : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hP4)
    field_simp [h3, h4]
    rw [show (2:ℚ) * ↑(Pcont n 3) - 3 * ↑(Pcont n 4) = ((2 * Pcont n 3 - 3 * Pcont n 4 : ℤ) : ℚ) by norm_num]
    rw [hden]
    have qpos : 0 < (5*(n:ℤ)-4) := by omega
    rw [← Rat.divInt_eq_div]
    apply Rat.divInt_ne_zero_of_ne_zero
    · exact ne_of_gt qpos
    · exact ne_of_gt hP3
  simp [hnle2, hnne3, htail, hval_ne]
  rw [Rat.divInt_eq_div]
  rw [Rat.divInt_eq_div] at htail_ne ⊢
  have h3 : ((Pcont n 3 : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hP3)
  have h4 : ((Pcont n 4 : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hP4)
  field_simp [h3, h4]
  have hdenQ : (2 * ↑(Pcont n 3) - 3 * ↑(Pcont n 4) : ℚ) = ↑(5*(n:ℤ)-4) := by exact_mod_cast hden
  rw [hdenQ]


def Iprod (k n : ℕ) : ℤ := ((Finset.Icc k n).prod (fun j => (j:ℤ)))

lemma Pcont_mod_prod (n k : ℕ) (hn : 4 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) :
    Pcont n k ≡ ((5*((n-k:ℕ):ℤ)+6) * Iprod k n) [ZMOD (5*(n:ℤ)-4)] := by
  by_cases hk_n : k = n
  · subst hk_n
    rw [Pcont_at_n, Iprod]
    simp
    rw [Int.modEq_iff_dvd]
    use 1
    ring
  · by_cases hk_pred : k = n - 1
    · subst hk_pred
      rw [Pcont_at_pred (by omega : 1 ≤ n), Iprod]
      have hI : (Finset.Icc (n - 1) n).prod (fun j => (j:ℤ)) = ((n-1:ℕ):ℤ) * (n:ℤ) := by
        have hsucc : n - 1 + 1 = n := by omega
        rw [← hsucc]
        rw [Finset.prod_Icc_succ_top]
        · simp [Iprod]
        · omega
      rw [hI]
      rw [Int.modEq_iff_dvd]
      use (2*(n:ℤ)-1)
      have hn1 : ((n - 1 : ℕ):ℤ) = (n:ℤ)-1 := by omega
      have hnsub : ((n - (n - 1) : ℕ):ℤ) = 1 := by omega
      rw [hn1, hnsub]
      ring
    · have hklt : k < n - 1 := by omega
      have hstep := lin_inv_step hk hklt
      rw [hstep]
      have ih1 := Pcont_mod_prod n (k+1) hn (by omega) (by omega)
      have ih2 := Pcont_mod_prod n (k+2) hn (by omega) (by omega)
      have hmod : (k:ℤ) * Pcont n (k+1) - (k+1:ℤ) * Pcont n (k+2) ≡
          (k:ℤ) * ((5*((n-(k+1):ℕ):ℤ)+6) * Iprod (k+1) n) -
            (k+1:ℤ) * ((5*((n-(k+2):ℕ):ℤ)+6) * Iprod (k+2) n)
          [ZMOD (5*(n:ℤ)-4)] := by
        exact Int.ModEq.sub (Int.ModEq.mul (Int.ModEq.refl _) ih1)
          (Int.ModEq.mul (Int.ModEq.refl _) ih2)
      refine hmod.trans ?_
      simp only [Iprod]
      have hprod1 : (Finset.Icc k n).prod (fun j => (j:ℤ)) =
          (k:ℤ) * (Finset.Icc (k+1) n).prod (fun j => (j:ℤ)) := by
        rw [Finset.Icc_eq_cons_Ioc (by omega : k ≤ n)]
        have hIoc : Finset.Ioc k n = Finset.Icc (k+1) n := by ext x; simp
        simp [hIoc]
      have hprod2 : (Finset.Icc (k+1) n).prod (fun j => (j:ℤ)) =
          ((k+1:ℕ):ℤ) * (Finset.Icc (k+2) n).prod (fun j => (j:ℤ)) := by
        rw [Finset.Icc_eq_cons_Ioc (by omega : k+1 ≤ n)]
        have hIoc : Finset.Ioc (k+1) n = Finset.Icc (k+2) n := by ext x; simp; omega
        simp [hIoc]
      rw [hprod1, hprod2]
      rw [Int.modEq_iff_dvd]
      use (((k+1:ℕ):ℤ) * ((Finset.Icc (k+2) n).prod (fun j => (j:ℤ))))
      have hnk1 : ((n - (k + 1) : ℕ):ℤ) = (n:ℤ) - (k:ℤ) - 1 := by omega
      have hnk2 : ((n - (k + 2) : ℕ):ℤ) = (n:ℤ) - (k:ℤ) - 2 := by omega
      have hnk : ((n - k : ℕ):ℤ) = (n:ℤ) - (k:ℤ) := by omega
      have hk1cast : (((k+1):ℕ):ℤ) = (k:ℤ)+1 := by omega
      rw [hnk1, hnk2, hnk, hk1cast]
      ring_nf
termination_by n - k

lemma den_shape (n : ℕ) (hn : 4 ≤ n) :
    a n = (5*n - 4) / (Int.gcd (5*(n:ℤ)-4) (Pcont n 3)) := by
  have hv := val_eq_P n hn
  rw [a]
  have hnlt : ¬ n < 3 := by omega
  simp [hnlt, hv]
  rw [Rat.den_divInt]
  have hqne : (5*(n:ℤ)-4) ≠ 0 := by omega
  simp [hqne]
  have habs : (5*(n:ℤ)-4).natAbs = 5*n - 4 := by omega
  rw [habs]

def Bprod (n : ℕ) : ℕ := (Finset.Icc 3 n).prod (fun j => j)
def qnat (n : ℕ) : ℕ := 5*n - 4
def mnat (n : ℕ) : ℕ := 5*n - 9

lemma q_m_coprime (n:ℕ) (hn:4≤n) : (qnat n).Coprime (mnat n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  unfold qnat mnat
  have h1 : 5*n - 4 = 5 + (5*n - 9) := by omega
  rw [h1]
  rw [Nat.gcd_add_self_left]
  have hmod : (5*n - 9) % 5 = 1 := by omega
  rw [Nat.gcd_rec]
  rw [hmod]
  norm_num

lemma Iprod_eq_B (n : ℕ) : Iprod 3 n = (Bprod n : ℤ) := by
  unfold Iprod Bprod
  norm_num

lemma P_gcd_eq_B_gcd (n : ℕ) (hn : 4 ≤ n) :
    Int.gcd (5*(n:ℤ)-4) (Pcont n 3) = Nat.gcd (qnat n) (Bprod n) := by
  apply Nat.dvd_antisymm
  · rw [Nat.dvd_gcd_iff]
    constructor
    · have hz := Int.gcd_dvd_left (5*(n:ℤ)-4) (Pcont n 3)
      have hQcast : ((qnat n : ℤ) = 5*(n:ℤ)-4) := by unfold qnat; omega
      exact Int.ofNat_dvd.mp (by simpa [hQcast] using hz)
    · let D := Int.gcd (5*(n:ℤ)-4) (Pcont n 3)
      have hDq : D ∣ qnat n := by
        have hz := Int.gcd_dvd_left (5*(n:ℤ)-4) (Pcont n 3)
        have hQcast : ((qnat n : ℤ) = 5*(n:ℤ)-4) := by unfold qnat; omega
        exact Int.ofNat_dvd.mp (by simpa [hQcast] using hz)
      have hDP : (D:ℤ) ∣ Pcont n 3 := Int.gcd_dvd_right _ _
      have hmod := Pcont_mod_prod n 3 hn (by omega) (by omega)
      have hDqZ : (D:ℤ) ∣ (5*(n:ℤ)-4) := Int.gcd_dvd_left _ _
      have hmodD := Int.ModEq.of_dvd hDqZ hmod
      have hDmulZ : (D:ℤ) ∣ ((5*((n-3:ℕ):ℤ)+6) * Iprod 3 n) := by
        rw [← hmodD.dvd_iff]
        exact hDP
      have hm_eq : (5*((n-3:ℕ):ℤ)+6) = (mnat n : ℤ) := by
        unfold mnat; omega
      rw [hm_eq, Iprod_eq_B] at hDmulZ
      have hDmul : D ∣ mnat n * Bprod n := by exact_mod_cast hDmulZ
      have hcop : D.Coprime (mnat n) := Nat.Coprime.coprime_dvd_left hDq (q_m_coprime n hn)
      exact hcop.dvd_of_dvd_mul_left hDmul
  · let D := Nat.gcd (qnat n) (Bprod n)
    have hDq : D ∣ qnat n := Nat.gcd_dvd_left _ _
    have hDB : D ∣ Bprod n := Nat.gcd_dvd_right _ _
    have hmod := Pcont_mod_prod n 3 hn (by omega) (by omega)
    have hDqZ : (D:ℤ) ∣ (5*(n:ℤ)-4) := by
      have hQcast : ((qnat n : ℤ) = 5*(n:ℤ)-4) := by unfold qnat; omega
      exact (by simpa [hQcast] using (Int.ofNat_dvd.mpr hDq) : (D:ℤ) ∣ (5*(n:ℤ)-4))
    have hmodD := Int.ModEq.of_dvd hDqZ hmod
    have hDmulZ : (D:ℤ) ∣ ((5*((n-3:ℕ):ℤ)+6) * Iprod 3 n) := by
      rw [Iprod_eq_B]
      exact dvd_mul_of_dvd_right (by exact_mod_cast hDB : (D:ℤ) ∣ (Bprod n : ℤ)) _
    have hDP : (D:ℤ) ∣ Pcont n 3 := by
      rw [hmodD.dvd_iff]
      exact hDmulZ
    exact Int.dvd_gcd hDqZ hDP

lemma a_formula_ge4 (n : ℕ) (hn : 4 ≤ n) :
    a n = qnat n / Nat.gcd (qnat n) (Bprod n) := by
  rw [den_shape n hn, P_gcd_eq_B_gcd n hn]
  rfl

lemma a_three : a 3 = 11 := by
  rw [a, continued_fraction_val]
  norm_num

lemma prime_not_dvd_Bprod {p n : ℕ} (hp : Nat.Prime p) (hpn : n < p) :
    ¬ p ∣ Bprod n := by
  unfold Bprod
  exact hp.prime.not_dvd_finset_prod (fun j hj hd => by
    have hjle : j ≤ n := by simpa using (Finset.mem_Icc.mp hj).2
    have hjlt : j < p := lt_of_le_of_lt hjle hpn
    have hjpos : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hp_le_j := Nat.le_of_dvd hjpos hd
    omega)

lemma gcd_cp_B_eq_c {c p n : ℕ} (hp : Nat.Prime p) (hcB : c ∣ Bprod n)
    (hpB : ¬ p ∣ Bprod n) : Nat.gcd (c*p) (Bprod n) = c := by
  apply Nat.dvd_antisymm
  · let G := Nat.gcd (c*p) (Bprod n)
    have hGdvd : G ∣ c*p := Nat.gcd_dvd_left _ _
    have hnot : ¬ p ∣ G := by
      intro h
      exact hpB (h.trans (Nat.gcd_dvd_right _ _))
    have hcop : G.Coprime p := ((hp.coprime_iff_not_dvd).mpr hnot).symm
    exact hcop.dvd_of_dvd_mul_right hGdvd
  · exact Nat.dvd_gcd (Nat.dvd_mul_right c p) hcB

lemma a_eq_prime_of_q_eq_cp {n p c : ℕ} (hn : 4 ≤ n) (hp : Nat.Prime p)
    (hpn : n < p) (hcpos : 0 < c) (hcB : c ∣ Bprod n) (hq : qnat n = c*p) :
    a n = p := by
  rw [a_formula_ge4 n hn]
  have hpB : ¬ p ∣ Bprod n := prime_not_dvd_Bprod hp hpn
  rw [hq, gcd_cp_B_eq_c hp hcB hpB]
  rw [Nat.mul_comm]
  exact Nat.mul_div_left p hcpos

lemma Bprod_dvd_one (n) : 1 ∣ Bprod n := by simp
lemma Bprod_dvd_two {n} (hn : 4 ≤ n) : 2 ∣ Bprod n := by
  have h4mem : 4 ∈ Finset.Icc 3 n := by simp; omega
  exact (show 2 ∣ 4 from by norm_num).trans (by simpa [Bprod] using Finset.dvd_prod_of_mem (fun j => j) h4mem)
lemma Bprod_dvd_three {n} (hn : 3 ≤ n) : 3 ∣ Bprod n := by
  have h3mem : 3 ∈ Finset.Icc 3 n := by simp; omega
  simpa [Bprod] using Finset.dvd_prod_of_mem (fun j => j) h3mem
lemma Bprod_dvd_four {n} (hn : 4 ≤ n) : 4 ∣ Bprod n := by
  have h4mem : 4 ∈ Finset.Icc 3 n := by simp; omega
  simpa [Bprod] using Finset.dvd_prod_of_mem (fun j => j) h4mem

lemma exists_case_mod2 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) (hmod : p % 5 = 2) :
    ∃ n, n ≥ 3 ∧ a n = p := by
  let n := (3*p + 4) / 5
  have hdiv : (3*p + 4) % 5 = 0 := by omega
  have hn_eq : 5*n = 3*p + 4 := by
    unfold n
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hn4 : 4 ≤ n := by
    have hp2 := hp.two_le
    have hpne2 : p ≠ 2 := by omega
    omega
  refine ⟨n, by omega, ?_⟩
  apply (a_eq_prime_of_q_eq_cp (c:=3) hn4 hp)
  · omega
  · norm_num
  · exact Bprod_dvd_three (by omega)
  · unfold qnat
    omega

lemma exists_case_mod1 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) (hp3 : p ≠ 3) (hp11 : p ≠ 11)
    (hmod : p % 5 = 1) : ∃ n, n ≥ 3 ∧ a n = p := by
  let n := (p + 4) / 5
  have hdiv : (p + 4) % 5 = 0 := by omega
  have hn_eq : 5*n = p + 4 := by
    unfold n
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hn4 : 4 ≤ n := by
    have hp2 := hp.two_le
    have hpne2 : p ≠ 2 := by omega
    omega
  refine ⟨n, by omega, ?_⟩
  apply (a_eq_prime_of_q_eq_cp (c:=1) hn4 hp)
  · omega
  · norm_num
  · simp
  · unfold qnat; omega

lemma exists_case_mod3 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) (hp3 : p ≠ 3) (hmod : p % 5 = 3) :
    ∃ n, n ≥ 3 ∧ a n = p := by
  let n := (2*p + 4) / 5
  have hdiv : (2*p + 4) % 5 = 0 := by omega
  have hn_eq : 5*n = 2*p + 4 := by
    unfold n
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hn4 : 4 ≤ n := by
    have hp2 := hp.two_le
    have hpne2 : p ≠ 2 := by omega
    omega
  refine ⟨n, by omega, ?_⟩
  apply (a_eq_prime_of_q_eq_cp (c:=2) hn4 hp)
  · omega
  · norm_num
  · exact Bprod_dvd_two hn4
  · unfold qnat; omega

lemma exists_case_mod4 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) (hmod : p % 5 = 4) :
    ∃ n, n ≥ 3 ∧ a n = p := by
  let n := (4*p + 4) / 5
  have hdiv : (4*p + 4) % 5 = 0 := by omega
  have hn_eq : 5*n = 4*p + 4 := by
    unfold n
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hn4 : 4 ≤ n := by
    have hp2 := hp.two_le
    have hpne2 : p ≠ 2 := by omega
    omega
  refine ⟨n, by omega, ?_⟩
  apply (a_eq_prime_of_q_eq_cp (c:=4) hn4 hp)
  · omega
  · norm_num
  · exact Bprod_dvd_four hn4
  · unfold qnat; omega

lemma exists_for_prime (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ∃ n, n ≥ 3 ∧ a n = p := by
  by_cases hp11 : p = 11
  · subst hp11
    exact ⟨3, by norm_num, by simpa using a_three⟩
  · have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : p % 5
    · have hdvd : 5 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
      have hcases := hp.eq_one_or_self_of_dvd 5 hdvd
      rcases hcases with h1 | h5eq
      · norm_num at h1
      · exact (hp5 h5eq.symm).elim
    · exact exists_case_mod1 hp hodd hp3 hp11 h
    · exact exists_case_mod2 hp hodd h
    · exact exists_case_mod3 hp hodd hp3 h
    · exact exists_case_mod4 hp hodd h

lemma prime_eligible_ge7 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) : 7 ≤ p := by
  have hp2 := hp.two_le
  have hpne2 : p ≠ 2 := by omega
  omega

lemma mul_dvd_Bprod_of_mem_ne {x z n : ℕ} (hx : x ∈ Finset.Icc 3 n) (hz : z ∈ Finset.Icc 3 n)
    (hneq : x ≠ z) : x*z ∣ Bprod n := by
  unfold Bprod
  let s := Finset.Icc 3 n
  have hxmem : x ∈ s := hx
  have hzmemerase : z ∈ s.erase x := by simpa [s, Finset.mem_erase, hneq.symm] using hz
  have hzdiv : z ∣ (s.erase x).prod (fun j => j) := Finset.dvd_prod_of_mem (fun j => j) hzmemerase
  rcases hzdiv with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [← Finset.prod_erase_mul s (fun j => j) hxmem]
  rw [ht]
  ring

lemma relation_of_a_eq_prime {n p : ℕ} (hn3 : 3 ≤ n) (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (ha : a n = p) :
    ∃ c, 0 < c ∧ c < 5 ∧ qnat n = c*p := by
  have hp7 : 7 ≤ p := prime_eligible_ge7 hp hodd hp3 hp5
  by_cases hn3eq : n = 3
  · subst hn3eq
    have : p = 11 := by simpa [a_three] using ha.symm
    subst this
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    unfold qnat; norm_num
  · have hn4 : 4 ≤ n := by omega
    have hform := a_formula_ge4 n hn4
    let G := Nat.gcd (qnat n) (Bprod n)
    have hGdvdq : G ∣ qnat n := Nat.gcd_dvd_left _ _
    have hqdiv : qnat n / G = p := by simpa [G, hform] using ha
    have hqeq : qnat n = p * G := Nat.eq_mul_of_div_eq_left hGdvdq hqdiv
    have hGpos : 0 < G := by
      have hqpos : 0 < qnat n := by unfold qnat; omega
      exact Nat.pos_of_dvd_of_pos hGdvdq hqpos
    have hn_lt_p : n < p := by
      by_contra hnot
      have hple : p ≤ n := by omega
      have hp_mem : p ∈ Finset.Icc 3 n := by simp; omega
      have hG_lt_n : G < n := by
        have hmul_lt : p * G < p * n := by
          rw [← hqeq]
          unfold qnat
          have hlt : 5 * n - 4 < 7 * n := by omega
          exact lt_of_lt_of_le hlt (Nat.mul_le_mul_right n hp7)
        exact (Nat.mul_lt_mul_left hp.pos).mp hmul_lt
      have hG_ge3 : 3 ≤ G := by
        by_contra hg
        have hGle2 : G ≤ 2 := by omega
        have hle : p * G ≤ 2 * n := by
          exact le_trans (Nat.mul_le_mul_left p hGle2) (by nlinarith [hple])
        rw [← hqeq] at hle
        unfold qnat at hle
        omega
      have hG_mem : G ∈ Finset.Icc 3 n := by simp; omega
      have hq_dvd_B : qnat n ∣ Bprod n := by
        by_cases hGp : G = p
        · have hqpp : qnat n = p*p := by simpa [hGp] using hqeq
          have h2p_le : 2*p ≤ n := by
            have hp11 : 11 ≤ p := by
              by_contra hlt
              have hp_le10 : p ≤ 10 := by omega
              interval_cases p
              all_goals try norm_num at hp
              all_goals try norm_num at hodd
              all_goals try norm_num at hp5
              all_goals try norm_num [qnat] at hqpp
              all_goals omega
            have hz0 : ((qnat n : ℤ) = (p:ℤ)*(p:ℤ)) := by exact_mod_cast hqpp
            have hzq : ((qnat n : ℤ) = 5*(n:ℤ)-4) := by unfold qnat; omega
            nlinarith [hz0, hzq, show (11:ℤ) ≤ p by exact_mod_cast hp11]
          have hp_mem2 : (2*p) ∈ Finset.Icc 3 n := by
            simp
            constructor <;> nlinarith [show (7:ℤ) ≤ p by exact_mod_cast hp7]
          have hne : p ≠ 2*p := by nlinarith [show (0:ℤ) < p by exact_mod_cast hp.pos]
          have hdiv := mul_dvd_Bprod_of_mem_ne hp_mem hp_mem2 hne
          have hp2dvd : p*p ∣ p*(2*p) := by
            refine ⟨2, by ring⟩
          exact (by simpa [hqpp, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hp2dvd.trans hdiv)
        · have hp_ne_G : p ≠ G := by intro h; exact hGp h.symm
          have hdiv := mul_dvd_Bprod_of_mem_ne hp_mem hG_mem hp_ne_G
          simpa [hqeq, Nat.mul_comm] using hdiv
      have hgcd_eq_q : Nat.gcd (qnat n) (Bprod n) = qnat n := Nat.gcd_eq_left hq_dvd_B
      have ha1 : a n = 1 := by
        rw [a_formula_ge4 n hn4, hgcd_eq_q]
        exact Nat.div_self (by unfold qnat; omega : 0 < qnat n)
      have hp_ne_one : p ≠ 1 := hp.ne_one
      omega
    refine ⟨G, hGpos, ?_, hqeq.trans ?_⟩
    · unfold qnat at hqeq
      have hmul_lt : p * G < p * 5 := by
        rw [← hqeq]
        omega
      exact (Nat.mul_lt_mul_left hp.pos).mp hmul_lt
    · rw [Nat.mul_comm]

/--
Conjecture 2: Except for 3 and 5, all odd primes appear in the sequence once.
Formally: for every natural number $p$ that is an odd prime and $p 
e 3$ and $p 
e 5$,
there is exactly one index $n \ge 3$ such that $a(n) = p$.
-/
theorem oeis_372761_conjecture_2 :
  ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 →
    ∃! n, n ≥ 3 ∧ a n = p := by
  intro p hpall
  rcases hpall with ⟨hp, hodd, hp3, hp5⟩
  obtain ⟨n, hn⟩ := exists_for_prime p hp hodd hp3 hp5
  refine ⟨n, hn, ?_⟩
  intro y hy
  obtain ⟨c, hcpos, hclt, hyq⟩ := relation_of_a_eq_prime hy.1 hp hodd hp3 hp5 hy.2
  obtain ⟨d, hdpos, hdlt, hnq⟩ := relation_of_a_eq_prime hn.1 hp hodd hp3 hp5 hn.2
  have hpmod_ne : p % 5 ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hcases := hp.eq_one_or_self_of_dvd 5 hdvd
    rcases hcases with h1 | h5eq
    · norm_num at h1
    · exact hp5 h5eq.symm
  have hceq : c = d := by
    unfold qnat at hyq hnq
    interval_cases c <;> interval_cases d <;> first | rfl | (exfalso; omega)
  subst hceq
  unfold qnat at hyq hnq
  omega
