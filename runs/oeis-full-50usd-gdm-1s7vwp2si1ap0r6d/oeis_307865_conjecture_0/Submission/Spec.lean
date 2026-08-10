import FormalConjectures.Util.ProblemImports

open Nat Finset ZMod

/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$. We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

/--
oeis_307865_conjecture_0: Conjecture: if $2n+1$ is an absolute Euler pseudoprime, then $a(n) = 0$.
Note: this conjecture trivially holds for $n=0$ since $2 \cdot 0 + 1 = 1$, which is not an absolute Euler pseudoprime.
For a meaningful statement, one usually considers $n>3$.
-/
lemma prod_ge_one_of_ge_one (L : List ℕ) (h : ∀ x ∈ L, x ≥ 1) : L.prod ≥ 1 := by
  induction L with
  | nil => simp
  | cons x L' ih =>
    simp only [List.prod_cons]
    have hx : x ≥ 1 := h x (List.mem_cons.mpr (Or.inl rfl))
    have ih' : L'.prod ≥ 1 := ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))
    have : x * L'.prod ≥ 1 * 1 := Nat.mul_le_mul hx ih'
    omega

lemma exists_p_v_of_composite {M : ℕ} (hM1 : M > 1) (hComp : ¬ Nat.Prime M) :
    ∃ p v : ℕ, Nat.Prime p ∧ p ∣ M ∧ v > 1 ∧ M = p * v ∧ (p ∣ v ∨ Coprime p v) := by
  have h_ne_zero : M ≠ 0 := by omega
  have h_prod := Nat.prod_primeFactorsList h_ne_zero
  generalize hL : Nat.primeFactorsList M = L
  rw [hL] at h_prod
  rcases L with _ | ⟨p, _ | ⟨q, L'⟩⟩
  · -- []
    simp only [List.prod_nil] at h_prod; omega
  · -- [p]
    simp only [List.prod_singleton] at h_prod
    have hp : Nat.Prime p := by
      have h_mem : p ∈ Nat.primeFactorsList M := by rw [hL]; exact List.mem_cons.mpr (Or.inl rfl)
      exact Nat.prime_of_mem_primeFactorsList h_mem
    rw [h_prod] at hp
    exact (hComp hp).elim
  · -- p :: q :: L'
    have hp : Nat.Prime p := by
      have h_mem : p ∈ Nat.primeFactorsList M := by rw [hL]; exact List.mem_cons.mpr (Or.inl rfl)
      exact Nat.prime_of_mem_primeFactorsList h_mem
    have hq : Nat.Prime q := by
      have h_mem : q ∈ Nat.primeFactorsList M := by rw [hL]; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      exact Nat.prime_of_mem_primeFactorsList h_mem
    have hp_dvd : p ∣ M := Nat.dvd_of_mem_primeFactorsList (by rw [hL]; exact List.mem_cons.mpr (Or.inl rfl))
    let v := M / p
    have hM_eq : M = p * v := (Nat.mul_div_cancel' hp_dvd).symm
    have hv1 : v > 1 := by
      have h_prod' : p * (q * L'.prod) = M := h_prod
      rw [hM_eq] at h_prod'
      have h_v_eq : v = q * L'.prod := Nat.eq_of_mul_eq_mul_left hp.pos h_prod'.symm
      rw [h_v_eq]
      have h_q_ge_2 := hq.two_le
      have h_prod_ge_1 : L'.prod ≥ 1 := by
        apply prod_ge_one_of_ge_one
        intro x hx
        have hx_mem : x ∈ Nat.primeFactorsList M := by
          rw [hL]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hx)))
        have hx_prime := Nat.prime_of_mem_primeFactorsList hx_mem
        have h_one_lt := hx_prime.one_lt
        omega
      have : q * L'.prod ≥ 2 * 1 := Nat.mul_le_mul h_q_ge_2 h_prod_ge_1
      omega
    use p, v
    refine ⟨hp, hp_dvd, hv1, hM_eq, ?_⟩
    rcases Decidable.em (p ∣ v) with h_dvd | h_ndvd
    · left; exact h_dvd
    · right; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr h_ndvd

lemma prime_factor_odd {M p : ℕ} (hMod : M % 2 = 1) (hp : Nat.Prime p) (h_dvd : p ∣ M) : p % 2 = 1 := by
  have hp_even : p ≠ 2 := by
    intro hc
    rw [hc] at h_dvd
    have h2 : 2 ∣ M := h_dvd
    have h3 : M % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
    omega
  have hp_two_le := hp.two_le
  rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
  · have h_dvd2 : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hp2 := hp.eq_one_or_self_of_dvd 2 h_dvd2
    omega
  · exact h1

lemma r_dvd_v_of_p_dvd_v {M p v r : ℕ} (hM : M = p * v) (hp : Nat.Prime p) (hr : Nat.Prime r) (h_dvd_v : p ∣ v) (h_dvd_M : r ∣ M) : r ∣ v := by
  have h_dvd_mul : r ∣ p * v := by rwa [← hM]
  rcases hr.dvd_mul.mp h_dvd_mul with hr_p | hr_v
  · have hr_eq_p : p = r := (Nat.Prime.dvd_iff_eq hp hr.ne_one).mp hr_p
    rw [← hr_eq_p]
    exact h_dvd_v
  · exact hr_v

lemma coprime_one_add_v_of_dvd (M : ℕ) {v : ℕ} (h_div : ∀ r, Nat.Prime r → r ∣ M → r ∣ v) : Coprime (1 + v) M := by
  by_contra hc
  rcases Nat.exists_prime_and_dvd hc with ⟨r, hr, hr_dvd⟩
  have hr_dvd1 : r ∣ 1 + v := Nat.dvd_trans hr_dvd (Nat.gcd_dvd_left _ _)
  have hr_dvdM : r ∣ M := Nat.dvd_trans hr_dvd (Nat.gcd_dvd_right _ _)
  have hr_dvdv : r ∣ v := h_div r hr hr_dvdM
  have hr_dvd_one : r ∣ 1 := by
    have h_sub : (1 + v) - v = 1 := by omega
    rw [← h_sub]
    exact Nat.dvd_sub hr_dvd1 hr_dvdv
  have hr_ne_one := hr.ne_one
  have hr_one : r = 1 := Nat.dvd_one.mp hr_dvd_one
  exact False.elim (hr_ne_one hr_one)

lemma v_sq_eq_zero {M p v : ℕ} (hM : M = p * v) (hp_v : p ∣ v) : ((v : ZMod M) ^ 2) = 0 := by
  rcases hp_v with ⟨d, hd⟩
  have hv2 : v ^ 2 = M * d := by
    calc
      v ^ 2 = v * v := sq v
      _ = v * (p * d) := by rw [hd]
      _ = (p * v) * d := by ring
      _ = M * d := by rw [hM]
  have h_dvd : M ∣ v ^ 2 := ⟨d, hv2⟩
  have h_cast : ((v ^ 2 : ℕ) : ZMod M) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod M) M]
    exact h_dvd
  push_cast at h_cast
  exact h_cast

lemma one_add_pow_eq_one_add_mul {M : ℕ} (v : ZMod M) (hv2 : v ^ 2 = 0) (n : ℕ) : (1 + v) ^ n = 1 + (n : ZMod M) * v := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    calc
      (1 + v) ^ (k + 1) = (1 + v) ^ k * (1 + v) := pow_succ (1 + v) k
      _ = (1 + (k : ZMod M) * v) * (1 + v) := by rw [ih]
      _ = 1 + (k : ZMod M) * v + v + (k : ZMod M) * (v ^ 2) := by ring
      _ = 1 + (k : ZMod M) * v + v + (k : ZMod M) * 0 := by rw [hv2]
      _ = 1 + ((k + 1 : ℕ) : ZMod M) * v := by
        push_cast
        ring

lemma contradiction_p_dvd_n {M p n : ℕ} (hM : M = 2 * n + 1) (hp : Nat.Prime p) (h1 : p ∣ M) (h2 : p ∣ n) : False := by
  have h_dvd_2n : p ∣ 2 * n := dvd_mul_of_dvd_right h2 2
  have h_sub : M - 2 * n = 1 := by omega
  have h_dvd_1 : p ∣ 1 := by
    rw [← h_sub]
    exact Nat.dvd_sub h1 h_dvd_2n
  have hp_ne_one := hp.ne_one
  have hp_one : p = 1 := Nat.dvd_one.mp h_dvd_1
  exact hp_ne_one hp_one

theorem oeis_307865_conjecture_0 (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
  set m := 2 * n + 1
  have hm : m = 2 * n + 1 := rfl
  have hm1 : m > 1 := h.1
  have hComp : ¬ Nat.Prime m := h.2.1
  have h_ae_raw := h.2.2
  have h_n : (m - 1) / 2 = n := by omega
  rw [h_n] at h_ae_raw
  rw [a]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b hb hb_pow
  change b ∈ Ico 1 m at hb
  change (b : ZMod m) ^ n = -1 at hb_pow
  have hb1 : 1 ≤ b := (mem_Ico.mp hb).1
  have hbm : b < m := (mem_Ico.mp hb).2
  rcases exists_p_v_of_composite hm1 hComp with ⟨p, v, hp, hp_dvd, hv1, hm_eq, h_cases⟩
  have hm_odd : m % 2 = 1 := by omega
  have hp_odd : p % 2 = 1 := prime_factor_odd hm_odd hp hp_dvd
  rcases h_cases with hp_dvd_v | h_cop
  · set b_test := 1 + v
    have h_div : ∀ r, Nat.Prime r → r ∣ m → r ∣ v := by
      intro r hr hr_dvd
      exact r_dvd_v_of_p_dvd_v hm_eq hp hr hp_dvd_v hr_dvd
    have h_cop_test : Coprime b_test m := coprime_one_add_v_of_dvd m h_div
    have h_test_pow_cases := h_ae_raw b_test h_cop_test
    have hv2_zmod : (v : ZMod m) ^ 2 = 0 := v_sq_eq_zero hm_eq hp_dvd_v
    have h_bin : (1 + (v : ZMod m)) ^ n = 1 + (n : ZMod m) * (v : ZMod m) := by
      exact one_add_pow_eq_one_add_mul (v : ZMod m) hv2_zmod n
    have h_cast_b_test : (b_test : ZMod m) = 1 + (v : ZMod m) := by
      change (((1 + v : ℕ) : ZMod m)) = 1 + (v : ZMod m)
      push_cast
      rfl
    have h_test_pow : (b_test : ZMod m) ^ n = 1 + (n : ZMod m) * (v : ZMod m) := by
      rw [h_cast_b_test, h_bin]
    have h_not_neg_one : (b_test : ZMod m) ^ n ≠ -1 := by
      intro hc
      have hdvd : m ∣ b_test ^ n + 1 := by
        have h_eq_zero : ((b_test : ZMod m) ^ n + 1) = 0 := by rw [hc, neg_add_cancel]
        have h_nat : ((b_test ^ n + 1 : ℕ) : ZMod m) = 0 := by push_cast; exact h_eq_zero
        rwa [CharP.cast_eq_zero_iff (ZMod m) m] at h_nat
      have hdvd_p : p ∣ b_test ^ n + 1 := dvd_trans hp_dvd hdvd
      have h_zero_p : ((b_test ^ n + 1 : ℕ) : ZMod p) = 0 := by
        rwa [CharP.cast_eq_zero_iff (ZMod p) p]
      have h_pow_p : (b_test : ZMod p) ^ n = -1 := by
        push_cast at h_zero_p
        exact eq_neg_of_add_eq_zero_left h_zero_p
      have h_b_p : (b_test : ZMod p) = 1 := by
        have h_v_p : (v : ZMod p) = 0 := by
          rwa [CharP.cast_eq_zero_iff (ZMod p) p]
        have h_sum : (b_test : ZMod p) = 1 + (v : ZMod p) := by
          change (((1 + v : ℕ) : ZMod p)) = 1 + (v : ZMod p)
          push_cast
          rfl
        rw [h_v_p] at h_sum
        simp at h_sum
        exact h_sum
      rw [h_b_p] at h_pow_p
      simp at h_pow_p
      have h_two : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 1 + 1 := by ring
        _ = 1 + -1 := by rw [← h_pow_p]
        _ = 0 := by ring
      have h_p_dvd_2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h_two
      have h_le := Nat.le_of_dvd (by decide) h_p_dvd_2
      have hp_ge_2 := hp.two_le
      omega
    rcases h_test_pow_cases with h_one | h_neg_one
    · have h_nv_zero : ((n : ZMod m) * (v : ZMod m)) = 0 := by
        have h_eq_one : 1 + (n : ZMod m) * (v : ZMod m) = 1 + 0 := by
          rw [add_zero]
          rw [← h_test_pow]
          exact h_one
        exact add_left_cancel h_eq_one
      have hdvd_nv : m ∣ n * v := by
        have h_nat : ((n * v : ℕ) : ZMod m) = 0 := by push_cast; exact h_nv_zero
        rwa [CharP.cast_eq_zero_iff (ZMod m) m] at h_nat
      rw [hm_eq] at hdvd_nv
      have hv_pos : v > 0 := by omega
      have hp_dvd_n : p ∣ n := Nat.dvd_of_mul_dvd_mul_right hv_pos hdvd_nv
      exact contradiction_p_dvd_n hm hp hp_dvd hp_dvd_n
    · contradiction

  · have hb_v_pow : (b : ZMod v) ^ n = -1 := by
      have hdvd : m ∣ b ^ n + 1 := by
        have h1 : ((b : ZMod m) ^ n + 1) = 0 := by rw [hb_pow, neg_add_cancel]
        have h2 : ((b ^ n + 1 : ℕ) : ZMod m) = 0 := by push_cast; exact h1
        rwa [CharP.cast_eq_zero_iff (ZMod m) m] at h2
      have hdvd_v : v ∣ b ^ n + 1 := by
        have hv_m : v ∣ m := ⟨p, by rw [hm_eq, mul_comm]⟩
        exact dvd_trans hv_m hdvd
      have h3 : ((b ^ n + 1 : ℕ) : ZMod v) = 0 := by
        rwa [CharP.cast_eq_zero_iff (ZMod v) v]
      push_cast at h3
      exact eq_neg_of_add_eq_zero_left h3
    have hb_p_pow : (b : ZMod p) ^ n = -1 := by
      have hdvd : m ∣ b ^ n + 1 := by
        have h1 : ((b : ZMod m) ^ n + 1) = 0 := by rw [hb_pow, neg_add_cancel]
        have h2 : ((b ^ n + 1 : ℕ) : ZMod m) = 0 := by push_cast; exact h1
        rwa [CharP.cast_eq_zero_iff (ZMod m) m] at h2
      have hdvd_p : p ∣ b ^ n + 1 := dvd_trans hp_dvd hdvd
      have h3 : ((b ^ n + 1 : ℕ) : ZMod p) = 0 := by
        rwa [CharP.cast_eq_zero_iff (ZMod p) p]
      push_cast at h3
      exact eq_neg_of_add_eq_zero_left h3
    have hb_v_unit : IsUnit (b : ZMod v) := by
      have h1 : (b : ZMod v) * (- (b : ZMod v) ^ (n - 1)) = 1 := by
        have hn_ge_1 : n ≥ 1 := by omega
        calc
          (b : ZMod v) * (- (b : ZMod v) ^ (n - 1)) = - ((b : ZMod v) ^ (n - 1) * (b : ZMod v)) := by ring
          _ = - ((b : ZMod v) ^ (n - 1 + 1)) := by rw [← pow_succ]
          _ = - ((b : ZMod v) ^ n) := by rw [Nat.sub_add_cancel hn_ge_1]
          _ = - (-1) := by rw [hb_v_pow]
          _ = 1 := by ring
      exact IsUnit.of_mul_eq_one (- (b : ZMod v) ^ (n - 1)) h1
    let x_raw := (ZMod.chineseRemainder h_cop).symm ((1 : ZMod p), (b : ZMod v))
    have hu_pair : IsUnit ((1 : ZMod p), (b : ZMod v)) := by
      rcases hb_v_unit with ⟨u, hu_eq⟩
      rw [← hu_eq]
      have h1 : ((1 : ZMod p), (u : ZMod v)) * ((1 : ZMod p), (u.inv : ZMod v)) = 1 := by
        ext
        · simp
        · simp only [Prod.snd_mul, Prod.snd_one]
          exact u.mul_inv
      exact IsUnit.of_mul_eq_one ((1 : ZMod p), (u.inv : ZMod v)) h1
    have hu_raw : IsUnit x_raw := IsUnit.map (ZMod.chineseRemainder h_cop).symm hu_pair
    have h_raw_pow : x_raw ^ n = (ZMod.chineseRemainder h_cop).symm (1, -1) := by
      have h_pow := map_pow (ZMod.chineseRemainder h_cop).symm ((1 : ZMod p), (b : ZMod v)) n
      rw [← h_pow]
      have h_pair : ((1 : ZMod p), (b : ZMod v)) ^ n = (1, -1) := by
        ext
        · simp
        · simp [hb_v_pow]
      rw [h_pair]
    have hv_odd : v % 2 = 1 := by
      have h1 : (p * v) % 2 = ((p % 2) * (v % 2)) % 2 := Nat.mul_mod p v 2
      rw [← hm_eq] at h1
      rw [hm_odd] at h1
      rcases Nat.mod_two_eq_zero_or_one v with h0 | h2
      · rw [h0] at h1
        simp at h1
      · exact h2
    rw [hm_eq] at h_ae_raw
    have hI : NeZero (p * v) := ⟨by omega⟩
    have h_cop_K : x_raw.val.Coprime (p * v) := by
      have h_unit_equiv : IsUnit x_raw ↔ x_raw.val.Coprime (p * v) := by
        have h := ZMod.isUnit_iff_coprime x_raw.val (p * v)
        have hx : (x_raw.val : ZMod (p * v)) = x_raw := by rw [ZMod.natCast_val, ZMod.cast_id]
        rw [hx] at h
        exact h
      exact h_unit_equiv.mp hu_raw
    have h_pow_cases := h_ae_raw x_raw.val h_cop_K
    have hx_val : (x_raw.val : ZMod (p * v)) = x_raw := by rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hx_val] at h_pow_cases
    rcases h_pow_cases with h_one | h_neg_one
    · rw [h_raw_pow] at h_one
      have h_one' : (ZMod.chineseRemainder h_cop).symm (1, -1) = (ZMod.chineseRemainder h_cop).symm (1, 1) := by
        have h_symm_one : (ZMod.chineseRemainder h_cop).symm (1, 1) = 1 := by
          have h1 : (1 : ZMod p × ZMod v) = (1, 1) := rfl
          rw [← h1]
          exact map_one (ZMod.chineseRemainder h_cop).symm
        rw [h_symm_one]
        exact h_one
      have h_inj := (ZMod.chineseRemainder h_cop).symm.injective h_one'
      have h_snd : (-1 : ZMod v) = 1 := by injection h_inj
      have h2 : (2 : ZMod v) = 0 := by
        calc (2 : ZMod v) = 1 + 1 := by ring
        _ = -1 + 1 := by rw [h_snd]
        _ = 0 := by ring
      have hdvd : v ∣ 2 := (CharP.cast_eq_zero_iff (ZMod v) v 2).mp h2
      have h_le := Nat.le_of_dvd (by decide) hdvd
      omega
    · rw [h_raw_pow] at h_neg_one
      have h_neg_one' : (ZMod.chineseRemainder h_cop).symm (1, -1) = (ZMod.chineseRemainder h_cop).symm (-1, -1) := by
        have h_symm_neg_one : (ZMod.chineseRemainder h_cop).symm (-1, -1) = -1 := by
          have h1 : (-1 : ZMod p × ZMod v) = (-1, -1) := rfl
          rw [← h1]
          rw [map_neg, map_one]
        rw [h_symm_neg_one]
        exact h_neg_one
      have h_inj := (ZMod.chineseRemainder h_cop).symm.injective h_neg_one'
      have h_fst : (1 : ZMod p) = -1 := by injection h_inj
      have h2 : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 1 + 1 := by ring
        _ = 1 + -1 := by rw [← h_fst]
        _ = 0 := by ring
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
      have h_le := Nat.le_of_dvd (by decide) hdvd
      have hp_ge_2 := hp.two_le
      omega

