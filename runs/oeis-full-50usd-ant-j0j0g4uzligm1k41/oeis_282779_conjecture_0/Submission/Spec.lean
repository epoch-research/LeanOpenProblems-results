import FormalConjectures.Util.ProblemImports

open Nat Set Classical

/--
A282779: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that $\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def A282779 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

open Finset in
/-- Any period `T` must be divisible by every prime `q` dividing `n`.  This uses the fact
that if `q ∤ T` then translation by `T` generates all of `ZMod q`, forcing `x ↦ x^p` to be
constant, which is absurd. -/
private theorem period_div_lemma (p n T : ℕ) (hp : Nat.Prime p) (q : ℕ) (hq : Nat.Prime q)
    (hqn : q ∣ n) (hP : ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n) : q ∣ T := by
  haveI := Fact.mk hq
  by_contra hnT
  have ht : (T : ZMod q) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hshift : ∀ x : ZMod q, (x + (T : ZMod q)) ^ p = x ^ p := by
    intro x
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective x
    have hmod : (k + T) ^ p ≡ k ^ p [MOD q] := Nat.ModEq.of_dvd hqn (hP k)
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
    push_cast at this
    convert this using 2
  have key : ∀ m : ℕ, ∀ x : ZMod q, (x + m • (T : ZMod q)) ^ p = x ^ p := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro x
      rw [succ_nsmul, ← add_assoc, hshift (x + m • (T : ZMod q)), ih]
  have hall : ∀ y : ZMod q, y ^ p = 0 := by
    intro y
    have hc : y = (y * (T : ZMod q)⁻¹).val • (T : ZMod q) := by
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, mul_assoc,
        inv_mul_cancel₀ ht, mul_one]
    have := key (y * (T : ZMod q)⁻¹).val 0
    rw [zero_add] at this
    rw [hc, this, zero_pow hp.pos.ne']
  have := hall 1
  rw [one_pow] at this
  exact one_ne_zero this

open Finset in
/-- The core valuation bound: for any prime `q`, `v_q(n) ≤ v_q(p) + v_q(T)` for any period `T`. -/
private theorem period_core_lemma (p n T : ℕ) (hp : Nat.Prime p) (hn : 0 < n) (hT : 0 < T)
    (q : ℕ) (hq : Nat.Prime q) (hP : ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n) :
    n.factorization q ≤ p.factorization q + T.factorization q := by
  set vn := n.factorization q with hvn
  set vp := p.factorization q with hvp
  set vt := T.factorization q with hvt
  by_contra hcon
  push_neg at hcon
  have hqn : q ∣ n := by
    have : 1 ≤ vn := by omega
    exact hq.dvd_of_dvd_pow (n := 1) (by simpa using (hq.pow_dvd_iff_le_factorization hn.ne').2 this)
  have hqT : q ∣ T := period_div_lemma p n T hp q hq hqn hP
  have hvt1 : 1 ≤ vt := by
    rw [hvt]
    exact (hq.pow_dvd_iff_le_factorization hT.ne').1 (by simpa using hqT)
  have hbinid : (1 + (T : ℤ)) ^ p
      = 1 + (p : ℤ) * T + (∑ k ∈ Finset.Ico 2 p, (T : ℤ) ^ k * (p.choose k)) + (T : ℤ) ^ p := by
    have hbin : (1 + (T : ℤ)) ^ p = ∑ k ∈ Finset.range (p + 1), (T : ℤ) ^ k * (p.choose k) := by
      rw [add_comm, add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      rw [one_pow, mul_one]
    rw [hbin, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by norm_num)
        (show 2 ≤ p + 1 by have := hp.two_le; omega),
      Finset.sum_Ico_succ_top (show 2 ≤ p by exact hp.two_le)]
    have h02 : ∑ k ∈ Finset.Ico 0 2, (T : ℤ) ^ k * (p.choose k) = 1 + (p : ℤ) * T := by
      rw [show (2 : ℕ) = 0 + 1 + 1 by rfl, Finset.sum_Ico_succ_top (by norm_num),
          Finset.sum_Ico_succ_top (by norm_num)]
      simp [Nat.choose_one_right]
      ring
    rw [h02, Nat.choose_self]
    push_cast
    ring
  set R : ℤ := ∑ k ∈ Finset.Ico 2 p, (T : ℤ) ^ k * (p.choose k) with hR
  have hRdvd : (q : ℤ) ^ (vp + vt + 1) ∣ R := by
    rw [hR]
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk2, hkp⟩ := hk
    have hqvtT : (q : ℤ) ^ vt ∣ (T : ℤ) := by
      have : q ^ vt ∣ T := (hq.pow_dvd_iff_le_factorization hT.ne').2 (le_of_eq hvt.symm)
      exact_mod_cast this
    have hTk : (q : ℤ) ^ (vt * k) ∣ (T : ℤ) ^ k := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd hqvtT k
    have hchoose : (q : ℤ) ^ vp ∣ ((p.choose k : ℕ) : ℤ) := by
      by_cases hqp : q = p
      · subst hqp
        have hf1 : q.factorization q = 1 := by
          rw [hq.factorization, Finsupp.single_eq_same]
        rw [hvp, hf1, pow_one]
        have : q ∣ q.choose k := hq.dvd_choose_self (by omega) hkp
        exact_mod_cast this
      · have hf0 : p.factorization q = 0 := by
          rw [hp.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp)]
        rw [hvp, hf0, pow_zero]
        exact one_dvd _
    have hterm : (q : ℤ) ^ (vp + vt * k) ∣ (T : ℤ) ^ k * (p.choose k) := by
      rw [pow_add, mul_comm ((T : ℤ) ^ k) _]
      exact mul_dvd_mul hchoose hTk
    calc (q : ℤ) ^ (vp + vt + 1) ∣ (q : ℤ) ^ (vp + vt * k) := by
            apply pow_dvd_pow
            have h1 : vt * 2 ≤ vt * k := Nat.mul_le_mul (le_refl vt) hk2
            omega
      _ ∣ (T : ℤ) ^ k * (p.choose k) := hterm
  have hd1 : (n : ℤ) ∣ (1 + (T : ℤ)) ^ p - 1 := by
    have h := Nat.modEq_iff_dvd.mp (hP 1).symm
    push_cast at h
    simpa using h
  have hd0 : (n : ℤ) ∣ (T : ℤ) ^ p := by
    have h := Nat.modEq_iff_dvd.mp (hP 0).symm
    push_cast at h
    simpa [zero_pow hp.pos.ne'] using h
  have hD : (n : ℤ) ∣ ((p : ℤ) * T + R) := by
    have hsub : (n : ℤ) ∣ ((1 + (T : ℤ)) ^ p - 1 - (T : ℤ) ^ p) := dvd_sub hd1 hd0
    have heq : (1 + (T : ℤ)) ^ p - 1 - (T : ℤ) ^ p = (p : ℤ) * T + R := by rw [hbinid]; ring
    rwa [heq] at hsub
  have hqpow : (q : ℤ) ^ (vp + vt + 1) ∣ (n : ℤ) := by
    have h1 : q ^ (vp + vt + 1) ∣ n :=
      (pow_dvd_pow q (by omega)).trans (Nat.ordProj_dvd n q)
    exact_mod_cast h1
  have hdpT : (q : ℤ) ^ (vp + vt + 1) ∣ ((p : ℤ) * T) := by
    have h2 : (q : ℤ) ^ (vp + vt + 1) ∣ ((p : ℤ) * T + R) := hqpow.trans hD
    have := dvd_sub h2 hRdvd
    simpa using this
  have hnot : ¬ (q : ℤ) ^ (vp + vt + 1) ∣ ((p : ℤ) * T) := by
    rw [show ((p : ℤ) * T) = ((p * T : ℕ) : ℤ) by push_cast; ring,
        show ((q : ℤ) ^ (vp + vt + 1)) = ((q ^ (vp + vt + 1) : ℕ) : ℤ) by push_cast; ring,
        Int.natCast_dvd_natCast,
        hq.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hp.pos.ne' hT.ne'),
        Nat.factorization_mul hp.pos.ne' hT.ne', Finsupp.add_apply, ← hvp, ← hvt]
    omega
  exact hnot hdpT

open Finset in
/-- `A = (if p^2 ∣ n then n/p else n)` is itself a period. -/
private theorem period_mem_lemma (p n : ℕ) (hp : Nat.Prime p) (hn : 0 < n) :
    ∀ k : ℕ, (k + (if p ^ 2 ∣ n then n / p else n)) ^ p % n = k ^ p % n := by
  split
  · rename_i hpn
    intro k
    set m := n / p with hm
    have hpdvd : p ∣ n := (dvd_pow_self p (by norm_num) : p ∣ p ^ 2).trans hpn
    have hnpm : n = p * m := by rw [hm, Nat.mul_div_cancel' hpdvd]
    have hpm : p ∣ m := by
      rw [hm]
      exact Nat.dvd_div_of_mul_dvd (by rw [pow_two] at hpn; exact hpn)
    have hpmZ : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpm
    have hdvd : (n : ℤ) ∣ ((k : ℤ) + m) ^ p - (k : ℤ) ^ p := by
      have hbin : ((k : ℤ) + m) ^ p - (k : ℤ) ^ p
          = ∑ i ∈ Finset.range p, (k : ℤ) ^ i * (m : ℤ) ^ (p - i) * (p.choose i) := by
        rw [add_pow, Finset.sum_range_succ]
        simp [Nat.choose_self]
      rw [hbin]
      apply Finset.dvd_sum
      intro i hi
      rw [Finset.mem_range] at hi
      have hterm : (n : ℤ) ∣ (m : ℤ) ^ (p - i) * (p.choose i) := by
        rcases Nat.eq_zero_or_pos i with hi0 | hi1
        · subst hi0
          simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
          rw [hnpm]; push_cast
          calc ((p : ℤ) * m) ∣ (m : ℤ) ^ 2 := by
                rw [pow_two]; exact mul_dvd_mul_right hpmZ (m : ℤ)
            _ ∣ (m : ℤ) ^ p := pow_dvd_pow _ hp.two_le
        · have hpc : (p : ℤ) ∣ ((p.choose i : ℕ) : ℤ) := by
            exact_mod_cast hp.dvd_choose_self (by omega) hi
          have hmd : (m : ℤ) ∣ (m : ℤ) ^ (p - i) := dvd_pow_self _ (by omega)
          rw [hnpm]; push_cast
          rw [mul_comm ((m : ℤ) ^ (p - i)) _]
          exact mul_dvd_mul hpc hmd
      calc (n : ℤ) ∣ (m : ℤ) ^ (p - i) * (p.choose i) := hterm
        _ ∣ (k : ℤ) ^ i * ((m : ℤ) ^ (p - i) * (p.choose i)) := dvd_mul_left _ _
        _ = (k : ℤ) ^ i * (m : ℤ) ^ (p - i) * (p.choose i) := by ring
    show (k + m) ^ p ≡ k ^ p [MOD n]
    rw [Nat.modEq_iff_dvd]
    push_cast
    have hrw : (k : ℤ) ^ p - ((k : ℤ) + m) ^ p = -(((k : ℤ) + m) ^ p - (k : ℤ) ^ p) := by ring
    rw [hrw]
    exact dvd_neg.mpr hdvd
  · intro k
    show (k + n) ^ p ≡ k ^ p [MOD n]
    have hkn : (k + n) ≡ k [MOD n] := by
      simp [Nat.ModEq, Nat.add_mod_right]
    exact hkn.pow p

open Finset in
/-- Every period `A = (if p^2 ∣ n then n/p else n)` divides every period `T`. -/
private theorem period_dvd_lemma (p n T : ℕ) (hp : Nat.Prime p) (hn : 0 < n) (hT : 0 < T)
    (hP : ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n) :
    (if p ^ 2 ∣ n then n / p else n) ∣ T := by
  have hApos : 0 < (if p ^ 2 ∣ n then n / p else n) := by
    split
    · rename_i hpn
      exact Nat.div_pos (Nat.le_of_dvd hn ((dvd_pow_self p two_ne_zero).trans hpn)) hp.pos
    · exact hn
  rw [← Nat.factorization_le_iff_dvd hApos.ne' hT.ne', Finsupp.le_def]
  intro q
  by_cases hq : Nat.Prime q
  · have hcore := period_core_lemma p n T hp hn hT q hq hP
    split
    · rename_i hpn
      -- A = n/p, factorization = n.factorization - p.factorization
      rw [Nat.factorization_div (by exact (dvd_pow_self p two_ne_zero).trans hpn),
          Finsupp.tsub_apply]
      omega
    · rename_i hpn
      -- A = n
      by_cases hqp : q = p
      · subst hqp
        have hle1 : n.factorization q ≤ 1 := by
          by_contra h
          push_neg at h
          exact hpn ((hq.pow_dvd_iff_le_factorization hn.ne').2 h)
        rcases Nat.lt_or_ge (n.factorization q) 1 with h0 | h1
        · omega
        · have hqn : q ∣ n :=
            hq.dvd_of_dvd_pow (n := 1) (by simpa using (hq.pow_dvd_iff_le_factorization hn.ne').2 h1)
          have hqT : q ∣ T := period_div_lemma q n T hp q hq hqn hP
          have : 1 ≤ T.factorization q :=
            (hq.pow_dvd_iff_le_factorization hT.ne').1 (by simpa using hqT)
          omega
      · have hf0 : p.factorization q = 0 := by
          rw [hp.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp)]
        omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

/--
oeis_282779_conjecture_0: Conjecture: let a_p(n) be the length of the period of the sequence k^p mod n where p is a prime,
then a_p(n) = n/p if n == 0 (mod p^2) else a_p(n) = n.
-/
theorem oeis_282779_conjecture_0 (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
    period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
  set A := if p ^ 2 ∣ n then n / p else n with hA
  have hApos : 0 < A := by
    rw [hA]
    split
    · rename_i hpn
      exact Nat.div_pos (Nat.le_of_dvd hn ((dvd_pow_self p two_ne_zero).trans hpn)) hp.pos
    · exact hn
  have hmem : A ∈ { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n } := by
    refine ⟨hApos, ?_⟩
    rw [hA]
    exact period_mem_lemma p n hp hn
  unfold period_of_power_mod
  rw [if_neg hn.ne']
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · have hne : { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }.Nonempty := ⟨A, hmem⟩
    have hmem2 := Nat.sInf_mem hne
    obtain ⟨hpos2, hprop2⟩ := hmem2
    have hdvd : A ∣ sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n } := by
      rw [hA]
      exact period_dvd_lemma p n _ hp hn hpos2 hprop2
    exact Nat.le_of_dvd hpos2 hdvd
