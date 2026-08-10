import FormalConjectures.Util.ProblemImports
open Finset

open Polynomial in
/-- The descending Pochhammer product form. -/
lemma prodk (N : ℤ) (j : ℕ) :
    (∏ i ∈ range j, (N - (i:ℤ))) = (j.factorial : ℤ) * Ring.choose N j := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N j
  rw [nsmul_eq_mul] at h
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
  exact h

/-- If `x ≡ v (mod m)` (as integers) with `v < m`, then `x % m = v` for naturals. -/
lemma resmod (x m v : ℕ) (hv : v < m) (h : (x:ℤ) ≡ (v:ℤ) [ZMOD (m:ℤ)]) :
    x % m = v := by
  have h2 : x ≡ v [MOD m] := (Int.natCast_modEq_iff).mp h
  have := h2  -- x % m = v % m
  rw [Nat.ModEq] at this
  rw [this, Nat.mod_eq_of_lt hv]

/-- Core counting bound via Legendre + Kummer. -/
lemma count_bound {p : ℕ} [hp : Fact p.Prime] {E k N a : ℕ} (hkN : k ≤ N)
    (H : ∀ i, 1 ≤ i → i ≤ E → p ^ i ≤ a - 1 ∨ p ^ i ≤ k % p ^ i + (N - k) % p ^ i) :
    E ≤ padicValNat p (Nat.choose N k) + padicValNat p ((a - 1).factorial) := by
  set B := N + a + E + 2 with hB
  have hlogN : Nat.log p N < B := lt_of_le_of_lt (Nat.log_le_self p N) (by omega)
  have hloga : Nat.log p (a - 1) < B := lt_of_le_of_lt (Nat.log_le_self p (a - 1)) (by omega)
  have pvc := padicValNat_choose (p := p) hkN hlogN
  have pvf := padicValNat_factorial (p := p) (n := a - 1) hloga
  rw [pvc, pvf]
  -- rewrite the card as a sum of booleans
  rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  -- E = card (Ico 1 (E+1)) = sum of ones
  have hEcard : E = ∑ _i ∈ Finset.Ico 1 (E + 1), 1 := by
    rw [Finset.sum_const, Nat.card_Ico]; simp
  rw [hEcard]
  -- Ico 1 (E+1) ⊆ Ico 1 B
  have hsub : Finset.Ico 1 (E + 1) ⊆ Finset.Ico 1 B := by
    apply Finset.Ico_subset_Ico (le_refl 1); omega
  calc ∑ _i ∈ Finset.Ico 1 (E + 1), 1
      ≤ ∑ i ∈ Finset.Ico 1 (E + 1),
          ((if p ^ i ≤ k % p ^ i + (N - k) % p ^ i then 1 else 0) + (a - 1) / p ^ i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        rcases H i hi.1 (by omega) with hleft | hcarry
        · have hppos : 0 < p ^ i := pow_pos hp.out.pos i
          have hd : 1 ≤ (a - 1) / p ^ i := Nat.div_pos hleft hppos
          exact le_trans hd (Nat.le_add_left _ _)
        · rw [if_pos hcarry]; exact Nat.le_add_right 1 _
    _ ≤ ∑ i ∈ Finset.Ico 1 B,
          ((if p ^ i ≤ k % p ^ i + (N - k) % p ^ i then 1 else 0) + (a - 1) / p ^ i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _; exact Nat.zero_le _

/-- The main divisibility, reduced to naturals. -/
lemma keydvd_nat {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ}
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hres : ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i) :
    p ^ E ∣ (a - 1).factorial * Nat.choose N (M - b) := by
  have hchoose_pos : 0 < Nat.choose N (M - b) := Nat.choose_pos hkN
  have hprodpos : 0 < (a - 1).factorial * Nat.choose N (M - b) :=
    Nat.mul_pos (Nat.factorial_pos _) hchoose_pos
  rw [padicValNat_dvd_iff_le hprodpos.ne']
  rw [padicValNat.mul (Nat.factorial_pos _).ne' hchoose_pos.ne', Nat.add_comm]
  apply count_bound hkN
  intro i hi1 hiE
  by_cases hlt : p ^ i ≤ a - 1
  · exact Or.inl hlt
  · right
    push_neg at hlt
    have hai : a ≤ p ^ i := by omega
    have hbm : b < p ^ i := by omega
    have hmM : p ^ i ∣ M := (pow_dvd_pow p hiE).trans hpEM
    have hkval : ((M - b : ℕ) : ℤ) = (M : ℤ) - (b : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hbM)]
    have hkm : (M - b) % p ^ i = p ^ i - b := by
      apply resmod
      · omega
      · rw [Int.modEq_iff_dvd]
        rw [Nat.cast_sub (le_of_lt hbm), hkval]
        have : ((p : ℤ) ^ i - (b : ℤ)) - ((M : ℤ) - (b : ℤ)) = (p : ℤ) ^ i - (M : ℤ) := by
          push_cast; ring
        rw [show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring, this]
        exact dvd_sub (dvd_refl _) (by exact_mod_cast hmM)
    have hres_i := hres i hi1 hiE hai
    omega

/-- Integer version of the reduced divisibility. -/
lemma core_int {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ}
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hres : ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i) :
    (p : ℤ) ^ E ∣ ((a - 1).factorial : ℤ) * (Nat.choose N (M - b) : ℤ) := by
  have hnat := keydvd_nat hpEM hb hab hbM hkN hres
  have : ((p ^ E : ℕ) : ℤ) ∣ (((a - 1).factorial * Nat.choose N (M - b) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hnat
  rw [Nat.cast_mul] at this
  rwa [show ((p ^ E : ℕ) : ℤ) = (p : ℤ) ^ E by push_cast; ring] at this

/-- Residue bound in the direct case (top `= A·M − a ≥ 0`). -/
lemma res_pos {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ} (A : ℤ)
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hNval : (N : ℤ) = A * (M : ℤ) - (a : ℤ)) :
    ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i := by
  intro i hi1 hiE hai
  have hmM : p ^ i ∣ M := (pow_dvd_pow p hiE).trans hpEM
  have hbm : b < p ^ i := by omega
  have habm : a - b < p ^ i := by omega
  have hres : (N - (M - b)) % p ^ i = p ^ i - (a - b) := by
    apply resmod
    · omega
    · rw [Int.modEq_iff_dvd]
      have hdvd : ((p : ℤ) ^ i) ∣ (M : ℤ) := by exact_mod_cast hmM
      have e : ((p ^ i - (a - b) : ℕ) : ℤ) - ((N - (M - b) : ℕ) : ℤ)
          = (p : ℤ) ^ i - (A - 1) * (M : ℤ) := by
        rw [Nat.cast_sub (le_of_lt habm), Nat.cast_sub hkN, Nat.cast_sub (le_of_lt hbM),
          Nat.cast_sub (le_of_lt hab), hNval,
          show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring]
        ring
      rw [e, show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring]
      exact dvd_sub (dvd_refl _) (Dvd.dvd.mul_left hdvd (A - 1))
  omega

/-- Residue bound in the reflected case (top `= A·M − a < 0`). -/
lemma res_neg {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ} (A : ℤ)
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hNval : (N : ℤ) = (a : ℤ) - A * (M : ℤ) + (M : ℤ) - (b : ℤ) - 1) :
    ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i := by
  intro i hi1 hiE hai
  have hmM : p ^ i ∣ M := (pow_dvd_pow p hiE).trans hpEM
  have ha1 : a - 1 < p ^ i := by omega
  have hres : (N - (M - b)) % p ^ i = a - 1 := by
    apply resmod
    · omega
    · rw [Int.modEq_iff_dvd]
      have hdvd : ((p : ℤ) ^ i) ∣ (M : ℤ) := by exact_mod_cast hmM
      have e : ((a - 1 : ℕ) : ℤ) - ((N - (M - b) : ℕ) : ℤ) = A * (M : ℤ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub hkN, Nat.cast_sub (le_of_lt hbM),
          hNval]
        push_cast; ring
      rw [e, show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring]
      exact Dvd.dvd.mul_left hdvd A
  omega

/-- **Generalized Kummer bound.** -/
theorem GK (p : ℕ) (hp : p.Prime) (A : ℤ) (M : ℕ) (a b : ℕ) (hab : b < a) (hb : 0 < b) :
    (p:ℤ) ^ (padicValNat p M) ∣ ((a-1).factorial : ℤ) * Ring.choose (A * (M:ℤ) - a) (M - b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E := padicValNat p M with hE
  by_cases hE0 : E = 0
  · rw [hE0, pow_zero]; exact one_dvd _
  · have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · exfalso; apply hE0; rw [hE, h, padicValNat.zero]
      · exact h
    have hpEM : p ^ E ∣ M := by rw [hE]; exact pow_padicValNat_dvd
    by_cases hbM : b < M
    · by_cases hkN0 : (0 : ℤ) ≤ A * (M:ℤ) - (a:ℤ)
      · -- top ≥ 0
        set N := (A * (M:ℤ) - (a:ℤ)).toNat with hNdef
        have hNval : (N : ℤ) = A * (M:ℤ) - (a:ℤ) := Int.toNat_of_nonneg hkN0
        have hch : Ring.choose (A * (M:ℤ) - (a:ℤ)) (M - b) = (Nat.choose N (M - b) : ℤ) := by
          rw [← hNval, Ring.choose_natCast]
        rw [hch]
        by_cases hkN : M - b ≤ N
        · exact core_int hpEM hb hab hbM hkN (res_pos A hpEM hb hab hbM hkN hNval)
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]; exact dvd_zero _
      · -- top < 0
        push_neg at hkN0
        set N := ((a:ℤ) - A * (M:ℤ) + (M:ℤ) - (b:ℤ) - 1).toNat with hNdef
        have hbMz : (b:ℤ) < (M:ℤ) := by exact_mod_cast hbM
        have hpos : (0:ℤ) ≤ (a:ℤ) - A * (M:ℤ) + (M:ℤ) - (b:ℤ) - 1 := by linarith
        have hNval : (N : ℤ) = (a:ℤ) - A * (M:ℤ) + (M:ℤ) - (b:ℤ) - 1 :=
          Int.toNat_of_nonneg hpos
        have hch : Ring.choose (A * (M:ℤ) - (a:ℤ)) (M - b)
            = (Int.negOnePow ((M - b : ℕ) : ℤ) : ℤ) * (Nat.choose N (M - b) : ℤ) := by
          have h1 : A * (M:ℤ) - (a:ℤ) = -((a:ℤ) - A * (M:ℤ)) := by ring
          rw [h1, Ring.choose_neg]
          have h2 : (a:ℤ) - A * (M:ℤ) + ((M - b : ℕ):ℤ) - 1 = (N:ℤ) := by
            rw [hNval, Nat.cast_sub (le_of_lt hbM)]; ring
          rw [h2, Ring.choose_natCast, Units.smul_def, smul_eq_mul]
        rw [hch]
        by_cases hkN : M - b ≤ N
        · have hcore := core_int hpEM hb hab hbM hkN (res_neg A hpEM hb hab hbM hkN hNval)
          have hmul := hcore.mul_left (Int.negOnePow ((M - b : ℕ) : ℤ) : ℤ)
          rw [show ((a-1).factorial : ℤ) * ((Int.negOnePow ((M - b : ℕ) : ℤ):ℤ) * (Nat.choose N (M-b):ℤ))
              = (Int.negOnePow ((M - b : ℕ) : ℤ):ℤ) * (((a-1).factorial:ℤ) * (Nat.choose N (M-b):ℤ)) by ring]
          exact hmul
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
          exact dvd_zero _
    · -- b ≥ M, so M - b = 0
      have hk0 : M - b = 0 := by omega
      rw [hk0, Ring.choose_zero_right, mul_one]
      have hMfac : M ∣ (a-1).factorial := Nat.dvd_factorial hM (by omega)
      have hfin : p ^ E ∣ (a-1).factorial := hpEM.trans hMfac
      exact_mod_cast hfin

#print axioms GK
