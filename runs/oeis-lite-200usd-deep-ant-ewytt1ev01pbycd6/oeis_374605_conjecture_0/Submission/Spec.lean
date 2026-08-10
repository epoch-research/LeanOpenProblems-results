import FormalConjectures.Util.ProblemImports

/- ===== From Base1.lean ===== -/

open Finset in
def T (n k : ℕ) : ℕ :=
  (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def aa (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => T n k

open Finset

-- Nilpotent product expansion: if t^2 = 0 then ∏ (a i + t) = ∏ a i + t * ∑_j ∏_{i≠j} a i
theorem prod_add_nilpotent {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (t : R) (ht : t ^ 2 = 0) (a : ι → R) (s : Finset ι) :
    (∏ i ∈ s, (a i + t)) = (∏ i ∈ s, a i) + t * (∑ j ∈ s, ∏ i ∈ s.erase j, a i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert j₀ s hj₀ ih =>
    rw [Finset.prod_insert hj₀, ih, Finset.prod_insert hj₀, Finset.sum_insert hj₀]
    have e0 : (insert j₀ s).erase j₀ = s := Finset.erase_insert hj₀
    have key : ∀ j ∈ s, ∏ i ∈ (insert j₀ s).erase j, a i
        = a j₀ * ∏ i ∈ s.erase j, a i := by
      intro j hj
      have hne : j₀ ≠ j := by rintro rfl; exact hj₀ hj
      rw [Finset.erase_insert_of_ne hne,
        Finset.prod_insert (fun h => hj₀ (Finset.mem_of_mem_erase h))]
    rw [e0, Finset.sum_congr rfl key, ← Finset.mul_sum]
    linear_combination (∑ j ∈ s, ∏ i ∈ s.erase j, a i) * ht

lemma invsum_univ (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have hb := Equiv.sum_comp (inv_involutive (G := ZMod p)).toPerm (fun x : ZMod p => x⁻¹)
  simp only [Function.Involutive.coe_toPerm, inv_inv] at hb
  rw [← hb]
  have : ∑ x : ZMod p, x = ∑ x : ZMod p, x ^ 1 := by simp
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1 (by rw [hcard]; omega)
  simpa using this

lemma invsum_range (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ∑ j ∈ Finset.range (p - 1), (1 + (j : ZMod p))⁻¹ = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  rw [← invsum_univ p hp3, ← Finset.sum_erase Finset.univ (by simp : (0 : ZMod p)⁻¹ = 0)]
  have hp0 : 0 < p := by omega
  refine Finset.sum_bij (fun j _ => (1 + (j : ZMod p))) ?_ ?_ ?_ ?_
  · -- maps into univ.erase 0
    intro j hj
    dsimp only
    rw [Finset.mem_range] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    have : (1 + (j : ZMod p)) = ((1 + j : ℕ) : ZMod p) := by push_cast; ring
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · -- injective
    intro j₁ h₁ j₂ h₂ heq
    dsimp only at heq
    rw [Finset.mem_range] at h₁ h₂
    have : ((j₁ : ℕ) : ZMod p) = ((j₂ : ℕ) : ZMod p) := by
      rw [add_right_inj] at heq; exact heq
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · -- surjective
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hb0, _⟩ := hb
    have hval0 : b.val ≠ 0 := fun h => hb0 ((ZMod.val_eq_zero b).mp h)
    refine ⟨b.val - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hlt := ZMod.val_lt b
      omega
    · dsimp only
      have : ((b.val - 1 : ℕ) : ZMod p) = (b.val : ZMod p) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ b.val)]; ring
      rw [this]
      rw [ZMod.natCast_zmod_val]
      ring
  · intro j hj
    rfl

-- the (p-2)-th elementary symmetric of {1,...,p-1} is divisible by p
lemma pdvdE (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    p ∣ ∑ j ∈ Finset.range (p - 1), ∏ i ∈ (Finset.range (p - 1)).erase j, (1 + i) := by
  haveI : NeZero p := ⟨by omega⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have hne : ∀ j ∈ Finset.range (p - 1), (1 + (j : ZMod p)) ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : (1 + (j : ZMod p)) = ((1 + j : ℕ) : ZMod p) := by push_cast; ring
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hP : ∀ j ∈ Finset.range (p - 1),
      ∏ i ∈ (Finset.range (p - 1)).erase j, (1 + (i : ZMod p))
      = (∏ i ∈ Finset.range (p - 1), (1 + (i : ZMod p))) * (1 + (j : ZMod p))⁻¹ := by
    intro j hj
    have hmul := Finset.mul_prod_erase (Finset.range (p - 1))
      (fun i => (1 + (i : ZMod p))) hj
    rw [← hmul, mul_right_comm, mul_inv_cancel₀ (hne j hj), one_mul]
  rw [Finset.sum_congr rfl hP, ← Finset.mul_sum, invsum_range p hp3, mul_zero]

lemma factA (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : ZMod (p ^ 2)) = 1 := by
  haveI : NeZero p := ⟨by omega⟩
  have hp0 : 0 < p := by omega
  -- integer identity
  have h1 : Nat.factorial (p - 1) * Nat.choose (3 * p - 1) (p - 1) = (2 * p + 1).ascFactorial (p - 1) := by
    have h := Nat.ascFactorial_eq_factorial_mul_choose (2 * p) (p - 1)
    rw [h]
    congr 2
    omega
  have h2 : (2 * p + 1).ascFactorial (p - 1)
      = ∏ i ∈ Finset.range (p - 1), (2 * p + 1 + i) := by
    rw [Nat.ascFactorial_eq_prod_range]
  -- cast to ZMod (p^2)
  set R := ZMod (p ^ 2)
  have h3 : (Nat.factorial (p - 1) : R) * ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : R)
      = ∏ i ∈ Finset.range (p - 1), ((2 * p + 1 + i : ℕ) : R) := by
    rw [← Nat.cast_prod, ← h2, ← h1]
    push_cast
    ring
  -- nilpotent expansion
  set t : R := ((2 * p : ℕ) : R) with ht_def
  have htsq : t ^ 2 = 0 := by
    have hcp : t ^ 2 = ((4 * p ^ 2 : ℕ) : R) := by
      rw [ht_def, ← Nat.cast_pow]; congr 1; ring
    rw [hcp, ZMod.natCast_eq_zero_iff]
    exact ⟨4, by ring⟩
  have hterm : ∀ i, ((2 * p + 1 + i : ℕ) : R) = ((1 + i : ℕ) : R) + t := by
    intro i; rw [ht_def]; push_cast; ring
  rw [Finset.prod_congr rfl (fun i _ => hterm i)] at h3
  rw [prod_add_nilpotent t htsq (fun i => ((1 + i : ℕ) : R)) (Finset.range (p - 1))] at h3
  -- ∏ (1+i) = (p-1)!
  have hprod : ∏ i ∈ Finset.range (p - 1), ((1 + i : ℕ) : R) = (Nat.factorial (p - 1) : R) := by
    rw [← Nat.cast_prod]
    congr 1
    rw [← Finset.prod_range_add_one_eq_factorial]
    apply Finset.prod_congr rfl
    intro i _; ring
  -- t * (sum) = 0
  have hsum0 : t * (∑ j ∈ Finset.range (p - 1),
      ∏ i ∈ (Finset.range (p - 1)).erase j, ((1 + i : ℕ) : R)) = 0 := by
    have hcast : (∑ j ∈ Finset.range (p - 1),
        ∏ i ∈ (Finset.range (p - 1)).erase j, ((1 + i : ℕ) : R))
        = ((∑ j ∈ Finset.range (p - 1),
            ∏ i ∈ (Finset.range (p - 1)).erase j, (1 + i) : ℕ) : R) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_prod]
    rw [hcast, ht_def, ← Nat.cast_mul]
    rw [ZMod.natCast_eq_zero_iff]
    obtain ⟨m, hm⟩ := pdvdE p (by omega)
    rw [hm]
    ring_nf
    exact ⟨2 * m, by ring⟩
  rw [hprod, hsum0, add_zero] at h3
  -- cancel unit (p-1)!
  have hpp : p.Prime := Fact.out
  have hunit : IsUnit ((Nat.factorial (p - 1) : ℕ) : R) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp, hpp.dvd_factorial]
    omega
  have := hunit.mul_left_cancel (a := (Nat.factorial (p - 1) : R))
    (b := ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : R)) (c := 1)
  rw [mul_one] at this
  exact this h3

lemma T0eq (p : ℕ) (hp5 : 5 ≤ p) : T (p - 1) 0 = Nat.choose (3 * p - 3) (p - 1) := by
  unfold T
  simp only [Nat.choose_zero_right, one_pow, mul_zero, add_zero, one_mul]
  congr 1
  omega

lemma T1eq (p : ℕ) (hp5 : 5 ≤ p) :
    T (p - 1) 1 = (p - 1) ^ 2 * p * Nat.choose (3 * p - 1) (p - 1) := by
  unfold T
  rw [Nat.choose_one_right (p - 1), Nat.choose_one_right (p - 1 + 1),
    show p - 1 + 1 = p by omega, show 3 * (p - 1) + 2 * 1 = 3 * p - 1 by omega]

-- Integer version of Fact (a)
lemma hC1dvd (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((p : ℤ)) ^ 2 ∣ (Nat.choose (3 * p - 1) (p - 1) : ℤ) - 1 := by
  have hz : (((Nat.choose (3 * p - 1) (p - 1) : ℤ) - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by
    push_cast
    rw [factA p hp5]
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  rwa [Nat.cast_pow] at hz

lemma huCoprime (p : ℕ) (hpp : p.Prime) (hp5 : 5 ≤ p) :
    IsCoprime ((p : ℤ) ^ 3) ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2)) := by
  have hu : (3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2) = (((3 * p - 1) * (3 * p - 2) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (show 1 ≤ 3 * p by omega), Nat.cast_sub (show 2 ≤ 3 * p by omega)]
    ring
  rw [hu, ← Nat.cast_pow, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  show Nat.Coprime (p ^ 3) ((3 * p - 1) * (3 * p - 2))
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.mul_right
  · rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro h
    have h2 : p ∣ 3 * p := dvd_mul_left p 3
    have h3 := Nat.dvd_sub h2 h
    rw [show 3 * p - (3 * p - 1) = 1 by omega] at h3
    have := Nat.le_of_dvd one_pos h3; omega
  · rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro h
    have h2 : p ∣ 3 * p := dvd_mul_left p 3
    have h3 := Nat.dvd_sub h2 h
    rw [show 3 * p - (3 * p - 2) = 2 by omega] at h3
    have := Nat.le_of_dvd (by omega) h3; omega

-- Fact (c): exact integer identity
lemma factC (p : ℕ) (hp5 : 5 ≤ p) :
    Nat.choose (3 * p - 3) (p - 1) * ((3 * p - 1) * (3 * p - 2))
    = Nat.choose (3 * p - 1) (p - 1) * ((2 * p) * (2 * p - 1)) := by
  have hK : 0 < Nat.factorial (p - 1) * Nat.factorial (2 * p - 2) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hK
  have eA := Nat.choose_mul_factorial_mul_factorial (show p - 1 ≤ 3 * p - 3 by omega)
  have eB := Nat.choose_mul_factorial_mul_factorial (show p - 1 ≤ 3 * p - 1 by omega)
  rw [show 3 * p - 3 - (p - 1) = 2 * p - 2 by omega] at eA
  rw [show 3 * p - 1 - (p - 1) = 2 * p by omega] at eB
  have hf1 : Nat.factorial (3 * p - 3) * ((3 * p - 1) * (3 * p - 2))
      = Nat.factorial (3 * p - 1) := by
    have e1 := Nat.mul_factorial_pred (show 3 * p - 1 ≠ 0 by omega)
    have e2 := Nat.mul_factorial_pred (show 3 * p - 2 ≠ 0 by omega)
    rw [show 3 * p - 1 - 1 = 3 * p - 2 by omega] at e1
    rw [show 3 * p - 2 - 1 = 3 * p - 3 by omega] at e2
    rw [← e1, ← e2]; ring
  have hf2 : Nat.factorial (2 * p) = (2 * p) * (2 * p - 1) * Nat.factorial (2 * p - 2) := by
    have e1 := Nat.mul_factorial_pred (show 2 * p ≠ 0 by omega)
    have e2 := Nat.mul_factorial_pred (show 2 * p - 1 ≠ 0 by omega)
    rw [show 2 * p - 1 - 1 = 2 * p - 2 by omega] at e2
    rw [← e1, ← e2]; ring
  calc Nat.choose (3 * p - 3) (p - 1) * ((3 * p - 1) * (3 * p - 2))
        * (Nat.factorial (p - 1) * Nat.factorial (2 * p - 2))
      = (Nat.choose (3 * p - 3) (p - 1) * Nat.factorial (p - 1) * Nat.factorial (2 * p - 2))
        * ((3 * p - 1) * (3 * p - 2)) := by ring
    _ = Nat.factorial (3 * p - 3) * ((3 * p - 1) * (3 * p - 2)) := by rw [eA]
    _ = Nat.factorial (3 * p - 1) := hf1
    _ = Nat.choose (3 * p - 1) (p - 1) * Nat.factorial (p - 1) * Nat.factorial (2 * p) := eB.symm
    _ = Nat.choose (3 * p - 1) (p - 1) * ((2 * p) * (2 * p - 1))
        * (Nat.factorial (p - 1) * Nat.factorial (2 * p - 2)) := by rw [hf2]; ring

-- C(p-1,k) ≡ (-1)^k mod p
lemma choose_pm (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ k, k ≤ p - 1 → (Nat.choose (p - 1) k : ZMod p) = (-1) ^ k := by
  haveI : NeZero p := ⟨by omega⟩
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hcast : (↑(Nat.choose (p - 1) (k + 1)) : ZMod p) * ((k : ZMod p) + 1)
        = (↑(Nat.choose (p - 1) k) : ZMod p) * (↑(p - 1 - k) : ZMod p) := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) (Nat.choose_succ_right_eq (p - 1) k)
      push_cast at h
      exact h
    have hp1k : (↑(p - 1 - k) : ZMod p) = -((k : ZMod p) + 1) := by
      have hsum : (p - 1 - k) + (k + 1) = p := by omega
      have h0 : (↑(p - 1 - k) : ZMod p) + ((k : ZMod p) + 1) = 0 := by
        have h := congrArg (Nat.cast : ℕ → ZMod p) hsum
        push_cast at h
        rw [ZMod.natCast_self] at h
        linear_combination h
      exact eq_neg_of_add_eq_zero_left h0
    rw [hp1k, ih (by omega)] at hcast
    have hknz : ((k : ZMod p) + 1) ≠ 0 := by
      have hh : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      push_cast at hh; exact hh
    apply mul_right_cancel₀ hknz
    rw [hcast]; ring

lemma lucasB (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    Nat.choose (p - 1 + k) (k - 1) ≡ 1 [MOD p] := by
  have e : p - 1 + k = (k - 1) + p := by omega
  rw [e]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := (k - 1) + p) (k := k - 1) (p := p)
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (show k - 1 < p by omega),
      Nat.add_div_right _ (show 0 < p by omega),
      Nat.div_eq_of_lt (show k - 1 < p by omega)] at h
  simpa using h

lemma lucasG (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    Nat.choose (3 * (p - 1) + 2 * k) p ≡ (3 * (p - 1) + 2 * k) / p [MOD p] := by
  have hp0 : 0 < p := by omega
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 3 * (p - 1) + 2 * k) (k := p) (p := p)
  rw [Nat.mod_self, Nat.div_self hp0] at h
  simpa using h

lemma modToZMod {p a b : ℕ} (h : a ≡ b [MOD p]) : (a : ZMod p) = (b : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

lemma interiorK (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    p ^ 2 ∣ T (p - 1) k ∧
    (2 * (k : ZMod p) * ((k : ZMod p) - 1)) * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod p)
      = (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨by omega⟩
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < p := by omega
  set N := 3 * (p - 1) + 2 * k with hN
  -- L1 : k * C(p-1+k, k) = p * C(p-1+k, k-1)
  have hL1 : k * Nat.choose (p - 1 + k) k = p * Nat.choose (p - 1 + k) (k - 1) := by
    have h2 := Nat.choose_succ_right_eq (p - 1 + k) (k - 1)
    rw [show (k - 1) + 1 = k by omega, show (p - 1 + k) - (k - 1) = p by omega] at h2
    rw [Nat.mul_comm k, Nat.mul_comm p]; exact h2
  have hpdvdC : p ∣ Nat.choose (p - 1 + k) k := by
    have hh : p ∣ k * Nat.choose (p - 1 + k) k := ⟨_, hL1⟩
    rcases hpp.dvd_mul.mp hh with h | h
    · exfalso; have := Nat.le_of_dvd (by omega) h; omega
    · exact h
  -- L3 : p * C(N, p) = C(N, p-1) * (2*(p-1+k))
  have hL3 : p * Nat.choose N p = Nat.choose N (p - 1) * (2 * (p - 1 + k)) := by
    have h2 := Nat.choose_succ_right_eq N (p - 1)
    rw [show (p - 1) + 1 = p by omega, show N - (p - 1) = 2 * (p - 1 + k) by rw [hN]; omega] at h2
    rw [Nat.mul_comm p]; exact h2
  have hpdvdD : p ∣ Nat.choose N (p - 1) := by
    have hh : p ∣ Nat.choose N (p - 1) * (2 * (p - 1 + k)) := ⟨_, hL3.symm⟩
    rcases hpp.dvd_mul.mp hh with h | h
    · exact h
    · exfalso
      rcases hpp.dvd_mul.mp h with h2 | h2
      · have := Nat.le_of_dvd (by omega) h2; omega
      · have h3 := Nat.dvd_sub h2 (dvd_refl p)
        rw [show (p - 1 + k) - p = k - 1 by omega] at h3
        have := Nat.le_of_dvd (by omega) h3; omega
  obtain ⟨a, ha⟩ := hpdvdC
  obtain ⟨d, hd⟩ := hpdvdD
  -- factorization of T
  have hT : T (p - 1) k = p ^ 2 * (Nat.choose (p - 1) k ^ 2 * a * d) := by
    unfold T
    rw [← hN, ha, hd]; ring
  have hWval : (T (p - 1) k / p ^ 2 : ℕ) = Nat.choose (p - 1) k ^ 2 * a * d := by
    rw [hT, Nat.mul_div_cancel_left _ (show 0 < p ^ 2 by positivity)]
  -- ZMod facts
  have hka : (k : ZMod p) * (a : ZMod p) = 1 := by
    have hka_nat : k * a = Nat.choose (p - 1 + k) (k - 1) := by
      have : p * (k * a) = p * Nat.choose (p - 1 + k) (k - 1) := by rw [← hL1, ha]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hka_nat
    push_cast at h1
    rw [h1, modToZMod (lucasB p k hp5 hk2 hkp), Nat.cast_one]
  have hpm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod p) (show (p - 1) + 1 = p by omega)
    push_cast at h; rw [ZMod.natCast_self] at h
    exact eq_neg_of_add_eq_zero_left h
  have hpk1 : ((p - 1 : ℕ) : ZMod p) + (k : ZMod p) = (k : ZMod p) - 1 := by
    rw [hpm1]; ring
  have hd_zmod : 2 * ((k : ZMod p) - 1) * (d : ZMod p) = (((N / p) : ℕ) : ZMod p) := by
    have hd_nat : Nat.choose N p = d * (2 * (p - 1 + k)) := by
      have : p * Nat.choose N p = p * (d * (2 * (p - 1 + k))) := by rw [hL3, hd]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hd_nat
    have hg := lucasG p k hp5
    rw [← hN] at hg
    rw [modToZMod hg] at h1
    push_cast at h1
    rw [hpk1] at h1
    rw [h1]; ring
  have hC2 : ((Nat.choose (p - 1) k : ZMod p)) ^ 2 = 1 := by
    rw [choose_pm p hp5 k hkp, ← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  refine ⟨⟨_, hT⟩, ?_⟩
  rw [hWval]
  push_cast
  calc 2 * (k : ZMod p) * ((k : ZMod p) - 1)
        * ((↑(Nat.choose (p - 1) k)) ^ 2 * (a : ZMod p) * (d : ZMod p))
      = (↑(Nat.choose (p - 1) k)) ^ 2 * ((k : ZMod p) * (a : ZMod p))
        * (2 * ((k : ZMod p) - 1) * (d : ZMod p)) := by ring
    _ = 1 * 1 * (((N / p) : ℕ) : ZMod p) := by rw [hC2, hka, hd_zmod]
    _ = (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) := by rw [hN]; ring

lemma per_k (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod p)
      = (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p)
        * (((k - 1 : ℕ) : ZMod p)⁻¹ - ((k : ℕ) : ZMod p)⁻¹) := by
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨_, hk_eq⟩ := interiorK p k hp5 hk2 hkp
  have hkne : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hk1ne : ((k - 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hk1eq : ((k - 1 : ℕ) : ZMod p) = (k : ZMod p) - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring
  rw [← hk1eq] at hk_eq
  rw [inv_sub_inv hk1ne hkne]
  have hkk : (k : ZMod p) - ((k - 1 : ℕ) : ZMod p) = 1 := by rw [hk1eq]; ring
  rw [hkk, mul_one_div, eq_div_iff (mul_ne_zero hk1ne hkne), ← hk_eq]; ring

lemma teleIco {p : ℕ} (g : ℕ → ZMod p) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (g (k - 1) - g k) = g (a - 1) - g (b - 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcong : ∀ i ∈ Finset.range (b - a),
      g (a + i - 1) - g (a + i) = g (a - 1 + i) - g (a - 1 + (i + 1)) := by
    intro i _
    rw [show a + i - 1 = a - 1 + i by omega, show a + i = a - 1 + (i + 1) by omega]
  rw [Finset.sum_congr rfl hcong, Finset.sum_range_sub' (fun j => g (a - 1 + j)) (b - a)]
  simp only [Nat.add_zero]
  rw [show a - 1 + (b - a) = b - 1 by omega]

lemma sumW (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 2 p, 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod p) = 9 := by
  haveI : NeZero p := ⟨by omega⟩
  have hpp : p.Prime := Fact.out
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two (by omega))
  set c := (p + 3) / 2 with hc
  set g : ℕ → ZMod p := fun j => ((j : ℕ) : ZMod p)⁻¹ with hg
  -- rewrite each term via per_k
  have hterm : ∀ k ∈ Finset.Ico 2 p, 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod p)
      = (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) * (g (k - 1) - g k) := by
    intro k hk; rw [Finset.mem_Ico] at hk
    exact per_k p k hp5 (by omega) (by omega)
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_Ico_consecutive
      (fun k => (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) * (g (k - 1) - g k))
      (show (2 : ℕ) ≤ c by omega) (show c ≤ p by omega)]
  -- region A
  have hAsum : ∑ k ∈ Finset.Ico 2 c,
      (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) * (g (k - 1) - g k)
      = 3 * (g 1 - g (c - 1)) := by
    have h1 : ∀ k ∈ Finset.Ico 2 c,
        (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) * (g (k - 1) - g k)
        = (3 : ZMod p) * (g (k - 1) - g k) := by
      intro k hk; rw [Finset.mem_Ico] at hk
      rw [show (3 * (p - 1) + 2 * k) / p = 3 from Nat.div_eq_of_lt_le (by omega) (by omega)]
      norm_num
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
      teleIco g 2 c (by omega) (by omega)]
  have hBsum : ∑ k ∈ Finset.Ico c p,
      (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) * (g (k - 1) - g k)
      = 4 * (g (c - 1) - g (p - 1)) := by
    have h1 : ∀ k ∈ Finset.Ico c p,
        (((3 * (p - 1) + 2 * k) / p : ℕ) : ZMod p) * (g (k - 1) - g k)
        = (4 : ZMod p) * (g (k - 1) - g k) := by
      intro k hk; rw [Finset.mem_Ico] at hk
      rw [show (3 * (p - 1) + 2 * k) / p = 4 from Nat.div_eq_of_lt_le (by omega) (by omega)]
      norm_num
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
      teleIco g c p (by omega) (by omega)]
  rw [hAsum, hBsum]
  -- evaluate g at endpoints
  have hpm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod p) (show (p - 1) + 1 = p by omega)
    push_cast at h; rw [ZMod.natCast_self] at h
    exact eq_neg_of_add_eq_zero_left h
  have hg1 : g 1 = 1 := by simp only [hg]; simp
  have hgp : g (p - 1) = -1 := by
    simp only [hg]; rw [hpm1, inv_neg, inv_one]
  have hgc : g (c - 1) = 2 := by
    have hc1 : (c - 1) * 2 = p + 1 := by omega
    have hmul : ((c - 1 : ℕ) : ZMod p) * 2 = 1 := by
      have e : ((c - 1 : ℕ) : ZMod p) * 2 = (((c - 1) * 2 : ℕ) : ZMod p) := by push_cast; ring
      rw [e, hc1]; push_cast; rw [ZMod.natCast_self]; ring
    simp only [hg]; exact inv_eq_of_mul_eq_one_right hmul
  rw [hg1, hgp, hgc]; ring

-- p * C1 ≡ p mod p^3
lemma hpC (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ℤ) * (Nat.choose (3 * p - 1) (p - 1) : ℤ) ≡ (p : ℤ) [ZMOD (p : ℤ) ^ 3] := by
  obtain ⟨m, hm⟩ := hC1dvd p hp5
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  have hval : (Nat.choose (3 * p - 1) (p - 1) : ℤ) = 1 + (p : ℤ) ^ 2 * m := by linarith [hm]
  rw [hval]; ring

lemma T1cong (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    2 * (T (p - 1) 1 : ℤ) ≡ 2 * (p : ℤ) - 4 * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
  have hcast : (T (p - 1) 1 : ℤ)
      = ((p : ℤ) - 1) ^ 2 * p * (Nat.choose (3 * p - 1) (p - 1) : ℤ) := by
    rw [T1eq p hp5]; push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; ring
  rw [hcast]
  have h1 : 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) * (Nat.choose (3 * p - 1) (p - 1) : ℤ))
      ≡ 2 * ((p : ℤ) - 1) ^ 2 * (p : ℤ) [ZMOD (p : ℤ) ^ 3] :=
    (hpC p hp5).mul_left _
  have h2 : 2 * ((p : ℤ) - 1) ^ 2 * (p : ℤ)
      ≡ 2 * (p : ℤ) - 4 * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-2, by ring⟩
  calc 2 * (((p : ℤ) - 1) ^ 2 * p * (Nat.choose (3 * p - 1) (p - 1) : ℤ))
      = 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) * (Nat.choose (3 * p - 1) (p - 1) : ℤ)) := by ring
    _ ≡ 2 * ((p : ℤ) - 1) ^ 2 * (p : ℤ) [ZMOD (p : ℤ) ^ 3] := h1
    _ ≡ 2 * (p : ℤ) - 4 * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := h2

lemma T0cong (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    2 * (T (p - 1) 0 : ℤ) ≡ -2 * (p : ℤ) - 5 * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
  have hpp : p.Prime := Fact.out
  rw [T0eq p hp5]
  set C0 : ℤ := (Nat.choose (3 * p - 3) (p - 1) : ℤ) with hC0
  set C1 : ℤ := (Nat.choose (3 * p - 1) (p - 1) : ℤ) with hC1
  have hfc : C0 * ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2))
      = C1 * ((2 * (p : ℤ)) * (2 * (p : ℤ) - 1)) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) (factC p hp5)
    push_cast [Nat.cast_sub (show 1 ≤ 3 * p by omega), Nat.cast_sub (show 2 ≤ 3 * p by omega),
      Nat.cast_sub (show 1 ≤ 2 * p by omega)] at h
    rw [hC0, hC1]; linear_combination h
  obtain ⟨m, hm⟩ := hC1dvd p hp5
  have hC1val : C1 = 1 + (p : ℤ) ^ 2 * m := by rw [hC1]; linarith [hm]
  have hDu : (2 * C0 + 2 * (p : ℤ) + 5 * (p : ℤ) ^ 2)
      * ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2))
      = (p : ℤ) ^ 3 * (-27 + 45 * (p : ℤ) + 8 * (p : ℤ) * m - 4 * m) := by
    have e : (2 * C0 + 2 * (p : ℤ) + 5 * (p : ℤ) ^ 2)
        * ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2))
        = 2 * (C0 * ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2)))
          + (2 * (p : ℤ) + 5 * (p : ℤ) ^ 2) * ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2)) := by ring
    rw [e, hfc, hC1val]; ring
  have hdvd : (p : ℤ) ^ 3 ∣ (2 * C0 + 2 * (p : ℤ) + 5 * (p : ℤ) ^ 2) := by
    apply (huCoprime p hpp hp5).dvd_of_dvd_mul_right
    rw [hDu]; exact dvd_mul_right _ _
  rw [Int.modEq_iff_dvd]
  rw [show -2 * (p : ℤ) - 5 * (p : ℤ) ^ 2 - 2 * C0
      = -(2 * C0 + 2 * (p : ℤ) + 5 * (p : ℤ) ^ 2) by ring]
  exact (dvd_neg).mpr hdvd

lemma haa (p : ℕ) (hp5 : 5 ≤ p) :
    aa (p - 1) = T (p - 1) 0 + T (p - 1) 1 + ∑ k ∈ Finset.Ico 2 p, T (p - 1) k := by
  unfold aa
  rw [show (p - 1) + 1 = p by omega, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun k => T (p - 1) k)
        (show (0 : ℕ) ≤ 2 by omega) (show (2 : ℕ) ≤ p by omega)]
  rw [show Finset.Ico 0 2 = ({0, 1} : Finset ℕ) by decide,
      Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]

theorem base1 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : (p ^ 3 : ℕ) ∣ aa (p - 1) := by
  haveI := Fact.mk hp
  set M : ℕ := ∑ k ∈ Finset.Ico 2 p, (T (p - 1) k / p ^ 2) with hM
  -- Σ T_k = p^2 * M
  have hSeq : ∑ k ∈ Finset.Ico 2 p, T (p - 1) k = p ^ 2 * M := by
    rw [hM, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_Ico] at hk
    obtain ⟨hdvd, _⟩ := interiorK p k hp5 (by omega) (by omega)
    rw [Nat.mul_div_cancel' hdvd]
  -- 2*M ≡ 9 mod p
  have h2M9 : ((2 * M : ℕ) : ZMod p) = 9 := by
    have hcast : ((2 * M : ℕ) : ZMod p)
        = ∑ k ∈ Finset.Ico 2 p, 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod p) := by
      rw [hM]; push_cast; rw [Finset.mul_sum]
    rw [hcast]; exact sumW p hp5
  have h2Mmod : 2 * M ≡ 9 [MOD p] := by
    have : ((2 * M : ℕ) : ZMod p) = ((9 : ℕ) : ZMod p) := by rw [h2M9]; norm_num
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have h2Mdvd : (p : ℤ) ∣ (9 : ℤ) - 2 * (M : ℤ) := by
    have h := Nat.modEq_iff_dvd.mp h2Mmod
    push_cast at h; exact h
  -- 2*S ≡ 9p^2 mod p^3
  have hSZ : (∑ k ∈ Finset.Ico 2 p, (T (p - 1) k : ℤ)) = (p : ℤ) ^ 2 * (M : ℤ) := by
    rw [← Nat.cast_sum, hSeq]; push_cast; ring
  have hS : 2 * (∑ k ∈ Finset.Ico 2 p, (T (p - 1) k : ℤ)) ≡ 9 * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
    rw [hSZ, Int.modEq_iff_dvd]
    obtain ⟨t, ht⟩ := h2Mdvd
    exact ⟨t, by linear_combination (p : ℤ) ^ 2 * ht⟩
  -- combine
  have hkey : 2 * (aa (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 3] := by
    have haaZ : (aa (p - 1) : ℤ)
        = (T (p - 1) 0 : ℤ) + (T (p - 1) 1 : ℤ) + (∑ k ∈ Finset.Ico 2 p, (T (p - 1) k : ℤ)) := by
      rw [haa p hp5]; push_cast; ring
    have hsum := ((T0cong p hp5).add (T1cong p hp5)).add hS
    have hz : (-2 * (p : ℤ) - 5 * (p : ℤ) ^ 2 + (2 * (p : ℤ) - 4 * (p : ℤ) ^ 2)) + 9 * (p : ℤ) ^ 2
        = 0 := by ring
    rw [hz] at hsum
    have he : 2 * (aa (p - 1) : ℤ) = 2 * (T (p - 1) 0 : ℤ) + 2 * (T (p - 1) 1 : ℤ)
        + 2 * (∑ k ∈ Finset.Ico 2 p, (T (p - 1) k : ℤ)) := by rw [haaZ]; ring
    rw [he]; exact hsum
  -- conclude
  have hdvdZ : (p : ℤ) ^ 3 ∣ 2 * (aa (p - 1) : ℤ) := by
    have := (Int.modEq_iff_dvd.mp hkey)
    simpa using this
  have hnat : (p ^ 3 : ℕ) ∣ 2 * aa (p - 1) := by
    have : ((p ^ 3 : ℕ) : ℤ) ∣ ((2 * aa (p - 1) : ℕ) : ℤ) := by push_cast; exact hdvdZ
    exact_mod_cast this
  have hcop : Nat.Coprime (p ^ 3) 2 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  exact hcop.dvd_of_dvd_mul_left hnat
/- ===== From AARec.lean ===== -/

def Sc (x : ℤ) : ℤ := 5616*x^4 + 14040*x^3 + 12915*x^2 + 5183*x + 770

def P11 (x : ℤ) : ℤ :=
  72783360*x^11 + 946183680*x^10 + 5506947648*x^9 + 18919626192*x^8
  + 42578365230*x^7 + 65816429067*x^6 + 71201437287*x^5 + 53826632241*x^4
  + 27825371259*x^3 + 9355168720*x^2 + 1839302884*x + 160171824

def cc2 (x : ℤ) : ℤ := 16*(x+2)^3*(4*x+5)^2*(4*x+7)^2*Sc x
def cc1 (x : ℤ) : ℤ := -36 * P11 x
def cc0 (x : ℤ) : ℤ := -27*(x+2)*(3*x+1)^3*(3*x+2)^3*Sc (x+1)

/-- Factorial closed form (cross-multiplied) for `T m k` when `k ≤ m`. -/
theorem Tfact (m k : ℕ) (h : k ≤ m) :
    T m k * ((Nat.factorial k)^3 * (Nat.factorial (m-k))^2 * Nat.factorial (2*m+2*k))
      = Nat.factorial (m+k) * Nat.factorial (3*m+2*k) := by
  have h1 : Nat.choose m k * Nat.factorial k * Nat.factorial (m-k) = Nat.factorial m :=
    Nat.choose_mul_factorial_mul_factorial h
  have h2 : Nat.choose (m+k) k * Nat.factorial k * Nat.factorial m = Nat.factorial (m+k) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ m+k by omega)
    rwa [show m+k-k = m by omega] at this
  have h3 : Nat.choose (3*m+2*k) m * Nat.factorial m * Nat.factorial (2*m+2*k)
      = Nat.factorial (3*m+2*k) := by
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 3*m+2*k by omega)
    rwa [show 3*m+2*k-m = 2*m+2*k by omega] at this
  unfold T
  rw [← h2, ← h3, ← h1]
  ring

/-- Certificate polynomial coefficients (over ℤ). -/
def A3 (n : ℤ) : ℤ := -2*(n+2)*(7443918144*n^12+89116249248*n^11+477840074580*n^10+1516263919164*n^9+3169124935875*n^8+4594117665555*n^7+4735175091369*n^6+3496319453673*n^5+1835935007068*n^4+668997560020*n^3+160713656664*n^2+22879883456*n+1461816416)
def A4 (n : ℤ) : ℤ := -4*(5430851712*n^12+76404332160*n^11+478560783096*n^10+1764717701220*n^9+4266342913203*n^8+7122208462266*n^7+8416883932265*n^6+7094141090927*n^5+4232641509540*n^4+1743942444451*n^3+471297834004*n^2+75082696980*n+5339697360)
def A5 (n : ℤ) : ℤ := -2*(83700864*n^11+16982581824*n^10+177956884440*n^9+836257162176*n^8+2283369599763*n^7+3994731964001*n^6+4669388154027*n^5+3688720523319*n^4+1943489115054*n^3+653530537932*n^2+126705453624*n+10766446432)
def A6 (n : ℤ) : ℤ := 16*(655623072*n^10+6580177344*n^9+28502444970*n^8+69591754005*n^7+104774027786*n^6+99585074036*n^5+58138805400*n^4+18529114771*n^3+1748071108*n^2-604031484*n-137313264)
def A7 (n : ℤ) : ℤ := 8*(478084464*n^9+4884878232*n^8+21665145987*n^7+54638336225*n^6+86179658227*n^5+87993309183*n^4+58065207134*n^3+23852127404*n^2+5533215480*n+552935264)

/-- The certificate numerator `Pnum(n,k)`. -/
def PN (n k : ℤ) : ℤ := A3 n * k^3 + A4 n * k^4 + A5 n * k^5 + A6 n * k^6 + A7 n * k^7

/-- The telescoping term `g(n,k)` (over ℤ). -/
def gg (n k : ℕ) : ℤ :=
  PN n k * ((Nat.choose (n+2) k : ℤ))^2 * (Nat.choose (n+k) k) * (Nat.choose (3*n+2*k) n)

/-- Factorial expansion helpers. -/
lemma fj1 (a : ℕ) : Nat.factorial (a+1) = (a+1) * Nat.factorial a := Nat.factorial_succ a
lemma fj2 (a : ℕ) : Nat.factorial (a+2) = (a+2)*(a+1) * Nat.factorial a := by
  rw [Nat.factorial_succ (a+1), Nat.factorial_succ a]; ring
lemma fj3 (a : ℕ) : Nat.factorial (a+3) = (a+3)*(a+2)*(a+1) * Nat.factorial a := by
  rw [Nat.factorial_succ (a+2), Nat.factorial_succ (a+1), Nat.factorial_succ a]; ring
lemma fj4 (a : ℕ) : Nat.factorial (a+4) = (a+4)*(a+3)*(a+2)*(a+1) * Nat.factorial a := by
  rw [Nat.factorial_succ (a+3), Nat.factorial_succ (a+2), Nat.factorial_succ (a+1),
    Nat.factorial_succ a]; ring
lemma fj6 (a : ℕ) : Nat.factorial (a+6)
    = (a+6)*(a+5)*(a+4)*(a+3)*(a+2)*(a+1) * Nat.factorial a := by
  rw [Nat.factorial_succ (a+5), Nat.factorial_succ (a+4), Nat.factorial_succ (a+3),
    Nat.factorial_succ (a+2), Nat.factorial_succ (a+1), Nat.factorial_succ a]; ring

/-- Closed-form (cross-multiplied) core identity for the binomial part of `gg`. -/
theorem GGF_core (n k : ℕ) (h : k ≤ n+2) :
    (Nat.choose (n+2) k ^ 2 * Nat.choose (n+k) k * Nat.choose (3*n+2*k) n)
      * (Nat.factorial k ^ 3 * Nat.factorial (n+2-k) ^ 2 * Nat.factorial n ^ 2
          * Nat.factorial (2*n+2*k))
      = Nat.factorial (n+2) ^ 2 * Nat.factorial (n+k) * Nat.factorial (3*n+2*k) := by
  have c1 : Nat.choose (n+2) k * Nat.factorial k * Nat.factorial (n+2-k) = Nat.factorial (n+2) :=
    Nat.choose_mul_factorial_mul_factorial h
  have c2 : Nat.choose (n+k) k * Nat.factorial k * Nat.factorial n = Nat.factorial (n+k) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ n+k by omega)
    rwa [show n+k-k = n by omega] at this
  have c3 : Nat.choose (3*n+2*k) n * Nat.factorial n * Nat.factorial (2*n+2*k)
      = Nat.factorial (3*n+2*k) := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3*n+2*k by omega)
    rwa [show 3*n+2*k-n = 2*n+2*k by omega] at this
  rw [← c1, ← c2, ← c3]; ring

/-- Ratio identity relating `T (n+1) k` to `T n k`. -/
theorem RA (n k : ℕ) (h : k ≤ n) :
    (T (n+1) k : ℤ) * (((n:ℤ)+1-k)^2 * (2*(n:ℤ)+2*k+2) * (2*(n:ℤ)+2*k+1))
      = (T n k : ℤ) * (((n:ℤ)+1+k) * (3*(n:ℤ)+2*k+3) * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1)) := by
  have E1 := Tfact (n+1) k (by omega)
  have E0 := Tfact n k h
  rw [show n+1-k = (n-k)+1 by omega, fj1 (n-k),
      show 2*(n+1)+2*k = (2*n+2*k)+2 by ring, fj2 (2*n+2*k),
      show n+1+k = (n+k)+1 by ring, fj1 (n+k),
      show 3*(n+1)+2*k = (3*n+2*k)+3 by ring, fj3 (3*n+2*k)] at E1
  have Gz := congrArg (Nat.cast (R := ℤ)) E1
  have E0z := congrArg (Nat.cast (R := ℤ)) E0
  push_cast [Nat.cast_sub h] at Gz E0z
  have hk : (Nat.factorial k : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : (Nat.factorial (n-k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (Nat.factorial (2*n+2*k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcf := mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hk) (pow_ne_zero 2 hnk)) h2
  apply mul_right_cancel₀ hcf
  linear_combination Gz - (((n:ℤ)+1+k) * (3*(n:ℤ)+2*k+3) * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1)) * E0z

/-- Ratio identity relating `T (n+2) k` to `T n k`. -/
theorem RB (n k : ℕ) (h : k ≤ n) :
    (T (n+2) k : ℤ) * (((n:ℤ)+2-k)^2 * ((n:ℤ)+1-k)^2 * (2*(n:ℤ)+2*k+4) * (2*(n:ℤ)+2*k+3)
        * (2*(n:ℤ)+2*k+2) * (2*(n:ℤ)+2*k+1))
      = (T n k : ℤ) * (((n:ℤ)+2+k) * ((n:ℤ)+1+k) * (3*(n:ℤ)+2*k+6) * (3*(n:ℤ)+2*k+5)
        * (3*(n:ℤ)+2*k+4) * (3*(n:ℤ)+2*k+3) * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1)) := by
  have E1 := Tfact (n+2) k (by omega)
  have E0 := Tfact n k h
  rw [show n+2-k = (n-k)+2 by omega, fj2 (n-k),
      show 2*(n+2)+2*k = (2*n+2*k)+4 by ring, fj4 (2*n+2*k),
      show n+2+k = (n+k)+2 by ring, fj2 (n+k),
      show 3*(n+2)+2*k = (3*n+2*k)+6 by ring, fj6 (3*n+2*k)] at E1
  have Gz := congrArg (Nat.cast (R := ℤ)) E1
  have E0z := congrArg (Nat.cast (R := ℤ)) E0
  push_cast [Nat.cast_sub h] at Gz E0z
  have hk : (Nat.factorial k : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : (Nat.factorial (n-k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (Nat.factorial (2*n+2*k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcf := mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hk) (pow_ne_zero 2 hnk)) h2
  apply mul_right_cancel₀ hcf
  linear_combination Gz - (((n:ℤ)+2+k) * ((n:ℤ)+1+k) * (3*(n:ℤ)+2*k+6) * (3*(n:ℤ)+2*k+5)
        * (3*(n:ℤ)+2*k+4) * (3*(n:ℤ)+2*k+3) * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1)) * E0z

/-- Ratio identity relating `gg n k` to `T n k`. -/
theorem RC (n k : ℕ) (h : k ≤ n) :
    gg n k * (((n:ℤ)+2-k)^2 * ((n:ℤ)+1-k)^2)
      = (T n k : ℤ) * (PN n k * ((n:ℤ)+1)^2 * ((n:ℤ)+2)^2) := by
  have G := GGF_core n k (by omega)
  have E0 := Tfact n k h
  rw [show n+2-k = (n-k)+2 by omega, fj2 (n-k), fj2 n] at G
  have Gz := congrArg (Nat.cast (R := ℤ)) G
  have E0z := congrArg (Nat.cast (R := ℤ)) E0
  push_cast [Nat.cast_sub h] at Gz E0z
  have hk : (Nat.factorial k : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : (Nat.factorial (n-k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (Nat.factorial (2*n+2*k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hn : (Nat.factorial n : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hcf := mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hk) (pow_ne_zero 2 hnk)) h2)
    (pow_ne_zero 2 hn)
  have hcore : ((Nat.choose (n+2) k : ℤ)^2 * (Nat.choose (n+k) k) * (Nat.choose (3*n+2*k) n))
        * (((n:ℤ)+2-k)^2 * ((n:ℤ)+1-k)^2)
      = (T n k : ℤ) * (((n:ℤ)+1)^2 * ((n:ℤ)+2)^2) := by
    apply mul_right_cancel₀ hcf
    linear_combination Gz - (((n:ℤ)+1)^2 * ((n:ℤ)+2)^2 * (Nat.factorial n : ℤ)^2) * E0z
  unfold gg
  linear_combination (PN n k) * hcore

/-- Ratio identity relating `gg n (k+1)` to `T n k`. -/
theorem RD (n k : ℕ) (h : k ≤ n) :
    gg n (k+1) * (((k:ℤ)+1)^3 * ((n:ℤ)+1-k)^2 * (2*(n:ℤ)+2*k+2) * (2*(n:ℤ)+2*k+1))
      = (T n k : ℤ) * (PN n (k+1) * ((n:ℤ)+2)^2 * ((n:ℤ)+1)^2 * ((n:ℤ)+k+1)
          * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1)) := by
  have G := GGF_core n (k+1) (by omega)
  have E0 := Tfact n k h
  rw [fj1 k, show n+2-(k+1) = (n-k)+1 by omega, fj1 (n-k),
      show 2*n+2*(k+1) = (2*n+2*k)+2 by ring, fj2 (2*n+2*k), fj2 n,
      show n+(k+1) = (n+k)+1 by ring, fj1 (n+k),
      show 3*n+2*(k+1) = (3*n+2*k)+2 by ring, fj2 (3*n+2*k)] at G
  have Gz := congrArg (Nat.cast (R := ℤ)) G
  have E0z := congrArg (Nat.cast (R := ℤ)) E0
  push_cast [Nat.cast_sub h] at Gz E0z
  have hk : (Nat.factorial k : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : (Nat.factorial (n-k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (Nat.factorial (2*n+2*k) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hn : (Nat.factorial n : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hcf := mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hk) (pow_ne_zero 2 hnk)) h2)
    (pow_ne_zero 2 hn)
  have hcore : ((Nat.choose (n+2) (k+1) : ℤ)^2 * (Nat.choose (n+k+1) (k+1))
        * (Nat.choose (3*n+2*k+2) n))
        * (((k:ℤ)+1)^3 * ((n:ℤ)+1-k)^2 * (2*(n:ℤ)+2*k+2) * (2*(n:ℤ)+2*k+1))
      = (T n k : ℤ) * (((n:ℤ)+2)^2 * ((n:ℤ)+1)^2 * ((n:ℤ)+k+1)
          * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1)) := by
    apply mul_right_cancel₀ hcf
    linear_combination Gz - (((n:ℤ)+2)^2 * ((n:ℤ)+1)^2 * ((n:ℤ)+k+1)
        * (3*(n:ℤ)+2*k+2) * (3*(n:ℤ)+2*k+1) * (Nat.factorial n : ℤ)^2) * E0z
  unfold gg
  rw [show 3*n+2*(k+1) = 3*n+2*k+2 by ring, show n+(k+1) = n+k+1 by ring]
  push_cast
  linear_combination (PN (n:ℤ) ((k:ℤ)+1)) * hcore

/-- The key creative-telescoping identity `(*)`, valid for `k ≤ n`. -/
theorem star (n k : ℕ) (h : k ≤ n) :
    (cc2 n * (T (n+2) k : ℤ) + cc1 n * (T (n+1) k : ℤ) + cc0 n * (T n k : ℤ))
      * ((2*(k:ℤ)+2*n+1) * (2*(k:ℤ)+2*n+3) * ((n:ℤ)+1)^2 * ((n:ℤ)+2)^2)
      = gg n (k+1) * (2*(k:ℤ)+2*n+1) - gg n k * (2*(k:ℤ)+2*n+3) := by
  have hRA := RA n k h
  have hRB := RB n k h
  have hRC := RC n k h
  have hRD := RD n k h
  have hn0 : (0:ℤ) ≤ (n:ℤ) := Int.natCast_nonneg n
  have hk0 : (0:ℤ) ≤ (k:ℤ) := Int.natCast_nonneg k
  have hkn : (k:ℤ) ≤ (n:ℤ) := by exact_mod_cast h
  have e1 : ((n:ℤ)+2-k) ≠ 0 := by omega
  have e2 : ((n:ℤ)+1-k) ≠ 0 := by omega
  have e3 : ((n:ℤ)+k+1) ≠ 0 := by omega
  have e4 : ((n:ℤ)+k+2) ≠ 0 := by omega
  have e5 : (2*(n:ℤ)+2*k+1) ≠ 0 := by omega
  have e6 : (2*(n:ℤ)+2*k+3) ≠ 0 := by omega
  have e7 : ((k:ℤ)+1)^3 ≠ 0 := by positivity
  have hL : (4*((k:ℤ)+1)^3 * ((n:ℤ)+2-k)^2 * ((n:ℤ)+1-k)^2 * ((n:ℤ)+k+1) * ((n:ℤ)+k+2)
      * (2*(n:ℤ)+2*k+1) * (2*(n:ℤ)+2*k+3)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) e7) (pow_ne_zero 2 e1)) (pow_ne_zero 2 e2)) e3) e4) e5) e6
  apply mul_right_cancel₀ hL
  linear_combination (norm := (simp only [cc0, cc1, cc2, Sc, P11, PN, A3, A4, A5, A6, A7]; push_cast; ring1))
    (cc1 (n:ℤ) * ((2*(k:ℤ)+2*n+1)*(2*(k:ℤ)+2*n+3)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
        * (2*((k:ℤ)+1)^3*((n:ℤ)+2-k)^2*((n:ℤ)+k+2)*(2*(k:ℤ)+2*n+3))) * hRA
    + (cc2 (n:ℤ) * ((2*(k:ℤ)+2*n+1)*(2*(k:ℤ)+2*n+3)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
        * (((k:ℤ)+1)^3)) * hRB
    + ((2*(k:ℤ)+2*n+3) * (4*((k:ℤ)+1)^3*((n:ℤ)+k+1)*((n:ℤ)+k+2)*(2*(k:ℤ)+2*n+1)*(2*(k:ℤ)+2*n+3)))
        * hRC
    + (-(2*(k:ℤ)+2*n+1) * (2*((n:ℤ)+2-k)^2*((n:ℤ)+k+2)*(2*(k:ℤ)+2*n+3))) * hRD

/-- Boundary identity at `k = n+2`. -/
theorem starB2red (n : ℕ) :
    cc2 n * (T (n+2) (n+2) : ℤ) * ((4*(n:ℤ)+5)*(4*(n:ℤ)+7)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
      + gg n (n+2) * (4*(n:ℤ)+7) = 0 := by
  have T0 := Tfact (n+2) (n+2) (le_refl _)
  rw [show n+2-(n+2) = 0 by omega, Nat.factorial_zero,
      show 2*(n+2)+2*(n+2) = (4*n+4)+4 by ring, fj4 (4*n+4),
      show n+2+(n+2) = (2*n+2)+2 by ring, fj2 (2*n+2),
      show 3*(n+2)+2*(n+2) = (5*n+4)+6 by ring, fj6 (5*n+4),
      fj2 n] at T0
  have Tz := congrArg (Nat.cast (R := ℤ)) T0
  push_cast at Tz
  have B0 := GGF_core n (n+2) (by omega)
  rw [show n+2-(n+2) = 0 by omega, Nat.factorial_zero,
      show 2*n+2*(n+2) = 4*n+4 by ring,
      show n+(n+2) = 2*n+2 by ring,
      show 3*n+2*(n+2) = 5*n+4 by ring,
      fj2 n] at B0
  have Bz := congrArg (Nat.cast (R := ℤ)) B0
  push_cast at Bz
  have hF44 : (Nat.factorial (4*n+4) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hFn : (Nat.factorial n : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hM2 : (8*(Nat.factorial (4*n+4):ℤ)*(Nat.factorial n:ℤ)^5*((n:ℤ)+1)^3
      *((n:ℤ)+2)^4*(2*(n:ℤ)+3)*(4*(n:ℤ)+5)*(4*(n:ℤ)+7)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · norm_num
    · exact hF44
    · exact pow_ne_zero 5 hFn
    · positivity
    · positivity
    · positivity
    · positivity
    · positivity
  have key : (cc2 (n:ℤ) * (T (n+2) (n+2) : ℤ)
        * ((4*(n:ℤ)+5)*(4*(n:ℤ)+7)*((n:ℤ)+1)^2*((n:ℤ)+2)^2) + gg n (n+2) * (4*(n:ℤ)+7))
      * (8*(Nat.factorial (4*n+4):ℤ)*(Nat.factorial n:ℤ)^5*((n:ℤ)+1)^3
        *((n:ℤ)+2)^4*(2*(n:ℤ)+3)*(4*(n:ℤ)+5)*(4*(n:ℤ)+7)) = 0 := by
    unfold gg
    rw [show n+(n+2) = 2*n+2 by ring, show 3*n+2*(n+2) = 5*n+4 by ring]
    push_cast
    linear_combination (norm := (simp only [cc2, Sc, PN, A3, A4, A5, A6, A7]; push_cast; ring1))
      (16*(Nat.factorial n:ℤ)^2*((n:ℤ)+1)^2*((n:ℤ)+2)^5*(4*(n:ℤ)+5)^3*(4*(n:ℤ)+7)^3*Sc (n:ℤ)) * Tz
      + (-800*((n:ℤ)+1)*((n:ℤ)+2)^5*(2*(n:ℤ)+3)*(4*(n:ℤ)+5)^3*(4*(n:ℤ)+7)^3
          *(5*(n:ℤ)+6)*(5*(n:ℤ)+7)*(5*(n:ℤ)+8)*(5*(n:ℤ)+9)*Sc (n:ℤ)) * Bz
  exact (mul_eq_zero.mp key).resolve_right hM2

/-- Boundary identity at `k = n+1`. -/
theorem starB1red (n : ℕ) :
    cc2 n * (T (n+2) (n+1) : ℤ) * ((4*(n:ℤ)+3)*(4*(n:ℤ)+5)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
      + cc1 n * (T (n+1) (n+1) : ℤ) * ((4*(n:ℤ)+3)*(4*(n:ℤ)+5)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
      - (gg n (n+2) * (4*(n:ℤ)+3) - gg n (n+1) * (4*(n:ℤ)+5)) = 0 := by
  -- Tfact (n+2) (n+1)
  have T21 := Tfact (n+2) (n+1) (by omega)
  rw [show n+2-(n+1) = 1 by omega, Nat.factorial_one,
      show 2*(n+2)+2*(n+1) = (4*n+2)+4 by ring, fj4 (4*n+2),
      show n+2+(n+1) = (2*n+1)+2 by ring, fj2 (2*n+1),
      show 3*(n+2)+2*(n+1) = (5*n+2)+6 by ring, fj6 (5*n+2),
      fj1 n] at T21
  have Tz21 := congrArg (Nat.cast (R := ℤ)) T21
  push_cast at Tz21
  -- Tfact (n+1) (n+1)
  have T11 := Tfact (n+1) (n+1) (le_refl _)
  rw [show n+1-(n+1) = 0 by omega, Nat.factorial_zero,
      show 2*(n+1)+2*(n+1) = (4*n+2)+2 by ring, fj2 (4*n+2),
      show n+1+(n+1) = (2*n+1)+1 by ring, fj1 (2*n+1),
      show 3*(n+1)+2*(n+1) = (5*n+2)+3 by ring, fj3 (5*n+2),
      fj1 n] at T11
  have Tz11 := congrArg (Nat.cast (R := ℤ)) T11
  push_cast at Tz11
  -- GGF_core n (n+1)
  have B1 := GGF_core n (n+1) (by omega)
  rw [show n+2-(n+1) = 1 by omega, Nat.factorial_one,
      show 2*n+2*(n+1) = 4*n+2 by ring,
      show n+(n+1) = 2*n+1 by ring,
      show 3*n+2*(n+1) = 5*n+2 by ring,
      fj1 n, fj2 n] at B1
  have Bz1 := congrArg (Nat.cast (R := ℤ)) B1
  push_cast at Bz1
  -- GGF_core n (n+2)
  have B2 := GGF_core n (n+2) (by omega)
  rw [show n+2-(n+2) = 0 by omega, Nat.factorial_zero,
      show 2*n+2*(n+2) = (4*n+2)+2 by ring, fj2 (4*n+2),
      show n+(n+2) = (2*n+1)+1 by ring, fj1 (2*n+1),
      show 3*n+2*(n+2) = (5*n+2)+2 by ring, fj2 (5*n+2),
      fj2 n] at B2
  have Bz2 := congrArg (Nat.cast (R := ℤ)) B2
  push_cast at Bz2
  have hQ : (Nat.factorial (4*n+2) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hFn : (Nat.factorial n : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hM1 : (8*(Nat.factorial n:ℤ)^5*(Nat.factorial (4*n+2):ℤ)*((n:ℤ)+1)^4
      *((n:ℤ)+2)^3*(2*(n:ℤ)+3)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · norm_num
    · exact pow_ne_zero 5 hFn
    · exact hQ
    · positivity
    · positivity
    · positivity
    · positivity
    · positivity
  have key : (cc2 (n:ℤ) * (T (n+2) (n+1) : ℤ) * ((4*(n:ℤ)+3)*(4*(n:ℤ)+5)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
        + cc1 (n:ℤ) * (T (n+1) (n+1) : ℤ) * ((4*(n:ℤ)+3)*(4*(n:ℤ)+5)*((n:ℤ)+1)^2*((n:ℤ)+2)^2)
        - (gg n (n+2) * (4*(n:ℤ)+3) - gg n (n+1) * (4*(n:ℤ)+5)))
      * (8*(Nat.factorial n:ℤ)^5*(Nat.factorial (4*n+2):ℤ)*((n:ℤ)+1)^4
        *((n:ℤ)+2)^3*(2*(n:ℤ)+3)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)) = 0 := by
    unfold gg
    rw [show n+(n+1) = 2*n+1 by ring, show 3*n+2*(n+1) = 5*n+2 by ring,
        show n+(n+2) = (2*n+1)+1 by ring, show 3*n+2*(n+2) = (5*n+2)+2 by ring]
    push_cast
    linear_combination (norm := (simp only [cc2, cc1, Sc, P11, PN, A3, A4, A5, A6, A7]; push_cast; ring1))
      (16*(Nat.factorial n:ℤ)^2*((n:ℤ)+1)^2*((n:ℤ)+2)^8*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)^3*(4*(n:ℤ)+7)^2*Sc (n:ℤ)) * Tz21
      + (-72*(Nat.factorial n:ℤ)^2*((n:ℤ)+1)^2*((n:ℤ)+2)^5*(2*(n:ℤ)+3)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)^2*P11 (n:ℤ)) * Tz11
      + (-80*((n:ℤ)+1)^4*((n:ℤ)+2)^3*(2*(n:ℤ)+3)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)^2*(5*(n:ℤ)+3)*(5*(n:ℤ)+4)
          *(89856000*(n:ℤ)^11 + 1388275200*(n:ℤ)^10 + 9213580800*(n:ℤ)^9 + 35023498688*(n:ℤ)^8
            + 85213018968*(n:ℤ)^7 + 139805454174*(n:ℤ)^6 + 158154230555*(n:ℤ)^5 + 123520908104*(n:ℤ)^4
            + 65331247863*(n:ℤ)^3 + 22303203692*(n:ℤ)^2 + 4427032756*(n:ℤ) + 387603984)) * Bz1
      + (200*((n:ℤ)+1)*((n:ℤ)+2)^4*(2*(n:ℤ)+3)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)^3*(4*(n:ℤ)+7)
          *(5*(n:ℤ)+6)*(5*(n:ℤ)+7)*(5*(n:ℤ)+8)*(5*(n:ℤ)+9)*Sc (n:ℤ)) * Bz2
  exact (mul_eq_zero.mp key).resolve_right hM1

/-- `T m k = 0` when `m < k`. -/
theorem T_eq_zero (m k : ℕ) (h : m < k) : T m k = 0 := by
  unfold T
  rw [Nat.choose_eq_zero_of_lt h]; ring

/-- `gg n k = 0` when `n+2 < k`. -/
theorem gg_eq_zero (n k : ℕ) (h : n+2 < k) : gg n k = 0 := by
  unfold gg
  rw [Nat.choose_eq_zero_of_lt h]; push_cast; ring

/-- The key creative-telescoping identity, valid for ALL `k`. -/
theorem starAll (n k : ℕ) :
    (cc2 n * (T (n+2) k : ℤ) + cc1 n * (T (n+1) k : ℤ) + cc0 n * (T n k : ℤ))
      * ((2*(k:ℤ)+2*n+1) * (2*(k:ℤ)+2*n+3) * ((n:ℤ)+1)^2 * ((n:ℤ)+2)^2)
      = gg n (k+1) * (2*(k:ℤ)+2*n+1) - gg n k * (2*(k:ℤ)+2*n+3) := by
  rcases Nat.lt_or_ge k (n+1) with hkn | hkn
  · exact star n k (by omega)
  · rcases Nat.lt_or_ge k (n+3) with hk3 | hk3
    · have hk12 : k = n+1 ∨ k = n+2 := by omega
      rcases hk12 with rfl | rfl
      · -- k = n+1
        have hz : (T n (n+1) : ℤ) = 0 := by exact_mod_cast T_eq_zero n (n+1) (by omega)
        have hb := starB1red n
        rw [show n+1+1 = n+2 from rfl, hz]
        push_cast
        linear_combination hb
      · -- k = n+2
        have hz1 : (T (n+1) (n+2) : ℤ) = 0 := by exact_mod_cast T_eq_zero (n+1) (n+2) (by omega)
        have hz2 : (T n (n+2) : ℤ) = 0 := by exact_mod_cast T_eq_zero n (n+2) (by omega)
        have hz3 : gg n (n+3) = 0 := gg_eq_zero n (n+3) (by omega)
        have hb := starB2red n
        rw [show n+2+1 = n+3 from rfl, hz1, hz2, hz3]
        push_cast
        linear_combination hb
    · -- k ≥ n+3
      rw [T_eq_zero (n+2) k (by omega), T_eq_zero (n+1) k (by omega), T_eq_zero n k (by omega),
          gg_eq_zero n k (by omega), gg_eq_zero n (k+1) (by omega)]
      push_cast; ring

/-- The telescoping antidifference (over ℚ). -/
def G (n k : ℕ) : ℚ :=
  (gg n k : ℚ) / ((2*(k:ℚ)+2*(n:ℚ)+1) * ((n:ℚ)+1)^2 * ((n:ℚ)+2)^2)

theorem G_zero (n : ℕ) : G n 0 = 0 := by
  have h0 : gg n 0 = 0 := by unfold gg; simp [PN]
  unfold G; rw [h0]; simp

theorem G_top (n : ℕ) : G n (n+3) = 0 := by
  unfold G; rw [gg_eq_zero n (n+3) (by omega)]; simp

/-- The per-`k` telescoping step. -/
theorem hFG (n k : ℕ) :
    ((cc2 (n:ℤ) * (T (n+2) k : ℤ) + cc1 (n:ℤ) * (T (n+1) k : ℤ) + cc0 (n:ℤ) * (T n k : ℤ)) : ℚ)
      = G n (k+1) - G n k := by
  have hs := starAll n k
  have hsQ : ((cc2 (n:ℤ) * (T (n+2) k : ℤ) + cc1 (n:ℤ) * (T (n+1) k : ℤ)
        + cc0 (n:ℤ) * (T n k : ℤ)) : ℚ)
      * ((2*(k:ℚ)+2*(n:ℚ)+1) * (2*(k:ℚ)+2*(n:ℚ)+3) * ((n:ℚ)+1)^2 * ((n:ℚ)+2)^2)
      = ((gg n (k+1) : ℤ) : ℚ) * (2*(k:ℚ)+2*(n:ℚ)+1)
        - ((gg n k : ℤ) : ℚ) * (2*(k:ℚ)+2*(n:ℚ)+3) := by
    exact_mod_cast hs
  unfold G
  rw [div_sub_div _ _ (by positivity) (by positivity), eq_div_iff (by positivity)]
  push_cast
  push_cast at hsQ
  linear_combination ((n:ℚ)+1)^2*((n:ℚ)+2)^2 * hsQ

theorem aaSum2 (n : ℕ) :
    (∑ k ∈ Finset.range (n+3), (T (n+2) k : ℤ)) = (aa (n+2) : ℤ) := by
  unfold aa; rw [Nat.cast_sum]

theorem aaSum1 (n : ℕ) :
    (∑ k ∈ Finset.range (n+3), (T (n+1) k : ℤ)) = (aa (n+1) : ℤ) := by
  rw [show n+3 = (n+1+1)+1 from rfl, Finset.sum_range_succ,
      show T (n+1) (n+1+1) = 0 from T_eq_zero (n+1) (n+1+1) (by omega)]
  simp [aa, Nat.cast_sum]

theorem aaSum0 (n : ℕ) :
    (∑ k ∈ Finset.range (n+3), (T n k : ℤ)) = (aa n : ℤ) := by
  rw [show n+3 = (n+1+1)+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      show T n (n+1+1) = 0 from T_eq_zero n (n+1+1) (by omega),
      show T n (n+1) = 0 from T_eq_zero n (n+1) (by omega)]
  simp [aa, Nat.cast_sum]

theorem aa_rec (n : ℕ) :
    cc2 n * (aa (n+2) : ℤ) + cc1 n * (aa (n+1) : ℤ) + cc0 n * (aa n : ℤ) = 0 := by
  -- Sum of the per-`k` identity over ℚ telescopes.
  have sumQ : ∑ k ∈ Finset.range (n+3),
      ((cc2 (n:ℤ) * (T (n+2) k : ℤ) + cc1 (n:ℤ) * (T (n+1) k : ℤ)
        + cc0 (n:ℤ) * (T n k : ℤ)) : ℚ) = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => hFG n k)]
    rw [Finset.sum_range_sub (fun k => G n k) (n+3)]
    rw [G_top, G_zero]; ring
  -- Cast back to ℤ.
  have sumZ : ∑ k ∈ Finset.range (n+3),
      (cc2 (n:ℤ) * (T (n+2) k : ℤ) + cc1 (n:ℤ) * (T (n+1) k : ℤ)
        + cc0 (n:ℤ) * (T n k : ℤ)) = 0 := by
    exact_mod_cast sumQ
  rw [← aaSum2, ← aaSum1, ← aaSum0, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact sumZ


/-- Quotient in det_div_S. -/
def Qdet (x : ℤ) : ℤ :=
  1222933730623488*x^18 + 15286671632793600*x^17 + 84106679157043200*x^16
  + 265688045183139840*x^15 + 523535781572570880*x^14 + 642409842124787328*x^13
  + 427714287152625360*x^12 + 20326519267278480*x^11 + (-220633846931193120)*x^10
  + (-172535683330638720)*x^9 + (-30831512051943792)*x^8 + 29643757232746320*x^7
  + 19157762179670400*x^6 + 2811486865410720*x^5 + (-993323760615360)*x^4
  + (-369785522754432)*x^3 + (-8922594320640)*x^2 + 10147378913280*x + 1093691289600

theorem det_div_S (x : ℤ) : Sc x ∣ (cc1 x * cc1 (x-1) - cc0 x * cc2 (x-1)) :=
  ⟨Qdet x, by simp only [cc1, cc0, cc2, P11, Sc, Qdet]; ring⟩

def C0factor (x : ℤ) : ℤ := -27*(x+2)*(3*x+1)^3*(3*x+2)^3
theorem cc0_eq (x : ℤ) : cc0 x = C0factor x * Sc (x+1) := by
  unfold cc0 C0factor Sc; ring
def C2factor (x : ℤ) : ℤ := 16*(x+2)^3*(4*x+5)^2*(4*x+7)^2
theorem cc2_eq (x : ℤ) : cc2 x = C2factor x * Sc x := by
  unfold cc2 C2factor Sc; ring
/- ===== From Refine.lean ===== -/

open Finset

/-!
# Refinement supercongruence : aa(p-1) ≡ -p^3 mod p^4

This file proves `refine1 : (p:ℤ)^4 ∣ (aa (p-1) : ℤ) + p^3` for primes p ≥ 5,
strengthening `base1` (mod p^3) to mod p^4.
-/

/-- Second-order product expansion when `t^3 = 0`. -/
theorem two_prod {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (t : R) (ht : t ^ 3 = 0) (y : ι → R) (s : Finset ι) :
    2 * (∏ i ∈ s, (1 + t * y i))
      = 2 + 2 * t * (∑ i ∈ s, y i)
        + t ^ 2 * ((∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert j₀ s hj₀ ih =>
    rw [Finset.prod_insert hj₀, Finset.sum_insert hj₀, Finset.sum_insert hj₀]
    -- 2 * ((1 + t y_{j0}) * ∏) = (1 + t y) * (2 ∏)
    have expand : 2 * ((1 + t * y j₀) * ∏ i ∈ s, (1 + t * y i))
        = (1 + t * y j₀) * (2 * ∏ i ∈ s, (1 + t * y i)) := by ring
    rw [expand, ih]
    linear_combination (y j₀ * (( ∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2)) * ht

/-- The reduction hom `ZMod (p^3) → ZMod p`. -/
noncomputable def redp (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (show p ∣ p ^ 3 by exact Dvd.intro_left (p ^ 2) rfl) (ZMod p)

/-- Reduction helper: an element of `ZMod (p^3)` that vanishes mod `p` is killed by `p^2`. -/
lemma sq_mul_of_castHom_zero (p : ℕ) [Fact p.Prime] (hp0 : 0 < p) (x : ZMod (p ^ 3))
    (h : (redp p) x = 0) : ((p : ZMod (p ^ 3))) ^ 2 * x = 0 := by
  haveI : NeZero (p ^ 3) := ⟨by positivity⟩
  rw [redp, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  have hx : x = (p : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [hm]; push_cast; ring
  rw [hx]
  have h3 : ((p : ZMod (p ^ 3))) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  linear_combination (m : ZMod (p ^ 3)) * h3

/-- `∑_{x} (x⁻¹)^2 = 0` in `ZMod p` for `p ≥ 5`. -/
lemma invsq_univ (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
  have hb := Equiv.sum_comp (inv_involutive (G := ZMod p)).toPerm (fun x : ZMod p => x ^ 2)
  simp only [Function.Involutive.coe_toPerm] at hb
  rw [show (∑ x : ZMod p, (x⁻¹) ^ 2) = ∑ x : ZMod p, (fun x : ZMod p => x ^ 2) x⁻¹ from rfl, hb]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 (by rw [hcard]; omega)
  simpa using this

/-- `∑_{i<p-1} ((1+i)⁻¹)^2 = 0` in `ZMod p`. -/
lemma invsqsum_range (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ j ∈ Finset.range (p - 1), (((1 + j : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have herase : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹) ^ 2
      = ∑ x : ZMod p, (x⁻¹) ^ 2 := Finset.sum_erase Finset.univ (by simp)
  rw [← invsq_univ p hp5, ← herase]
  have hp0 : 0 < p := by omega
  refine Finset.sum_bij (fun j _ => (1 + (j : ZMod p))) ?_ ?_ ?_ ?_
  · intro j hj
    dsimp only
    rw [Finset.mem_range] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    have : (1 + (j : ZMod p)) = ((1 + j : ℕ) : ZMod p) := by push_cast; ring
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro j₁ h₁ j₂ h₂ heq
    dsimp only at heq
    rw [Finset.mem_range] at h₁ h₂
    have : ((j₁ : ℕ) : ZMod p) = ((j₂ : ℕ) : ZMod p) := by
      rw [add_right_inj] at heq; exact heq
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hb0, _⟩ := hb
    have hval0 : b.val ≠ 0 := fun h => hb0 ((ZMod.val_eq_zero b).mp h)
    refine ⟨b.val - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hlt := ZMod.val_lt b
      omega
    · dsimp only
      have : ((b.val - 1 : ℕ) : ZMod p) = (b.val : ZMod p) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ b.val)]; ring
      rw [this, ZMod.natCast_zmod_val]; ring
  · intro j hj
    dsimp only
    congr 1
    push_cast; ring

/-- `redp` sends the inverse of a `natCast` unit to the inverse of its reduction. -/
lemma redp_inv (p m : ℕ) [Fact p.Prime] (hm : ¬ p ∣ m) :
    (redp p) (((m : ℕ) : ZMod (p ^ 3))⁻¹) = ((m : ℕ) : ZMod p)⁻¹ := by
  haveI : NeZero (p ^ 3) := ⟨by have := (Fact.out : p.Prime).two_le; positivity⟩
  have hpp : p.Prime := Fact.out
  have hcop : Nat.Coprime m (p ^ 3) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]; exact (hpp.coprime_iff_not_dvd).mpr hm
  have hunit : IsUnit ((m : ℕ) : ZMod (p ^ 3)) := by rw [ZMod.isUnit_iff_coprime]; exact hcop
  have hmulinv : ((m : ℕ) : ZMod (p ^ 3)) * (((m : ℕ) : ZMod (p ^ 3))⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hfm : (redp p) ((m : ℕ) : ZMod (p ^ 3)) = ((m : ℕ) : ZMod p) := by rw [redp]; simp
  have hkey : ((m : ℕ) : ZMod p) * (redp p) (((m : ℕ) : ZMod (p ^ 3))⁻¹) = 1 := by
    rw [← hfm, ← map_mul, hmulinv, map_one]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hkey)

/-- Wolstenholme (mod `p^3`): `C(3p-1, p-1) ≡ 1 (mod p^3)`. -/
lemma factA3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : ZMod (p ^ 3)) = 1 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero (p ^ 3) := ⟨by positivity⟩
  have hp0 : 0 < p := by omega
  have hpp : p.Prime := Fact.out
  set R := ZMod (p ^ 3) with hR
  -- integer identity
  have h1 : Nat.factorial (p - 1) * Nat.choose (3 * p - 1) (p - 1)
      = (2 * p + 1).ascFactorial (p - 1) := by
    have h := Nat.ascFactorial_eq_factorial_mul_choose (2 * p) (p - 1)
    rw [h]; congr 2; omega
  have h2 : (2 * p + 1).ascFactorial (p - 1) = ∏ i ∈ Finset.range (p - 1), (2 * p + 1 + i) :=
    Nat.ascFactorial_eq_prod_range _ _
  have h3 : (Nat.factorial (p - 1) : R) * ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : R)
      = ∏ i ∈ Finset.range (p - 1), ((2 * p + 1 + i : ℕ) : R) := by
    rw [← Nat.cast_prod, ← h2, ← h1]; push_cast; ring
  -- coprimality of (1+i)
  have hcop1 : ∀ i ∈ Finset.range (p - 1), ¬ p ∣ (1 + i) := by
    intro i hi; rw [Finset.mem_range] at hi
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hunit1 : ∀ i ∈ Finset.range (p - 1), IsUnit (((1 + i : ℕ)) : R) := by
    intro i hi
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]; exact (hpp.coprime_iff_not_dvd).mpr (hcop1 i hi)
  -- rewrite each factor
  have hterm : ∀ i ∈ Finset.range (p - 1), ((2 * p + 1 + i : ℕ) : R)
      = ((1 + i : ℕ) : R) * (1 + (2 * p : ℕ) * (((1 + i : ℕ) : R))⁻¹) := by
    intro i hi
    have hmi : ((1 + i : ℕ) : R) * (((1 + i : ℕ) : R))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hunit1 i hi)
    have : ((1 + i : ℕ) : R) * (1 + (2 * p : ℕ) * (((1 + i : ℕ) : R))⁻¹)
        = ((1 + i : ℕ) : R) + (2 * p : ℕ) * (((1 + i : ℕ) : R) * (((1 + i : ℕ) : R))⁻¹) := by
      ring
    rw [this, hmi]; push_cast; ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib] at h3
  -- ∏ (1+i) = (p-1)!
  have hprod : ∏ i ∈ Finset.range (p - 1), ((1 + i : ℕ) : R) = (Nat.factorial (p - 1) : R) := by
    rw [← Nat.cast_prod]; congr 1
    rw [← Finset.prod_range_add_one_eq_factorial]
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hprod] at h3
  -- cancel (p-1)!
  have hfacunit : IsUnit ((Nat.factorial (p - 1) : ℕ) : R) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp, hpp.dvd_factorial]; omega
  have hC1 : ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : R)
      = ∏ i ∈ Finset.range (p - 1), (1 + (2 * p : ℕ) * (((1 + i : ℕ) : R))⁻¹) :=
    hfacunit.mul_left_cancel h3
  -- second-order product expansion
  set S : R := ∑ i ∈ Finset.range (p - 1), (((1 + i : ℕ) : R))⁻¹ with hS
  set P : R := ∑ i ∈ Finset.range (p - 1), ((((1 + i : ℕ) : R))⁻¹) ^ 2 with hP
  have ht3 : ((2 * p : ℕ) : R) ^ 3 = 0 := by
    have h : (((2 * p) ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact ⟨8, by ring⟩
    rw [← Nat.cast_pow]; exact h
  have hexp := two_prod ((2 * p : ℕ) : R) ht3 (fun i => (((1 + i : ℕ) : R))⁻¹)
    (Finset.range (p - 1))
  rw [← hS, ← hP] at hexp
  rw [← hC1] at hexp
  -- pairing: 2 * S = p * G
  set G : R := ∑ i ∈ Finset.range (p - 1),
    (((1 + i : ℕ) : R))⁻¹ * (((p - 1 - i : ℕ) : R))⁻¹ with hG
  -- units for (p-1-i)
  have hbdvd : ∀ i ∈ Finset.range (p - 1), ¬ p ∣ (p - 1 - i) := by
    intro i hi; rw [Finset.mem_range] at hi
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hunit2 : ∀ i ∈ Finset.range (p - 1), IsUnit (((p - 1 - i : ℕ)) : R) := by
    intro i hi
    rw [ZMod.isUnit_iff_coprime]; apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]; exact (hpp.coprime_iff_not_dvd).mpr (hbdvd i hi)
  have hpair : 2 * S = (p : R) * G := by
    have hreindex : ∑ i ∈ Finset.range (p - 1), (((p - 1 - i : ℕ) : R))⁻¹ = S := by
      rw [hS, ← Finset.sum_range_reflect (fun j => (((1 + j : ℕ) : R))⁻¹) (p - 1)]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi
      rw [show p - 1 - 1 - i = p - 1 - (1 + i) by omega, show 1 + (p - 1 - (1 + i)) = p - 1 - i by omega]
    have hsummand : ∀ i ∈ Finset.range (p - 1),
        (((1 + i : ℕ) : R))⁻¹ + (((p - 1 - i : ℕ) : R))⁻¹
          = (p : R) * ((((1 + i : ℕ) : R))⁻¹ * (((p - 1 - i : ℕ) : R))⁻¹) := by
      intro i hi
      have hainv : ((1 + i : ℕ) : R) * (((1 + i : ℕ) : R))⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (hunit1 i hi)
      have hbinv : ((p - 1 - i : ℕ) : R) * (((p - 1 - i : ℕ) : R))⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (hunit2 i hi)
      have hsum_eq : (p : R) = ((1 + i : ℕ) : R) + ((p - 1 - i : ℕ) : R) := by
        rw [← Nat.cast_add]; congr 1
        rw [Finset.mem_range] at hi; omega
      rw [hsum_eq]
      linear_combination (-(((p - 1 - i : ℕ) : R))⁻¹) * hainv + (-(((1 + i : ℕ) : R))⁻¹) * hbinv
    calc 2 * S = ∑ i ∈ Finset.range (p - 1),
          ((((1 + i : ℕ) : R))⁻¹ + (((p - 1 - i : ℕ) : R))⁻¹) := by
            rw [Finset.sum_add_distrib, hreindex, ← hS]; ring
      _ = ∑ i ∈ Finset.range (p - 1),
            (p : R) * ((((1 + i : ℕ) : R))⁻¹ * (((p - 1 - i : ℕ) : R))⁻¹) :=
            Finset.sum_congr rfl hsummand
      _ = (p : R) * G := by rw [hG, Finset.mul_sum]
  -- reductions mod p
  have hp3 : ((p : ℕ) : R) ^ 3 = 0 := by
    have h : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := ZMod.natCast_self (p ^ 3)
    rw [← Nat.cast_pow]; exact h
  have hredP : (redp p) P = 0 := by
    rw [hP, map_sum, ← invsqsum_range p hp5]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_pow, redp_inv p (1 + i) (hcop1 i hi)]
  have hredG : (redp p) G = 0 := by
    rw [hG, map_sum]
    have hcongr : ∀ i ∈ Finset.range (p - 1),
        (redp p) ((((1 + i : ℕ) : R))⁻¹ * (((p - 1 - i : ℕ) : R))⁻¹)
          = -(((1 + i : ℕ) : ZMod p)⁻¹) ^ 2 := by
      intro i hi
      rw [map_mul, redp_inv p (1 + i) (hcop1 i hi), redp_inv p (p - 1 - i) (hbdvd i hi)]
      have hneg : ((p - 1 - i : ℕ) : ZMod p) = -((1 + i : ℕ) : ZMod p) := by
        have : ((1 + i : ℕ) : ZMod p) + ((p - 1 - i : ℕ) : ZMod p) = 0 := by
          rw [← Nat.cast_add]
          rw [Finset.mem_range] at hi
          rw [show 1 + i + (p - 1 - i) = p by omega, ZMod.natCast_self]
        linear_combination this
      rw [hneg, inv_neg]; ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib, invsqsum_range p hp5, neg_zero]
  -- p^2 kills G and P
  have hp2G : ((p : ℕ) : R) ^ 2 * G = 0 := sq_mul_of_castHom_zero p hp0 G hredG
  have hp2P : ((p : ℕ) : R) ^ 2 * P = 0 := sq_mul_of_castHom_zero p hp0 P hredP
  -- t = 2p
  have htp : ((2 * p : ℕ) : R) = 2 * (p : R) := by push_cast; ring
  -- the two correction terms vanish
  have hterm1 : 2 * ((2 * p : ℕ) : R) * S = 0 := by
    rw [htp]
    have : 2 * (2 * (p : R)) * S = 2 * (p : R) * (2 * S) := by ring
    rw [this, hpair]
    linear_combination (2 : R) * hp2G
  have hterm2 : ((2 * p : ℕ) : R) ^ 2 * (S ^ 2 - P) = 0 := by
    rw [htp]
    have hS2 : (2 * (p : R)) ^ 2 * S ^ 2 = 0 := by
      have h2S : 2 * (p : R) * S = (p : R) ^ 2 * G := by
        have : 2 * (p : R) * S = (p : R) * (2 * S) := by ring
        rw [this, hpair]; ring
      have : (2 * (p : R)) ^ 2 * S ^ 2 = (2 * (p : R) * S) ^ 2 := by ring
      rw [this, h2S]
      calc ((p : R) ^ 2 * G) ^ 2 = ((p : R) ^ 3) * ((p : R) * G ^ 2) := by ring
        _ = 0 := by rw [hp3]; ring
    have hSP : (2 * (p : R)) ^ 2 * P = 0 := by
      have : (2 * (p : R)) ^ 2 * P = 4 * (((p : ℕ) : R) ^ 2 * P) := by ring
      rw [this, hp2P]; ring
    have : (2 * (p : R)) ^ 2 * (S ^ 2 - P) = (2 * (p : R)) ^ 2 * S ^ 2 - (2 * (p : R)) ^ 2 * P := by
      ring
    rw [this, hS2, hSP]; ring
  -- conclude 2 * C1 = 2
  rw [hterm1, hterm2, add_zero, add_zero] at hexp
  have h2unit : IsUnit (2 : R) := by
    have hu : IsUnit ((2 : ℕ) : ZMod (p ^ 3)) := by
      rw [ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm]
      exact (hpp.coprime_iff_not_dvd).mpr (by
        intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
    simpa using hu
  have hfin : (2 : R) * ((Nat.choose (3 * p - 1) (p - 1) : ℕ) : R) = 2 * 1 := by
    rw [mul_one]; exact hexp
  exact h2unit.mul_left_cancel hfin

/-- Integer form of Wolstenholme mod `p^3`. -/
lemma hC1dvd3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((p : ℤ)) ^ 3 ∣ (Nat.choose (3 * p - 1) (p - 1) : ℤ) - 1 := by
  have hz : (((Nat.choose (3 * p - 1) (p - 1) : ℤ) - 1 : ℤ) : ZMod (p ^ 3)) = 0 := by
    push_cast; rw [factA3 p hp5]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  rwa [Nat.cast_pow] at hz

/- ## Infrastructure for the interior sum (mod p^2)

We work in `R = ZMod (p^2)` and reduce mod `p` via `redp2`.  Harmonic sums
`Hp` (in `ZMod p`) and `HR` (in `ZMod (p^2)`) collect inverses of `1..n`. -/

/-- The reduction hom `ZMod (p^2) → ZMod p`. -/
noncomputable def redp2 (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) (ZMod p)

/-- If `redp2 z = 0` then `p * z = 0` in `ZMod (p^2)`. -/
lemma p_mul_of_redp2_zero (p : ℕ) [Fact p.Prime] (z : ZMod (p ^ 2))
    (h : redp2 p z = 0) : (p : ZMod (p ^ 2)) * z = 0 := by
  haveI : NeZero (p ^ 2) := ⟨by have := (Fact.out : p.Prime).two_le; positivity⟩
  rw [redp2, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  have hz : z = (p : ZMod (p ^ 2)) * (m : ZMod (p ^ 2)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [hm]; push_cast; ring
  rw [hz]
  have h2 : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  linear_combination (m : ZMod (p ^ 2)) * h2

/-- `p * x = p * y` in `ZMod (p^2)` whenever they agree after reducing mod `p`. -/
lemma p_mul_eq_of_redp2_eq (p : ℕ) [Fact p.Prime] (x y : ZMod (p ^ 2))
    (h : redp2 p x = redp2 p y) : (p : ZMod (p ^ 2)) * x = (p : ZMod (p ^ 2)) * y := by
  have h0 : redp2 p (x - y) = 0 := by rw [map_sub, h, sub_self]
  have := p_mul_of_redp2_zero p (x - y) h0
  linear_combination this

/-- `redp2` sends the inverse of a `natCast` unit to the inverse of its reduction. -/
lemma redp2_inv (p m : ℕ) [Fact p.Prime] (hm : ¬ p ∣ m) :
    (redp2 p) (((m : ℕ) : ZMod (p ^ 2))⁻¹) = ((m : ℕ) : ZMod p)⁻¹ := by
  haveI : NeZero (p ^ 2) := ⟨by have := (Fact.out : p.Prime).two_le; positivity⟩
  have hpp : p.Prime := Fact.out
  have hcop : Nat.Coprime m (p ^ 2) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]; exact (hpp.coprime_iff_not_dvd).mpr hm
  have hunit : IsUnit ((m : ℕ) : ZMod (p ^ 2)) := by rw [ZMod.isUnit_iff_coprime]; exact hcop
  have hmulinv : ((m : ℕ) : ZMod (p ^ 2)) * (((m : ℕ) : ZMod (p ^ 2))⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hfm : (redp2 p) ((m : ℕ) : ZMod (p ^ 2)) = ((m : ℕ) : ZMod p) := by rw [redp2]; simp
  have hkey : ((m : ℕ) : ZMod p) * (redp2 p) (((m : ℕ) : ZMod (p ^ 2))⁻¹) = 1 := by
    rw [← hfm, ← map_mul, hmulinv, map_one]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hkey)

/-- Harmonic sum `∑_{j=1}^n 1/j` in `ZMod p`. -/
def Hp (p n : ℕ) : ZMod p := ∑ j ∈ Finset.Ico 1 (n + 1), ((j : ℕ) : ZMod p)⁻¹

/-- Harmonic sum `∑_{j=1}^n 1/j` in `ZMod (p^2)`. -/
def HR (p n : ℕ) : ZMod (p ^ 2) := ∑ j ∈ Finset.Ico 1 (n + 1), ((j : ℕ) : ZMod (p ^ 2))⁻¹

lemma Hp_succ (p n : ℕ) : Hp p (n + 1) = Hp p n + (((n + 1 : ℕ)) : ZMod p)⁻¹ := by
  unfold Hp
  rw [Finset.sum_Ico_succ_top (by omega)]

lemma HR_succ (p n : ℕ) : HR p (n + 1) = HR p n + (((n + 1 : ℕ)) : ZMod (p ^ 2))⁻¹ := by
  unfold HR
  rw [Finset.sum_Ico_succ_top (by omega)]

lemma Hp_zero (p : ℕ) : Hp p 0 = 0 := by unfold Hp; simp

lemma HR_zero (p : ℕ) : HR p 0 = 0 := by unfold HR; simp

/-- `redp2 (HR n) = Hp n` when `n < p` (all denominators coprime to `p`). -/
lemma redp2_HR (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    (redp2 p) (HR p n) = Hp p n := by
  unfold HR Hp
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact redp2_inv p j (by
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega)

/-- Reflection of inverses: `1/(p-a) = -1/a` in `ZMod p`. -/
lemma inv_reflect (p a : ℕ) [Fact p.Prime] (ha1 : 1 ≤ a) (hap : a ≤ p) :
    ((p - a : ℕ) : ZMod p)⁻¹ = -(((a : ℕ) : ZMod p))⁻¹ := by
  have hneg : ((p - a : ℕ) : ZMod p) = -((a : ℕ) : ZMod p) := by
    have h : ((p - a : ℕ) : ZMod p) + ((a : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add, show (p - a) + a = p by omega, ZMod.natCast_self]
    linear_combination h
  rw [hneg, inv_neg]

/-- Wolstenholme: `H_{p-1} = 0` in `ZMod p`. -/
lemma Hp_p_sub_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : Hp p (p - 1) = 0 := by
  have : Hp p (p - 1) = ∑ i ∈ Finset.range (p - 1), (1 + (i : ZMod p))⁻¹ := by
    unfold Hp
    rw [show p - 1 + 1 = p by omega, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by rw [show p - 1 = p - 1 by rfl]) 
    intro i _
    congr 1
    push_cast; ring
  rw [this, invsum_range p (by omega)]

/-- Reflection for harmonic sums: `H_{p-1-m} = H_m` in `ZMod p`. -/
lemma Hp_reflect (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hm : m ≤ p - 1) :
    Hp p (p - 1 - m) = Hp p m := by
  induction m with
  | zero => simpa [Hp_zero] using Hp_p_sub_one p hp5
  | succ n ih =>
    have hn : n ≤ p - 1 := by omega
    have ihn := ih hn
    have hstep := Hp_succ p (p - 1 - (n + 1))
    rw [show p - 1 - (n + 1) + 1 = p - 1 - n by omega] at hstep
    have hstep2 : Hp p (n + 1) = Hp p n + (((n + 1 : ℕ)) : ZMod p)⁻¹ := Hp_succ p n
    -- inv (p-1-n) = inv (p - (n+1)) = - inv (n+1)
    have href : (((p - 1 - n : ℕ)) : ZMod p)⁻¹ = -(((n + 1 : ℕ)) : ZMod p)⁻¹ := by
      rw [show p - 1 - n = p - (n + 1) by omega]
      exact inv_reflect p (n + 1) (by omega) (by omega)
    rw [href] at hstep
    linear_combination -hstep + ihn - hstep2

/-- First-order product expansion: `∏ (a i + t) = (∏ a i)(1 + t·∑ 1/a i)` when `t² = 0`
and all `a i` are units. -/
lemma prod_add_const_expand {p : ℕ} (t : ZMod (p ^ 2)) (ht : t ^ 2 = 0)
    (a : ℕ → ZMod (p ^ 2)) (s : Finset ℕ) (hunit : ∀ i ∈ s, IsUnit (a i)) :
    (∏ i ∈ s, (a i + t)) = (∏ i ∈ s, a i) * (1 + t * ∑ i ∈ s, (a i)⁻¹) := by
  rw [prod_add_nilpotent t ht a s]
  have hkey : ∑ j ∈ s, ∏ i ∈ s.erase j, a i = (∏ i ∈ s, a i) * ∑ j ∈ s, (a j)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hmul := Finset.mul_prod_erase s a hj
    have hinv : a j * (a j)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hunit j hj)
    have : ∏ i ∈ s.erase j, a i = (∏ i ∈ s, a i) * (a j)⁻¹ := by
      calc ∏ i ∈ s.erase j, a i
          = ((a j)⁻¹ * a j) * ∏ i ∈ s.erase j, a i := by rw [mul_comm (a j)⁻¹, hinv, one_mul]
        _ = (a j)⁻¹ * (a j * ∏ i ∈ s.erase j, a i) := by ring
        _ = (a j)⁻¹ * ∏ i ∈ s, a i := by rw [hmul]
        _ = (∏ i ∈ s, a i) * (a j)⁻¹ := by ring
    rw [this]
  rw [hkey]; ring

lemma HR_eq_range (p k : ℕ) : HR p k = ∑ i ∈ Finset.range k, ((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
  unfold HR
  rw [Finset.sum_Ico_eq_sum_range, show k + 1 - 1 = k by omega]
  apply Finset.sum_congr rfl
  intro i _; congr 2; omega

/-- `t = (p : ZMod (p^2))` is square-zero. -/
lemma p_sq_zero (p : ℕ) : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- units of small naturals in `ZMod (p^2)`. -/
lemma isUnit_natCast_lt (p m : ℕ) [Fact p.Prime] (hm : 0 < m) (hmp : m < p) :
    IsUnit ((m : ℕ) : ZMod (p ^ 2)) := by
  have hpp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm]
  exact (hpp.coprime_iff_not_dvd).mpr (by intro hd; have := Nat.le_of_dvd hm hd; omega)

/-- `k!` is a unit in `ZMod (p^2)` for `k < p`. -/
lemma isUnit_factorial (p k : ℕ) [Fact p.Prime] (hkp : k < p) :
    IsUnit ((Nat.factorial k : ℕ) : ZMod (p ^ 2)) := by
  have hpp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp, hpp.dvd_factorial]
  omega

/-- `(-a)⁻¹ = -a⁻¹` for units in `ZMod n`. -/
lemma neg_inv_unit {n : ℕ} {a : ZMod n} (ha : IsUnit a) : (-a)⁻¹ = -a⁻¹ := by
  have hL : (-a)⁻¹ * (-a) = 1 := ZMod.inv_mul_of_unit _ ha.neg
  have hR : (-a) * (-a⁻¹) = 1 := by rw [neg_mul_neg]; exact ZMod.mul_inv_of_unit _ ha
  calc (-a)⁻¹ = (-a)⁻¹ * ((-a) * (-a⁻¹)) := by rw [hR, mul_one]
    _ = ((-a)⁻¹ * (-a)) * (-a⁻¹) := by ring
    _ = -a⁻¹ := by rw [hL, one_mul]

/-- **Ingredient I**: `C(p-1,k)² ≡ 1 - 2p·H_k  (mod p²)`. -/
lemma sq_choose_expand (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ 2)) ^ 2
      = 1 - 2 * (p : ZMod (p ^ 2)) * HR p k := by
  set R := ZMod (p ^ 2)
  -- k! * C = descFactorial (p-1) k = ∏ (p-1-i)
  have hdf : (Nat.factorial k) * Nat.choose (p - 1) k = Nat.descFactorial (p - 1) k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
  have hprodN : Nat.descFactorial (p - 1) k = ∏ i ∈ Finset.range k, (p - 1 - i) :=
    Nat.descFactorial_eq_prod_range (p - 1) k
  -- cast to R
  have hcast : (Nat.factorial k : R) * ((Nat.choose (p - 1) k : ℕ) : R)
      = ∏ i ∈ Finset.range k, ((p - 1 - i : ℕ) : R) := by
    rw [← Nat.cast_mul, hdf, hprodN, Nat.cast_prod]
  -- each factor = -(i+1) + p
  have hterm : ∀ i ∈ Finset.range k, ((p - 1 - i : ℕ) : R) = (-(((i + 1 : ℕ)) : R)) + (p : R) := by
    intro i hi; rw [Finset.mem_range] at hi
    have : ((p - 1 - i : ℕ) : R) + ((i + 1 : ℕ) : R) = (p : R) := by
      rw [← Nat.cast_add, show (p - 1 - i) + (i + 1) = p by omega]
    linear_combination this
  rw [Finset.prod_congr rfl hterm,
    prod_add_const_expand (p : R) (p_sq_zero p) (fun i => -(((i + 1 : ℕ)) : R)) (Finset.range k)
      (fun i hi => by
        rw [Finset.mem_range] at hi
        exact (isUnit_natCast_lt p (i + 1) (by omega) (by omega)).neg)] at hcast
  -- simplify the product and sum
  have hprodA : ∏ i ∈ Finset.range k, (-(((i + 1 : ℕ)) : R)) = (-1) ^ k * (Nat.factorial k : R) := by
    have hh : ∀ i ∈ Finset.range k, (-(((i + 1 : ℕ)) : R)) = (-1) * (((i + 1 : ℕ)) : R) := by
      intro i _; ring
    rw [Finset.prod_congr rfl hh, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  have hsumA : ∑ i ∈ Finset.range k, (-(((i + 1 : ℕ)) : R))⁻¹ = -HR p k := by
    rw [HR_eq_range, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    exact neg_inv_unit (isUnit_natCast_lt p (i + 1) (by omega) (by omega))
  rw [hprodA, hsumA] at hcast
  have hunit := isUnit_factorial p k (by omega)
  have hCval : ((Nat.choose (p - 1) k : ℕ) : R) = (-1) ^ k * (1 - (p : R) * HR p k) := by
    apply hunit.mul_left_cancel
    rw [hcast]; ring
  rw [hCval]
  have hs : ((-1 : R) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hp2 : (p : R) ^ 2 = 0 := p_sq_zero p
  linear_combination (1 - (p : R) * HR p k) ^ 2 * hs + (HR p k) ^ 2 * hp2

/-- **Ingredient II**: `C(p-1+k, k-1) ≡ 1 + p·H_{k-1}  (mod p²)`. -/
lemma choose_pk_expand (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    ((Nat.choose (p - 1 + k) (k - 1) : ℕ) : ZMod (p ^ 2))
      = 1 + (p : ZMod (p ^ 2)) * HR p (k - 1) := by
  set R := ZMod (p ^ 2)
  have hasc : (p + 1).ascFactorial (k - 1) = Nat.factorial (k - 1) * Nat.choose (p - 1 + k) (k - 1) := by
    have := Nat.ascFactorial_eq_factorial_mul_choose p (k - 1)
    rw [show p + (k - 1) = p - 1 + k by omega] at this
    exact this
  have hprodN : (p + 1).ascFactorial (k - 1) = ∏ i ∈ Finset.range (k - 1), (p + 1 + i) :=
    Nat.ascFactorial_eq_prod_range (p + 1) (k - 1)
  have hcast : (Nat.factorial (k - 1) : R) * ((Nat.choose (p - 1 + k) (k - 1) : ℕ) : R)
      = ∏ i ∈ Finset.range (k - 1), ((p + 1 + i : ℕ) : R) := by
    rw [← Nat.cast_mul, ← hasc, hprodN, Nat.cast_prod]
  have hterm : ∀ i ∈ Finset.range (k - 1), ((p + 1 + i : ℕ) : R) = (((i + 1 : ℕ)) : R) + (p : R) := by
    intro i _; push_cast; ring
  rw [Finset.prod_congr rfl hterm,
    prod_add_const_expand (p : R) (p_sq_zero p) (fun i => (((i + 1 : ℕ)) : R)) (Finset.range (k - 1))
      (fun i hi => by
        rw [Finset.mem_range] at hi
        exact isUnit_natCast_lt p (i + 1) (by omega) (by omega))] at hcast
  have hprodA : ∏ i ∈ Finset.range (k - 1), (((i + 1 : ℕ)) : R) = (Nat.factorial (k - 1) : R) := by
    rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  have hsumA : ∑ i ∈ Finset.range (k - 1), (((i + 1 : ℕ)) : R)⁻¹ = HR p (k - 1) :=
    (HR_eq_range p (k - 1)).symm
  rw [hprodA, hsumA] at hcast
  have hunit := isUnit_factorial p (k - 1) (by omega)
  apply hunit.mul_left_cancel
  linear_combination hcast

/-- Product of a consecutive block near `c·p`, expanded to first order in `ZMod (p²)`. -/
lemma prod_Ico_shift_expand (p c a L : ℕ) [Fact p.Prime] (ha1 : 1 ≤ a) (haL : a + L ≤ p) :
    ((∏ m ∈ Finset.Ico (c * p + a) (c * p + a + L), m : ℕ) : ZMod (p ^ 2))
      = (∏ i ∈ Finset.range L, ((a + i : ℕ) : ZMod (p ^ 2)))
        * (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))
            * ∑ i ∈ Finset.range L, ((a + i : ℕ) : ZMod (p ^ 2))⁻¹) := by
  set R := ZMod (p ^ 2)
  rw [Nat.cast_prod, Finset.prod_Ico_eq_prod_range, show c * p + a + L - (c * p + a) = L by omega]
  have hterm : ∀ i ∈ Finset.range L, ((c * p + a + i : ℕ) : R) = ((a + i : ℕ) : R) + (c : R) * (p : R) := by
    intro i _; push_cast; ring
  rw [Finset.prod_congr rfl hterm,
    prod_add_const_expand ((c : R) * (p : R)) (by rw [mul_pow, p_sq_zero, mul_zero])
      (fun i => ((a + i : ℕ) : R)) (Finset.range L)
      (fun i hi => by
        rw [Finset.mem_range] at hi
        exact isUnit_natCast_lt p (a + i) (by omega) (by omega))]

/-- Sum of inverses over `Ico a b` equals `H_{b-1} - H_{a-1}` in `ZMod (p²)`. -/
lemma HR_Ico (p a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, ((j : ℕ) : ZMod (p ^ 2))⁻¹ = HR p (b - 1) - HR p (a - 1) := by
  have hcons := Finset.sum_Ico_consecutive (fun j => ((j : ℕ) : ZMod (p ^ 2))⁻¹) ha hab
  have e1 : HR p (b - 1) = ∑ j ∈ Finset.Ico 1 b, ((j : ℕ) : ZMod (p ^ 2))⁻¹ := by
    unfold HR; rw [show b - 1 + 1 = b by omega]
  have e2 : HR p (a - 1) = ∑ j ∈ Finset.Ico 1 a, ((j : ℕ) : ZMod (p ^ 2))⁻¹ := by
    unfold HR; rw [show a - 1 + 1 = a by omega]
  rw [e1, e2]; linear_combination hcons

/-- **Ingredient III' (region A)**: for `2 ≤ k` and `2k ≤ p+1`,
`C(3(p-1)+2k, p) ≡ 3(1 + p·H_{2k-3})  (mod p²)`. -/
lemma CNp_regionA (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkA : 2 * k ≤ p + 1) :
    ((Nat.choose (3 * (p - 1) + 2 * k) p : ℕ) : ZMod (p ^ 2))
      = 3 * (1 + (p : ZMod (p ^ 2)) * HR p (2 * k - 3)) := by
  set R := ZMod (p ^ 2)
  set N := 3 * (p - 1) + 2 * k with hN
  have hpN : p ≤ N := by omega
  -- Nat: ∏_{Ico (N-p+1)(N+1)} m = C(N,p) * p!
  have hlow : ∏ m ∈ Finset.Ico 1 (N - p + 1), m = Nat.factorial (N - p) := by
    have := Finset.prod_Ico_id_eq_factorial (N - p); rwa [show N - p + 1 = N - p + 1 from rfl] at this
  have hfull : ∏ m ∈ Finset.Ico 1 (N + 1), m = Nat.factorial N := Finset.prod_Ico_id_eq_factorial N
  have hcons : (∏ m ∈ Finset.Ico 1 (N - p + 1), m) * (∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m)
      = ∏ m ∈ Finset.Ico 1 (N + 1), m :=
    Finset.prod_Ico_consecutive (fun m => m) (by omega) (by omega)
  rw [hlow, hfull] at hcons
  have hcmf := Nat.choose_mul_factorial_mul_factorial hpN
  have hPPP : ∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m = Nat.choose N p * Nat.factorial p := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (N - p))
    rw [hcons, ← hcmf]; ring
  -- split at 3p
  have hsplit : (∏ m ∈ Finset.Ico (N - p + 1) (3 * p), m) * (∏ m ∈ Finset.Ico (3 * p) (N + 1), m)
      = ∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m :=
    Finset.prod_Ico_consecutive (fun m => m) (by omega) (by omega)
  have habove : ∏ m ∈ Finset.Ico (3 * p) (N + 1), m
      = (3 * p) * ∏ m ∈ Finset.Ico (3 * p + 1) (N + 1), m :=
    Finset.prod_eq_prod_Ico_succ_bot (by omega) (fun m => m)
  -- cancel p:  3 * (PB * PA) = C * (p-1)!
  set PB := ∏ m ∈ Finset.Ico (N - p + 1) (3 * p), m with hPB
  set PA := ∏ m ∈ Finset.Ico (3 * p + 1) (N + 1), m with hPA
  have hchain : p * (3 * (PB * PA)) = p * (Nat.choose N p * Nat.factorial (p - 1)) := by
    calc p * (3 * (PB * PA)) = PB * (3 * p * PA) := by ring
      _ = ∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m := by rw [← hsplit, habove]
      _ = Nat.choose N p * Nat.factorial p := hPPP
      _ = p * (Nat.choose N p * Nat.factorial (p - 1)) := by
          rw [← Nat.mul_factorial_pred (show p ≠ 0 by omega)]; ring
  have hnatfin : 3 * (PB * PA) = Nat.choose N p * Nat.factorial (p - 1) :=
    Nat.eq_of_mul_eq_mul_left (by omega) hchain
  -- Nat product combination for PB's leading part
  have hprodNat : Nat.factorial (2 * k - 3) * ∏ j ∈ Finset.Ico (2 * k - 2) p, j = Nat.factorial (p - 1) := by
    have h1 : ∏ j ∈ Finset.Ico 1 (2 * k - 2), j = Nat.factorial (2 * k - 3) := by
      have := Finset.prod_Ico_id_eq_factorial (2 * k - 3); rwa [show 2 * k - 3 + 1 = 2 * k - 2 by omega] at this
    have h2 : ∏ j ∈ Finset.Ico 1 p, j = Nat.factorial (p - 1) := by
      have := Finset.prod_Ico_id_eq_factorial (p - 1); rwa [show p - 1 + 1 = p by omega] at this
    have hc := Finset.prod_Ico_consecutive (fun j => j) (show 1 ≤ 2 * k - 2 by omega) (show 2 * k - 2 ≤ p by omega)
    rw [← h1, ← h2, ← hc]
  -- expand PA in R
  have hPAR : (PA : R) = (Nat.factorial (2 * k - 3) : R) * (1 + 3 * (p : R) * HR p (2 * k - 3)) := by
    rw [hPA, show N + 1 = 3 * p + 1 + (2 * k - 3) by omega,
      prod_Ico_shift_expand p 3 1 (2 * k - 3) (by omega) (by omega)]
    have hprodA : ∏ i ∈ Finset.range (2 * k - 3), ((1 + i : ℕ) : R) = (Nat.factorial (2 * k - 3) : R) := by
      rw [← Nat.cast_prod, show (fun i => 1 + i) = (fun i => i + 1) from by funext i; ring,
        Finset.prod_range_add_one_eq_factorial]
    have hsumA : ∑ i ∈ Finset.range (2 * k - 3), ((1 + i : ℕ) : R)⁻¹ = HR p (2 * k - 3) := by
      rw [HR_eq_range]; apply Finset.sum_congr rfl; intro i _; congr 2; omega
    rw [hprodA, hsumA]; push_cast; ring
  -- expand PB in R
  have hPBR : (PB : R) = (∏ j ∈ Finset.Ico (2 * k - 2) p, (j : R))
      * (1 + 2 * (p : R) * (HR p (p - 1) - HR p (2 * k - 3))) := by
    rw [hPB, show (3 * p) = 2 * p + (2 * k - 2) + (p + 2 - 2 * k) by omega,
      show N - p + 1 = 2 * p + (2 * k - 2) by omega,
      prod_Ico_shift_expand p 2 (2 * k - 2) (p + 2 - 2 * k) (by omega) (by omega)]
    have hsumB : ∑ i ∈ Finset.range (p + 2 - 2 * k), ((2 * k - 2 + i : ℕ) : R)⁻¹
        = HR p (p - 1) - HR p (2 * k - 3) := by
      have hhr := HR_Ico p (2 * k - 2) p (by omega) (by omega)
      rw [show 2 * k - 2 - 1 = 2 * k - 3 by omega] at hhr
      rw [← hhr, Finset.sum_Ico_eq_sum_range, show p - (2 * k - 2) = p + 2 - 2 * k by omega]
    have hprodB : ∏ i ∈ Finset.range (p + 2 - 2 * k), ((2 * k - 2 + i : ℕ) : R)
        = ∏ j ∈ Finset.Ico (2 * k - 2) p, (j : R) := by
      rw [Finset.prod_Ico_eq_prod_range, show p - (2 * k - 2) = p + 2 - 2 * k by omega]
    rw [hsumB, hprodB]; push_cast; ring
  -- combine
  have hprodNatR : (Nat.factorial (2 * k - 3) : R) * ∏ j ∈ Finset.Ico (2 * k - 2) p, (j : R)
      = (Nat.factorial (p - 1) : R) := by
    rw [← Nat.cast_prod, ← Nat.cast_mul, hprodNat]
  have hHR0 : (p : R) * HR p (p - 1) = 0 :=
    p_mul_of_redp2_zero p (HR p (p - 1)) (by rw [redp2_HR p (p - 1) (by omega)]; exact Hp_p_sub_one p hp5)
  have hcastfin : 3 * ((PB : R) * (PA : R)) = (Nat.choose N p : R) * (Nat.factorial (p - 1) : R) := by
    have := congrArg (Nat.cast (R := R)) hnatfin; push_cast at this; linear_combination this
  rw [hPAR, hPBR] at hcastfin
  have hunit : IsUnit ((Nat.factorial (p - 1) : ℕ) : R) := isUnit_factorial p (p - 1) (by omega)
  apply hunit.mul_left_cancel
  have hp2 : (p : R) ^ 2 = 0 := p_sq_zero p
  -- rearrange
  rw [show ((Nat.factorial (p - 1) : ℕ) : R) * (3 * (1 + (p : R) * HR p (2 * k - 3)))
      = 3 * (((Nat.factorial (2 * k - 3) : R) * ∏ j ∈ Finset.Ico (2 * k - 2) p, (j : R))
          * (1 + (p : R) * HR p (2 * k - 3))) from by rw [hprodNatR]; ring]
  rw [show ((Nat.factorial (p - 1) : ℕ) : R) * ((Nat.choose N p : ℕ) : R)
      = ((Nat.choose N p : ℕ) : R) * (Nat.factorial (p - 1) : R) from by ring, ← hcastfin]
  linear_combination (18 * (Nat.factorial (2 * k - 3) : R) * (∏ j ∈ Finset.Ico (2 * k - 2) p, (j : R))
      * (HR p (p - 1) - HR p (2 * k - 3)) * HR p (2 * k - 3)) * hp2
      + (6 * (Nat.factorial (2 * k - 3) : R) * (∏ j ∈ Finset.Ico (2 * k - 2) p, (j : R))) * hHR0

/-- **Ingredient III' (region B)**: for `p+3 ≤ 2k` and `k ≤ p-1`,
`C(3(p-1)+2k, p) ≡ 4(1 + p·H_{2k-3-p})  (mod p²)`. -/
lemma CNp_regionB (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hkB : p + 3 ≤ 2 * k) (hkp : k ≤ p - 1) :
    ((Nat.choose (3 * (p - 1) + 2 * k) p : ℕ) : ZMod (p ^ 2))
      = 4 * (1 + (p : ZMod (p ^ 2)) * HR p (2 * k - 3 - p)) := by
  set R := ZMod (p ^ 2)
  set N := 3 * (p - 1) + 2 * k with hN
  have hpN : p ≤ N := by omega
  have hlow : ∏ m ∈ Finset.Ico 1 (N - p + 1), m = Nat.factorial (N - p) :=
    Finset.prod_Ico_id_eq_factorial (N - p)
  have hfull : ∏ m ∈ Finset.Ico 1 (N + 1), m = Nat.factorial N := Finset.prod_Ico_id_eq_factorial N
  have hcons : (∏ m ∈ Finset.Ico 1 (N - p + 1), m) * (∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m)
      = ∏ m ∈ Finset.Ico 1 (N + 1), m :=
    Finset.prod_Ico_consecutive (fun m => m) (by omega) (by omega)
  rw [hlow, hfull] at hcons
  have hcmf := Nat.choose_mul_factorial_mul_factorial hpN
  have hPPP : ∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m = Nat.choose N p * Nat.factorial p := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (N - p))
    rw [hcons, ← hcmf]; ring
  have hsplit : (∏ m ∈ Finset.Ico (N - p + 1) (4 * p), m) * (∏ m ∈ Finset.Ico (4 * p) (N + 1), m)
      = ∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m :=
    Finset.prod_Ico_consecutive (fun m => m) (by omega) (by omega)
  have habove : ∏ m ∈ Finset.Ico (4 * p) (N + 1), m
      = (4 * p) * ∏ m ∈ Finset.Ico (4 * p + 1) (N + 1), m :=
    Finset.prod_eq_prod_Ico_succ_bot (by omega) (fun m => m)
  set PB := ∏ m ∈ Finset.Ico (N - p + 1) (4 * p), m with hPB
  set PA := ∏ m ∈ Finset.Ico (4 * p + 1) (N + 1), m with hPA
  have hchain : p * (4 * (PB * PA)) = p * (Nat.choose N p * Nat.factorial (p - 1)) := by
    calc p * (4 * (PB * PA)) = PB * (4 * p * PA) := by ring
      _ = ∏ m ∈ Finset.Ico (N - p + 1) (N + 1), m := by rw [← hsplit, habove]
      _ = Nat.choose N p * Nat.factorial p := hPPP
      _ = p * (Nat.choose N p * Nat.factorial (p - 1)) := by
          rw [← Nat.mul_factorial_pred (show p ≠ 0 by omega)]; ring
  have hnatfin : 4 * (PB * PA) = Nat.choose N p * Nat.factorial (p - 1) :=
    Nat.eq_of_mul_eq_mul_left (by omega) hchain
  have hprodNat : Nat.factorial (2 * k - 3 - p) * ∏ j ∈ Finset.Ico (2 * k - 2 - p) p, j
      = Nat.factorial (p - 1) := by
    have h1 : ∏ j ∈ Finset.Ico 1 (2 * k - 2 - p), j = Nat.factorial (2 * k - 3 - p) := by
      have := Finset.prod_Ico_id_eq_factorial (2 * k - 3 - p)
      rwa [show 2 * k - 3 - p + 1 = 2 * k - 2 - p by omega] at this
    have h2 : ∏ j ∈ Finset.Ico 1 p, j = Nat.factorial (p - 1) := by
      have := Finset.prod_Ico_id_eq_factorial (p - 1); rwa [show p - 1 + 1 = p by omega] at this
    have hc := Finset.prod_Ico_consecutive (fun j => j) (show 1 ≤ 2 * k - 2 - p by omega)
      (show 2 * k - 2 - p ≤ p by omega)
    rw [← h1, ← h2, ← hc]
  have hPAR : (PA : R) = (Nat.factorial (2 * k - 3 - p) : R) * (1 + 4 * (p : R) * HR p (2 * k - 3 - p)) := by
    rw [hPA, show N + 1 = 4 * p + 1 + (2 * k - 3 - p) by omega,
      prod_Ico_shift_expand p 4 1 (2 * k - 3 - p) (by omega) (by omega)]
    have hprodA : ∏ i ∈ Finset.range (2 * k - 3 - p), ((1 + i : ℕ) : R) = (Nat.factorial (2 * k - 3 - p) : R) := by
      rw [← Nat.cast_prod, show (fun i => 1 + i) = (fun i => i + 1) from by funext i; ring,
        Finset.prod_range_add_one_eq_factorial]
    have hsumA : ∑ i ∈ Finset.range (2 * k - 3 - p), ((1 + i : ℕ) : R)⁻¹ = HR p (2 * k - 3 - p) := by
      rw [HR_eq_range]; apply Finset.sum_congr rfl; intro i _; congr 2; omega
    rw [hprodA, hsumA]; push_cast; ring
  have hPBR : (PB : R) = (∏ j ∈ Finset.Ico (2 * k - 2 - p) p, (j : R))
      * (1 + 3 * (p : R) * (HR p (p - 1) - HR p (2 * k - 3 - p))) := by
    rw [hPB, show (4 * p) = 3 * p + (2 * k - 2 - p) + (2 * p + 2 - 2 * k) by omega,
      show N - p + 1 = 3 * p + (2 * k - 2 - p) by omega,
      prod_Ico_shift_expand p 3 (2 * k - 2 - p) (2 * p + 2 - 2 * k) (by omega) (by omega)]
    have hsumB : ∑ i ∈ Finset.range (2 * p + 2 - 2 * k), ((2 * k - 2 - p + i : ℕ) : R)⁻¹
        = HR p (p - 1) - HR p (2 * k - 3 - p) := by
      have hhr := HR_Ico p (2 * k - 2 - p) p (by omega) (by omega)
      rw [show 2 * k - 2 - p - 1 = 2 * k - 3 - p by omega] at hhr
      rw [← hhr, Finset.sum_Ico_eq_sum_range, show p - (2 * k - 2 - p) = 2 * p + 2 - 2 * k by omega]
    have hprodB : ∏ i ∈ Finset.range (2 * p + 2 - 2 * k), ((2 * k - 2 - p + i : ℕ) : R)
        = ∏ j ∈ Finset.Ico (2 * k - 2 - p) p, (j : R) := by
      rw [Finset.prod_Ico_eq_prod_range, show p - (2 * k - 2 - p) = 2 * p + 2 - 2 * k by omega]
    rw [hsumB, hprodB]; push_cast; ring
  have hprodNatR : (Nat.factorial (2 * k - 3 - p) : R) * ∏ j ∈ Finset.Ico (2 * k - 2 - p) p, (j : R)
      = (Nat.factorial (p - 1) : R) := by
    rw [← Nat.cast_prod, ← Nat.cast_mul, hprodNat]
  have hHR0 : (p : R) * HR p (p - 1) = 0 :=
    p_mul_of_redp2_zero p (HR p (p - 1)) (by rw [redp2_HR p (p - 1) (by omega)]; exact Hp_p_sub_one p hp5)
  have hcastfin : 4 * ((PB : R) * (PA : R)) = (Nat.choose N p : R) * (Nat.factorial (p - 1) : R) := by
    have := congrArg (Nat.cast (R := R)) hnatfin; push_cast at this; linear_combination this
  rw [hPAR, hPBR] at hcastfin
  have hunit : IsUnit ((Nat.factorial (p - 1) : ℕ) : R) := isUnit_factorial p (p - 1) (by omega)
  apply hunit.mul_left_cancel
  have hp2 : (p : R) ^ 2 = 0 := p_sq_zero p
  rw [show ((Nat.factorial (p - 1) : ℕ) : R) * (4 * (1 + (p : R) * HR p (2 * k - 3 - p)))
      = 4 * (((Nat.factorial (2 * k - 3 - p) : R) * ∏ j ∈ Finset.Ico (2 * k - 2 - p) p, (j : R))
          * (1 + (p : R) * HR p (2 * k - 3 - p))) from by rw [hprodNatR]; ring]
  rw [show ((Nat.factorial (p - 1) : ℕ) : R) * ((Nat.choose N p : ℕ) : R)
      = ((Nat.choose N p : ℕ) : R) * (Nat.factorial (p - 1) : R) from by ring, ← hcastfin]
  linear_combination (48 * (Nat.factorial (2 * k - 3 - p) : R) * (∏ j ∈ Finset.Ico (2 * k - 2 - p) p, (j : R))
      * (HR p (p - 1) - HR p (2 * k - 3 - p)) * HR p (2 * k - 3 - p)) * hp2
      + (12 * (Nat.factorial (2 * k - 3 - p) : R) * (∏ j ∈ Finset.Ico (2 * k - 2 - p) p, (j : R))) * hHR0

/-- Exact natural-number identity underlying the per-term expansion. -/
lemma natIdentity (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    2 * k * (p - 1 + k) * (T (p - 1) k / p ^ 2)
      = Nat.choose (p - 1) k ^ 2 * Nat.choose (p - 1 + k) (k - 1)
          * Nat.choose (3 * (p - 1) + 2 * k) p := by
  set N := 3 * (p - 1) + 2 * k with hN
  have hdvd := (interiorK p k hp5 hk2 hkp).1
  have hTeq : p ^ 2 * (T (p - 1) k / p ^ 2) = T (p - 1) k := Nat.mul_div_cancel' hdvd
  have hTdef : T (p - 1) k
      = Nat.choose (p - 1) k ^ 2 * Nat.choose (p - 1 + k) k * Nat.choose N (p - 1) := by
    unfold T; rw [← hN]
  have hL1 : k * Nat.choose (p - 1 + k) k = p * Nat.choose (p - 1 + k) (k - 1) := by
    have h2 := Nat.choose_succ_right_eq (p - 1 + k) (k - 1)
    rw [show (k - 1) + 1 = k by omega, show (p - 1 + k) - (k - 1) = p by omega] at h2
    rw [Nat.mul_comm k, Nat.mul_comm p]; exact h2
  have hL3 : p * Nat.choose N p = Nat.choose N (p - 1) * (2 * (p - 1 + k)) := by
    have h2 := Nat.choose_succ_right_eq N (p - 1)
    rw [show (p - 1) + 1 = p by omega, show N - (p - 1) = 2 * (p - 1 + k) by rw [hN]; omega] at h2
    rw [Nat.mul_comm p]; exact h2
  apply Nat.eq_of_mul_eq_mul_left (show 0 < p ^ 2 by positivity)
  calc p ^ 2 * (2 * k * (p - 1 + k) * (T (p - 1) k / p ^ 2))
        = 2 * k * (p - 1 + k) * (p ^ 2 * (T (p - 1) k / p ^ 2)) := by ring
    _ = 2 * k * (p - 1 + k) * T (p - 1) k := by rw [hTeq]
    _ = 2 * k * (p - 1 + k)
          * (Nat.choose (p - 1) k ^ 2 * Nat.choose (p - 1 + k) k * Nat.choose N (p - 1)) := by
        rw [hTdef]
    _ = Nat.choose (p - 1) k ^ 2 * (k * Nat.choose (p - 1 + k) k)
          * (Nat.choose N (p - 1) * (2 * (p - 1 + k))) := by ring
    _ = Nat.choose (p - 1) k ^ 2 * (p * Nat.choose (p - 1 + k) (k - 1)) * (p * Nat.choose N p) := by
        rw [hL1, ← hL3]
    _ = p ^ 2 * (Nat.choose (p - 1) k ^ 2 * Nat.choose (p - 1 + k) (k - 1) * Nat.choose N p) := by
        ring

/-- **Per-term expansion** (generic in the region data `mk`, `β`).  Given the leading-binomial
expansion `C(N,p) = mk·(1 + p·H_β)`, the interior term `u_k = T/p²` satisfies
`2·u_k = mk·(1/(k-1) - 1/k)·(1 + p·(H_β - H_{k-1} - 2/k - 1/(k-1)))` in `ZMod (p²)`. -/
lemma per_term_gen (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1)
    (mk : ZMod (p ^ 2)) (β : ℕ)
    (hCN : ((Nat.choose (3 * (p - 1) + 2 * k) p : ℕ) : ZMod (p ^ 2))
      = mk * (1 + (p : ZMod (p ^ 2)) * HR p β)) :
    2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2))
      = mk * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (1 + (p : ZMod (p ^ 2))
            * (HR p β - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
                - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)) := by
  have hP2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_sq_zero p
  -- cast the nat identity
  have hcast : (2 : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) * (((p - 1 : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)))
        * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2))
      = ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ 2)) ^ 2 * ((Nat.choose (p - 1 + k) (k - 1) : ℕ) : ZMod (p ^ 2))
          * ((Nat.choose (3 * (p - 1) + 2 * k) p : ℕ) : ZMod (p ^ 2)) := by
    have hh := congrArg (Nat.cast (R := ZMod (p ^ 2))) (natIdentity p k hp5 hk2 hkp)
    push_cast at hh
    linear_combination hh
  rw [sq_choose_expand p k hp5 hk2 hkp, choose_pk_expand p k hp5 hk2 hkp, hCN] at hcast
  -- units and basic casts
  have hAu : IsUnit ((k : ℕ) : ZMod (p ^ 2)) := isUnit_natCast_lt p k (by omega) (by omega)
  have hkinv : ((k : ℕ) : ZMod (p ^ 2)) * ((k : ℕ) : ZMod (p ^ 2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hAu
  have hk1u : IsUnit ((k - 1 : ℕ) : ZMod (p ^ 2)) := isUnit_natCast_lt p (k - 1) (by omega) (by omega)
  have hk1inv : ((k - 1 : ℕ) : ZMod (p ^ 2)) * ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hk1u
  have hpm : ((p - 1 : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ p by omega)]; push_cast; ring
  have hk1c : ((k - 1 : ℕ) : ZMod (p ^ 2)) = (k : ZMod (p ^ 2)) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega)]; push_cast; ring
  have hk1inv' : ((k : ZMod (p ^ 2)) - 1) * ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 := by rw [← hk1c]; exact hk1inv
  have hHksucc : HR p k = HR p (k - 1) + ((k : ℕ) : ZMod (p ^ 2))⁻¹ := by
    have := HR_succ p (k - 1); rwa [show (k - 1) + 1 = k by omega] at this
  -- Abel-cancellation of the leading factor
  have hAwb : (k : ZMod (p ^ 2)) * (((p - 1 : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)))
        * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
      = 1 + (p : ZMod (p ^ 2)) * ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
    rw [hpm]
    linear_combination (1 - (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2))) * hkinv
      + ((p : ZMod (p ^ 2)) + (k : ZMod (p ^ 2))) * hk1inv'
  -- the unit we cancel
  have hunit : IsUnit ((k : ZMod (p ^ 2)) * (((p - 1 : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)))) := by
    refine hAu.mul ?_
    rw [show ((p - 1 : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)) = ((p - 1 + k : ℕ) : ZMod (p ^ 2)) by push_cast; ring]
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    refine (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => ?_)
    have hd2 : p ∣ (k - 1) := by
      have heq : p - 1 + k = p + (k - 1) := by omega
      rw [heq] at hd; exact (Nat.dvd_add_right (dvd_refl p)).mp hd
    have := Nat.le_of_dvd (by omega) hd2; omega
  apply hunit.mul_left_cancel
  -- LHS side
  have hLHSside : (k : ZMod (p ^ 2)) * (((p - 1 : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)))
      * (2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2)))
      = (1 - 2 * (p : ZMod (p ^ 2)) * HR p k) * (1 + (p : ZMod (p ^ 2)) * HR p (k - 1))
          * (mk * (1 + (p : ZMod (p ^ 2)) * HR p β)) := by
    rw [← hcast]; ring
  rw [hLHSside, hHksucc]
  -- now reduce both sides to the common form
  linear_combination
    (mk * ((-2) * HR p β * HR p (k - 1) ^ 2 * (p : ZMod (p ^ 2))
      - 2 * HR p β * HR p (k - 1) * (p : ZMod (p ^ 2)) * ((k : ℕ) : ZMod (p ^ 2))⁻¹
      - HR p β * HR p (k - 1) - 2 * HR p β * ((k : ℕ) : ZMod (p ^ 2))⁻¹ - 2 * HR p (k - 1) ^ 2
      - 2 * HR p (k - 1) * ((k : ℕ) : ZMod (p ^ 2))⁻¹)) * hP2
    - (mk * (HR p β - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹ - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)
        * ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹) * hP2
    - (mk * (1 + (p : ZMod (p ^ 2)) * (HR p β - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
        - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹))) * hAwb

/-- Nonzero natCast in `ZMod p`. -/
lemma natCast_ne_zero_lt (p m : ℕ) [Fact p.Prime] (hm : 0 < m) (hmp : m < p) :
    ((m : ℕ) : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨by omega⟩
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd; have := Nat.le_of_dvd hm hd; omega

/-- **Region A closed form** for the correction partial sums (in the field `ZMod p`). -/
lemma regionA_closed (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ K, 2 ≤ K → 2 * K ≤ p + 1 →
    ∑ k ∈ Finset.Ico 2 (K + 1),
        (3 * (((k - 1 : ℕ) : ZMod p)⁻¹ - ((k : ℕ) : ZMod p)⁻¹)
          * (Hp p (2 * k - 3) - Hp p (k - 1) - 2 * ((k : ℕ) : ZMod p)⁻¹ - ((k - 1 : ℕ) : ZMod p)⁻¹))
      = 3 * ((2 - ((K : ℕ) : ZMod p)⁻¹) * Hp p (2 * K - 3)
          + ((K : ℕ) : ZMod p)⁻¹ * Hp p K - 2 * Hp p (K - 2)
          - (3 / 2) * ((K - 1 : ℕ) : ZMod p)⁻¹ + ((K : ℕ) : ZMod p)⁻¹
          + (((K : ℕ) : ZMod p)⁻¹) ^ 2 - 5 / 2) := by
  intro K hK2
  induction K, hK2 using Nat.le_induction with
  | base =>
    intro _
    have hHp1 : Hp p 1 = 1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Hp_succ, Hp_zero, zero_add, Nat.cast_one, inv_one]
    have hHp2 : Hp p 2 = 1 + ((2 : ℕ) : ZMod p)⁻¹ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Hp_succ, hHp1]
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty, zero_add]
    simp only [Nat.reduceMul, Nat.reduceSub]
    rw [hHp1, hHp2, Hp_zero, Nat.cast_one, inv_one]
    simp only [Nat.cast_ofNat]
    have h2 : (2 : ZMod p) ≠ 0 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]
      exact natCast_ne_zero_lt p 2 (by omega) (by omega)
    field_simp
    ring
  | succ n hn ih =>
    intro hKc
    have ihv := ih (by omega)
    rw [Finset.sum_Ico_succ_top (by omega), ihv]
    simp only [Nat.add_sub_cancel]
    -- Hp difference facts
    have hA : Hp p (2 * (n + 1) - 3)
        = Hp p (2 * n - 3) + ((2 * n - 2 : ℕ) : ZMod p)⁻¹ + ((2 * n - 1 : ℕ) : ZMod p)⁻¹ := by
      have s1 : Hp p (2 * n - 2) = Hp p (2 * n - 3) + ((2 * n - 2 : ℕ) : ZMod p)⁻¹ := by
        have := Hp_succ p (2 * n - 3); rwa [show (2 * n - 3) + 1 = 2 * n - 2 by omega] at this
      have s2 : Hp p (2 * n - 1) = Hp p (2 * n - 2) + ((2 * n - 1 : ℕ) : ZMod p)⁻¹ := by
        have := Hp_succ p (2 * n - 2); rwa [show (2 * n - 2) + 1 = 2 * n - 1 by omega] at this
      rw [show 2 * (n + 1) - 3 = 2 * n - 1 by omega, s2, s1]
    have hB : Hp p (n + 1) = Hp p n + ((n + 1 : ℕ) : ZMod p)⁻¹ := Hp_succ p n
    have hC : Hp p ((n + 1) - 2) = Hp p (n - 2) + ((n - 1 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (n - 2); rw [show (n - 2) + 1 = n - 1 by omega] at this
      rw [show (n + 1) - 2 = n - 1 by omega, this]
    have hE : Hp p n = Hp p (n - 2) + ((n - 1 : ℕ) : ZMod p)⁻¹ + ((n : ℕ) : ZMod p)⁻¹ := by
      have s1 : Hp p (n - 1) = Hp p (n - 2) + ((n - 1 : ℕ) : ZMod p)⁻¹ := by
        have := Hp_succ p (n - 2); rwa [show (n - 2) + 1 = n - 1 by omega] at this
      have s2 : Hp p n = Hp p (n - 1) + ((n : ℕ) : ZMod p)⁻¹ := by
        have := Hp_succ p (n - 1); rwa [show (n - 1) + 1 = n by omega] at this
      rw [s2, s1]
    rw [hB, hC, hA, hE]
    -- normalise all natCasts to polynomials in (n : ZMod p)
    have e1 : ((n - 1 : ℕ) : ZMod p) = (n : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : ((n + 1 : ℕ) : ZMod p) = (n : ZMod p) + 1 := by push_cast; ring
    have e3 : ((2 * n - 2 : ℕ) : ZMod p) = 2 * (n : ZMod p) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e4 : ((2 * n - 1 : ℕ) : ZMod p) = 2 * (n : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2, e3, e4]
    -- nonzero facts
    have hne0 : (n : ZMod p) ≠ 0 := natCast_ne_zero_lt p n (by omega) (by omega)
    have hne1 : (n : ZMod p) - 1 ≠ 0 := by rw [← e1]; exact natCast_ne_zero_lt p (n - 1) (by omega) (by omega)
    have hne2 : (n : ZMod p) + 1 ≠ 0 := by rw [← e2]; exact natCast_ne_zero_lt p (n + 1) (by omega) (by omega)
    have hne3 : 2 * (n : ZMod p) - 2 ≠ 0 := by rw [← e3]; exact natCast_ne_zero_lt p (2 * n - 2) (by omega) (by omega)
    have hne4 : 2 * (n : ZMod p) - 1 ≠ 0 := by rw [← e4]; exact natCast_ne_zero_lt p (2 * n - 1) (by omega) (by omega)
    have hne5 : (2 : ZMod p) ≠ 0 := natCast_ne_zero_lt p 2 (by omega) (by omega)
    field_simp
    ring

/-- **Region B closed form** for the correction partial sums (in the field `ZMod p`). -/
lemma regionB_closed (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) :
    ∀ K, (p + 3) / 2 ≤ K → K ≤ p - 1 →
    ∑ k ∈ Finset.Ico ((p + 3) / 2) (K + 1),
        (4 * (((k - 1 : ℕ) : ZMod p)⁻¹ - ((k : ℕ) : ZMod p)⁻¹)
          * (Hp p (2 * k - 3 - p) - Hp p (k - 1) - 2 * ((k : ℕ) : ZMod p)⁻¹ - ((k - 1 : ℕ) : ZMod p)⁻¹))
      = 4 * ((1 - ((K : ℕ) : ZMod p)⁻¹) * Hp p (2 * K - 3 - p)
          + (((K : ℕ) : ZMod p)⁻¹ - 3 / 2) * Hp p (K - 1)
          + (1 / 2) * Hp p (K - (p + 3) / 2) - (1 / 2) * Hp p ((p + 3) / 2 - 1)
          + ((K : ℕ) : ZMod p)⁻¹ + 2 * (((K : ℕ) : ZMod p)⁻¹) ^ 2 - 6) := by
  set c := (p + 3) / 2 with hcdef
  have hc2 : 2 * c = p + 3 := by omega
  have hcval : ((c : ℕ) : ZMod p) = 3 * (2 : ZMod p)⁻¹ := by
    have h2ne : (2 : ZMod p) ≠ 0 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 2 (by omega) (by omega)
    have : ((c : ℕ) : ZMod p) * 2 = 3 := by
      rw [show ((c : ℕ) : ZMod p) * 2 = ((2 * c : ℕ) : ZMod p) by push_cast; ring, hc2]
      push_cast; rw [ZMod.natCast_self]; ring
    field_simp
    linear_combination this
  intro K hKc
  induction K, hKc using Nat.le_induction with
  | base =>
    intro _
    have h0 : (2 * c - 3 - p) = 0 := by omega
    have h0' : (c - c) = 0 := by omega
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty, zero_add,
      h0, h0', Hp_zero]
    have h2ne : (2 : ZMod p) ≠ 0 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 2 (by omega) (by omega)
    have h3ne : (3 : ZMod p) ≠ 0 := by
      rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 3 (by omega) (by omega)
    have hcm1 : ((c - 1 : ℕ) : ZMod p) = (2 : ZMod p)⁻¹ := by
      have : ((c - 1 : ℕ) : ZMod p) * 2 = 1 := by
        rw [show ((c - 1 : ℕ) : ZMod p) * 2 = ((2 * (c - 1) : ℕ) : ZMod p) by push_cast; ring,
          show 2 * (c - 1) = p + 1 by omega]
        push_cast; rw [ZMod.natCast_self]; ring
      field_simp; linear_combination this
    have hcm1ne : ((c - 1 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_lt p (c - 1) (by omega) (by omega)
    have hcne : ((c : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_lt p c (by omega) (by omega)
    rw [hcval, hcm1]
    field_simp
    ring
  | succ n hn ih =>
    intro hKp
    have ihv := ih (by omega)
    rw [Finset.sum_Ico_succ_top (by omega), ihv]
    simp only [Nat.add_sub_cancel]
    have hA : Hp p (2 * (n + 1) - 3 - p)
        = Hp p (2 * n - 3 - p) + ((2 * n - 2 - p : ℕ) : ZMod p)⁻¹ + ((2 * n - 1 - p : ℕ) : ZMod p)⁻¹ := by
      have s1 : Hp p (2 * n - 2 - p) = Hp p (2 * n - 3 - p) + ((2 * n - 2 - p : ℕ) : ZMod p)⁻¹ := by
        have := Hp_succ p (2 * n - 3 - p); rwa [show (2 * n - 3 - p) + 1 = 2 * n - 2 - p by omega] at this
      have s2 : Hp p (2 * n - 1 - p) = Hp p (2 * n - 2 - p) + ((2 * n - 1 - p : ℕ) : ZMod p)⁻¹ := by
        have := Hp_succ p (2 * n - 2 - p); rwa [show (2 * n - 2 - p) + 1 = 2 * n - 1 - p by omega] at this
      rw [show 2 * (n + 1) - 3 - p = 2 * n - 1 - p by omega, s2, s1]
    have hBn : Hp p n = Hp p (n - 1) + ((n : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (n - 1); rwa [show (n - 1) + 1 = n by omega] at this
    have hC : Hp p ((n + 1) - c) = Hp p (n - c) + ((n + 1 - c : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (n - c); rw [show (n - c) + 1 = n + 1 - c by omega] at this
      rw [show (n + 1) - c = n + 1 - c by omega, this]
    rw [hA, hC, hBn]
    -- cast normalisations
    have e_n1 : ((n + 1 : ℕ) : ZMod p) = (n : ZMod p) + 1 := by push_cast; ring
    have e_nm1 : ((n - 1 : ℕ) : ZMod p) = (n : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e_2n2p : ((2 * n - 2 - p : ℕ) : ZMod p) = 2 * (n : ZMod p) - 2 := by
      rw [Nat.cast_sub (show p ≤ 2 * n - 2 by omega), Nat.cast_sub (show 2 ≤ 2 * n by omega),
        ZMod.natCast_self]; push_cast; ring
    have e_2n1p : ((2 * n - 1 - p : ℕ) : ZMod p) = 2 * (n : ZMod p) - 1 := by
      rw [Nat.cast_sub (show p ≤ 2 * n - 1 by omega), Nat.cast_sub (show 1 ≤ 2 * n by omega),
        ZMod.natCast_self]; push_cast; ring
    have h2ne : (2 : ZMod p) ≠ 0 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 2 (by omega) (by omega)
    -- ((n+1-c)) = (2n-1)/2  as field element
    have hYrel : 2 * ((n + 1 - c : ℕ) : ZMod p) = 2 * (n : ZMod p) - 1 := by
      rw [show 2 * ((n + 1 - c : ℕ) : ZMod p) = ((2 * (n + 1 - c) : ℕ) : ZMod p) by push_cast; ring,
        show 2 * (n + 1 - c) = 2 * n - 1 - p by omega, e_2n1p]
    have e_c : ((n + 1 - c : ℕ) : ZMod p) = (2 * (n : ZMod p) - 1) * (2 : ZMod p)⁻¹ := by
      field_simp; linear_combination hYrel
    have e_cinv : ((n + 1 - c : ℕ) : ZMod p)⁻¹ = (2 : ZMod p) * (2 * (n : ZMod p) - 1)⁻¹ := by
      rw [e_c, mul_inv_rev, inv_inv]
    rw [e_n1, e_2n2p, e_2n1p, e_cinv]
    have hne0 : (n : ZMod p) ≠ 0 := natCast_ne_zero_lt p n (by omega) (by omega)
    have hne1 : (n : ZMod p) - 1 ≠ 0 := by rw [← e_nm1]; exact natCast_ne_zero_lt p (n - 1) (by omega) (by omega)
    have hne2 : (n : ZMod p) + 1 ≠ 0 := by rw [← e_n1]; exact natCast_ne_zero_lt p (n + 1) (by omega) (by omega)
    have hne3 : 2 * (n : ZMod p) - 2 ≠ 0 := by rw [← e_2n2p]; exact natCast_ne_zero_lt p (2 * n - 2 - p) (by omega) (by omega)
    have hne4 : 2 * (n : ZMod p) - 1 ≠ 0 := by rw [← e_2n1p]; exact natCast_ne_zero_lt p (2 * n - 1 - p) (by omega) (by omega)
    have hne3' : (n : ZMod p) * 2 - 2 ≠ 0 := by rw [mul_comm]; exact hne3
    have hne4' : (n : ZMod p) * 2 - 1 ≠ 0 := by rw [mul_comm]; exact hne4
    field_simp
    ring

/-- Region A decomposition of `∑ 2 u_k` into leading (telescoping) part plus `p ·` correction. -/
lemma decompA (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) :
    ∑ k ∈ Finset.Ico 2 ((p + 3) / 2), 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2))
      = 3 * (((1 : ℕ) : ZMod (p ^ 2))⁻¹ - (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹)
        + (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Ico 2 ((p + 3) / 2),
            (3 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
              * (HR p (2 * k - 3) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
                  - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)) := by
  set g : ℕ → ZMod (p ^ 2) := fun j => ((j : ℕ) : ZMod (p ^ 2))⁻¹ with hg
  have hterm : ∀ k ∈ Finset.Ico 2 ((p + 3) / 2),
      2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2))
      = 3 * (g (k - 1) - g k)
        + (p : ZMod (p ^ 2)) * (3 * (g (k - 1) - g k)
            * (HR p (2 * k - 3) - HR p (k - 1) - 2 * g k - g (k - 1))) := by
    intro k hk; rw [Finset.mem_Ico] at hk
    have hkA : 2 * k ≤ p + 1 := by omega
    have hpt := per_term_gen p k hp5 (by omega) (by omega) 3 (2 * k - 3)
      (CNp_regionA p k hp5 (by omega) hkA)
    simp only [hg]
    rw [hpt]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [teleIco g 2 ((p + 3) / 2) (by omega) (by omega)]
  · rw [← Finset.mul_sum]

/-- Region B decomposition of `∑ 2 u_k` into leading (telescoping) part plus `p ·` correction. -/
lemma decompB (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) :
    ∑ k ∈ Finset.Ico ((p + 3) / 2) p, 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2))
      = 4 * ((((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((p - 1 : ℕ) : ZMod (p ^ 2))⁻¹)
        + (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Ico ((p + 3) / 2) p,
            (4 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
              * (HR p (2 * k - 3 - p) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
                  - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)) := by
  set g : ℕ → ZMod (p ^ 2) := fun j => ((j : ℕ) : ZMod (p ^ 2))⁻¹ with hg
  have hterm : ∀ k ∈ Finset.Ico ((p + 3) / 2) p,
      2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2))
      = 4 * (g (k - 1) - g k)
        + (p : ZMod (p ^ 2)) * (4 * (g (k - 1) - g k)
            * (HR p (2 * k - 3 - p) - HR p (k - 1) - 2 * g k - g (k - 1))) := by
    intro k hk; rw [Finset.mem_Ico] at hk
    have hkB : p + 3 ≤ 2 * k := by omega
    have hpt := per_term_gen p k hp5 (by omega) (by omega) 4 (2 * k - 3 - p)
      (CNp_regionB p k hp5 hkB (by omega))
    simp only [hg]
    rw [hpt]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [teleIco g ((p + 3) / 2) p (by omega) (by omega)]
  · rw [← Finset.mul_sum]

/-- Region A correction sum reduces (mod `p`) to `39/2`. -/
lemma evalA (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) :
    redp2 p (∑ k ∈ Finset.Ico 2 ((p + 3) / 2),
      (3 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (HR p (2 * k - 3) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
            - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)))
      = 39 * (2 : ZMod p)⁻¹ := by
  set c := (p + 3) / 2 with hcdef
  have hc2 : 2 * c = p + 3 := by omega
  rw [map_sum]
  have hpush : ∀ k ∈ Finset.Ico 2 c, redp2 p
      (3 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (HR p (2 * k - 3) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
            - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹))
      = 3 * (((k - 1 : ℕ) : ZMod p)⁻¹ - ((k : ℕ) : ZMod p)⁻¹)
        * (Hp p (2 * k - 3) - Hp p (k - 1) - 2 * ((k : ℕ) : ZMod p)⁻¹
            - ((k - 1 : ℕ) : ZMod p)⁻¹) := by
    intro k hk; rw [Finset.mem_Ico] at hk
    have hd_k : ¬ p ∣ k := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hd_k1 : ¬ p ∣ (k - 1) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    simp only [map_mul, map_sub, map_ofNat, redp2_inv p k hd_k, redp2_inv p (k - 1) hd_k1,
      redp2_HR p (2 * k - 3) (by omega), redp2_HR p (k - 1) (by omega)]
  rw [Finset.sum_congr rfl hpush]
  have hcl := regionA_closed p hp5 (c - 1) (by omega) (by omega)
  rw [show c - 1 + 1 = c by omega] at hcl
  rw [hcl, show 2 * (c - 1) - 3 = p - 2 by omega, show (c - 1) - 2 = c - 3 by omega,
    show (c - 1) - 1 = c - 2 by omega]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 2 (by omega) (by omega)
  have hne1 : ((c - 1 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_lt p (c - 1) (by omega) (by omega)
  have hne2 : ((c - 2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_lt p (c - 2) (by omega) (by omega)
  have hKinv : ((c - 1 : ℕ) : ZMod p)⁻¹ = 2 := by
    have h1 : ((c - 1 : ℕ) : ZMod p) * 2 = 1 := by
      rw [show ((c - 1 : ℕ) : ZMod p) * 2 = ((2 * (c - 1) : ℕ) : ZMod p) by push_cast; ring,
        show 2 * (c - 1) = p + 1 by omega]
      push_cast; rw [ZMod.natCast_self]; ring
    field_simp; linear_combination -h1
  have hK1inv : ((c - 2 : ℕ) : ZMod p)⁻¹ = -2 := by
    have h1 : ((c - 2 : ℕ) : ZMod p) * 2 = -1 := by
      rw [show ((c - 2 : ℕ) : ZMod p) * 2 = ((2 * (c - 2) : ℕ) : ZMod p) by push_cast; ring,
        show 2 * (c - 2) = p - 1 by omega, Nat.cast_sub (by omega)]
      push_cast; rw [ZMod.natCast_self]; ring
    field_simp; linear_combination h1
  have hHdiff : Hp p (c - 1) = Hp p (c - 3) + ((c - 2 : ℕ) : ZMod p)⁻¹ + ((c - 1 : ℕ) : ZMod p)⁻¹ := by
    have s1 : Hp p (c - 2) = Hp p (c - 3) + ((c - 2 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (c - 3); rwa [show (c - 3) + 1 = c - 2 by omega] at this
    have s2 : Hp p (c - 1) = Hp p (c - 2) + ((c - 1 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (c - 2); rwa [show (c - 2) + 1 = c - 1 by omega] at this
    rw [s2, s1]
  rw [hHdiff, hKinv, hK1inv]
  field_simp
  ring

/-- Region B correction sum reduces (mod `p`) to `-12`. -/
lemma evalB (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) :
    redp2 p (∑ k ∈ Finset.Ico ((p + 3) / 2) p,
      (4 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (HR p (2 * k - 3 - p) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
            - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)))
      = -12 := by
  rw [map_sum]
  have hpush : ∀ k ∈ Finset.Ico ((p + 3) / 2) p, redp2 p
      (4 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (HR p (2 * k - 3 - p) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
            - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹))
      = 4 * (((k - 1 : ℕ) : ZMod p)⁻¹ - ((k : ℕ) : ZMod p)⁻¹)
        * (Hp p (2 * k - 3 - p) - Hp p (k - 1) - 2 * ((k : ℕ) : ZMod p)⁻¹
            - ((k - 1 : ℕ) : ZMod p)⁻¹) := by
    intro k hk; rw [Finset.mem_Ico] at hk
    have hd_k : ¬ p ∣ k := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    have hd_k1 : ¬ p ∣ (k - 1) := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    simp only [map_mul, map_sub, map_ofNat, redp2_inv p k hd_k, redp2_inv p (k - 1) hd_k1,
      redp2_HR p (2 * k - 3 - p) (by omega), redp2_HR p (k - 1) (by omega)]
  rw [Finset.sum_congr rfl hpush]
  have hcl := regionB_closed p hp5 hpodd (p - 1) (by omega) (by omega)
  rw [show p - 1 + 1 = p by omega] at hcl
  rw [hcl, show 2 * (p - 1) - 3 - p = p - 5 by omega, show p - 1 - 1 = p - 2 by omega]
  -- special values
  have h2ne : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 2 (by omega) (by omega)
  have h3ne : (3 : ZMod p) ≠ 0 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 3 (by omega) (by omega)
  have h4ne : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 4 (by omega) (by omega)
  have hpm1inv : ((p - 1 : ℕ) : ZMod p)⁻¹ = -1 := by
    have := inv_reflect p 1 (by omega) (by omega); simpa using this
  have hHp_pm2 : Hp p (p - 2) = 1 := by
    have e := Hp_p_sub_one p hp5
    have s4 : Hp p (p - 1) = Hp p (p - 2) + ((p - 1 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (p - 2); rwa [show (p - 2) + 1 = p - 1 by omega] at this
    rw [hpm1inv, e] at s4
    linear_combination -s4
  have hHp_pm5 : Hp p (p - 5) = (4 : ZMod p)⁻¹ + (3 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ + 1 := by
    have e := Hp_p_sub_one p hp5
    have s1 : Hp p (p - 4) = Hp p (p - 5) + ((p - 4 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (p - 5); rwa [show (p - 5) + 1 = p - 4 by omega] at this
    have s2 : Hp p (p - 3) = Hp p (p - 4) + ((p - 3 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (p - 4); rwa [show (p - 4) + 1 = p - 3 by omega] at this
    have s3 : Hp p (p - 2) = Hp p (p - 3) + ((p - 2 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (p - 3); rwa [show (p - 3) + 1 = p - 2 by omega] at this
    have s4 : Hp p (p - 1) = Hp p (p - 2) + ((p - 1 : ℕ) : ZMod p)⁻¹ := by
      have := Hp_succ p (p - 2); rwa [show (p - 2) + 1 = p - 1 by omega] at this
    have chain : Hp p (p - 1) = Hp p (p - 5) + ((p - 4 : ℕ) : ZMod p)⁻¹
        + ((p - 3 : ℕ) : ZMod p)⁻¹ + ((p - 2 : ℕ) : ZMod p)⁻¹ + ((p - 1 : ℕ) : ZMod p)⁻¹ := by
      rw [s4, s3, s2, s1]
    have r4 := inv_reflect p 4 (by omega) (by omega)
    have r3 := inv_reflect p 3 (by omega) (by omega)
    have r2 := inv_reflect p 2 (by omega) (by omega)
    have r1 := inv_reflect p 1 (by omega) (by omega)
    simp only [Nat.cast_ofNat, Nat.cast_one, inv_one] at r4 r3 r2 r1
    rw [r4, r3, r2, r1, e] at chain
    linear_combination -chain
  have hcmul : (((p + 3) / 2 : ℕ) : ZMod p) * 2 = 3 := by
    rw [show (((p + 3) / 2 : ℕ) : ZMod p) * 2 = ((2 * ((p + 3) / 2) : ℕ) : ZMod p) by push_cast; ring,
      show 2 * ((p + 3) / 2) = p + 3 by omega]
    push_cast; rw [ZMod.natCast_self]; ring
  have hcne : (((p + 3) / 2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_lt p ((p + 3) / 2) (by omega) (by omega)
  have hcinv : (((p + 3) / 2 : ℕ) : ZMod p)⁻¹ = 2 * (3 : ZMod p)⁻¹ := by
    field_simp; linear_combination -hcmul
  have hHpc : Hp p ((p + 3) / 2) = Hp p ((p + 3) / 2 - 1) + (((p + 3) / 2 : ℕ) : ZMod p)⁻¹ := by
    have := Hp_succ p ((p + 3) / 2 - 1); rwa [show (p + 3) / 2 - 1 + 1 = (p + 3) / 2 by omega] at this
  rw [Hp_reflect p ((p + 3) / 2) hp5 (by omega), hHpc, hHp_pm2, hHp_pm5, hpm1inv, hcinv]
  field_simp
  ring

/-- Main mod-`p²` evaluation of the interior sum: `4·M ≡ 18 + 19 p`. -/
lemma hM4main (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    4 * (∑ k ∈ Finset.Ico 2 p, ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2)))
      = 18 + 19 * (p : ZMod (p ^ 2)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have hP2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_sq_zero p
  -- consecutive split of the doubled sum
  have hcons := (Finset.sum_Ico_consecutive
      (fun k => 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2)))
      (show 2 ≤ (p + 3) / 2 by omega) (show (p + 3) / 2 ≤ p by omega)).symm
  rw [decompA p hp5 hpodd, decompB p hp5 hpodd] at hcons
  -- fold the two correction sums
  set SA := ∑ k ∈ Finset.Ico 2 ((p + 3) / 2),
      (3 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (HR p (2 * k - 3) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
            - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)) with hSA
  set SB := ∑ k ∈ Finset.Ico ((p + 3) / 2) p,
      (4 * (((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹ - ((k : ℕ) : ZMod (p ^ 2))⁻¹)
        * (HR p (2 * k - 3 - p) - HR p (k - 1) - 2 * ((k : ℕ) : ZMod (p ^ 2))⁻¹
            - ((k - 1 : ℕ) : ZMod (p ^ 2))⁻¹)) with hSB
  -- rewrite LHS of hcons as `2 * M`
  rw [show (∑ k ∈ Finset.Ico 2 p, 2 * ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2)))
      = 2 * (∑ k ∈ Finset.Ico 2 p, ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2)))
      from by rw [Finset.mul_sum]] at hcons
  -- endpoint values
  have hg1 : ((1 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 := by norm_num
  have hcu : IsUnit (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2)) :=
    isUnit_natCast_lt p ((p + 3) / 2 - 1) (by omega) (by omega)
  have h2c : (2 : ZMod (p ^ 2)) * (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) + 1 := by
    rw [show (2 : ZMod (p ^ 2)) * (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))
        = ((2 * ((p + 3) / 2 - 1) : ℕ) : ZMod (p ^ 2)) by push_cast; ring,
      show 2 * ((p + 3) / 2 - 1) = p + 1 by omega]
    push_cast; ring
  have hcmul : (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2)) * (2 - 2 * (p : ZMod (p ^ 2))) = 1 := by
    linear_combination (1 - (p : ZMod (p ^ 2))) * h2c - hP2
  have hcinvmul : (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹ * (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2)) = 1 :=
    ZMod.inv_mul_of_unit _ hcu
  have hX : (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹ = 2 - 2 * (p : ZMod (p ^ 2)) := by
    calc (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹
        = (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹
            * ((((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2)) * (2 - 2 * (p : ZMod (p ^ 2)))) := by
          rw [hcmul, mul_one]
      _ = ((((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2))⁻¹ * (((p + 3) / 2 - 1 : ℕ) : ZMod (p ^ 2)))
            * (2 - 2 * (p : ZMod (p ^ 2))) := by ring
      _ = 2 - 2 * (p : ZMod (p ^ 2)) := by rw [hcinvmul, one_mul]
  have hpu : IsUnit ((p - 1 : ℕ) : ZMod (p ^ 2)) := isUnit_natCast_lt p (p - 1) (by omega) (by omega)
  have hpm1c : ((p - 1 : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hymul : ((p - 1 : ℕ) : ZMod (p ^ 2)) * (-1 - (p : ZMod (p ^ 2))) = 1 := by
    rw [hpm1c]; linear_combination -hP2
  have hyinvmul : ((p - 1 : ℕ) : ZMod (p ^ 2))⁻¹ * ((p - 1 : ℕ) : ZMod (p ^ 2)) = 1 :=
    ZMod.inv_mul_of_unit _ hpu
  have hY : ((p - 1 : ℕ) : ZMod (p ^ 2))⁻¹ = -1 - (p : ZMod (p ^ 2)) := by
    calc ((p - 1 : ℕ) : ZMod (p ^ 2))⁻¹
        = ((p - 1 : ℕ) : ZMod (p ^ 2))⁻¹
            * (((p - 1 : ℕ) : ZMod (p ^ 2)) * (-1 - (p : ZMod (p ^ 2)))) := by rw [hymul, mul_one]
      _ = (((p - 1 : ℕ) : ZMod (p ^ 2))⁻¹ * ((p - 1 : ℕ) : ZMod (p ^ 2)))
            * (-1 - (p : ZMod (p ^ 2))) := by ring
      _ = -1 - (p : ZMod (p ^ 2)) := by rw [hyinvmul, one_mul]
  -- the `p·(correction)` collapse
  have hPsum : (p : ZMod (p ^ 2)) * (2 * (SA + SB)) = (p : ZMod (p ^ 2)) * 15 := by
    apply p_mul_eq_of_redp2_eq
    rw [hSA, hSB]
    simp only [map_mul, map_add, map_ofNat]
    rw [evalA p hp5 hpodd, evalB p hp5 hpodd]
    have h2ne : (2 : ZMod p) ≠ 0 := by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num]; exact natCast_ne_zero_lt p 2 (by omega) (by omega)
    field_simp
    ring
  linear_combination 2 * hcons + hPsum + 6 * hg1 + 2 * hX - 8 * hY

lemma interiorSum (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((p : ℤ)) ^ 2 ∣
      (3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2)
          * (∑ k ∈ Finset.Ico 2 p, ((T (p - 1) k / p ^ 2 : ℕ) : ℤ))
        - ((2 - 2 * (p : ℤ)) * ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2)) - (9 * (p : ℤ) - 5)) := by
  rw [show ((p : ℤ)) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; ring,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Int.cast_sum, Int.cast_one]
  have hP2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_sq_zero p
  have hM4 := hM4main p hp5
  have h4u : IsUnit (4 : ZMod (p ^ 2)) := by
    rw [show (4 : ZMod (p ^ 2)) = ((4 : ℕ) : ZMod (p ^ 2)) by norm_num]
    exact isUnit_natCast_lt p 4 (by omega) (by omega)
  have hkey : 4 * ((3 * (p : ZMod (p ^ 2)) - 1) * (3 * (p : ZMod (p ^ 2)) - 2)
        * (∑ k ∈ Finset.Ico 2 p, ((T (p - 1) k / p ^ 2 : ℕ) : ZMod (p ^ 2)))
        - ((2 - 2 * (p : ZMod (p ^ 2))) * ((3 * (p : ZMod (p ^ 2)) - 1) * (3 * (p : ZMod (p ^ 2)) - 2))
            - (9 * (p : ZMod (p ^ 2)) - 5))) = 0 := by
    linear_combination ((3 * (p : ZMod (p ^ 2)) - 1) * (3 * (p : ZMod (p ^ 2)) - 2)) * hM4
      + (243 * (p : ZMod (p ^ 2)) - 153) * hP2
  exact h4u.mul_left_cancel (by rw [mul_zero]; exact hkey)

theorem refine1 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 4 ∣ (aa (p - 1) : ℤ) + (p : ℤ) ^ 3 := by
  haveI := Fact.mk hp
  set D : ℤ := (3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2) with hD
  set C1 : ℤ := (Nat.choose (3 * p - 1) (p - 1) : ℤ) with hC1
  set M : ℕ := ∑ k ∈ Finset.Ico 2 p, (T (p - 1) k / p ^ 2) with hM
  -- Σ T_k = p^2 * M
  have hSeq : ∑ k ∈ Finset.Ico 2 p, T (p - 1) k = p ^ 2 * M := by
    rw [hM, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_Ico] at hk
    obtain ⟨hdvd, _⟩ := interiorK p k hp5 (by omega) (by omega)
    rw [Nat.mul_div_cancel' hdvd]
  -- integer expression for aa
  have haaZ : (aa (p - 1) : ℤ)
      = (T (p - 1) 0 : ℤ) + (T (p - 1) 1 : ℤ) + (p : ℤ) ^ 2 * (M : ℤ) := by
    rw [haa p hp5]
    have : ((∑ k ∈ Finset.Ico 2 p, T (p - 1) k : ℕ) : ℤ) = (p : ℤ) ^ 2 * (M : ℤ) := by
      rw [hSeq]; push_cast; ring
    push_cast [this]; ring
  -- factC as integer identity: T0 * D = C1 * (2p)(2p-1)
  have hfc : (T (p - 1) 0 : ℤ) * D = C1 * ((2 * (p : ℤ)) * (2 * (p : ℤ) - 1)) := by
    rw [T0eq p hp5]
    have h := congrArg (Nat.cast : ℕ → ℤ) (factC p hp5)
    push_cast [Nat.cast_sub (show 1 ≤ 3 * p by omega), Nat.cast_sub (show 2 ≤ 3 * p by omega),
      Nat.cast_sub (show 1 ≤ 2 * p by omega)] at h
    rw [hD, hC1]; linear_combination h
  -- T1 = (p-1)^2 * p * C1
  have hT1 : (T (p - 1) 1 : ℤ) = ((p : ℤ) - 1) ^ 2 * (p : ℤ) * C1 := by
    rw [T1eq p hp5, hC1]; push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; ring
  -- C1 = 1 + p^3 * m
  obtain ⟨m, hm⟩ := hC1dvd3 p hp5
  have hC1val : C1 = 1 + (p : ℤ) ^ 3 * m := by rw [hC1]; linarith [hm]
  -- interior
  obtain ⟨q, hq⟩ := interiorSum p hp5
  have hMcast : (M : ℤ) = ∑ k ∈ Finset.Ico 2 p, ((T (p - 1) k / p ^ 2 : ℕ) : ℤ) := by
    rw [hM, Nat.cast_sum]
  have hqval : D * (M : ℤ)
      = (2 - 2 * (p : ℤ)) * D - (9 * (p : ℤ) - 5) + (p : ℤ) ^ 2 * q := by
    rw [hD, hMcast]; linarith [hq]
  -- key: p^4 ∣ D * (aa + p^3)
  have hkey : (p : ℤ) ^ 4 ∣ D * ((aa (p - 1) : ℤ) + (p : ℤ) ^ 3) := by
    have hexpand : D * ((aa (p - 1) : ℤ) + (p : ℤ) ^ 3)
        = C1 * ((2 * (p : ℤ)) * (2 * (p : ℤ) - 1))
          + D * (((p : ℤ) - 1) ^ 2 * (p : ℤ) * C1)
          + (p : ℤ) ^ 2 * (D * (M : ℤ)) + D * (p : ℤ) ^ 3 := by
      linear_combination D * haaZ + hfc + D * hT1
    rw [hexpand, hC1val, hqval]
    refine ⟨(2 * (2 * (p : ℤ) - 1)) * m
        + D * (((p : ℤ) - 1) ^ 2 * m) + q, ?_⟩
    rw [hD]; ring
  -- coprimality of D and p
  have hcop : IsCoprime ((p : ℤ) ^ 4) D := by
    have h3 := huCoprime p hp hp5
    rw [hD]
    have hbase : IsCoprime (p : ℤ) ((3 * (p : ℤ) - 1) * (3 * (p : ℤ) - 2)) :=
      (IsCoprime.pow_left_iff (by norm_num)).mp h3
    exact hbase.pow_left
  exact hcop.dvd_of_dvd_mul_left hkey


/- ===== From Base2.lean ===== -/

/-!
# Base2 : `lucas13` and `base2`
-/

open Finset

/-- `aa p ≡ 13 (mod p)` for primes `p ≥ 5`. -/
lemma lucas13 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : (aa p : ZMod p) = 13 := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨by omega⟩
  have hp0 : 0 < p := by omega
  -- Lucas: choose (a*p) p ≡ a (mod p).
  have lucasM : ∀ a : ℕ, (Nat.choose (a * p) p : ZMod p) = (a : ZMod p) := by
    intro a
    apply modToZMod
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := a * p) (k := p) (p := p)
    rw [Nat.mul_mod_left, Nat.mod_self, Nat.mul_div_cancel _ hp0, Nat.div_self hp0,
        Nat.choose_zero_right, Nat.choose_one_right, one_mul] at h
    exact h
  -- Cast the sum into `ZMod p`.
  have hcast : (aa p : ZMod p) = ∑ k ∈ Finset.range (p + 1), (T p k : ZMod p) := by
    unfold aa; rw [Nat.cast_sum]
  rw [hcast, Finset.sum_range_succ]
  -- Interior terms vanish.
  have hinner : ∑ k ∈ Finset.range p, (T p k : ZMod p) = (T p 0 : ZMod p) := by
    apply Finset.sum_eq_single 0
    · intro k hk hk0
      rw [Finset.mem_range] at hk
      have hpdT : p ∣ T p k := by
        unfold T
        have h2 : p ∣ Nat.choose p k ^ 2 :=
          dvd_pow (hp.dvd_choose_self hk0 hk) (by norm_num)
        exact (h2.mul_right _).mul_right _
      rw [ZMod.natCast_eq_zero_iff]
      exact hpdT
    · intro h
      exact absurd (Finset.mem_range.mpr hp0) h
  rw [hinner]
  -- Evaluate the two surviving terms.
  have hT0eq : T p 0 = Nat.choose (3 * p) p := by unfold T; simp
  have hTppeq : T p p = Nat.choose (2 * p) p * Nat.choose (5 * p) p := by
    unfold T
    rw [Nat.choose_self, one_pow, one_mul,
        show p + p = 2 * p by ring, show 3 * p + 2 * p = 5 * p by ring]
  have hT0 : (T p 0 : ZMod p) = 3 := by rw [hT0eq, lucasM 3]; norm_num
  have hTpp : (T p p : ZMod p) = 10 := by
    rw [hTppeq]; push_cast; rw [lucasM 2, lucasM 5]; norm_num
  rw [hT0, hTpp]; norm_num

/-- `p^3 ∣ aa (p-2)` for primes `p ≥ 17`. -/
lemma base2 (p : ℕ) (hp : Nat.Prime p) (hp17 : 17 ≤ p) : (p : ℤ) ^ 3 ∣ (aa (p - 2) : ℤ) := by
  haveI := Fact.mk hp
  have hp5 : 5 ≤ p := by omega
  have hp0 : 0 < p := by omega
  have hp_ne : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- The recurrence at `n = p-2`.
  have hcp2 : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ p by omega)]; norm_num
  have hrec := aa_rec (p - 2)
  rw [show (p - 2) + 2 = p by omega, show (p - 2) + 1 = p - 1 by omega, hcp2] at hrec
  -- KEY 1 setup: factor cc2.
  set A : ℤ := (16 * (4 * (p : ℤ) - 3) ^ 2 * (4 * (p : ℤ) - 1) ^ 2 * Sc ((p : ℤ) - 2)) with hA
  have hcc2 : cc2 ((p : ℤ) - 2) = (p : ℤ) ^ 3 * A := by
    rw [hA]; simp only [cc2, Sc]; ring
  -- The mod-p vanishing.
  have hUcc1 : (p : ℤ) ∣ (A * (aa p : ℤ) - cc1 ((p : ℤ) - 2)) := by
    have h13 : ((aa p : ℕ) : ZMod p) = 13 := lucas13 p hp hp5
    rw [hA, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [Sc, cc1, P11]
    rw [ZMod.natCast_self, h13]
    norm_num
  obtain ⟨s, hs⟩ := hUcc1
  obtain ⟨t, ht⟩ := refine1 p hp hp5
  set V : ℤ := s + cc1 ((p : ℤ) - 2) * t with hV
  have hkey1 : cc2 ((p : ℤ) - 2) * (aa p : ℤ) + cc1 ((p : ℤ) - 2) * (aa (p - 1) : ℤ)
      = (p : ℤ) ^ 4 * V := by
    have haa1 : (aa (p - 1) : ℤ) = (p : ℤ) ^ 4 * t - (p : ℤ) ^ 3 := by linarith [ht]
    rw [hcc2, haa1, hV]
    linear_combination (p : ℤ) ^ 3 * hs
  -- KEY 2 setup: factor cc0.
  set W0 : ℤ := (-27 * (3 * (p : ℤ) - 5) ^ 3 * (3 * (p : ℤ) - 4) ^ 3 * Sc ((p : ℤ) - 1)) with hW0
  have hcc0 : cc0 ((p : ℤ) - 2) = (p : ℤ) * W0 := by
    rw [hW0]; simp only [cc0, Sc]; ring
  have hcop : IsCoprime (p : ℤ) W0 := by
    rw [hpz.coprime_iff_not_dvd]
    intro hdvd
    have hpoly : (p : ℤ) ∣ (W0 + 16848000) := by
      rw [hW0, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast [Sc]
      rw [ZMod.natCast_self]
      norm_num
    have hd : (p : ℤ) ∣ (16848000 : ℤ) := by
      have := dvd_sub hpoly hdvd
      simpa using this
    have hdN : p ∣ 16848000 := by
      rwa [show (16848000 : ℤ) = ((16848000 : ℕ) : ℤ) by norm_num,
        Int.natCast_dvd_natCast] at hd
    rw [show (16848000 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 ^ 3 * 13 by norm_num] at hdN
    rcases (hp.dvd_mul.mp hdN) with h | h13
    · rcases (hp.dvd_mul.mp h) with h' | h5
      · rcases (hp.dvd_mul.mp h') with h2 | h3
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5); omega
    · have := Nat.le_of_dvd (by norm_num) h13; omega
  -- Combine.
  have hcomb : (p : ℤ) * W0 * (aa (p - 2) : ℤ) = -((p : ℤ) ^ 4 * V) := by
    have h := hrec
    rw [hkey1, hcc0] at h
    linear_combination h
  have hWaa : W0 * (aa (p - 2) : ℤ) = -((p : ℤ) ^ 3 * V) := by
    apply mul_left_cancel₀ hp_ne
    linear_combination hcomb
  have hdvd3 : (p : ℤ) ^ 3 ∣ W0 * (aa (p - 2) : ℤ) := ⟨-V, by rw [hWaa]; ring⟩
  exact (hcop.pow_left).dvd_of_dvd_mul_left hdvd3
/- ===== From Induct.lean ===== -/

/-!
# Induct : the MAIN theorem `main_range`.
-/

open Finset

/-- A positive integer smaller than a prime `p` is not divisible by `p`. -/
lemma ndvd_of_pos_lt (p : ℕ) (c : ℤ) (h0 : 0 < c) (hc : c < (p : ℤ)) :
    ¬ (p : ℤ) ∣ c := by
  intro h
  have := Int.le_of_dvd h0 h
  omega

/-- A linear factor `α*(p-m)+β` is not divisible by `p` when the reduced value
`α*m-β` lies strictly between `0` and `p`. -/
lemma lin_ndvd (p : ℕ) (m : ℕ) (α β : ℤ)
    (hc0 : 0 < α * (m : ℤ) - β) (hcp : α * (m : ℤ) - β < (p : ℤ)) :
    ¬ (p : ℤ) ∣ (α * ((p : ℤ) - (m : ℤ)) + β) := by
  intro h
  have hpp : (p : ℤ) ∣ α * (p : ℤ) := dvd_mul_left (p : ℤ) α
  have hc : (p : ℤ) ∣ (α * (m : ℤ) - β) := by
    have e : α * (m : ℤ) - β = α * (p : ℤ) - (α * ((p : ℤ) - (m : ℤ)) + β) := by ring
    rw [e]; exact dvd_sub hpp h
  exact ndvd_of_pos_lt p _ hc0 hcp hc

/-- If `f = p*k - c` with `0 < c < p`, then `p ∤ f`. -/
lemma ndvd_val (p : ℕ) (f c k : ℤ) (hf : f = (p : ℤ) * k - c)
    (h0 : 0 < c) (hlt : c < (p : ℤ)) : ¬ (p : ℤ) ∣ f := by
  intro h
  have hpk : (p : ℤ) ∣ (p : ℤ) * k := dvd_mul_right _ _
  have : (p : ℤ) ∣ c := by
    have e : c = (p : ℤ) * k - f := by rw [hf]; ring
    rw [e]; exact dvd_sub hpk h
  exact ndvd_of_pos_lt p c h0 hlt this

/-- Coprimality of `p` with `C0factor x`, via reduced residues of its three linear factors. -/
lemma coprime_C0 (p : ℕ) (hp : Nat.Prime p) (hp17 : 17 ≤ p) (x : ℤ)
    (a b c : ℤ)
    (hxa : x + 2 = (p : ℤ) * 1 - a) (hxb : 3*x + 1 = (p : ℤ) * 3 - b)
    (hxc : 3*x + 2 = (p : ℤ) * 3 - c)
    (ha0 : 0 < a) (ha : a < (p : ℤ)) (hb0 : 0 < b) (hb : b < (p : ℤ))
    (hc0 : 0 < c) (hc : c < (p : ℤ)) :
    IsCoprime (p : ℤ) (C0factor x) := by
  have hz : Prime (p : ℤ) := (Nat.prime_iff_prime_int).mp hp
  have h27 : ¬ (p : ℤ) ∣ (-27 : ℤ) := by
    intro h
    have h27' : (p : ℤ) ∣ (27 : ℤ) := (dvd_neg).mp h
    have : p ∣ (27 : ℕ) := by exact_mod_cast h27'
    rw [show (27 : ℕ) = 3^3 by norm_num] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow this)
    omega
  have hfa : ¬ (p : ℤ) ∣ (x + 2) := ndvd_val p (x+2) a 1 hxa ha0 ha
  have hfb : ¬ (p : ℤ) ∣ (3*x + 1) := ndvd_val p (3*x+1) b 3 hxb hb0 hb
  have hfc : ¬ (p : ℤ) ∣ (3*x + 2) := ndvd_val p (3*x+2) c 3 hxc hc0 hc
  unfold C0factor
  exact ((((hz.coprime_iff_not_dvd.mpr h27).mul_right
    (hz.coprime_iff_not_dvd.mpr hfa)).mul_right
    (hz.coprime_iff_not_dvd.mpr hfb).pow_right).mul_right
    (hz.coprime_iff_not_dvd.mpr hfc).pow_right)

/-- The "isolated" lemma: no two consecutive `Sc`-roots occur in the range. -/
lemma isolated (p : ℕ) (hp : Nat.Prime p) (hp17 : 17 ≤ p) (x : ℤ)
    (hlo : ((2 * p + 3) / 3 : ℕ) ≤ x) (hhi : x ≤ (p : ℤ) - 1)
    (h1 : (p : ℤ) ∣ Sc x) (h2 : (p : ℤ) ∣ Sc (x + 1)) : False := by
  -- Constant Bezout identity  A*Sc(x) + B*Sc(x+1) = R.
  have hR : (p : ℤ) ∣ (686722798248729801455554265088 : ℤ) := by
    have e :
        (3151661073637754752513081344*x^3 + 16933492438840199379513507840*x^2
            + 30574823013813535993588875264*x + 18616147687372219694368948224) * Sc x
          + (-3151661073637754752513081344*x^3 - 4326848144289180369461182464*x^2
            - 2236616678924672881948360704*x - 354265157331218963846135808) * Sc (x + 1)
          = 686722798248729801455554265088 := by
      unfold Sc; ring
    have hd := dvd_add
      (h1.mul_left (3151661073637754752513081344*x^3 + 16933492438840199379513507840*x^2
            + 30574823013813535993588875264*x + 18616147687372219694368948224))
      (h2.mul_left (-3151661073637754752513081344*x^3 - 4326848144289180369461182464*x^2
            - 2236616678924672881948360704*x - 354265157331218963846135808))
    rwa [e] at hd
  -- Move to ℕ.
  have hRn : p ∣ (686722798248729801455554265088 : ℕ) := by exact_mod_cast hR
  -- Factor  R = (2^23*3^15*13^3) * (37139 * 69921781).
  rw [show (686722798248729801455554265088 : ℕ)
        = (2^23 * 3^15 * 13^3) * (37139 * 69921781) by norm_num] at hRn
  rcases (hp.dvd_mul).mp hRn with hbad | hgood
  · -- p divides 2^23*3^15*13^3 : impossible for p ≥ 17.
    rcases (hp.dvd_mul).mp hbad with h23 | h13
    · rcases (hp.dvd_mul).mp h23 with h2' | h3'
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2'); omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3'); omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h13); omega
  · -- p divides 37139 * 69921781.
    rcases (hp.dvd_mul).mp hgood with ha | hb
    · -- p = 37139
      have hp37 : p = 37139 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp ha
      subst hp37
      push_cast at h1 h2 hhi
      have hxlo : (24760 : ℤ) ≤ x := by
        have := hlo; rw [show (2 * 37139 + 3) / 3 = 24760 from by norm_num] at this
        exact_mod_cast this
      have elin :
          (10575*x^2 + 10325*x + 25989) * Sc x + (26564*x^2 + 31975*x + 13110) * Sc (x + 1)
            = (x - 10012) + 37139 * (5616*x^6 + 36504*x^5 + 108387*x^4 + 172547*x^3
                + 151879*x^2 + 70754*x + 14138) := by
        unfold Sc; ring
      have hdvdL : (37139 : ℤ) ∣ (x - 10012) := by
        have hd := dvd_add (h1.mul_left (10575*x^2 + 10325*x + 25989))
          (h2.mul_left (26564*x^2 + 31975*x + 13110))
        rw [elin] at hd
        have hq : (37139 : ℤ) ∣ 37139 * (5616*x^6 + 36504*x^5 + 108387*x^4 + 172547*x^3
                + 151879*x^2 + 70754*x + 14138) := dvd_mul_right _ _
        simpa using (dvd_sub hd hq)
      exact ndvd_of_pos_lt 37139 (x - 10012) (by omega) (by push_cast; omega)
        (by exact_mod_cast hdvdL)
    · -- p = 69921781
      have hp69 : p = 69921781 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hb
      subst hp69
      push_cast at h1 h2 hhi
      have hxlo : (46614521 : ℤ) ≤ x := by
        have := hlo; rw [show (2 * 69921781 + 3) / 3 = 46614521 from by norm_num] at this
        exact_mod_cast this
      have elin :
          (18797412*x^2 + 7258934*x + 25573182) * Sc x
            + (51124369*x^2 + 67930714*x + 48182028) * Sc (x + 1)
            = (x - 5743856) + 69921781 * (5616*x^6 + 36504*x^5 + 111195*x^4 + 189125*x^3
                + 187654*x^2 + 105277*x + 26828) := by
        unfold Sc; ring
      have hdvdL : (69921781 : ℤ) ∣ (x - 5743856) := by
        have hd := dvd_add (h1.mul_left (18797412*x^2 + 7258934*x + 25573182))
          (h2.mul_left (51124369*x^2 + 67930714*x + 48182028))
        rw [elin] at hd
        have hq : (69921781 : ℤ) ∣ 69921781 * (5616*x^6 + 36504*x^5 + 111195*x^4 + 189125*x^3
                + 187654*x^2 + 105277*x + 26828) := dvd_mul_right _ _
        simpa using (dvd_sub hd hq)
      exact ndvd_of_pos_lt 69921781 (x - 5743856) (by omega) (by push_cast; omega)
        (by exact_mod_cast hdvdL)

/-- MAIN theorem. -/
theorem main_range (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ∀ n : ℕ, (2*p+3)/3 ≤ n → n ≤ p - 1 → (p^3 : ℕ) ∣ aa n := by
  by_cases hp17 : 17 ≤ p
  · -- Big prime: strong induction on m = p - n.
    have H : ∀ m : ℕ, 1 ≤ m → (2*p+3)/3 ≤ p - m → (p : ℤ)^3 ∣ (aa (p - m) : ℤ) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IH =>
        intro hm1 hmn0
        have hmp : m ≤ p := by omega
        have h3m : 3 * m < p := by omega
        rcases Nat.lt_or_ge m 3 with hlt3 | hge3
        · -- m = 1 or m = 2
          interval_cases m
          · -- m = 1
            have hb := base1 p hp (by omega)
            exact_mod_cast hb
          · -- m = 2
            exact base2 p hp hp17
        · -- m ≥ 3
          set x : ℤ := (p : ℤ) - (m : ℤ) with hxdef
          have hxm : ((p - m : ℕ) : ℤ) = x := by rw [hxdef, Nat.cast_sub hmp]
          have hi1 : p - m + 1 = p - (m - 1) := by omega
          have hi2 : p - m + 2 = p - (m - 2) := by omega
          have IH1 : (p : ℤ)^3 ∣ (aa (p - m + 1) : ℤ) := by
            rw [hi1]; exact IH (m - 1) (by omega) (by omega) (by omega)
          have IH2 : (p : ℤ)^3 ∣ (aa (p - m + 2) : ℤ) := by
            rw [hi2]; exact IH (m - 2) (by omega) (by omega) (by omega)
          have E1 := aa_rec (p - m)
          rw [hxm] at E1
          by_cases hSc : (p : ℤ) ∣ Sc (x + 1)
          · -- EXCEPTIONAL
            have hm4 : 4 ≤ m := by
              by_contra hcon
              have hm3 : m = 3 := by omega
              have hx1val : x + 1 = (p : ℤ) - 2 := by rw [hxdef, hm3]; push_cast; ring
              have hSc' := hSc
              rw [hx1val] at hSc'
              have hd19 : (p : ℤ) ∣ (19600 : ℤ) := by
                have e : (19600 : ℤ) = Sc ((p : ℤ) - 2)
                    - (p : ℤ) * (5616*(p:ℤ)^3 - 30888*(p:ℤ)^2 + 63459*(p:ℤ) - 57709) := by
                  unfold Sc; ring
                rw [e]; exact dvd_sub hSc' (dvd_mul_right _ _)
              have hd19n : p ∣ (19600 : ℕ) := by exact_mod_cast hd19
              rw [show (19600 : ℕ) = 2^4 * 5^2 * 7^2 by norm_num] at hd19n
              rcases (hp.dvd_mul).mp hd19n with h' | h7
              · rcases (hp.dvd_mul).mp h' with h2 | h5
                · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
                  omega
                · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h5)
                  omega
              · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h7)
                omega
            have hi3 : p - m + 3 = p - (m - 3) := by omega
            have IH3 : (p : ℤ)^3 ∣ (aa (p - m + 3) : ℤ) := by
              rw [hi3]; exact IH (m - 3) (by omega) (by omega) (by omega)
            have E2 := aa_rec (p - m + 1)
            have hxm1 : ((p - m + 1 : ℕ) : ℤ) = x + 1 := by
              rw [Nat.cast_add, Nat.cast_one, hxm]
            rw [hxm1, show (p - m + 1) + 2 = p - m + 3 by omega,
              show (p - m + 1) + 1 = p - m + 2 by omega] at E2
            have hdet := det_div_S (x + 1)
            rw [show (x + 1) - 1 = x by ring] at hdet
            obtain ⟨qd, hqd⟩ := hdet
            rw [cc0_eq x] at E1
            rw [cc2_eq (x + 1)] at E2
            have hxge : (12 : ℤ) ≤ x := by
              rw [← hxm]; exact_mod_cast (show 12 ≤ p - m by omega)
            have hspos : (0 : ℤ) < Sc (x + 1) := by
              have ht : (0 : ℤ) < x + 1 := by omega
              unfold Sc; nlinarith [pow_pos ht 4, pow_pos ht 3, pow_pos ht 2, ht]
            have hsne : Sc (x + 1) ≠ 0 := ne_of_gt hspos
            have hS0 : Sc (x + 1) * (C0factor x * cc0 (x + 1) * (aa (p - m) : ℤ)
                - (cc1 x * C2factor (x + 1) * (aa (p - m + 3) : ℤ)
                    + (aa (p - m + 2) : ℤ) * qd)) = 0 := by
              linear_combination cc0 (x + 1) * E1 - cc1 x * E2 + (aa (p - m + 2) : ℤ) * hqd
            have hEq : C0factor x * cc0 (x + 1) * (aa (p - m) : ℤ)
                = cc1 x * C2factor (x + 1) * (aa (p - m + 3) : ℤ)
                    + (aa (p - m + 2) : ℤ) * qd :=
              sub_eq_zero.mp ((mul_eq_zero.mp hS0).resolve_left hsne)
            have hRHSdiv : (p : ℤ)^3 ∣ (cc1 x * C2factor (x + 1) * (aa (p - m + 3) : ℤ)
                + (aa (p - m + 2) : ℤ) * qd) :=
              dvd_add (IH3.mul_left _) (IH2.mul_right _)
            have hprod : (p : ℤ)^3 ∣ C0factor x * cc0 (x + 1) * (aa (p - m) : ℤ) := by
              rw [hEq]; exact hRHSdiv
            have hcopC0 : IsCoprime (p : ℤ) (C0factor x) :=
              coprime_C0 p hp hp17 x ((m:ℤ) - 2) (3*(m:ℤ) - 1) (3*(m:ℤ) - 2)
                (by rw [hxdef]; ring) (by rw [hxdef]; ring)
                (by rw [hxdef]; ring) (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega)
            have hcopC0' : IsCoprime (p : ℤ) (C0factor (x + 1)) :=
              coprime_C0 p hp hp17 (x + 1) ((m:ℤ) - 3) (3*(m:ℤ) - 4) (3*(m:ℤ) - 5)
                (by rw [hxdef]; ring) (by rw [hxdef]; ring)
                (by rw [hxdef]; ring) (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega)
            have hlo2 : ((2*p+3)/3 : ℕ) ≤ (x + 1) := by rw [← hxm]; omega
            have hhi2 : (x + 1) ≤ (p : ℤ) - 1 := by rw [← hxm]; omega
            have hncSc2 : ¬ (p : ℤ) ∣ Sc (x + 2) := by
              intro hd
              exact isolated p hp hp17 (x + 1) hlo2 hhi2 hSc
                (by rw [show (x + 1) + 1 = x + 2 by ring]; exact hd)
            have hcopSc2 : IsCoprime (p : ℤ) (Sc (x + 2)) :=
              (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hncSc2
            have hcopu0 : IsCoprime (p : ℤ) (cc0 (x + 1)) := by
              rw [cc0_eq (x + 1), show (x + 1) + 1 = x + 2 by ring]
              exact hcopC0'.mul_right hcopSc2
            have hcopfull : IsCoprime (p : ℤ) (C0factor x * cc0 (x + 1)) :=
              hcopC0.mul_right hcopu0
            exact (hcopfull.pow_left).dvd_of_dvd_mul_left hprod
          · -- GENERIC
            have hcopC0 : IsCoprime (p : ℤ) (C0factor x) :=
              coprime_C0 p hp hp17 x ((m:ℤ) - 2) (3*(m:ℤ) - 1) (3*(m:ℤ) - 2)
                (by rw [hxdef]; ring) (by rw [hxdef]; ring)
                (by rw [hxdef]; ring) (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega)
            have hcopSc : IsCoprime (p : ℤ) (Sc (x + 1)) :=
              (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hSc
            have hcop0 : IsCoprime (p : ℤ) (cc0 x) := by
              rw [cc0_eq x]; exact hcopC0.mul_right hcopSc
            have hRHS : (p : ℤ)^3 ∣ (cc2 x * (aa (p - m + 2) : ℤ)
                + cc1 x * (aa (p - m + 1) : ℤ)) :=
              dvd_add (IH2.mul_left _) (IH1.mul_left _)
            have hprod : (p : ℤ)^3 ∣ cc0 x * (aa (p - m) : ℤ) := by
              have e : cc0 x * (aa (p - m) : ℤ)
                  = -(cc2 x * (aa (p - m + 2) : ℤ) + cc1 x * (aa (p - m + 1) : ℤ)) := by
                linear_combination E1
              rw [e]; exact (dvd_neg).mpr hRHS
            exact (hcop0.pow_left).dvd_of_dvd_mul_left hprod
    -- Assemble main statement from H.
    intro n hlo hhi
    have hkey := H (p - n) (by omega) (by rw [show p - (p - n) = n by omega]; exact hlo)
    rw [show p - (p - n) = n by omega] at hkey
    exact_mod_cast hkey
  · -- Small primes p ∈ {5,7,11,13}.
    interval_cases p <;>
      first
        | (exact absurd hp (by decide))
        | (intro n hlo hhi; interval_cases n <;> decide)


/- ===== Original conjecture statement (unchanged) + final proof ===== -/

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  have hbridge : ∀ n, a n = aa n := fun n => rfl
  intro n h1 h2
  rw [hbridge]
  exact main_range p hp hp5 n h1 h2
