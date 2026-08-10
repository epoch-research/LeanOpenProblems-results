import FormalConjectures.Util.ProblemImports

open Matrix Finset BigOperators Complex

namespace CharM

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Number of units. -/
abbrev N (p : ℕ) [Fact p.Prime] : ℕ := Nat.card (ZMod p)ˣ

/-- The cyclic isomorphism. -/
def ee (p : ℕ) [Fact p.Prime] : Multiplicative (ZMod (N p)) ≃* (ZMod p)ˣ :=
  zmodCyclicMulEquiv (inferInstance : IsCyclic (ZMod p)ˣ)

/-- The power map `ZMod N → units`. -/
def pw (p : ℕ) [Fact p.Prime] (a : ZMod (N p)) : (ZMod p)ˣ := ee p (Multiplicative.ofAdd a)

/-- Discrete log: function from units to `ZMod N`. -/
def dl (u : (ZMod p)ˣ) : ZMod (N p) := Multiplicative.toAdd ((ee p).symm u)

theorem pw_dl (u : (ZMod p)ˣ) : pw p (dl u) = u := by
  simp only [pw, dl, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem dl_pw (a : ZMod (N p)) : dl (pw p a) = a := by
  simp only [pw, dl, MulEquiv.symm_apply_apply, toAdd_ofAdd]

theorem pw_add (a b : ZMod (N p)) : pw p (a + b) = pw p a * pw p b := by
  simp only [pw, ofAdd_add, map_mul]

theorem pw_zero : pw p (0 : ZMod (N p)) = 1 := by
  simp only [pw, ofAdd_zero, map_one]

theorem dl_mul (u v : (ZMod p)ˣ) : dl (u * v) = dl u + dl v := by
  simp only [dl, map_mul, toAdd_mul]

theorem card_N : N p = p - 1 := by
  rw [N, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

theorem N_pos : 0 < N p := by
  rw [card_N]; have := (Fact.out : p.Prime).two_le; omega

instance : NeZero (N p) := ⟨by have := @N_pos p _; omega⟩

/-- `pw a = gen ^ a.val`. -/
theorem pw_eq_gen_pow (a : ZMod (N p)) : pw p a = (pw p 1) ^ (a.val) := by
  have h1 : (pw p 1) ^ (a.val) = pw p ((a.val : ℕ) • (1 : ZMod (N p))) := by
    rw [pw, pw, ← map_pow, ← ofAdd_nsmul]
  rw [h1]
  congr 2
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id]

theorem N_even (hodd : p % 2 = 1) : N p = 2 * (N p / 2) := by
  rw [card_N]
  have hp := (Fact.out : p.Prime).two_le
  omega

/-- The exponential map `ZMod N → ℂ`. -/
def ze (ζ : ℂ) (a : ZMod (N p)) : ℂ := ζ ^ a.val

theorem ze_add (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (a b : ZMod (N p)) :
    ze (p := p) ζ (a + b) = ze (p := p) ζ a * ze (p := p) ζ b := by
  rw [ze, ze, ze, ← pow_add]
  have hv : a.val + b.val = N p * ((a.val + b.val) / N p) + (a + b).val := by
    rw [ZMod.val_add]; exact (Nat.div_add_mod _ _).symm
  rw [hv, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

theorem ze_zero (ζ : ℂ) : ze (p := p) ζ (0 : ZMod (N p)) = 1 := by
  rw [ze, ZMod.val_zero, pow_zero]

theorem ze_natCast (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (k : ℕ) :
    ze (p := p) ζ (k : ZMod (N p)) = ζ ^ k := by
  rw [ze, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod k (N p)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- The quadratic character of `ZMod p` (integer valued). -/
abbrev qc (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℤ := quadraticChar (ZMod p)

theorem gen_not_square (hodd : p % 2 = 1) :
    ¬ IsSquare ((pw p 1 : (ZMod p)ˣ) : ZMod p) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact (Units.ne_zero _) hr
  set u := (isUnit_iff_ne_zero.mpr hr0).unit with hu
  have hus : (u : ZMod p) = r := IsUnit.unit_spec _
  have hpw1 : pw p 1 = u * u := by
    apply Units.ext
    rw [Units.val_mul, hus, hr]
  have hdl : (1 : ZMod (N p)) = dl u + dl u := by
    rw [← dl_mul, ← hpw1, dl_pw]
  have h2 : (2 : ℕ) ∣ N p := ⟨N p / 2, N_even hodd⟩
  have key : (1 : ZMod 2)
      = (ZMod.castHom h2 (ZMod 2)) (dl u) + (ZMod.castHom h2 (ZMod 2)) (dl u) := by
    rw [← map_add, ← hdl, map_one]
  revert key
  generalize (ZMod.castHom h2 (ZMod 2)) (dl u) = y
  revert y
  decide

theorem qc_gen (hodd : p % 2 = 1) : qc p ((pw p 1 : (ZMod p)ˣ) : ZMod p) = -1 :=
  (quadraticChar_neg_one_iff_not_isSquare).2 (gen_not_square hodd)

theorem qc_pw (hodd : p % 2 = 1) (a : ZMod (N p)) :
    qc p ((pw p a : (ZMod p)ˣ) : ZMod p) = (-1) ^ a.val := by
  rw [pw_eq_gen_pow, Units.val_pow_eq_pow_val, map_pow, qc_gen hodd]

theorem sum_zmod_range (M : ℕ) [NeZero M] (f : ℕ → ℂ) :
    ∑ a : ZMod M, f (a.val) = ∑ k ∈ Finset.range M, f k := by
  refine Finset.sum_bij' (fun a _ => a.val) (fun k _ => (k : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro k _; exact Finset.mem_univ _
  · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro k hk; rw [Finset.mem_range] at hk; exact ZMod.val_natCast_of_lt hk
  · intro a _; rfl

theorem ze_mul_pow (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (a d : ZMod (N p)) :
    ze (p := p) ζ (a * d) = (ze (p := p) ζ d) ^ (a.val) := by
  have h1 : a * d = (((a.val * d.val : ℕ)) : ZMod (N p)) := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
  rw [h1, ze_natCast ζ hζ, ze, ← pow_mul, mul_comm]

/-- Orthogonality of the `ze` characters. -/
theorem ze_orthogonality (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (d : ZMod (N p)) :
    ∑ a : ZMod (N p), ze (p := p) ζ (a * d) = if d = 0 then (N p : ℂ) else 0 := by
  have hrw : ∀ a : ZMod (N p), ze (p := p) ζ (a * d) = (ze (p := p) ζ d) ^ (a.val) :=
    fun a => ze_mul_pow ζ hζ a d
  rw [Finset.sum_congr rfl (fun a _ => hrw a), sum_zmod_range (N p) (fun k => (ze (p := p) ζ d) ^ k)]
  by_cases hd : d = 0
  · subst hd
    rw [ze_zero]
    simp
  · rw [if_neg hd]
    have hr1 : ze (p := p) ζ d ≠ 1 := by
      rw [ze]
      intro h
      apply hd
      have hdlt : d.val < N p := ZMod.val_lt d
      have := hζ.pow_eq_one_iff_dvd d.val
      rw [h] at this
      have hdvd : (N p) ∣ d.val := this.1 rfl
      exact (ZMod.val_eq_zero d).1 (Nat.eq_zero_of_dvd_of_lt hdvd hdlt)
    have hrN : (ze (p := p) ζ d) ^ (N p) = 1 := by
      rw [ze, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hr1 (N p), hrN, sub_self, zero_div]

/-- The value `h(g^s) = χ(1 - g^s)` as a complex number. -/
def hf (ζ : ℂ) (s : ZMod (N p)) : ℂ :=
  ((qc p (1 - ((pw p s : (ZMod p)ˣ) : ZMod p)) : ℤ) : ℂ)

/-- Fourier coefficient. -/
def hhat (ζ : ℂ) (a : ZMod (N p)) : ℂ :=
  (N p : ℂ)⁻¹ * ∑ s : ZMod (N p), hf (p := p) ζ s * ze (p := p) ζ (-(a * s))

theorem fourier_inv (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (s : ZMod (N p)) :
    hf (p := p) ζ s = ∑ a : ZMod (N p), hhat (p := p) ζ a * ze (p := p) ζ (a * s) := by
  have hN : (N p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := @N_pos p _; omega)
  have step1 : ∀ a : ZMod (N p), hhat (p := p) ζ a * ze (p := p) ζ (a * s)
      = (N p : ℂ)⁻¹ * ∑ t : ZMod (N p),
          hf (p := p) ζ t * ze (p := p) ζ (a * (s - t)) := by
    intro a
    rw [hhat, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, ← ze_add ζ hζ]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun a _ => step1 a), ← Finset.mul_sum, Finset.sum_comm]
  have step2 : (∑ t : ZMod (N p), ∑ a : ZMod (N p),
        hf (p := p) ζ t * ze (p := p) ζ (a * (s - t)))
      = ∑ t : ZMod (N p), hf (p := p) ζ t * (if s - t = 0 then (N p : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.mul_sum, ze_orthogonality ζ hζ (s - t)]
  rw [step2]
  have step3 : (∑ t : ZMod (N p), hf (p := p) ζ t * (if s - t = 0 then (N p : ℂ) else 0))
      = hf (p := p) ζ s * (N p : ℂ) := by
    rw [Finset.sum_eq_single s]
    · rw [sub_self, if_pos rfl]
    · intro t _ hts
      rw [if_neg (by rw [sub_eq_zero]; exact fun h => hts h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [step3, mul_comm (hf (p := p) ζ s) (N p : ℂ), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

instance instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The "half" element of `ZMod N`. -/
def half (p : ℕ) [Fact p.Prime] : ZMod (N p) := ((N p / 2 : ℕ) : ZMod (N p))

theorem ze_half_eq (hodd : p % 2 = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) :
    ze (p := p) ζ (half p) = -1 := by
  have hNlt : N p / 2 < N p := by have := @N_pos p _; omega
  rw [ze, half, ZMod.val_natCast_of_lt hNlt]
  -- ζ^(N/2) = -1
  have h2 : (ζ ^ (N p / 2)) * (ζ ^ (N p / 2)) = 1 := by
    rw [← pow_add, ← Nat.two_mul, ← N_even hodd, hζ.pow_eq_one]
  have hN2 : 2 ≤ N p := by
    rw [card_N]; have := (Fact.out : p.Prime).two_le; omega
  rcases mul_self_eq_one_iff.1 h2 with h | h
  · exfalso
    rw [hζ.pow_eq_one_iff_dvd] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  · exact h

theorem ze_half_mul (hodd : p % 2 = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (s : ZMod (N p)) :
    ze (p := p) ζ (half p * s) = (-1) ^ s.val := by
  rw [mul_comm, ze_mul_pow ζ hζ, ze_half_eq hodd ζ hζ]

theorem qc_neg_one (h4 : p % 4 = 3) : qc p (-1) = -1 := by
  have hrc : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  rw [qc, quadraticChar_neg_one hrc, ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four h4

theorem pw_neg (s : ZMod (N p)) : pw p (-s) = (pw p s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pw_add, neg_add_cancel, pw_zero]

/-- Key reflection identity for `hf`. -/
theorem hf_neg (h4 : p % 4 = 3) (ζ : ℂ) (s : ZMod (N p)) :
    hf (p := p) ζ (-s) * ((-1 : ℂ) ^ s.val) = - hf (p := p) ζ s := by
  have hodd : p % 2 = 1 := by omega
  set u : ZMod p := ((pw p s : (ZMod p)ˣ) : ZMod p) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hpwneg : ((pw p (-s) : (ZMod p)ˣ) : ZMod p) = u⁻¹ := by
    rw [pw_neg, hu]; exact Units.val_inv_eq_inv_val _
  -- hf ζ (-s) = qc (1 - u⁻¹)
  have hqcsq : (qc p u) ^ 2 = 1 := quadraticChar_sq_one hu0
  -- 1 - u⁻¹ = u⁻¹ * ((-1) * (1 - u))
  have hfac : (1 : ZMod p) - u⁻¹ = u⁻¹ * ((-1) * (1 - u)) := by
    field_simp
    ring
  have hsval : hf (p := p) ζ s = ((qc p (1 - u) : ℤ) : ℂ) := by
    rw [hf]
  have hnegval : hf (p := p) ζ (-s) = ((qc p (1 - u⁻¹) : ℤ) : ℂ) := by
    rw [hf, hpwneg]
  -- qc u⁻¹ = qc u
  have hqcu_inv : qc p u⁻¹ = qc p u := by
    have hmul : qc p u * qc p u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have hsq : qc p u * qc p u = 1 := by rw [← sq]; exact hqcsq
    have hne : qc p u ≠ 0 := by
      intro h; rw [h] at hsq; simp at hsq
    have heq := hsq.trans hmul.symm
    exact (mul_left_cancel₀ hne heq).symm
  have hqcu_val : qc p u = (-1) ^ s.val := by rw [hu]; exact qc_pw hodd s
  have hqcexpand : qc p (1 - u⁻¹) = (-1) ^ s.val * (-1) * qc p (1 - u) := by
    rw [hfac, map_mul, map_mul, hqcu_inv, hqcu_val, qc_neg_one h4]; ring
  rw [hnegval, hsval, hqcexpand]
  push_cast
  have hsq2 : (-1 : ℂ) ^ s.val * (-1 : ℂ) ^ s.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-(((qc p) (1 - u) : ℤ) : ℂ)) * hsq2

/-- Reflection symmetry of the Fourier coefficients. -/
theorem hhat_symm (h4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (a : ZMod (N p)) :
    hhat (p := p) ζ (half p - a) = - hhat (p := p) ζ a := by
  have hodd : p % 2 = 1 := by omega
  rw [hhat, hhat, ← mul_neg]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (ZMod (N p)))
        (fun s => hf (p := p) ζ s * ze (p := p) ζ (-((half p - a) * s))),
      ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Equiv.neg_apply]
  have e1 : -((half p - a) * -s) = (half p) * s + (-(a * s)) := by ring
  rw [e1, ze_add ζ hζ, ze_half_mul hodd ζ hζ, ← mul_assoc, hf_neg h4 ζ s]
  ring

end

end CharM
