import FormalConjectures.Util.ProblemImports
import Submission.Zeta341
import Submission.ZeroFree

/-!
Bound on `-ζ'/ζ` for `σ ≥ 1 + 1 / log(|t|+2)`, via discrete Abel summation.
-/

open Complex Real Set
open ArithmeticFunction hiding log
open Chebyshev

noncomputable section

lemma psi_nat (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ Finset.Icc 1 n, vonMangoldt k := by
  rw [psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun _ _ => rfl)).symm
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hk
    have : k = 0 := by omega
    simp [this, vonMangoldt_zero']

lemma vonMangoldt_eq_psi_sub {n : ℕ} (hn : 1 ≤ n) :
    vonMangoldt n = ψ (n : ℝ) - ψ ((n - 1 : ℕ) : ℝ) := by
  rw [psi_nat n, psi_nat (n - 1)]
  have hins : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    constructor
    · intro ⟨h1, hkn⟩
      rcases eq_or_lt_of_le hkn with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, Nat.le_sub_one_of_lt hlt⟩
    · intro h
      rcases h with rfl | ⟨h1, hk⟩
      · exact ⟨hn, le_rfl⟩
      · exact ⟨h1, hk.trans (Nat.sub_le n 1)⟩
  have hnin : n ∉ Finset.Icc 1 (n - 1) := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro; exact Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 1) hn) (by decide)
  rw [hins, Finset.sum_insert hnin]
  ring

lemma psi_zero : ψ (0 : ℝ) = 0 :=
  psi_eq_zero_of_lt_two (by norm_num)

lemma log4_add_four_pos : 0 < Real.log 4 + 4 :=
  add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (by norm_num)

lemma psi_le_C_mul (x : ℝ) (hx : 0 ≤ x) : ψ x ≤ (Real.log 4 + 4) * x :=
  psi_le_const_mul_self hx

/-- Discrete Abel: `∑_{n=a+1}^b Λ(n) f(n)`. -/
lemma abel_vonMangoldt {a b : ℕ} (hab : a < b) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc (a + 1) b, vonMangoldt n * f n =
      ψ (b : ℝ) * f b - ψ (a : ℝ) * f (a + 1) +
        ∑ n ∈ Finset.Icc (a + 1) (b - 1), ψ (n : ℝ) * (f n - f (n + 1)) := by
  have hterm : ∀ n ∈ Finset.Icc (a + 1) b,
      vonMangoldt n * f n = (ψ (n : ℝ) - ψ ((n - 1 : ℕ) : ℝ)) * f n := by
    intro n hn
    have : 1 ≤ n := by simp only [Finset.mem_Icc] at hn; omega
    rw [vonMangoldt_eq_psi_sub this]
  rw [Finset.sum_congr rfl hterm]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hshift :
      ∑ n ∈ Finset.Icc (a + 1) b, ψ ((n - 1 : ℕ) : ℝ) * f n =
        ∑ m ∈ Finset.Icc a (b - 1), ψ (m : ℝ) * f (m + 1) := by
    refine Finset.sum_nbij' (fun n => n - 1) (fun m => m + 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      have : a ≤ n - 1 ∧ n - 1 ≤ b - 1 := by omega
      exact this
    · intro m hm
      rw [Finset.mem_Icc] at hm ⊢
      have : a + 1 ≤ m + 1 ∧ m + 1 ≤ b := by omega
      exact this
    · intro n hn
      rw [Finset.mem_Icc] at hn
      have : n - 1 + 1 = n := by omega
      exact this
    · intro m hm
      rw [Finset.mem_Icc] at hm
      have : m + 1 - 1 = m := by omega
      exact this
    · intro n hn
      rw [Finset.mem_Icc] at hn
      have : n - 1 + 1 = n := by omega
      simp [this]
  rw [hshift]
  have hsplitA : Finset.Icc a (b - 1) = insert a (Finset.Icc (a + 1) (b - 1)) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hanotin : a ∉ Finset.Icc (a + 1) (b - 1) := by
    simp only [Finset.mem_Icc, not_and, not_le]; intro; omega
  rw [hsplitA, Finset.sum_insert hanotin]
  have hsplitB : Finset.Icc (a + 1) b = insert b (Finset.Icc (a + 1) (b - 1)) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hbnotin : b ∉ Finset.Icc (a + 1) (b - 1) := by
    simp only [Finset.mem_Icc, not_and, not_le]; intro; omega
  rw [hsplitB, Finset.sum_insert hbnotin]
  calc
    ψ (b : ℝ) * f b + ∑ n ∈ Finset.Icc (a + 1) (b - 1), ψ (n : ℝ) * f n -
        (ψ (a : ℝ) * f (a + 1) + ∑ n ∈ Finset.Icc (a + 1) (b - 1), ψ (n : ℝ) * f (n + 1))
        = ψ (b : ℝ) * f b - ψ (a : ℝ) * f (a + 1) +
            (∑ n ∈ Finset.Icc (a + 1) (b - 1), ψ (n : ℝ) * f n -
              ∑ n ∈ Finset.Icc (a + 1) (b - 1), ψ (n : ℝ) * f (n + 1)) := by ring
    _ = ψ (b : ℝ) * f b - ψ (a : ℝ) * f (a + 1) +
          ∑ n ∈ Finset.Icc (a + 1) (b - 1), (ψ (n : ℝ) * f n - ψ (n : ℝ) * f (n + 1)) := by
        rw [Finset.sum_sub_distrib]
    _ = ψ (b : ℝ) * f b - ψ (a : ℝ) * f (a + 1) +
          ∑ n ∈ Finset.Icc (a + 1) (b - 1), ψ (n : ℝ) * (f n - f (n + 1)) := by
        refine congrArg _ (Finset.sum_congr rfl fun n hn => ?_); ring

lemma nat_inv_sub_succ (n : ℕ) (hn : 0 < n) :
    (n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹ = ((n : ℝ) * (n + 1))⁻¹ := by
  have h0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field

lemma n_mul_inv_sub (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹) = (n + 1 : ℝ)⁻¹ := by
  rw [nat_inv_sub_succ n hn]
  have h0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field

lemma sum_inv_Icc_two {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹ ≤ Real.log N := by
  have hharm : (harmonic N : ℝ) = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; simp
  have h1 : ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ ≤ 1 + Real.log N := by
    simpa [hharm] using (harmonic_le_one_add_log N)
  by_cases hN1 : N = 1
  · subst hN1; simp
  have hN2 : 2 ≤ N := by omega
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h1notin : 1 ∉ Finset.Icc 2 N := by
    simp only [Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert h1notin] at h1
  simp only [Nat.cast_one, inv_one] at h1
  linarith

/-- `∑_{n=1}^N Λ(n)/n ≤ (log 4 + 4) (1 + log N)` for `N ≥ 1`. -/
lemma sum_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n ≤
      (Real.log 4 + 4) * (1 + Real.log N) := by
  have hC := log4_add_four_pos.le
  by_cases hN1 : N = 1
  · subst hN1
    simp only [vonMangoldt_apply_one, Finset.sum_singleton, Finset.Icc_self,
      Nat.cast_one, div_one]
    have : (0 : ℝ) ≤ 1 + Real.log 1 := by rw [Real.log_one]; norm_num
    exact mul_nonneg hC this
  have hNlt : (0 : ℕ) < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hN
  have habel := abel_vonMangoldt (a := 0) (b := N) hNlt (fun n => (n : ℝ)⁻¹)
  have hI : Finset.Icc (0 + 1) N = Finset.Icc 1 N := rfl
  rw [hI] at habel
  simp only [Nat.cast_zero, zero_add, psi_zero, zero_mul, sub_zero] at habel
  have hcast : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := fun n => by
    simp [Nat.cast_add, Nat.cast_one]
  simp only [hcast] at habel
  have hfeq : ∑ n ∈ Finset.Icc 1 N, vonMangoldt n * (n : ℝ)⁻¹ =
      ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n :=
    Finset.sum_congr rfl fun n hn => (div_eq_mul_inv _ _).symm
  rw [← hfeq, habel]
  have hpsiN : ψ (N : ℝ) ≤ (Real.log 4 + 4) * N :=
    psi_le_C_mul _ (Nat.cast_nonneg _)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hterm1 : ψ (N : ℝ) * (N : ℝ)⁻¹ ≤ Real.log 4 + 4 := by
    rw [mul_inv_le_iff₀ hNpos]
    simpa [mul_comm] using hpsiN
  have hmid : ∑ n ∈ Finset.Icc 1 (N - 1),
        ψ (n : ℝ) * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹) ≤
      (Real.log 4 + 4) * Real.log N := by
    have hbound : ∀ n ∈ Finset.Icc 1 (N - 1),
        ψ (n : ℝ) * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹) ≤
          (Real.log 4 + 4) * ((n + 1 : ℝ)⁻¹) := by
      intro n hn
      have hn1 : 1 ≤ n := by simp only [Finset.mem_Icc] at hn; exact hn.1
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hpsi : ψ (n : ℝ) ≤ (Real.log 4 + 4) * n :=
        psi_le_C_mul _ (Nat.cast_nonneg _)
      have hdiff0 : 0 ≤ (n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹ :=
        sub_nonneg.mpr (inv_anti₀ hnpos (by linarith : (n : ℝ) ≤ n + 1))
      calc
        ψ (n : ℝ) * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹)
            ≤ ((Real.log 4 + 4) * n) * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hpsi hdiff0
        _ = (Real.log 4 + 4) * (n * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹)) := by ring
        _ = (Real.log 4 + 4) * (n + 1 : ℝ)⁻¹ := by rw [n_mul_inv_sub n hn1]
    have hsum := Finset.sum_le_sum hbound
    have hre :
        ∑ n ∈ Finset.Icc 1 (N - 1), ((n + 1 : ℝ)⁻¹) =
          ∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹ := by
      refine Finset.sum_nbij' (fun n => n + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_Icc] at hn ⊢
        have : 2 ≤ n + 1 ∧ n + 1 ≤ N := by omega
        exact this
      · intro k hk
        rw [Finset.mem_Icc] at hk ⊢
        have : 1 ≤ k - 1 ∧ k - 1 ≤ N - 1 := by omega
        exact this
      · intro n hn
        rw [Finset.mem_Icc] at hn
        have : n + 1 - 1 = n := by omega
        exact this
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have : k - 1 + 1 = k := by omega
        exact this
      · intro; simp
    calc
      ∑ n ∈ Finset.Icc 1 (N - 1), ψ (n : ℝ) * ((n : ℝ)⁻¹ - (n + 1 : ℝ)⁻¹)
          ≤ ∑ n ∈ Finset.Icc 1 (N - 1), (Real.log 4 + 4) * ((n + 1 : ℝ)⁻¹) := hsum
      _ = (Real.log 4 + 4) * ∑ n ∈ Finset.Icc 1 (N - 1), ((n + 1 : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
      _ = (Real.log 4 + 4) * ∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹ := by rw [hre]
      _ ≤ (Real.log 4 + 4) * Real.log N :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_two hN) hC
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (Nat.one_le_cast.mpr hN)
  nlinarith [hterm1, hmid]

/-- Partial sum of the Dirichlet series for `-ζ'/ζ`. -/
lemma abs_sum_vonMangoldt_cpow_le {N : ℕ} (hN : 1 ≤ N) (s : ℂ) (hσ : 1 ≤ s.re) :
    ‖∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)‖ ≤
      (Real.log 4 + 4) * (1 + Real.log N) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖(vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)‖ = vonMangoldt n * (n : ℝ) ^ (-s.re) := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have : 1 ≤ n := by simp only [Finset.mem_Icc] at hn; exact hn.1
      exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_cpow_of_ne_zero hn0]
    simp [neg_re]
  have hle1 : ‖∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)‖ ≤
      ∑ n ∈ Finset.Icc 1 N, vonMangoldt n * (n : ℝ) ^ (-s.re) := by
    refine (norm_sum_le _ _).trans ?_
    exact le_of_eq (Finset.sum_congr rfl fun n hn => hterm n hn)
  have hle2 : ∑ n ∈ Finset.Icc 1 N, vonMangoldt n * (n : ℝ) ^ (-s.re) ≤
      ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := by simp only [Finset.mem_Icc] at hn; exact hn.1
    have hnR : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn1
    have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg hσ)
    have : (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
    rw [this] at hpow
    exact (mul_le_mul_of_nonneg_left hpow vonMangoldt_nonneg).trans_eq
      (div_eq_mul_inv _ _)
  exact hle1.trans (hle2.trans (sum_vonMangoldt_div_le hN))

lemma rpow_sub_succ_le {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ0 : 0 < σ) :
    (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ σ * (n : ℝ) ^ (-σ - 1) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlt : (n : ℝ) < n + 1 := by exact_mod_cast Nat.lt_succ_self n
  have hderiv : ∀ x ∈ Set.Icc (n : ℝ) (n + 1),
      HasDerivAt (fun t : ℝ => t ^ (-σ)) ((-σ) * x ^ (-σ - 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
    exact Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
  obtain ⟨ξ, hξ, hξeq⟩ :=
    exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-σ)) (fun x => (-σ) * x ^ (-σ - 1))
      hlt (fun x hx => (hderiv x (Set.Ioo_subset_Icc_self hx)).differentiableAt)
      (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx))
  -- f(n+1) - f(n) = f'(ξ) * 1, so f(n) - f(n+1) = -f'(ξ) = σ ξ^{-σ-1}
  have hdiff : (n : ℝ) ^ (-σ) - ((n + 1 : ℝ) ^ (-σ)) = σ * ξ ^ (-σ - 1) := by
    have : ((n + 1 : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ)) / ((n + 1 : ℝ) - n) =
        (-σ) * ξ ^ (-σ - 1) := hξeq
    have hden : (n + 1 : ℝ) - n = 1 := by ring
    rw [hden, div_one] at this
    linarith
  have hξn : (n : ℝ) ≤ ξ := hξ.1
  have hpow : ξ ^ (-σ - 1) ≤ (n : ℝ) ^ (-σ - 1) := by
    have hneg : -σ - 1 < 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hn0 hξn hneg.le
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
  rw [hcast, hdiff]
  nlinarith [Real.rpow_nonneg hn0.le (-σ - 1), hσ0.le]

/-- Finite tail of `∑ Λ(n) n^{-σ}`. -/
lemma sum_vonMangoldt_rpow_Icc_tail {a b : ℕ} {σ : ℝ}
    (hab : a < b) (ha : 1 ≤ a) (hσ : 1 < σ) :
    ∑ n ∈ Finset.Icc (a + 1) b, vonMangoldt n * (n : ℝ) ^ (-σ) ≤
      (Real.log 4 + 4) *
        ((b : ℝ) ^ (1 - σ) + (a : ℝ) ^ (1 - σ) +
          σ * ∑ n ∈ Finset.Icc (a + 1) (b - 1), (n : ℝ) ^ (1 - σ - 1)) := by
  have habel := abel_vonMangoldt hab (fun n => (n : ℝ) ^ (-σ))
  rw [habel]
  have hC := log4_add_four_pos.le
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hψb : ψ (b : ℝ) * (b : ℝ) ^ (-σ) ≤ (Real.log 4 + 4) * (b : ℝ) ^ (1 - σ) := by
    have : ψ (b : ℝ) ≤ (Real.log 4 + 4) * b := psi_le_C_mul _ hb0
    have hpow : 0 ≤ (b : ℝ) ^ (-σ) := Real.rpow_nonneg hb0 _
    calc
      ψ (b : ℝ) * (b : ℝ) ^ (-σ) ≤ ((Real.log 4 + 4) * b) * (b : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right this hpow
      _ = (Real.log 4 + 4) * (b * (b : ℝ) ^ (-σ)) := by ring
      _ = (Real.log 4 + 4) * (b : ℝ) ^ (1 - σ) := by
          have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 1) (le_of_lt (lt_of_le_of_lt ha hab)))
          rw [← Real.rpow_natCast, Nat.cast_one, ← Real.rpow_add hbpos]
          simp [sub_eq_add_neg]
  have hψa : ψ (a : ℝ) * ((a + 1 : ℕ) : ℝ) ^ (-σ) ≥ 0 :=
    mul_nonneg (psi_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmid : ∑ n ∈ Finset.Icc (a + 1) (b - 1),
        ψ (n : ℝ) * ((n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      (Real.log 4 + 4) * σ * ∑ n ∈ Finset.Icc (a + 1) (b - 1), (n : ℝ) ^ (1 - σ - 1) := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) ?_
    · have hn1 : 1 ≤ n := by
        rw [Finset.mem_Icc] at hn; omega
      have hψ : ψ (n : ℝ) ≤ (Real.log 4 + 4) * n := psi_le_C_mul _ (Nat.cast_nonneg _)
      have hdiff := rpow_sub_succ_le hn1 (lt_trans (by norm_num : (0 : ℝ) < 1) hσ)
      have hdiff0 : 0 ≤ (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) :=
        le_trans (by linarith) (le_trans hdiff (mul_nonneg (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) hσ)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      -- simpler nonneg: rpow decreasing
      have hdiff0' : 0 ≤ (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
        rw [sub_nonneg]
        have hnR : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn1
        have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        have hneg : -σ ≤ 0 := by linarith
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast Nat.cast_pos.mpr hn1) this hneg
      calc
        ψ (n : ℝ) * ((n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ))
            ≤ ((Real.log 4 + 4) * n) * ((n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_right hψ hdiff0'
        _ ≤ ((Real.log 4 + 4) * n) * (σ * (n : ℝ) ^ (-σ - 1)) :=
          mul_le_mul_of_nonneg_left hdiff (mul_nonneg hC (Nat.cast_nonneg _))
        _ = (Real.log 4 + 4) * σ * (n * (n : ℝ) ^ (-σ - 1)) := by ring
        _ = (Real.log 4 + 4) * σ * (n : ℝ) ^ (1 - σ - 1) := by
            have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
            rw [← Real.rpow_natCast, Nat.cast_one, ← Real.rpow_add hnpos]
            simp [sub_eq_add_neg]
    · rw [← Finset.mul_sum, ← mul_assoc]
  -- drop the negative -ψ(a) f(a+1) ≤ 0 so omit it (upper bound)
  have : ψ (b : ℝ) * (b : ℝ) ^ (-σ) - ψ (a : ℝ) * ((a + 1 : ℕ) : ℝ) ^ (-σ) +
        ∑ n ∈ Finset.Icc (a + 1) (b - 1),
          ψ (n : ℝ) * ((n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      (Real.log 4 + 4) * (b : ℝ) ^ (1 - σ) +
        (Real.log 4 + 4) * σ * ∑ n ∈ Finset.Icc (a + 1) (b - 1), (n : ℝ) ^ (1 - σ - 1) := by
    nlinarith [hψb, hψa, hmid]
  refine le_trans this ?_
  have : (Real.log 4 + 4) * (a : ℝ) ^ (1 - σ) ≥ 0 :=
    mul_nonneg hC (Real.rpow_nonneg ha0 _)
  nlinarith

end
