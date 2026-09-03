import Submission.Investigation

/-! Prime-free translates and the obstruction to walks in bounded-width strips. -/

namespace Erdos952Investigation

set_option maxHeartbeats 0

lemma gaussian_linear_divisor (t : ℤ) (z : GaussianInt)
    (h : t ^ 2 + 1 ∣ z.re - t * z.im) : (⟨t, 1⟩ : GaussianInt) ∣ z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨t * k + z.im, -k⟩, ?_⟩
  apply Zsqrtd.ext
  · simp only [Zsqrtd.re_mul]
    dsimp
    nlinarith [hk]
  · simp only [Zsqrtd.im_mul]
    ring

lemma not_prime_of_small_divisor {a z : GaussianInt} (had : a ∣ z)
    (ha : 1 < a.norm) (hz : a.norm < z.norm) : ¬ Prime z := by
  intro hp
  obtain ⟨b, hb⟩ := had
  have hau : ¬ IsUnit a := by
    intro h
    have := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) a).mpr h
    omega
  have hbu := (hp.irreducible.isUnit_or_isUnit hb).resolve_left hau
  have hb1 := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) b).mpr hbu
  have hnorm : z.norm = a.norm := by rw [hb, Zsqrtd.norm_mul, hb1, mul_one]
  omega

lemma exists_prime_free_horizontal_translate {ι : Type*} [Fintype ι]
    (f : ι → GaussianInt) (M : ℤ) :
    ∃ A : ℤ, M < A ∧ ∀ i, ¬ Prime ((A : GaussianInt) + f i) := by
  classical
  let e : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  have he : Function.Injective e :=
    Fin.val_injective.comp (Fintype.equivFin ι).injective
  let t : ι → ℕ := fun i => Nat.fermatNumber (e i) - 1
  let m : ι → ℕ := fun i => Nat.fermatNumber (e i + 1)
  have hm (i : ι) : (m i : ℤ) = (t i : ℤ) ^ 2 + 1 := by
    exact_mod_cast Nat.fermatNumber_succ (e i)
  have hmpos (i : ι) : 0 < m i := lt_of_lt_of_le (by decide : 0 < 3)
    (Nat.three_le_fermatNumber _)
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact Nat.coprime_fermatNumber_fermatNumber (fun h => hij (he (by omega)))
  let r : ι → ℕ := fun i => (((t i : ℤ) * (f i).im - (f i).re) % (m i : ℤ)).toNat
  let a := Nat.chineseRemainderOfFinset r m Finset.univ
    (fun i _ => (hmpos i).ne') hcop
  let P : ℕ := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos fun i _ => hmpos i
  let T : ℤ := ∑ i, ((m i : ℤ) + |(f i).re|)
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (T + |M|)
  let A : ℕ := a.val + K * P
  have hKA : (K : ℤ) ≤ (A : ℤ) := by
    have : K ≤ A := by dsimp [A]; nlinarith
    exact_mod_cast this
  refine ⟨A, by have := le_abs_self M; omega, ?_⟩
  intro i
  simp only [Int.cast_natCast]
  have hdP : m i ∣ P := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hmod : A ≡ r i [MOD m i] := by
    change (a.val + K * P) % m i = r i % m i
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdP, mul_zero,
      Nat.zero_mod, add_zero, Nat.mod_mod]
    exact a.property i (Finset.mem_univ i)
  have hr : (r i : ℤ) = ((t i : ℤ) * (f i).im - (f i).re) % m i := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (hmpos i).ne'))
  have hmod' : (A : ℤ) ≡ (t i : ℤ) * (f i).im - (f i).re [ZMOD m i] := by
    calc
      _ = (r i : ℤ) % m i := Int.natCast_modEq_iff.mpr hmod
      _ = _ := by rw [hr, Int.emod_emod]
  have hdiv : (m i : ℤ) ∣ (A : ℤ) + (f i).re - (t i : ℤ) * (f i).im := by
    convert dvd_neg.mpr (Int.modEq_iff_dvd.mp hmod') using 1 <;> ring
  have hsmall : (m i : ℤ) + |(f i).re| ≤ T :=
    Finset.single_le_sum (f := fun j => (m j : ℤ) + |(f j).re|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hreal : (m i : ℤ) < (A : ℤ) + (f i).re := by
    have := neg_abs_le (f i).re
    have := abs_nonneg M
    omega
  let z : GaussianInt := (A : GaussianInt) + f i
  let d : GaussianInt := ⟨t i, 1⟩
  have hd : d.norm = (m i : ℤ) := by simp [d, gaussian_norm_sq, hm]
  apply not_prime_of_small_divisor (a := d)
  · apply gaussian_linear_divisor
    simpa only [z, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      zero_add, ← hm] using hdiv
  · rw [hd]
    have hmi : 1 < m i := lt_of_lt_of_le (by decide : 1 < 3)
      (Nat.three_le_fermatNumber (e i + 1))
    exact_mod_cast hmi
  · rw [hd, gaussian_norm_sq]
    have hzre : z.re = (A : ℤ) + (f i).re := by simp [z]
    change (m i : ℤ) < z.re ^ 2 + z.im ^ 2
    have := Int.le_self_sq z.re
    nlinarith [sq_nonneg z.im]

lemma exists_prime_free_rectangle (B W : ℕ) (M : ℤ) :
    ∃ A : ℤ, M < A ∧ ∀ z : GaussianInt,
      A ≤ z.re → z.re ≤ A + W → -(B : ℤ) ≤ z.im → z.im ≤ B → ¬ Prime z := by
  let f : Fin (W + 1) × Fin (2 * B + 1) → GaussianInt :=
    fun p => ⟨p.1.val, (p.2.val : ℤ) - B⟩
  obtain ⟨A, hA, hf⟩ := exists_prime_free_horizontal_translate f M
  refine ⟨A, hA, ?_⟩
  intro z hrl hru hil hiu
  let u : Fin (W + 1) := ⟨(z.re - A).toNat, by omega⟩
  let v : Fin (2 * B + 1) := ⟨(z.im + B).toNat, by omega⟩
  have hz : (A : GaussianInt) + f (u, v) = z := by
    apply Zsqrtd.ext <;> simp [f, u, v] <;> omega
  rw [← hz]
  exact hf (u, v)

lemma abs_re_le_gaussian_norm (z : GaussianInt) : |z.re| ≤ z.norm := by
  rw [abs_le, gaussian_norm_sq]
  have h1 := Int.le_self_sq z.re
  have h2 := Int.le_self_sq (-z.re)
  constructor <;> nlinarith [sq_nonneg z.im]

lemma prime_walk_bounded_in_horizontal_strip (x : ℕ → GaussianInt) (C : ℤ) (B : ℕ)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (hi : ∀ n, |(x n).im| ≤ B) : ∃ L : ℤ, ∀ n, (x n).norm ≤ L := by
  have hC : 0 < C := lt_of_le_of_lt (GaussianInt.norm_nonneg _) (h 0).2
  have hW : (C.toNat : ℤ) = C := Int.toNat_of_nonneg hC.le
  obtain ⟨A, hA, hfree⟩ := exists_prime_free_rectangle B C.toNat |(x 0).re|
  have hApos : 0 < A := lt_of_le_of_lt (abs_nonneg _) hA
  have hb (n : ℕ) : -(B : ℤ) ≤ (x n).im ∧ (x n).im ≤ B := abs_le.mp (hi n)
  have hr (n : ℕ) : -A < (x n).re ∧ (x n).re < A := by
    induction n with
    | zero => exact abs_lt.mp hA
    | succ n ih =>
      have hstep : |(x (n + 1)).re - (x n).re| < C :=
        lt_of_le_of_lt (abs_re_le_gaussian_norm _) (h n).2
      have hdelta := abs_lt.mp hstep
      constructor
      · by_contra hn
        have hnp : ¬ Prime (-x (n + 1)) := hfree (-x (n + 1))
          (by simp only [Zsqrtd.re_neg]; omega)
          (by simp only [Zsqrtd.re_neg]; omega)
          (by simp only [Zsqrtd.im_neg]; have := hb (n + 1); omega)
          (by simp only [Zsqrtd.im_neg]; have := hb (n + 1); omega)
        exact hnp (h (n + 1)).1.neg
      · by_contra hn
        exact hfree (x (n + 1)) (by omega) (by omega)
          (hb (n + 1)).1 (hb (n + 1)).2 (h (n + 1)).1
  refine ⟨A ^ 2 + (B : ℤ) ^ 2, ?_⟩
  intro n
  have hr2 : (x n).re ^ 2 ≤ A ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_pos hApos]
    exact le_of_lt (abs_lt.mpr (hr n)))
  have hi2 : (x n).im ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg B)]
    exact hi n)
  rw [gaussian_norm_sq]
  omega

lemma injective_prime_walk_im_unbounded (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    ¬ ∃ B : ℕ, ∀ n, |(x n).im| ≤ B := by
  rintro ⟨B, hi⟩
  obtain ⟨L, hL⟩ := prime_walk_bounded_in_horizontal_strip x C B h hi
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx L
  have := hN N le_rfl
  have := hL N
  omega

#print axioms prime_walk_bounded_in_horizontal_strip
#print axioms injective_prime_walk_im_unbounded

#print axioms exists_prime_free_rectangle

#print axioms exists_prime_free_horizontal_translate

end Erdos952Investigation
