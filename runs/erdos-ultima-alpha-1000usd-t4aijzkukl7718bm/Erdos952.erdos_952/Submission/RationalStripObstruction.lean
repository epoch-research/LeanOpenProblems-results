import Submission.StripObstruction

/-! Prime walks cannot remain in a finite-width strip of rational slope. -/
namespace Erdos952Investigation
namespace RationalStrip

set_option maxHeartbeats 0

/-- A Euclid sequence whose square-plus-one moduli avoid every factor of `B`. -/
def euclidT (B : ℕ) : ℕ → ℕ
  | 0 => B
  | n + 1 => euclidT B n * (euclidT B n ^ 2 + 1)

def euclidM (B n : ℕ) : ℕ := euclidT B n ^ 2 + 1

lemma base_dvd_t (B n : ℕ) : B ∣ euclidT B n := by
  induction n with
  | zero => exact dvd_rfl
  | succ n ih => exact dvd_mul_of_dvd_left ih _

lemma t_pos {B : ℕ} (hB : 0 < B) (n : ℕ) : 0 < euclidT B n := by
  induction n with
  | zero => exact hB
  | succ n ih => exact Nat.mul_pos ih (by positivity)

lemma m_dvd_later_t (B : ℕ) {i j : ℕ} (hij : i < j) : euclidM B i ∣ euclidT B j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : i = j
    · subst i
      exact dvd_mul_left _ _
    · exact dvd_mul_of_dvd_left (ih (by omega)) _

lemma coprime_m_base (B n : ℕ) : (euclidM B n).Coprime B := by
  apply Nat.Coprime.symm
  apply Nat.Coprime.of_dvd_left (dvd_pow (base_dvd_t B n) (by decide : 2 ≠ 0))
  simp [euclidM, Nat.coprime_self_add_right]

lemma pairwise_coprime_m (B : ℕ) : Pairwise fun i j => (euclidM B i).Coprime (euclidM B j) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (by omega)).symm
  apply Nat.Coprime.of_dvd_left (dvd_pow (m_dvd_later_t B hlt) (by decide : 2 ≠ 0))
  simp [euclidM, Nat.coprime_self_add_right]

lemma exists_scaled_prime_free_horizontal_translate {ι : Type*} [Fintype ι]
    (d : GaussianInt) (hd0 : d ≠ 0) (f : ι → GaussianInt) (M : ℤ) :
    ∃ A : ℤ, M < A ∧ ∀ i, ∀ z : GaussianInt,
      d * z = (A : GaussianInt) + f i → ¬ Prime z := by
  classical
  have hdn := GaussianInt.norm_nonneg d
  let B := d.norm.natAbs
  have hB : 0 < B := Int.natAbs_pos.mpr (GaussianInt.norm_pos.mpr hd0).ne'
  let e : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  have he : Function.Injective e :=
    Fin.val_injective.comp (Fintype.equivFin ι).injective
  let t : ι → ℕ := fun i => euclidT B (e i)
  let m : ι → ℕ := fun i => euclidM B (e i)
  have hm (i : ι) : (m i : ℤ) = (t i : ℤ) ^ 2 + 1 := by
    simp [m, t, euclidM]
  have hmpos (i : ι) : 0 < m i := by dsimp [m, euclidM]; positivity
  have hmone (i : ι) : 1 < m i := by
    have ht := t_pos hB (e i)
    dsimp [m, euclidM]
    nlinarith
  have hmB (i : ι) : (m i).Coprime B := coprime_m_base B (e i)
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact pairwise_coprime_m B (fun h => hij (he h))
  let r : ι → ℕ := fun i => (((t i : ℤ) * (f i).im - (f i).re) % (m i : ℤ)).toNat
  let a := Nat.chineseRemainderOfFinset r m Finset.univ
    (fun i _ => (hmpos i).ne') hcop
  let P : ℕ := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos fun i _ => hmpos i
  let T : ℤ := ∑ i, (d.norm * (m i : ℤ)^2 + |(f i).re| + 1)
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (T + |M|)
  let A : ℕ := a.val + K * P
  have hKA : (K : ℤ) ≤ (A : ℤ) := by
    have : K ≤ A := by dsimp [A]; nlinarith
    exact_mod_cast this
  refine ⟨A, by have := le_abs_self M; omega, ?_⟩
  intro i z hz hpz
  simp only [Int.cast_natCast] at hz
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
    convert dvd_neg.mpr (Int.modEq_iff_dvd.mp hmod') using 1; ring
  have hsmall : d.norm * (m i : ℤ)^2 + |(f i).re| + 1 ≤ T :=
    Finset.single_le_sum (f := fun j => d.norm * (m j : ℤ)^2 + |(f j).re| + 1)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hreal : d.norm * (m i : ℤ)^2 < (A : ℤ) + (f i).re := by
    have := neg_abs_le (f i).re
    have := abs_nonneg M
    omega
  let y : GaussianInt := (A : GaussianInt) + f i
  let g : GaussianInt := ⟨t i, 1⟩
  have hg : g.norm = (m i : ℤ) := by simp [g, gaussian_norm_sq, hm]
  have hgy : g ∣ y := by
    apply gaussian_linear_divisor
    simpa only [y, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      zero_add, ← hm] using hdiv
  have hnormdiv : (m i : ℤ) ∣ d.norm * z.norm := by
    have hdv := map_dvd (Zsqrtd.normMonoidHom (d := -1)) hgy
    change g.norm ∣ y.norm at hdv
    rw [hg, show y = d * z from hz.symm, Zsqrtd.norm_mul] at hdv
    exact hdv
  have hnatdiv : m i ∣ B * z.norm.natAbs := by
    simpa only [Int.natAbs_natCast, Int.natAbs_mul, B] using
      (Int.natAbs_dvd_natAbs.mpr hnormdiv)
  have hmz : m i ∣ z.norm.natAbs := (hmB i).dvd_of_dvd_mul_left hnatdiv
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (ne_of_gt (hmone i))
  have hpzdiv : (p : ℤ) ∣ z.norm := Int.natCast_dvd.mpr (hpm.trans hmz)
  have hzbound := prime_norm_divisor_bound hpz hp hpzdiv
  have hpbound : (p : ℤ) ≤ m i := by exact_mod_cast Nat.le_of_dvd (hmpos i) hpm
  have hm0 : (0 : ℤ) ≤ m i := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg _
  have hzm : z.norm ≤ (m i : ℤ)^2 := by nlinarith
  have hynorm : y.norm ≤ d.norm * (m i : ℤ)^2 := by
    rw [show y = d * z from hz.symm, Zsqrtd.norm_mul]
    exact mul_le_mul_of_nonneg_left hzm hdn
  have hyre : y.re = (A : ℤ) + (f i).re := by simp [y]
  have hylower : y.re ≤ y.norm := le_trans (le_abs_self _) (abs_re_le_gaussian_norm y)
  rw [hyre] at hylower
  omega

lemma exists_scaled_prime_free_rectangle (d : GaussianInt) (hd : d ≠ 0)
    (B W : ℕ) (M : ℤ) :
    ∃ A : ℤ, M < A ∧ ∀ z : GaussianInt,
      A ≤ (d * z).re → (d * z).re ≤ A + W →
      -(B : ℤ) ≤ (d * z).im → (d * z).im ≤ B → ¬ Prime z := by
  let f : Fin (W + 1) × Fin (2 * B + 1) → GaussianInt :=
    fun p => ⟨p.1.val, (p.2.val : ℤ) - B⟩
  obtain ⟨A, hA, hf⟩ := exists_scaled_prime_free_horizontal_translate d hd f M
  refine ⟨A, hA, ?_⟩
  intro z hrl hru hil hiu
  let u : Fin (W + 1) := ⟨((d * z).re - A).toNat, by omega⟩
  let v : Fin (2 * B + 1) := ⟨((d * z).im + B).toNat, by omega⟩
  have hz : d * z = (A : GaussianInt) + f (u, v) := by
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, neg_mul, one_mul] at hrl hru hil hiu
    apply Zsqrtd.ext <;> simp [f, u, v] <;> omega
  exact hf (u, v) z hz

lemma prime_walk_bounded_in_rational_strip (d : GaussianInt) (hd : d ≠ 0)
    (x : ℕ → GaussianInt) (C : ℤ) (B : ℕ)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (hi : ∀ n, |(d * x n).im| ≤ B) : ∃ L : ℤ, ∀ n, (x n).norm ≤ L := by
  have hC : 0 < C := lt_of_le_of_lt (GaussianInt.norm_nonneg _) (h 0).2
  have hdn : 0 < d.norm := GaussianInt.norm_pos.mpr hd
  let D : ℤ := d.norm * C
  have hD : 0 < D := mul_pos hdn hC
  have hW : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hD.le
  let y : ℕ → GaussianInt := fun n => d * x n
  have hstepnorm (n : ℕ) : (y (n + 1) - y n).norm < D := by
    dsimp [y, D]
    rw [← mul_sub, Zsqrtd.norm_mul]
    exact mul_lt_mul_of_pos_left (h n).2 hdn
  obtain ⟨A, hA, hfree⟩ := exists_scaled_prime_free_rectangle d hd B D.toNat |(y 0).re|
  have hApos : 0 < A := lt_of_le_of_lt (abs_nonneg _) hA
  have hb (n : ℕ) : -(B : ℤ) ≤ (y n).im ∧ (y n).im ≤ B := abs_le.mp (hi n)
  have hr (n : ℕ) : -A < (y n).re ∧ (y n).re < A := by
    induction n with
    | zero => exact abs_lt.mp hA
    | succ n ih =>
      have hstep : |(y (n + 1)).re - (y n).re| < D :=
        lt_of_le_of_lt (abs_re_le_gaussian_norm _) (hstepnorm n)
      have hdelta := abs_lt.mp hstep
      constructor
      · by_contra hn
        have hnp : ¬ Prime (-x (n + 1)) := hfree (-x (n + 1))
          (by simp only [mul_neg, Zsqrtd.re_neg];
              change A ≤ -(y (n + 1)).re; omega)
          (by simp only [mul_neg, Zsqrtd.re_neg]; change -(y (n + 1)).re ≤ _; omega)
          (by simp only [mul_neg, Zsqrtd.im_neg]; change -(B : ℤ) ≤ -(y (n + 1)).im;
              have := hb (n + 1); omega)
          (by simp only [mul_neg, Zsqrtd.im_neg]; change -(y (n + 1)).im ≤ (B : ℤ);
              have := hb (n + 1); omega)
        exact hnp (h (n + 1)).1.neg
      · by_contra hn
        exact hfree (x (n + 1)) (by change A ≤ (y (n + 1)).re; omega)
          (by change (y (n + 1)).re ≤ _; omega)
          (hb (n + 1)).1 (hb (n + 1)).2 (h (n + 1)).1
  refine ⟨A ^ 2 + (B : ℤ) ^ 2, ?_⟩
  intro n
  have hr2 : (y n).re ^ 2 ≤ A ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_pos hApos]
    exact le_of_lt (abs_lt.mpr (hr n)))
  have hi2 : (y n).im ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg B)]
    exact hi n)
  have hybound : (y n).norm ≤ A ^ 2 + (B : ℤ)^2 := by
    rw [gaussian_norm_sq]
    omega
  have hxy : (x n).norm ≤ (y n).norm := by
    change (x n).norm ≤ (d * x n).norm
    rw [Zsqrtd.norm_mul]
    have hdn1 : 1 ≤ d.norm := hdn
    have := GaussianInt.norm_nonneg (x n)
    nlinarith
  exact hxy.trans hybound

/-- Every nonzero integer linear projection of an injective bounded-step prime
walk is unbounded on every tail. -/
theorem rational_projection_unbounded (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ N B : ℕ, ∃ n ≥ N, (B : ℤ) < |a * (x n).re + b * (x n).im| := by
  intro N B
  by_contra! hbound
  let d : GaussianInt := ⟨b, a⟩
  have hd : d ≠ 0 := by
    intro he
    have ha := congrArg Zsqrtd.im he
    have hb := congrArg Zsqrtd.re he
    simp only [d, Zsqrtd.im_zero, Zsqrtd.re_zero] at ha hb
    exact hab.elim (fun h => h ha) (fun h => h hb)
  let y : ℕ → GaussianInt := fun n => x (N + n)
  have hyinj : Function.Injective y := by
    intro i j hij
    exact Nat.add_left_cancel (hx hij)
  have hyp : ∀ n, Prime (y n) ∧ (y (n + 1) - y n).norm < C := by
    intro n
    simpa only [y, Nat.add_assoc] using h (N + n)
  have hystrip : ∀ n, |(d * y n).im| ≤ B := by
    intro n
    simpa only [Zsqrtd.im_mul, d, y, add_comm] using
      hbound (N + n) (Nat.le_add_right _ _)
  obtain ⟨L, hL⟩ := prime_walk_bounded_in_rational_strip d hd y C B hyp hystrip
  obtain ⟨k, hk⟩ := injective_escapes_norm y hyinj L
  have := hk k le_rfl
  have := hL k
  omega

theorem not_in_rational_affine_strip (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C)
    (a b k : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ ∃ B : ℕ, ∀ n, |a * (x n).re + b * (x n).im - k| ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, _, hn⟩ := rational_projection_unbounded x C hx h a b hab 0 (B + k.natAbs)
  have habs : |a * (x n).re + b * (x n).im| ≤ (B : ℤ) + |k| := by
    calc
      _ = |(a * (x n).re + b * (x n).im - k) + k| := by rw [sub_add_cancel]
      _ ≤ |a * (x n).re + b * (x n).im - k| + |k| := abs_add_le _ _
      _ ≤ _ := add_le_add_left (hB n) _
  simp only [Nat.cast_add, Int.natCast_natAbs] at hn
  omega

#print axioms not_in_rational_affine_strip

#print axioms exists_scaled_prime_free_rectangle
#print axioms rational_projection_unbounded

end RationalStrip
end Erdos952Investigation
