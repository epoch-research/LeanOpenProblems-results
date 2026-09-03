import FormalConjecturesUtil

/-!
# Erdős Problem 322

*Reference:* [erdosproblems.com/322](https://www.erdosproblems.com/322)
-/

namespace Erdos322

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of nonnegative integers. The bases can be restricted to the interval from `0` to `n`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

lemma count_ge_of_family {α : Type} [Fintype α] (k n : ℕ) (hk : 0 < k)
    (f : α → Fin k → ℕ) (hf : Function.Injective f)
    (hs : ∀ a, ∑ i, f a i ^ k = n) :
    Fintype.card α ≤ representationCount k n := by
  classical
  have hb : ∀ a i, f a i ≤ n := by
    intro a i
    calc
      f a i ≤ f a i ^ k := Nat.le_pow hk
      _ ≤ ∑ j, f a j ^ k := Finset.single_le_sum (f := fun j ↦ f a j ^ k) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      _ = n := hs a
  let g : α → Fin k → Fin (n + 1) := fun a i ↦ ⟨f a i, Nat.lt_succ_of_le (hb a i)⟩
  have hg : Function.Injective g := by
    intro a b h
    apply hf
    funext i
    exact congrArg Fin.val (congrFun h i)
  have hc := Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := (Finset.univ : Finset (Fin k → Fin (n + 1))).filter
      (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)) g
    (by intro a _; simpa [g] using hs a) hg.injOn
  simpa [representationCount] using hc

lemma count_dilate_le (k n t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    representationCount k n ≤ representationCount k (t^k*n) := by
  classical
  let s := (Finset.univ : Finset (Fin k → Fin (n+1))).filter
    (fun a ↦ ∑ i, (a i : ℕ)^k = n)
  let f : s → Fin k → ℕ := fun a i ↦ t * (a.val i : ℕ)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hi := congrFun h i
    exact Nat.eq_of_mul_eq_mul_left ht hi
  have hs : ∀ a, ∑ i, f a i ^ k = t^k*n := by
    intro a
    have ha : ∑ i, (a.val i : ℕ)^k = n := (Finset.mem_filter.mp a.property).2
    simp only [f, mul_pow, ← Finset.mul_sum, ha]
  have h := count_ge_of_family k (t^k*n) hk f hf hs
  simpa only [Fintype.card_coe, s, representationCount] using h

lemma count_dilate_eq_of_dvd (k n t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (H : ∀ a : Fin k → ℕ, ∑ i, a i ^ k = t^k*n → ∀ i, t ∣ a i) :
    representationCount k (t^k*n) = representationCount k n := by
  classical
  apply Nat.le_antisymm ?_ (count_dilate_le k n t hk ht)
  let s := (Finset.univ : Finset (Fin k → Fin (t^k*n+1))).filter
    (fun a ↦ ∑ i, (a i : ℕ)^k = t^k*n)
  let f : s → Fin k → ℕ := fun a i ↦ (a.val i : ℕ) / t
  have ha : ∀ a : s, ∑ i, (a.val i : ℕ)^k = t^k*n :=
    fun a ↦ (Finset.mem_filter.mp a.property).2
  have hd : ∀ (a : s) i, t ∣ (a.val i : ℕ) := fun a ↦ H _ (ha a)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hi : (a.val i : ℕ) / t = (b.val i : ℕ) / t := congrFun h i
    rw [← Nat.div_mul_cancel (hd a i), ← Nat.div_mul_cancel (hd b i), hi]
  have hs : ∀ a, ∑ i, f a i ^ k = n := by
    intro a
    have hh : t^k * (∑ i, f a i ^ k) = t^k*n := by
      calc
        t^k * (∑ i, f a i ^ k) = ∑ i, (t * f a i)^k := by
          simp only [Finset.mul_sum, mul_pow]
        _ = ∑ i, (a.val i : ℕ)^k := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show t * f a i = (a.val i : ℕ) from Nat.mul_div_cancel' (hd a i)]
        _ = t^k*n := ha a
    exact Nat.eq_of_mul_eq_mul_left (pow_pos ht k) hh
  have hh := count_ge_of_family k n hk f hf hs
  simpa only [Fintype.card_coe, s, representationCount] using hh

lemma fourth_mod16_le_one (a : ℕ) : a^4 % 16 ≤ 1 := by
  have h : ∀ b : Fin 16, (b : ℕ)^4 % 16 ≤ 1 := by decide
  have ha := h ⟨a % 16, Nat.mod_lt _ (by decide)⟩
  simpa [Nat.pow_mod] using ha

lemma even_of_four_fourths (a : Fin 4 → ℕ) (h : 16 ∣ ∑ i, a i ^ 4) :
    ∀ i, 2 ∣ a i := by
  have hs : ∑ i, a i ^ 4 % 16 ≤ 4 := by
    calc
      ∑ i, a i ^ 4 % 16 ≤ ∑ _ : Fin 4, 1 :=
        Finset.sum_le_sum (fun i _ ↦ fourth_mod16_le_one (a i))
      _ = 4 := by simp
  have hm : (∑ i, a i ^ 4 % 16) % 16 = 0 := by
    rw [← Finset.sum_nat_mod]
    exact Nat.mod_eq_zero_of_dvd h
  have hz : ∑ i, a i ^ 4 % 16 = 0 := by omega
  intro i
  have hi : a i ^ 4 % 16 = 0 := by
    have hle : a i ^ 4 % 16 ≤ ∑ j, a j ^ 4 % 16 :=
      Finset.single_le_sum (f := fun j ↦ a j ^ 4 % 16)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle
  have hd : 2 ∣ a i ^ 4 := (by decide : 2 ∣ 16).trans (Nat.dvd_of_mod_eq_zero hi)
  exact Nat.prime_two.dvd_of_dvd_pow hd

lemma count_four_dilate16 (n : ℕ) :
    representationCount 4 (16*n) = representationCount 4 n := by
  apply count_dilate_eq_of_dvd 4 n 2 (by decide) (by decide)
  intro a ha
  apply even_of_four_fourths a
  rw [ha]
  norm_num


lemma mahler (p q : ℕ) (hpq : 3 * p ≤ q) :
    (q^4 - 9*p^3*q)^3 + (9*p^4)^3 + (3*p*q^3 - 9*p^4)^3 = q^12 := by
  have hA : 9*p^3*q ≤ q^4 := by
    have h := Nat.pow_le_pow_left hpq 3
    calc
      9*p^3*q ≤ 27*p^3*q := Nat.mul_le_mul_right q (Nat.mul_le_mul_right (p^3) (by decide))
      _ = (3*p)^3*q := by ring
      _ ≤ q^3*q := Nat.mul_le_mul_right q h
      _ = q^4 := by ring
  have hB : 9*p^4 ≤ 3*p*q^3 := by
    have h := Nat.pow_le_pow_left hpq 3
    calc
      9*p^4 ≤ 81*p^4 := by omega
      _ = 3*p*(3*p)^3 := by ring
      _ ≤ 3*p*q^3 := Nat.mul_le_mul_left (3*p) h
  zify [hA, hB]
  ring


def rotation (a b c : ℕ) (r : Fin 3) : Fin 3 → ℕ :=
  ![![a, b, c], ![b, c, a], ![c, a, b]] r

lemma rotation_min (a b c : ℕ) (r : Fin 3) (hba : b ≤ a) (hbc : b ≤ c) :
    min (rotation a b c r 0) (min (rotation a b c r 1) (rotation a b c r 2)) = b := by
  fin_cases r <;> simp [rotation] <;> omega

lemma rotation_injective (a b c : ℕ) (hab : a ≠ b) :
    Function.Injective (rotation a b c) := by
  intro r s h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases r <;> fin_cases s <;> simp [rotation] at h0 h1 h2 ⊢ <;> omega

lemma rotation_sum (a b c : ℕ) (r : Fin 3) :
    ∑ i, rotation a b c r i ^ 3 = a^3 + b^3 + c^3 := by
  fin_cases r <;> simp [rotation, Fin.sum_univ_succ] <;> omega

lemma mahler_min_bounds (p q : ℕ) (hpq : 3*p ≤ q) (hq : 0 < q) :
    9*p^4 < q^4 - 9*p^3*q ∧ 9*p^4 ≤ 3*p*q^3 - 9*p^4 := by
  have h3 := Nat.pow_le_pow_left hpq 3
  have h4 := Nat.pow_le_pow_left hpq 4
  have hpos : 0 < q^4 := pow_pos hq 4
  have hA : 9*p^4 + 9*p^3*q < q^4 := by
    nlinarith [Nat.mul_le_mul_right q h3]
  have hB : 18*p^4 ≤ 3*p*q^3 := by
    calc
      18*p^4 ≤ 81*p^4 := by omega
      _ = 3*p*(3*p)^3 := by ring
      _ ≤ 3*p*q^3 := Nat.mul_le_mul_left (3*p) h3
  omega

lemma cubic_count_strong (m : ℕ) (hm : 0 < m) :
    3 * (m + 1) ≤ representationCount 3 ((3*m)^12) := by
  let A : Fin (m+1) → ℕ := fun p ↦ (3*m)^4 - 9*(p:ℕ)^3*(3*m)
  let B : Fin (m+1) → ℕ := fun p ↦ 9*(p:ℕ)^4
  let C : Fin (m+1) → ℕ := fun p ↦ 3*(p:ℕ)*(3*m)^3 - 9*(p:ℕ)^4
  have hb : ∀ p, B p < A p ∧ B p ≤ C p := by
    intro p
    exact mahler_min_bounds (p:ℕ) (3*m) (by have := p.isLt; omega) (by omega)
  let f : Fin 3 × Fin (m+1) → Fin 3 → ℕ := fun x ↦ rotation (A x.2) (B x.2) (C x.2) x.1
  have hinj : Function.Injective f := by
    rintro ⟨r,p⟩ ⟨s,p'⟩ h
    have hv := congrArg (fun g : Fin 3 → ℕ ↦ min (g 0) (min (g 1) (g 2))) h
    change min (rotation (A p) (B p) (C p) r 0)
      (min (rotation (A p) (B p) (C p) r 1) (rotation (A p) (B p) (C p) r 2)) =
      min (rotation (A p') (B p') (C p') s 0)
      (min (rotation (A p') (B p') (C p') s 1) (rotation (A p') (B p') (C p') s 2)) at hv
    rw [rotation_min _ _ _ _ (hb p).1.le (hb p).2,
      rotation_min _ _ _ _ (hb p').1.le (hb p').2] at hv
    have hp : p = p' := by
      apply Fin.ext
      simpa [B] using hv
    subst p'
    have hr : r = s := rotation_injective (A p) (B p) (C p) (ne_of_gt (hb p).1) h
    subst s
    rfl
  have hs : ∀ x, ∑ i, f x i ^ 3 = (3*m)^12 := by
    rintro ⟨r,p⟩
    rw [show f (r,p) = rotation (A p) (B p) (C p) r from rfl, rotation_sum]
    exact mahler (p:ℕ) (3*m) (by have := p.isLt; omega)
  simpa using count_ge_of_family 3 ((3*m)^12) (by decide) f hinj hs

lemma power_root12 (m : ℕ) : (((3*(m+1))^12 : ℕ) : ℝ)^(1/12:ℝ) = (3*(m+1):ℕ) := by
  push_cast
  rw [← Real.rpow_natCast_mul (by positivity) 12 (1/12)]
  norm_num

lemma cubic_growth_strong :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount 3 n}.Infinite := by
  refine ⟨1/12, by norm_num, ?_⟩
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ ↦ (3*(m+1))^12)
  · intro m m' h
    have h := (Nat.pow_left_injective (by decide : 12 ≠ 0)) h
    omega
  · intro m
    have h := cubic_count_strong (m + 1) (by omega)
    change (((3*(m+1))^12 : ℕ) : ℝ) ^ (1 / 12 : ℝ) < _
    rw [power_root12]
    exact_mod_cast (lt_of_lt_of_le (show 3*(m+1) < 3*(m+1+1) by omega) h)


theorem no_polynomial_growth_iff (f : ℕ → ℕ) :
    (¬ ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < f n}.Infinite) ↔
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ n : ℕ, 1 ≤ n → (f n : ℝ) ≤ C * (n : ℝ)^ε := by
  classical
  constructor
  · intro h ε hε
    have hs : {n : ℕ | (n : ℝ)^ε < f n}.Finite := by
      by_contra hi
      exact h ⟨ε, hε, hi⟩
    obtain ⟨M, hM⟩ := (hs.image f).bddAbove
    refine ⟨M + 1, by positivity, ?_⟩
    intro n hn
    have hp : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
    by_cases he : (n : ℝ)^ε < f n
    · have hf : f n ≤ M := hM (Set.mem_image_of_mem f he)
      have hfR : (f n : ℝ) ≤ M := by exact_mod_cast hf
      nlinarith
    · have hf := le_of_not_gt he
      have hnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith
  · rintro h ⟨c, hc, hi⟩
    obtain ⟨C, hC, hbound⟩ := h (c/2) (by linarith)
    have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < c/2)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp ht C
    obtain ⟨n, hn, hnN⟩ := hi.exists_gt (max N 1)
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hu := hbound n hn1
    have hv := hN n (by omega)
    have hsq : (n : ℝ)^(c/2) * (n : ℝ)^(c/2) = (n : ℝ)^c := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have hw : C * (n : ℝ)^(c/2) ≤ (n : ℝ)^c := by
      rw [← hsq]
      exact mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hn0.le _)
    exact (not_lt_of_ge (hu.trans hw)) hn


/-- A precise characterization of a disproof, using the proved cubic case. -/
theorem disproof_iff_subpolynomial :
    (¬ (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite)) ↔
    ∃ k : ℕ, 4 ≤ k ∧ ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ n : ℕ, 1 ≤ n → (representationCount k n : ℝ) ≤ C * (n : ℝ)^ε := by
  classical
  constructor
  · intro h
    simp only [not_forall] at h
    obtain ⟨k, hk, hn⟩ := h
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have he : k = 3 := by omega
      subst k
      exact hn cubic_growth_strong
    exact ⟨k, hk4, (no_polynomial_growth_iff (representationCount k)).mp hn⟩
  · rintro ⟨k, hk, hb⟩ h
    exact (no_polynomial_growth_iff (representationCount k)).mpr hb (h k (by omega))

namespace PolynomialGrowthCriterion

lemma root_power (q D : ℕ) (hD : D ≠ 0) :
    ((q : ℝ)^D)^((1 : ℝ)/D) = q := by
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg q)]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  rw [mul_one_div_cancel hDR, Real.rpow_one]

/-- Linear multiplicity at a sequence of polynomially bounded heights is sufficient. -/
theorem of_power_sequence (f : ℕ → ℕ) (C D : ℕ) (hC : 0 < C) (hD : 0 < D)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ f (C*t^D)) :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < f n}.Infinite := by
  refine ⟨1/(D+1 : ℕ), by positivity, ?_⟩
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ ↦ C*(m+C+2)^D)
  · intro m m' he
    have hp := Nat.eq_of_mul_eq_mul_left hC he
    have hq := Nat.pow_left_injective (Nat.ne_of_gt hD) hp
    omega
  · intro m
    let t := m+C+2
    have ht : 1 ≤ t := by dsimp [t]; omega
    have hCt : C < t := by dsimp [t]; omega
    have hlt : C*t^D < t^(D+1) := by
      rw [pow_succ]
      exact (Nat.mul_lt_mul_of_pos_right hCt (pow_pos (by omega) D)).trans_eq (Nat.mul_comm _ _)
    have hr : (((C*t^D : ℕ) : ℝ))^((1 : ℝ)/(D+1 : ℕ)) < (t : ℝ) := by
      have hpos : (0 : ℝ) < 1/(D+1 : ℕ) := by positivity
      have hn : (0 : ℝ) ≤ (C*t^D : ℕ) := Nat.cast_nonneg _
      have hnlt : ((C*t^D : ℕ) : ℝ) < (t : ℝ)^(D+1) := by exact_mod_cast hlt
      have hh := Real.rpow_lt_rpow hn hnlt hpos
      rw [root_power t (D+1) (by omega)] at hh
      exact hh
    have hc : (t : ℝ) ≤ f (C*t^D) := by exact_mod_cast h t ht
    exact hr.trans_le hc

end PolynomialGrowthCriterion

/- A logarithmic lower bound for fourth-power representations. -/
namespace Quartic

def z : Zsqrtd (-3) := ⟨1, 4⟩
def A (r : ℕ) : ℤ := (z^r).re
def B (r : ℕ) : ℤ := (z^r).im

lemma A_succ (r : ℕ) : A (r+1) = A r - 12 * B r := by
  simp [A, B, z, pow_succ, Zsqrtd.re_mul]
  ring

lemma B_succ (r : ℕ) : B (r+1) = 4 * A r + B r := by
  simp [A, B, z, pow_succ, Zsqrtd.im_mul]
  ring

lemma A_step (r : ℕ) : A (r+2) = 2 * A (r+1) - 49 * A r := by
  rw [show r+2 = (r+1)+1 by omega, A_succ, B_succ, A_succ]
  ring

lemma A_not_dvd (r : ℕ) : ¬ (7 : ℤ) ∣ A r := by
  induction r using Nat.twoStepInduction with
  | zero => norm_num [A, z]
  | one => norm_num [A, z]
  | more r h0 h1 =>
    intro h
    have hd : (7 : ℤ) ∣ 49 * A r := dvd_mul_of_dvd_left (by norm_num) _
    have h2 : (7 : ℤ) ∣ 2 * A (r+1) := by
      convert dvd_add h hd using 1
      rw [A_step]
      ring
    have hp : Prime (7 : ℤ) := by norm_num
    rcases hp.dvd_mul.mp h2 with hh | hh
    · norm_num at hh
    · exact h1 hh

lemma AB_norm (r : ℕ) : (A r)^2 + 3*(B r)^2 = (7 : ℤ)^(2*r) := by
  calc
    (A r)^2 + 3*(B r)^2 = (z^r).norm := by simp [A, B, Zsqrtd.norm]; ring
    _ = z.norm ^ r := (Zsqrtd.normMonoidHom (d := -3)).map_pow z r
    _ = (7 : ℤ)^(2*r) := by simp [z, Zsqrtd.norm, pow_mul]

def quartet (r : ℕ) : Fin 4 → ℤ :=
  ![2*A r, A r + 3*B r, A r - 3*B r, (7 : ℤ)^r]

lemma quartet_sum_int (r : ℕ) : ∑ i, quartet r i ^ 4 = (19 : ℤ)*7^(4*r) := by
  have hn := AB_norm r
  have he : (2*A r)^4 + (A r+3*B r)^4 + (A r-3*B r)^4 =
      18 * ((A r)^2+3*(B r)^2)^2 := by ring
  simp only [quartet, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rw [← add_assoc, ← add_assoc, he, hn]
  simp only [← pow_mul]
  ring

lemma quartet_sum (r : ℕ) : ∑ i, (quartet r i).natAbs ^ 4 = 19*7^(4*r) := by
  apply Int.ofNat_inj.mp
  push_cast
  simp only [(by decide : Even 4).pow_abs]
  exact quartet_sum_int r

lemma quartet_first_value (r s : ℕ) :
    padicValNat 7 ((quartet r 0).natAbs * 7^s) = s := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hn : ¬ 7 ∣ (quartet r 0).natAbs := by
    rw [← Int.natCast_dvd]
    change ¬ (7 : ℤ) ∣ 2*A r
    intro h
    have hp : Prime (7 : ℤ) := by norm_num
    rcases hp.dvd_mul.mp h with h | h
    · norm_num at h
    · exact A_not_dvd r h
  have hne : (quartet r 0).natAbs ≠ 0 := by
    intro h
    exact hn (h ▸ dvd_zero _)
  rw [padicValNat.mul hne (by positivity), padicValNat.eq_zero_of_not_dvd hn,
    padicValNat.prime_pow, zero_add]

lemma quartic_count_lower (t : ℕ) :
    t + 1 ≤ representationCount 4 (19*7^(4*t)) := by
  let f : Fin (t+1) → Fin 4 → ℕ :=
    fun r i ↦ (quartet (r:ℕ) i).natAbs * 7^(t-(r:ℕ))
  have hf : Function.Injective f := by
    intro r r' h
    have hv := congrArg (padicValNat 7) (congrFun h 0)
    change padicValNat 7 ((quartet (r:ℕ) 0).natAbs * 7^(t-(r:ℕ))) =
      padicValNat 7 ((quartet (r':ℕ) 0).natAbs * 7^(t-(r':ℕ))) at hv
    rw [quartet_first_value, quartet_first_value] at hv
    apply Fin.ext
    have hr := r.isLt
    have hr' := r'.isLt
    omega
  have hs : ∀ r, ∑ i, f r i ^ 4 = 19*7^(4*t) := by
    intro r
    have he : 4*(r:ℕ) + (t-(r:ℕ))*4 = 4*t := by have := r.isLt; omega
    simp only [f, mul_pow, ← Finset.sum_mul, quartet_sum, ← pow_mul]
    rw [mul_assoc, ← pow_add, he]
  simpa using count_ge_of_family 4 (19*7^(4*t)) (by decide) f hf hs

theorem count_unbounded : ∀ M : ℕ, ∃ n : ℕ, M < representationCount 4 n := by
  intro M
  exact ⟨19*7^(4*M), lt_of_lt_of_le (Nat.lt_succ_self M) (quartic_count_lower M)⟩

/-- The norm construction gives logarithmically many representations infinitely often.
This is weaker than the positive-power growth in the conjecture. -/
theorem logarithmic_growth :
    {n : ℕ | Real.log (n : ℝ) / 32 < representationCount 4 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ ↦ 19*7^(4*t))
  · intro t u h
    have hp : 7^(4*t) = 7^(4*u) := Nat.eq_of_mul_eq_mul_left (by decide) h
    have he := Nat.pow_right_injective (by decide : 2 ≤ 7) hp
    omega
  · intro t
    change Real.log ((19*7^(4*t) : ℕ) : ℝ) / 32 < _
    have hl : Real.log ((19*7^(4*t) : ℕ) : ℝ) ≤ 19 + 28*(t : ℝ) := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      have h7 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 7)
      have h19 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 19)
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith
    have hc : (t : ℝ) + 1 ≤ representationCount 4 (19*7^(4*t)) := by
      exact_mod_cast quartic_count_lower t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith

end Quartic

namespace Quartic.TwoPrimes

def z7 : Zsqrtd (-3) := ⟨1, 4⟩
def z13 : Zsqrtd (-3) := ⟨11, 4⟩
def w (r s : ℕ) : Zsqrtd (-3) := z7^(r+1) * z13^(s+1)
def q (r s : ℕ) : ℕ := 7^(r+1) * 13^(s+1)

def eval7 : Zsqrtd (-3) →+* ZMod 7 :=
  Zsqrtd.lift ⟨2, by decide⟩
def eval7' : Zsqrtd (-3) →+* ZMod 7 :=
  Zsqrtd.lift ⟨-2, by decide⟩
def eval13 : Zsqrtd (-3) →+* ZMod 13 :=
  Zsqrtd.lift ⟨6, by decide⟩
def eval13' : Zsqrtd (-3) →+* ZMod 13 :=
  Zsqrtd.lift ⟨-6, by decide⟩

lemma norm_w (r s : ℕ) : (w r s).re^2 + 3*(w r s).im^2 = (q r s : ℤ)^2 := by
  calc
    (w r s).re^2 + 3*(w r s).im^2 = (w r s).norm := by
      simp [Zsqrtd.norm]; ring
    _ = z7.norm^(r+1) * z13.norm^(s+1) := by
      change (Zsqrtd.normMonoidHom (d := -3)) (z7^(r+1)*z13^(s+1)) = _
      simp only [map_mul, map_pow]
      rfl
    _ = (q r s : ℤ)^2 := by
      have h7 : z7.norm = (7 : ℤ)^2 := by norm_num [z7, Zsqrtd.norm]
      have h13 : z13.norm = (13 : ℤ)^2 := by norm_num [z13, Zsqrtd.norm]
      rw [h7, h13]
      simp only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← pow_mul]
      congr 2 <;> omega

lemma first_not_dvd7 (r s : ℕ) : ¬ (7 : ℤ) ∣ 2*(w r s).re := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have he : ((2*(w r s).re : ℤ) : ZMod 7) = eval7 (w r s) + eval7' (w r s) := by
    simp only [eval7, eval7', Zsqrtd.lift_apply_apply]
    push_cast
    ring
  have hval : ((2*(w r s).re : ℤ) : ZMod 7) = 2^(r+1)*5^(s+1) := by
    rw [he]
    simp only [w, map_mul, map_pow]
    rw [show eval7 z7 = 2 from by decide, show eval7 z13 = 5 from by decide,
      show eval7' z7 = 0 from by decide]
    simp
  intro h
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rw [hval] at hz
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)) hz

lemma first_not_dvd13 (r s : ℕ) : ¬ (13 : ℤ) ∣ 2*(w r s).re := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have he : ((2*(w r s).re : ℤ) : ZMod 13) = eval13 (w r s) + eval13' (w r s) := by
    simp only [eval13, eval13', Zsqrtd.lift_apply_apply]
    push_cast
    ring
  have hval : ((2*(w r s).re : ℤ) : ZMod 13) = 12^(r+1)*9^(s+1) := by
    rw [he]
    simp only [w, map_mul, map_pow]
    rw [show eval13 z7 = 12 from by decide, show eval13 z13 = 9 from by decide,
      show eval13' z13 = 0 from by decide]
    simp
  intro h
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rw [hval] at hz
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)) hz

def tuple (r s : ℕ) : Fin 4 → ℤ :=
  ![2*(w r s).re, (w r s).re+3*(w r s).im,
    (w r s).re-3*(w r s).im, q r s]

lemma tuple_sum_int (r s : ℕ) : ∑ i, tuple r s i^4 = 19*(q r s : ℤ)^4 := by
  have he : (2*(w r s).re)^4 + ((w r s).re+3*(w r s).im)^4 +
      ((w r s).re-3*(w r s).im)^4 =
      18*((w r s).re^2+3*(w r s).im^2)^2 := by ring
  simp only [tuple, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [← add_assoc, ← add_assoc, he, norm_w]
  ring

lemma tuple_sum (r s : ℕ) : ∑ i, (tuple r s i).natAbs^4 = 19*(q r s)^4 := by
  apply Int.ofNat_inj.mp
  push_cast
  simp only [(by decide : Even 4).pow_abs]
  exact tuple_sum_int r s

lemma first_value7 (r s a b : ℕ) :
    padicValNat 7 ((tuple r s 0).natAbs * (7^a*13^b)) = a := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hn : ¬ 7 ∣ (tuple r s 0).natAbs := by
    rw [← Int.natCast_dvd]
    exact first_not_dvd7 r s
  have hz : (tuple r s 0).natAbs ≠ 0 := by
    intro h; exact hn (h ▸ dvd_zero _)
  rw [padicValNat.mul hz (by positivity), padicValNat.eq_zero_of_not_dvd hn,
    padicValNat_mul_pow_left a b (by decide), zero_add]

lemma first_value13 (r s a b : ℕ) :
    padicValNat 13 ((tuple r s 0).natAbs * (7^a*13^b)) = b := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hn : ¬ 13 ∣ (tuple r s 0).natAbs := by
    rw [← Int.natCast_dvd]
    exact first_not_dvd13 r s
  have hz : (tuple r s 0).natAbs ≠ 0 := by
    intro h; exact hn (h ▸ dvd_zero _)
  rw [padicValNat.mul hz (by positivity), padicValNat.eq_zero_of_not_dvd hn,
    padicValNat_mul_pow_right a b (by decide), zero_add]

lemma q_scaled (r s t : ℕ) (hr : r ≤ t) (hs : s ≤ t) :
    q r s * (7^(t-r)*13^(t-s)) = 91^(t+1) := by
  have he7 : r+1+(t-r) = t+1 := by omega
  have he13 : s+1+(t-s) = t+1 := by omega
  calc
    q r s * (7^(t-r)*13^(t-s)) =
        (7^(r+1)*7^(t-r))*(13^(s+1)*13^(t-s)) := by unfold q; ring
    _ = 7^(t+1)*13^(t+1) := by rw [← pow_add, ← pow_add, he7, he13]
    _ = 91^(t+1) := by rw [← mul_pow]; norm_num

/-- Combining the independent norm factors 7 and 13 gives quadratically
many representations in the logarithm of the target. -/
theorem count_lower (t : ℕ) :
    (t+1)^2 ≤ representationCount 4 (19*91^(4*(t+1))) := by
  let f : Fin (t+1) × Fin (t+1) → Fin 4 → ℕ :=
    fun a i ↦ (tuple a.1 a.2 i).natAbs * (7^(t-a.1.val)*13^(t-a.2.val))
  have hf : Function.Injective f := by
    intro a b h
    have hv7 := congrArg (padicValNat 7) (congrFun h 0)
    have hv13 := congrArg (padicValNat 13) (congrFun h 0)
    change padicValNat 7 ((tuple a.1 a.2 0).natAbs * (7^(t-a.1.val)*13^(t-a.2.val))) =
      padicValNat 7 ((tuple b.1 b.2 0).natAbs * (7^(t-b.1.val)*13^(t-b.2.val))) at hv7
    change padicValNat 13 ((tuple a.1 a.2 0).natAbs * (7^(t-a.1.val)*13^(t-a.2.val))) =
      padicValNat 13 ((tuple b.1 b.2 0).natAbs * (7^(t-b.1.val)*13^(t-b.2.val))) at hv13
    rw [first_value7, first_value7] at hv7
    rw [first_value13, first_value13] at hv13
    have ha1 := a.1.isLt
    have ha2 := a.2.isLt
    have hb1 := b.1.isLt
    have hb2 := b.2.isLt
    apply Prod.ext <;> apply Fin.ext <;> omega
  have hs : ∀ a, ∑ i, f a i^4 = 19*91^(4*(t+1)) := by
    intro a
    simp only [f, mul_pow, ← Finset.sum_mul, tuple_sum]
    rw [mul_assoc, ← mul_pow, ← mul_pow,
      q_scaled a.1 a.2 t (by have := a.1.isLt; omega)
        (by have := a.2.isLt; omega), ← pow_mul]
    congr 2
    omega
  have hc := count_ge_of_family 4 (19*91^(4*(t+1))) (by decide) f hf hs
  simpa [pow_two] using hc

theorem logarithmic_squared_growth :
    {n : ℕ | (Real.log (n : ℝ)/400)^2 < representationCount 4 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ ↦ 19*91^(4*(t+1)))
  · intro t u h
    have hp : 91^(4*(t+1)) = 91^(4*(u+1)) := Nat.eq_of_mul_eq_mul_left (by decide) h
    have he := Nat.pow_right_injective (by decide : 2 ≤ 91) hp
    omega
  · intro t
    change (Real.log ((19*91^(4*(t+1)) : ℕ) : ℝ)/400)^2 < _
    have hl : Real.log ((19*91^(4*(t+1)) : ℕ) : ℝ) < 400*((t : ℝ)+1) := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      have h91 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 91)
      have h19 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 19)
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith
    have hnonneg : 0 ≤ Real.log ((19*91^(4*(t+1)) : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 19*91^(4*(t+1)) from by
        have : 0 < 19*91^(4*(t+1)) := by positivity
        omega)
    have hsq : (Real.log ((19*91^(4*(t+1)) : ℕ) : ℝ)/400)^2 < ((t : ℝ)+1)^2 := by
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith [sq_nonneg (Real.log ((19*91^(4*(t+1)) : ℕ) : ℝ)/400 - ((t : ℝ)+1))]
    have hc : ((t : ℝ)+1)^2 ≤ representationCount 4 (19*91^(4*(t+1))) := by
      exact_mod_cast count_lower t
    exact hsq.trans_le hc

end Quartic.TwoPrimes

namespace Quartic.Multi

lemma pval_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (hf a (by simp))
        (Finset.prod_ne_zero_iff.mpr (fun i hi ↦ hf i (by simp [hi]))),
      ih (fun i hi ↦ hf i (by simp [hi]))]

def W {d : ℕ} (z : Fin d → Zsqrtd (-3)) (r : Fin d → ℕ) : Zsqrtd (-3) :=
  ∏ i, z i^(r i+1)

def Q {d : ℕ} (q : Fin d → ℕ) (r : Fin d → ℕ) : ℕ := ∏ i, q i^(r i+1)

def tuple (z : Zsqrtd (-3)) (q : ℕ) : Fin 4 → ℤ :=
  ![2*z.re, z.re+3*z.im, z.re-3*z.im, q]

lemma tuple_sum (z : Zsqrtd (-3)) (q : ℕ) (hn : z.norm = (q : ℤ)^2) :
    ∑ i, (tuple z q i).natAbs^4 = 19*q^4 := by
  have hnorm : z.re^2+3*z.im^2 = (q : ℤ)^2 := by
    simpa [Zsqrtd.norm, sub_eq_add_neg, pow_two, mul_assoc] using hn
  have he : (2*z.re)^4 + (z.re+3*z.im)^4 + (z.re-3*z.im)^4 =
      18*(z.re^2+3*z.im^2)^2 := by ring
  apply Int.ofNat_inj.mp
  push_cast
  simp only [(by decide : Even 4).pow_abs, tuple, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [← add_assoc, ← add_assoc, he, hnorm]
  ring

lemma W_norm {d : ℕ} (z : Fin d → Zsqrtd (-3)) (q : Fin d → ℕ)
    (hz : ∀ i, (z i).norm = (q i : ℤ)^2) (r : Fin d → ℕ) :
    (W z r).norm = (Q q r : ℤ)^2 := by
  change (Zsqrtd.normMonoidHom (d := -3)) (∏ i, z i^(r i+1)) = _
  rw [map_prod]
  simp only [map_pow]
  change (∏ i, (z i).norm^(r i+1)) = _
  simp only [hz, Q, Nat.cast_prod, Nat.cast_pow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

lemma Q_scale {d : ℕ} (q : Fin d → ℕ) (r : Fin d → ℕ) (t : ℕ)
    (hr : ∀ i, r i ≤ t) :
    Q q r * (∏ i, q i^(t-r i)) = (∏ i, q i)^(t+1) := by
  rw [Q, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add]
  congr 1
  have := hr i
  omega

lemma scale_value {d : ℕ} (q p : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (hp : ∀ i, (p i).Prime) (hdiff : ∀ i j, j ≠ i → ¬ p i ∣ q j)
    (r : Fin d → ℕ) (t : ℕ) (i : Fin d) :
    padicValNat (p i) (∏ j, q j^(t-r j)) = (t-r i)*padicValNat (p i) (q i) := by
  letI : Fact (p i).Prime := ⟨hp i⟩
  rw [pval_prod _ _ _ (fun j _ ↦ pow_ne_zero _ (hq j).ne')]
  simp only [padicValNat.pow _ (hq _).ne']
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [padicValNat.eq_zero_of_not_dvd (hdiff i j hji), mul_zero]
  · simp

/-- A finite collection of independent norm factors gives a product family. -/
theorem count_of_factors {d : ℕ} (z : Fin d → Zsqrtd (-3)) (q p : Fin d → ℕ)
    (hq : ∀ i, 0 < q i) (hp : ∀ i, (p i).Prime) (hdiv : ∀ i, p i ∣ q i)
    (hdiff : ∀ i j, j ≠ i → ¬ p i ∣ q j)
    (hz : ∀ i, (z i).norm = (q i : ℤ)^2)
    (htrace : ∀ (r : Fin d → ℕ) i, ¬ (p i : ℤ) ∣ 2*(W z r).re) (t : ℕ) :
    (t+1)^d ≤ representationCount 4 (19*(∏ i, q i)^(4*(t+1))) := by
  let f : (Fin d → Fin (t+1)) → Fin 4 → ℕ := fun r i ↦
    (tuple (W z (fun j ↦ r j)) (Q q (fun j ↦ r j)) i).natAbs *
      (∏ j, q j^(t-(r j).val))
  have hval : ∀ (r : Fin d → Fin (t+1)) (i : Fin d),
      padicValNat (p i) (f r 0) = (t-(r i).val)*padicValNat (p i) (q i) := by
    intro r i
    letI : Fact (p i).Prime := ⟨hp i⟩
    have hn : ¬ p i ∣ (2*(W z (fun j ↦ r j)).re).natAbs := by
      rw [← Int.natCast_dvd]
      exact htrace _ i
    have hne : (2*(W z (fun j ↦ r j)).re).natAbs ≠ 0 := by
      intro h; exact hn (h ▸ dvd_zero _)
    change padicValNat (p i) ((2*(W z (fun j ↦ r j)).re).natAbs * _) = _
    rw [padicValNat.mul hne (Finset.prod_ne_zero_iff.mpr
      (fun j _ ↦ pow_ne_zero _ (hq j).ne')),
      padicValNat.eq_zero_of_not_dvd hn, zero_add, scale_value q p hq hp hdiff]
  have hf : Function.Injective f := by
    intro r s he
    funext i
    letI : Fact (p i).Prime := ⟨hp i⟩
    have hv := congrArg (padicValNat (p i)) (congrFun he 0)
    rw [hval, hval] at hv
    have hpos : 0 < padicValNat (p i) (q i) :=
      one_le_padicValNat_of_dvd (hq i).ne' (hdiv i)
    have heq := Nat.eq_of_mul_eq_mul_right hpos hv
    apply Fin.ext
    have hr := (r i).isLt
    have hs := (s i).isLt
    omega
  have hs : ∀ r, ∑ i, f r i^4 = 19*(∏ i, q i)^(4*(t+1)) := by
    intro r
    calc
      ∑ i, f r i^4 = (∑ i, (tuple (W z (fun j ↦ r j)) (Q q (fun j ↦ r j)) i).natAbs^4) *
          (∏ j, q j^(t-(r j).val))^4 := by
        simp only [f, mul_pow, Finset.sum_mul]
      _ = 19*(Q q (fun j ↦ r j) * (∏ j, q j^(t-(r j).val)))^4 := by
        rw [tuple_sum _ _ (W_norm z q hz _)]
        ring
      _ = 19*(∏ i, q i)^(4*(t+1)) := by
        rw [Q_scale q _ t (fun j ↦ by have := (r j).isLt; omega), ← pow_mul,
          Nat.mul_comm (t+1) 4]
  simpa using count_ge_of_family 4 _ (by decide) f hf hs

def N (b : ℕ) : ℕ := 1+12*b^2

def base (b : ℕ) : Zsqrtd (-3) := (⟨1, 2*b⟩ : Zsqrtd (-3))^2

lemma base_norm (b : ℕ) : (base b).norm = (N b : ℤ)^2 := by
  change (Zsqrtd.normMonoidHom (d := -3)) ((⟨1, 2*b⟩ : Zsqrtd (-3))^2) = _
  rw [map_pow]
  change (⟨1, 2*b⟩ : Zsqrtd (-3)).norm^2 = _
  simp [Zsqrtd.norm, N]
  ring

lemma base_trace {d : ℕ} (b : Fin d → ℕ) (p : ℕ) (hp : p.Prime)
    (i : Fin d) (hdiv : p ∣ N (b i))
    (hdiff : ∀ j, j ≠ i → ¬ p ∣ N (b j)) (r : Fin d → ℕ) :
    ¬ (p : ℤ) ∣ 2*(W (fun j ↦ base (b j)) r).re := by
  letI : Fact p.Prime := ⟨hp⟩
  let v : ZMod p := 2*(b i : ZMod p)
  have hN : (N (b i) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hrel : 1+3*v^2 = 0 := by
    dsimp [v, N] at *
    push_cast at hN
    linear_combination hN
  have hv : v ≠ 0 := by intro he; simp [he] at hrel
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hz : v = 0 := by simp [v, he]
    exact hv hz
  have hs : v⁻¹*v⁻¹ = (-3 : ℤ) := by
    push_cast
    field_simp
    linear_combination hrel
  let φ : Zsqrtd (-3) →+* ZMod p := Zsqrtd.lift ⟨v⁻¹, hs⟩
  let ψ : Zsqrtd (-3) →+* ZMod p := Zsqrtd.lift ⟨-v⁻¹, by simpa using hs⟩
  have hφi : φ (base (b i)) = (2 : ZMod p)^2 := by
    rw [base, map_pow]
    simp only [φ, Zsqrtd.lift_apply_apply]
    push_cast
    change (1+v*v⁻¹)^2 = 2^2
    rw [mul_inv_cancel₀ hv]
    norm_num
  have hψi : ψ (base (b i)) = 0 := by
    rw [base, map_pow]
    simp only [ψ, Zsqrtd.lift_apply_apply]
    push_cast
    change (1+v*(-v⁻¹))^2 = 0
    simp [hv]
  have hnorm : ∀ z : Zsqrtd (-3), φ z * ψ z = (z.norm : ZMod p) := by
    intro z
    simp only [φ, ψ, Zsqrtd.lift_apply_apply, Zsqrtd.norm]
    push_cast
    linear_combination -(z.im : ZMod p)^2 * hs
  have hφ : ∀ j, φ (base (b j)) ≠ 0 := by
    intro j
    by_cases he : j = i
    · subst j
      rw [hφi]
      exact pow_ne_zero _ h2
    · have hq : (N (b j) : ZMod p) ≠ 0 :=
        (ZMod.natCast_eq_zero_iff _ _).not.mpr (hdiff j he)
      intro hz
      have hn := hnorm (base (b j))
      rw [hz, zero_mul, base_norm, Int.cast_pow] at hn
      push_cast at hn
      exact (pow_ne_zero 2 hq) hn.symm
  have hprodφ : φ (W (fun j ↦ base (b j)) r) ≠ 0 := by
    simp only [W, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ ↦ pow_ne_zero _ (hφ j))
  have hprodψ : ψ (W (fun j ↦ base (b j)) r) = 0 := by
    simp only [W, map_prod, map_pow]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hψi]
  have hsum : ((2*(W (fun j ↦ base (b j)) r).re : ℤ) : ZMod p) =
      φ (W (fun j ↦ base (b j)) r) + ψ (W (fun j ↦ base (b j)) r) := by
    simp only [φ, ψ, Zsqrtd.lift_apply_apply]
    push_cast
    ring
  intro he
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr he
  rw [hsum, hprodψ, add_zero] at hz
  exact hprodφ hz

def denominator : ℕ → ℕ
  | 0 => 1
  | n+1 => denominator n * N (denominator n)

lemma denominator_pos (n : ℕ) : 0 < denominator n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [denominator, N]; positivity

lemma N_denominator_gt_one (n : ℕ) : 1 < N (denominator n) := by
  have h := denominator_pos n
  dsimp [N]
  nlinarith

lemma N_dvd_denominator (i j : ℕ) (hij : i < j) :
    N (denominator i) ∣ denominator j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [denominator]
    by_cases he : i = j
    · subst i
      exact dvd_mul_left _ _
    · exact (ih (by omega)).trans (dvd_mul_right _ _)

lemma N_coprime_of_lt (i j : ℕ) (hij : i < j) :
    (N (denominator i)).Coprime (N (denominator j)) := by
  have hd := N_dvd_denominator i j hij
  have hd2 : N (denominator i) ∣ 12*(denominator j)^2 := by
    simpa [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd (denominator j)) 12
  change (N (denominator i)).Coprime (1+12*(denominator j)^2)
  rw [Nat.coprime_add_iff_left hd2]
  exact Nat.coprime_one_right _

lemma N_pairwise_coprime (i j : ℕ) (hij : i ≠ j) :
    (N (denominator i)).Coprime (N (denominator j)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact N_coprime_of_lt i j h
  · exact (N_coprime_of_lt j i h).symm

def prime (i : ℕ) : ℕ := (N (denominator i)).minFac

lemma prime_prime (i : ℕ) : (prime i).Prime :=
  Nat.minFac_prime (N_denominator_gt_one i).ne'

lemma prime_dvd (i : ℕ) : prime i ∣ N (denominator i) := Nat.minFac_dvd _

lemma prime_not_dvd (i j : ℕ) (hji : j ≠ i) : ¬ prime i ∣ N (denominator j) := by
  intro h
  exact (prime_prime i).ne_one
    (Nat.eq_one_of_dvd_coprimes (N_pairwise_coprime i j hji.symm) (prime_dvd i) h)

/-- For every positive integer d there is a fixed exponential sequence of
quartic targets with at least (t+1)^d representations. -/
theorem arbitrarily_many_factors (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ t : ℕ,
      (t+1)^d ≤ representationCount 4 (19*C^(4*(t+1))) := by
  let q : Fin d → ℕ := fun i ↦ N (denominator i)
  let z : Fin d → Zsqrtd (-3) := fun i ↦ base (denominator i)
  let p : Fin d → ℕ := fun i ↦ prime i
  refine ⟨∏ i, q i, ?_, ?_⟩
  · have hfirst : 2 ≤ q ⟨0, hd⟩ := N_denominator_gt_one 0
    have hle : q ⟨0, hd⟩ ≤ ∏ i, q i := by
      apply Finset.single_le_prod' (f := q) (fun i _ ↦ ?_) (Finset.mem_univ _)
      exact (N_denominator_gt_one i).le
    exact hfirst.trans hle
  · intro t
    apply count_of_factors z q p
    · intro i; exact lt_trans Nat.zero_lt_one (N_denominator_gt_one i)
    · intro i; exact prime_prime i
    · intro i; exact prime_dvd i
    · intro i j hji
      apply prime_not_dvd i j
      exact fun he ↦ hji (Fin.ext he)
    · intro i; exact base_norm (denominator i)
    · intro r i
      apply base_trace (fun j : Fin d ↦ denominator j) (prime i) (prime_prime i) i (prime_dvd i)
      intro j hji
      exact prime_not_dvd i j (fun he ↦ hji (Fin.ext he))

/-- The quartic representation count exceeds every fixed integer power of
log n infinitely often. This still does not assert positive-power growth in n. -/
theorem every_logarithmic_power (d : ℕ) :
    {n : ℕ | (Real.log (n : ℝ))^d < representationCount 4 n}.Infinite := by
  obtain ⟨C, hC, hcount⟩ := arbitrarily_many_factors (d+1) (by omega)
  let K : ℕ := 20+4*C
  apply Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ ↦ 19*C^(4*(m+K^d+1)))
  · intro m m' he
    have hp := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 19) he
    have hexp := Nat.pow_right_injective hC hp
    omega
  · intro m
    let t := m+K^d
    change (Real.log ((19*C^(4*(t+1)) : ℕ) : ℝ))^d < _
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hC0 : 0 < C := by omega
    have hlog : Real.log ((19*C^(4*(t+1)) : ℕ) : ℝ) ≤ (K : ℝ)*((t : ℝ)+1) := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      have hlogC := Real.log_le_self (Nat.cast_nonneg C)
      have hlog19 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 19)
      have hKeq : (K : ℝ) = 20+4*(C : ℝ) := by simp [K]
      rw [hKeq]
      nlinarith
    have hnonneg : 0 ≤ Real.log ((19*C^(4*(t+1)) : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 19*C^(4*(t+1)) from by
        have : 0 < 19*C^(4*(t+1)) := by positivity
        omega)
    have hp := pow_le_pow_left₀ hnonneg hlog d
    rw [mul_pow] at hp
    have hK : (K : ℝ)^d < (t : ℝ)+1 := by
      exact_mod_cast (show K^d < t+1 from by dsimp [t]; omega)
    have hstrict : (K : ℝ)^d*((t : ℝ)+1)^d < ((t : ℝ)+1)^(d+1) := by
      calc
        (K : ℝ)^d*((t : ℝ)+1)^d < ((t : ℝ)+1)*((t : ℝ)+1)^d :=
          mul_lt_mul_of_pos_right hK (pow_pos (by positivity) _)
        _ = ((t : ℝ)+1)^(d+1) := by rw [pow_succ]; ring
    have hc : ((t : ℝ)+1)^(d+1) ≤ representationCount 4 (19*C^(4*(t+1))) := by
      exact_mod_cast hcount t
    exact (hp.trans_lt hstrict).trans_le hc

lemma denominator_prod (d : ℕ) : (∏ i : Fin d, N (denominator i)) = denominator d := by
  induction d with
  | zero => simp [denominator]
  | succ d ih =>
    rw [Fin.prod_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last, denominator] using
      congrArg (fun a ↦ a * N (denominator d)) ih

lemma denominator_upper (d : ℕ) : denominator d ≤ 13^(3^d-1) := by
  induction d with
  | zero => norm_num [denominator]
  | succ d ih =>
    have hp := denominator_pos d
    have h3 : 1 ≤ 3^d := Nat.one_le_pow _ _ (by decide)
    calc
      denominator (d+1) = denominator d*(1+12*(denominator d)^2) := rfl
      _ ≤ 13*(denominator d)^3 := by nlinarith
      _ ≤ 13*(13^(3^d-1))^3 := Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left ih 3)
      _ = 13^(3*(3^d-1)+1) := by
        rw [← pow_mul, Nat.mul_comm (3^d-1) 3, pow_succ]
        exact Nat.mul_comm _ _
      _ ≤ 13^(3^(d+1)-1) := by
        apply Nat.pow_le_pow_right (by decide)
        rw [pow_succ]
        omega

/-- An explicit form of the finite-factor lower bound, including d=0. -/
theorem denominator_count (d t : ℕ) :
    (t+1)^d ≤ representationCount 4 (19*(denominator d)^(4*(t+1))) := by
  rw [← denominator_prod d]
  apply count_of_factors (fun i : Fin d ↦ base (denominator i))
    (fun i ↦ N (denominator i)) (fun i ↦ prime i)
  · intro i; exact lt_trans Nat.zero_lt_one (N_denominator_gt_one i)
  · intro i; exact prime_prime i
  · intro i; exact prime_dvd i
  · intro i j hji
    exact prime_not_dvd i j (fun he ↦ hji (Fin.ext he))
  · intro i; exact base_norm (denominator i)
  · intro r i
    apply base_trace (fun j : Fin d ↦ denominator j) (prime i) (prime_prime i) i (prime_dvd i)
    intro j hji
    exact prime_not_dvd i j (fun he ↦ hji (Fin.ext he))

/-- A quantitative family with super-polynomial growth in its logarithmic
height parameter, but not with positive-power growth in the target itself. -/
theorem quantitative_family (d : ℕ) :
    ∃ n : ℕ, n ≤ 19*13^(8*9^d) ∧ 3^(d^2) ≤ representationCount 4 n := by
  refine ⟨19*(denominator d)^(4*(3^d+1)), ?_, ?_⟩
  · apply Nat.mul_le_mul_left 19
    calc
      (denominator d)^(4*(3^d+1)) ≤ (13^(3^d-1))^(4*(3^d+1)) :=
        Nat.pow_le_pow_left (denominator_upper d) _
      _ = 13^((3^d-1)*(4*(3^d+1))) := (pow_mul 13 (3^d-1) (4*(3^d+1))).symm
      _ ≤ 13^(8*9^d) := by
        apply Nat.pow_le_pow_right (by decide)
        have h3 : 1 ≤ 3^d := Nat.one_le_pow _ _ (by decide)
        have he : 9^d = (3^d)^2 := by rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num
        rw [he]
        nlinarith [Nat.sub_add_cancel h3]
  · have hcount := denominator_count d (3^d)
    apply le_trans ?_ hcount
    calc
      3^(d^2) = (3^d)^d := by rw [← pow_mul, pow_two]
      _ ≤ (3^d+1)^d := Nat.pow_le_pow_left (by omega) d

end Quartic.Multi

namespace GaussianUpper
open UniqueFactorizationMonoid

noncomputable instance : NormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.normalizationMonoid

def normN : GaussianInt →* ℕ := Int.natAbsHom.toMonoidHom.comp Zsqrtd.normMonoidHom

lemma normN_def (z : GaussianInt) : normN z = z.norm.natAbs := rfl

lemma normN_zero_iff (z : GaussianInt) : normN z = 0 ↔ z = 0 := by
  simp only [normN_def, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

lemma normN_one_iff (z : GaussianInt) : normN z = 1 ↔ IsUnit z := Zsqrtd.norm_eq_one_iff

lemma normN_associated {z w : GaussianInt} (h : Associated z w) : normN z = normN w :=
  associated_iff_eq.mp (h.map normN)

def box (B : ℕ) : Finset GaussianInt :=
  ((Finset.Icc (-(B : ℤ)) B) ×ˢ (Finset.Icc (-(B : ℤ)) B)).image
    (fun p : ℤ × ℤ ↦ (⟨p.1, p.2⟩ : GaussianInt))

lemma mem_box (z : GaussianInt) (B : ℕ) (hz : normN z ≤ B) : z ∈ box B := by
  have hr : z.re.natAbs ≤ B := by
    calc
      z.re.natAbs ≤ z.re.natAbs^2 := Nat.le_pow (by decide)
      _ ≤ z.re.natAbs*z.re.natAbs + z.im.natAbs*z.im.natAbs := by
        rw [pow_two]; omega
      _ = normN z := (GaussianInt.natAbs_norm_eq z).symm
      _ ≤ B := hz
  have hi : z.im.natAbs ≤ B := by
    calc
      z.im.natAbs ≤ z.im.natAbs^2 := Nat.le_pow (by decide)
      _ ≤ z.re.natAbs*z.re.natAbs + z.im.natAbs*z.im.natAbs := by
        rw [pow_two]; omega
      _ = normN z := (GaussianInt.natAbs_norm_eq z).symm
      _ ≤ B := hz
  have hr' : |z.re| ≤ (B : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hr
  have hi' : |z.im| ≤ (B : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hi
  apply Finset.mem_image.mpr
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hr'),
      Finset.mem_Icc.mpr (abs_le.mp hi')⟩
  · rfl

noncomputable instance unitsFintype : Fintype GaussianIntˣ := by
  let f : GaussianIntˣ → (box 1) := fun u ↦
    ⟨u, mem_box u 1 (le_of_eq ((normN_one_iff u).mpr u.isUnit))⟩
  apply Fintype.ofInjective f
  intro u v h
  apply Units.ext
  exact congrArg Subtype.val h

lemma divisor_card (a : GaussianInt) (ha : a ≠ 0) (s : Finset GaussianInt)
    (hs : ∀ z ∈ s, z ∣ a) :
    s.card ≤ Fintype.card GaussianIntˣ * ∏ p ∈ (normalizedFactors a).toFinset,
      ((normalizedFactors a).count p+1) := by
  classical
  let S := (Finset.Iic (normalizedFactors a)) ×ˢ (Finset.univ : Finset GaussianIntˣ)
  let f : Multiset GaussianInt × GaussianIntˣ → GaussianInt := fun p ↦ p.1.prod*p.2
  have hsurj : Set.SurjOn f ↑S ↑s := by
    intro z hz
    have hd := hs z hz
    have hz0 : z ≠ 0 := ne_zero_of_dvd_ne_zero ha hd
    obtain ⟨u, hu⟩ := prod_normalizedFactors hz0
    refine ⟨(normalizedFactors z, u), ?_, hu⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Iic.mpr ?_, Finset.mem_univ _⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hz0 ha).mp hd
  have hc := Finset.card_le_card_of_surjOn f hsurj
  simpa [S, Finset.card_product, Multiset.card_Iic, Nat.mul_comm] using hc

def localConstant (k : ℕ) : ℕ := k.factorial*2^k

def factorConstant (k : ℕ) : ℕ := (localConstant k)^(box (2^k)).card

noncomputable def totalConstant (k : ℕ) : ℕ :=
  (Fintype.card GaussianIntˣ)^k * factorConstant k

lemma localConstant_pos (k : ℕ) : 0 < localConstant k := by
  unfold localConstant
  positivity

lemma totalConstant_pos (k : ℕ) : 0 < totalConstant k := by
  have hu : 0 < Fintype.card GaussianIntˣ := Fintype.card_pos
  have hl := localConstant_pos k
  unfold totalConstant factorConstant
  positivity

lemma linear_power_le_exp (a k : ℕ) : (a+1)^k ≤ localConstant k * 2^a := by
  calc
    (a+1)^k ≤ (a+1).ascFactorial k := Nat.pow_succ_le_ascFactorial _ _
    _ = k.factorial * (a+k).choose k := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ k.factorial * 2^(a+k) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = localConstant k * 2^a := by unfold localConstant; rw [pow_add]; ring

lemma local_factor_bound (p a k : ℕ) (hp : 2 ≤ p) :
    (a+1)^k ≤ (if p < 2^k then localConstant k else 1) * p^a := by
  by_cases h : p < 2^k
  · rw [if_pos h]
    exact (linear_power_le_exp a k).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp _))
  · rw [if_neg h, one_mul]
    have he : a+1 ≤ 2^a := Nat.lt_two_pow_self
    calc
      (a+1)^k ≤ (2^a)^k := Nat.pow_le_pow_left he k
      _ = (2^k)^a := by rw [← pow_mul, ← pow_mul, Nat.mul_comm a k]
      _ ≤ p^a := Nat.pow_le_pow_left (by omega) a

lemma factor_power_bound (a : GaussianInt) (k : ℕ) (ha : a ≠ 0) :
    (∏ p ∈ (normalizedFactors a).toFinset, ((normalizedFactors a).count p+1))^k ≤
      factorConstant k * normN a := by
  classical
  have hprod : ∏ p ∈ (normalizedFactors a).toFinset, (normN p)^((normalizedFactors a).count p) =
      normN a := by
    calc
      _ = ((normalizedFactors a).map normN).prod :=
        (Finset.prod_multiset_map_count (normalizedFactors a) normN).symm
      _ = normN (normalizedFactors a).prod := (map_multiset_prod normN _).symm
      _ = normN a := normN_associated (prod_normalizedFactors ha)
  have hc : (∏ p ∈ (normalizedFactors a).toFinset,
      if normN p < 2^k then localConstant k else 1) ≤ factorConstant k := by
    rw [← Finset.prod_filter, Finset.prod_const]
    apply Nat.pow_le_pow_right (localConstant_pos k)
    apply Finset.card_le_card
    intro z hz
    exact mem_box z _ (Finset.mem_filter.mp hz).2.le
  calc
    _ = ∏ p ∈ (normalizedFactors a).toFinset, ((normalizedFactors a).count p+1)^k := by
      rw [Finset.prod_pow]
    _ ≤ ∏ p ∈ (normalizedFactors a).toFinset,
        (if normN p < 2^k then localConstant k else 1)*(normN p)^((normalizedFactors a).count p) := by
      apply Finset.prod_le_prod'
      intro p hp
      have hprime := prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
      have hn0 : normN p ≠ 0 := (normN_zero_iff p).not.mpr hprime.ne_zero
      have hn1 : normN p ≠ 1 := (normN_one_iff p).not.mpr hprime.not_unit
      exact local_factor_bound _ _ _ (by omega)
    _ = (∏ p ∈ (normalizedFactors a).toFinset,
        if normN p < 2^k then localConstant k else 1)*normN a := by
      rw [Finset.prod_mul_distrib, hprod]
    _ ≤ factorConstant k*normN a := Nat.mul_le_mul_right _ hc

lemma card_power_bound (a : GaussianInt) (ha : a ≠ 0) (s : Finset GaussianInt)
    (hs : ∀ z ∈ s, z ∣ a) (k : ℕ) :
    s.card^k ≤ totalConstant k*normN a := by
  have hc := Nat.pow_le_pow_left (divisor_card a ha s hs) k
  rw [mul_pow] at hc
  calc
    s.card^k ≤ (Fintype.card GaussianIntˣ)^k *
        (∏ p ∈ (normalizedFactors a).toFinset, ((normalizedFactors a).count p+1))^k := hc
    _ ≤ (Fintype.card GaussianIntˣ)^k * (factorConstant k*normN a) :=
      Nat.mul_le_mul_left _ (factor_power_bound a k ha)
    _ = totalConstant k*normN a := by unfold totalConstant; ring

/-- Uniform subpolynomial bounds for finite sets of Gaussian divisors. -/
theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (a : GaussianInt), a ≠ 0 → ∀ s : Finset GaussianInt,
      (∀ z ∈ s, z ∣ a) → (s.card : ℝ) ≤ C*(normN a : ℝ)^ε := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hk0 : (0 : ℝ) < k+1 := by positivity
  have hke : 1 ≤ ε*((k : ℝ)+1) := le_of_lt ((div_lt_iff₀ hk0).mp hk)
  let C : ℕ := totalConstant (k+1)
  have hC0 : 0 < C := totalConstant_pos _
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC0
  refine ⟨C, by exact_mod_cast hC0, ?_⟩
  intro a ha s hs
  have hN0 : 0 < normN a := Nat.pos_of_ne_zero ((normN_zero_iff a).not.mpr ha)
  have hN1 : (1 : ℝ) ≤ normN a := by exact_mod_cast hN0
  have hNn : (0 : ℝ) ≤ normN a := Nat.cast_nonneg _
  have hCpow : (C : ℝ) ≤ (C : ℝ)^(k+1) := le_self_pow₀ hC1 (by omega)
  have hNpow : (normN a : ℝ) ≤ (normN a : ℝ)^(ε*((k : ℝ)+1)) := by
    convert Real.rpow_le_rpow_of_exponent_le hN1 hke using 1
    simp
  have hb : (s.card : ℝ)^(k+1) ≤ (C : ℝ)*normN a := by
    exact_mod_cast card_power_bound a ha s hs (k+1)
  apply le_of_pow_le_pow_left₀ (n := k+1) (by omega) (by positivity)
  calc
    (s.card : ℝ)^(k+1) ≤ (C : ℝ)*normN a := hb
    _ ≤ (C : ℝ)^(k+1) * (normN a : ℝ)^(ε*((k : ℝ)+1)) :=
      mul_le_mul hCpow hNpow hNn (by positivity)
    _ = ((C : ℝ)*(normN a : ℝ)^ε)^(k+1) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hNn]
      push_cast
      rfl

def fourthPair (u : ℕ × ℕ) : GaussianInt := ⟨(u.1 : ℤ)^2, (u.2 : ℤ)^2⟩

lemma fourthPair_injective : Function.Injective fourthPair := by
  intro u v h
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  change (u.1 : ℤ)^2 = (v.1 : ℤ)^2 at hr
  change (u.2 : ℤ)^2 = (v.2 : ℤ)^2 at hi
  have hr' : u.1^2 = v.1^2 := by exact_mod_cast hr
  have hi' : u.2^2 = v.2^2 := by exact_mod_cast hi
  apply Prod.ext <;> nlinarith

lemma fourthPair_norm (u : ℕ × ℕ) : (fourthPair u).norm = ((u.1^4+u.2^4 : ℕ) : ℤ) := by
  simp [fourthPair, Zsqrtd.norm]
  ring

lemma fourthPair_dvd (u : ℕ × ℕ) (m : ℕ) (hu : u.1^4+u.2^4=m) :
    fourthPair u ∣ (m : GaussianInt) := by
  refine ⟨star (fourthPair u), ?_⟩
  have h := Zsqrtd.norm_eq_mul_conj (fourthPair u)
  simpa [fourthPair_norm, hu] using h

/-- Pairs of fourth powers admit a uniform subpolynomial counting bound. -/
theorem fourth_pair_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (m : ℕ) (s : Finset (ℕ × ℕ)),
      (∀ u ∈ s, u.1^4+u.2^4=m) → (s.card : ℝ) ≤ C*((m : ℝ)+1)^ε := by
  classical
  obtain ⟨C, hC, hb⟩ := divisor_bound (ε/2) (by linarith)
  refine ⟨max C 1, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro m s hs
  by_cases hm : m=0
  · subst m
    have hsub : s ⊆ {(0,0)} := by
      intro u hu
      have he := hs u hu
      have h1 : u.1^4=0 := by omega
      have h2 : u.2^4=0 := by omega
      simpa only [Finset.mem_singleton] using
        Prod.ext (eq_zero_of_pow_eq_zero h1) (eq_zero_of_pow_eq_zero h2)
    have hcard : s.card ≤ 1 := by simpa using Finset.card_le_card hsub
    have hreal : (s.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    simpa using hreal.trans (le_max_right C 1)
  · have hmG : (m : GaussianInt) ≠ 0 := by
      intro he
      have hr := congrArg Zsqrtd.re he
      apply hm
      simpa using hr
    have hdiv : ∀ z ∈ s.image fourthPair, z ∣ (m : GaussianInt) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact fourthPair_dvd u m (hs u hu)
    have hbound := hb (m : GaussianInt) hmG (s.image fourthPair) hdiv
    rw [Finset.card_image_of_injective _ fourthPair_injective] at hbound
    have hN : normN (m : GaussianInt) = m^2 := by
      simp [normN_def, Zsqrtd.norm, pow_two, Int.natAbs_mul]
    rw [hN] at hbound
    have he : (((m^2 : ℕ) : ℝ))^(ε/2) = (m : ℝ)^ε := by
      push_cast
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg m)]
      congr 1
      ring
    rw [he] at hbound
    calc
      (s.card : ℝ) ≤ C*(m : ℝ)^ε := hbound
      _ ≤ max C 1*((m : ℝ)+1)^ε :=
        mul_le_mul (le_max_left _ _)
          (Real.rpow_le_rpow (Nat.cast_nonneg m) (by linarith) hε.le)
          (Real.rpow_nonneg (Nat.cast_nonneg m) _) (by positivity)

end GaussianUpper

namespace Quartic.GlobalUpper
lemma coordinate_bound (n : ℕ) (a : Fin 4 → Fin (n+1))
    (ha : ∑ i, (a i : ℕ)^4 = n) (i : Fin 4) :
    (a i : ℕ) ≤ Nat.sqrt (Nat.sqrt n) := by
  have hp : (a i : ℕ)^4 ≤ n := by
    calc
      (a i : ℕ)^4 ≤ ∑ j, (a j : ℕ)^4 :=
        Finset.single_le_sum (f := fun j ↦ (a j : ℕ)^4)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      _ = n := ha
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  convert hp using 1 <;> ring

/-- A uniform upper bound for all quartic representations, not just the
norm families. The square-root loss prevents this from being a disproof. -/
theorem sqrt_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (representationCount 4 n : ℝ) ≤ C*((Nat.sqrt n : ℝ)+1)*((n : ℝ)+1)^ε := by
  classical
  obtain ⟨C, hC, hpair⟩ := GaussianUpper.fourth_pair_bound ε hε
  refine ⟨4*C, by positivity, ?_⟩
  intro n
  let S := (Finset.univ : Finset (Fin 4 → Fin (n+1))).filter
    (fun a ↦ ∑ i, (a i : ℕ)^4 = n)
  let front : (Fin 4 → Fin (n+1)) → ℕ × ℕ := fun a ↦ (a 0, a 1)
  let back : (Fin 4 → Fin (n+1)) → ℕ × ℕ := fun a ↦ (a 2, a 3)
  let B := Nat.sqrt (Nat.sqrt n)
  have hS : ∀ a ∈ S, ∑ i, (a i : ℕ)^4 = n := fun a ha ↦ (Finset.mem_filter.mp ha).2
  have hfront : (S.image front).card ≤ (B+1)^2 := by
    have hsub : S.image front ⊆ (Finset.range (B+1)) ×ˢ (Finset.range (B+1)) := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (coordinate_bound n a (hS a ha) 0)),
          Finset.mem_range.mpr (Nat.lt_succ_of_le (coordinate_bound n a (hS a ha) 1))⟩
    simpa [pow_two] using Finset.card_le_card hsub
  have hfiber : ∀ p : ℕ × ℕ,
      ((S.filter (fun a ↦ front a = p)).card : ℝ) ≤ C*((n : ℝ)+1)^ε := by
    intro p
    let T := S.filter (fun a ↦ front a = p)
    have hinj : Set.InjOn back ↑T := by
      intro a ha b hb he
      have hab : front a = front b := (Finset.mem_filter.mp ha).2.trans
        (Finset.mem_filter.mp hb).2.symm
      have h0 := congrArg Prod.fst hab
      have h1 := congrArg Prod.snd hab
      have h2 := congrArg Prod.fst he
      have h3 := congrArg Prod.snd he
      funext i
      fin_cases i
      · exact Fin.ext h0
      · exact Fin.ext h1
      · exact Fin.ext h2
      · exact Fin.ext h3
    have hs : ∀ u ∈ T.image back, u.1^4+u.2^4 = n-(p.1^4+p.2^4) := by
      intro u hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      have hsum := hS a (Finset.mem_filter.mp ha).1
      have hfp := (Finset.mem_filter.mp ha).2
      have h0 : (a 0 : ℕ) = p.1 := congrArg Prod.fst hfp
      have h1 : (a 1 : ℕ) = p.2 := congrArg Prod.snd hfp
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
      change (a 0 : ℕ)^4 + ((a 1 : ℕ)^4 + ((a 2 : ℕ)^4 + (a 3 : ℕ)^4)) = n at hsum
      rw [h0, h1] at hsum
      change (a 2 : ℕ)^4+(a 3 : ℕ)^4 = _
      omega
    have hc := hpair (n-(p.1^4+p.2^4)) (T.image back) hs
    rw [Finset.card_image_of_injOn hinj] at hc
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    exact_mod_cast (show n-(p.1^4+p.2^4)+1 ≤ n+1 from by omega)
  have hcard : (representationCount 4 n : ℝ) ≤ ((B+1 : ℕ) : ℝ)^2 * (C*((n : ℝ)+1)^ε) := by
    have he : S.card = ∑ p ∈ S.image front, (S.filter (fun a ↦ front a = p)).card :=
      Finset.card_eq_sum_card_image front S
    change (S.card : ℝ) ≤ _
    rw [he, Nat.cast_sum]
    calc
      ∑ p ∈ S.image front, ((S.filter (fun a ↦ front a = p)).card : ℝ) ≤
          ∑ _p ∈ S.image front, C*((n : ℝ)+1)^ε :=
        Finset.sum_le_sum (fun p _ ↦ hfiber p)
      _ = ((S.image front).card : ℝ)*(C*((n : ℝ)+1)^ε) := by simp
      _ ≤ ((B+1 : ℕ) : ℝ)^2 * (C*((n : ℝ)+1)^ε) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hfront
  have hB2 : B^2 ≤ Nat.sqrt n := by simpa [B, pow_two] using Nat.sqrt_le' (Nat.sqrt n)
  have hB1 : B ≤ B^2 := Nat.le_pow (by decide)
  have hB : (B+1)^2 ≤ 4*(Nat.sqrt n+1) := by nlinarith
  have hBR : ((B+1 : ℕ) : ℝ)^2 ≤ 4*((Nat.sqrt n : ℝ)+1) := by exact_mod_cast hB
  calc
    (representationCount 4 n : ℝ) ≤ ((B+1 : ℕ) : ℝ)^2 * (C*((n : ℝ)+1)^ε) := hcard
    _ ≤ (4*((Nat.sqrt n : ℝ)+1)) * (C*((n : ℝ)+1)^ε) :=
      mul_le_mul_of_nonneg_right hBR (by positivity)
    _ = (4*C)*((Nat.sqrt n : ℝ)+1)*((n : ℝ)+1)^ε := by ring

/-- A global polynomial upper bound, weaker than the uniform subpolynomial
bound that would disprove the conjecture. -/
theorem power_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (representationCount 4 n : ℝ) ≤ C*((n : ℝ)+1)^(1/2+ε) := by
  obtain ⟨C, hC, hb⟩ := sqrt_upper_bound ε hε
  refine ⟨2*C, by positivity, ?_⟩
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs0 := Real.sqrt_nonneg ((n : ℝ)+1)
  have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)+1)
  have hnat0 : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hnat2 : (Nat.sqrt n : ℝ)^2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hs1 : 1 ≤ Real.sqrt ((n : ℝ)+1) := by nlinarith
  have hsN : (Nat.sqrt n : ℝ) ≤ Real.sqrt ((n : ℝ)+1) := by nlinarith
  have hs : (Nat.sqrt n : ℝ)+1 ≤ 2*Real.sqrt ((n : ℝ)+1) := by linarith
  calc
    (representationCount 4 n : ℝ) ≤ C*((Nat.sqrt n : ℝ)+1)*((n : ℝ)+1)^ε := hb n
    _ ≤ C*(2*Real.sqrt ((n : ℝ)+1))*((n : ℝ)+1)^ε := by
      gcongr
    _ = (2*C)*((n : ℝ)+1)^(1/2+ε) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add (by positivity)]
      ring

end Quartic.GlobalUpper

/- The following congruence construction establishes growth beyond every fixed
power of the logarithm for all k≥2. This does not establish positive-power growth. -/
namespace UniversalModularLower
open Polynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

lemma good_prime (k : ℕ) (hk : 2 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ k ∧ p ∣ 1+k^k := by
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd
    (show 1+k^k ≠ 1 by have := pow_pos (by omega : 0 < k) k; omega)
  refine ⟨p,hp,?_,hd⟩
  intro hpk
  have hd' : p ∣ k^k := dvd_pow hpk (by omega : k ≠ 0)
  have h1 : p ∣ 1 := (Nat.dvd_add_left hd').mp hd
  exact hp.not_dvd_one h1

/-- A simple root at 1 modulo p lifts to every prime power. -/
lemma power_root_lift {p k : ℕ} (hp : p.Prime) (hpk : ¬p ∣ k)
    (c e : ℕ) (hc : p ∣ 1+c) :
    ∃ x : ℕ, x < p^e ∧ p^e ∣ x^k+c := by
  letI : Fact p.Prime := ⟨hp⟩
  let f : ℤ[X] := X^k+C (c : ℤ)
  have heval : f.aeval (1 : ℤ_[p]) = ((1+c : ℕ) : ℤ_[p]) := by
    simp [f]
  have hderiv : f.derivative.aeval (1 : ℤ_[p]) = (k : ℤ_[p]) := by
    simp [f, derivative_X_pow]
  have hdnorm : ‖f.derivative.aeval (1 : ℤ_[p])‖ = 1 := by
    rw [hderiv, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hpk
  have hsmall : ‖f.aeval (1 : ℤ_[p])‖ < ‖f.derivative.aeval (1 : ℤ_[p])‖^2 := by
    rw [hdnorm,one_pow,heval,PadicInt.norm_natCast_lt_one_iff]
    exact hc
  obtain ⟨z,hz,_⟩ := hensels_lemma hsmall
  have hzero : z^k+(c : ℤ_[p])=0 := by simpa [f] using hz
  let r : ZMod (p^e) := PadicInt.toZModPow e z
  refine ⟨r.val, ZMod.val_lt r, ?_⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have hh := congrArg (PadicInt.toZModPow e) hzero
  simpa only [map_add,map_pow,map_natCast,map_zero,ZMod.natCast_zmod_val, Nat.cast_add,
    Nat.cast_pow] using hh

lemma root_not_dvd {p k c e x : ℕ} (hp : p.Prime) (hk : 0 < k)
    (he : 0 < e) (hc : p ∣ 1+c) (hx : p^e ∣ x^k+c) : ¬p ∣ x := by
  intro hpx
  have hpPow : p ∣ p^e := dvd_pow_self p (by omega)
  have hsum := hpPow.trans hx
  have hxp : p ∣ x^k := dvd_pow hpx (by omega : k ≠ 0)
  have hcp : p ∣ c := (Nat.dvd_add_right hxp).mp hsum
  exact hp.not_dvd_one ((Nat.dvd_add_left hcp).mp hc)

noncomputable def modSolutions (k q : ℕ) : Finset (Fin k → Fin q) := by
  classical
  exact Finset.univ.filter (fun a ↦ q ∣ ∑ i, (a i : ℕ)^k)

lemma mem_modSolutions (k q : ℕ) (a : Fin k → Fin q) :
    a ∈ modSolutions k q ↔ q ∣ ∑ i, (a i : ℕ)^k := by
  classical
  simp [modSolutions]

/-- A single nonsingular residue solution gives a full box of free lifts. -/
lemma primitive_lower (d p e : ℕ) {seed : ℕ} (hp : p.Prime) (hpk : ¬p ∣ d+2)
    (hroot : p ∣ 1+seed^(d+2)) :
    p^(e*(d+1)) ≤ ((modSolutions (d+2) (p^(e+1))).filter
      (fun a ↦ ¬p ∣ (a 0 : ℕ))).card := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let r : Fin (d+1) → ℕ := Fin.cons (seed%p) (fun _ ↦ 0)
  have hr : ∀ i, r i < p := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Nat.mod_lt _ hp.pos
    · exact hp.pos
  let free (b : Fin (d+1) → Fin (p^e)) (i : Fin (d+1)) : ℕ := p*(b i)+r i
  have hfree : ∀ b i, free b i < p^(e+1) := by
    intro b i
    have hi := (b i).isLt
    have hri := hr i
    dsimp [free]
    rw [pow_succ']
    nlinarith
  have hmod : ∀ b, p ∣ 1+∑ i, free b i^(d+2) := by
    intro b
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hf : ∀ i, (free b i : ZMod p)=(r i : ZMod p) := by
      intro i
      simp [free]
    have ht := (ZMod.natCast_eq_zero_iff _ p).mpr hroot
    push_cast at ht ⊢
    simp_rw [hf]
    simpa [r, Fin.sum_univ_succ] using ht
  choose x hxlt hxdiv using
    (fun b : Fin (d+1) → Fin (p^e) ↦
      power_root_lift hp hpk (∑ i, free b i^(d+2)) (e+1) (hmod b))
  let F (b : Fin (d+1) → Fin (p^e)) : Fin (d+2) → Fin (p^(e+1)) :=
    Fin.cons ⟨x b,hxlt b⟩ (fun i ↦ ⟨free b i,hfree b i⟩)
  have hF : ∀ b, F b ∈ (modSolutions (d+2) (p^(e+1))).filter
      (fun a ↦ ¬p ∣ (a 0 : ℕ)) := by
    intro b
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_modSolutions, Fin.sum_univ_succ]
      exact hxdiv b
    · exact root_not_dvd hp (by omega) (by omega) (hmod b) (hxdiv b)
  have hinj : Function.Injective F := by
    intro b c h
    funext i
    have he : free b i=free c i := congrArg Fin.val (congrFun h i.succ)
    dsimp [free] at he
    have hb : (b i : ℕ)=(c i : ℕ) := Nat.eq_of_mul_eq_mul_left hp.pos (by omega)
    exact Fin.ext hb
  have hh := Finset.card_le_card_of_injOn (s := Finset.univ) F (fun b _ ↦ hF b) (fun b _ c _ h ↦ hinj h)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ← pow_mul] using hh

/-- Scaling all coordinates contributes the previous local density again,
with the same critical-dimensional normalizing factor. -/
lemma dilated_lower (k p q : ℕ) (hk : 0 < k) (hp : 0 < p) (hq : 0 < q) :
    p^(k*(k-1))*(modSolutions k q).card ≤
      ((modSolutions k (q*p^k)).filter (fun a ↦ ∀ i, p ∣ (a i : ℕ))).card := by
  classical
  have hpow : p*p^(k-1)=p^k := by rw [← pow_succ']; congr 1; omega
  let F (z : (Fin k → Fin q) × (Fin k → Fin (p^(k-1)))) :
      Fin k → Fin (q*p^k) := fun i ↦
    ⟨p*((z.1 i : ℕ)+q*(z.2 i : ℕ)), by
      have ha := (z.1 i).isLt
      have hb := (z.2 i).isLt
      have hh : (z.1 i : ℕ)+q*(z.2 i : ℕ) < q*p^(k-1) := by nlinarith
      have hm := Nat.mul_lt_mul_of_pos_left hh hp
      nlinarith [hpow]⟩
  have hF : ∀ z ∈ (modSolutions k q) ×ˢ (Finset.univ : Finset (Fin k → Fin (p^(k-1)))),
      F z ∈ (modSolutions k (q*p^k)).filter (fun a ↦ ∀ i, p ∣ (a i : ℕ)) := by
    intro z hz
    have hza := (mem_modSolutions k q z.1).mp (Finset.mem_product.mp hz).1
    have hsum : q ∣ ∑ i, ((z.1 i : ℕ)+q*(z.2 i : ℕ))^k := by
      apply (ZMod.natCast_eq_zero_iff _ q).mp
      have he := (ZMod.natCast_eq_zero_iff _ q).mpr hza
      push_cast at he ⊢
      simpa using he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_modSolutions]
      change q*p^k ∣ ∑ i, (p*((z.1 i : ℕ)+q*(z.2 i : ℕ)))^k
      simp only [mul_pow, ← Finset.mul_sum]
      simpa only [Nat.mul_comm] using Nat.mul_dvd_mul_left (p^k) hsum
    · intro i
      exact dvd_mul_right p _
  have hinj : Function.Injective F := by
    intro z w h
    have hh : ∀ i, (z.1 i : ℕ)+q*(z.2 i : ℕ) =
        (w.1 i : ℕ)+q*(w.2 i : ℕ) := fun i ↦
      Nat.eq_of_mul_eq_mul_left hp (congrArg Fin.val (congrFun h i))
    have ha : z.1=w.1 := by
      funext i
      apply Fin.ext
      have he := congrArg (fun n ↦ n%q) (hh i)
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (z.1 i).isLt,
        Nat.mod_eq_of_lt (w.1 i).isLt] using he
    have hb : z.2=w.2 := by
      funext i
      apply Fin.ext
      apply Nat.eq_of_mul_eq_mul_left hq
      have he := hh i
      rw [ha] at he
      omega
    exact Prod.ext ha hb
  have hh := Finset.card_le_card_of_injOn F hF (fun z _ w _ he ↦ hinj he)
  simpa [Finset.card_product, ← pow_mul, Nat.mul_comm] using hh

lemma local_recurrence (d p t : ℕ) {seed : ℕ} (hp : p.Prime) (hpk : ¬p ∣ d+2)
    (hroot : p ∣ 1+seed^(d+2)) :
    p^((d+2)*(d+1))*(modSolutions (d+2) (p^((d+2)*t))).card +
      p^(((d+2)*(t+1)-1)*(d+1)) ≤
      (modSolutions (d+2) (p^((d+2)*(t+1)))).card := by
  classical
  let s := modSolutions (d+2) (p^((d+2)*(t+1)))
  let a := s.filter (fun a ↦ ∀ i, p ∣ (a i : ℕ))
  let b := s.filter (fun a ↦ ¬p ∣ (a 0 : ℕ))
  have had := dilated_lower (d+2) p (p^((d+2)*t)) (by omega) hp.pos (pow_pos hp.pos _)
  have hexp : p^((d+2)*t)*p^(d+2)=p^((d+2)*(t+1)) := by rw [← pow_add, Nat.mul_add, Nat.mul_one]
  rw [hexp] at had
  have hb := primitive_lower d p ((d+2)*(t+1)-1) hp hpk hroot
  have he : (d+2)*(t+1)-1+1=(d+2)*(t+1) := by
    have hpos : 0 < (d+2)*(t+1) := by positivity
    omega
  rw [he] at hb
  have hd : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 ((Finset.mem_filter.mp hx).2 0)
  have hu : a ∪ b ⊆ s := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hh : a.card+b.card ≤ s.card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card hu
  have ha : p^((d+2)*(d+1))*(modSolutions (d+2) (p^((d+2)*t))).card ≤ a.card := by
    simpa only [Nat.add_sub_cancel] using had
  exact (Nat.add_le_add ha hb).trans hh

/-- The normalized local count grows at least linearly with the depth. -/
theorem normalized_local_lower (d p t : ℕ) {seed : ℕ} (hp : p.Prime) (hpk : ¬p ∣ d+2)
    (hroot : p ∣ 1+seed^(d+2)) :
    (t+1)*(p^((d+2)*t))^(d+1) ≤
      p^(d+1)*(modSolutions (d+2) (p^((d+2)*t))).card := by
  classical
  induction t with
  | zero =>
    simpa [modSolutions] using (one_le_pow₀ (Nat.one_le_of_lt hp.one_lt) : 1 ≤ p^(d+1))
  | succ t ih =>
    have hpow1 : p^((d+2)*(d+1))*(p^((d+2)*t))^(d+1) =
        (p^((d+2)*(t+1)))^(d+1) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    have hpos : 0 < (d+2)*(t+1) := by positivity
    have hsub : (d+2)*(t+1)-1+1=(d+2)*(t+1) := by omega
    have hpow2 : p^(d+1)*p^(((d+2)*(t+1)-1)*(d+1)) =
        (p^((d+2)*(t+1)))^(d+1) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      nlinarith
    calc
      _ = p^((d+2)*(d+1))*((t+1)*(p^((d+2)*t))^(d+1)) +
          p^(d+1)*p^(((d+2)*(t+1)-1)*(d+1)) := by
        rw [mul_left_comm (p^((d+2)*(d+1))) (t+1),hpow1,hpow2]
        ring
      _ ≤ p^((d+2)*(d+1))*(p^(d+1)*(modSolutions (d+2) (p^((d+2)*t))).card) +
          p^(d+1)*p^(((d+2)*(t+1)-1)*(d+1)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ = p^(d+1)*(p^((d+2)*(d+1))*(modSolutions (d+2) (p^((d+2)*t))).card +
          p^(((d+2)*(t+1)-1)*(d+1))) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (local_recurrence d p t hp hpk hroot)

lemma tuple_sum_lt (k q : ℕ) (hk : 0 < k) (a : Fin k → Fin q) :
    (∑ i, (a i : ℕ)^k) < k*q^k := by
  have h := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset (Fin k))) (by exact ⟨⟨0,hk⟩, Finset.mem_univ _⟩)
    (f := fun i ↦ (a i : ℕ)^k) (g := fun _ ↦ q^k)
    (fun i _ ↦ Nat.pow_lt_pow_left (a i).isLt (by omega : k ≠ 0))
  simpa using h

lemma fiber_card_le_count {k q n : ℕ} (hk : 0 < k)
    (s : Finset (Fin k → Fin q)) (hs : ∀ a ∈ s, ∑ i, (a i : ℕ)^k = n) :
    s.card ≤ representationCount k n := by
  classical
  let f (a : s) (i : Fin k) : ℕ := a.val i
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun he i
  have hb := count_ge_of_family k n hk f hf (fun a ↦ hs a.val a.property)
  simpa only [Fintype.card_coe] using hb

/-- The local density is bounded by the largest representation count in the
corresponding finite box, times the number of possible target multiples. -/
lemma modular_upper (k q M : ℕ) (hk : 0 < k) (hq : 0 < q)
    (hM : ∀ n < k*q^k, representationCount k n ≤ M) :
    (modSolutions k q).card ≤ M*(k*q^(k-1)) := by
  classical
  let f (a : Fin k → Fin q) : ℕ := (∑ i, (a i : ℕ)^k)/q
  have hpow : q^(k-1)*q=q^k := by rw [← pow_succ]; congr 1; omega
  have hmap : ∀ a ∈ modSolutions k q, f a ∈ Finset.range (k*q^(k-1)) := by
    intro a _
    rw [Finset.mem_range]
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    change (∑ i, (a i : ℕ)^k) < k*q^(k-1)*q
    rw [Nat.mul_assoc,hpow]
    exact tuple_sum_lt k q hk a
  have hfiber : ∀ m ∈ Finset.range (k*q^(k-1)),
      ((modSolutions k q).filter (fun a ↦ f a=m)).card ≤ M := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    have hn : m*q < k*q^k := by
      have hh := Nat.mul_lt_mul_of_pos_right hm' hq
      simpa only [Nat.mul_assoc,hpow] using hh
    refine (fiber_card_le_count hk _ ?_).trans (hM (m*q) hn)
    intro a ha
    have hd := (mem_modSolutions k q a).mp (Finset.mem_filter.mp ha).1
    have he := (Finset.mem_filter.mp ha).2
    change (∑ i, (a i : ℕ)^k)/q = m at he
    calc
      _ = ((∑ i, (a i : ℕ)^k)/q)*q := (Nat.div_mul_cancel hd).symm
      _ = _ := by rw [he]
  simpa only [Finset.card_range] using
    Finset.card_le_mul_card_image_of_maps_to hmap M hfiber

/-- Every exponent at least two has arbitrarily large representation counts,
with an explicit exponential upper bound on the first target found here. -/
theorem large_count_bounded_height (d p M : ℕ) {seed : ℕ} (hp : p.Prime) (hpk : ¬p ∣ d+2)
    (hroot : p ∣ 1+seed^(d+2)) :
    ∃ n < (d+2)*(p^((d+2)*(M*(d+2)*p^(d+1))))^(d+2),
      M < representationCount (d+2) n := by
  classical
  by_contra hn
  push_neg at hn
  let t := M*(d+2)*p^(d+1)
  let q := p^((d+2)*t)
  have hq : 0 < q := pow_pos hp.pos _
  have hu := modular_upper (d+2) q M (by omega) hq hn
  have hl := normalized_local_lower d p t hp hpk hroot
  have hl' : (t+1)*q^(d+1) ≤ p^(d+1)*(modSolutions (d+2) q).card := hl
  have hu' : (modSolutions (d+2) q).card ≤ M*((d+2)*q^(d+1)) := by
    simpa only [Nat.add_sub_cancel] using hu
  have hh : (t+1)*q^(d+1) ≤ t*q^(d+1) := by
    calc
      _ ≤ p^(d+1)*(modSolutions (d+2) q).card := hl'
      _ ≤ p^(d+1)*(M*((d+2)*q^(d+1))) := Nat.mul_le_mul_left _ hu'
      _ = _ := by dsimp [t]; ring
  have hpos : 0 < q^(d+1) := pow_pos hq _
  nlinarith

theorem count_unbounded (k : ℕ) (hk : 2 ≤ k) (M : ℕ) :
    ∃ n : ℕ, M < representationCount k n := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨p,hp,hpk,hroot⟩ := good_prime (2+d) (by omega)
  obtain ⟨n,_,hn⟩ := large_count_bounded_height d p M hp
    (by simpa only [Nat.add_comm] using hpk) (by simpa only [Nat.add_comm] using hroot)
  exact ⟨n,by simpa only [Nat.add_comm] using hn⟩

theorem exponential_heights (k : ℕ) (hk : 2 ≤ k) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ M : ℕ, 1 ≤ M →
      ∃ n : ℕ, n < B^M ∧ M < representationCount k n := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
  have hkd : k=d+2 := by omega
  clear hd
  subst k
  obtain ⟨p,hp,hpk,hroot⟩ := good_prime (d+2) (by omega)
  let D := (d+2)^3*p^(d+1)
  let B := (d+2)*p^D
  have hBD : 1 ≤ p^D := one_le_pow₀ (Nat.one_le_of_lt hp.one_lt)
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  refine ⟨B,hB,?_⟩
  intro M hM
  obtain ⟨n,hn,hcount⟩ := large_count_bounded_height d p M hp hpk hroot
  refine ⟨n,hn.trans_le ?_,hcount⟩
  have hexp : (p^((d+2)*(M*(d+2)*p^(d+1))))^(d+2)=(p^D)^M := by
    rw [← pow_mul,← pow_mul]
    congr 1
    dsimp [D]
    ring
  rw [hexp]
  have hkpow : d+2 ≤ (d+2)^M := Nat.le_pow (by omega)
  calc
    _ ≤ (d+2)^M*(p^D)^M := Nat.mul_le_mul_right _ hkpow
    _ = B^M := by rw [← mul_pow]

lemma infinite_logarithmic_of_exponential_heights (f : ℕ → ℕ) (B : ℕ) (hB : 2 ≤ B)
    (h : ∀ M : ℕ, 1 ≤ M → ∃ n : ℕ, n < B^M ∧ M < f n) :
    {n : ℕ | Real.log (n : ℝ)/Real.log (B : ℝ) < f n}.Infinite := by
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  intro hfinite
  obtain ⟨M,hM⟩ := (hfinite.image f).bddAbove
  obtain ⟨n,hn,hcount⟩ := h (M+1) (by omega)
  have hmem : n ∈ {n : ℕ | Real.log (n : ℝ)/Real.log (B : ℝ) < f n} := by
    change Real.log (n : ℝ)/Real.log (B : ℝ) < f n
    by_cases hn0 : n=0
    · simp only [hn0, Nat.cast_zero, Real.log_zero, zero_div]
      exact_mod_cast (show 0 < f 0 by simpa [hn0] using (Nat.zero_le M).trans_lt (Nat.lt_succ_self M) |>.trans hcount)
    · have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hbound : (n : ℝ) < (B : ℝ)^(M+1) := by exact_mod_cast hn
      have hl := Real.log_lt_log hnr hbound
      rw [Real.log_pow] at hl
      have hl' : Real.log (n : ℝ)/Real.log (B : ℝ) < (M+1 : ℕ) :=
        (div_lt_iff₀ hlog).mpr hl
      exact hl'.trans (by exact_mod_cast hcount)
  have hh : f n ≤ M := hM (Set.mem_image_of_mem f hmem)
  omega

/-- A logarithmic lower bound holds infinitely often at every exponent at least
2. No fixed positive-power lower bound follows from this theorem. -/
theorem logarithmic_growth (k : ℕ) (hk : 2 ≤ k) :
    ∃ C > (0 : ℝ),
      {n : ℕ | Real.log (n : ℝ)/C < representationCount k n}.Infinite := by
  obtain ⟨B,hB,h⟩ := exponential_heights k hk
  refine ⟨Real.log (B : ℝ), Real.log_pos (by exact_mod_cast hB), ?_⟩
  exact infinite_logarithmic_of_exponential_heights (representationCount k) B hB h

lemma good_prime_avoiding (k N : ℕ) (hk : 2 ≤ k) (hN : 0 < N) :
    ∃ p seed : ℕ, p.Prime ∧ ¬p ∣ k ∧ ¬p ∣ N ∧ p ∣ 1+seed^k := by
  let seed := k*N
  have hs : 0 < seed := Nat.mul_pos (by omega) hN
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd
    (show 1+seed^k ≠ 1 by have := pow_pos hs k; omega)
  have hps : ¬p ∣ seed := by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow h (by omega : k ≠ 0))).mp hd)
  refine ⟨p,seed,hp,?_,?_,hd⟩
  · intro h
    exact hps (dvd_mul_of_dvd_left h N)
  · intro h
    exact hps (dvd_mul_of_dvd_right h k)

lemma crt_lower (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (modSolutions k a).card*(modSolutions k b).card ≤ (modSolutions k (a*b)).card := by
  classical
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  let e := ZMod.chineseRemainder hab
  let z (w : (Fin k → Fin a) × (Fin k → Fin b)) (i : Fin k) : ZMod (a*b) :=
    e.symm ((w.1 i : ZMod a),(w.2 i : ZMod b))
  let F (w : (Fin k → Fin a) × (Fin k → Fin b)) (i : Fin k) : Fin (a*b) :=
    ⟨(z w i).val, ZMod.val_lt _⟩
  have hcast : ∀ w i, ((F w i : ℕ) : ZMod (a*b))=z w i := by
    intro w i
    exact ZMod.natCast_zmod_val _
  have hF : ∀ w ∈ (modSolutions k a) ×ˢ (modSolutions k b),
      F w ∈ modSolutions k (a*b) := by
    intro w hw
    have hwa := (mem_modSolutions k a w.1).mp (Finset.mem_product.mp hw).1
    have hwb := (mem_modSolutions k b w.2).mp (Finset.mem_product.mp hw).2
    have hza := (ZMod.natCast_eq_zero_iff _ a).mpr hwa
    have hzb := (ZMod.natCast_eq_zero_iff _ b).mpr hwb
    rw [mem_modSolutions]
    apply (ZMod.natCast_eq_zero_iff _ (a*b)).mp
    push_cast
    simp_rw [hcast]
    apply e.injective
    simp only [map_sum,map_pow,map_zero,z,RingEquiv.apply_symm_apply]
    apply Prod.ext
    · simpa only [Prod.fst_sum,Nat.cast_sum,Nat.cast_pow] using hza
    · simpa only [Prod.snd_sum,Nat.cast_sum,Nat.cast_pow] using hzb
  have hinj : Function.Injective F := by
    intro v w h
    have he : ∀ i, ((v.1 i : ZMod a),(v.2 i : ZMod b)) =
        ((w.1 i : ZMod a),(w.2 i : ZMod b)) := by
      intro i
      have hh := congrArg (fun x : Fin (a*b) ↦ e ((x : ℕ) : ZMod (a*b))) (congrFun h i)
      simpa only [hcast,z,RingEquiv.apply_symm_apply] using hh
    apply Prod.ext
    · funext i
      apply Fin.ext
      have hv := congrArg ZMod.val (congrArg Prod.fst (he i))
      simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (v.1 i).isLt,
        Nat.mod_eq_of_lt (w.1 i).isLt] using hv
    · funext i
      apply Fin.ext
      have hv := congrArg ZMod.val (congrArg Prod.snd (he i))
      simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (v.2 i).isLt,
        Nat.mod_eq_of_lt (w.2 i).isLt] using hv
  have hh := Finset.card_le_card_of_injOn F hF (fun v _ w _ he ↦ hinj he)
  simpa only [Finset.card_product] using hh

/-- Independent primes give arbitrarily high powers of the local depth. -/
theorem normalized_many_primes (k : ℕ) (hk : 2 ≤ k) (r : ℕ) :
    ∃ A D : ℕ, 1 ≤ A ∧ 1 ≤ D ∧ ∀ t : ℕ,
      (t+1)^r*(A^t)^(k-1) ≤ D*(modSolutions k (A^t)).card := by
  classical
  induction r with
  | zero =>
    refine ⟨1,1,by omega,by omega,?_⟩
    intro t
    simp [modSolutions]
  | succ r ih =>
    obtain ⟨A,D,hA,hD,h⟩ := ih
    obtain ⟨p,seed,hp,hpk,hpA,hroot⟩ := good_prime_avoiding k A hk (by omega)
    have hcop : A.Coprime p := (hp.coprime_iff_not_dvd.mpr hpA).symm
    have hppos : 0 < p^(k-1) := pow_pos hp.pos _
    have hpkpos : 0 < p^k := pow_pos hp.pos _
    refine ⟨A*p^k,D*p^(k-1),by nlinarith,by nlinarith,?_⟩
    intro t
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
    have hkd : k=d+2 := by omega
    clear hd
    have hl : (t+1)*(p^(k*t))^(k-1) ≤ p^(k-1)*(modSolutions k (p^(k*t))).card := by
      subst k
      simpa only [show d+2-1=d+1 by omega] using normalized_local_lower d p t hp
        (by simpa only [Nat.add_comm] using hpk) (by simpa only [Nat.add_comm] using hroot)
    have hc := crt_lower k (A^t) (p^(k*t)) (pow_pos (by omega) _) (pow_pos hp.pos _)
      (hcop.pow t (k*t))
    have he : (A*p^k)^t=A^t*p^(k*t) := by rw [mul_pow,pow_mul]
    calc
      _ = ((t+1)^r*(A^t)^(k-1))*((t+1)*(p^(k*t))^(k-1)) := by
        rw [he,mul_pow,pow_succ]
        ring
      _ ≤ (D*(modSolutions k (A^t)).card)*
          (p^(k-1)*(modSolutions k (p^(k*t))).card) := Nat.mul_le_mul (h t) hl
      _ = (D*p^(k-1))*((modSolutions k (A^t)).card*(modSolutions k (p^(k*t))).card) := by ring
      _ ≤ (D*p^(k-1))*(modSolutions k (A^t*p^(k*t))).card := Nat.mul_le_mul_left _ hc
      _ = _ := by rw [he]

/-- For each fixed logarithmic degree, there are that many powers of the
parameter in the count at targets of exponential, rather than polynomial, height. -/
theorem many_large_counts_exponential_heights (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ T : ℕ, 1 ≤ T →
      ∃ n : ℕ, n < B^T ∧ T^r < representationCount k n := by
  classical
  obtain ⟨A,D,hA,hD,h⟩ := normalized_many_primes k hk r
  let B := k*A^(D*k*k)
  have hApow : 1 ≤ A^(D*k*k) := one_le_pow₀ hA
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  refine ⟨B,hB,?_⟩
  intro T hT
  let t := D*k*T
  let q := A^t
  have hq : 0 < q := pow_pos (by omega) _
  have hex : ∃ n < k*q^k, T^r < representationCount k n := by
    by_contra hn
    push_neg at hn
    have hu := modular_upper k q (T^r) (by omega) hq hn
    have hl : (t+1)^r*q^(k-1) ≤ D*(modSolutions k q).card := h t
    have hh : (t+1)^r*q^(k-1) ≤ (D*k*T^r)*q^(k-1) := by
      calc
        _ ≤ D*(modSolutions k q).card := hl
        _ ≤ D*(T^r*(k*q^(k-1))) := Nat.mul_le_mul_left _ hu
        _ = _ := by ring
    have hdk : D*k ≤ (D*k)^r := Nat.le_pow (by omega)
    have ht : D*k*T^r ≤ t^r := by
      dsimp [t]
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ hdk
    have hstrict : D*k*T^r < (t+1)^r :=
      ht.trans_lt (Nat.pow_lt_pow_left (by omega) (by omega))
    exact (not_lt_of_ge hh)
      (Nat.mul_lt_mul_of_pos_right hstrict (pow_pos hq _))
  obtain ⟨n,hn,hcount⟩ := hex
  refine ⟨n,hn.trans_le ?_,hcount⟩
  have he : q^k=(A^(D*k*k))^T := by
    dsimp [q,t]
    simp only [← pow_mul]
    congr 1
    ring
  rw [he]
  calc
    k*(A^(D*k*k))^T ≤ k^T*(A^(D*k*k))^T :=
      Nat.mul_le_mul_right _ (Nat.le_pow (by omega))
    _ = B^T := by rw [← mul_pow]

lemma infinite_log_power_of_exponential_heights (f : ℕ → ℕ) (B r : ℕ)
    (hB : 2 ≤ B) (hr : 1 ≤ r)
    (h : ∀ T : ℕ, 1 ≤ T → ∃ n : ℕ, n < B^T ∧ T^r < f n) :
    {n : ℕ | (Real.log (n : ℝ))^r/(Real.log (B : ℝ))^r < f n}.Infinite := by
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  have hC : 0 < (Real.log (B : ℝ))^r := pow_pos hlog _
  intro hfinite
  obtain ⟨M,hM⟩ := (hfinite.image f).bddAbove
  obtain ⟨n,hn,hcount⟩ := h (M+1) (by omega)
  have hMpow : M+1 ≤ (M+1)^r := Nat.le_pow (by omega)
  have hmem : n ∈ {n : ℕ | (Real.log (n : ℝ))^r/(Real.log (B : ℝ))^r < f n} := by
    change (Real.log (n : ℝ))^r/(Real.log (B : ℝ))^r < f n
    by_cases hn0 : n=0
    · simp only [hn0,Nat.cast_zero,Real.log_zero,zero_pow (by omega : r ≠ 0),zero_div]
      have hfpos : 0 < f 0 := by rw [hn0] at hcount; omega
      exact_mod_cast hfpos
    · have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hbound : (n : ℝ) < (B : ℝ)^(M+1) := by exact_mod_cast hn
      have hl := Real.log_lt_log hnr hbound
      rw [Real.log_pow] at hl
      have hpow := pow_lt_pow_left₀ hl (Real.log_nonneg hn1) (by omega : r ≠ 0)
      rw [mul_pow] at hpow
      have hdiv := (div_lt_iff₀ hC).mpr hpow
      exact hdiv.trans (by exact_mod_cast hcount)
  have hh : f n ≤ M := hM (Set.mem_image_of_mem f hmem)
  omega

/-- Every fixed logarithmic power is exceeded infinitely often, uniformly in
its applicability to all exponents k≥2. The constant depends on k and r. -/
theorem every_logarithmic_power (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    ∃ C > (0 : ℝ),
      {n : ℕ | (Real.log (n : ℝ))^r/C < representationCount k n}.Infinite := by
  obtain ⟨B,hB,h⟩ := many_large_counts_exponential_heights k r hk hr
  refine ⟨(Real.log (B : ℝ))^r,
    pow_pos (Real.log_pos (by exact_mod_cast hB)) _, ?_⟩
  exact infinite_log_power_of_exponential_heights (representationCount k) B r hB hr h

/-- The multiplicative constant can be removed by constructing one extra
logarithmic power. This also includes r=0. -/
theorem every_logarithmic_power_unscaled (k r : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | (Real.log (n : ℝ))^r < representationCount k n}.Infinite := by
  obtain ⟨B,hB,h⟩ := many_large_counts_exponential_heights k (r+1) hk (by omega)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  intro hfinite
  obtain ⟨M,hM⟩ := (hfinite.image (representationCount k)).bddAbove
  let C : ℕ := ⌈(Real.log (B : ℝ))^r⌉₊
  let T : ℕ := M+C+2
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hMT : M < T := by dsimp [T]; omega
  have hCT : (Real.log (B : ℝ))^r < T := by
    have hc : (Real.log (B : ℝ))^r ≤ (C : ℝ) := Nat.le_ceil _
    have hct : (C : ℝ) < T := by exact_mod_cast (show C<T by dsimp [T]; omega)
    exact hc.trans_lt hct
  obtain ⟨n,hn,hcount⟩ := h T hT
  have hl : Real.log (n : ℝ) ≤ (T : ℝ)*Real.log (B : ℝ) := by
    by_cases hn0 : n=0
    · simp only [hn0,Nat.cast_zero,Real.log_zero]
      positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hnlt : (n : ℝ) < (B : ℝ)^T := by exact_mod_cast hn
      simpa only [Real.log_pow] using (Real.log_lt_log hnpos hnlt).le
  have hmem : n ∈ {n : ℕ | (Real.log (n : ℝ))^r < representationCount k n} := by
    change (Real.log (n : ℝ))^r < representationCount k n
    calc
      _ ≤ ((T : ℝ)*Real.log (B : ℝ))^r :=
        pow_le_pow_left₀ (Real.log_natCast_nonneg n) hl r
      _ < (T : ℝ)^(r+1) := by
        rw [mul_pow,pow_succ]
        exact mul_lt_mul_of_pos_left hCT (pow_pos (by exact_mod_cast (show 0<T by omega)) _)
      _ < _ := by exact_mod_cast hcount
  have hh : representationCount k n ≤ M := hM (Set.mem_image_of_mem _ hmem)
  have hTp : T ≤ T^(r+1) := Nat.le_pow (by omega)
  omega

end UniversalModularLower

/- The following quantitative refinement uses Dirichlet's theorem and the
same local lifting construction. Its bound is still subpolynomial. -/
namespace PrimeAPGrowth
open Filter
set_option maxHeartbeats 1000000

lemma log_div_le_rpow (x : ℝ) (hx : 0 < x) :
    Real.log x / x ≤ 4*x^(-(3/4 : ℝ)) := by
  have hl := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1/4)
  have he : x^(1/4 : ℝ)/x = x^(-(3/4 : ℝ)) := by
    have hh := Real.rpow_sub hx (1/4 : ℝ) 1
    norm_num at hh
    exact hh.symm
  calc
    _ ≤ (x^(1/4 : ℝ)/(1/4))/x := div_le_div_of_nonneg_right hl hx.le
    _ = 4*(x^(1/4 : ℝ)/x) := by ring
    _ = _ := by rw [he]

theorem nth_prime_ap_le_square_frequently (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ∀ R : ℕ, ∃ r : ℕ, R ≤ r ∧
      Nat.nth (fun p : ℕ ↦ p.Prime ∧ (p : ZMod q)=a) r ≤ (r+1)^2 := by
  classical
  let P : ℕ → Prop := fun p ↦ p.Prime ∧ (p : ZMod q)=a
  let g : ℕ → ℝ := fun n ↦
    (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0)/(n : ℝ)
  have hinf : {p | P p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod ha
  have hg : ¬ Summable g := ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div ha
  have hnonneg (n : ℕ) : 0 ≤ g n := by
    dsimp [g]
    apply div_nonneg _ (Nat.cast_nonneg _)
    split_ifs
    · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _
    · rfl
  have heval (n : ℕ) : g (Nat.nth P n) =
      Real.log (Nat.nth P n : ℝ)/(Nat.nth P n : ℝ) := by
    obtain ⟨hp,ha'⟩ := Nat.nth_mem_of_infinite hinf n
    dsimp [g,ArithmeticFunction.vonMangoldt.residueClass]
    have hm : Nat.nth P n ∈ {n : ℕ | (n : ZMod q)=a} := ha'
    rw [if_pos hp,Set.indicator_of_mem hm,ArithmeticFunction.vonMangoldt_apply_prime hp]
  intro R
  by_contra h
  push_neg at h
  have hcomp : Summable (g ∘ Nat.nth P) := by
    have hsum : Summable (fun n : ℕ ↦ 4*((n+1 : ℕ) : ℝ)^(-(3/2 : ℝ))) := by
      apply Summable.mul_left
      exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
    apply hsum.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop R] with n hn
    rw [Function.comp_apply,Real.norm_of_nonneg (hnonneg _),heval]
    have hp := (Nat.nth_mem_of_infinite hinf n).1
    have hpos : (0 : ℝ) < Nat.nth P n := by exact_mod_cast hp.pos
    apply (log_div_le_rpow _ hpos).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    have hbound : (((n+1 : ℕ) : ℝ)^2) ≤ Nat.nth P n := by exact_mod_cast (h n hn).le
    have hh := Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < ((n+1 : ℕ) : ℝ)^2 by positivity)
      hbound (by norm_num : -(3/4 : ℝ) ≤ 0)
    have he : ((((n+1 : ℕ) : ℝ)^2)^(-(3/4 : ℝ))) =
        ((n+1 : ℕ) : ℝ)^(-(3/2 : ℝ)) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    exact he ▸ hh
  apply hg
  apply (Nat.nth_injective hinf).summable_iff _ |>.mp hcomp
  intro n hn
  have hn' : ¬ P n := by
    intro hpn
    exact hn (Nat.subset_range_nth hpn)
  dsimp [P] at hn'
  dsimp [g,ArithmeticFunction.vonMangoldt.residueClass]
  by_cases hp : n.Prime
  · have hm : n ∉ {n : ℕ | (n : ZMod q)=a} := fun hn ↦ hn' ⟨hp,hn⟩
    rw [if_pos hp,Set.indicator_of_notMem hm,zero_div]
  · rw [if_neg hp,zero_div]

lemma root_of_prime_one_mod (k p : ℕ) (hk : 0 < k) (hp : p.Prime)
    (hmod : (p : ZMod (2*k)) = 1) :
    ¬ p ∣ k ∧ ∃ seed : ℕ, p ∣ 1+seed^k := by
  have hpp : 2 ≤ p := hp.two_le
  have hcong : p ≡ 1 [MOD 2*k] :=
    (ZMod.natCast_eq_natCast_iff p 1 (2*k)).mp (by simpa using hmod)
  have hdiv : 2*k ∣ p-1 := Nat.modEq_zero_iff_dvd.mp
    (by simpa using hcong.sub hp.one_lt.le (by rfl : 1 ≤ 1) (Nat.ModEq.refl 1))
  have hkle : 2*k ≤ p-1 := Nat.le_of_dvd (by omega) hdiv
  have hpk : ¬p ∣ k := Nat.not_dvd_of_pos_of_lt hk (by omega)
  refine ⟨hpk,?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card,ZMod.card_units] at hg
  have hg' : IsPrimitiveRoot (g : ZMod p) (p-1) :=
    IsPrimitiveRoot.coe_units_iff.mpr (hg ▸ IsPrimitiveRoot.orderOf g)
  obtain ⟨t,ht⟩ := hdiv
  have hrt : IsPrimitiveRoot ((g : ZMod p)^t) (2*k) :=
    hg'.pow (by omega) (by simpa only [Nat.mul_comm] using ht)
  have hz : (((g : ZMod p)^t)^k) = -1 :=
    (hrt.pow (by omega) (by omega : 2*k=k*2)).eq_neg_one_of_two_right
  refine ⟨((g : ZMod p)^t).val,?_⟩
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  push_cast
  rw [ZMod.natCast_zmod_val,hz,add_neg_cancel]

end PrimeAPGrowth

namespace SuperLogLower
open UniversalModularLower
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma normalized_finite_primes (k : ℕ) (hk : 2 ≤ k) (r : ℕ)
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpk : ∀ i, ¬p i ∣ k) (hroot : ∀ i, ∃ seed : ℕ, p i ∣ 1+seed^k) :
    ∀ t : ℕ, (t+1)^r*((∏ i, p i^k)^t)^(k-1) ≤
      (∏ i, p i^(k-1))*(modSolutions k ((∏ i, p i^k)^t)).card := by
  classical
  induction r with
  | zero => intro t; simp [modSolutions]
  | succ r ih =>
    let p' : Fin r → ℕ := fun i ↦ p i.castSucc
    have hi := ih p' (fun i ↦ hp i.castSucc)
      (hinj.comp (Fin.castSucc_injective r)) (fun i ↦ hpk i.castSucc)
      (fun i ↦ hroot i.castSucc)
    let A := ∏ i, p' i^k
    let D := ∏ i, p' i^(k-1)
    let z := p (Fin.last r)
    have hz : z.Prime := hp _
    have hApos : 0 < A := Finset.prod_pos (fun i _ ↦ pow_pos (hp i.castSucc).pos _)
    have hcop : A.Coprime z := by
      apply Nat.Coprime.prod_left
      intro i _
      apply Nat.Coprime.pow_left
      apply (Nat.coprime_primes (hp i.castSucc) hz).mpr
      intro he
      have hh := hinj he
      have hh' := congrArg Fin.val hh
      have hil := i.isLt
      simp only [Fin.val_castSucc,Fin.val_last] at hh'
      omega
    intro t
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
    have hkd : k=d+2 := by omega
    clear hd
    obtain ⟨seed,hseed⟩ := hroot (Fin.last r)
    have hl : (t+1)*(z^(k*t))^(k-1) ≤
        z^(k-1)*(modSolutions k (z^(k*t))).card := by
      subst k
      simpa only [show d+2-1=d+1 by omega] using
        normalized_local_lower d z t hz (hpk _) hseed
    have hc := crt_lower k (A^t) (z^(k*t)) (pow_pos hApos _) (pow_pos hz.pos _)
      (hcop.pow t (k*t))
    have he : (∏ i, p i^k)^t=A^t*z^(k*t) := by
      rw [Fin.prod_univ_castSucc,mul_pow,pow_mul]
    have hD : (∏ i, p i^(k-1))=D*z^(k-1) := Fin.prod_univ_castSucc _
    calc
      _ = ((t+1)^r*(A^t)^(k-1))*((t+1)*(z^(k*t))^(k-1)) := by
        rw [he,mul_pow,pow_succ]; ring
      _ ≤ (D*(modSolutions k (A^t)).card)*(z^(k-1)*(modSolutions k (z^(k*t))).card) :=
        Nat.mul_le_mul (hi t) hl
      _ = (D*z^(k-1))*((modSolutions k (A^t)).card*(modSolutions k (z^(k*t))).card) := by ring
      _ ≤ (D*z^(k-1))*(modSolutions k (A^t*z^(k*t))).card := Nat.mul_le_mul_left _ hc
      _ = _ := by rw [he,hD]

lemma count_from_bounded_primes (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpk : ∀ i, ¬p i ∣ k) (hroot : ∀ i, ∃ seed : ℕ, p i ∣ 1+seed^k)
    (hbound : ∀ i, p i ≤ (r+1)^2) :
    ∃ n : ℕ, n < 2^((k+4*k^3)*(r+1)^(2*k)) ∧
      2^r < representationCount k n := by
  classical
  let b := r+1
  let L := b^(2*(k-1))
  let t := 2*k*L
  let A := ∏ i, p i^k
  let D := ∏ i, p i^(k-1)
  let q := A^t
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hL : 1 ≤ L := one_le_pow₀ hb
  have hApos : 0 < A := Finset.prod_pos (fun i _ ↦ pow_pos (hp i).pos _)
  have hq : 0 < q := pow_pos hApos _
  have hD : D ≤ L^r := by
    have hh := Finset.prod_le_pow_card (Finset.univ : Finset (Fin r))
      (fun i ↦ p i^(k-1)) L (fun i _ ↦ by
        simpa only [L,b,← pow_mul] using Nat.pow_le_pow_left (hbound i) (k-1))
    simpa only [L,b,pow_mul,Finset.card_univ,Fintype.card_fin] using hh
  have hl := normalized_finite_primes k hk r p hp hinj hpk hroot t
  have hstrict : D*k*2^r < (t+1)^r := by
    have hkr : k ≤ k^r := Nat.le_pow (by omega)
    calc
      _ ≤ L^r*k^r*2^r := Nat.mul_le_mul_right _ (Nat.mul_le_mul hD hkr)
      _ = t^r := by dsimp [t]; rw [mul_pow,mul_pow]; ring
      _ < _ := Nat.pow_lt_pow_left (by omega) (by omega)
  have hex : ∃ n < k*q^k, 2^r < representationCount k n := by
    by_contra hn
    push_neg at hn
    have hu := modular_upper k q (2^r) (by omega) hq hn
    have hh : (t+1)^r*q^(k-1) ≤ (D*k*2^r)*q^(k-1) := by
      calc
        _ ≤ D*(modSolutions k q).card := hl
        _ ≤ D*(2^r*(k*q^(k-1))) := Nat.mul_le_mul_left _ hu
        _ = _ := by ring
    exact (not_lt_of_ge hh)
      (Nat.mul_lt_mul_of_pos_right hstrict (pow_pos hq _))
  obtain ⟨n,hn,hcount⟩ := hex
  refine ⟨n,hn.trans_le ?_,hcount⟩
  have hA : A ≤ b^(2*k*r) := by
    have hh := Finset.prod_le_pow_card (Finset.univ : Finset (Fin r))
      (fun i ↦ p i^k) ((b^2)^k) (fun i _ ↦ Nat.pow_le_pow_left (hbound i) k)
    simpa only [← pow_mul,Finset.card_univ,Fintype.card_fin] using hh
  have hpow : b^2*b^(2*(k-1)) = b^(2*k) := by
    rw [← pow_add]
    congr 1
    omega
  have hE : b*(2*k*r*(t*k)) ≤ 4*k^3*b^(2*k) := by
    calc
      _ = 4*k^3*(r*b)*b^(2*(k-1)) := by dsimp [t,L]; ring
      _ ≤ 4*k^3*(b*b)*b^(2*(k-1)) := by gcongr; dsimp [b]; omega
      _ = 4*k^3*(b^2*b^(2*(k-1))) := by ring
      _ = _ := by rw [hpow]
  have hqbound : q^k ≤ 2^(4*k^3*b^(2*k)) := by
    calc
      _ = A^(t*k) := (pow_mul A t k).symm
      _ ≤ (b^(2*k*r))^(t*k) := Nat.pow_le_pow_left hA _
      _ = b^(2*k*r*(t*k)) := (pow_mul _ _ _).symm
      _ ≤ (2^b)^(2*k*r*(t*k)) :=
        Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
      _ = 2^(b*(2*k*r*(t*k))) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hE
  calc
    k*q^k ≤ 2^k*2^(4*k^3*b^(2*k)) :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le hqbound
    _ = 2^(k+4*k^3*b^(2*k)) := (pow_add _ _ _).symm
    _ ≤ 2^((k+4*k^3)*b^(2*k)) := by
      apply Nat.pow_le_pow_right (by omega)
      have hh : 1 ≤ b^(2*k) := one_le_pow₀ hb
      nlinarith
    _ = _ := rfl

/-- Infinitely far out, exponential counts occur at heights with logarithm
bounded by a fixed polynomial in the indexing parameter. -/
theorem superlog_height_family (k : ℕ) (hk : 2 ≤ k) :
    ∀ R : ℕ, ∃ r n : ℕ, R ≤ r ∧
      n < 2^((k+4*k^3)*(r+1)^(2*k)) ∧ 2^r < representationCount k n := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  let P : ℕ → Prop := fun p ↦ p.Prime ∧ (p : ZMod (2*k))=1
  have hP : {p | P p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod isUnit_one
  intro R
  obtain ⟨r,hr,hpr⟩ := PrimeAPGrowth.nth_prime_ap_le_square_frequently
    (2*k) 1 isUnit_one (max R 1)
  let p : Fin r → ℕ := fun i ↦ Nat.nth P i.val
  have hp (i : Fin r) : (p i).Prime := (Nat.nth_mem_of_infinite hP i.val).1
  have hi : Function.Injective p := (Nat.nth_injective hP).comp Fin.val_injective
  have hg (i : Fin r) : ¬ p i ∣ k ∧ ∃ seed : ℕ, p i ∣ 1+seed^k :=
    PrimeAPGrowth.root_of_prime_one_mod k (p i) (by omega) (hp i)
      (Nat.nth_mem_of_infinite hP i.val).2
  have hb (i : Fin r) : p i ≤ (r+1)^2 :=
    (Nat.nth_monotone hP (Nat.le_of_lt i.isLt)).trans hpr
  obtain ⟨n,hn,hcount⟩ := count_from_bounded_primes k r hk (by omega) p hp hi
    (fun i ↦ (hg i).1) (fun i ↦ (hg i).2) hb
  exact ⟨r,n,by omega,hn,hcount⟩

lemma infinite_exp_log_root_of_heights (f : ℕ → ℕ) (K D : ℕ)
    (hK : 0 < K) (hD : 0 < D)
    (h : ∀ R : ℕ, ∃ r n : ℕ, R ≤ r ∧
      n < 2^(K*(r+1)^D) ∧ 2^r < f n) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ))^(1/(D : ℝ))) < f n}.Infinite := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let B : ℝ := ((K : ℝ)*Real.log 2)^(1/(D : ℝ))
  have hB : 0 < B := Real.rpow_pos_of_pos (by positivity) _
  let c : ℝ := Real.log 2/(4*B)
  have hc : 0 < c := div_pos hlog (by positivity)
  refine ⟨c,hc,?_⟩
  intro hfinite
  obtain ⟨M,hM⟩ := (hfinite.image f).bddAbove
  obtain ⟨r,n,hr,hn,hcount⟩ := h (M+1)
  have hr1 : 1 ≤ r := by omega
  have hnlog : Real.log (n : ℝ) ≤
      ((K : ℝ)*Real.log 2)*((r+1 : ℕ) : ℝ)^D := by
    by_cases hn0 : n=0
    · simp only [hn0,Nat.cast_zero,Real.log_zero]
      positivity
    · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hnr : (n : ℝ) < (2 : ℝ)^(K*(r+1)^D) := by exact_mod_cast hn
      have hh := Real.log_lt_log hnp hnr
      rw [Real.log_pow,Nat.cast_mul,Nat.cast_pow] at hh
      nlinarith
  have hroot : (Real.log (n : ℝ))^(1/(D : ℝ)) ≤ B*((r+1 : ℕ) : ℝ) := by
    have hh := Real.rpow_le_rpow (Real.log_natCast_nonneg n) hnlog
      (show (0 : ℝ) ≤ 1/(D : ℝ) by positivity)
    have he : ((((r+1 : ℕ) : ℝ)^D)^(1/(D : ℝ))) = ((r+1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
      rw [mul_one_div_cancel hd,Real.rpow_one]
    rw [Real.mul_rpow (by positivity) (by positivity),he] at hh
    exact hh
  have hexp : c*(Real.log (n : ℝ))^(1/(D : ℝ)) < (r : ℝ)*Real.log 2 := by
    calc
      _ ≤ c*(B*((r+1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hroot hc.le
      _ = Real.log 2*((r+1 : ℕ) : ℝ)/4 := by dsimp [c]; field_simp
      _ < _ := by
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        push_cast
        nlinarith
  have hmem : n ∈ {n : ℕ | Real.exp (c*(Real.log (n : ℝ))^(1/(D : ℝ))) < f n} := by
    change Real.exp (c*(Real.log (n : ℝ))^(1/(D : ℝ))) < f n
    calc
      _ < Real.exp ((r : ℝ)*Real.log 2) := Real.exp_lt_exp.mpr hexp
      _ = ((2^r : ℕ) : ℝ) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]; norm_cast
      _ < _ := by exact_mod_cast hcount
  have hmax : f n ≤ M := hM (Set.mem_image_of_mem f hmem)
  have hpow : r < 2^r := Nat.lt_two_pow_self
  omega

/-- A stretched-exponential-in-log lower bound at every exponent k≥2.
This remains subpolynomial in n and does not settle erdos_322. -/
theorem stretched_exponential_log_growth (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ))^(1/(2*(k : ℝ)))) <
        representationCount k n}.Infinite := by
  have hh := infinite_exp_log_root_of_heights (representationCount k)
    (k+4*k^3) (2*k) (by omega) (by omega) (superlog_height_family k hk)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

end SuperLogLower

/- Uniform lifting and finite-field energy strengthen the lower bound
further, to exp(c log(n)/loglog(n)). The effective exponent still tends to
zero; the original fixed-power conjecture below remains unresolved. -/
namespace UniformLocalLower
open UniversalModularLower Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma root_lift_at_residue (p k a c e : ℕ) (hp : p.Prime)
    (hpk : ¬p ∣ k) (hpa : ¬p ∣ a) (he : 0 < e) (hc : p ∣ a^k+c) :
    ∃ x : ℕ, x < p^e ∧ p^e ∣ x^k+c ∧ x%p=a%p := by
  letI : Fact p.Prime := ⟨hp⟩
  let f : ℤ[X] := X^k+C (c : ℤ)
  have heval : f.aeval (a : ℤ_[p]) = ((a^k+c : ℕ) : ℤ_[p]) := by simp [f]
  have hderiv : f.derivative.aeval (a : ℤ_[p]) =
      (k : ℤ_[p])*(a : ℤ_[p])^(k-1) := by simp [f,derivative_X_pow]
  have hdnorm : ‖f.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    rw [hderiv,norm_mul,norm_pow,PadicInt.norm_natCast_eq_one_iff.mpr
      (hp.coprime_iff_not_dvd.mpr hpk),PadicInt.norm_natCast_eq_one_iff.mpr
      (hp.coprime_iff_not_dvd.mpr hpa),one_pow,mul_one]
  have hsmall : ‖f.aeval (a : ℤ_[p])‖ < ‖f.derivative.aeval (a : ℤ_[p])‖^2 := by
    rw [hdnorm,one_pow,heval,PadicInt.norm_natCast_lt_one_iff]
    exact hc
  obtain ⟨z,hz,hclose,_⟩ := hensels_lemma hsmall
  rw [hdnorm] at hclose
  obtain ⟨w,hw⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp hclose
  have hzero : z^k+(c : ℤ_[p])=0 := by simpa [f] using hz
  let r : ZMod (p^e) := PadicInt.toZModPow e z
  refine ⟨r.val,ZMod.val_lt _,?_,?_⟩
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hh := congrArg (PadicInt.toZModPow e) hzero
    simpa only [map_add,map_pow,map_natCast,map_zero,ZMod.natCast_zmod_val,
      Nat.cast_add,Nat.cast_pow] using hh
  · have hh := congrArg (PadicInt.toZModPow e) hw
    simp only [map_sub,map_mul,map_natCast] at hh
    let g := ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p)
    have hg := congrArg g hh
    have hr : g r = (r.val : ZMod p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val r]
      exact map_natCast g r.val
    change g (r-(a : ZMod (p^e))) = g ((p : ZMod (p^e))*PadicInt.toZModPow e w) at hg
    simp only [map_sub,map_mul,map_natCast,hr,ZMod.natCast_self,zero_mul,sub_eq_zero] at hg
    have hv := congrArg ZMod.val hg
    simpa only [ZMod.val_natCast] using hv

noncomputable def firstUnitSolutions (d p q : ℕ) : Finset (Fin (d+1) → Fin q) := by
  classical
  exact (modSolutions (d+1) q).filter (fun a ↦ ¬p ∣ (a 0 : ℕ))

lemma primitive_lifts (d p e : ℕ) (hp : p.Prime) (hpk : ¬p ∣ d+1) :
    (firstUnitSolutions d p p).card*p^(e*d) ≤
      (firstUnitSolutions d p (p^(e+1))).card := by
  classical
  let s := firstUnitSolutions d p p
  let T := s × (Fin d → Fin (p^e))
  let free (b : T) (i : Fin d) : ℕ := p*(b.2 i : ℕ)+(b.1.val i.succ : ℕ)
  have hfree (b : T) (i : Fin d) : free b i < p^(e+1) := by
    have hb := (b.2 i).isLt
    have ha := (b.1.val i.succ).isLt
    dsimp [free]
    rw [pow_succ']
    nlinarith
  have hmod (b : T) : p ∣ (b.1.val 0 : ℕ)^(d+1)+∑ i, free b i^(d+1) := by
    have hs := (mem_modSolutions _ _ b.1.val).mp (Finset.mem_filter.mp b.1.property).1
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hs
    push_cast at hh ⊢
    simpa [free,Fin.sum_univ_succ] using hh
  have hunit (b : T) : ¬p ∣ (b.1.val 0 : ℕ) := (Finset.mem_filter.mp b.1.property).2
  choose x hxlt hxdiv hxmod using (fun b : T ↦ root_lift_at_residue p (d+1)
    (b.1.val 0 : ℕ) (∑ i, free b i^(d+1)) (e+1) hp hpk (hunit b) (by omega) (hmod b))
  let F (b : T) : Fin (d+1) → Fin (p^(e+1)) :=
    Fin.cons ⟨x b,hxlt b⟩ (fun i ↦ ⟨free b i,hfree b i⟩)
  have hF (b : T) : F b ∈ firstUnitSolutions d p (p^(e+1)) := by
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · rw [mem_modSolutions,Fin.sum_univ_succ]
      exact hxdiv b
    · change ¬p ∣ x b
      intro hd
      apply hunit b
      apply Nat.dvd_of_mod_eq_zero
      rw [← hxmod b]
      exact Nat.mod_eq_zero_of_dvd hd
  have hrecover (b : T) (i : Fin (d+1)) : (F b i : ℕ)%p=(b.1.val i : ℕ) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [F,Fin.cons_zero,Nat.mod_eq_of_lt (b.1.val 0).isLt] using hxmod b
    · simp [F,free,Nat.add_mod,Nat.mod_eq_of_lt (b.1.val j.succ).isLt]
  have hinj : Function.Injective F := by
    intro b c he
    have ha : b.1=c.1 := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      rw [← hrecover b i,← hrecover c i]
      exact congrArg (fun t : Fin (p^(e+1)) ↦ (t : ℕ)%p) (congrFun he i)
    have hb : b.2=c.2 := by
      funext i
      apply Fin.ext
      have hh : free b i=free c i := congrArg Fin.val (congrFun he i.succ)
      dsimp [free] at hh
      rw [ha] at hh
      exact Nat.eq_of_mul_eq_mul_left hp.pos (Nat.add_right_cancel hh)
    exact Prod.ext ha hb
  have hc := Finset.card_le_card_of_injOn (s := Finset.univ) F
    (fun b _ ↦ hF b) (fun b _ c _ he ↦ hinj he)
  simpa only [Finset.card_univ,T,Fintype.card_prod,Fintype.card_coe,
    Fintype.card_fun,Fintype.card_fin,← pow_mul,s] using hc

lemma even_mod_count (d p : ℕ) (hd : 0 < d) (hp : p.Prime)
    (seed : ℕ) (hseed : p ∣ 1+seed^(d+d)) :
    p^(d+d-1) ≤ (modSolutions (d+d) p).card := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let lam : ZMod p := seed
  have hlam : lam^(d+d) = -1 := by
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hseed
    push_cast at hh
    dsimp [lam]
    exact eq_neg_of_add_eq_zero_right hh
  have hlam0 : lam ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by omega : d+d ≠ 0)] at hlam
    have hh := neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)
    exact hh hlam.symm
  let norm (a : Fin d → Fin p) : ZMod p := ∑ i, (a i : ZMod p)^(d+d)
  let fiber (z : ZMod p) := {a : Fin d → Fin p // norm a=z}
  let S := Σ z : ZMod p, fiber z × fiber z
  let F (u : S) : Fin (d+d) → Fin p := Fin.append u.2.1.val
    (fun i ↦ ⟨(lam*(u.2.2.val i : ZMod p)).val,ZMod.val_lt _⟩)
  have hF (u : S) : F u ∈ modSolutions (d+d) p := by
    rw [mem_modSolutions]
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    simp only [F,Fin.sum_univ_add,Fin.append_left,Fin.append_right,ZMod.natCast_zmod_val,
      mul_pow,← Finset.mul_sum,hlam]
    change norm u.2.1.val + (-1)*norm u.2.2.val=0
    rw [u.2.1.property,u.2.2.property]
    ring
  have hinj : Function.Injective F := by
    rintro ⟨z,a,b⟩ ⟨w,c,e⟩ hh
    have ha : a.val=c.val := by
      funext i
      simpa only [F,Fin.append_left] using congrFun hh (Fin.castAdd d i)
    have hb : b.val=e.val := by
      funext i
      have he := congrArg (fun t : Fin p ↦ (t : ZMod p))
        (congrFun hh (Fin.natAdd d i))
      simp only [F,Fin.append_right,ZMod.natCast_zmod_val] at he
      have he' := mul_left_cancel₀ hlam0 he
      apply Fin.ext
      have hv := congrArg ZMod.val he'
      simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (b.val i).isLt,
        Nat.mod_eq_of_lt (e.val i).isLt] using hv
    have hz : z=w := by rw [← a.property,← c.property,ha]
    subst w
    have hac : a=c := Subtype.ext ha
    have hbe : b=e := Subtype.ext hb
    subst c
    subst e
    rfl
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ) F
    (fun u _ ↦ hF u) (fun u _ v _ he ↦ hinj he)
  rw [Finset.card_univ] at hcard
  let c : ZMod p → ℕ := fun z ↦ Fintype.card (fiber z)
  have hsum : (∑ z, c z)=p^d := by
    have hh := Finset.card_eq_sum_card_fiberwise (f := norm)
      (s := Finset.univ) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,c,fiber,
      Fintype.card_subtype] using hh.symm
  have hS : Fintype.card S=∑ z, c z^2 := by
    simp only [S,Fintype.card_sigma,Fintype.card_prod,c,pow_two]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod p))) (f := c)
  rw [hsum,Finset.card_univ,ZMod.card,← hS] at hcs
  apply Nat.le_of_mul_le_mul_left (c := p) ?_ hp.pos
  calc
    p*p^(d+d-1) = p^(d+d) := by rw [← pow_succ']; congr 1; omega
    _ = (p^d)^2 := by rw [pow_add,pow_two]
    _ ≤ p*Fintype.card S := hcs
    _ ≤ _ := Nat.mul_le_mul_left p hcard

lemma first_unit_covers (d p : ℕ) (hp : 0 < p) :
    (modSolutions (d+1) p).card ≤ 1+(d+1)*(firstUnitSolutions d p p).card := by
  classical
  let s := modSolutions (d+1) p
  let C (i : Fin (d+1)) := s.filter (fun a ↦ ¬p ∣ (a i : ℕ))
  let zeroTuple : Fin (d+1) → Fin p := fun _ ↦ ⟨0,hp⟩
  have hsub : s ⊆ insert zeroTuple (Finset.univ.biUnion C) := by
    intro a ha
    by_cases hi : ∃ i, ¬p ∣ (a i : ℕ)
    · obtain ⟨i,hi⟩ := hi
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨ha,hi⟩⟩)
    · have hz : a=zeroTuple := by
        funext i
        apply Fin.ext
        exact Nat.eq_zero_of_dvd_of_lt (not_not.mp (fun h ↦ hi ⟨i,h⟩)) (a i).isLt
      rw [hz]; exact Finset.mem_insert_self _ _
  have hC (i : Fin (d+1)) : (C i).card ≤ (firstUnitSolutions d p p).card := by
    let e := Equiv.swap (0 : Fin (d+1)) i
    let F (a : Fin (d+1) → Fin p) := a ∘ e
    apply Finset.card_le_card_of_injOn F
    · intro a ha
      obtain ⟨ha,hi⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_modSolutions] at ha ⊢
        have he : (∑ j, (F a j : ℕ)^(d+1))=(∑ j, (a j : ℕ)^(d+1)) :=
          Equiv.sum_comp e (fun j ↦ (a j : ℕ)^(d+1))
        rwa [he]
      · simpa [F,e] using hi
    · intro a _ b _ he
      funext j
      have hh := congrFun he (e j)
      simpa [F,e] using hh
  calc
    s.card ≤ (insert zeroTuple (Finset.univ.biUnion C)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.biUnion C).card+1 := Finset.card_insert_le _ _
    _ ≤ (∑ i, (C i).card)+1 := Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _i : Fin (d+1), (firstUnitSolutions d p p).card)+1 :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun i _ ↦ hC i)) 1
    _ = _ := by simp; ring

lemma uniform_first_unit (d p : ℕ) (hd : 0 < d) (hp : p.Prime)
    (hcount : p^d ≤ (modSolutions (d+1) p).card) :
    p^d ≤ (2*(d+1))*(firstUnitSolutions d p p).card := by
  have hh := first_unit_covers d p hp.pos
  have hp2 : 2 ≤ p^d := hp.two_le.trans (Nat.le_pow hd)
  have hfirst : 1 ≤ (firstUnitSolutions d p p).card := by
    by_contra hz
    have hzero : (firstUnitSolutions d p p).card=0 := by omega
    rw [hzero,mul_zero,add_zero] at hh
    omega
  have hmul : 1 ≤ (d+1)*(firstUnitSolutions d p p).card := by nlinarith
  nlinarith

lemma uniform_primitive_lower (d p e : ℕ) (hd : 0 < d) (hp : p.Prime)
    (hpk : ¬p ∣ d+1) (hcount : p^d ≤ (modSolutions (d+1) p).card) :
    p^((e+1)*d) ≤ (2*(d+1))*(firstUnitSolutions d p (p^(e+1))).card := by
  calc
    _ = p^d*p^(e*d) := by rw [← pow_add]; congr 1; ring
    _ ≤ ((2*(d+1))*(firstUnitSolutions d p p).card)*p^(e*d) :=
      Nat.mul_le_mul_right _ (uniform_first_unit d p hd hp hcount)
    _ = (2*(d+1))*((firstUnitSolutions d p p).card*p^(e*d)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (primitive_lifts d p e hp hpk)

theorem normalized_uniform_local (d p t : ℕ) (hd : 0 < d) (hp : p.Prime)
    (hpk : ¬p ∣ d+1) (hcount : p^d ≤ (modSolutions (d+1) p).card) :
    (t+1)*(p^((d+1)*t))^d ≤ (2*(d+1))*(modSolutions (d+1) (p^((d+1)*t))).card := by
  classical
  induction t with
  | zero => simp [modSolutions]; omega
  | succ t ih =>
    let s := modSolutions (d+1) (p^((d+1)*(t+1)))
    let a := s.filter (fun a ↦ ∀ i, p ∣ (a i : ℕ))
    let b := firstUnitSolutions d p (p^((d+1)*(t+1)))
    have had := dilated_lower (d+1) p (p^((d+1)*t)) (by omega) hp.pos (pow_pos hp.pos _)
    have he : p^((d+1)*t)*p^(d+1)=p^((d+1)*(t+1)) := by
      rw [← pow_add,Nat.mul_add,Nat.mul_one]
    rw [he] at had
    have ha : p^((d+1)*d)*(modSolutions (d+1) (p^((d+1)*t))).card ≤ a.card := by
      simpa only [Nat.add_sub_cancel] using had
    have hb := uniform_primitive_lower d p ((d+1)*(t+1)-1) hd hp hpk hcount
    have hpos : 0 < (d+1)*(t+1) := by positivity
    have hsub : (d+1)*(t+1)-1+1=(d+1)*(t+1) := by omega
    rw [hsub] at hb
    have hb' : (p^((d+1)*(t+1)))^d ≤ (2*(d+1))*b.card := by
      simpa only [← pow_mul] using hb
    have hdis : Disjoint a b := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_filter.mp hy).2 ((Finset.mem_filter.mp hx).2 0)
    have hcard : a.card+b.card ≤ s.card := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hpow : p^((d+1)*d)*(p^((d+1)*t))^d=(p^((d+1)*(t+1)))^d := by
      simp only [← pow_mul,← pow_add]
      congr 1
      ring
    calc
      _ = p^((d+1)*d)*((t+1)*(p^((d+1)*t))^d)+(p^((d+1)*(t+1)))^d := by
        rw [mul_left_comm (p^((d+1)*d)) (t+1),hpow]
        ring
      _ ≤ p^((d+1)*d)*((2*(d+1))*(modSolutions (d+1) (p^((d+1)*t))).card)+
          (2*(d+1))*b.card := Nat.add_le_add (Nat.mul_le_mul_left _ ih) hb'
      _ = (2*(d+1))*(p^((d+1)*d)*(modSolutions (d+1) (p^((d+1)*t))).card+b.card) := by ring
      _ ≤ (2*(d+1))*(a.card+b.card) := Nat.mul_le_mul_left _ (Nat.add_le_add_right ha _)
      _ ≤ _ := Nat.mul_le_mul_left _ hcard

theorem even_normalized_local (k p t : ℕ) (hk : 2 ≤ k) (heven : Even k)
    (hp : p.Prime) (hpk : ¬p ∣ k) (seed : ℕ) (hseed : p ∣ 1+seed^k) :
    (t+1)*(p^(k*t))^(k-1) ≤ (2*k)*(modSolutions k (p^(k*t))).card := by
  have hcount : p^(k-1) ≤ (modSolutions k p).card := by
    obtain ⟨d,rfl⟩ := heven
    exact even_mod_count d p (by omega) hp seed hseed
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
  have he : k=(d+1)+1 := by omega
  clear hd
  subst k
  have hsub : d+1+1-1=d+1 := by omega
  rw [hsub] at hcount ⊢
  exact normalized_uniform_local (d+1) p t (by omega) hp hpk hcount

end UniformLocalLower

namespace NearPowerLower
open UniversalModularLower UniformLocalLower
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma normalized_finite_primes (k C : ℕ) (_hk : 2 ≤ k) (r : ℕ)
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hlocal : ∀ i t, (t+1)*(p i^(k*t))^(k-1) ≤
      C*(modSolutions k (p i^(k*t))).card) :
    ∀ t : ℕ, (t+1)^r*((∏ i, p i^k)^t)^(k-1) ≤
      C^r*(modSolutions k ((∏ i, p i^k)^t)).card := by
  classical
  induction r with
  | zero => intro t; simp [modSolutions]
  | succ r ih =>
    let p' : Fin r → ℕ := fun i ↦ p i.castSucc
    have hi := ih p' (fun i ↦ hp i.castSucc)
      (hinj.comp (Fin.castSucc_injective r)) (fun i ↦ hlocal i.castSucc)
    let A := ∏ i, p' i^k
    let D := C^r
    let z := p (Fin.last r)
    have hz : z.Prime := hp _
    have hApos : 0 < A := Finset.prod_pos (fun i _ ↦ pow_pos (hp i.castSucc).pos _)
    have hcop : A.Coprime z := by
      apply Nat.Coprime.prod_left
      intro i _
      apply Nat.Coprime.pow_left
      apply (Nat.coprime_primes (hp i.castSucc) hz).mpr
      intro he
      have hh := hinj he
      have hh' := congrArg Fin.val hh
      have hil := i.isLt
      simp only [Fin.val_castSucc,Fin.val_last] at hh'
      omega
    intro t
    have hl : (t+1)*(z^(k*t))^(k-1) ≤ C*(modSolutions k (z^(k*t))).card :=
      hlocal (Fin.last r) t
    have hc := crt_lower k (A^t) (z^(k*t)) (pow_pos hApos _) (pow_pos hz.pos _)
      (hcop.pow t (k*t))
    have he : (∏ i, p i^k)^t=A^t*z^(k*t) := by
      rw [Fin.prod_univ_castSucc,mul_pow,pow_mul]
    have hD : C^(r+1)=D*C := pow_succ C r
    calc
      _ = ((t+1)^r*(A^t)^(k-1))*((t+1)*(z^(k*t))^(k-1)) := by
        rw [he,mul_pow,pow_succ]; ring
      _ ≤ (D*(modSolutions k (A^t)).card)*(C*(modSolutions k (z^(k*t))).card) :=
        Nat.mul_le_mul (hi t) hl
      _ = (D*C)*((modSolutions k (A^t)).card*(modSolutions k (z^(k*t))).card) := by ring
      _ ≤ (D*C)*(modSolutions k (A^t*z^(k*t))).card := Nat.mul_le_mul_left _ hc
      _ = _ := by rw [he,hD]

lemma count_from_bounded_uniform_primes (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hlocal : ∀ i t, (t+1)*(p i^(k*t))^(k-1) ≤
      (2*k)*(modSolutions k (p i^(k*t))).card)
    (hbound : ∀ i, p i ≤ (r+1)^2) :
    ∃ n : ℕ, n < (r+1)^((k+8*k^4)*(r+1)) ∧ 2^r < representationCount k n := by
  classical
  let b := r+1
  let t := 4*k^2
  let A := ∏ i, p i^k
  let q := A^t
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hApos : 0 < A := Finset.prod_pos (fun i _ ↦ pow_pos (hp i).pos _)
  have hq : 0 < q := pow_pos hApos _
  have hl := normalized_finite_primes k (2*k) hk r p hp hinj hlocal t
  have hstrict : (2*k)^r*k*2^r < (t+1)^r := by
    have hkr : k ≤ k^r := Nat.le_pow (by omega)
    calc
      _ ≤ (2*k)^r*k^r*2^r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkr)
      _ = t^r := by dsimp [t]; rw [← mul_pow,← mul_pow]; congr 1; ring
      _ < _ := Nat.pow_lt_pow_left (by omega) (by omega)
  have hex : ∃ n < k*q^k, 2^r < representationCount k n := by
    by_contra hn
    push_neg at hn
    have hu := modular_upper k q (2^r) (by omega) hq hn
    have hh : (t+1)^r*q^(k-1) ≤ ((2*k)^r*k*2^r)*q^(k-1) := by
      calc
        _ ≤ (2*k)^r*(modSolutions k q).card := hl
        _ ≤ (2*k)^r*(2^r*(k*q^(k-1))) := Nat.mul_le_mul_left _ hu
        _ = _ := by ring
    exact (not_lt_of_ge hh) (Nat.mul_lt_mul_of_pos_right hstrict (pow_pos hq _))
  obtain ⟨n,hn,hcount⟩ := hex
  refine ⟨n,hn.trans_le ?_,hcount⟩
  have hA : A ≤ b^(2*k*r) := by
    have hh := Finset.prod_le_pow_card (Finset.univ : Finset (Fin r))
      (fun i ↦ p i^k) ((b^2)^k) (fun i _ ↦ Nat.pow_le_pow_left (hbound i) k)
    simpa only [← pow_mul,Finset.card_univ,Fintype.card_fin] using hh
  have hqbound : q^k ≤ b^(8*k^4*r) := by
    calc
      _ = A^(t*k) := (pow_mul A t k).symm
      _ ≤ (b^(2*k*r))^(t*k) := Nat.pow_le_pow_left hA _
      _ = b^(8*k^4*r) := by rw [← pow_mul]; congr 1; dsimp [t]; ring
  have hkbound : k ≤ b^k := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hb _)
  calc
    k*q^k ≤ b^k*b^(8*k^4*r) := Nat.mul_le_mul hkbound hqbound
    _ = b^(k+8*k^4*r) := (pow_add _ _ _).symm
    _ ≤ b^((k+8*k^4)*b) := by
      apply Nat.pow_le_pow_right (by omega)
      have hrb : r ≤ b := by dsimp [b]; omega
      calc
        k+8*k^4*r ≤ k*b+8*k^4*b := Nat.add_le_add
          (Nat.le_mul_of_pos_right k (by omega)) (Nat.mul_le_mul_left _ hrb)
        _ = _ := by ring
    _ = _ := rfl

/-- Near-power heights from uniformly bounded local losses. -/
theorem even_height_family (k : ℕ) (hk : 2 ≤ k) (heven : Even k) :
    ∀ R : ℕ, ∃ r n : ℕ, R ≤ r ∧
      n < (r+1)^((k+8*k^4)*(r+1)) ∧ 2^r < representationCount k n := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  let P : ℕ → Prop := fun p ↦ p.Prime ∧ (p : ZMod (2*k))=1
  have hP : {p | P p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod isUnit_one
  intro R
  obtain ⟨r,hr,hpr⟩ := PrimeAPGrowth.nth_prime_ap_le_square_frequently
    (2*k) 1 isUnit_one (max R 1)
  let p : Fin r → ℕ := fun i ↦ Nat.nth P i.val
  have hp (i : Fin r) : (p i).Prime := (Nat.nth_mem_of_infinite hP i.val).1
  have hi : Function.Injective p := (Nat.nth_injective hP).comp Fin.val_injective
  have hg (i : Fin r) : ¬ p i ∣ k ∧ ∃ seed : ℕ, p i ∣ 1+seed^k :=
    PrimeAPGrowth.root_of_prime_one_mod k (p i) (by omega) (hp i)
      (Nat.nth_mem_of_infinite hP i.val).2
  have hlocal (i : Fin r) (t : ℕ) : (t+1)*(p i^(k*t))^(k-1) ≤
      (2*k)*(modSolutions k (p i^(k*t))).card := by
    obtain ⟨seed,hseed⟩ := (hg i).2
    exact even_normalized_local k (p i) t hk heven (hp i) (hg i).1 seed hseed
  have hb (i : Fin r) : p i ≤ (r+1)^2 :=
    (Nat.nth_monotone hP (Nat.le_of_lt i.isLt)).trans hpr
  obtain ⟨n,hn,hcount⟩ := count_from_bounded_uniform_primes k r hk (by omega) p hp hi hlocal hb
  exact ⟨r,n,by omega,hn,hcount⟩

lemma infinite_exp_log_div_max_of_heights (f : ℕ → ℕ) (C : ℕ) (hC : 0 < C)
    (h : ∀ R : ℕ, ∃ r n : ℕ, R ≤ r ∧
      n < (r+1)^(C*(r+1)) ∧ 2^r < f n) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/max 1 (Real.log (Real.log (n : ℝ))))) <
        f n}.Infinite := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2/(4*(C : ℝ))
  have hc : 0 < c := div_pos hlog (by positivity)
  refine ⟨c,hc,?_⟩
  intro hfinite
  obtain ⟨M,hM⟩ := (hfinite.image f).bddAbove
  obtain ⟨r,n,hr,hn,hcount⟩ := h (M+1)
  have hr1 : 1 ≤ r := by omega
  let b : ℝ := (r+1 : ℕ)
  have hb : 2 ≤ b := by dsimp [b]; exact_mod_cast (show 2 ≤ r+1 by omega)
  have hbpos : 0 < b := by linarith
  let L : ℝ := max 1 (Real.log (Real.log (n : ℝ)))
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := by linarith
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hnlog : Real.log (n : ℝ) ≤ (C : ℝ)*b*Real.log b := by
    by_cases hn0 : n=0
    · simp only [hn0,Nat.cast_zero,Real.log_zero]
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hnr : (n : ℝ) < b^(C*(r+1)) := by dsimp [b]; exact_mod_cast hn
      have hh := Real.log_lt_log hnp hnr
      rw [Real.log_pow,Nat.cast_mul] at hh
      exact hh.le
  have hratio : Real.log (n : ℝ)/L ≤ (C : ℝ)*b := by
    by_cases hs : Real.log (n : ℝ) ≤ b
    · calc
        _ ≤ Real.log (n : ℝ) := div_le_self (Real.log_natCast_nonneg n) hL
        _ ≤ b := hs
        _ ≤ _ := by nlinarith
    · have hbn : b ≤ Real.log (n : ℝ) := (lt_of_not_ge hs).le
      have hh : Real.log b ≤ L :=
        (Real.log_le_log hbpos hbn).trans (le_max_right _ _)
      apply (div_le_iff₀ hLpos).mpr
      exact hnlog.trans (mul_le_mul_of_nonneg_left hh (by positivity))
  have hexp : c*(Real.log (n : ℝ)/L) < (r : ℝ)*Real.log 2 := by
    calc
      _ ≤ c*((C : ℝ)*b) := mul_le_mul_of_nonneg_left hratio hc.le
      _ = Real.log 2*b/4 := by dsimp [c]; field_simp
      _ < _ := by
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        dsimp [b]
        push_cast
        nlinarith
  have hmem : n ∈ {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/
      max 1 (Real.log (Real.log (n : ℝ))))) < f n} := by
    change Real.exp (c*(Real.log (n : ℝ)/L)) < f n
    calc
      _ < Real.exp ((r : ℝ)*Real.log 2) := Real.exp_lt_exp.mpr hexp
      _ = ((2^r : ℕ) : ℝ) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]; norm_cast
      _ < _ := by exact_mod_cast hcount
  have hmax : f n ≤ M := hM (Set.mem_image_of_mem f hmem)
  have hpow : r < 2^r := Nat.lt_two_pow_self
  omega

lemma infinite_exp_log_div_loglog_of_heights (f : ℕ → ℕ) (C : ℕ) (hC : 0 < C)
    (h : ∀ R : ℕ, ∃ r n : ℕ, R ≤ r ∧
      n < (r+1)^(C*(r+1)) ∧ 2^r < f n) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
        f n}.Infinite := by
  obtain ⟨c,hc,hi⟩ := infinite_exp_log_div_max_of_heights f C hC h
  have ht : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := Filter.tendsto_atTop_atTop.mp ht 1
  refine ⟨c,hc,?_⟩
  apply (hi.diff (Finset.finite_toSet (Finset.range N))).mono
  intro n hn
  have hnN : N ≤ n := by simpa only [Finset.mem_coe,Finset.mem_range,not_lt] using hn.2
  have hh := hn.1
  simpa only [Set.mem_setOf_eq,max_eq_right (hN n hnN)] using hh

/-- A divisor-order lower bound for every even exponent. The exponent on n
implicit in this expression still tends to zero. -/
theorem even_near_power_growth (k : ℕ) (hk : 2 ≤ k) (heven : Even k) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
        representationCount k n}.Infinite :=
  infinite_exp_log_div_loglog_of_heights (representationCount k) (k+8*k^4)
    (by omega) (even_height_family k hk heven)

end NearPowerLower

namespace UniformLocalLower
open UniversalModularLower
set_option maxHeartbeats 2000000

lemma pow_surjective_of_coprime (k p : ℕ) (hk : 0 < k) (hp : p.Prime)
    (hcop : (p-1).Coprime k) :
    Function.Surjective (fun z : ZMod p ↦ z^k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc : (Nat.card (ZMod p)ˣ).Coprime k := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hcop
  have hb := hc.pow_left_bijective (G := (ZMod p)ˣ)
  intro z
  by_cases hz : z=0
  · exact ⟨0,by simp only [hz,zero_pow (by omega : k ≠ 0)]⟩
  · obtain ⟨u,hu⟩ := hb.surjective (Units.mk0 z hz)
    exact ⟨(u : ZMod p),by simpa only [Units.val_pow_eq_pow_val,Units.val_mk0] using congrArg Units.val hu⟩

lemma mod_count_of_power_surjective (d p : ℕ) (hp : 0 < p)
    (hsurj : Function.Surjective (fun z : ZMod p ↦ z^(d+1))) :
    p^d ≤ (modSolutions (d+1) p).card := by
  classical
  letI : NeZero p := ⟨by omega⟩
  choose x hx using (fun a : Fin d → Fin p ↦ hsurj (-(∑ i, (a i : ZMod p)^(d+1))))
  let F (a : Fin d → Fin p) : Fin (d+1) → Fin p :=
    Fin.cons ⟨(x a).val,ZMod.val_lt _⟩ a
  have hF (a : Fin d → Fin p) : F a ∈ modSolutions (d+1) p := by
    rw [mem_modSolutions]
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    simp only [F,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,ZMod.natCast_zmod_val,hx,neg_add_cancel]
  have hinj : Function.Injective F := by
    intro a b he
    funext i
    exact congrFun he i.succ
  have hh := Finset.card_le_card_of_injOn (s := Finset.univ) F
    (fun a _ ↦ hF a) (fun a _ b _ he ↦ hinj he)
  simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin] using hh

lemma odd_prime_two_mod (k p : ℕ) (hodd : Odd k) (hp : p.Prime)
    (hmod : (p : ZMod k)=2) :
    ¬p ∣ k ∧ (p-1).Coprime k := by
  have hcong : p ≡ 2 [MOD k] := (ZMod.natCast_eq_natCast_iff p 2 k).mp (by simpa using hmod)
  have hm : p-1 ≡ 1 [MOD k] := by
    simpa using hcong.sub (by have := hp.two_le; omega) (by decide : 1 ≤ 2) (Nat.ModEq.refl 1)
  refine ⟨?_,Nat.coprime_of_mul_modEq_one 1 (by simpa using hm)⟩
  intro hpk
  have hd2 : p ∣ 2 := (hcong.dvd_iff hpk).mp (dvd_refl p)
  have hh := Nat.dvd_gcd hd2 hpk
  rw [hodd.coprime_two_left.gcd_eq_one] at hh
  exact hp.not_dvd_one hh

theorem coprime_normalized_local (k p t : ℕ) (hk : 2 ≤ k)
    (hp : p.Prime) (hpk : ¬p ∣ k) (hcop : (p-1).Coprime k) :
    (t+1)*(p^(k*t))^(k-1) ≤ (2*k)*(modSolutions k (p^(k*t))).card := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
  have he : k=(d+1)+1 := by omega
  clear hd
  subst k
  have hsub : d+1+1-1=d+1 := by omega
  rw [hsub]
  apply normalized_uniform_local (d+1) p t (by omega) hp hpk
  exact mod_count_of_power_surjective (d+1) p hp.pos
    (pow_surjective_of_coprime _ p (by omega) hp hcop)

end UniformLocalLower

namespace NearPowerLower
open UniversalModularLower UniformLocalLower

theorem odd_height_family (k : ℕ) (hk : 2 ≤ k) (hodd : Odd k) :
    ∀ R : ℕ, ∃ r n : ℕ, R ≤ r ∧
      n < (r+1)^((k+8*k^4)*(r+1)) ∧ 2^r < representationCount k n := by
  classical
  letI : NeZero k := ⟨by omega⟩
  have hunit : IsUnit (2 : ZMod k) := (ZMod.isUnit_iff_coprime 2 k).mpr hodd.coprime_two_left
  let P : ℕ → Prop := fun p ↦ p.Prime ∧ (p : ZMod k)=2
  have hP : {p | P p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod hunit
  intro R
  obtain ⟨r,hr,hpr⟩ := PrimeAPGrowth.nth_prime_ap_le_square_frequently
    k 2 hunit (max R 1)
  let p : Fin r → ℕ := fun i ↦ Nat.nth P i.val
  have hp (i : Fin r) : (p i).Prime := (Nat.nth_mem_of_infinite hP i.val).1
  have hi : Function.Injective p := (Nat.nth_injective hP).comp Fin.val_injective
  have hg (i : Fin r) : ¬p i ∣ k ∧ (p i-1).Coprime k :=
    odd_prime_two_mod k (p i) hodd (hp i) (Nat.nth_mem_of_infinite hP i.val).2
  have hlocal (i : Fin r) (t : ℕ) : (t+1)*(p i^(k*t))^(k-1) ≤
      (2*k)*(modSolutions k (p i^(k*t))).card :=
    coprime_normalized_local k (p i) t hk (hp i) (hg i).1 (hg i).2
  have hb (i : Fin r) : p i ≤ (r+1)^2 :=
    (Nat.nth_monotone hP (Nat.le_of_lt i.isLt)).trans hpr
  obtain ⟨n,hn,hcount⟩ := count_from_bounded_uniform_primes k r hk (by omega) p hp hi hlocal hb
  exact ⟨r,n,by omega,hn,hcount⟩

/-- Uniform applicability of the divisor-order lower bound to all k≥2.
This is not a positive fixed-power bound in n. -/
theorem near_power_growth (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
        representationCount k n}.Infinite := by
  rcases Nat.even_or_odd k with heven | hodd
  · exact even_near_power_growth k hk heven
  · exact infinite_exp_log_div_loglog_of_heights (representationCount k) (k+8*k^4)
      (by omega) (odd_height_family k hk hodd)

end NearPowerLower

/--
Let $k\geq 3$ and $A\subset \mathbb{N}$ be the set of $k$th powers. What is the order of growth of $1_A^{(k)}(n)$, i.e. the number of representations of $n$ as the sum of $k$ many $k$th powers? Does there exist some $c>0$ and infinitely many $n$ such that\[1_A^{(k)}(n) >n^c?\]
-/
theorem erdos_322 :
    (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite) := by
  intro k hk
  by_cases h : k = 3
  · subst k
    exact cubic_growth_strong
  · have hk4 : 4 ≤ k := by omega
    sorry

end Erdos322
