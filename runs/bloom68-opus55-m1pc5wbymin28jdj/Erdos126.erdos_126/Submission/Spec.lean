import FormalConjecturesUtil

/-!
# Erdős Problem 126

*Reference:* [erdosproblems.com/126](https://www.erdosproblems.com/126)
-/

namespace E126

open Finset Filter

/-- signed indicator `e_a(r) = [a = r] - [a = -r]` in `ZMod m`. -/
noncomputable def ee (m : ℕ) (a : ℕ) (r : ZMod m) : ℝ :=
  (if (a : ZMod m) = r then 1 else 0) - (if (a : ZMod m) = -r then 1 else 0)

open Classical in
/-- residues `r` whose class `{r, -r}` contains two distinct elements of `A`. -/
noncomputable def RR (m : ℕ) [NeZero m] (A : Finset ℕ) : Finset (ZMod m) :=
  Finset.univ.filter (fun r => ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧
    ((a : ZMod m) = r ∨ (a : ZMod m) = -r) ∧ ((b : ZMod m) = r ∨ (b : ZMod m) = -r))

noncomputable def KK (m : ℕ) [NeZero m] (A : Finset ℕ) (a b : ℕ) : ℝ :=
  ∑ r ∈ RR m A, ee m a r * ee m b r

lemma KK_psd (m : ℕ) [NeZero m] (A : Finset ℕ) (y : ℕ → ℝ) :
    0 ≤ ∑ a ∈ A, ∑ b ∈ A, y a * y b * KK m A a b := by
  have h : ∑ a ∈ A, ∑ b ∈ A, y a * y b * KK m A a b
      = ∑ r ∈ RR m A, ((∑ a ∈ A, y a * ee m a r) ^ 2 : ℝ) := by
    have h1 : ∀ r ∈ RR m A, ((∑ a ∈ A, y a * ee m a r) ^ 2 : ℝ)
        = ∑ a ∈ A, ∑ b ∈ A, (y a * ee m a r) * (y b * ee m b r) := by
      intro r _
      rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl h1]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [KK, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [h]
  exact Finset.sum_nonneg (fun r _ => sq_nonneg _)

lemma ee_mul_ee_eq_zero_of_not_mem (m : ℕ) [NeZero m] (A : Finset ℕ) (a b : ℕ)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (r : ZMod m) (hr : r ∉ RR m A) :
    ee m a r * ee m b r = 0 := by
  classical
  by_contra hne
  have h1 : ee m a r ≠ 0 := left_ne_zero_of_mul hne
  have h2 : ee m b r ≠ 0 := right_ne_zero_of_mul hne
  apply hr
  simp only [RR, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨a, ha, b, hb, hab, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply h1
    simp [ee, hc.1, hc.2]
  · by_contra hc
    push_neg at hc
    apply h2
    simp [ee, hc.1, hc.2]

lemma ind_prod_aux {G : Type*} [AddGroup G] [DecidableEq G] (α β r : G) :
    ((if α = r then (1:ℝ) else 0) - (if α = -r then 1 else 0)) *
      ((if β = r then (1:ℝ) else 0) - (if β = -r then 1 else 0))
    = (if α = r then (if β = r then (1:ℝ) else 0) else 0)
      - (if α = r then (if β = -r then (1:ℝ) else 0) else 0)
      - (if -α = r then (if β = r then (1:ℝ) else 0) else 0)
      + (if -α = r then (if β = -r then (1:ℝ) else 0) else 0) := by
  have hneg : (α = -r) ↔ (-α = r) := by
    constructor
    · intro h; rw [h, neg_neg]
    · intro h; rw [← h, neg_neg]
  rw [show (if α = -r then (1:ℝ) else 0) = (if -α = r then (1:ℝ) else 0) from by
    simp only [hneg]]
  simp only [sub_mul, mul_sub, ite_mul, one_mul, zero_mul]
  ring

lemma sum_ee_mul_ee (m : ℕ) [NeZero m] (a b : ℕ) :
    ∑ r : ZMod m, ee m a r * ee m b r
      = 2 * ((if (a : ZMod m) = b then 1 else 0) - (if (a : ZMod m) = -(b : ZMod m) then 1 else 0)) := by
  classical
  simp only [ee]
  simp only [ind_prod_aux, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hb1 : ((b : ZMod m) = -(a : ZMod m)) ↔ ((a : ZMod m) = -(b : ZMod m)) := by
    constructor
    · intro h; rw [h, neg_neg]
    · intro h; rw [h, neg_neg]
  have hb2 : ((b : ZMod m) = - -(a : ZMod m)) ↔ ((a : ZMod m) = (b : ZMod m)) := by
    rw [neg_neg]; exact eq_comm
  have hb3 : ((b : ZMod m) = (a : ZMod m)) ↔ ((a : ZMod m) = (b : ZMod m)) := eq_comm
  simp only [hb1, hb2, hb3]
  split_ifs <;> ring

lemma KK_offdiag (m : ℕ) [NeZero m] (A : Finset ℕ) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) :
    KK m A a b = 2 * ((if (a : ZMod m) = b then 1 else 0) -
      (if (a : ZMod m) = -(b : ZMod m) then 1 else 0)) := by
  rw [← sum_ee_mul_ee]
  unfold KK
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  exact ee_mul_ee_eq_zero_of_not_mem m A a b ha hb hab r hr

lemma ee_sq_le (m : ℕ) (a : ℕ) (r : ZMod m) :
    ee m a r * ee m a r ≤ (if (a : ZMod m) = r then 1 else 0) + (if (a : ZMod m) = -r then 1 else 0) := by
  unfold ee
  split_ifs <;> norm_num

lemma KK_diag_nonneg (m : ℕ) [NeZero m] (A : Finset ℕ) (a : ℕ) : 0 ≤ KK m A a a := by
  unfold KK
  exact Finset.sum_nonneg (fun r _ => mul_self_nonneg _)

lemma KK_diag_le (m : ℕ) [NeZero m] (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
    KK m A a a ≤ 2 * (if ((a : ZMod m) ≠ -(a : ZMod m)) ∧
      (∃ b ∈ A, b ≠ a ∧ ((b : ZMod m) = a ∨ (b : ZMod m) = -(a : ZMod m))) then 1 else 0) := by
  classical
  split_ifs with hcond
  · -- bound by the full sum
    calc KK m A a a ≤ ∑ r : ZMod m, ee m a r * ee m a r := by
          unfold KK
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro r _ _; exact mul_self_nonneg _
      _ ≤ ∑ r : ZMod m, ((if (a : ZMod m) = r then 1 else 0) + (if (a : ZMod m) = -r then 1 else 0)) :=
          Finset.sum_le_sum (fun r _ => ee_sq_le m a r)
      _ = 2 * 1 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          have : ∀ r : ZMod m, ((a : ZMod m) = -r) ↔ (-(a : ZMod m) = r) := by
            intro r; constructor
            · intro h; rw [h, neg_neg]
            · intro h; rw [← h, neg_neg]
          simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          norm_num
  · -- all terms vanish
    have hz : ∀ r ∈ RR m A, ee m a r * ee m a r = 0 := by
      intro r hr
      simp only [RR, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      obtain ⟨a', ha', b', hb', hab', h1, h2⟩ := hr
      by_contra hne
      have hee : ee m a r ≠ 0 := by
        intro h; apply hne; rw [h, zero_mul]
      -- a is in {r, -r}
      have hA : (a : ZMod m) = r ∨ (a : ZMod m) = -r := by
        by_contra hc; push_neg at hc; apply hee; simp [ee, hc.1, hc.2]
      -- a ≠ -a
      have hna : (a : ZMod m) ≠ -(a : ZMod m) := by
        intro h
        apply hee
        unfold ee
        rcases hA with h' | h'
        · have : (a : ZMod m) = -r := by rw [h, h']
          rw [if_pos h', if_pos this, sub_self]
        · have : (a : ZMod m) = r := by rw [h, h', neg_neg]
          rw [if_pos h', if_pos this, sub_self]
      apply hcond
      refine ⟨hna, ?_⟩
      -- one of a', b' differs from a
      by_cases hc : a' = a
      · refine ⟨b', hb', ?_, ?_⟩
        · intro h; apply hab'; rw [hc, h]
        · rcases hA with h' | h' <;> rcases h2 with h'' | h'' <;> simp [h', h'']
      · refine ⟨a', ha', hc, ?_⟩
        rcases hA with h' | h' <;> rcases h1 with h'' | h'' <;> simp [h', h'']
    unfold KK
    rw [Finset.sum_eq_zero hz]
    norm_num

noncomputable def KK' (m : ℕ) (A : Finset ℕ) (a b : ℕ) : ℝ :=
  if h : m = 0 then 0 else @KK m ⟨h⟩ A a b

lemma KK'_eq (m : ℕ) (h : m ≠ 0) (A : Finset ℕ) (a b : ℕ) :
    KK' m A a b = @KK m ⟨h⟩ A a b := by
  unfold KK'; rw [dif_neg h]

lemma KK'_psd (m : ℕ) (A : Finset ℕ) (y : ℕ → ℝ) :
    0 ≤ ∑ a ∈ A, ∑ b ∈ A, y a * y b * KK' m A a b := by
  by_cases h : m = 0
  · simp [KK', h]
  · simp only [KK'_eq m h]
    exact @KK_psd m ⟨h⟩ A y

noncomputable def HH (p N : ℕ) (A : Finset ℕ) (a b : ℕ) : ℝ :=
  (1/2) * ∑ k ∈ Icc 1 N, KK' (p^k) A a b

lemma HH_psd (p N : ℕ) (A : Finset ℕ) (y : ℕ → ℝ) :
    0 ≤ ∑ a ∈ A, ∑ b ∈ A, y a * y b * HH p N A a b := by
  have h : ∑ a ∈ A, ∑ b ∈ A, y a * y b * HH p N A a b
      = (1/2) * ∑ k ∈ Icc 1 N, ∑ a ∈ A, ∑ b ∈ A, y a * y b * KK' (p^k) A a b := by
    rw [Finset.mul_sum]
    have e1 : ∀ a ∈ A, ∑ b ∈ A, y a * y b * HH p N A a b
        = ∑ k ∈ Icc 1 N, ∑ b ∈ A, (1/2) * (y a * y b * KK' (p^k) A a b) := by
      intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [HH, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  rw [h]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun k _ => KK'_psd _ A y)

lemma zmod_eq_iff (m a b : ℕ) : ((a : ZMod m) = (b : ZMod m)) ↔ m ∣ Int.natAbs ((a:ℤ) - b) := by
  have h1 : ((a : ZMod m) = (b : ZMod m)) ↔ (((a:ℤ) : ZMod m) = ((b:ℤ) : ZMod m)) := by
    simp only [Int.cast_natCast]
  rw [h1, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd, ← Int.natAbs_neg, neg_sub]

lemma zmod_eq_neg_iff (m a b : ℕ) : ((a : ZMod m) = -(b : ZMod m)) ↔ m ∣ a + b := by
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]

lemma sum_ind_pow_dvd (p x N : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hN : x.factorization p ≤ N) :
    ∑ k ∈ Icc 1 N, (if p^k ∣ x then (1:ℝ) else 0) = x.factorization p := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Icc 1 N).filter (fun k => p^k ∣ x) = Icc 1 (x.factorization p) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, hp.pow_dvd_iff_le_factorization hx]
    omega
  rw [this, Nat.card_Icc]
  simp

lemma natAbs_sub_le (a b : ℕ) : Int.natAbs ((a:ℤ) - b) ≤ a + b := by omega

lemma natAbs_sub_ne_zero (a b : ℕ) (h : a ≠ b) : Int.natAbs ((a:ℤ) - b) ≠ 0 := by omega

lemma HH_offdiag (p N : ℕ) (hp : p.Prime) (A : Finset ℕ) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hN : a + b ≤ N) :
    HH p N A a b = ((Int.natAbs ((a:ℤ) - b)).factorization p : ℝ) - ((a + b).factorization p : ℝ) := by
  have hpk : ∀ k, p^k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  unfold HH
  have h1 : ∀ k ∈ Icc 1 N, KK' (p^k) A a b = 2 * ((if p^k ∣ Int.natAbs ((a:ℤ) - b) then 1 else 0)
      - (if p^k ∣ a + b then 1 else 0)) := by
    intro k _
    rw [KK'_eq _ (hpk k), @KK_offdiag (p^k) ⟨hpk k⟩ A a b ha hb hab]
    simp only [zmod_eq_iff, zmod_eq_neg_iff]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hx1 : Int.natAbs ((a:ℤ) - b) ≠ 0 := natAbs_sub_ne_zero a b hab
  have hx2 : a + b ≠ 0 := by omega
  rw [sum_ind_pow_dvd p _ N hp hx1 _, sum_ind_pow_dvd p _ N hp hx2 _]
  · ring
  · exact le_trans (Nat.factorization_lt p hx2).le hN
  · have := Nat.factorization_lt p hx1
    have := natAbs_sub_le a b
    omega

open Classical in
noncomputable def Cset (p N : ℕ) (A : Finset ℕ) (a : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun k => ¬ p^k ∣ 2 * a ∧
    ∃ b ∈ A, b ≠ a ∧ (p^k ∣ Int.natAbs ((b:ℤ) - a) ∨ p^k ∣ b + a))

lemma HH_diag_le (p N : ℕ) (hp : p.Prime) (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
    HH p N A a a ≤ (Cset p N A a).card := by
  classical
  have hpk : ∀ k, p^k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  unfold HH
  have h1 : ∀ k ∈ Icc 1 N, KK' (p^k) A a a ≤ 2 * (if (¬ p^k ∣ 2 * a ∧ ∃ b ∈ A, b ≠ a ∧
      (p^k ∣ Int.natAbs ((b:ℤ) - a) ∨ p^k ∣ b + a)) then 1 else 0) := by
    intro k _
    rw [KK'_eq _ (hpk k)]
    have := @KK_diag_le (p^k) ⟨hpk k⟩ A a ha
    have e1 : ((a : ZMod (p^k)) ≠ -(a : ZMod (p^k))) ↔ ¬ p^k ∣ 2 * a := by
      rw [Ne, zmod_eq_neg_iff, two_mul]
    simp only [e1, zmod_eq_iff, zmod_eq_neg_iff] at this
    convert this using 3
  calc (1/2) * ∑ k ∈ Icc 1 N, KK' (p^k) A a a
      ≤ (1/2) * ∑ k ∈ Icc 1 N, 2 * (if (¬ p^k ∣ 2 * a ∧ ∃ b ∈ A, b ≠ a ∧
          (p^k ∣ Int.natAbs ((b:ℤ) - a) ∨ p^k ∣ b + a)) then (1:ℝ) else 0) := by
        gcongr with k hk
        exact h1 k hk
    _ = (Cset p N A a).card := by
        rw [← Finset.mul_sum, Finset.sum_boole]
        unfold Cset
        simp only [one_div]
        rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_mul]


noncomputable def LL (a b : ℕ) : ℝ := Real.log ((a + b : ℕ) : ℝ) - Real.log ((Nat.gcd a b : ℕ) : ℝ)

lemma LL_symm (a b : ℕ) : LL a b = LL b a := by
  unfold LL; rw [add_comm, Nat.gcd_comm]

lemma D_bound (p N : ℕ) (hp : p.Prime) (A : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) (a : ℕ) (ha : a ∈ A)
    (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ : ∀ b ∈ A, b ≠ a → LL a b ≤ Δ) :
    ((Cset p N A a).card : ℝ) * Real.log p ≤ Δ := by
  classical
  rcases (Cset p N A a).eq_empty_or_nonempty with hC | hC
  · rw [hC]; simp [hΔ0]
  have hkmem : (Cset p N A a).max' hC ∈ Cset p N A a := Finset.max'_mem _ _
  have hkle : ∀ j ∈ Cset p N A a, j ≤ (Cset p N A a).max' hC := fun j hj => Finset.le_max' _ j hj
  generalize (Cset p N A a).max' hC = k at hkmem hkle
  have hkmem' := hkmem
  unfold Cset at hkmem'
  simp only [Finset.mem_filter, Finset.mem_Icc] at hkmem'
  obtain ⟨⟨hk1, hkN⟩, hndvd, b, hb, hba, hdvd⟩ := hkmem'
  have ha0 : 0 < a := hA a ha
  have hb0 : 0 < b := hA b hb
  have h2a : 2 * a ≠ 0 := by omega
  have hvk : (2 * a).factorization p < k := by
    by_contra hcon; push_neg at hcon
    exact hndvd ((hp.pow_dvd_iff_le_factorization h2a).mpr hcon)
  have hcard : (Cset p N A a).card ≤ k - (2 * a).factorization p := by
    have hsub : Cset p N A a ⊆ Ioc ((2 * a).factorization p) k := by
      intro j hj
      have hj' := hj
      unfold Cset at hj'
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj'
      simp only [Finset.mem_Ioc]
      refine ⟨?_, hkle j hj⟩
      by_contra hcon; push_neg at hcon
      exact hj'.2.1 ((hp.pow_dvd_iff_le_factorization h2a).mpr hcon)
    calc (Cset p N A a).card ≤ (Ioc ((2 * a).factorization p) k).card := Finset.card_le_card hsub
      _ = k - (2 * a).factorization p := Nat.card_Ioc _ k
  obtain ⟨X, hXdef, hXdvd⟩ : ∃ X, (X = Int.natAbs ((b:ℤ) - a) ∨ X = b + a) ∧ p^k ∣ X := by
    rcases hdvd with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hX0 : X ≠ 0 := by
    rcases hXdef with h | h
    · rw [h]; exact natAbs_sub_ne_zero b a hba
    · omega
  have hXle : X ≤ a + b := by
    rcases hXdef with h | h
    · rw [h]; have := natAbs_sub_le b a; omega
    · omega
  have hgX : Nat.gcd a b ∣ X := by
    rcases hXdef with h | h
    · rw [h, ← Int.natCast_dvd]
      exact dvd_sub (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b))
        (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b))
    · rw [h]; exact dvd_add (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b)
  have hg0 : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have hpv0 : p ^ (k - (2 * a).factorization p) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hdiv : Nat.gcd a b * p ^ (k - (2 * a).factorization p) ∣ X := by
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hg0 hpv0) hX0]
    rw [Nat.factorization_mul hg0 hpv0, hp.factorization_pow]
    intro q
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    have hgq : (Nat.gcd a b).factorization q ≤ X.factorization q :=
      (Nat.factorization_le_iff_dvd hg0 hX0).mpr hgX q
    split_ifs with hpq
    · subst hpq
      have h1 : (Nat.gcd a b).factorization p ≤ (2 * a).factorization p := by
        have : Nat.gcd a b ∣ 2 * a := dvd_mul_of_dvd_right (Nat.gcd_dvd_left a b) 2
        exact (Nat.factorization_le_iff_dvd hg0 h2a).mpr this p
      have h2 : k ≤ X.factorization p := (hp.pow_dvd_iff_le_factorization hX0).mp hXdvd
      omega
    · omega
  have hle : Nat.gcd a b * p ^ (k - (2 * a).factorization p) ≤ a + b :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hX0) hdiv) hXle
  have hlog : Real.log ((Nat.gcd a b : ℕ) : ℝ) + ((k - (2 * a).factorization p : ℕ) : ℝ) * Real.log p
      ≤ Real.log ((a + b : ℕ) : ℝ) := by
    have hpos : (0:ℝ) < ((Nat.gcd a b * p ^ (k - (2 * a).factorization p) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hg0 hpv0)
    have := Real.log_le_log hpos (Nat.cast_le.mpr hle)
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by exact_mod_cast hg0) (by exact_mod_cast hpv0),
      Real.log_pow] at this
    exact this
  have hL := hΔ b hb hba
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc ((Cset p N A a).card : ℝ) * Real.log p
      ≤ ((k - (2 * a).factorization p : ℕ) : ℝ) * Real.log p := by
        gcongr
    _ ≤ LL a b := by unfold LL; linarith
    _ ≤ Δ := hL

lemma HH_diag_bound (p N : ℕ) (hp : p.Prime) (A : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) (a : ℕ)
    (ha : a ∈ A) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ : ∀ b ∈ A, b ≠ a → LL a b ≤ Δ) :
    Real.log p * HH p N A a a ≤ Δ := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc Real.log p * HH p N A a a ≤ Real.log p * (Cset p N A a).card := by
        gcongr; exact HH_diag_le p N hp A a ha
    _ = ((Cset p N A a).card : ℝ) * Real.log p := by ring
    _ ≤ Δ := D_bound p N hp A hA a ha Δ hΔ0 hΔ

/-- the sign predicate on unit parts -/
def Pu (q u : ℕ) : Prop := if q = 2 then u % 4 = 1 else 2 * (u % q) < q

def posv (q a : ℕ) : Prop := Pu q (a / q ^ (a.factorization q))

open Classical in
noncomputable def yv (q a : ℕ) : ℝ := if posv q a then 1 else -1

lemma yv_sq (q a : ℕ) : yv q a * yv q a = 1 := by unfold yv; split_ifs <;> norm_num

lemma yv_cases (q a : ℕ) : yv q a = 1 ∨ yv q a = -1 := by unfold yv; split_ifs <;> simp

lemma resid_add (q u u' : ℕ) (hq : q.Prime) (hu : ¬ q ∣ u) (hu' : ¬ q ∣ u')
    (h : ((q : ℤ) ^ ((if q = 2 then 1 else 0) + 1)) ∣ (u:ℤ) + u') : (Pu q u ↔ ¬ Pu q u') := by
  unfold Pu
  by_cases hq2 : q = 2
  · subst hq2
    simp only [if_true] at h ⊢
    norm_num at h
    omega
  · simp only [hq2, if_false] at h ⊢
    simp only [zero_add, pow_one] at h
    have h' : q ∣ u + u' := by exact_mod_cast h
    have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
    have hr : 0 < u % q := Nat.pos_of_ne_zero (fun h0 => hu (Nat.dvd_of_mod_eq_zero h0))
    have hr1 : u % q < q := Nat.mod_lt _ hq.pos
    have hr2 : u' % q < q := Nat.mod_lt _ hq.pos
    have hsum : q ∣ u % q + u' % q := by
      have e : u % q + u' % q = (u + u') - q * (u / q + u' / q) := by
        have := Nat.div_add_mod u q
        have := Nat.div_add_mod u' q
        rw [Nat.mul_add]; omega
      rw [e]
      exact Nat.dvd_sub h' (dvd_mul_right _ _)
    obtain ⟨c, hc⟩ := hsum
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    subst hc1
    omega

lemma resid_sub (q u u' : ℕ) (hq : q.Prime) (hu : ¬ q ∣ u) (hu' : ¬ q ∣ u')
    (h : ((q : ℤ) ^ ((if q = 2 then 1 else 0) + 1)) ∣ (u:ℤ) - u') : (Pu q u ↔ Pu q u') := by
  unfold Pu
  by_cases hq2 : q = 2
  · subst hq2
    simp only [if_true] at h ⊢
    norm_num at h
    omega
  · simp only [hq2, if_false] at h ⊢
    simp only [zero_add, pow_one] at h
    have hmod : u' ≡ u [MOD q] := Nat.modEq_iff_dvd.mpr h
    unfold Nat.ModEq at hmod
    rw [hmod]

lemma val_eq (q a b j : ℕ) (hq : q.Prime) (ha : a ≠ 0) (hb : b ≠ 0) (s : ℤ) (hs : s * s = 1)
    (hj : min (a.factorization q) (b.factorization q) < j) (h : ((q : ℤ) ^ j) ∣ (a:ℤ) + s * b) :
    a.factorization q = b.factorization q := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hm : min (a.factorization q) (b.factorization q) = a.factorization q := min_eq_left hlt.le
    rw [hm] at hj
    have h1 : ((q:ℤ) ^ (a.factorization q + 1)) ∣ (a:ℤ) + s * b :=
      dvd_trans (pow_dvd_pow _ hj) h
    have h2 : q ^ (a.factorization q + 1) ∣ b := (hq.pow_dvd_iff_le_factorization hb).mpr hlt
    have h2' : ((q:ℤ) ^ (a.factorization q + 1)) ∣ s * (b:ℤ) :=
      dvd_mul_of_dvd_right (by exact_mod_cast h2) s
    have h3 : ((q:ℤ) ^ (a.factorization q + 1)) ∣ (a:ℤ) := by
      have := dvd_sub h1 h2'
      simpa using this
    have h4 : q ^ (a.factorization q + 1) ∣ a := by exact_mod_cast h3
    have := (hq.pow_dvd_iff_le_factorization ha).mp h4
    omega
  · have hm : min (a.factorization q) (b.factorization q) = b.factorization q := min_eq_right hlt.le
    rw [hm] at hj
    have h1 : ((q:ℤ) ^ (b.factorization q + 1)) ∣ (a:ℤ) + s * b :=
      dvd_trans (pow_dvd_pow _ hj) h
    have h2 : q ^ (b.factorization q + 1) ∣ a := (hq.pow_dvd_iff_le_factorization ha).mpr hlt
    have h3 : ((q:ℤ) ^ (b.factorization q + 1)) ∣ s * (b:ℤ) := by
      have := dvd_sub h1 (show ((q:ℤ) ^ (b.factorization q + 1)) ∣ (a:ℤ) by exact_mod_cast h2)
      simpa using this
    have h3' : ((q:ℤ) ^ (b.factorization q + 1)) ∣ (b:ℤ) := by
      have := dvd_mul_of_dvd_right h3 s
      rwa [← mul_assoc, hs, one_mul] at this
    have h4 : q ^ (b.factorization q + 1) ∣ b := by exact_mod_cast h3'
    have := (hq.pow_dvd_iff_le_factorization hb).mp h4
    omega

/-- dividing out the common prime power -/
lemma unit_dvd (q a b c : ℕ) (hq : q.Prime) (hab : a.factorization q = b.factorization q)
    (s : ℤ) (h : ((q : ℤ) ^ (a.factorization q + c)) ∣ (a:ℤ) + s * b) :
    ((q : ℤ) ^ c) ∣ ((a / q ^ (a.factorization q) : ℕ) : ℤ) + s * ((b / q ^ (b.factorization q) : ℕ) : ℤ) := by
  have ea := Nat.ordProj_mul_ordCompl_eq_self a q
  have eb := Nat.ordProj_mul_ordCompl_eq_self b q
  rw [← hab] at eb
  have hq0 : ((q:ℤ) ^ (a.factorization q)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
  rw [← hab]
  have e : (a:ℤ) + s * b = (q:ℤ) ^ (a.factorization q) *
      (((a / q ^ (a.factorization q) : ℕ) : ℤ) + s * ((b / q ^ (a.factorization q) : ℕ) : ℤ)) := by
    conv_lhs => rw [← ea, ← eb]
    push_cast
    ring
  rw [e, pow_add] at h
  exact (mul_dvd_mul_iff_left hq0).mp h

lemma claimA (q a b : ℕ) (hq : q.Prime) (ha : 0 < a) (hb : 0 < b)
    (hpos : posv q a ↔ posv q b) :
    (a + b).factorization q ≤ (Nat.gcd a b).factorization q + (if q = 2 then 1 else 0) := by
  by_contra hcon
  push_neg at hcon
  have hg : (Nat.gcd a b).factorization q = min (a.factorization q) (b.factorization q) := by
    rw [Nat.factorization_gcd ha.ne' hb.ne']; rfl
  set c := (if q = 2 then 1 else 0) with hc
  have hdvd : q ^ ((Nat.gcd a b).factorization q + c + 1) ∣ a + b :=
    (hq.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
  have hdvdZ : ((q:ℤ) ^ ((Nat.gcd a b).factorization q + c + 1)) ∣ (a:ℤ) + 1 * b := by
    rw [one_mul]; exact_mod_cast hdvd
  have heq : a.factorization q = b.factorization q :=
    val_eq q a b _ hq ha.ne' hb.ne' 1 (by norm_num) (by rw [← hg]; omega) hdvdZ
  have hm : (Nat.gcd a b).factorization q = a.factorization q := by
    rw [hg, heq, min_self]
  rw [hm, add_assoc] at hdvdZ
  have hu := unit_dvd q a b (c + 1) hq heq 1 hdvdZ
  rw [one_mul] at hu
  have hr := resid_add q _ _ hq (Nat.not_dvd_ordCompl hq ha.ne') (Nat.not_dvd_ordCompl hq hb.ne') hu
  unfold posv at hpos
  tauto

lemma claimB (q a b : ℕ) (hq : q.Prime) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hpos : posv q a ↔ ¬ posv q b) :
    (Int.natAbs ((a:ℤ) - b)).factorization q ≤ (Nat.gcd a b).factorization q + (if q = 2 then 1 else 0) := by
  by_contra hcon
  push_neg at hcon
  have hg : (Nat.gcd a b).factorization q = min (a.factorization q) (b.factorization q) := by
    rw [Nat.factorization_gcd ha.ne' hb.ne']; rfl
  set c := (if q = 2 then 1 else 0) with hc
  have hdvd : q ^ ((Nat.gcd a b).factorization q + c + 1) ∣ Int.natAbs ((a:ℤ) - b) :=
    (hq.pow_dvd_iff_le_factorization (natAbs_sub_ne_zero a b hab)).mpr (by omega)
  have hdvdZ : ((q:ℤ) ^ ((Nat.gcd a b).factorization q + c + 1)) ∣ (a:ℤ) + (-1) * b := by
    have : ((q ^ ((Nat.gcd a b).factorization q + c + 1) : ℕ) : ℤ) ∣ (a:ℤ) - b :=
      Int.natCast_dvd.mpr hdvd
    have e : (a:ℤ) + (-1) * b = (a:ℤ) - b := by ring
    rw [e]; exact_mod_cast this
  have heq : a.factorization q = b.factorization q :=
    val_eq q a b _ hq ha.ne' hb.ne' (-1) (by norm_num) (by rw [← hg]; omega) hdvdZ
  have hm : (Nat.gcd a b).factorization q = a.factorization q := by
    rw [hg, heq, min_self]
  rw [hm, add_assoc] at hdvdZ
  have hu := unit_dvd q a b (c + 1) hq heq (-1) hdvdZ
  have e2 : ((a / q ^ (a.factorization q) : ℕ) : ℤ) + (-1) * ((b / q ^ (b.factorization q) : ℕ) : ℤ)
      = ((a / q ^ (a.factorization q) : ℕ) : ℤ) - ((b / q ^ (b.factorization q) : ℕ) : ℤ) := by ring
  rw [e2] at hu
  have hr := resid_sub q _ _ hq (Nat.not_dvd_ordCompl hq ha.ne') (Nat.not_dvd_ordCompl hq hb.ne') hu
  unfold posv at hpos
  tauto

lemma pair_ineq (q a b : ℕ) (hq : q.Prime) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ((a + b).factorization q : ℝ) + ((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ)
      - 2 * ((Nat.gcd a b).factorization q : ℝ) - 2 * (if q = 2 then 1 else 0)
    ≤ (yv q a * yv q b) * (((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ)
      - ((a + b).factorization q : ℝ)) := by
  have hc : ((if q = 2 then 1 else 0 : ℕ) : ℝ) = (if q = 2 then 1 else 0 : ℝ) := by
    split_ifs <;> simp
  unfold yv
  by_cases h1 : posv q a <;> by_cases h2 : posv q b
  · have := claimA q a b hq ha hb (by tauto)
    have h' : ((a + b).factorization q : ℝ) ≤ ((Nat.gcd a b).factorization q : ℝ)
        + (if q = 2 then 1 else 0 : ℝ) := by
      rw [← hc]; exact_mod_cast this
    simp only [h1, h2, if_true]
    linarith
  · have := claimB q a b hq ha hb hab (by tauto)
    have h' : ((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ) ≤ ((Nat.gcd a b).factorization q : ℝ)
        + (if q = 2 then 1 else 0 : ℝ) := by
      rw [← hc]; exact_mod_cast this
    simp only [h1, h2, if_true, if_false]
    linarith
  · have := claimB q a b hq ha hb hab (by tauto)
    have h' : ((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ) ≤ ((Nat.gcd a b).factorization q : ℝ)
        + (if q = 2 then 1 else 0 : ℝ) := by
      rw [← hc]; exact_mod_cast this
    simp only [h1, h2, if_true, if_false]
    linarith
  · have := claimA q a b hq ha hb (by tauto)
    have h' : ((a + b).factorization q : ℝ) ≤ ((Nat.gcd a b).factorization q : ℝ)
        + (if q = 2 then 1 else 0 : ℝ) := by
      rw [← hc]; exact_mod_cast this
    simp only [h1, h2, if_false]
    linarith

lemma split_sum (T : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ a ∈ T, ∑ b ∈ T, g a b = ∑ a ∈ T, g a a + ∑ a ∈ T, ∑ b ∈ T.erase a, g a b := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.add_sum_erase _ _ ha]

lemma swap3 (S T : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ p ∈ S, ∑ a ∈ T, ∑ b ∈ T, F p a b = ∑ a ∈ T, ∑ b ∈ T, ∑ p ∈ S, F p a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]

lemma abstract_ineq (T S : Finset ℕ) (H : ℕ → ℕ → ℕ → ℝ) (w : ℕ → ℝ) (y : ℕ → ℕ → ℝ)
    (P Q G : ℕ → ℕ → ℝ) (c Δ : ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p)
    (hpsd : ∀ p ∈ S, ∀ z : ℕ → ℝ, 0 ≤ ∑ a ∈ T, ∑ b ∈ T, z a * z b * H p a b)
    (hy : ∀ q ∈ S, ∀ a ∈ T, y q a = 1 ∨ y q a = -1)
    (hoff : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ∑ p ∈ S, w p * H p a b = Q a b - P a b)
    (hQP : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Q a b ≤ P a b)
    (hdiag : ∀ p ∈ S, ∀ a ∈ T, w p * H p a a ≤ Δ)
    (hpair : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
       P a b + Q a b - 2 * G a b - 2 * c ≤ ∑ q ∈ S, w q * (y q a * y q b * H q a b)) :
    ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - G a b - c)
      ≤ (S.card : ℝ) * ((S.card : ℝ) * (T.card * Δ)) := by
  -- general expansion
  have expand : ∀ z : ℕ → ℝ, ∑ p ∈ S, w p * (∑ a ∈ T, ∑ b ∈ T, z a * z b * H p a b)
      = ∑ a ∈ T, z a * z a * (∑ p ∈ S, w p * H p a a)
        + ∑ a ∈ T, ∑ b ∈ T.erase a, z a * z b * (Q a b - P a b) := by
    intro z
    have e1 : ∑ p ∈ S, w p * (∑ a ∈ T, ∑ b ∈ T, z a * z b * H p a b)
        = ∑ a ∈ T, ∑ b ∈ T, z a * z b * (∑ p ∈ S, w p * H p a b) := by
      simp_rw [Finset.mul_sum]
      rw [swap3]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
        (fun b _ => Finset.sum_congr rfl (fun p _ => ?_)))
      ring
    rw [e1, split_sum]
    congr 1
    refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
    rw [hoff a ha b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm]
  have step1 : ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - Q a b) ≤ ∑ a ∈ T, ∑ p ∈ S, w p * H p a a := by
    have h0 : 0 ≤ ∑ p ∈ S, w p * (∑ a ∈ T, ∑ b ∈ T,
        (fun _ => (1:ℝ)) a * (fun _ => (1:ℝ)) b * H p a b) :=
      Finset.sum_nonneg (fun p hp => mul_nonneg (hw p hp) (hpsd p hp _))
    rw [expand] at h0
    simp only [one_mul] at h0
    have : ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - Q a b)
        = - ∑ a ∈ T, ∑ b ∈ T.erase a, (Q a b - P a b) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun b _ => ?_); ring
    linarith
  have step2q : ∀ q ∈ S, w q * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H q a b)
      ≤ ∑ a ∈ T, ∑ p ∈ S, w p * H p a a + ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - Q a b) := by
    intro q hq
    have h1 : w q * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H q a b)
        ≤ ∑ p ∈ S, w p * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H p a b) := by
      apply Finset.single_le_sum (f := fun p => w p * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H p a b))
        (fun p hp => mul_nonneg (hw p hp) (hpsd p hp _)) hq
    rw [expand] at h1
    have h2 : ∑ a ∈ T, y q a * y q a * (∑ p ∈ S, w p * H p a a)
        = ∑ a ∈ T, ∑ p ∈ S, w p * H p a a := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rcases hy q hq a ha with h | h <;> rw [h] <;> ring
    have h3 : ∑ a ∈ T, ∑ b ∈ T.erase a, y q a * y q b * (Q a b - P a b)
        ≤ ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - Q a b) := by
      apply Finset.sum_le_sum; intro a ha
      apply Finset.sum_le_sum; intro b hb
      have hb' := Finset.mem_of_mem_erase hb
      have hne := (Finset.ne_of_mem_erase hb).symm
      have := hQP a ha b hb' hne
      rcases hy q hq a ha with h | h <;> rcases hy q hq b hb' with h' | h' <;> rw [h, h'] <;> linarith
    linarith
  have step2 : ∑ q ∈ S, w q * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H q a b)
      ≤ (S.card : ℝ) * (∑ a ∈ T, ∑ p ∈ S, w p * H p a a
        + ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - Q a b)) := by
    have := Finset.sum_le_sum step2q
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have step3 : ∑ a ∈ T, ∑ p ∈ S, w p * H p a a
      + ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b + Q a b - 2 * G a b - 2 * c)
      ≤ ∑ q ∈ S, w q * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H q a b) := by
    have e1 : ∑ q ∈ S, w q * (∑ a ∈ T, ∑ b ∈ T, y q a * y q b * H q a b)
        = ∑ a ∈ T, ∑ b ∈ T, ∑ q ∈ S, w q * (y q a * y q b * H q a b) := by
      simp_rw [Finset.mul_sum]; rw [swap3]
    rw [e1, split_sum]
    apply add_le_add
    · apply le_of_eq
      refine Finset.sum_congr rfl (fun a ha => ?_)
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rcases hy q hq a ha with h | h <;> rw [h] <;> ring
    · apply Finset.sum_le_sum; intro a ha
      apply Finset.sum_le_sum; intro b hb
      exact hpair a ha b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
  have hDle : ∑ a ∈ T, ∑ p ∈ S, w p * H p a a ≤ T.card * ((S.card : ℝ) * Δ) := by
    have : ∀ a ∈ T, ∑ p ∈ S, w p * H p a a ≤ (S.card : ℝ) * Δ := by
      intro a ha
      calc ∑ p ∈ S, w p * H p a a ≤ ∑ p ∈ S, Δ := Finset.sum_le_sum (fun p hp => hdiag p hp a ha)
        _ = S.card * Δ := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ a ∈ T, ∑ p ∈ S, w p * H p a a ≤ ∑ a ∈ T, (S.card : ℝ) * Δ := Finset.sum_le_sum this
      _ = T.card * ((S.card : ℝ) * Δ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have split2 : ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b + Q a b - 2 * G a b - 2 * c)
      = 2 * ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - G a b - c)
        - ∑ a ∈ T, ∑ b ∈ T.erase a, (P a b - Q a b) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hs0 : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  rw [split2] at step3
  have h5 := mul_le_mul_of_nonneg_left step1 hs0
  have h6 := mul_le_mul_of_nonneg_left hDle hs0
  nlinarith

lemma log_eq_sum_S (x : ℕ) (S : Finset ℕ) (hx : x.primeFactors ⊆ S) :
    Real.log x = ∑ p ∈ S, (x.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · rw [Nat.support_factorization]; exact hx
  · intro p _; simp

lemma sum_S_le_log (x : ℕ) (S : Finset ℕ) :
    ∑ p ∈ S, (x.factorization p : ℝ) * Real.log p ≤ Real.log x := by
  rw [log_eq_sum_S x (S ∪ x.primeFactors) Finset.subset_union_right]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro p _ _
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem ineq_I (T S : Finset ℕ) (hT : ∀ x ∈ T, 0 < x) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (a + b).primeFactors ⊆ S)
    (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → LL a b ≤ Δ) :
    ∑ a ∈ T, ∑ b ∈ T.erase a, (LL a b - Real.log 2)
      ≤ (S.card : ℝ) * ((S.card : ℝ) * (T.card * Δ)) := by
  have hNab : ∀ a ∈ T, ∀ b ∈ T, a + b ≤ 2 * T.sup id := by
    intro a ha b hb
    have h1 : a ≤ T.sup id := Finset.le_sup (f := id) ha
    have h2 : b ≤ T.sup id := Finset.le_sup (f := id) hb
    omega
  have hoff : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ∑ p ∈ S, Real.log p * HH p (2 * T.sup id) T a b
      = (∑ p ∈ S, ((Int.natAbs ((a:ℤ) - b)).factorization p : ℝ) * Real.log p)
        - Real.log ((a + b : ℕ) : ℝ) := by
    intro a ha b hb hab
    rw [log_eq_sum_S (a + b) S (hS a ha b hb hab), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [HH_offdiag p _ (hSp p hp) T a b ha hb hab (hNab a ha b hb)]
    ring
  have hQP : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      (∑ p ∈ S, ((Int.natAbs ((a:ℤ) - b)).factorization p : ℝ) * Real.log p)
        ≤ Real.log ((a + b : ℕ) : ℝ) := by
    intro a ha b hb hab
    calc _ ≤ Real.log ((Int.natAbs ((a:ℤ) - b) : ℕ) : ℝ) := sum_S_le_log _ S
      _ ≤ Real.log ((a + b : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast Nat.pos_of_ne_zero (natAbs_sub_ne_zero a b hab)
        · exact_mod_cast natAbs_sub_le a b
  have hdiag : ∀ p ∈ S, ∀ a ∈ T, Real.log p * HH p (2 * T.sup id) T a a ≤ Δ := by
    intro p hp a ha
    exact HH_diag_bound p _ (hSp p hp) T hT a ha Δ hΔ0 (fun b hb hba => hΔ a ha b hb hba.symm)
  have hpair : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      Real.log ((a + b : ℕ) : ℝ)
        + (∑ p ∈ S, ((Int.natAbs ((a:ℤ) - b)).factorization p : ℝ) * Real.log p)
        - 2 * Real.log ((Nat.gcd a b : ℕ) : ℝ) - 2 * Real.log 2
      ≤ ∑ q ∈ S, Real.log q * (yv q a * yv q b * HH q (2 * T.sup id) T a b) := by
    intro a ha b hb hab
    have hsub : (Nat.gcd a b).primeFactors ⊆ S := by
      intro p hp
      apply hS a ha b hb hab
      have := hT a ha
      exact Nat.primeFactors_mono (Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))
        (by omega) hp
    rw [log_eq_sum_S (a + b) S (hS a ha b hb hab), log_eq_sum_S (Nat.gcd a b) S hsub]
    have h2 : ∑ q ∈ S, Real.log q * (if q = 2 then 1 else 0) ≤ Real.log 2 := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_refl _
      · exact Real.log_nonneg (by norm_num)
    have h3 : ∀ q ∈ S, Real.log q * (((a + b).factorization q : ℝ)
        + ((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ)
        - 2 * ((Nat.gcd a b).factorization q : ℝ) - 2 * (if q = 2 then 1 else 0))
        ≤ Real.log q * (yv q a * yv q b * HH q (2 * T.sup id) T a b) := by
      intro q hq
      rw [HH_offdiag q _ (hSp q hq) T a b ha hb hab (hNab a ha b hb)]
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg q)
      exact pair_ineq q a b (hSp q hq) (hT a ha) (hT b hb) hab
    have h4 := Finset.sum_le_sum h3
    have e : ∑ q ∈ S, Real.log q * (((a + b).factorization q : ℝ)
        + ((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ)
        - 2 * ((Nat.gcd a b).factorization q : ℝ) - 2 * (if q = 2 then 1 else 0))
        = ∑ q ∈ S, ((a + b).factorization q : ℝ) * Real.log q
          + ∑ q ∈ S, ((Int.natAbs ((a:ℤ) - b)).factorization q : ℝ) * Real.log q
          - 2 * ∑ q ∈ S, ((Nat.gcd a b).factorization q : ℝ) * Real.log q
          - 2 * ∑ q ∈ S, Real.log q * (if q = 2 then 1 else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      ring
    rw [e] at h4
    linarith
  have key := abstract_ineq T S (fun p a b => HH p (2 * T.sup id) T a b) (fun p => Real.log p) yv
    (fun a b => Real.log ((a + b : ℕ) : ℝ))
    (fun a b => ∑ p ∈ S, ((Int.natAbs ((a:ℤ) - b)).factorization p : ℝ) * Real.log p)
    (fun a b => Real.log ((Nat.gcd a b : ℕ) : ℝ)) (Real.log 2) Δ
    (fun p _ => Real.log_natCast_nonneg p)
    (fun p _ z => HH_psd p _ T z)
    (fun q _ a _ => yv_cases q a)
    hoff hQP hdiag hpair
  unfold LL
  exact key

lemma LL_ge_log3 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : Real.log 3 ≤ LL a b := by
  have hg0 : 0 < Nat.gcd a b := by positivity
  have h3 : 3 * Nat.gcd a b ≤ a + b := by
    obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
    obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
    have ha'0 : 0 < a' := by
      rcases Nat.eq_zero_or_pos a' with h | h
      · rw [h, mul_zero] at ha'; omega
      · exact h
    have hb'0 : 0 < b' := by
      rcases Nat.eq_zero_or_pos b' with h | h
      · rw [h, mul_zero] at hb'; omega
      · exact h
    have hne : a' ≠ b' := by
      intro h; apply hab
      calc a = Nat.gcd a b * a' := ha'
        _ = Nat.gcd a b * b' := by rw [h]
        _ = b := hb'.symm
    have e : a + b = Nat.gcd a b * (a' + b') := by
      rw [mul_add, ← ha', ← hb']
    rw [e]
    have : 3 ≤ a' + b' := by omega
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < ((3 * Nat.gcd a b : ℕ) : ℝ))
    (Nat.cast_le.mpr h3)
  rw [Nat.cast_mul, Real.log_mul (by norm_num) (by exact_mod_cast hg0.ne')] at hlog
  unfold LL
  push_cast at hlog ⊢
  linarith

lemma LL_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : 0 < LL a b := by
  have := LL_ge_log3 a b ha hb hab
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

lemma gcd_mul_gcd_dvd (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nat.gcd a b * Nat.gcd b c ∣ b * Nat.gcd a c := by
  have h1 : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha.ne'
  have h2 : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb.ne'
  have h3 : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha.ne'
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero h1 h2) (mul_ne_zero hb.ne' h3)]
  rw [Nat.factorization_mul h1 h2, Nat.factorization_mul hb.ne' h3,
    Nat.factorization_gcd ha.ne' hb.ne', Nat.factorization_gcd hb.ne' hc.ne',
    Nat.factorization_gcd ha.ne' hc.ne']
  intro q
  simp only [Finsupp.add_apply, Finsupp.inf_apply]
  omega

lemma LL_triangle (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    LL a c ≤ LL a b + LL b c := by
  have hdvd := gcd_mul_gcd_dvd a b c ha hb hc
  have hg1 : 0 < Nat.gcd a b := by positivity
  have hg2 : 0 < Nat.gcd b c := by positivity
  have hg3 : 0 < Nat.gcd a c := by positivity
  have h1 : Nat.gcd a b * Nat.gcd b c ≤ b * Nat.gcd a c := Nat.le_of_dvd (by positivity) hdvd
  have key : (a + c) * (Nat.gcd a b * Nat.gcd b c) ≤ (a + b) * (b + c) * Nat.gcd a c := by
    calc (a + c) * (Nat.gcd a b * Nat.gcd b c) ≤ (a + c) * (b * Nat.gcd a c) :=
          Nat.mul_le_mul_left _ h1
      _ = ((a + c) * b) * Nat.gcd a c := by ring
      _ ≤ ((a + b) * (b + c)) * Nat.gcd a c := Nat.mul_le_mul_right _ (by nlinarith)
  have hlog := Real.log_le_log (by positivity :
      (0:ℝ) < (((a + c) * (Nat.gcd a b * Nat.gcd b c) : ℕ) : ℝ)) (Nat.cast_le.mpr key)
  simp only [Nat.cast_mul] at hlog
  have hac : ((a + c : ℕ) : ℝ) ≠ 0 := by positivity
  have hab : ((a + b : ℕ) : ℝ) ≠ 0 := by positivity
  have hbc : ((b + c : ℕ) : ℝ) ≠ 0 := by positivity
  have hg1' : ((Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by positivity
  have hg2' : ((Nat.gcd b c : ℕ) : ℝ) ≠ 0 := by positivity
  have hg3' : ((Nat.gcd a c : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul hac (mul_ne_zero hg1' hg2'), Real.log_mul hg1' hg2',
    Real.log_mul (mul_ne_zero hab hbc) hg3', Real.log_mul hab hbc] at hlog
  unfold LL
  linarith

/-- valuation lemma for the gap argument -/
lemma VL (p t b b' : ℕ) (hp : p.Prime) (ht : 0 < t) (hb : 0 < b) (hb' : 0 < b') (hbb : b ≠ b')
    (he : (Nat.gcd t b).factorization p < (t + b).factorization p)
    (he' : (Nat.gcd t b').factorization p < (t + b').factorization p) :
    ((min ((t + b).factorization p - (Nat.gcd t b).factorization p)
         ((t + b').factorization p - (Nat.gcd t b').factorization p) : ℕ) : ℝ) * Real.log p
      < LL b b' := by
  have hg1 : (Nat.gcd t b).factorization p = min (t.factorization p) (b.factorization p) := by
    rw [Nat.factorization_gcd ht.ne' hb.ne']; rfl
  have hg2 : (Nat.gcd t b').factorization p = min (t.factorization p) (b'.factorization p) := by
    rw [Nat.factorization_gcd ht.ne' hb'.ne']; rfl
  have hdvd1 : ((p:ℤ) ^ ((t + b).factorization p)) ∣ (t:ℤ) + 1 * b := by
    rw [one_mul]; exact_mod_cast Nat.ordProj_dvd (t + b) p
  have hdvd2 : ((p:ℤ) ^ ((t + b').factorization p)) ∣ (t:ℤ) + 1 * b' := by
    rw [one_mul]; exact_mod_cast Nat.ordProj_dvd (t + b') p
  have heq1 : t.factorization p = b.factorization p :=
    val_eq p t b _ hp ht.ne' hb.ne' 1 (by norm_num) (by rw [← hg1]; exact he) hdvd1
  have heq2 : t.factorization p = b'.factorization p :=
    val_eq p t b' _ hp ht.ne' hb'.ne' 1 (by norm_num) (by rw [← hg2]; exact he') hdvd2
  have hm1 : (Nat.gcd t b).factorization p = t.factorization p := by rw [hg1, ← heq1, min_self]
  have hm2 : (Nat.gcd t b').factorization p = t.factorization p := by rw [hg2, ← heq2, min_self]
  generalize hj : min ((t + b).factorization p - (Nat.gcd t b).factorization p)
         ((t + b').factorization p - (Nat.gcd t b').factorization p) = j
  have hj1 : t.factorization p + j ≤ (t + b).factorization p := by
    have := min_le_left ((t + b).factorization p - (Nat.gcd t b).factorization p)
         ((t + b').factorization p - (Nat.gcd t b').factorization p)
    omega
  have hj2 : t.factorization p + j ≤ (t + b').factorization p := by
    have := min_le_right ((t + b).factorization p - (Nat.gcd t b).factorization p)
         ((t + b').factorization p - (Nat.gcd t b').factorization p)
    omega
  have hd1 : p ^ (t.factorization p + j) ∣ t + b :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mpr hj1
  have hd2 : p ^ (t.factorization p + j) ∣ t + b' :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mpr hj2
  have hdZ : ((p ^ (t.factorization p + j) : ℕ) : ℤ) ∣ (b:ℤ) - b' := by
    have := dvd_sub (Int.natCast_dvd_natCast.mpr hd1) (Int.natCast_dvd_natCast.mpr hd2)
    have e : (((t + b : ℕ) : ℤ) - ((t + b' : ℕ) : ℤ)) = (b:ℤ) - b' := by push_cast; ring
    rw [e] at this
    exact this
  have hdN : p ^ (t.factorization p + j) ∣ Int.natAbs ((b:ℤ) - b') := Int.natCast_dvd.mp hdZ
  have hg3 : (Nat.gcd b b').factorization p = t.factorization p := by
    rw [Nat.factorization_gcd hb.ne' hb'.ne', Finsupp.inf_apply, ← heq1, ← heq2, inf_idem]
  have hX0 := natAbs_sub_ne_zero b b' hbb
  have hgX : Nat.gcd b b' ∣ Int.natAbs ((b:ℤ) - b') := by
    rw [← Int.natCast_dvd]
    exact dvd_sub (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left b b'))
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right b b'))
  have hg0 : Nat.gcd b b' ≠ 0 := Nat.gcd_ne_zero_left hb.ne'
  have hpj0 : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hdiv : Nat.gcd b b' * p ^ j ∣ Int.natAbs ((b:ℤ) - b') := by
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hg0 hpj0) hX0]
    rw [Nat.factorization_mul hg0 hpj0, hp.factorization_pow]
    intro q
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    have hgq : (Nat.gcd b b').factorization q ≤ (Int.natAbs ((b:ℤ) - b')).factorization q :=
      (Nat.factorization_le_iff_dvd hg0 hX0).mpr hgX q
    split_ifs with hpq
    · subst hpq
      have h2 := (hp.pow_dvd_iff_le_factorization hX0).mp hdN
      omega
    · omega
  have hlt : Nat.gcd b b' * p ^ j < b + b' :=
    lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hX0) hdiv) (by omega)
  have hlog := Real.log_lt_log (by exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hg0 hpj0))
    (Nat.cast_lt.mpr hlt)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by exact_mod_cast hg0) (by exact_mod_cast hpj0),
    Real.log_pow] at hlog
  unfold LL
  linarith

lemma LL_eq_sum (t b : ℕ) (ht : 0 < t) (hb : 0 < b) (S : Finset ℕ)
    (hS : (t + b).primeFactors ⊆ S) :
    LL t b = ∑ p ∈ S, (((t + b).factorization p - (Nat.gcd t b).factorization p : ℕ) : ℝ)
      * Real.log p := by
  have hg0 : Nat.gcd t b ≠ 0 := Nat.gcd_ne_zero_left ht.ne'
  have hgd : Nat.gcd t b ∣ t + b := Nat.dvd_add (Nat.gcd_dvd_left t b) (Nat.gcd_dvd_right t b)
  have hsub : (Nat.gcd t b).primeFactors ⊆ S :=
    fun p hp => hS (Nat.primeFactors_mono hgd (by omega) hp)
  unfold LL
  rw [log_eq_sum_S (t + b) S hS, log_eq_sum_S (Nat.gcd t b) S hsub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hle : (Nat.gcd t b).factorization p ≤ (t + b).factorization p :=
    (Nat.factorization_le_iff_dvd hg0 (by omega)).mpr hgd p
  rw [Nat.cast_sub hle]
  ring

theorem gap_lemma (A S : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a + b).primeFactors ⊆ S)
    (t : ℕ) (ht : t ∈ A) (B : Finset ℕ) (hB : B ⊆ A) (htB : t ∉ B)
    (hgap : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → (S.card : ℝ) * LL b b' ≤ LL t b) :
    B.card ≤ S.card := by
  classical
  rcases B.eq_empty_or_nonempty with hBe | ⟨b0, hb0⟩
  · rw [hBe]; simp
  have ht0 := hA t ht
  have htb : ∀ b ∈ B, t ≠ b := fun b hb h => htB (h ▸ hb)
  have hSne : S.Nonempty := by
    have hb0A := hB hb0
    have h1 := hS t ht b0 hb0A (htb b0 hb0)
    have h2 : 2 ≤ t + b0 := by have := hA b0 hb0A; omega
    obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (show t + b0 ≠ 1 by omega)
    exact ⟨p, h1 (Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, by omega⟩)⟩
  have hs1 : (1:ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hex : ∀ b ∈ B, ∃ p ∈ S, ∀ p' ∈ S,
      (((t + b).factorization p' - (Nat.gcd t b).factorization p' : ℕ) : ℝ) * Real.log p'
        ≤ (((t + b).factorization p - (Nat.gcd t b).factorization p : ℕ) : ℝ) * Real.log p := by
    intro b _
    exact Finset.exists_max_image S _ hSne
  choose! pf hpfS hpfmax using hex
  -- LL t b ≤ s * e * log p
  have hbound : ∀ b ∈ B, LL t b ≤ (S.card : ℝ) *
      ((((t + b).factorization (pf b) - (Nat.gcd t b).factorization (pf b) : ℕ) : ℝ)
        * Real.log (pf b)) := by
    intro b hb
    rw [LL_eq_sum t b ht0 (hA b (hB hb)) S (hS t ht b (hB hb) (htb b hb))]
    calc _ ≤ ∑ p' ∈ S, (((t + b).factorization (pf b) - (Nat.gcd t b).factorization (pf b) : ℕ) : ℝ)
          * Real.log (pf b) := Finset.sum_le_sum (fun p' hp' => hpfmax b hb p' hp')
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- e ≥ 1
  have hepos : ∀ b ∈ B, (Nat.gcd t b).factorization (pf b) < (t + b).factorization (pf b) := by
    intro b hb
    by_contra hcon
    push_neg at hcon
    have h0 : (t + b).factorization (pf b) - (Nat.gcd t b).factorization (pf b) = 0 := by omega
    have := hbound b hb
    rw [h0] at this
    simp only [Nat.cast_zero, zero_mul, mul_zero] at this
    have := LL_pos t b ht0 (hA b (hB hb)) (htb b hb)
    linarith
  apply Finset.card_le_card_of_injOn pf
  · intro b hb; exact hpfS b hb
  · intro b hb b' hb' heq
    by_contra hne
    have hb1 : b ∈ B := hb
    have hb1' : b' ∈ B := hb'
    have hvl := VL (pf b) t b b' (hSp _ (hpfS b hb1)) ht0 (hA b (hB hb1)) (hA b' (hB hb1')) hne
      (hepos b hb1) (by rw [heq]; exact hepos b' hb1')
    have hB1 := hbound b hb1
    have hB2 := hbound b' hb1'
    rw [← heq] at hB2
    have hg1 := hgap b hb1 b' hb1' hne
    have hg2 := hgap b' hb1' b hb1 (Ne.symm hne)
    rw [LL_symm b' b] at hg2
    have hlogp : 0 ≤ Real.log (pf b) := Real.log_natCast_nonneg _
    rcases le_total ((t + b).factorization (pf b) - (Nat.gcd t b).factorization (pf b))
        ((t + b').factorization (pf b) - (Nat.gcd t b').factorization (pf b)) with hle | hle
    · rw [min_eq_left hle] at hvl
      have := mul_lt_mul_of_pos_left hvl (by linarith : (0:ℝ) < S.card)
      linarith
    · rw [min_eq_right hle] at hvl
      have := mul_lt_mul_of_pos_left hvl (by linarith : (0:ℝ) < S.card)
      linarith

theorem ball_bound (A S : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a + b).primeFactors ⊆ S)
    (x : ℕ) (hx : x ∈ A) (F : Finset ℕ) (hF : F ⊆ A) (hxF : x ∉ F) (Δ : ℝ)
    (hFx : ∀ w ∈ F, Δ ≤ 2 * LL x w) (b : ℕ) (hb : b ∈ F) :
    ((F.erase b).filter (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ)).card + 1 ≤ S.card := by
  classical
  have hbB : b ∉ (F.erase b).filter (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ) := by simp
  rw [← Finset.card_insert_of_notMem hbB]
  have hBallF : ∀ z ∈ (F.erase b).filter (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ),
      z ∈ F ∧ z ≠ b ∧ 4 * (S.card:ℝ) * LL b z ≤ Δ := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_erase] at hz
    exact ⟨hz.1.2, hz.1.1, hz.2⟩
  have hinsF : ∀ z ∈ insert b ((F.erase b).filter (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ)),
      z ∈ F := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with h | h
    · rw [h]; exact hb
    · exact (hBallF z h).1
  have hs0 : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  apply gap_lemma A S hA hSp hS x hx _ (fun z hz => hF (hinsF z hz)) (fun h => hxF (hinsF x h))
  intro c hc c' hc' hcc'
  have hcF := hinsF c hc
  have hc'F := hinsF c' hc'
  have h1 := hFx c hcF
  have hpos : ∀ y ∈ F, 0 < y := fun y hy => hA y (hF hy)
  suffices h : 2 * ((S.card : ℝ) * LL c c') ≤ Δ by linarith
  rw [Finset.mem_insert] at hc hc'
  rcases hc with hcb | hc <;> rcases hc' with hc'b | hc'
  · exact absurd (hcb.trans hc'b.symm) hcc'
  · rw [hcb]
    have h2 := (hBallF c' hc').2.2
    have hL := LL_pos b c' (hpos b hb) (hpos c' hc'F) (hBallF c' hc').2.1.symm
    nlinarith
  · rw [hc'b, LL_symm]
    have h2 := (hBallF c hc).2.2
    have hL := LL_pos b c (hpos b hb) (hpos c hcF) (hBallF c hc).2.1.symm
    nlinarith
  · have h2 := (hBallF c hc).2.2
    have h3 := (hBallF c' hc').2.2
    have htri := LL_triangle c b c' (hpos c hcF) (hpos b hb) (hpos c' hc'F)
    rw [LL_symm c b] at htri
    have hL1 := LL_pos b c (hpos b hb) (hpos c hcF) (hBallF c hc).2.1.symm
    have hL2 := LL_pos b c' (hpos b hb) (hpos c' hc'F) (hBallF c' hc').2.1.symm
    have : (S.card:ℝ) * LL c c' ≤ S.card * LL b c + S.card * LL b c' := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left htri hs0
    nlinarith

theorem F_bound (A S : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a + b).primeFactors ⊆ S)
    (x : ℕ) (hx : x ∈ A) (F : Finset ℕ) (hF : F ⊆ A) (hxF : x ∉ F) (Δ : ℝ)
    (hΔA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → LL a b ≤ Δ)
    (hFx : ∀ w ∈ F, Δ ≤ 2 * LL x w) (hs1 : 1 ≤ S.card)
    (hbig : 8 * (S.card : ℝ) * Real.log 2 ≤ Δ) :
    (F.card : ℝ) ≤ 8 * (S.card : ℝ)^3 + S.card := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs1' : (1:ℝ) ≤ S.card := by exact_mod_cast hs1
  have hΔpos : 0 < Δ := by nlinarith
  have hpos : ∀ y ∈ F, 0 < y := fun y hy => hA y (hF hy)
  -- per-b lower bound
  have hper : ∀ b ∈ F, ((F.card : ℝ) - S.card) * Δ
      ≤ 8 * (S.card : ℝ) * ∑ b' ∈ F.erase b, (LL b b' - Real.log 2) := by
    intro b hb
    have hball := ball_bound A S hA hSp hS x hx F hF hxF Δ hFx b hb
    rw [← Finset.sum_filter_add_sum_filter_not (F.erase b)
      (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ)]
    have hnear : 0 ≤ ∑ b' ∈ (F.erase b).filter (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ),
        (LL b b' - Real.log 2) := by
      apply Finset.sum_nonneg
      intro b' hb'
      rw [Finset.mem_filter, Finset.mem_erase] at hb'
      have := LL_ge_log3 b b' (hpos b hb) (hpos b' hb'.1.2) hb'.1.1.symm
      have : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
    have hfar : (((F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ))).card : ℝ) * Δ
        ≤ 8 * (S.card : ℝ) * ∑ b' ∈ (F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ)),
          (LL b b' - Real.log 2) := by
      rw [Finset.mul_sum]
      have : ∀ b' ∈ (F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ)),
          Δ ≤ 8 * (S.card : ℝ) * (LL b b' - Real.log 2) := by
        intro b' hb'
        have h := (Finset.mem_filter.mp hb').2
        push_neg at h
        nlinarith
      calc (((F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ))).card : ℝ) * Δ
          = ∑ b' ∈ (F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ)), Δ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum this
    have hcardsplit : ((F.erase b).filter (fun b' => 4 * (S.card : ℝ) * LL b b' ≤ Δ)).card
        + ((F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ))).card = F.card - 1 := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hb]
    have hF1 : 1 ≤ F.card := Finset.card_pos.mpr ⟨b, hb⟩
    have hfarcard : (F.card : ℝ) - S.card
        ≤ (((F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ))).card : ℝ) := by
      have h' : F.card ≤ ((F.erase b).filter (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ))).card
          + S.card := by omega
      have h'' : (F.card : ℝ) ≤ (((F.erase b).filter
          (fun b' => ¬ (4 * (S.card : ℝ) * LL b b' ≤ Δ))).card : ℝ) + S.card := by exact_mod_cast h'
      linarith
    have := mul_le_mul_of_nonneg_right hfarcard hΔpos.le
    have h8 : 0 ≤ 8 * (S.card : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hnear h8
    rw [mul_add]
    linarith
  have hsum : (F.card : ℝ) * (((F.card : ℝ) - S.card) * Δ)
      ≤ 8 * (S.card : ℝ) * ∑ b ∈ F, ∑ b' ∈ F.erase b, (LL b b' - Real.log 2) := by
    rw [Finset.mul_sum]
    calc (F.card : ℝ) * (((F.card : ℝ) - S.card) * Δ) = ∑ b ∈ F, ((F.card : ℝ) - S.card) * Δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hper
  have hI := ineq_I F S hpos hSp (fun a ha b hb hab => hS a (hF ha) b (hF hb) hab) Δ hΔpos.le
    (fun a ha b hb hab => hΔA a (hF ha) b (hF hb) hab)
  have h8 : 0 ≤ 8 * (S.card : ℝ) := by positivity
  have hI8 := mul_le_mul_of_nonneg_left hI h8
  rcases Nat.eq_zero_or_pos F.card with hF0 | hF0
  · rw [hF0]; simp; positivity
  have hFpos : (0:ℝ) < F.card := by exact_mod_cast hF0
  by_contra hcon
  push_neg at hcon
  have hkey : 0 < ((F.card : ℝ) - S.card - 8 * (S.card : ℝ)^3) * ((F.card : ℝ) * Δ) :=
    mul_pos (by linarith) (mul_pos hFpos hΔpos)
  nlinarith

theorem clique_bound_pos (A S : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a + b).primeFactors ⊆ S) :
    A.card ≤ 18 * S.card ^ 3 + 1 := by
  classical
  by_cases hn : A.card ≤ 1
  · omega
  push_neg at hn
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hn
  have hs1 : 1 ≤ S.card := by
    have h1 := hS u hu v hv huv
    have h2 : 2 ≤ u + v := by have := hA u hu; have := hA v hv; omega
    obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (show u + v ≠ 1 by omega)
    exact Finset.card_pos.mpr ⟨p, h1 (Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, by omega⟩)⟩
  have hOD : A.offDiag.Nonempty := ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩⟩
  obtain ⟨⟨u0, v0⟩, huv0, hmax⟩ :=
    Finset.exists_max_image A.offDiag (fun pr => LL pr.1 pr.2) hOD
  rw [Finset.mem_offDiag] at huv0
  obtain ⟨hu0, hv0, huv0'⟩ := huv0
  have hΔA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → LL a b ≤ LL u0 v0 :=
    fun a ha b hb hab => hmax (a, b) (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)
  have hΔpos : 0 < LL u0 v0 := LL_pos u0 v0 (hA u0 hu0) (hA v0 hv0) huv0'
  have hs1' : (1:ℝ) ≤ S.card := by exact_mod_cast hs1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  suffices h : (A.card : ℝ) ≤ 18 * (S.card : ℝ) ^ 3 + 1 by exact_mod_cast h
  by_cases hbig : 8 * (S.card : ℝ) * Real.log 2 ≤ LL u0 v0
  · have hFu := F_bound A S hA hSp hS u0 hu0 (A.filter (fun w => w ≠ u0 ∧ LL u0 v0 ≤ 2 * LL u0 w))
      (Finset.filter_subset _ _) (by simp) (LL u0 v0) hΔA
      (fun w hw => (Finset.mem_filter.mp hw).2.2) hs1 hbig
    have hFv := F_bound A S hA hSp hS v0 hv0 (A.filter (fun w => w ≠ v0 ∧ LL u0 v0 ≤ 2 * LL v0 w))
      (Finset.filter_subset _ _) (by simp) (LL u0 v0) hΔA
      (fun w hw => (Finset.mem_filter.mp hw).2.2) hs1 hbig
    have hcover : A ⊆ A.filter (fun w => w ≠ u0 ∧ LL u0 v0 ≤ 2 * LL u0 w)
        ∪ A.filter (fun w => w ≠ v0 ∧ LL u0 v0 ≤ 2 * LL v0 w) := by
      intro w hw
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hwu : w = u0
      · right; refine ⟨hw, ?_, ?_⟩
        · rw [hwu]; exact huv0'
        · rw [hwu, LL_symm v0 u0]; linarith
      · by_cases hwv : w = v0
        · left; refine ⟨hw, hwu, ?_⟩; rw [hwv]; linarith
        · have htri := LL_triangle u0 w v0 (hA u0 hu0) (hA w hw) (hA v0 hv0)
          rw [LL_symm w v0] at htri
          by_cases h1 : LL u0 v0 ≤ 2 * LL u0 w
          · left; exact ⟨hw, hwu, h1⟩
          · right; refine ⟨hw, hwv, ?_⟩; linarith
    have hcardN : A.card ≤ (A.filter (fun w => w ≠ u0 ∧ LL u0 v0 ≤ 2 * LL u0 w)).card
        + (A.filter (fun w => w ≠ v0 ∧ LL u0 v0 ≤ 2 * LL v0 w)).card :=
      le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
    have hcard : (A.card : ℝ) ≤ ((A.filter (fun w => w ≠ u0 ∧ LL u0 v0 ≤ 2 * LL u0 w)).card : ℝ)
        + ((A.filter (fun w => w ≠ v0 ∧ LL u0 v0 ≤ 2 * LL v0 w)).card : ℝ) := by
      exact_mod_cast hcardN
    have hs3 : (S.card : ℝ) ≤ (S.card : ℝ)^3 := le_self_pow₀ hs1' (by norm_num)
    linarith
  · push_neg at hbig
    have hI := ineq_I A S hA hSp hS (LL u0 v0) hΔpos.le hΔA
    have hL3 : 0 < Real.log 3 - Real.log 2 := by
      have := Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
      linarith
    have hlow : (A.card : ℝ) * (((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2))
        ≤ ∑ a ∈ A, ∑ b ∈ A.erase a, (LL a b - Real.log 2) := by
      have hper : ∀ a ∈ A, ((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2)
          ≤ ∑ b ∈ A.erase a, (LL a b - Real.log 2) := by
        intro a ha
        have hc : ((A.erase a).card : ℝ) = A.card - 1 := by
          rw [Finset.card_erase_of_mem ha]
          have : 1 ≤ A.card := by omega
          push_cast [Nat.cast_sub this]
          ring
        calc ((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2)
            = ∑ b ∈ A.erase a, (Real.log 3 - Real.log 2) := by
              rw [Finset.sum_const, nsmul_eq_mul, hc]
          _ ≤ _ := Finset.sum_le_sum (fun b hb => by
              have := LL_ge_log3 a b (hA a ha) (hA b (Finset.mem_of_mem_erase hb))
                (Finset.ne_of_mem_erase hb).symm
              linarith)
      calc (A.card : ℝ) * (((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2))
          = ∑ a ∈ A, ((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hper
    have hlog : 25 * Real.log 2 ≤ 17 * Real.log 3 := by
      have e1 : 25 * Real.log 2 = Real.log ((2:ℝ)^25) := by rw [Real.log_pow]; norm_num
      have e2 : 17 * Real.log 3 = Real.log ((3:ℝ)^17) := by rw [Real.log_pow]; norm_num
      rw [e1, e2]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hn0 : (0:ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
    have hs0 : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
    have hstep : (S.card : ℝ) * ((S.card : ℝ) * ((A.card : ℝ) * LL u0 v0))
        ≤ (S.card : ℝ) * ((S.card : ℝ) * ((A.card : ℝ) * (8 * (S.card : ℝ) * Real.log 2))) := by
      apply mul_le_mul_of_nonneg_left _ hs0
      apply mul_le_mul_of_nonneg_left _ hs0
      exact mul_le_mul_of_nonneg_left hbig.le hn0.le
    have h1 : (A.card : ℝ) * (((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2))
        ≤ (A.card : ℝ) * (17 * (S.card : ℝ)^3 * (Real.log 3 - Real.log 2)) := by
      have : (S.card : ℝ) * ((S.card : ℝ) * ((A.card : ℝ) * (8 * (S.card : ℝ) * Real.log 2)))
          ≤ (A.card : ℝ) * (17 * (S.card : ℝ)^3 * (Real.log 3 - Real.log 2)) := by
        have hs3 : (0:ℝ) ≤ (S.card : ℝ)^3 := by positivity
        have : (S.card : ℝ) * ((S.card : ℝ) * ((A.card : ℝ) * (8 * (S.card : ℝ) * Real.log 2)))
            = (A.card : ℝ) * ((S.card : ℝ)^3 * (8 * Real.log 2)) := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_left _ hn0.le
        have : (S.card : ℝ)^3 * (8 * Real.log 2) ≤ (S.card : ℝ)^3 * (17 * (Real.log 3 - Real.log 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hs3
        linarith
      linarith
    have h2 := le_of_mul_le_mul_left h1 hn0
    have h3 : (A.card : ℝ) - 1 ≤ 17 * (S.card : ℝ)^3 := by
      have : ((A.card : ℝ) - 1) * (Real.log 3 - Real.log 2)
          ≤ (17 * (S.card : ℝ)^3) * (Real.log 3 - Real.log 2) := by linarith
      exact le_of_mul_le_mul_right this hL3
    have hs3 : (1:ℝ) ≤ (S.card : ℝ)^3 := one_le_pow₀ hs1'
    linarith

theorem clique_bound (A S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a + b).primeFactors ⊆ S) :
    A.card ≤ 18 * S.card ^ 3 + 2 := by
  classical
  have h := clique_bound_pos (A.erase 0) S
    (fun x hx => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hx)) hSp
    (fun a ha b hb hab => hS a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
  have h2 : A.card - 1 ≤ (A.erase 0).card := Finset.pred_card_le_card_erase
  omega

theorem tendsto_of_bound (f : ℕ → ℕ) (hf : ∀ n : ℕ, (n : ℝ) ≤ 18 * (f n : ℝ)^3 + 2) :
    Tendsto (fun n => (f n : ℝ) / Real.log n) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  have hM' : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc : 0 < 1 / (36 * (max M 1)^3) := by positivity
  have hev := (Real.isLittleO_pow_log_id_atTop (n := 3)).def hc
  have hev' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hev', eventually_ge_atTop 5] with n hn hn5
  have hn5' : (5:ℝ) ≤ n := by exact_mod_cast hn5
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  rw [le_div_iff₀ hlogpos]
  have hmain : max M 1 * Real.log n ≤ f n := by
    by_contra hcon
    push_neg at hcon
    have h1 : (f n : ℝ)^3 < (max M 1 * Real.log n)^3 :=
      pow_lt_pow_left₀ hcon (Nat.cast_nonneg _) (by norm_num)
    simp only [Real.norm_eq_abs, id] at hn
    have h2 : (Real.log n)^3 ≤ 1 / (36 * (max M 1)^3) * n := by
      have habs : |(n:ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg _)
      rw [habs] at hn
      exact le_trans (le_abs_self _) hn
    have h3 : (max M 1 * Real.log n)^3 ≤ (n:ℝ) / 36 := by
      rw [mul_pow]
      calc (max M 1)^3 * (Real.log n)^3 ≤ (max M 1)^3 * (1 / (36 * (max M 1)^3) * (n:ℝ)) := by
            gcongr
        _ = (n:ℝ) / 36 := by field_simp
    have h4 := hf n
    nlinarith
  calc M * Real.log n ≤ max M 1 * Real.log n := by
        gcongr; exact le_max_left _ _
    _ ≤ f n := hmain

theorem card_bound_prod (A : Finset ℕ) :
    A.card ≤ 18 * ((∏ x ∈ A.offDiag, (x.1 + x.2)).primeFactors.card)^3 + 2 := by
  apply clique_bound A _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
  intro a ha b hb hab
  apply Nat.primeFactors_mono
  · exact Finset.dvd_prod_of_mem (fun x : ℕ × ℕ => x.1 + x.2)
      (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩ : (a, b) ∈ A.offDiag)
  · rw [Finset.prod_ne_zero_iff]
    intro x hx
    rw [Finset.mem_offDiag] at hx
    omega

end E126

open Filter

namespace Erdos126

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

theorem size_bound (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) (n : ℕ) :
    (n : ℝ) ≤ 18 * (f n : ℝ)^3 + 2 := by
  obtain ⟨_, hub⟩ := hf n
  by_contra hcon
  push_neg at hcon
  have h1 : f n + 1 ≤ f n := by
    apply hub
    intro A hA
    change f n + 1 ≤ (∏ x ∈ A.offDiag, (x.1 + x.2)).primeFactors.card
    by_contra hlt
    push_neg at hlt
    have hk := E126.card_bound_prod A
    rw [hA] at hk
    have hc : (∏ x ∈ A.offDiag, (x.1 + x.2)).primeFactors.card ≤ f n := by omega
    have hk2 : n ≤ 18 * (f n)^3 + 2 := le_trans hk (by gcongr)
    have hk3 : (n:ℝ) ≤ 18 * (f n : ℝ)^3 + 2 := by exact_mod_cast hk2
    linarith
  omega

/--
Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $|A| = n$ then
$\prod_{a\neq b\in A}(a + b)$ has at least $f(n)$ distinct prime factors.
Is it true that $\frac{f(n)}{\log n} \to\infty$?
-/
theorem erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n => f n / Real.log n) atTop atTop := by
  intro f hf
  exact E126.tendsto_of_bound f (size_bound f hf)

end Erdos126

theorem Erdos126.erdos_126.disproof : ¬ (type_of% @Erdos126.erdos_126) := sorry
