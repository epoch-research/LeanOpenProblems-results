import FormalConjectures.Util.ProblemImports

-- ===== Dev1 =====


namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Ob j x` means `x = O(p^j)` p-adically, i.e. `‖x‖ ≤ p^(-j)`. -/
def Ob (p : ℕ) [Fact p.Prime] (j : ℤ) (x : ℚ_[p]) : Prop := ‖x‖ ≤ (p : ℝ) ^ (-j)

lemma p_real_pos : (0:ℝ) < (p:ℝ) := by
  have := hp.out.pos; exact_mod_cast this

lemma p_real_one_lt : (1:ℝ) < (p:ℝ) := by
  have := hp.out.one_lt; exact_mod_cast this

lemma Ob_mono {j j' : ℤ} {x : ℚ_[p]} (h : Ob p j x) (hj : j' ≤ j) : Ob p j' x := by
  unfold Ob at *
  calc ‖x‖ ≤ (p:ℝ)^(-j) := h
    _ ≤ (p:ℝ)^(-j') := zpow_le_zpow_right₀ (le_of_lt p_real_one_lt) (by omega)

lemma Ob_zero (j : ℤ) : Ob p j (0 : ℚ_[p]) := by
  unfold Ob; simp; positivity

lemma Ob_neg {j : ℤ} {x : ℚ_[p]} (h : Ob p j x) : Ob p j (-x) := by
  unfold Ob at *; simpa using h

lemma Ob_add {j : ℤ} {x y : ℚ_[p]} (hx : Ob p j x) (hy : Ob p j y) : Ob p j (x + y) := by
  unfold Ob at *
  exact le_trans (Padic.nonarchimedean x y) (max_le hx hy)

lemma Ob_sub {j : ℤ} {x y : ℚ_[p]} (hx : Ob p j x) (hy : Ob p j y) : Ob p j (x - y) := by
  rw [sub_eq_add_neg]; exact Ob_add hx (Ob_neg hy)

lemma Ob_mul {j k : ℤ} {x y : ℚ_[p]} (hx : Ob p j x) (hy : Ob p k y) : Ob p (j + k) (x * y) := by
  unfold Ob at *
  rw [Padic.padicNormE.mul, neg_add, zpow_add₀ (ne_of_gt p_real_pos)]
  exact mul_le_mul hx hy (norm_nonneg _) (by positivity)

lemma Ob_sum {ι : Type*} (s : Finset ι) {j : ℤ} {f : ι → ℚ_[p]}
    (h : ∀ i ∈ s, Ob p j (f i)) : Ob p j (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ob_zero j
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Ob_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Ob_prod {ι : Type*} (s : Finset ι) {f : ι → ℚ_[p]}
    (h : ∀ i ∈ s, Ob p 0 (f i)) : Ob p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold Ob; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := Ob_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa using this

lemma Ob_intCast (z : ℤ) : Ob p 0 ((z : ℚ_[p])) := by
  unfold Ob; simpa using Padic.norm_int_le_one z

lemma Ob_natCast (n : ℕ) : Ob p 0 ((n : ℚ_[p])) := by
  have := Ob_intCast (p := p) (n : ℤ); simpa using this

lemma Ob_one : Ob p 0 (1 : ℚ_[p]) := by
  have := Ob_natCast (p := p) 1; simpa using this

lemma Ob_ofNat (n : ℕ) [n.AtLeastTwo] : Ob p 0 (OfNat.ofNat n : ℚ_[p]) := by
  have := Ob_natCast (p := p) n; simpa using this

lemma Ob_p_pow (n : ℕ) : Ob p n ((p : ℚ_[p]) ^ n) := by
  unfold Ob; rw [Padic.norm_p_pow]

lemma Ob_p : Ob p 1 ((p : ℚ_[p])) := by
  have := Ob_p_pow (p := p) 1; simpa using this

/-- an integer divisible by p^n is O(p^n) -/
lemma Ob_of_dvd {z : ℤ} {n : ℕ} (h : (p : ℤ)^n ∣ z) : Ob p n ((z : ℚ_[p])) := by
  unfold Ob; exact (Padic.norm_int_le_pow_iff_dvd z n).2 h

lemma Ob_of_dvd_nat {z : ℕ} {n : ℕ} (h : p^n ∣ z) : Ob p n ((z : ℚ_[p])) := by
  have : ((p:ℤ))^n ∣ (z:ℤ) := by exact_mod_cast h
  have := Ob_of_dvd (p := p) this; simpa using this

/-- a unit: integer not divisible by p has norm 1 -/
lemma norm_int_eq_one_of_not_dvd {z : ℤ} (h : ¬ (p:ℤ) ∣ z) : ‖(z : ℚ_[p])‖ = 1 := by
  have h1 := Padic.norm_int_le_one (p := p) z
  have h2 : ¬ ‖(z : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_intCast_lt_one_iff]; exact h
  exact le_antisymm h1 (not_lt.mp h2)

lemma norm_nat_eq_one_of_not_dvd {z : ℕ} (h : ¬ p ∣ z) : ‖(z : ℚ_[p])‖ = 1 := by
  have : ¬ (p:ℤ) ∣ (z:ℤ) := by exact_mod_cast h
  have := norm_int_eq_one_of_not_dvd (p := p) this; simpa using this

lemma Ob_inv_nat_of_not_dvd {z : ℕ} (h : ¬ p ∣ z) : Ob p 0 ((z : ℚ_[p])⁻¹) := by
  unfold Ob; rw [norm_inv, norm_nat_eq_one_of_not_dvd h]; simp

lemma Ob_inv_int_of_not_dvd {z : ℤ} (h : ¬ (p:ℤ) ∣ z) : Ob p 0 ((z : ℚ_[p])⁻¹) := by
  unfold Ob; rw [norm_inv, norm_int_eq_one_of_not_dvd h]; simp

lemma Ob_pow {j : ℤ} {x : ℚ_[p]} (h : Ob p j x) (n : ℕ) : Ob p (n * j) (x ^ n) := by
  induction n with
  | zero => simpa using Ob_one
  | succ n ih =>
    rw [pow_succ]
    have := Ob_mul ih h
    convert this using 1; push_cast; ring

lemma Ob_iff_norm_le {j : ℤ} {x : ℚ_[p]} : Ob p j x ↔ ‖x‖ ≤ (p:ℝ)^(-j) := Iff.rfl

/-- Ob for `p^j * y` with `y = O(1)`. -/
lemma Ob_p_pow_mul {y : ℚ_[p]} (n : ℕ) (hy : Ob p 0 y) : Ob p n ((p:ℚ_[p])^n * y) := by
  have := Ob_mul (Ob_p_pow (p := p) n) hy; simpa using this

/-- If `x = O(p^j)` with `j ≥ 0` and `y = O(1)`, then `x*y = O(p^j)`. -/
lemma Ob_mul_unit {j : ℤ} {x y : ℚ_[p]} (hx : Ob p j x) (hy : Ob p 0 y) : Ob p j (x * y) := by
  have := Ob_mul hx hy; simpa using this

lemma Ob_unit_mul {j : ℤ} {x y : ℚ_[p]} (hx : Ob p 0 x) (hy : Ob p j y) : Ob p j (x * y) := by
  have := Ob_mul hx hy; simpa using this

/-- division by p^n -/
lemma Ob_div_p_pow {j : ℤ} {x : ℚ_[p]} (hx : Ob p j x) (n : ℕ) :
    Ob p (j - n) (x / (p:ℚ_[p])^n) := by
  unfold Ob at *
  have hp0 : (0:ℝ) < (p:ℝ) := p_real_pos
  rw [norm_div, Padic.norm_p_pow, div_le_iff₀ (zpow_pos hp0 _), ← zpow_add₀ (ne_of_gt hp0)]
  convert hx using 2; ring

lemma Ob_of_eq {j : ℤ} {x y : ℚ_[p]} (hx : Ob p j x) (h : y = x) : Ob p j y := h ▸ hx

/-- Ob and equality up to O: if `x - y = O(p^j)` and `y = O(p^j)` then `x = O(p^j)`. -/
lemma Ob_of_sub {j : ℤ} {x y : ℚ_[p]} (hxy : Ob p j (x - y)) (hy : Ob p j y) : Ob p j x := by
  have := Ob_add hxy hy; simpa using this

end A357565Proof

-- ===== Dev2 =====


set_option linter.unusedSectionVars false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- indices below `m` not divisible by `p` -/
def U (p m : ℕ) : Finset ℕ := (range m).filter (fun i => ¬ p ∣ i)

lemma mem_U {m i : ℕ} : i ∈ U p m ↔ i < m ∧ ¬ p ∣ i := by
  simp [U]

lemma U_pos {m i : ℕ} (h : i ∈ U p m) : 0 < i := by
  rcases mem_U.1 h with ⟨_, h2⟩
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; exact absurd (dvd_zero p) h2
  · exact h0

lemma U_mono {m m' : ℕ} (h : m ≤ m') : U p m ⊆ U p m' := by
  intro i hi; rw [mem_U] at *; exact ⟨lt_of_lt_of_le hi.1 h, hi.2⟩

lemma sum_U_eq_sum_range {m : ℕ} (g : ℕ → ℚ_[p]) :
    ∑ i ∈ U p m, g i = ∑ i ∈ range m, if p ∣ i then 0 else g i := by
  rw [U, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p ∣ i <;> simp [h]

lemma prod_U_eq_prod_range {m : ℕ} (g : ℕ → ℚ_[p]) :
    ∏ i ∈ U p m, g i = ∏ i ∈ range m, if p ∣ i then 1 else g i := by
  rw [U, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : p ∣ i <;> simp [h]

lemma U_reflect_mem {M : ℕ} (hM : p ∣ M) : ∀ i ∈ U p M, M - i ∈ U p M := by
  intro i hi
  have hpos := U_pos hi
  rw [mem_U] at *
  obtain ⟨h1, h2⟩ := hi
  refine ⟨by omega, ?_⟩
  intro hd
  apply h2
  have := Nat.dvd_sub hM hd
  rwa [Nat.sub_sub_self h1.le] at this

/-- reflection `i ↦ M - i` on `U M` when `p ∣ M` -/
lemma sum_U_reflect {M : ℕ} (hM : p ∣ M) (g : ℕ → ℚ_[p]) :
    ∑ i ∈ U p M, g i = ∑ i ∈ U p M, g (M - i) := by
  have key : ∀ i ∈ U p M, M - i ∈ U p M := U_reflect_mem hM
  apply Finset.sum_nbij' (fun i => M - i) (fun i => M - i) key key
  · intro i hi; have := (mem_U.1 hi).1; omega
  · intro i hi; have := (mem_U.1 hi).1; omega
  · intro i hi; have := (mem_U.1 hi).1; rw [Nat.sub_sub_self this.le]

lemma prod_U_reflect {M : ℕ} (hM : p ∣ M) (g : ℕ → ℚ_[p]) :
    ∏ i ∈ U p M, g i = ∏ i ∈ U p M, g (M - i) := by
  have key : ∀ i ∈ U p M, M - i ∈ U p M := U_reflect_mem hM
  apply Finset.prod_nbij' (fun i => M - i) (fun i => M - i) key key
  · intro i hi; have := (mem_U.1 hi).1; omega
  · intro i hi; have := (mem_U.1 hi).1; omega
  · intro i hi; have := (mem_U.1 hi).1; rw [Nat.sub_sub_self this.le]

/-- splitting `U M` into the lower half and its reflection, for `M` odd, `p ∣ M` -/
lemma sum_U_half {M : ℕ} (hM : p ∣ M) (hodd : Odd M) (g : ℕ → ℚ_[p]) :
    ∑ i ∈ U p M, g i = ∑ i ∈ U p ((M+1)/2), (g i + g (M - i)) := by
  rw [Finset.sum_add_distrib]
  have hsplit := Finset.sum_filter_add_sum_filter_not (U p M) (fun i => 2 * i < M) g
  rw [← hsplit]
  have hset : (U p M).filter (fun i => 2 * i < M) = U p ((M+1)/2) := by
    ext i; simp only [Finset.mem_filter, mem_U]
    obtain ⟨t, ht⟩ := hodd
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩
  rw [hset]
  congr 1
  have key : ∀ i ∈ U p M, M - i ∈ U p M := U_reflect_mem hM
  obtain ⟨t, ht⟩ := hodd
  apply Finset.sum_nbij' (fun i => M - i) (fun i => M - i)
  · intro i hi
    simp only [Finset.mem_filter, mem_U] at hi ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hi
    refine ⟨by omega, ?_⟩
    have := key i (mem_U.2 ⟨h1, h2⟩)
    exact (mem_U.1 this).2
  · intro i hi
    have hpos := U_pos hi
    simp only [Finset.mem_filter, mem_U] at hi ⊢
    obtain ⟨h1, h2⟩ := hi
    have := key i (mem_U.2 ⟨by omega, h2⟩)
    exact ⟨⟨by omega, (mem_U.1 this).2⟩, by omega⟩
  · intro i hi; simp only [Finset.mem_filter, mem_U] at hi; omega
  · intro i hi; simp only [mem_U] at hi; omega
  · intro i hi; simp only [Finset.mem_filter, mem_U] at hi; rw [Nat.sub_sub_self hi.1.1.le]

/-- `range (M*u)` decomposes into blocks `M*t + i` -/
lemma sum_range_mul' (M u : ℕ) (F : ℕ → ℚ_[p]) :
    ∑ k ∈ range (M * u), F k = ∑ t ∈ range u, ∑ i ∈ range M, F (M * t + i) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma prod_range_mul' (M u : ℕ) (F : ℕ → ℚ_[p]) :
    ∏ k ∈ range (M * u), F k = ∏ t ∈ range u, ∏ i ∈ range M, F (M * t + i) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ]

/-- block decomposition of `U (M*u)` when `p ∣ M` -/
lemma sum_U_mul {M : ℕ} (hM : p ∣ M) (u : ℕ) (g : ℕ → ℚ_[p]) :
    ∑ i ∈ U p (M * u), g i = ∑ t ∈ range u, ∑ i ∈ U p M, g (M * t + i) := by
  rw [sum_U_eq_sum_range, sum_range_mul']
  apply Finset.sum_congr rfl
  intro t _
  rw [sum_U_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have : p ∣ M * t + i ↔ p ∣ i := by
    constructor
    · intro h; exact (Nat.dvd_add_right (Dvd.dvd.mul_right hM t)).1 h
    · intro h; exact dvd_add (Dvd.dvd.mul_right hM t) h
  by_cases h : p ∣ i
  · simp [h, this.2 h]
  · simp [h, (not_congr this).2 h]

lemma prod_U_mul {M : ℕ} (hM : p ∣ M) (u : ℕ) (g : ℕ → ℚ_[p]) :
    ∏ i ∈ U p (M * u), g i = ∏ t ∈ range u, ∏ i ∈ U p M, g (M * t + i) := by
  rw [prod_U_eq_prod_range, prod_range_mul']
  apply Finset.prod_congr rfl
  intro t _
  rw [prod_U_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  have : p ∣ M * t + i ↔ p ∣ i := by
    constructor
    · intro h; exact (Nat.dvd_add_right (Dvd.dvd.mul_right hM t)).1 h
    · intro h; exact dvd_add (Dvd.dvd.mul_right hM t) h
  by_cases h : p ∣ i
  · simp [h, this.2 h]
  · simp [h, (not_congr this).2 h]

/-- norms of elements of `U` are 1 -/
lemma norm_U {m i : ℕ} (h : i ∈ U p m) : ‖(i : ℚ_[p])‖ = 1 :=
  norm_nat_eq_one_of_not_dvd (mem_U.1 h).2

lemma Ob_inv_U {m i : ℕ} (h : i ∈ U p m) (j : ℕ) : Ob p 0 (((i : ℚ_[p]) ^ j)⁻¹) := by
  unfold Ob; rw [norm_inv, norm_pow, norm_U h]; simp

lemma Ob_inv_pow_of_norm_one {x : ℚ_[p]} (h : ‖x‖ = 1) (j : ℕ) : Ob p 0 ((x ^ j)⁻¹) := by
  unfold Ob; rw [norm_inv, norm_pow, h]; simp

lemma Ob_inv_of_norm_one {x : ℚ_[p]} (h : ‖x‖ = 1) : Ob p 0 (x⁻¹) := by
  unfold Ob; rw [norm_inv, h]; simp

lemma U_p_sub {i : ℕ} (h : i ∈ U p p) : p - i ∈ U p p 
    := by
  have hpos := U_pos h
  rw [mem_U] at *
  obtain ⟨h1, h2⟩ := h
  refine ⟨by omega, ?_⟩
  intro hd; apply h2
  have := Nat.dvd_sub (dvd_refl p) hd
  rwa [Nat.sub_sub_self h1.le] at this

end A357565Proof

-- ===== Dev3 =====


set_option linter.unusedSectionVars false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_le_one_of_Ob0 {x : ℚ_[p]} (h : Ob p 0 x) : ‖x‖ ≤ 1 := by
  unfold Ob at h; simpa using h

lemma Ob0_of_norm_le_one {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : Ob p 0 x := by
  unfold Ob; simpa using h

lemma Ob0_of_norm_eq_one {x : ℚ_[p]} (h : ‖x‖ = 1) : Ob p 0 x := Ob0_of_norm_le_one h.le

lemma Ob_nonneg_to_zero {j : ℤ} (hj : 0 ≤ j) {x : ℚ_[p]} (h : Ob p j x) : Ob p 0 x :=
  Ob_mono h hj

lemma Ob_cast {j j' : ℤ} {x : ℚ_[p]} (h : j = j') (hx : Ob p j x) : Ob p j' x := h ▸ hx

lemma Ob_two : Ob p 0 (2 : ℚ_[p]) := Ob_ofNat 2

lemma Ob_three : Ob p 0 (3 : ℚ_[p]) := Ob_ofNat 3

lemma norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have : ¬ p ∣ 2 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h
    exact hp2 this
  have := norm_nat_eq_one_of_not_dvd (p := p) this
  simpa using this

lemma Ob_inv_two (hp2 : p ≠ 2) : Ob p 0 ((2 : ℚ_[p])⁻¹) :=
  Ob_inv_of_norm_one (norm_two_eq_one hp2)

lemma Ob_ratCast_of_den (q : ℚ) (hq : ¬ p ∣ q.den) : Ob p 0 ((q : ℚ_[p])) := by
  unfold Ob; simpa using Padic.norm_rat_le_one hq

/-- first-order product bound: `∏ (1 + x_i) - 1 = O(ε)` -/
lemma Ob_prod_sub_one {ι : Type*} (s : Finset ι) {j : ℕ} {x : ι → ℚ_[p]}
    (h : ∀ i ∈ s, Ob p j (x i)) : Ob p j (∏ i ∈ s, (1 + x i) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ob_zero (p := p) j
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hP := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha' := h a (Finset.mem_insert_self a s)
    have h1a : Ob p 0 (1 + x a) := Ob_add Ob_one (Ob_mono ha' (by simp))
    have : (1 + x a) * ∏ i ∈ s, (1 + x i) - 1 = (∏ i ∈ s, (1 + x i) - 1) * (1 + x a) + x a := by ring
    rw [this]
    exact Ob_add (Ob_mul_unit hP h1a) ha'

/-- second-order product bound -/
lemma Ob_prod_sub_one_sub_sum {ι : Type*} (s : Finset ι) {j : ℕ} {x : ι → ℚ_[p]}
    (h : ∀ i ∈ s, Ob p j (x i)) :
    Ob p (2 * j) (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ob_zero (p := p) (2 * j)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hP1 := Ob_prod_sub_one s (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha' := h a (Finset.mem_insert_self a s)
    have : (1 + x a) * ∏ i ∈ s, (1 + x i) - 1 - (x a + ∑ i ∈ s, x i)
        = (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) + x a * (∏ i ∈ s, (1 + x i) - 1) := by ring
    rw [this]
    refine Ob_add hP ?_
    exact Ob_cast (by ring) (Ob_mul ha' hP1)

/-- third-order product bound -/
lemma Ob_prod_second_order {ι : Type*} (s : Finset ι) {j : ℕ} {x : ι → ℚ_[p]}
    (h : ∀ i ∈ s, Ob p j (x i)) :
    Ob p (3 * j) (2 * (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i)
      - ((∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, (x i) ^ 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ob_zero (p := p) (3 * j)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have hP := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hP2 := Ob_prod_sub_one_sub_sum s (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha' := h a (Finset.mem_insert_self a s)
    have : 2 * ((1 + x a) * ∏ i ∈ s, (1 + x i) - 1 - (x a + ∑ i ∈ s, x i))
        - ((x a + ∑ i ∈ s, x i) ^ 2 - (x a ^ 2 + ∑ i ∈ s, x i ^ 2))
        = (2 * (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) - ((∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, (x i) ^ 2))
          + 2 * x a * (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) := by ring
    rw [this]
    refine Ob_add hP ?_
    exact Ob_cast (by ring) (Ob_mul (Ob_mul (Ob_two (p := p)) ha') hP2)

/-- `(i+x)^n - i^n = O(x)` for `‖i‖ ≤ 1` -/
lemma Ob_pow_sub_pow {i x : ℚ_[p]} (hi : Ob p 0 i) {j : ℕ} (hx : Ob p j x) (n : ℕ) :
    Ob p j ((i + x) ^ n - i ^ n) := by
  induction n with
  | zero => simpa using Ob_zero (p := p) j
  | succ n ih =>
    have : (i + x) ^ (n + 1) - i ^ (n + 1) = (i + x) * ((i + x) ^ n - i ^ n) + x * i ^ n := by ring
    rw [this]
    have hix : Ob p 0 (i + x) := Ob_add hi (Ob_mono hx (by simp))
    exact Ob_add (Ob_unit_mul hix ih) (Ob_mul_unit hx (by simpa using Ob_pow hi n))

/-- `(i+x)^(n+1) - i^(n+1) - (n+1) x i^n = O(x^2)` for `‖i‖ ≤ 1` -/
lemma Ob_pow_expand {i x : ℚ_[p]} (hi : Ob p 0 i) {j : ℕ} (hx : Ob p j x) (n : ℕ) :
    Ob p (2 * j) ((i + x) ^ (n + 1) - i ^ (n + 1) - ((n : ℚ_[p]) + 1) * x * i ^ n) := by
  induction n with
  | zero => simpa using Ob_zero (p := p) (2 * j)
  | succ n ih =>
    have : (i + x) ^ (n + 1 + 1) - i ^ (n + 1 + 1) - (((n + 1 : ℕ) : ℚ_[p]) + 1) * x * i ^ (n + 1)
        = (i + x) * ((i + x) ^ (n + 1) - i ^ (n + 1) - ((n : ℚ_[p]) + 1) * x * i ^ n)
          + ((n : ℚ_[p]) + 1) * x ^ 2 * i ^ n := by
      push_cast; ring
    rw [this]
    have hix : Ob p 0 (i + x) := Ob_add hi (Ob_mono hx (by simp))
    refine Ob_add (Ob_unit_mul hix ih) ?_
    have h1 : Ob p 0 ((n + 1 : ℚ_[p])) := by
      have := Ob_natCast (p := p) (n + 1); simpa using this
    have h2 : Ob p (2 * j) (x ^ 2) := by
      have := Ob_pow hx 2; simpa using this
    have h3 : Ob p 0 (i ^ n) := by simpa using Ob_pow hi n
    exact Ob_mul_unit (Ob_unit_mul h1 h2) h3

/-- inverse version: `(i+x)^{-(n+1)} - i^{-(n+1)} + (n+1) x i^{-(n+2)} = O(x^2)` for units `i`, `i+x` -/
lemma Ob_inv_pow_expand {i x : ℚ_[p]} (hi : ‖i‖ = 1) (hix : ‖i + x‖ = 1) {j : ℕ} (hx : Ob p j x)
    (n : ℕ) :
    Ob p (2 * j) (((i + x) ^ (n + 1))⁻¹ - (i ^ (n + 1))⁻¹ + ((n : ℚ_[p]) + 1) * x * (i ^ (n + 2))⁻¹) := by
  have hi0 : i ≠ 0 := by intro h; rw [h] at hi; simp at hi
  have hix0 : i + x ≠ 0 := by intro h; rw [h] at hix; simp at hix
  have hiO : Ob p 0 i := Ob0_of_norm_eq_one hi
  have hR := Ob_pow_expand hiO hx n
  set R := (i + x) ^ (n + 1) - i ^ (n + 1) - ((n : ℚ_[p]) + 1) * x * i ^ n with hRdef
  have key : ((i + x) ^ (n + 1))⁻¹ - (i ^ (n + 1))⁻¹ + ((n : ℚ_[p]) + 1) * x * (i ^ (n + 2))⁻¹
      = (-(i * R) + ((n : ℚ_[p]) + 1) * x * (R + ((n : ℚ_[p]) + 1) * x * i ^ n))
        * ((i ^ (n + 2))⁻¹ * ((i + x) ^ (n + 1))⁻¹) := by
    rw [hRdef]
    field_simp
    ring
  rw [key]
  have hu : Ob p 0 ((i ^ (n + 2))⁻¹ * ((i + x) ^ (n + 1))⁻¹) :=
    Ob_mul_unit (Ob_inv_pow_of_norm_one hi _) (Ob_inv_pow_of_norm_one hix _)
  refine Ob_mul_unit ?_ hu
  have hn : Ob p 0 ((n + 1 : ℚ_[p])) := by
    have := Ob_natCast (p := p) (n + 1); simpa using this
  refine Ob_add (Ob_neg (Ob_unit_mul hiO hR)) ?_
  have hxx : Ob p (2 * j) (((n : ℚ_[p]) + 1) * x * (((n : ℚ_[p]) + 1) * x * i ^ n)) :=
    Ob_cast (by ring)
      (Ob_mul (Ob_unit_mul hn hx) (Ob_mul_unit (Ob_unit_mul hn hx) (by simpa using Ob_pow hiO n)))
  have : Ob p (2 * j) (((n : ℚ_[p]) + 1) * x * R) := by
    have := Ob_mul (Ob_unit_mul hn hx) hR
    exact Ob_mono this (by omega)
  have := Ob_add this hxx
  convert this using 1; ring

/-- first order inverse Lipschitz bound -/
lemma Ob_inv_pow_sub {i x : ℚ_[p]} (hi : ‖i‖ = 1) (hix : ‖i + x‖ = 1) {j : ℕ} (hx : Ob p j x)
    (n : ℕ) : Ob p j (((i + x) ^ n)⁻¹ - (i ^ n)⁻¹) := by
  have hi0 : i ≠ 0 := by intro h; rw [h] at hi; simp at hi
  have hix0 : i + x ≠ 0 := by intro h; rw [h] at hix; simp at hix
  have key : ((i + x) ^ n)⁻¹ - (i ^ n)⁻¹ = -((i + x) ^ n - i ^ n) * ((i ^ n)⁻¹ * ((i + x) ^ n)⁻¹) := by
    field_simp; ring
  rw [key]
  exact Ob_mul_unit (Ob_neg (Ob_pow_sub_pow (Ob0_of_norm_eq_one hi) hx n))
    (Ob_mul_unit (Ob_inv_pow_of_norm_one hi _) (Ob_inv_pow_of_norm_one hix _))

/-- third-order expansion of `(i+x)^{-2}` -/
lemma Ob_inv_sq_expand3 {i x : ℚ_[p]} (hi : ‖i‖ = 1) (hix : ‖i + x‖ = 1) {j : ℕ} (hx : Ob p j x) :
    Ob p (3 * j) (((i + x) ^ 2)⁻¹ - (i ^ 2)⁻¹ + 2 * x * (i ^ 3)⁻¹ - 3 * x ^ 2 * (i ^ 4)⁻¹) := by
  have hi0 : i ≠ 0 := by intro h; rw [h] at hi; simp at hi
  have hix0 : i + x ≠ 0 := by intro h; rw [h] at hix; simp at hix
  have key : ((i + x) ^ 2)⁻¹ - (i ^ 2)⁻¹ + 2 * x * (i ^ 3)⁻¹ - 3 * x ^ 2 * (i ^ 4)⁻¹
      = -(x ^ 3 * (4 * i + 3 * x)) * ((i ^ 4)⁻¹ * ((i + x) ^ 2)⁻¹) := by
    field_simp
    ring
  rw [key]
  have hiO : Ob p 0 i := Ob0_of_norm_eq_one hi
  have hxO : Ob p 0 x := Ob_mono hx (by simp)
  have h1 : Ob p 0 (4 * i + 3 * x) := Ob_add (Ob_unit_mul (Ob_ofNat 4) hiO) (Ob_unit_mul Ob_three hxO)
  have h2 : Ob p (3 * j) (x ^ 3) := by have := Ob_pow hx 3; simpa using this
  exact Ob_mul_unit (Ob_neg (Ob_mul_unit h2 h1))
    (Ob_mul_unit (Ob_inv_pow_of_norm_one hi _) (Ob_inv_pow_of_norm_one hix _))

end A357565Proof

-- ===== Dev4 =====


set_option linter.unusedSectionVars false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `H*_j(m) = ∑_{i<m, p∤i} i^{-j}` -/
noncomputable def Hs (p : ℕ) [Fact p.Prime] (j m : ℕ) : ℚ_[p] := ∑ i ∈ U p m, ((i : ℚ_[p]) ^ j)⁻¹

lemma Ob_Hs (j m : ℕ) : Ob p 0 (Hs p j m) := Ob_sum _ (fun i hi => Ob_inv_U hi j)

lemma sum_range_id_eq :
    (∑ d ∈ range p, (d : ℚ_[p])) = (p : ℚ_[p]) * ((p - 1 : ℕ) : ℚ_[p]) / 2 := by
  have h := Finset.sum_range_id_mul_two p
  have : ((∑ d ∈ range p, d : ℕ) : ℚ_[p]) * 2 = (p : ℚ_[p]) * ((p - 1 : ℕ) : ℚ_[p]) := by
    exact_mod_cast h
  push_cast at this
  rw [eq_div_iff (by norm_num : (2:ℚ_[p]) ≠ 0)]
  exact this

lemma Ob_sum_range_id (hp2 : p ≠ 2) : Ob p 1 (∑ d ∈ range p, (d : ℚ_[p])) := by
  rw [sum_range_id_eq, div_eq_mul_inv]
  exact Ob_mul_unit (Ob_mul_unit Ob_p (Ob_natCast _)) (Ob_inv_two hp2)

lemma sum_range_sq_mul_six (n : ℕ) :
    (∑ d ∈ range n, (d : ℚ_[p]) ^ 2) * 6 = (n : ℚ_[p]) * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

lemma norm_six_eq_one (hp5 : 5 ≤ p) : ‖(6 : ℚ_[p])‖ = 1 := by
  have : ¬ p ∣ 6 := by
    intro h
    have h6 := Nat.le_of_dvd (by norm_num) h
    rcases (show p = 5 ∨ p = 6 by omega) with h5 | h6
    · subst h5; norm_num at h
    · subst h6; exact absurd hp.out (by norm_num)
  have := norm_nat_eq_one_of_not_dvd (p := p) this
  simpa using this

lemma Ob_sum_range_sq (hp5 : 5 ≤ p) : Ob p 1 (∑ d ∈ range p, (d : ℚ_[p]) ^ 2) := by
  have key : (∑ d ∈ range p, (d : ℚ_[p]) ^ 2)
      = (p : ℚ_[p]) * ((p:ℚ_[p]) - 1) * (2 * p - 1) * (6 : ℚ_[p])⁻¹ := by
    rw [← sum_range_sq_mul_six]; field_simp
  rw [key]
  refine Ob_mul_unit (Ob_mul_unit (Ob_mul_unit Ob_p ?_) ?_) (Ob_inv_of_norm_one (norm_six_eq_one hp5))
  · exact Ob_sub (Ob_natCast _) Ob_one
  · exact Ob_sub (Ob_mul_unit Ob_two (Ob_natCast _)) Ob_one

/-- block expansion of `Hs j (M*u)` -/
lemma Hs_mul_eq {M : ℕ} (hM : p ∣ M) (u j : ℕ) :
    Hs p j (M * u) = ∑ t ∈ range u, ∑ i ∈ U p M, (((i : ℚ_[p]) + (M : ℚ_[p]) * t) ^ j)⁻¹ := by
  unfold Hs; rw [sum_U_mul hM]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro i _
  push_cast; ring_nf

lemma norm_block {M i : ℕ} (hM : p ∣ M) (hi : i ∈ U p M) (t : ℕ) :
    ‖(i : ℚ_[p]) + (M : ℚ_[p]) * t‖ = 1 := by
  have h : ¬ p ∣ M * t + i := by
    intro h
    exact (mem_U.1 hi).2 ((Nat.dvd_add_right (Dvd.dvd.mul_right hM t)).1 h)
  have := norm_nat_eq_one_of_not_dvd (p := p) h
  push_cast at this
  rwa [add_comm] at this

lemma Ob_sum_sub_sum {ι : Type*} (s : Finset ι) {j : ℤ} {f g : ι → ℚ_[p]}
    (h : ∀ i ∈ s, Ob p j (f i - g i)) : Ob p j (∑ i ∈ s, f i - ∑ i ∈ s, g i) := by
  rw [← Finset.sum_sub_distrib]; exact Ob_sum _ h

lemma sum_sum_split {ι κ : Type*} (s : Finset ι) (t : Finset κ) (A : κ → ℚ_[p]) (f : ι → ℚ_[p])
    (g : κ → ℚ_[p]) :
    ∑ d ∈ s, ∑ i ∈ t, (A i + f d * g i)
      = (s.card : ℚ_[p]) * ∑ i ∈ t, A i + (∑ d ∈ s, f d) * (∑ i ∈ t, g i) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_mul_sum]

lemma sum_sum_split3 {ι κ : Type*} (s : Finset ι) (t : Finset κ) (A : κ → ℚ_[p]) (f f' : ι → ℚ_[p])
    (g g' : κ → ℚ_[p]) :
    ∑ d ∈ s, ∑ i ∈ t, (A i + f d * g i + f' d * g' i)
      = (s.card : ℚ_[p]) * ∑ i ∈ t, A i + (∑ d ∈ s, f d) * (∑ i ∈ t, g i)
        + (∑ d ∈ s, f' d) * (∑ i ∈ t, g' i) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_mul_sum]

/-- `Hs (j+1) (p^(m+1)) ≡ p * Hs (j+1) (p^m)  mod p^(m+1)` -/
lemma Ob_Hs_pow_succ (hp2 : p ≠ 2) (j : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Ob p (m + 1) (Hs p (j + 1) (p ^ (m + 1)) - (p : ℚ_[p]) * Hs p (j + 1) (p ^ m)) := by
  have hM : p ∣ p ^ m := dvd_pow_self p (by omega)
  have hpow : p ^ (m + 1) = p ^ m * p := by ring
  rw [hpow, Hs_mul_eq hM]
  set x : ℕ → ℚ_[p] := fun d => ((p ^ m : ℕ) : ℚ_[p]) * d with hx
  have hxO : ∀ d : ℕ, Ob p m (x d) := by
    intro d; simp only [hx]; push_cast; exact Ob_p_pow_mul m (Ob_natCast d)
  -- main term: A d i = (i^(j+1))⁻¹ - (j+1) x d (i^(j+2))⁻¹
  have hmain : ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
      (((i : ℚ_[p]) ^ (j + 1))⁻¹ - ((j : ℚ_[p]) + 1) * x d * ((i : ℚ_[p]) ^ (j + 2))⁻¹)
      = (p : ℚ_[p]) * Hs p (j + 1) (p ^ m)
        - ((j : ℚ_[p]) + 1) * ((p ^ m : ℕ) : ℚ_[p]) * (∑ d ∈ range p, (d : ℚ_[p])) * Hs p (j + 2) (p ^ m) := by
    have e1 : ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
        (((i : ℚ_[p]) ^ (j + 1))⁻¹ - ((j : ℚ_[p]) + 1) * x d * ((i : ℚ_[p]) ^ (j + 2))⁻¹)
        = ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
        (((i : ℚ_[p]) ^ (j + 1))⁻¹ + (-((j : ℚ_[p]) + 1) * x d) * ((i : ℚ_[p]) ^ (j + 2))⁻¹) := by
      apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e1, sum_sum_split, Finset.card_range]
    have e2 : ∑ d ∈ range p, (-((j : ℚ_[p]) + 1) * x d)
        = -(((j : ℚ_[p]) + 1) * ((p ^ m : ℕ) : ℚ_[p])) * ∑ d ∈ range p, (d : ℚ_[p]) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; simp only [hx]; ring
    rw [e2]; unfold Hs; ring
  have hsplit : ∀ d ∈ range p, ∀ i ∈ U p (p ^ m),
      Ob p (2 * m) ((((i : ℚ_[p]) + (p ^ m : ℕ) * d) ^ (j + 1))⁻¹
        - (((i : ℚ_[p]) ^ (j + 1))⁻¹ - ((j : ℚ_[p]) + 1) * x d * ((i : ℚ_[p]) ^ (j + 2))⁻¹)) := by
    intro d _ i hi
    have := Ob_inv_pow_expand (norm_U hi) (norm_block hM hi d) (hxO d) j
    simp only [hx] at this ⊢
    convert this using 1
    push_cast; ring
  have hR : Ob p (m + 1) (∑ d ∈ range p, ∑ i ∈ U p (p ^ m), (((i : ℚ_[p]) + (p ^ m : ℕ) * d) ^ (j + 1))⁻¹
      - ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
        (((i : ℚ_[p]) ^ (j + 1))⁻¹ - ((j : ℚ_[p]) + 1) * x d * ((i : ℚ_[p]) ^ (j + 2))⁻¹)) := by
    apply Ob_sum_sub_sum; intro d hd
    apply Ob_sum_sub_sum; intro i hi
    exact Ob_mono (hsplit d hd i hi) (by omega)
  rw [hmain] at hR
  have hB : Ob p (m + 1) (((j : ℚ_[p]) + 1) * ((p ^ m : ℕ) : ℚ_[p]) * (∑ d ∈ range p, (d : ℚ_[p]))
      * Hs p (j + 2) (p ^ m)) := by
    have h1 : Ob p 0 ((j : ℚ_[p]) + 1) := Ob_add (Ob_natCast j) Ob_one
    have h2 : Ob p m ((p ^ m : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow m
    have := Ob_mul (Ob_mul (Ob_unit_mul h1 h2) (Ob_sum_range_id hp2)) (Ob_Hs (j + 2) (p ^ m))
    exact Ob_cast (by ring) this
  have := Ob_add hR (Ob_neg hB)
  exact Ob_of_eq this (by ring)

/-- pairing bound for sums of inverse cubes -/
lemma Ob_sum_inv_cube_pair (hp2 : p ≠ 2) {M : ℕ} (hM : p ∣ M) (c : ℚ_[p]) (hc : Ob p 0 c)
    (hu : ∀ i ∈ U p M, ‖c + (i : ℚ_[p])‖ = 1) {j : ℤ} (hj : Ob p j (2 * c + (M : ℚ_[p]))) :
    Ob p j (∑ i ∈ U p M, ((c + (i : ℚ_[p])) ^ 3)⁻¹) := by
  have h2 : (2 : ℚ_[p]) * ∑ i ∈ U p M, ((c + (i : ℚ_[p])) ^ 3)⁻¹
      = ∑ i ∈ U p M, (((c + (i : ℚ_[p])) ^ 3)⁻¹ + ((c + ((M - i : ℕ) : ℚ_[p])) ^ 3)⁻¹) := by
    rw [Finset.sum_add_distrib, ← sum_U_reflect hM (fun i => ((c + (i : ℚ_[p])) ^ 3)⁻¹)]; ring
  have key : Ob p j (∑ i ∈ U p M, (((c + (i : ℚ_[p])) ^ 3)⁻¹ + ((c + ((M - i : ℕ) : ℚ_[p])) ^ 3)⁻¹)) := by
    apply Ob_sum; intro i hi
    have hi' : M - i ∈ U p M := U_reflect_mem hM i hi
    have ha := hu i hi
    have hb := hu (M - i) hi'
    set a := c + (i : ℚ_[p]) with hadef
    set b := c + ((M - i : ℕ) : ℚ_[p]) with hbdef
    have hab : a + b = 2 * c + M := by
      rw [hadef, hbdef, Nat.cast_sub (mem_U.1 hi).1.le]; ring
    have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
    have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
    have : (a ^ 3)⁻¹ + (b ^ 3)⁻¹ = (a + b) * (a ^ 2 - a * b + b ^ 2) * ((a ^ 3)⁻¹ * (b ^ 3)⁻¹) := by
      field_simp; ring
    rw [this, hab]
    have haO : Ob p 0 a := Ob0_of_norm_eq_one ha
    have hbO : Ob p 0 b := Ob0_of_norm_eq_one hb
    refine Ob_mul_unit (Ob_mul_unit hj ?_) (Ob_mul_unit (Ob_inv_pow_of_norm_one ha 3) (Ob_inv_pow_of_norm_one hb 3))
    exact Ob_add (Ob_sub (Ob_pow haO 2) (Ob_mul_unit haO hbO)) (Ob_pow hbO 2)
  have : ∑ i ∈ U p M, ((c + (i : ℚ_[p])) ^ 3)⁻¹ = (2 : ℚ_[p])⁻¹ * ((2 : ℚ_[p]) * ∑ i ∈ U p M, ((c + (i : ℚ_[p])) ^ 3)⁻¹) := by
    field_simp
  rw [this, h2]
  exact Ob_unit_mul (Ob_inv_two hp2) key

lemma Ob_Hs3 (hp2 : p ≠ 2) {M : ℕ} (hM : p ∣ M) {j : ℤ} (hMj : Ob p j (M : ℚ_[p])) :
    Ob p j (Hs p 3 M) := by
  have := Ob_sum_inv_cube_pair hp2 hM (0 : ℚ_[p]) (Ob_zero 0)
    (fun i hi => by simpa using norm_U hi) (j := j) (by simpa using hMj)
  unfold Hs; simpa using this

/-- refined version for `Hs 2` when `∑ d^2 ≡ 0 mod p` (i.e. `p ≥ 5`) -/
lemma Ob_Hs2_pow_succ_refined (hp2 : p ≠ 2) (hsq : Ob p 1 (∑ d ∈ range p, (d : ℚ_[p]) ^ 2))
    {m : ℕ} (hm : 1 ≤ m) :
    Ob p (m + 2) (Hs p 2 (p ^ (m + 1)) - (p : ℚ_[p]) * Hs p 2 (p ^ m)) := by
  have hM : p ∣ p ^ m := dvd_pow_self p (by omega)
  have hpow : p ^ (m + 1) = p ^ m * p := by ring
  rw [hpow, Hs_mul_eq hM]
  set x : ℕ → ℚ_[p] := fun d => ((p ^ m : ℕ) : ℚ_[p]) * d with hx
  have hxO : ∀ d : ℕ, Ob p m (x d) := by
    intro d; simp only [hx]; push_cast; exact Ob_p_pow_mul m (Ob_natCast d)
  have hmain : ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
      (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * x d * ((i : ℚ_[p]) ^ 3)⁻¹ + 3 * (x d) ^ 2 * ((i : ℚ_[p]) ^ 4)⁻¹)
      = (p : ℚ_[p]) * Hs p 2 (p ^ m)
        - 2 * ((p ^ m : ℕ) : ℚ_[p]) * (∑ d ∈ range p, (d : ℚ_[p])) * Hs p 3 (p ^ m)
        + 3 * ((p ^ m : ℕ) : ℚ_[p]) ^ 2 * (∑ d ∈ range p, (d : ℚ_[p]) ^ 2) * Hs p 4 (p ^ m) := by
    have e1 : ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
        (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * x d * ((i : ℚ_[p]) ^ 3)⁻¹ + 3 * (x d) ^ 2 * ((i : ℚ_[p]) ^ 4)⁻¹)
        = ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
        (((i : ℚ_[p]) ^ 2)⁻¹ + (-2 * x d) * ((i : ℚ_[p]) ^ 3)⁻¹ + (3 * (x d) ^ 2) * ((i : ℚ_[p]) ^ 4)⁻¹) := by
      apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e1, sum_sum_split3, Finset.card_range]
    have e2 : ∑ d ∈ range p, (-2 * x d) = -(2 * ((p ^ m : ℕ) : ℚ_[p])) * ∑ d ∈ range p, (d : ℚ_[p]) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; simp only [hx]; ring
    have e3 : ∑ d ∈ range p, (3 * (x d) ^ 2) = (3 * ((p ^ m : ℕ) : ℚ_[p]) ^ 2) * ∑ d ∈ range p, (d : ℚ_[p]) ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; simp only [hx]; ring
    rw [e2, e3]; unfold Hs; ring
  have hsplit : ∀ d ∈ range p, ∀ i ∈ U p (p ^ m),
      Ob p (3 * m) ((((i : ℚ_[p]) + (p ^ m : ℕ) * d) ^ 2)⁻¹
        - (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * x d * ((i : ℚ_[p]) ^ 3)⁻¹ + 3 * (x d) ^ 2 * ((i : ℚ_[p]) ^ 4)⁻¹)) := by
    intro d _ i hi
    have := Ob_inv_sq_expand3 (norm_U hi) (norm_block hM hi d) (hxO d)
    simp only [hx] at this ⊢
    convert this using 1
    push_cast; ring
  have hR : Ob p (m + 2) (∑ d ∈ range p, ∑ i ∈ U p (p ^ m), (((i : ℚ_[p]) + (p ^ m : ℕ) * d) ^ 2)⁻¹
      - ∑ d ∈ range p, ∑ i ∈ U p (p ^ m),
        (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * x d * ((i : ℚ_[p]) ^ 3)⁻¹ + 3 * (x d) ^ 2 * ((i : ℚ_[p]) ^ 4)⁻¹)) := by
    apply Ob_sum_sub_sum; intro d hd
    apply Ob_sum_sub_sum; intro i hi
    exact Ob_mono (hsplit d hd i hi) (by omega)
  rw [hmain] at hR
  have hpm : Ob p m ((p ^ m : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow m
  have hB : Ob p (m + 2) (2 * ((p ^ m : ℕ) : ℚ_[p]) * (∑ d ∈ range p, (d : ℚ_[p])) * Hs p 3 (p ^ m)) := by
    have := Ob_mul (Ob_mul (Ob_unit_mul Ob_two hpm) (Ob_sum_range_id hp2)) (Ob_Hs3 hp2 hM hpm)
    have h' : Ob p (2 * m + 1) (2 * ((p ^ m : ℕ) : ℚ_[p]) * (∑ d ∈ range p, (d : ℚ_[p])) * Hs p 3 (p ^ m)) :=
      Ob_cast (by push_cast; ring) this
    exact Ob_mono h' (by omega)
  have hC : Ob p (m + 2) (3 * ((p ^ m : ℕ) : ℚ_[p]) ^ 2 * (∑ d ∈ range p, (d : ℚ_[p]) ^ 2) * Hs p 4 (p ^ m)) := by
    have := Ob_mul (Ob_mul (Ob_unit_mul Ob_three (Ob_pow hpm 2)) hsq) (Ob_Hs 4 (p ^ m))
    have h' : Ob p (2 * m + 1) (3 * ((p ^ m : ℕ) : ℚ_[p]) ^ 2 * (∑ d ∈ range p, (d : ℚ_[p]) ^ 2) * Hs p 4 (p ^ m)) :=
      Ob_cast (by push_cast; ring) this
    exact Ob_mono h' (by omega)
  have := Ob_add (Ob_add hR (Ob_neg hB)) hC
  exact Ob_of_eq this (by ring)

/-- `2 Hs 1 M + M Hs 2 M = M^2 ∑ (i^2 (M-i))^{-1}` and the latter sum is `O(M)` -/
lemma Ob_Hs1_approx (hp2 : p ≠ 2) {M : ℕ} (hM : p ∣ M) {j : ℤ} (hj : 0 ≤ j) (hMj : Ob p j (M : ℚ_[p])) :
    Ob p (3 * j) (Hs p 1 M + (M : ℚ_[p]) / 2 * Hs p 2 M) := by
  have hMO : Ob p 0 (M : ℚ_[p]) := Ob_natCast M
  -- 2 Hs1 = Σ (a⁻¹ + b⁻¹)
  have h1 : (2 : ℚ_[p]) * Hs p 1 M = ∑ i ∈ U p M, (((i : ℚ_[p]) ^ 1)⁻¹ + (((M - i : ℕ) : ℚ_[p]) ^ 1)⁻¹) := by
    rw [Finset.sum_add_distrib]; unfold Hs
    rw [← sum_U_reflect hM (fun i => ((i : ℚ_[p]) ^ 1)⁻¹)]; ring
  have h2 : (2 : ℚ_[p]) * Hs p 1 M + (M : ℚ_[p]) * Hs p 2 M
      = (M : ℚ_[p]) ^ 2 * ∑ i ∈ U p M, (((i : ℚ_[p]) ^ 2)⁻¹ * (((M - i : ℕ) : ℚ_[p]))⁻¹) := by
    rw [h1, Hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi
    have ha := norm_U hi
    have hb := norm_U (U_reflect_mem hM i hi)
    have ha0 : (i : ℚ_[p]) ≠ 0 := by intro h; rw [h] at ha; simp at ha
    have hb0 : ((M - i : ℕ) : ℚ_[p]) ≠ 0 := by intro h; rw [h] at hb; simp at hb
    have hab : (i : ℚ_[p]) + ((M - i : ℕ) : ℚ_[p]) = M := by
      rw [Nat.cast_sub (mem_U.1 hi).1.le]; ring
    rw [← hab]
    field_simp
    ring
  -- Σ (a² b)⁻¹ = -Hs3 + M Σ (a³ b)⁻¹
  have h3 : ∑ i ∈ U p M, (((i : ℚ_[p]) ^ 2)⁻¹ * (((M - i : ℕ) : ℚ_[p]))⁻¹)
      = - Hs p 3 M + (M : ℚ_[p]) * ∑ i ∈ U p M, (((i : ℚ_[p]) ^ 3)⁻¹ * (((M - i : ℕ) : ℚ_[p]))⁻¹) := by
    rw [Hs, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi
    have ha := norm_U hi
    have hb := norm_U (U_reflect_mem hM i hi)
    have ha0 : (i : ℚ_[p]) ≠ 0 := by intro h; rw [h] at ha; simp at ha
    have hb0 : ((M - i : ℕ) : ℚ_[p]) ≠ 0 := by intro h; rw [h] at hb; simp at hb
    have hab : (i : ℚ_[p]) + ((M - i : ℕ) : ℚ_[p]) = M := by
      rw [Nat.cast_sub (mem_U.1 hi).1.le]; ring
    rw [← hab]
    field_simp
    ring
  have hS : Ob p j (∑ i ∈ U p M, (((i : ℚ_[p]) ^ 2)⁻¹ * (((M - i : ℕ) : ℚ_[p]))⁻¹)) := by
    rw [h3]
    refine Ob_add (Ob_neg (Ob_Hs3 hp2 hM hMj)) (Ob_mul_unit hMj ?_)
    apply Ob_sum; intro i hi
    exact Ob_mul_unit (Ob_inv_U hi 3) (Ob_inv_of_norm_one (norm_U (U_reflect_mem hM i hi)))
  have hfinal : Hs p 1 M + (M : ℚ_[p]) / 2 * Hs p 2 M
      = (2 : ℚ_[p])⁻¹ * ((2 : ℚ_[p]) * Hs p 1 M + (M : ℚ_[p]) * Hs p 2 M) := by
    field_simp
  rw [hfinal, h2]
  refine Ob_unit_mul (Ob_inv_two hp2) ?_
  exact Ob_cast (by ring) (Ob_mul (Ob_pow hMj 2) hS)

/-- first-order: `Hs k (M u) ≡ u Hs k M  mod M` -/
lemma Ob_Hs_mul {M : ℕ} (hM : p ∣ M) {j : ℕ} (hMj : Ob p j (M : ℚ_[p])) (u k : ℕ) :
    Ob p j (Hs p k (M * u) - (u : ℚ_[p]) * Hs p k M) := by
  rw [Hs_mul_eq hM]
  have : (u : ℚ_[p]) * Hs p k M = ∑ t ∈ range u, ∑ i ∈ U p M, ((i : ℚ_[p]) ^ k)⁻¹ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Hs]
  rw [this]
  apply Ob_sum_sub_sum; intro t _
  apply Ob_sum_sub_sum; intro i hi
  exact Ob_inv_pow_sub (norm_U hi) (norm_block hM hi t) (Ob_mul_unit hMj (Ob_natCast t)) k

/-- second-order: `Hs 2 (M u) ≡ u Hs 2 M  mod M^2` -/
lemma Ob_Hs2_mul (hp2 : p ≠ 2) {M : ℕ} (hM : p ∣ M) {j : ℕ} (hMj : Ob p j (M : ℚ_[p])) (u : ℕ) :
    Ob p (2 * j) (Hs p 2 (M * u) - (u : ℚ_[p]) * Hs p 2 M) := by
  rw [Hs_mul_eq hM]
  have hmain : ∑ t ∈ range u, ∑ i ∈ U p M,
      (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * ((M : ℚ_[p]) * t) * ((i : ℚ_[p]) ^ 3)⁻¹)
      = (u : ℚ_[p]) * Hs p 2 M - 2 * (M : ℚ_[p]) * (∑ t ∈ range u, (t : ℚ_[p])) * Hs p 3 M := by
    have e1 : ∑ t ∈ range u, ∑ i ∈ U p M,
        (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * ((M : ℚ_[p]) * t) * ((i : ℚ_[p]) ^ 3)⁻¹)
        = ∑ t ∈ range u, ∑ i ∈ U p M,
        (((i : ℚ_[p]) ^ 2)⁻¹ + (-2 * ((M : ℚ_[p]) * t)) * ((i : ℚ_[p]) ^ 3)⁻¹) := by
      apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e1, sum_sum_split, Finset.card_range]
    have e2 : ∑ t ∈ range u, (-2 * ((M : ℚ_[p]) * t)) = -(2 * (M : ℚ_[p])) * ∑ t ∈ range u, (t : ℚ_[p]) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
    rw [e2]; unfold Hs; ring
  have hR : Ob p (2 * j) (∑ t ∈ range u, ∑ i ∈ U p M, (((i : ℚ_[p]) + (M : ℚ_[p]) * t) ^ 2)⁻¹
      - ∑ t ∈ range u, ∑ i ∈ U p M,
        (((i : ℚ_[p]) ^ 2)⁻¹ - 2 * ((M : ℚ_[p]) * t) * ((i : ℚ_[p]) ^ 3)⁻¹)) := by
    apply Ob_sum_sub_sum; intro t _
    apply Ob_sum_sub_sum; intro i hi
    have := Ob_inv_pow_expand (norm_U hi) (norm_block hM hi t) (Ob_mul_unit hMj (Ob_natCast t)) 1
    convert this using 1
    push_cast; ring
  rw [hmain] at hR
  have hB : Ob p (2 * j) (2 * (M : ℚ_[p]) * (∑ t ∈ range u, (t : ℚ_[p])) * Hs p 3 M) := by
    have hs : Ob p 0 (∑ t ∈ range u, (t : ℚ_[p])) := Ob_sum _ (fun t _ => Ob_natCast t)
    have := Ob_mul (Ob_mul_unit (Ob_unit_mul Ob_two hMj) hs) (Ob_Hs3 hp2 hM hMj)
    exact Ob_cast (by ring) this
  have := Ob_add hR (Ob_neg hB)
  exact Ob_of_eq this (by ring)

end A357565Proof

-- ===== Dev5 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/- ### `H^{(2)}_{p-1} ≡ 0 mod p` for `p ≥ 5` -/

lemma sum_range_zmod_pow (k : ℕ) :
    ∑ i ∈ range p, ((i : ZMod p)) ^ k = ∑ x : ZMod p, x ^ k := by
  refine Finset.sum_nbij' (fun i : ℕ => (i : ZMod p)) (fun x : ZMod p => x.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro x _; simp [ZMod.val_lt]
  · intro i hi; simp at hi; exact ZMod.val_cast_of_lt hi
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro i _; rfl

lemma dvd_sum_range_pow (hp5 : 5 ≤ p) : p ∣ ∑ i ∈ range p, i ^ (p - 3) := by
  have h : ((∑ i ∈ range p, i ^ (p - 3) : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [sum_range_zmod_pow]
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  exact (ZMod.natCast_eq_zero_iff _ p).1 h

lemma Ob_fermat {i : ℕ} (hi : ¬ p ∣ i) : Ob p 1 ((i : ℚ_[p]) ^ (p - 1) - 1) := by
  have hz : (i : ZMod p) ≠ 0 := by
    intro h'; exact hi ((ZMod.natCast_eq_zero_iff i p).1 h')
  have hf := ZMod.pow_card_sub_one_eq_one hz
  have h2 : (((i : ℤ) ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by
    push_cast; rw [hf]; ring
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h2
  have := Ob_of_dvd (p := p) (n := 1) (by simpa using h3)
  push_cast at this
  exact this

lemma Ob_Hs2_p (hp5 : 5 ≤ p) : Ob p 1 (Hs p 2 p) := by
  have hp3 : p - 1 = 2 + (p - 3) := by omega
  -- Hs 2 p = Σ i^(p-3) + Σ (i^2)⁻¹ (1 - i^(p-1))
  have h1 : Hs p 2 p = ∑ i ∈ U p p, (i : ℚ_[p]) ^ (p - 3)
      + ∑ i ∈ U p p, ((i : ℚ_[p]) ^ 2)⁻¹ * (1 - (i : ℚ_[p]) ^ (p - 1)) := by
    unfold Hs; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi
    have hi0 : (i : ℚ_[p]) ≠ 0 := by
      have := norm_U hi; intro h; rw [h] at this; simp at this
    rw [hp3, pow_add]; field_simp; ring
  have h2 : ∑ i ∈ U p p, (i : ℚ_[p]) ^ (p - 3) = ((∑ i ∈ range p, i ^ (p - 3) : ℕ) : ℚ_[p]) := by
    push_cast
    rw [sum_U_eq_sum_range]
    apply Finset.sum_congr rfl; intro i hi
    by_cases h : p ∣ i
    · have : i = 0 := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · exact h0
        · exact absurd (Nat.le_of_dvd h0 h) (by simp at hi; omega)
      subst this; have : p - 3 ≠ 0 := by omega
      simp [this]
    · simp [h]
  rw [h1, h2]
  refine Ob_add (Ob_of_dvd_nat (by simpa using dvd_sum_range_pow hp5)) ?_
  apply Ob_sum; intro i hi
  have := Ob_fermat (p := p) (mem_U.1 hi).2
  exact Ob_unit_mul (Ob_inv_U hi 2) (Ob_of_eq (Ob_neg this) (by ring))

/- ### the parameter `e` -/

/-- standing hypotheses: `e = 1` for `p ≥ 5`, `e = 0` for `p = 3` -/
structure EData (p : ℕ) [Fact p.Prime] (e : ℕ) : Prop where
  he : e ≤ 1
  hp2 : p ≠ 2
  hh : Ob p e (Hs p 2 p)
  h3 : Ob p (1 - (e : ℤ)) (3 : ℚ_[p])
  hH2 : ∀ m : ℕ, 1 ≤ m → Ob p ((m : ℤ) + 1 + e) (Hs p 2 (p ^ (m + 1)) - (p : ℚ_[p]) * Hs p 2 (p ^ m))

lemma EData_three (h3 : p = 3) : EData p 0 := by
  refine ⟨by norm_num, by omega, Ob_Hs 2 p, ?_, ?_⟩
  · have : (3 : ℚ_[p]) = (p : ℚ_[p]) := by subst h3; norm_num
    rw [this]; simpa using Ob_p (p := p)
  · intro m hm
    have := Ob_Hs_pow_succ (p := p) (by omega) 1 hm
    simpa using this

lemma EData_ge5 (hp5 : 5 ≤ p) : EData p 1 := by
  refine ⟨le_refl _, by omega, Ob_Hs2_p hp5, by simpa using Ob_three (p := p), ?_⟩
  intro m hm
  have := Ob_Hs2_pow_succ_refined (p := p) (by omega) (Ob_sum_range_sq hp5) hm
  exact Ob_cast (by push_cast; ring) this

variable {e : ℕ}

lemma Ob_Hs2_pow (E : EData p e) {m : ℕ} (hm : 1 ≤ m) :
    Ob p ((m : ℤ) + e) (Hs p 2 (p ^ m) - (p : ℚ_[p]) ^ (m - 1) * Hs p 2 p) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simpa using Ob_zero (p := p) (1 + e)
    · have h1 := E.hH2 m h0
      have h2 := ih h0
      have h3 := Ob_mul (Ob_p (p := p)) h2
      have : Hs p 2 (p ^ (m + 1)) - (p : ℚ_[p]) ^ (m + 1 - 1) * Hs p 2 p
          = (Hs p 2 (p ^ (m + 1)) - (p : ℚ_[p]) * Hs p 2 (p ^ m))
            + (p : ℚ_[p]) * (Hs p 2 (p ^ m) - (p : ℚ_[p]) ^ (m - 1) * Hs p 2 p) := by
        have : (p : ℚ_[p]) * (p : ℚ_[p]) ^ (m - 1) = (p : ℚ_[p]) ^ (m + 1 - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [← this]; ring
      rw [this]
      exact Ob_add (Ob_cast (by push_cast; ring) h1) (Ob_cast (by push_cast; ring) h3)

lemma Ob_Hs2_pow_bound (E : EData p e) {m : ℕ} (hm : 1 ≤ m) :
    Ob p ((m : ℤ) + e - 1) (Hs p 2 (p ^ m)) := by
  have h1 := Ob_Hs2_pow E hm
  have h2 : Ob p ((m : ℤ) + e - 1) ((p : ℚ_[p]) ^ (m - 1) * Hs p 2 p) := by
    have := Ob_mul (Ob_p_pow (p := p) (m - 1)) E.hh
    exact Ob_cast (by push_cast [Nat.cast_sub hm]; ring) this
  exact Ob_of_sub (Ob_mono h1 (by omega)) h2

lemma Ob_Hs2_pow_mul_bound (E : EData p e) {m : ℕ} (hm : 1 ≤ m) (u : ℕ) :
    Ob p ((m : ℤ) + e - 1) (Hs p 2 (p ^ m * u)) := by
  have hM : p ∣ p ^ m := dvd_pow_self p (by omega)
  have hMj : Ob p m ((p ^ m : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow m
  have h1 := Ob_Hs_mul (p := p) hM hMj u 2
  have h2 : Ob p ((m : ℤ) + e - 1) ((u : ℚ_[p]) * Hs p 2 (p ^ m)) :=
    Ob_unit_mul (Ob_natCast u) (Ob_Hs2_pow_bound E hm)
  exact Ob_of_sub (Ob_mono h1 (by have := E.he; omega)) h2

lemma Ob_Hs1_pow_mul_bound (E : EData p e) {m : ℕ} (hm : 1 ≤ m) (u : ℕ) :
    Ob p (2 * (m : ℤ) + e - 1) (Hs p 1 (p ^ m * u)) := by
  have hM : p ∣ p ^ m * u := Dvd.dvd.mul_right (dvd_pow_self p (by omega)) u
  have hMj : Ob p m ((p ^ m * u : ℕ) : ℚ_[p]) := by
    push_cast; exact Ob_p_pow_mul m (Ob_natCast u)
  have h1 := Ob_Hs1_approx E.hp2 hM (j := m) (by omega) hMj
  have h2 : Ob p (2 * (m : ℤ) + e - 1) (((p ^ m * u : ℕ) : ℚ_[p]) / 2 * Hs p 2 (p ^ m * u)) := by
    have := Ob_mul (Ob_mul_unit hMj (Ob_inv_two E.hp2)) (Ob_Hs2_pow_mul_bound E hm u)
    rw [div_eq_mul_inv]
    exact Ob_cast (by ring) this
  have h3 : Ob p (2 * (m : ℤ) + e - 1) (Hs p 1 (p ^ m * u) + ((p ^ m * u : ℕ) : ℚ_[p]) / 2 * Hs p 2 (p ^ m * u)) :=
    Ob_mono h1 (by have := E.he; omega)
  have := Ob_sub h3 h2
  exact Ob_of_eq this (by ring)

lemma Ob_Hs1_pow_bound (E : EData p e) {m : ℕ} (hm : 1 ≤ m) :
    Ob p (2 * (m : ℤ) + e - 1) (Hs p 1 (p ^ m)) := by
  have := Ob_Hs1_pow_mul_bound E hm 1
  simpa using this

/- ### `Λ^{(m)}(k)` -/

/-- `Λ^{(m)}(k) = ∑_{j ∈ U(p^m)} (p^m k + j)^{-2}` -/
noncomputable def Lam (p : ℕ) [Fact p.Prime] (m k : ℕ) : ℚ_[p] :=
  ∑ j ∈ U p (p ^ m), (((j : ℚ_[p]) + (p : ℚ_[p]) ^ m * k) ^ 2)⁻¹

lemma Ob_Lam (E : EData p e) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    Ob p ((m : ℤ) + e - 1) (Lam p m k) := by
  have hM : p ∣ p ^ m := dvd_pow_self p (by omega)
  have h1 : Ob p m (Lam p m k - Hs p 2 (p ^ m)) := by
    unfold Lam Hs
    apply Ob_sum_sub_sum; intro j hj
    have hb := norm_block hM hj k
    push_cast at hb
    exact Ob_inv_pow_sub (norm_U hj) hb (Ob_p_pow_mul m (Ob_natCast k)) 2
  exact Ob_of_sub (Ob_mono h1 (by have := E.he; omega)) (Ob_Hs2_pow_bound E hm)

/-- `Λ^{(m+1)}(k') = ∑_{k₀<p} Λ^{(m)}(p k' + k₀)` -/
lemma Lam_succ {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    Lam p (m + 1) k = ∑ d ∈ range p, Lam p m (p * k + d) := by
  unfold Lam
  have hM : p ∣ p ^ m := dvd_pow_self p (by omega)
  rw [pow_succ, sum_U_mul hM]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro j _
  push_cast; ring_nf

/- ### reflection identity for `Hs 1` -/

lemma Hs1_split {m n : ℕ} (hm : p ∣ m) (hn : p ∣ n) (hmn : m ≤ n) :
    Hs p 1 n = Hs p 1 (n - m) + ∑ j ∈ U p m, (((n - j : ℕ) : ℚ_[p]) ^ 1)⁻¹ := by
  unfold Hs
  rw [← Finset.sum_filter_add_sum_filter_not (U p n) (fun i => i < n - m)]
  congr 1
  · apply Finset.sum_congr
    · ext i; simp only [Finset.mem_filter, mem_U]; omega
    · intros; rfl
  · symm
    refine Finset.sum_nbij' (fun j => n - j) (fun i => n - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hpos := U_pos hj
      simp only [Finset.mem_filter, mem_U] at hj ⊢
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro hd; apply hj.2
      have := Nat.dvd_sub hn hd
      rwa [Nat.sub_sub_self (by omega)] at this
    · intro i hi
      simp only [Finset.mem_filter, mem_U] at hi ⊢
      have hne : i ≠ n - m := by
        intro h; apply hi.1.2; rw [h]; exact Nat.dvd_sub hn hm
      refine ⟨by omega, ?_⟩
      intro hd; apply hi.1.2
      have := Nat.dvd_sub hn hd
      rwa [Nat.sub_sub_self (by omega)] at this
    · intro j hj; simp only [mem_U] at hj; show n - (n - j) = j; omega
    · intro i hi; simp only [Finset.mem_filter, mem_U] at hi; show n - (n - i) = i; omega
    · intro j _; rfl

lemma Hs1_reflect {m n : ℕ} (hm : p ∣ m) (hn : p ∣ n) (hmn : m ≤ n) :
    Hs p 1 m - Hs p 1 (n - m)
      = (n : ℚ_[p]) * ∑ j ∈ U p m, ((j : ℚ_[p]) * ((n - j : ℕ) : ℚ_[p]))⁻¹ - Hs p 1 n := by
  have hsplit := Hs1_split (p := p) hm hn hmn
  have : Hs p 1 m - Hs p 1 (n - m)
      = (Hs p 1 m + ∑ j ∈ U p m, (((n - j : ℕ) : ℚ_[p]) ^ 1)⁻¹) - Hs p 1 n := by
    rw [hsplit]; ring
  rw [this]
  congr 1
  unfold Hs
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  have ha := norm_U hj
  have ha0 : (j : ℚ_[p]) ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : ((n - j : ℕ) : ℚ_[p]) ≠ 0 := by
    have : ¬ p ∣ n - j := by
      intro hd; apply (mem_U.1 hj).2
      have := Nat.dvd_sub hn hd
      rwa [Nat.sub_sub_self (by have := (mem_U.1 hj).1; omega)] at this
    have := norm_nat_eq_one_of_not_dvd (p := p) this
    intro h; rw [h] at this; simp at this
  have hab : (j : ℚ_[p]) + ((n - j : ℕ) : ℚ_[p]) = n := by
    rw [Nat.cast_sub (by have := (mem_U.1 hj).1; omega)]; ring
  rw [← hab]
  field_simp
  ring

/-- `Hs1 m - Hs1 (n - m) + n Hs2 m = O(p^{2s+1+e})` for `n = p^(s+1)`, `p ∣ m ≤ n` -/
lemma Ob_Hs1_reflect_diff (E : EData p e) {s m : ℕ} (hm : p ∣ m) (hmn : m ≤ p ^ (s + 1)) :
    Ob p (2 * (s : ℤ) + 1 + e)
      (Hs p 1 m - Hs p 1 (p ^ (s + 1) - m) + (p : ℚ_[p]) ^ (s + 1) * Hs p 2 m) := by
  have hn : p ∣ p ^ (s + 1) := dvd_pow_self p (by omega)
  have hr := Hs1_reflect (p := p) hm hn hmn
  push_cast at hr
  rw [hr]
  -- Σ (j (n-j))⁻¹ + Hs 2 m = n Σ (j² (n-j))⁻¹
  have hkey : ∑ j ∈ U p m, ((j : ℚ_[p]) * ((p ^ (s + 1) - j : ℕ) : ℚ_[p]))⁻¹ + Hs p 2 m
      = (p : ℚ_[p]) ^ (s + 1) * ∑ j ∈ U p m, (((j : ℚ_[p]) ^ 2)⁻¹ * (((p ^ (s + 1) - j : ℕ) : ℚ_[p]))⁻¹) := by
    unfold Hs
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    have ha := norm_U hj
    have ha0 : (j : ℚ_[p]) ≠ 0 := by intro h; rw [h] at ha; simp at ha
    have hjn : j ≤ p ^ (s + 1) := by have := (mem_U.1 hj).1; omega
    have hb0 : ((p ^ (s + 1) - j : ℕ) : ℚ_[p]) ≠ 0 := by
      have : ¬ p ∣ p ^ (s + 1) - j := by
        intro hd; apply (mem_U.1 hj).2
        have := Nat.dvd_sub hn hd
        rwa [Nat.sub_sub_self hjn] at this
      have := norm_nat_eq_one_of_not_dvd (p := p) this
      intro h; rw [h] at this; simp at this
    have hab : (j : ℚ_[p]) + ((p ^ (s + 1) - j : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ (s + 1) := by
      rw [Nat.cast_sub hjn]; push_cast; ring
    rw [← hab]
    field_simp
  have hS : Ob p 0 (∑ j ∈ U p m, (((j : ℚ_[p]) ^ 2)⁻¹ * (((p ^ (s + 1) - j : ℕ) : ℚ_[p]))⁻¹)) := by
    apply Ob_sum; intro j hj
    have hjn : j ≤ p ^ (s + 1) := by have := (mem_U.1 hj).1; omega
    have : ¬ p ∣ p ^ (s + 1) - j := by
      intro hd; apply (mem_U.1 hj).2
      have := Nat.dvd_sub hn hd
      rwa [Nat.sub_sub_self hjn] at this
    exact Ob_mul_unit (Ob_inv_U hj 2) (Ob_inv_of_norm_one (norm_nat_eq_one_of_not_dvd this))
  have h1 : Ob p (2 * (s : ℤ) + 2) ((p : ℚ_[p]) ^ (s + 1) *
      (∑ j ∈ U p m, ((j : ℚ_[p]) * ((p ^ (s + 1) - j : ℕ) : ℚ_[p]))⁻¹ + Hs p 2 m)) := by
    rw [hkey]
    have := Ob_mul (Ob_p_pow (p := p) (s + 1)) (Ob_mul (Ob_p_pow (p := p) (s + 1)) hS)
    exact Ob_cast (by push_cast; ring) this
  have h2 : Ob p (2 * (s : ℤ) + 1 + e) (Hs p 1 (p ^ (s + 1))) := by
    have := Ob_Hs1_pow_bound E (m := s + 1) (by omega)
    exact Ob_cast (by push_cast; ring) this
  have := Ob_sub (Ob_mono h1 (by have := E.he; omega)) h2
  exact Ob_of_eq this (by ring)

/- ### the deep-level harmonic values -/

/-- `Hs1 (p^s u) ≡ -(u²/2) p^(2s-1) h  mod p^(2s+e)` -/
lemma Ob_Hs1_deep (E : EData p e) {s : ℕ} (hs : 1 ≤ s) (u : ℕ) :
    Ob p (2 * (s : ℤ) + e)
      (Hs p 1 (p ^ s * u) + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (2 * s - 1) * Hs p 2 p) := by
  have hps : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hM : p ∣ p ^ s * u := Dvd.dvd.mul_right hps u
  have hMj : Ob p s ((p ^ s * u : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow_mul s (Ob_natCast u)
  have hpsO : Ob p s ((p ^ s : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow s
  have hA := Ob_Hs1_approx E.hp2 hM (j := s) (by omega) hMj
  have hB := Ob_Hs2_mul E.hp2 hps (j := s) hpsO u
  have hC := Ob_Hs2_pow E hs
  set M : ℚ_[p] := ((p ^ s * u : ℕ) : ℚ_[p]) with hMdef
  have hMeq : M = (p : ℚ_[p]) ^ s * u := by rw [hMdef]; push_cast; ring
  have hpow : (p : ℚ_[p]) ^ s * (p : ℚ_[p]) ^ (s - 1) = (p : ℚ_[p]) ^ (2 * s - 1) := by
    rw [← pow_add]; congr 1; omega
  have key : Hs p 1 (p ^ s * u) + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (2 * s - 1) * Hs p 2 p
      = (Hs p 1 (p ^ s * u) + M / 2 * Hs p 2 (p ^ s * u))
        - M / 2 * (Hs p 2 (p ^ s * u) - (u : ℚ_[p]) * Hs p 2 (p ^ s))
        - M * u / 2 * (Hs p 2 (p ^ s) - (p : ℚ_[p]) ^ (s - 1) * Hs p 2 p) := by
    rw [hMeq, ← hpow]; ring
  rw [key]
  have h1 : Ob p (2 * (s : ℤ) + e) (Hs p 1 (p ^ s * u) + M / 2 * Hs p 2 (p ^ s * u)) :=
    Ob_mono hA (by have := E.he; omega)
  have h2 : Ob p (2 * (s : ℤ) + e) (M / 2 * (Hs p 2 (p ^ s * u) - (u : ℚ_[p]) * Hs p 2 (p ^ s))) := by
    have := Ob_mul (Ob_mul_unit hMj (Ob_inv_two E.hp2)) hB
    rw [div_eq_mul_inv]
    have h' : Ob p (3 * (s : ℤ)) (M * 2⁻¹ * (Hs p 2 (p ^ s * u) - (u : ℚ_[p]) * Hs p 2 (p ^ s))) :=
      Ob_cast (by ring) this
    exact Ob_mono h' (by have := E.he; omega)
  have h3 : Ob p (2 * (s : ℤ) + e) (M * (u : ℚ_[p]) / 2 * (Hs p 2 (p ^ s) - (p : ℚ_[p]) ^ (s - 1) * Hs p 2 p)) := by
    have := Ob_mul (Ob_mul_unit (Ob_mul_unit hMj (Ob_natCast u)) (Ob_inv_two E.hp2)) hC
    rw [div_eq_mul_inv]
    exact Ob_cast (by push_cast; ring) this
  exact Ob_sub (Ob_sub h1 h2) h3

/-- `Hs1 (p^s u) - Hs1 (p^s (p-u)) ≡ -u p^(2s) h  mod p^(2s+1+e)` -/
lemma Ob_Hs1_deep_diff (E : EData p e) {s : ℕ} (hs : 1 ≤ s) {u : ℕ} (hu : u ≤ p) :
    Ob p (2 * (s : ℤ) + 1 + e)
      (Hs p 1 (p ^ s * u) - Hs p 1 (p ^ s * (p - u)) + (u : ℚ_[p]) * (p : ℚ_[p]) ^ (2 * s) * Hs p 2 p) := by
  have hps : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hM : p ∣ p ^ s * u := Dvd.dvd.mul_right hps u
  have hmn : p ^ s * u ≤ p ^ (s + 1) := by
    rw [pow_succ]; exact Nat.mul_le_mul_left _ hu
  have hsub : p ^ (s + 1) - p ^ s * u = p ^ s * (p - u) := by
    rw [pow_succ, Nat.mul_sub]
  have hR := Ob_Hs1_reflect_diff E (s := s) hM hmn
  rw [hsub] at hR
  have hpsO : Ob p s ((p ^ s : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow s
  have hB := Ob_Hs2_mul E.hp2 hps (j := s) hpsO u
  have hC := Ob_Hs2_pow E hs
  have hpow : (p : ℚ_[p]) ^ (s + 1) * (p : ℚ_[p]) ^ (s - 1) = (p : ℚ_[p]) ^ (2 * s) := by
    rw [← pow_add]; congr 1; omega
  have key : Hs p 1 (p ^ s * u) - Hs p 1 (p ^ s * (p - u)) + (u : ℚ_[p]) * (p : ℚ_[p]) ^ (2 * s) * Hs p 2 p
      = (Hs p 1 (p ^ s * u) - Hs p 1 (p ^ s * (p - u)) + (p : ℚ_[p]) ^ (s + 1) * Hs p 2 (p ^ s * u))
        - (p : ℚ_[p]) ^ (s + 1) * (Hs p 2 (p ^ s * u) - (u : ℚ_[p]) * Hs p 2 (p ^ s))
        - (p : ℚ_[p]) ^ (s + 1) * u * (Hs p 2 (p ^ s) - (p : ℚ_[p]) ^ (s - 1) * Hs p 2 p) := by
    rw [← hpow]; ring
  rw [key]
  have h2 : Ob p (2 * (s : ℤ) + 1 + e) ((p : ℚ_[p]) ^ (s + 1) * (Hs p 2 (p ^ s * u) - (u : ℚ_[p]) * Hs p 2 (p ^ s))) := by
    have := Ob_mul (Ob_p_pow (p := p) (s + 1)) hB
    have h' : Ob p (3 * (s : ℤ) + 1) ((p : ℚ_[p]) ^ (s + 1) * (Hs p 2 (p ^ s * u) - (u : ℚ_[p]) * Hs p 2 (p ^ s))) :=
      Ob_cast (by push_cast; ring) this
    exact Ob_mono h' (by have := E.he; omega)
  have h3 : Ob p (2 * (s : ℤ) + 1 + e) ((p : ℚ_[p]) ^ (s + 1) * (u : ℚ_[p]) * (Hs p 2 (p ^ s) - (p : ℚ_[p]) ^ (s - 1) * Hs p 2 p)) := by
    have := Ob_mul (Ob_mul_unit (Ob_p_pow (p := p) (s + 1)) (Ob_natCast u)) hC
    exact Ob_cast (by push_cast; ring) this
  exact Ob_sub (Ob_sub hR h2) h3

end A357565Proof

-- ===== Dev6 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `b(M,k) = C(M+k-1, k)` -/
noncomputable def bb (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] := ((M + k - 1).choose k : ℚ_[p])
/-- `c(M,k) = C(M+k, k)` -/
noncomputable def cc (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] := ((M + k).choose k : ℚ_[p])
/-- `ρ_{l,M}(m) = ∏_{i<m, p∤i} (1 + l M / i)` -/
noncomputable def rho (p : ℕ) [Fact p.Prime] (l M m : ℕ) : ℚ_[p] :=
  ∏ i ∈ U p m, (1 + (l : ℚ_[p]) * M / i)

lemma cc_zero (M : ℕ) : cc p M 0 = 1 := by simp [cc]

lemma cc_succ (M k : ℕ) : cc p M (k + 1) = cc p M k * (1 + (M : ℚ_[p]) / (k + 1)) := by
  have h := Nat.add_one_mul_choose_eq (M + k) k
  have hk : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h' : ((M : ℚ_[p]) + k + 1) * cc p M k = cc p M (k + 1) * ((k : ℚ_[p]) + 1) := by
    unfold cc
    rw [show M + (k + 1) = M + k + 1 by ring]
    exact_mod_cast h
  calc cc p M (k + 1) = cc p M (k + 1) * ((k : ℚ_[p]) + 1) / ((k : ℚ_[p]) + 1) := by field_simp
    _ = ((M : ℚ_[p]) + k + 1) * cc p M k / ((k : ℚ_[p]) + 1) := by rw [h']
    _ = cc p M k * (1 + (M : ℚ_[p]) / (k + 1)) := by field_simp; ring

/-- `c(M,k) = ∏_{i ≤ k} (1 + M/i)` (with the convention `M/0 = 0`) -/
lemma cc_eq_prod (M k : ℕ) : cc p M k = ∏ i ∈ range (k + 1), (1 + (M : ℚ_[p]) / i) := by
  induction k with
  | zero => simp [cc_zero]
  | succ k ih =>
    rw [cc_succ, ih, Finset.prod_range_succ (fun i => 1 + (M : ℚ_[p]) / i) (k + 1)]; push_cast; ring

lemma Ob_cc (M k : ℕ) : Ob p 0 (cc p M k) := Ob_natCast _

lemma bb_zero (M : ℕ) : bb p M 0 = 1 := by simp [bb]

lemma bb_succ (M k : ℕ) : bb p M (k + 1) = (M : ℚ_[p]) / (k + 1) * cc p M k := by
  unfold bb cc
  have h := Nat.choose_succ_right_eq (M + k) k
  rw [show M + k - k = M by omega] at h
  have h' : ((M + k).choose (k + 1) : ℚ_[p]) * ((k + 1 : ℕ) : ℚ_[p])
      = ((M + k).choose k : ℚ_[p]) * (M : ℚ_[p]) := by exact_mod_cast h
  push_cast at h'
  have hk : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [show M + (k + 1) - 1 = M + k by omega]
  field_simp
  linear_combination h'

lemma bb_eq (M : ℕ) {k : ℕ} (hk : 1 ≤ k) : bb p M k = (M : ℚ_[p]) / k * cc p M (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [bb_succ]; simp

lemma Ob_bb (M k : ℕ) : Ob p 0 (bb p M k) := Ob_natCast _

/-- `b(M, j+1) = b(M,j) (M+j)/(j+1)` for `M ≥ 1` -/
lemma bb_succ_ratio {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    bb p M (j + 1) = bb p M j * (((M : ℚ_[p]) + j) / (j + 1)) := by
  have h := Nat.add_one_mul_choose_eq (M + j - 1) j
  rw [show M + j - 1 + 1 = M + j by omega] at h
  have hj : ((j : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have h' : ((M : ℚ_[p]) + j) * bb p M j = bb p M (j + 1) * ((j : ℚ_[p]) + 1) := by
    unfold bb
    rw [show M + (j + 1) - 1 = M + j by omega]
    exact_mod_cast h
  calc bb p M (j + 1) = bb p M (j + 1) * ((j : ℚ_[p]) + 1) / ((j : ℚ_[p]) + 1) := by field_simp
    _ = ((M : ℚ_[p]) + j) * bb p M j / ((j : ℚ_[p]) + 1) := by rw [h']
    _ = bb p M j * (((M : ℚ_[p]) + j) / (j + 1)) := by ring

lemma Ob_rho_sub_one {l M m : ℕ} {j : ℕ} (h : Ob p j ((l : ℚ_[p]) * (M : ℚ_[p]))) : Ob p j (rho p l M m - 1) := by
  unfold rho
  apply Ob_prod_sub_one
  intro i hi
  rw [div_eq_mul_inv]
  exact Ob_mul_unit h (Ob_inv_of_norm_one (norm_U hi))

lemma Ob_rho {l M m : ℕ} : Ob p 0 (rho p l M m) := by
  have := Ob_rho_sub_one (p := p) (l := l) (M := M) (m := m) (j := 0)
    (Ob_mul_unit (Ob_natCast l) (Ob_natCast M))
  exact Ob_of_sub (Ob_of_eq this (by ring)) Ob_one

/-- multiples of `p` in `range (k+1)` -/
lemma filter_dvd_range (k : ℕ) :
    (range (k + 1)).filter (fun i => p ∣ i) = (range (k / p + 1)).image (fun i => p * i) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  have hp0 : 0 < p := hp.out.pos
  constructor
  · rintro ⟨h1, ⟨c, rfl⟩⟩
    refine ⟨c, ?_, rfl⟩
    have : c ≤ k / p := by
      rw [Nat.le_div_iff_mul_le hp0]; rw [mul_comm]; omega
    omega
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, dvd_mul_right p c⟩
    have : c ≤ k / p := by omega
    have := (Nat.le_div_iff_mul_le hp0).1 this
    rw [mul_comm]; omega

/-- descent for `c`: `c(pN, k) = c(N, ⌊k/p⌋) ρ_{1,pN}(k+1)` -/
lemma cc_descent (N k : ℕ) : cc p (p * N) k = cc p N (k / p) * rho p 1 (p * N) (k + 1) := by
  rw [cc_eq_prod, cc_eq_prod]
  unfold rho U
  rw [← Finset.prod_filter_mul_prod_filter_not (range (k + 1)) (fun i => p ∣ i)]
  congr 1
  · rw [filter_dvd_range]
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro i _
      have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      push_cast
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; simp
      · have hi : (i : ℚ_[p]) ≠ 0 := by exact_mod_cast h0.ne'
        field_simp
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos h
  · apply Finset.prod_congr rfl
    intro i _
    push_cast; ring

/-- descent for `b` at multiples of `p` -/
lemma bb_descent_mul (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    bb p (p * N) (p * k) = bb p N k * rho p 1 (p * N) (p * k) := by
  have hpk : 1 ≤ p * k := Nat.mul_pos hp.out.pos hk
  rw [bb_eq _ hpk, bb_eq _ hk, cc_descent]
  have hdiv : (p * k - 1) / p = k - 1 := by
    have hp1 : 1 ≤ p := hp.out.pos
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show p * (k' + 1) - 1 = p * k' + (p - 1) by rw [Nat.mul_succ]; omega]
    rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt (by omega)]; simp
  rw [hdiv, show p * k - 1 + 1 = p * k by omega]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hk0 : (k : ℚ_[p]) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  push_cast
  field_simp

/-- descent for `b` at non-multiples of `p` -/
lemma bb_descent_nondiv (N : ℕ) {k : ℕ} (hk : ¬ p ∣ k) :
    bb p (p * N) k = ((p : ℚ_[p]) * (N : ℚ_[p])) / (k : ℚ_[p]) * cc p N (k / p) * rho p 1 (p * N) k := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; exact absurd (dvd_zero p) hk
    · exact h0
  rw [bb_eq _ hk1, cc_descent]
  have hdiv : (k - 1) / p = k / p := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exact absurd h0 hp.out.ne_zero
    · rw [Nat.succ_div]
      simp [hk]
  rw [hdiv, show k - 1 + 1 = k by omega]
  push_cast; ring

/-- `1 ≤ j < p^s` implies `p^(s-1)/j` is a p-adic integer -/
lemma Ob_pow_div {s j : ℕ} (hj : 0 < j) (hjs : j < p ^ s) : Ob p 0 ((p : ℚ_[p]) ^ (s - 1) / (j : ℚ_[p])) := by
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show j ≠ 0 by omega) p hp.out.ne_one
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · subst h0; simp at hj
    · exact h0
  have hv : v < s := by
    by_contra h
    push_neg at h
    have : p ^ s ≤ p ^ v * u := by
      calc p ^ s ≤ p ^ v := Nat.pow_le_pow_right hp.out.pos h
        _ ≤ p ^ v * u := Nat.le_mul_of_pos_right _ hu0
    omega
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu0' : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast hu0.ne'
  have : (p : ℚ_[p]) ^ (s - 1) / ((p ^ v * u : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ (s - 1 - v) * (u : ℚ_[p])⁻¹ := by
    push_cast
    have hsplit : (p : ℚ_[p]) ^ (s - 1) = (p : ℚ_[p]) ^ (s - 1 - v) * (p : ℚ_[p]) ^ v := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    field_simp
  rw [this]
  exact Ob_mul_unit (Ob_mono (Ob_p_pow (s - 1 - v)) (by omega)) (Ob_inv_nat_of_not_dvd hu)

/-- `p^s / j` has norm `≤ p^{-(s-v)}` when `j = p^v u`, `p ∤ u` -/
lemma Ob_pow_div' {s v u : ℕ} (hu : ¬ p ∣ u) (hvs : v ≤ s) :
    Ob p ((s : ℤ) - v) ((p : ℚ_[p]) ^ s / ((p ^ v * u : ℕ) : ℚ_[p])) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu0 : (u : ℚ_[p]) ≠ 0 := by
    have : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
    exact_mod_cast this
  have : (p : ℚ_[p]) ^ s / ((p ^ v * u : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ (s - v) * (u : ℚ_[p])⁻¹ := by
    push_cast
    have hsplit : (p : ℚ_[p]) ^ s = (p : ℚ_[p]) ^ (s - v) * (p : ℚ_[p]) ^ v := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    field_simp
  rw [this]
  exact Ob_cast (by push_cast [Nat.cast_sub hvs]; ring) (Ob_mul_unit (Ob_p_pow (s - v)) (Ob_inv_nat_of_not_dvd hu))

/-- `c(p^s, k) ≡ 1 mod p` for `k < p^s` -/
lemma Ob_cc_sub_one {s k : ℕ} (hs : 1 ≤ s) (hk : k < p ^ s) : Ob p 1 (cc p (p ^ s) k - 1) := by
  rw [cc_eq_prod]
  apply Ob_prod_sub_one
  intro i hi
  simp only [Finset.mem_range] at hi
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; simpa using Ob_zero (p := p) 1
  · have := Ob_pow_div (p := p) (s := s) h0 (by omega)
    have h2 : ((p ^ s : ℕ) : ℚ_[p]) / i = (p : ℚ_[p]) * ((p : ℚ_[p]) ^ (s - 1) / i) := by
      push_cast
      rw [mul_div_assoc', ← pow_succ']; congr 2; omega
    rw [h2]
    exact Ob_mul_unit Ob_p this

end A357565Proof

-- ===== Dev7 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Θ_M(k) = ∏_{j=k+1}^{M-k} (1 - 2M/j)` -/
noncomputable def Theta (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] :=
  ∏ j ∈ Ico (k + 1) (M - k + 1), (1 - 2 * (M : ℚ_[p]) / j)
/-- `Ψ_M(k) = ∏_{k<j<M/2} (1 + 2M²/(j(M-j)))` -/
noncomputable def Psi (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] :=
  ∏ j ∈ Ico (k + 1) ((M + 1) / 2), (1 + 2 * (M : ℚ_[p]) ^ 2 / (j * ((M : ℚ_[p]) - j)))
noncomputable def mu (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] := 1 - Psi p M k
/-- `Φ_N(k) = ∏_{k<j<pN/2, p∤j} (1 + 2(pN)²/(j(pN-j)))` -/
noncomputable def Phi (p : ℕ) [Fact p.Prime] (N k : ℕ) : ℚ_[p] :=
  ∏ j ∈ (Ico (k + 1) ((p * N + 1) / 2)).filter (fun j => ¬ p ∣ j),
    (1 + 2 * ((p * N : ℕ) : ℚ_[p]) ^ 2 / (j * (((p * N : ℕ) : ℚ_[p]) - j)))
/-- `ε_M(k) = 1 - Θ_M(k)` -/
noncomputable def eps (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] := 1 - Theta p M k

/-- reflection: `b(M, M-k) = -b(M,k) Θ_M(k)` for `M` odd, `1 ≤ k`, `2k+1 ≤ M` -/
lemma bb_reflect_aux (M : ℕ) : ∀ n k : ℕ, 1 ≤ k → 2 * k + 1 + 2 * n = M →
    bb p M (M - k) = - bb p M k * Theta p M k := by
  intro n
  induction n with
  | zero =>
    intro k hk hM
    have hM1 : 1 ≤ M := by omega
    have hMk : M - k = k + 1 := by omega
    rw [hMk, bb_succ_ratio hM1]
    unfold Theta
    rw [hMk, show k + 1 + 1 = (k + 1) + 1 by rfl, Finset.prod_Ico_succ_top (le_refl _), Finset.Ico_self,
      Finset.prod_empty, one_mul]
    have hk1 : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hMc : (M : ℚ_[p]) = 2 * k + 1 := by exact_mod_cast (by omega : M = 2 * k + 1)
    push_cast
    rw [hMc]
    field_simp
    ring
  | succ n ih =>
    intro k hk hM
    have hM1 : 1 ≤ M := by omega
    have h1 := ih (k + 1) (by omega) (by omega)
    -- b(M, M-k) = b(M, M-k-1) (M + (M-k-1))/(M-k)
    have h2 : bb p M (M - k) = bb p M (M - (k + 1)) * (((M : ℚ_[p]) + ((M - (k + 1) : ℕ) : ℚ_[p])) / (((M - (k + 1) : ℕ) : ℚ_[p]) + 1)) := by
      have := bb_succ_ratio (p := p) hM1 (M - (k + 1))
      rw [show M - (k + 1) + 1 = M - k by omega] at this
      exact this
    have h3 : bb p M (k + 1) = bb p M k * (((M : ℚ_[p]) + k) / (k + 1)) := bb_succ_ratio hM1 k
    have hT : Theta p M k = (1 - 2 * (M : ℚ_[p]) / (k + 1)) * Theta p M (k + 1) * (1 - 2 * (M : ℚ_[p]) / ((M - k : ℕ) : ℚ_[p])) := by
      unfold Theta
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : k + 1 < M - k + 1)]
      rw [show M - k + 1 = (M - k) + 1 by rfl, Finset.prod_Ico_succ_top (by omega : k + 1 + 1 ≤ M - k)]
      rw [show M - (k + 1) + 1 = M - k by omega]
      push_cast; ring
    rw [h2, h1, h3, hT]
    have hc1 : ((M - (k + 1) : ℕ) : ℚ_[p]) = (M : ℚ_[p]) - k - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((M - k : ℕ) : ℚ_[p]) = (M : ℚ_[p]) - k := by
      rw [Nat.cast_sub (by omega)]
    rw [hc1, hc2]
    have hk1 : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hMk : ((M : ℚ_[p]) - k) ≠ 0 := by
      have : ((M - k : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show M - k ≠ 0 by omega)
      rwa [hc2] at this
    have hMk1 : ((M : ℚ_[p]) - k - 1 + 1) ≠ 0 := by
      rw [sub_add_cancel]; exact hMk
    field_simp
    ring

lemma bb_reflect {M k : ℕ} (hM : Odd M) (hk : 1 ≤ k) (hkM : 2 * k + 1 ≤ M) :
    bb p M (M - k) = - bb p M k * Theta p M k := by
  obtain ⟨t, ht⟩ := hM
  exact bb_reflect_aux M (t - k) k hk (by omega)

/-- `Θ_M(k) = (1 - 2M/(M-k)) Ψ_M(k)` -/
lemma Theta_eq {M k : ℕ} (hM : Odd M) (hkM : 2 * k + 1 ≤ M) :
    Theta p M k = (1 - 2 * (M : ℚ_[p]) / ((M : ℚ_[p]) - k)) * Psi p M k := by
  obtain ⟨t, ht⟩ := hM
  have hh : (M + 1) / 2 = t + 1 := by omega
  unfold Theta Psi
  rw [show M - k + 1 = (M - k) + 1 by rfl, Finset.prod_Ico_succ_top (by omega : k + 1 ≤ M - k)]
  rw [← Finset.prod_Ico_consecutive _ (by omega : k + 1 ≤ (M + 1) / 2) (by omega : (M + 1) / 2 ≤ M - k)]
  have hrefl : ∏ j ∈ Ico ((M + 1) / 2) (M - k), (1 - 2 * (M : ℚ_[p]) / j)
      = ∏ j ∈ Ico (k + 1) ((M + 1) / 2), (1 - 2 * (M : ℚ_[p]) / ((M - j : ℕ) : ℚ_[p])) := by
    rw [Finset.prod_Ico_reflect (fun j => (1 - 2 * (M : ℚ_[p]) / (j : ℚ_[p]))) (k + 1) (by omega : (M + 1) / 2 ≤ M + 1)]
    rw [show M + 1 - (M + 1) / 2 = (M + 1) / 2 by omega, show M + 1 - (k + 1) = M - k by omega]
  rw [hrefl, ← Finset.prod_mul_distrib]
  have hc : ((M - k : ℕ) : ℚ_[p]) = (M : ℚ_[p]) - k := by rw [Nat.cast_sub (by omega)]
  rw [hc, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_Ico] at hj
  have hj0 : (j : ℚ_[p]) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hcj : ((M - j : ℕ) : ℚ_[p]) = (M : ℚ_[p]) - j := by rw [Nat.cast_sub (by omega)]
  have hMj : ((M : ℚ_[p]) - j) ≠ 0 := by
    have : ((M - j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show M - j ≠ 0 by omega)
    rwa [hcj] at this
  rw [hcj]
  field_simp
  ring

/-- `ε_M(k) = 2M/(M-k) - ((M+k)/(M-k)) μ_M(k)` -/
lemma eps_eq {M k : ℕ} (hM : Odd M) (hkM : 2 * k + 1 ≤ M) :
    eps p M k = 2 * (M : ℚ_[p]) / ((M : ℚ_[p]) - k) - (((M : ℚ_[p]) + k) / ((M : ℚ_[p]) - k)) * mu p M k := by
  unfold eps mu
  rw [Theta_eq hM hkM]
  have hMk : ((M : ℚ_[p]) - k) ≠ 0 := by
    have : ((M - k : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show M - k ≠ 0 by omega)
    rwa [Nat.cast_sub (by omega)] at this
  field_simp
  ring

/-- `D_M(k) = b(M,k) + b(M,M-k) = b(M,k) ε_M(k)` -/
lemma D_eq {M k : ℕ} (hM : Odd M) (hk : 1 ≤ k) (hkM : 2 * k + 1 ≤ M) :
    bb p M k + bb p M (M - k) = bb p M k * eps p M k := by
  rw [bb_reflect hM hk hkM]; unfold eps; ring

/- ### bounds -/

lemma Ob_pow_div_one {s j : ℕ} (hs : 1 ≤ s) (hj : 0 < j) (hjs : j < p ^ s) :
    Ob p 1 ((p : ℚ_[p]) ^ s / (j : ℚ_[p])) := by
  have := Ob_pow_div (p := p) (s := s) hj hjs
  have h2 : (p : ℚ_[p]) ^ s / j = (p : ℚ_[p]) * ((p : ℚ_[p]) ^ (s - 1) / j) := by
    rw [mul_div_assoc', ← pow_succ']; congr 2; omega
  rw [h2]
  exact Ob_mul_unit Ob_p this

/-- `μ_{p^s}(k) = O(p^2)` -/
lemma Ob_mu {s : ℕ} (hs : 1 ≤ s) (k : ℕ) : Ob p 2 (mu p (p ^ s) k) := by
  unfold mu Psi
  have := Ob_prod_sub_one (p := p) (Ico (k + 1) ((p ^ s + 1) / 2)) (j := 2)
    (x := fun j : ℕ => 2 * ((p ^ s : ℕ) : ℚ_[p]) ^ 2 / ((j : ℚ_[p]) * (((p ^ s : ℕ) : ℚ_[p]) - (j : ℚ_[p])))) ?_
  · exact Ob_of_eq (Ob_neg this) (by ring)
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    have hj0 : 0 < j := by omega
    have hjs : j < p ^ s := by omega
    have hjs' : p ^ s - j < p ^ s := by omega
    have hjs0 : 0 < p ^ s - j := by omega
    have h1 := Ob_pow_div_one (p := p) hs hj0 hjs
    have h2 := Ob_pow_div_one (p := p) hs hjs0 hjs'
    have hc : (((p ^ s - j : ℕ) : ℚ_[p])) = ((p ^ s : ℕ) : ℚ_[p]) - j := by
      rw [Nat.cast_sub (by omega)]
    have hj0' : (j : ℚ_[p]) ≠ 0 := by exact_mod_cast hj0.ne'
    have hMj : (((p ^ s : ℕ) : ℚ_[p]) - j) ≠ 0 := by
      rw [← hc]; exact_mod_cast hjs0.ne'
    have : 2 * ((p ^ s : ℕ) : ℚ_[p]) ^ 2 / (j * (((p ^ s : ℕ) : ℚ_[p]) - j))
        = 2 * (((p : ℚ_[p]) ^ s / j) * ((p : ℚ_[p]) ^ s / ((p ^ s - j : ℕ) : ℚ_[p]))) := by
      rw [hc]; push_cast; field_simp
    dsimp only
    rw [this]
    have h := Ob_unit_mul Ob_two (Ob_mul h1 h2)
    exact Ob_mono h (by norm_num)

/-- `1 - Φ_{p^s}(k) = O(p^(2s+2))` -/
lemma Ob_one_sub_Phi (s k : ℕ) : Ob p (2 * (s : ℤ) + 2) (1 - Phi p (p ^ s) k) := by
  unfold Phi
  have := Ob_prod_sub_one (p := p) ((Ico (k + 1) ((p * p ^ s + 1) / 2)).filter (fun j => ¬ p ∣ j))
    (j := 2 * s + 2)
    (x := fun j : ℕ => 2 * ((p * p ^ s : ℕ) : ℚ_[p]) ^ 2 / ((j : ℚ_[p]) * (((p * p ^ s : ℕ) : ℚ_[p]) - (j : ℚ_[p])))) ?_
  · exact Ob_of_eq (Ob_cast (by push_cast; ring) (Ob_neg this)) (by ring)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    have hjle : j ≤ p * p ^ s := by omega
    have hnd : ¬ p ∣ p * p ^ s - j := by
      intro hd
      apply hj3
      have := Nat.dvd_sub (dvd_mul_right p (p ^ s)) hd
      rwa [Nat.sub_sub_self hjle] at this
    have hc : (((p * p ^ s - j : ℕ) : ℚ_[p])) = ((p * p ^ s : ℕ) : ℚ_[p]) - j := by
      rw [Nat.cast_sub hjle]
    dsimp only
    rw [← hc, div_eq_mul_inv, mul_inv]
    have hM : Ob p ((s + 1) * 2 : ℕ) (((p * p ^ s : ℕ) : ℚ_[p]) ^ 2) := by
      have : ((p * p ^ s : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ (s + 1) := by push_cast; ring
      rw [this, ← pow_mul]
      exact Ob_p_pow (p := p) ((s + 1) * 2)
    have h := Ob_mul_unit (Ob_unit_mul Ob_two hM)
      (Ob_mul_unit (Ob_inv_nat_of_not_dvd hj3) (Ob_inv_nat_of_not_dvd hnd))
    exact Ob_mono h (by push_cast; omega)

/-- valuation of `p^s - k` equals that of `k` -/
lemma sub_pow_eq {s v u : ℕ} (hu : ¬ p ∣ u) (hvs : v < s) (hk : p ^ v * u < p ^ s) :
    ∃ u', ¬ p ∣ u' ∧ p ^ s - p ^ v * u = p ^ v * u' := by
  refine ⟨p ^ (s - v) - u, ?_, ?_⟩
  · intro hd
    have hpd : p ∣ p ^ (s - v) := dvd_pow_self p (by omega)
    have hu' : u ≤ p ^ (s - v) := by
      by_contra h; push_neg at h
      have : p ^ s < p ^ v * u := by
        calc p ^ s = p ^ v * p ^ (s - v) := by rw [← pow_add]; congr 1; omega
          _ < p ^ v * u := Nat.mul_lt_mul_of_pos_left h (pow_pos hp.out.pos v)
      omega
    have := Nat.dvd_sub hpd hd
    rw [Nat.sub_sub_self hu'] at this
    exact hu this
  · rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hvs.le]

/-- `|b(p^s, k)| ≤ p^{-(s-v)}` for `k = p^v u`, `p ∤ u`, `v ≤ s` -/
lemma Ob_bb_level {s v u : ℕ} (hu : ¬ p ∣ u) (hvs : v ≤ s) :
    Ob p ((s : ℤ) - v) (bb p (p ^ s) (p ^ v * u)) := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  have hk : 1 ≤ p ^ v * u := Nat.mul_pos (pow_pos hp.out.pos v) (Nat.pos_of_ne_zero hu0)
  rw [bb_eq _ hk]
  have h := Ob_pow_div' (p := p) hu hvs
  push_cast at h ⊢
  exact Ob_mul_unit h (Ob_cc _ _)

/-- `|ε_{p^s}(k)| ≤ p^{-t}` for `t ≤ 2`, `t ≤ s - v` where `k = p^v u`, `2k+1 ≤ p^s` -/
lemma Ob_eps {s v u : ℕ} (hs : 1 ≤ s) (hu : ¬ p ∣ u) (hodd : Odd (p ^ s))
    (hkM : 2 * (p ^ v * u) + 1 ≤ p ^ s) {t : ℕ} (ht2 : t ≤ 2) (hts : v + t ≤ s) :
    Ob p t (eps p (p ^ s) (p ^ v * u)) := by
  rw [eps_eq hodd hkM]
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  have hk : 1 ≤ p ^ v * u := Nat.mul_pos (pow_pos hp.out.pos v) (Nat.pos_of_ne_zero hu0)
  have hvs : v < s := by
    by_contra h; push_neg at h
    have : p ^ s ≤ p ^ v * u := by
      calc p ^ s ≤ p ^ v := Nat.pow_le_pow_right hp.out.pos h
        _ ≤ p ^ v * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    omega
  obtain ⟨u', hu', hsub⟩ := sub_pow_eq hu hvs (by omega)
  have hc : ((p ^ s : ℕ) : ℚ_[p]) - ((p ^ v * u : ℕ) : ℚ_[p]) = ((p ^ v * u' : ℕ) : ℚ_[p]) := by
    rw [← hsub, Nat.cast_sub (by omega)]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu'0 : (u' : ℚ_[p]) ≠ 0 := by
    have : u' ≠ 0 := by rintro rfl; exact hu' (dvd_zero p)
    exact_mod_cast this
  push_cast at hc ⊢
  rw [hc]
  -- first term: 2 p^s / (p^v u') = 2 p^(s-v) / u'
  have h1 : Ob p ((s : ℤ) - v) (2 * (p : ℚ_[p]) ^ s / ((p : ℚ_[p]) ^ v * (u' : ℚ_[p]))) := by
    have := Ob_pow_div' (p := p) hu' hvs.le
    push_cast at this
    exact Ob_of_eq (Ob_unit_mul Ob_two this) (by ring)
  -- second term: (p^s + p^v u)/(p^v u') = (p^(s-v) + u)/u' is a unit
  have h2 : Ob p 0 (((p : ℚ_[p]) ^ s + (p : ℚ_[p]) ^ v * (u : ℚ_[p])) / ((p : ℚ_[p]) ^ v * (u' : ℚ_[p]))) := by
    have : ((p : ℚ_[p]) ^ s + (p : ℚ_[p]) ^ v * (u : ℚ_[p])) / ((p : ℚ_[p]) ^ v * (u' : ℚ_[p]))
        = ((p : ℚ_[p]) ^ (s - v) + (u : ℚ_[p])) * (u' : ℚ_[p])⁻¹ := by
      have hsplit : (p : ℚ_[p]) ^ s = (p : ℚ_[p]) ^ v * (p : ℚ_[p]) ^ (s - v) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]; field_simp
    rw [this]
    exact Ob_mul_unit (Ob_add (Ob_p_pow _ |> fun h => Ob_mono h (by omega)) (Ob_natCast u))
      (Ob_inv_nat_of_not_dvd hu')
  have h3 := Ob_mu (p := p) hs (p ^ v * u)
  push_cast at h3
  refine Ob_sub (Ob_mono h1 (by omega)) ?_
  exact Ob_mono (Ob_unit_mul h2 h3) (by omega)

/-- `|D_{p^s}(k)| ≤ p^{-(s-v+t)}` -/
lemma Ob_D {s v u : ℕ} (hs : 1 ≤ s) (hu : ¬ p ∣ u) (hodd : Odd (p ^ s))
    (hkM : p ^ v * u < p ^ s) {t : ℕ} (ht2 : t ≤ 2) (hts : v + t ≤ s) :
    Ob p ((s : ℤ) - v + t) (bb p (p ^ s) (p ^ v * u) + bb p (p ^ s) (p ^ s - p ^ v * u)) := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  have hk : 1 ≤ p ^ v * u := Nat.mul_pos (pow_pos hp.out.pos v) (Nat.pos_of_ne_zero hu0)
  have hvs : v < s := by
    by_contra h; push_neg at h
    have : p ^ s ≤ p ^ v * u := by
      calc p ^ s ≤ p ^ v := Nat.pow_le_pow_right hp.out.pos h
        _ ≤ p ^ v * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    omega
  obtain ⟨t', ht'⟩ := hodd
  by_cases hhalf : 2 * (p ^ v * u) + 1 ≤ p ^ s
  · rw [D_eq ⟨t', ht'⟩ hk hhalf]
    exact Ob_mul (Ob_bb_level hu hvs.le) (Ob_eps hs hu ⟨t', ht'⟩ hhalf ht2 hts)
  · obtain ⟨u', hu', hsub⟩ := sub_pow_eq hu hvs hkM
    have hhalf' : 2 * (p ^ v * u') + 1 ≤ p ^ s := by omega
    have hk' : 1 ≤ p ^ v * u' := by
      have : u' ≠ 0 := by rintro rfl; exact hu' (dvd_zero p)
      exact Nat.mul_pos (pow_pos hp.out.pos v) (Nat.pos_of_ne_zero this)
    have hsub' : p ^ s - p ^ v * u' = p ^ v * u := by omega
    rw [hsub, ← hsub', add_comm (bb p (p ^ s) (p ^ s - p ^ v * u')), D_eq ⟨t', ht'⟩ hk' hhalf']
    exact Ob_mul (Ob_bb_level hu' hvs.le) (Ob_eps hs hu' ⟨t', ht'⟩ hhalf' ht2 hts)

/- ### descent for `Ψ` -/

lemma mul_lt_iff' {k' k₀ j' : ℕ} (hk : k₀ < p) : p * k' + k₀ < p * j' ↔ k' < j' := by
  constructor
  · intro h; by_contra h'; push_neg at h'
    have := Nat.mul_le_mul_left p h'; omega
  · intro h
    have := Nat.mul_le_mul_left p h
    rw [Nat.mul_succ] at this; omega

lemma two_mul_lt_iff' {j' N : ℕ} : 2 * (p * j') < p * N + 1 ↔ 2 * j' < N + 1 := by
  rw [Nat.lt_succ_iff, Nat.lt_succ_iff, show 2 * (p * j') = p * (2 * j') by ring]
  exact Nat.mul_le_mul_left_iff hp.out.pos

lemma filter_dvd_Ico {N k' k₀ : ℕ} (hk : k₀ < p) (hN : Odd N) :
    (Ico (p * k' + k₀ + 1) ((p * N + 1) / 2)).filter (fun j => p ∣ j)
      = (Ico (k' + 1) ((N + 1) / 2)).image (fun j => p * j) := by
  obtain ⟨t, ht⟩ := hN
  have hp1 : 1 ≤ p := hp.out.pos
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨j', rfl⟩⟩
    refine ⟨j', ⟨?_, ?_⟩, rfl⟩
    · have := (mul_lt_iff' (p := p) (k' := k') (j' := j') hk).1 (by omega); omega
    · have h3 : 2 * (p * j') < p * N + 1 := by
        have := Nat.div_mul_le_self (p * N + 1) 2
        have h4 : p * j' + 1 ≤ (p * N + 1) / 2 := h2
        have := Nat.mul_le_mul_left 2 h4
        omega
      have := (two_mul_lt_iff' (p := p)).1 h3
      omega
  · rintro ⟨j', ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right p j'⟩
    · have := (mul_lt_iff' (p := p) (k' := k') (j' := j') hk).2 (by omega : k' < j'); omega
    · have h3 : 2 * j' + 1 ≤ N := by omega
      have := Nat.mul_le_mul_left p h3
      rw [Nat.mul_add, Nat.mul_one, ← mul_assoc, mul_comm p 2, mul_assoc] at this
      omega

/-- descent for `Ψ`: `Ψ_{pN}(pk'+k₀) = Ψ_N(k') Φ_N(pk'+k₀)` -/
lemma Psi_descent {N k' k₀ : ℕ} (hk : k₀ < p) (hN : Odd N) :
    Psi p (p * N) (p * k' + k₀) = Psi p N k' * Phi p N (p * k' + k₀) := by
  unfold Psi Phi
  rw [← Finset.prod_filter_mul_prod_filter_not (Ico (p * k' + k₀ + 1) ((p * N + 1) / 2)) (fun j => p ∣ j)]
  congr 1
  · rw [filter_dvd_Ico hk hN, Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_Ico] at hj
      obtain ⟨t, ht⟩ := hN
      have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      have hj0 : (j : ℚ_[p]) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
      have hNj : ((N : ℚ_[p]) - j) ≠ 0 := by
        have : ((N - j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show N - j ≠ 0 by omega)
        rwa [Nat.cast_sub (by omega)] at this
      push_cast
      field_simp
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos h

/-- `μ_{pN}(k) = μ_N(k') + (1 - μ_N(k')) (1 - Φ_N(k))` for `k = pk'+k₀` -/
lemma mu_descent {N k' k₀ : ℕ} (hk : k₀ < p) (hN : Odd N) :
    mu p (p * N) (p * k' + k₀) = mu p N k' + (1 - mu p N k') * (1 - Phi p N (p * k' + k₀)) := by
  unfold mu; rw [Psi_descent hk hN]; ring

end A357565Proof

-- ===== Dev8 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

lemma odd_pow_of_EData (E : EData p e) (s : ℕ) : Odd (p ^ s) :=
  (hp.out.odd_of_ne_two E.hp2).pow

lemma Ob_rho_sub_one_pow (l : ℕ) (s m : ℕ) : Ob p s (rho p l (p ^ s) m - 1) := by
  apply Ob_rho_sub_one
  have := Ob_unit_mul (Ob_natCast (p := p) l) (Ob_p_pow (p := p) s)
  push_cast at this ⊢
  exact this

/-- **Lemma Z**: `∑_{k<p^s} c(p^s,k)² μ(p^s,k)² Λ^{(m)}(k) = O(p^{s+m+2+e})` -/
theorem lemmaZ (E : EData p e) {s : ℕ} (hs : 1 ≤ s) {m : ℕ} (hm : 1 ≤ m) :
    Ob p ((s : ℤ) + m + 2 + e)
      (∑ k ∈ range (p ^ s), cc p (p ^ s) k ^ 2 * mu p (p ^ s) k ^ 2 * Lam p m k) := by
  induction s generalizing m with
  | zero => omega
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · -- base case s = 1
      subst h0
      apply Ob_sum; intro k _
      have h1 : Ob p 0 (cc p (p ^ (0 + 1)) k ^ 2) := Ob_pow (Ob_cc _ _) 2
      have h2 : Ob p 4 (mu p (p ^ (0 + 1)) k ^ 2) := by
        have := Ob_pow (Ob_mu (p := p) (s := 0 + 1) (le_refl _) k) 2
        exact Ob_cast (by norm_num) this
      have h3 := Ob_Lam E hm k
      have := Ob_mul (Ob_mul h1 h2) h3
      exact Ob_mono this (by push_cast; omega)
    · -- inductive step
      have hN : Odd (p ^ s) := odd_pow_of_EData E s
      have hpow : p ^ (s + 1) = p * p ^ s := by ring
      rw [hpow, sum_range_mul']
      -- main term
      have hmain : Ob p ((s : ℤ) + 1 + m + 2 + e)
          (∑ k' ∈ range (p ^ s), ∑ k₀ ∈ range p, cc p (p ^ s) k' ^ 2 * mu p (p ^ s) k' ^ 2 * Lam p m (p * k' + k₀)) := by
        have : ∑ k' ∈ range (p ^ s), ∑ k₀ ∈ range p, cc p (p ^ s) k' ^ 2 * mu p (p ^ s) k' ^ 2 * Lam p m (p * k' + k₀)
            = ∑ k' ∈ range (p ^ s), cc p (p ^ s) k' ^ 2 * mu p (p ^ s) k' ^ 2 * Lam p (m + 1) k' := by
          apply Finset.sum_congr rfl; intro k' _
          rw [Lam_succ hm, Finset.mul_sum]
        rw [this]
        have := ih h0 (m := m + 1) (by omega)
        exact Ob_cast (by push_cast; ring) this
      -- correction terms
      have hcorr : Ob p ((s : ℤ) + 1 + m + 2 + e)
          (∑ k' ∈ range (p ^ s), ∑ k₀ ∈ range p,
              cc p (p * p ^ s) (p * k' + k₀) ^ 2 * mu p (p * p ^ s) (p * k' + k₀) ^ 2 * Lam p m (p * k' + k₀)
            - ∑ k' ∈ range (p ^ s), ∑ k₀ ∈ range p,
              cc p (p ^ s) k' ^ 2 * mu p (p ^ s) k' ^ 2 * Lam p m (p * k' + k₀)) := by
        apply Ob_sum_sub_sum; intro k' _
        apply Ob_sum_sub_sum; intro k₀ hk₀
        simp only [Finset.mem_range] at hk₀
        have hdiv : (p * k' + k₀) / p = k' := by
          rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hk₀]; simp
        rw [cc_descent, hdiv, mu_descent hk₀ hN]
        set c := cc p (p ^ s) k' with hc
        set ρ := rho p 1 (p * p ^ s) (p * k' + k₀ + 1) with hρ
        set μ := mu p (p ^ s) k' with hμ
        set δ := (1 - μ) * (1 - Phi p (p ^ s) (p * k' + k₀)) with hδ
        set L := Lam p m (p * k' + k₀) with hL
        have key : (c * ρ) ^ 2 * (μ + δ) ^ 2 * L - c ^ 2 * μ ^ 2 * L
            = c ^ 2 * L * ((ρ - 1) * (ρ + 1) * μ ^ 2) + c ^ 2 * L * (ρ ^ 2 * (2 * μ * δ)) + c ^ 2 * L * (ρ ^ 2 * δ ^ 2) := by
          ring
        rw [key]
        have hcO : Ob p 0 c := Ob_cc _ _
        have hLO := Ob_Lam E hm (p * k' + k₀)
        have hρ1 : Ob p (s + 1) (ρ - 1) := by
          rw [hρ, ← hpow]; exact Ob_rho_sub_one_pow 1 (s + 1) _
        have hρO : Ob p 0 ρ := by rw [hρ]; exact Ob_rho
        have hρ1' : Ob p 0 (ρ + 1) := Ob_add hρO Ob_one
        have hμO : Ob p 2 μ := by rw [hμ]; exact Ob_mu h0 k'
        have hδO : Ob p (2 * (s : ℤ) + 2) δ := by
          rw [hδ]
          exact Ob_unit_mul (Ob_sub Ob_one (Ob_mono hμO (by norm_num))) (Ob_one_sub_Phi s _)
        have hcL : Ob p ((m : ℤ) + e - 1) (c ^ 2 * L) := Ob_unit_mul (Ob_pow hcO 2) hLO
        have t1 : Ob p ((s : ℤ) + 1 + m + 2 + e) (c ^ 2 * L * ((ρ - 1) * (ρ + 1) * μ ^ 2)) := by
          have := Ob_mul hcL (Ob_mul (Ob_mul_unit hρ1 hρ1') (Ob_pow hμO 2))
          exact Ob_mono this (by have := E.he; push_cast; omega)
        have t2 : Ob p ((s : ℤ) + 1 + m + 2 + e) (c ^ 2 * L * (ρ ^ 2 * (2 * μ * δ))) := by
          have := Ob_mul hcL (Ob_unit_mul (Ob_pow hρO 2) (Ob_mul (Ob_unit_mul Ob_two hμO) hδO))
          exact Ob_mono this (by have := E.he; push_cast; omega)
        have t3 : Ob p ((s : ℤ) + 1 + m + 2 + e) (c ^ 2 * L * (ρ ^ 2 * δ ^ 2)) := by
          have := Ob_mul hcL (Ob_unit_mul (Ob_pow hρO 2) (Ob_pow hδO 2))
          exact Ob_mono this (by have := E.he; push_cast; omega)
        exact Ob_add (Ob_add t1 t2) t3
      have := Ob_add hcorr hmain
      exact Ob_of_eq (Ob_cast (by push_cast; ring) this) (by ring)

end A357565Proof

-- ===== Dev9 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

/-- `f(x) = 3x² + 2x³` -/
noncomputable def ff (x : ℚ_[p]) : ℚ_[p] := 3 * x ^ 2 + 2 * x ^ 3
/-- `g(x,y)`, with `g(x,y) + g(y,x) = f(x) + f(y) + 6xy` -/
noncomputable def gg (x y : ℚ_[p]) : ℚ_[p] :=
  3 * x ^ 2 * (x + y) + 3 / 2 * (x + y) ^ 2 - 3 * x * (x + y) ^ 2 + (x + y) ^ 3
noncomputable def aa (p : ℕ) [Fact p.Prime] (M : ℕ) : ℚ_[p] := ∑ k ∈ range (M + 1), ff (bb p M k)
noncomputable def Gk (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] := gg (bb p M k) (bb p M (M - k))
noncomputable def Bnd (p : ℕ) [Fact p.Prime] (M : ℕ) : ℚ_[p] :=
  5 + ff (cc p M M / 2) + 3 * cc p M M - 2 * cc p (2 * M) M
noncomputable def Uterm (p : ℕ) [Fact p.Prime] (M k : ℕ) : ℚ_[p] :=
  (bb p M k) ^ 2 * eps p M k *
    (3 * eps p M k + 6 * bb p M k - 6 * bb p M k * eps p M k + 2 * bb p M k * eps p M k ^ 2)

lemma vandermonde_padic (d : ℕ) :
    ∑ k ∈ range (d + 2), (((d + k).choose d : ℕ) : ℚ_[p]) * (((d + (d + 1 - k)).choose d : ℕ) : ℚ_[p])
      = (((3 * d + 2).choose (2 * d + 1) : ℕ) : ℚ_[p]) := by
  have h1 : (mk fun n => ((Nat.choose (d + n) d : ℕ) : ℚ_[p]) : ℚ_[p]⟦X⟧) * (mk fun n => ((Nat.choose (d + n) d : ℕ) : ℚ_[p]))
      = mk fun n => ((Nat.choose (2 * d + 1 + n) (2 * d + 1) : ℕ) : ℚ_[p]) := by
    rw [← mk_one_pow_eq_mk_choose_add, ← mk_one_pow_eq_mk_choose_add, ← pow_add]; congr 1; ring
  have h := congrArg (fun f => PowerSeries.coeff (R := ℚ_[p]) (d + 1) f) h1
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (((d + i).choose d : ℕ) : ℚ_[p]) * (((d + j).choose d : ℕ) : ℚ_[p]))] at h
  rw [h]
  congr 2; ring

lemma bb_self {M : ℕ} (hM : 1 ≤ M) : bb p M M = cc p M M / 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, M = d + 1 := ⟨M - 1, by omega⟩
  unfold bb cc
  have h := Nat.choose_mul_succ_eq (2 * d + 1) (d + 1)
  rw [show 2 * d + 1 + 1 - (d + 1) = d + 1 by omega] at h
  have h2 : 2 * ((2 * d + 1).choose (d + 1)) = (2 * d + 1 + 1).choose (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < d + 1 by omega)
    rw [← h]; ring
  rw [show d + 1 + (d + 1) - 1 = 2 * d + 1 by omega, show d + 1 + (d + 1) = 2 * d + 1 + 1 by omega]
  rw [← h2]; push_cast; ring

lemma VV_eq {M : ℕ} (hM : 1 ≤ M) :
    3 * ∑ k ∈ range (M + 1), bb p M k * bb p M (M - k) = 2 * cc p (2 * M) M := by
  obtain ⟨d, rfl⟩ : ∃ d, M = d + 1 := ⟨M - 1, by omega⟩
  have hv := vandermonde_padic (p := p) d
  have : ∑ k ∈ range (d + 1 + 1), bb p (d + 1) k * bb p (d + 1) (d + 1 - k)
      = ∑ k ∈ range (d + 2), (((d + k).choose d : ℕ) : ℚ_[p]) * (((d + (d + 1 - k)).choose d : ℕ) : ℚ_[p]) := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold bb
    rw [show d + 1 + k - 1 = d + k by omega, show d + 1 + (d + 1 - k) - 1 = d + (d + 1 - k) by omega,
      Nat.choose_symm_add, Nat.choose_symm_add]
  rw [this, hv]
  unfold cc
  have h := Nat.choose_mul_succ_eq (3 * d + 2) (d + 1)
  rw [show 3 * d + 2 + 1 - (d + 1) = 2 * d + 2 by omega] at h
  have hsym : (3 * d + 2).choose (2 * d + 1) = (3 * d + 2).choose (d + 1) := by
    rw [← Nat.choose_symm (show d + 1 ≤ 3 * d + 2 by omega)]; congr 1; omega
  have h3 : 3 * (3 * d + 2).choose (d + 1) = 2 * (3 * d + 2 + 1).choose (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < d + 1 by omega)
    calc 3 * (3 * d + 2).choose (d + 1) * (d + 1) = (3 * d + 2).choose (d + 1) * (3 * d + 2 + 1) := by ring
      _ = (3 * d + 2 + 1).choose (d + 1) * (2 * d + 2) := h
      _ = _ := by ring
  rw [hsym, show 2 * (d + 1) + (d + 1) = 3 * d + 2 + 1 by ring]
  exact_mod_cast h3

/-- **A1**: `a(M) = Bnd(M) + ∑_{1≤k<M} G_M(k)` -/
lemma aa_eq {M : ℕ} (hM : 1 ≤ M) : aa p M = Bnd p M + ∑ k ∈ Ico 1 M, Gk p M k := by
  have hrefl : ∑ k ∈ range (M + 1), ff (bb p M (M - k)) = aa p M := by
    unfold aa
    have := Finset.sum_range_reflect (fun k => ff (bb p M k)) (M + 1)
    simp only [Nat.add_sub_cancel] at this
    exact this
  have h2 : 2 * aa p M = ∑ k ∈ range (M + 1), (ff (bb p M k) + ff (bb p M (M - k))) := by
    rw [Finset.sum_add_distrib, hrefl]; unfold aa; ring
  have h3 : ∑ k ∈ range (M + 1), (ff (bb p M k) + ff (bb p M (M - k)))
      = 2 * ∑ k ∈ range (M + 1), Gk p M k - 6 * ∑ k ∈ range (M + 1), bb p M k * bb p M (M - k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; unfold Gk gg ff; ring
  have hV := VV_eq (p := p) hM
  have h4 : ∑ k ∈ range (M + 1), Gk p M k = Gk p M 0 + ∑ k ∈ Ico 1 M, Gk p M k + Gk p M M := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM]
  have h5 : Gk p M 0 + Gk p M M = 5 + ff (bb p M M) + 6 * bb p M M := by
    unfold Gk; rw [Nat.sub_zero, Nat.sub_self, bb_zero]; unfold gg ff; ring
  have h6 : aa p M = ∑ k ∈ range (M + 1), Gk p M k - 3 * ∑ k ∈ range (M + 1), bb p M k * bb p M (M - k) := by
    have := h2.trans h3; linear_combination this / 2
  rw [h6, h4]
  have h7 : 3 * ∑ k ∈ range (M + 1), bb p M k * bb p M (M - k) = 2 * cc p (2 * M) M := hV
  unfold Bnd
  rw [bb_self hM] at h5
  linear_combination h5 - h7

lemma Ico_filter_not_dvd (N : ℕ) : (Ico 1 (p * N)).filter (fun k => ¬ p ∣ k) = U p (p * N) := by
  ext k; simp only [Finset.mem_filter, Finset.mem_Ico, mem_U]
  constructor
  · rintro ⟨⟨_, h⟩, hd⟩; exact ⟨h, hd⟩
  · rintro ⟨h, hd⟩; refine ⟨⟨?_, h⟩, hd⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; exact absurd (dvd_zero p) hd
    · exact h0

lemma Ico_filter_dvd (N : ℕ) :
    (Ico 1 (p * N)).filter (fun k => p ∣ k) = (Ico 1 N).image (fun k' => p * k') := by
  ext k; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨k', rfl⟩⟩
    refine ⟨k', ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k' with h0 | h0
      · subst h0; simp at h1
      · exact h0
    · exact Nat.lt_of_mul_lt_mul_left h2
  · rintro ⟨k', ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right p k'⟩
    · exact Nat.mul_pos hp.out.pos h1
    · exact Nat.mul_lt_mul_of_pos_left h2 hp.out.pos

lemma sum_Ico_split (N : ℕ) (F : ℕ → ℚ_[p]) :
    ∑ k ∈ Ico 1 (p * N), F k = ∑ k ∈ U p (p * N), F k + ∑ k' ∈ Ico 1 N, F (p * k') := by
  rw [← Finset.sum_filter_add_sum_filter_not (Ico 1 (p * N)) (fun k => p ∣ k), Ico_filter_not_dvd,
    Ico_filter_dvd, Finset.sum_image]
  · ring
  · intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp.out.pos h

lemma sum_U_Gk {M : ℕ} (hM : p ∣ M) (hodd : Odd M) :
    ∑ k ∈ U p M, Gk p M k = ∑ k ∈ U p ((M + 1) / 2), Uterm p M k := by
  rw [sum_U_half hM hodd]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_U] at hk
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => hk.2 (h ▸ dvd_zero p))
  have hkM : 2 * k + 1 ≤ M := by obtain ⟨t, ht⟩ := hodd; omega
  unfold Gk Uterm
  rw [show M - (M - k) = k by omega, bb_reflect hodd hk1 hkM]
  unfold gg eps; ring

/-- main decomposition -/
lemma aa_diff {N : ℕ} (hN : 1 ≤ N) (hodd : Odd (p * N)) :
    aa p (p * N) - aa p N = (Bnd p (p * N) - Bnd p N) + ∑ k ∈ U p ((p * N + 1) / 2), Uterm p (p * N) k
      + ∑ k' ∈ Ico 1 N, (Gk p (p * N) (p * k') - Gk p N k') := by
  rw [aa_eq (Nat.mul_pos hp.out.pos hN), aa_eq hN, sum_Ico_split, sum_U_Gk (dvd_mul_right p N) hodd,
    Finset.sum_sub_distrib]
  ring

lemma Gk_descent {N k' : ℕ} (hk : 1 ≤ k') (hkN : k' < N) :
    Gk p (p * N) (p * k') = gg (bb p N k' * rho p 1 (p * N) (p * k'))
      (bb p N (N - k') * rho p 1 (p * N) (p * (N - k'))) := by
  unfold Gk
  rw [show p * N - p * k' = p * (N - k') by rw [Nat.mul_sub]]
  rw [bb_descent_mul N hk, bb_descent_mul N (by omega)]

end A357565Proof

-- ===== Dev10 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

/-- second-order expansion of `ρ_{l,M}(m)` -/
lemma rho_second_order (l : ℕ) {M m : ℕ} {j : ℕ} (hM : Ob p j (M : ℚ_[p])) :
    Ob p (3 * j) (2 * (rho p l M m - 1 - (l : ℚ_[p]) * (M : ℚ_[p]) * Hs p 1 m)
      - (((l : ℚ_[p]) * (M : ℚ_[p]) * Hs p 1 m) ^ 2 - ((l : ℚ_[p]) * (M : ℚ_[p])) ^ 2 * Hs p 2 m)) := by
  have h := Ob_prod_second_order (p := p) (U p m) (j := j) (x := fun i => (l : ℚ_[p]) * (M : ℚ_[p]) / (i : ℚ_[p])) (by
    intro i hi
    exact Ob_of_eq (Ob_mul_unit (Ob_unit_mul (Ob_natCast l) hM) (Ob_inv_of_norm_one (norm_U hi)))
      (by ring))
  have e1 : ∑ i ∈ U p m, (l : ℚ_[p]) * (M : ℚ_[p]) / (i : ℚ_[p]) = (l : ℚ_[p]) * (M : ℚ_[p]) * Hs p 1 m := by
    unfold Hs; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [pow_one, div_eq_mul_inv]
  have e2 : ∑ i ∈ U p m, ((l : ℚ_[p]) * (M : ℚ_[p]) / (i : ℚ_[p])) ^ 2 = ((l : ℚ_[p]) * (M : ℚ_[p])) ^ 2 * Hs p 2 m := by
    unfold Hs; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [div_pow, div_eq_mul_inv]
  unfold rho
  rw [e1, e2] at h
  exact h

/-- `ρ_{1,p^{s+1}}(p^{v+1} u) - 1 = O(p^{s+2+e+2v})` for `v ≤ s` -/
lemma Ob_rho_top (E : EData p e) {s v : ℕ} (hvs : v ≤ s) (u : ℕ) :
    Ob p ((s : ℤ) + 2 + e + 2 * v) (rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u) - 1) := by
  have hM : Ob p (s + 1) ((p ^ (s + 1) : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow _
  have h := rho_second_order (p := p) 1 (m := p ^ (v + 1) * u) hM
  have hH1 := Ob_Hs1_pow_mul_bound E (m := v + 1) (by omega) u
  have hH2 := Ob_Hs2_pow_mul_bound E (m := v + 1) (by omega) u
  have he := E.he
  set n : ℚ_[p] := ((p ^ (s + 1) : ℕ) : ℚ_[p]) with hn
  set H1 := Hs p 1 (p ^ (v + 1) * u)
  set H2 := Hs p 2 (p ^ (v + 1) * u)
  set ρ := rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u)
  have hnH1 : Ob p ((s : ℤ) + 2 + e + 2 * v) (n * H1) := by
    have := Ob_mul hM hH1; refine Ob_mono this ?_; push_cast; omega
  have hn2H2 : Ob p ((s : ℤ) + 2 + e + 2 * v) (n ^ 2 * H2) := by
    have := Ob_mul (Ob_pow hM 2) hH2; refine Ob_mono this ?_; push_cast; omega
  have hsq : Ob p ((s : ℤ) + 2 + e + 2 * v) ((n * H1) ^ 2) := by
    have := Ob_pow hnH1 2; refine Ob_mono this ?_; omega
  have h' : Ob p ((s : ℤ) + 2 + e + 2 * v)
      (2 * (ρ - 1 - ((1 : ℕ) : ℚ_[p]) * n * H1) - ((((1 : ℕ) : ℚ_[p]) * n * H1) ^ 2 - (((1 : ℕ) : ℚ_[p]) * n) ^ 2 * H2)) :=
    Ob_mono h (by push_cast; omega)
  have h2 : Ob p ((s : ℤ) + 2 + e + 2 * v) (2 * (ρ - 1)) := by
    have := Ob_add (Ob_add h' (Ob_unit_mul Ob_two hnH1)) (Ob_sub hsq hn2H2)
    exact Ob_of_eq this (by push_cast; ring)
  have := Ob_unit_mul (Ob_inv_two E.hp2) h2
  exact Ob_of_eq this (by field_simp)

/-- `ρ₁ - ρ₂ = O(p^{2s+2+v+e})` where `m = p^{v+1} u`, `p^{s+1} - m = p^{v+1} u'` -/
lemma Ob_rho_diff_gen (E : EData p e) {s v u u' : ℕ} (hvs : v ≤ s)
    (hm : p ^ (v + 1) * u ≤ p ^ (s + 1)) (hu' : p ^ (s + 1) - p ^ (v + 1) * u = p ^ (v + 1) * u') :
    Ob p (2 * (s : ℤ) + 2 + v + e)
      (rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u) - rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u')) := by
  have he := E.he
  have hM : Ob p (s + 1) ((p ^ (s + 1) : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow _
  have hpm : p ∣ p ^ (v + 1) * u := Dvd.dvd.mul_right (dvd_pow_self p (by omega)) u
  have h1 := rho_second_order (p := p) 1 (m := p ^ (v + 1) * u) hM
  have h2 := rho_second_order (p := p) 1 (m := p ^ (v + 1) * u') hM
  have hR := Ob_Hs1_reflect_diff E hpm hm
  rw [hu'] at hR
  have hH1 := Ob_Hs1_pow_mul_bound E (m := v + 1) (by omega) u
  have hH1' := Ob_Hs1_pow_mul_bound E (m := v + 1) (by omega) u'
  have hH2 := Ob_Hs2_pow_mul_bound E (m := v + 1) (by omega) u
  have hH2' := Ob_Hs2_pow_mul_bound E (m := v + 1) (by omega) u'
  push_cast at h1 h2 hR hM ⊢
  set n : ℚ_[p] := (p : ℚ_[p]) ^ (s + 1) with hn
  set A := Hs p 1 (p ^ (v + 1) * u)
  set A' := Hs p 1 (p ^ (v + 1) * u')
  set B := Hs p 2 (p ^ (v + 1) * u)
  set B' := Hs p 2 (p ^ (v + 1) * u')
  set ρ := rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u)
  set ρ' := rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u')
  have t1 : Ob p (2 * (s : ℤ) + 2 + v + e) (2 * (ρ - 1 - n * A) - ((n * A) ^ 2 - n ^ 2 * B)) :=
    Ob_mono (Ob_of_eq h1 (by ring)) (by push_cast; omega)
  have t2 : Ob p (2 * (s : ℤ) + 2 + v + e) (2 * (ρ' - 1 - n * A') - ((n * A') ^ 2 - n ^ 2 * B')) :=
    Ob_mono (Ob_of_eq h2 (by ring)) (by push_cast; omega)
  have t3 : Ob p (2 * (s : ℤ) + 2 + v + e) (2 * n * (A - A' + n * B)) := by
    have := Ob_mul (Ob_unit_mul Ob_two hM) hR
    refine Ob_mono this ?_; push_cast; omega
  have t4 : Ob p (2 * (s : ℤ) + 2 + v + e) (n ^ 2 * B) := by
    have := Ob_mul (Ob_pow hM 2) hH2; refine Ob_mono this ?_; push_cast; omega
  have t5 : Ob p (2 * (s : ℤ) + 2 + v + e) (n ^ 2 * B') := by
    have := Ob_mul (Ob_pow hM 2) hH2'; refine Ob_mono this ?_; push_cast; omega
  have t6 : Ob p (2 * (s : ℤ) + 2 + v + e) ((n * A) ^ 2) := by
    have := Ob_pow (Ob_mul hM hH1) 2; refine Ob_mono this ?_; push_cast; omega
  have t7 : Ob p (2 * (s : ℤ) + 2 + v + e) ((n * A') ^ 2) := by
    have := Ob_pow (Ob_mul hM hH1') 2; refine Ob_mono this ?_; push_cast; omega
  have key : Ob p (2 * (s : ℤ) + 2 + v + e) (2 * (ρ - ρ')) := by
    have := Ob_add (Ob_sub (Ob_add (Ob_sub t1 t2) t3) (Ob_sub (Ob_unit_mul Ob_three t4) t5))
      (Ob_sub t6 t7)
    exact Ob_of_eq this (by ring)
  have := Ob_unit_mul (Ob_inv_two E.hp2) key
  exact Ob_of_eq this (by field_simp)

/-- **DL2**: `ρ_{1,p^{s+1}}(p^s u) - 1 ≡ -(u²/2) p^{3s} h  mod p^{3s+1+e}` -/
lemma Ob_rho_deep (E : EData p e) {s : ℕ} (hs : 1 ≤ s) (u : ℕ) :
    Ob p (3 * (s : ℤ) + 1 + e) (rho p 1 (p ^ (s + 1)) (p ^ s * u) - 1
      + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * Hs p 2 p) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have he := E.he
  have hM : Ob p (s' + 1 + 1) ((p ^ (s' + 1 + 1) : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow _
  have h1 := rho_second_order (p := p) 1 (m := p ^ (s' + 1) * u) hM
  have hD := Ob_Hs1_deep E hs u
  rw [show 2 * (s' + 1) - 1 = 2 * s' + 1 by omega] at hD
  have hH1 := Ob_Hs1_pow_mul_bound E (m := s' + 1) (by omega) u
  have hH2 := Ob_Hs2_pow_mul_bound E (m := s' + 1) (by omega) u
  push_cast at h1 hD hM ⊢
  set n : ℚ_[p] := (p : ℚ_[p]) ^ (s' + 1 + 1) with hn
  set A := Hs p 1 (p ^ (s' + 1) * u)
  set B := Hs p 2 (p ^ (s' + 1) * u)
  set h := Hs p 2 p
  set ρ := rho p 1 (p ^ (s' + 1 + 1)) (p ^ (s' + 1) * u)
  have t1 : Ob p (3 * ((s' : ℤ) + 1) + 1 + e) (2 * (ρ - 1 - n * A) - ((n * A) ^ 2 - n ^ 2 * B)) :=
    Ob_mono (Ob_of_eq h1 (by ring)) (by push_cast; omega)
  have t3 : Ob p (3 * ((s' : ℤ) + 1) + 1 + e) (2 * n * (A + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (2 * s' + 1) * h)) := by
    have := Ob_mul (Ob_unit_mul Ob_two hM) hD
    refine Ob_mono this ?_; push_cast; omega
  have t4 : Ob p (3 * ((s' : ℤ) + 1) + 1 + e) (n ^ 2 * B) := by
    have := Ob_mul (Ob_pow hM 2) hH2; refine Ob_mono this ?_; push_cast; omega
  have t6 : Ob p (3 * ((s' : ℤ) + 1) + 1 + e) ((n * A) ^ 2) := by
    have := Ob_pow (Ob_mul hM hH1) 2; refine Ob_mono this ?_; push_cast; omega
  have key : Ob p (3 * ((s' : ℤ) + 1) + 1 + e)
      (2 * (ρ - 1 + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * (s' + 1)) * h)) := by
    have := Ob_sub (Ob_add t1 t3) (Ob_sub t4 t6)
    exact Ob_of_eq this (by rw [hn]; ring)
  have := Ob_unit_mul (Ob_inv_two E.hp2) key
  exact Ob_of_eq this (by field_simp)

/-- **DL3**: `ρ₁ - ρ₂ ≡ -2 u h p^{3s+1}  mod p^{3s+2+e}` at the deep level -/
lemma Ob_rho_deep_diff (E : EData p e) {s : ℕ} (hs : 1 ≤ s) {u : ℕ} (hu : u ≤ p) :
    Ob p (3 * (s : ℤ) + 2 + e) (rho p 1 (p ^ (s + 1)) (p ^ s * u) - rho p 1 (p ^ (s + 1)) (p ^ s * (p - u))
      + 2 * (u : ℚ_[p]) * Hs p 2 p * (p : ℚ_[p]) ^ (3 * s + 1)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have he := E.he
  have hM : Ob p (s' + 1 + 1) ((p ^ (s' + 1 + 1) : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow _
  have hN : Ob p (s' + 1) ((p ^ (s' + 1) : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow _
  have hps : p ∣ p ^ (s' + 1) := dvd_pow_self p (by omega)
  have h1 := rho_second_order (p := p) 1 (m := p ^ (s' + 1) * u) hM
  have h2 := rho_second_order (p := p) 1 (m := p ^ (s' + 1) * (p - u)) hM
  have hD := Ob_Hs1_deep_diff E hs hu
  have hH1 := Ob_Hs1_pow_mul_bound E (m := s' + 1) (by omega) u
  have hH1' := Ob_Hs1_pow_mul_bound E (m := s' + 1) (by omega) (p - u)
  have hm1 := Ob_Hs2_mul E.hp2 hps hN u
  have hm2 := Ob_Hs2_mul E.hp2 hps hN (p - u)
  have hpw := Ob_Hs2_pow E (m := s' + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpw
  push_cast [Nat.cast_sub hu] at h1 h2 hD hM hN hm1 hm2 hpw ⊢
  set n : ℚ_[p] := (p : ℚ_[p]) ^ (s' + 1 + 1) with hn
  set A := Hs p 1 (p ^ (s' + 1) * u)
  set A' := Hs p 1 (p ^ (s' + 1) * (p - u))
  set B := Hs p 2 (p ^ (s' + 1) * u)
  set B' := Hs p 2 (p ^ (s' + 1) * (p - u))
  set C := Hs p 2 (p ^ (s' + 1))
  set h := Hs p 2 p
  set ρ := rho p 1 (p ^ (s' + 1 + 1)) (p ^ (s' + 1) * u)
  set ρ' := rho p 1 (p ^ (s' + 1 + 1)) (p ^ (s' + 1) * (p - u))
  have t1 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (2 * (ρ - 1 - n * A) - ((n * A) ^ 2 - n ^ 2 * B)) :=
    Ob_mono (Ob_of_eq h1 (by ring)) (by push_cast; omega)
  have t2 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (2 * (ρ' - 1 - n * A') - ((n * A') ^ 2 - n ^ 2 * B')) :=
    Ob_mono (Ob_of_eq h2 (by ring)) (by push_cast; omega)
  have t3 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (2 * n * (A - A' + (u : ℚ_[p]) * (p : ℚ_[p]) ^ (2 * (s' + 1)) * h)) := by
    have := Ob_mul (Ob_unit_mul Ob_two hM) hD
    refine Ob_mono this ?_; push_cast; omega
  have t4 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (n ^ 2 * (B - (u : ℚ_[p]) * C)) := by
    have := Ob_mul (Ob_pow hM 2) hm1; refine Ob_mono this ?_; push_cast; omega
  have t5 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (n ^ 2 * (B' - ((p : ℚ_[p]) - (u : ℚ_[p])) * C)) := by
    have := Ob_mul (Ob_pow hM 2) hm2; refine Ob_mono this ?_; push_cast; omega
  have t6 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) ((n * A) ^ 2) := by
    have := Ob_pow (Ob_mul hM hH1) 2; refine Ob_mono this ?_; push_cast; omega
  have t7 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) ((n * A') ^ 2) := by
    have := Ob_pow (Ob_mul hM hH1') 2; refine Ob_mono this ?_; push_cast; omega
  have t8 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (n ^ 2 * (2 * (u : ℚ_[p]) - (p : ℚ_[p])) * (C - (p : ℚ_[p]) ^ s' * h)) := by
    have hu0 : Ob p 0 (2 * (u : ℚ_[p]) - (p : ℚ_[p])) := Ob_sub (Ob_unit_mul Ob_two (Ob_natCast u)) (Ob_natCast p)
    have := Ob_mul (Ob_mul_unit (Ob_pow hM 2) hu0) hpw; refine Ob_mono this ?_; push_cast; omega
  have t9 : Ob p (3 * ((s' : ℤ) + 1) + 2 + e) (n ^ 2 * (p : ℚ_[p]) ^ (s' + 1) * h) := by
    have := Ob_mul (Ob_mul (Ob_pow hM 2) hN) E.hh; refine Ob_mono this ?_; push_cast; omega
  have key : Ob p (3 * ((s' : ℤ) + 1) + 2 + e)
      (2 * (ρ - ρ' + 2 * (u : ℚ_[p]) * h * (p : ℚ_[p]) ^ (3 * (s' + 1) + 1))) := by
    have := Ob_add (Ob_sub (Ob_add (Ob_sub t1 t2) t3) (Ob_add (Ob_sub t4 t5) (Ob_sub t8 t9)))
      (Ob_sub t6 t7)
    exact Ob_of_eq this (by rw [hn]; ring)
  have := Ob_unit_mul (Ob_inv_two E.hp2) key
  exact Ob_of_eq this (by field_simp)

end A357565Proof

-- ===== Dev11 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

/-- termwise estimate for the middle levels `k' = p^v u`, `v + 2 ≤ s` -/
lemma Ob_gg_termwise (E : EData p e) {s v : ℕ} (hv : v + 2 ≤ s) {x y ρ₁ ρ₂ : ℚ_[p]}
    (hx : Ob p ((s : ℤ) - v) x) (hy : Ob p ((s : ℤ) - v) y) (hD : Ob p ((s : ℤ) - v + 2) (x + y))
    (ha : Ob p ((s : ℤ) + 2 + e + 2 * v) (ρ₁ - 1)) (hb : Ob p ((s : ℤ) + 2 + e + 2 * v) (ρ₂ - 1))
    (hab : Ob p (2 * (s : ℤ) + 2 + v + e) (ρ₁ - ρ₂)) :
    Ob p (3 * (s : ℤ) + 6) (gg (x * ρ₁) (y * ρ₂) - gg x y) := by
  have he := E.he
  obtain ⟨a, rfl⟩ : ∃ a, ρ₁ = a + 1 := ⟨ρ₁ - 1, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, ρ₂ = b + 1 := ⟨ρ₂ - 1, by ring⟩
  simp only [add_sub_cancel_right] at ha hb
  have hab' : Ob p (2 * (s : ℤ) + 2 + v + e) (a - b) := Ob_of_eq hab (by ring)
  set D := x + y with hDdef
  set W := x * (a - b) + D * b with hW
  have hWO : Ob p (2 * (s : ℤ) + 4 + e + v) W := by
    refine Ob_add ?_ ?_
    · refine Ob_mono (Ob_mul hx hab') ?_; omega
    · refine Ob_mono (Ob_mul hD hb) ?_; omega
  have hDW : Ob p ((s : ℤ) - v + 2) (D + W) := Ob_add hD (Ob_mono hWO (by omega))
  have h2DW : Ob p ((s : ℤ) - v + 2) (2 * D + W) := Ob_add (Ob_unit_mul Ob_two hD) (Ob_mono hWO (by omega))
  have h32 : Ob p 0 ((3 : ℚ_[p]) / 2) := by
    rw [div_eq_mul_inv]; exact Ob_mul_unit Ob_three (Ob_inv_two E.hp2)
  have ha2 : Ob p ((s : ℤ) + 2 + e + 2 * v) (2 * a + a ^ 2) :=
    Ob_add (Ob_unit_mul Ob_two ha) (Ob_mono (Ob_pow ha 2) (by omega))
  have key : gg (x * (a + 1)) (y * (b + 1)) - gg x y
      = 3 * (x ^ 2 * (2 * a + a ^ 2) * (D + W) + x ^ 2 * W) + 3 / 2 * (W * (2 * D + W))
        - 3 * (x * a * (D + W) ^ 2 + x * W * (2 * D + W)) + W * (3 * D ^ 2 + 3 * D * W + W ^ 2) := by
    rw [hW, hDdef]; unfold gg; ring
  rw [key]
  have t1 : Ob p (3 * (s : ℤ) + 6) (x ^ 2 * (2 * a + a ^ 2) * (D + W) + x ^ 2 * W) := by
    refine Ob_add ?_ ?_
    · refine Ob_mono (Ob_mul (Ob_mul (Ob_pow hx 2) ha2) hDW) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_pow hx 2) hWO) ?_; omega
  have t2 : Ob p (3 * (s : ℤ) + 6) (W * (2 * D + W)) := by
    refine Ob_mono (Ob_mul hWO h2DW) ?_; omega
  have t3 : Ob p (3 * (s : ℤ) + 6) (x * a * (D + W) ^ 2 + x * W * (2 * D + W)) := by
    refine Ob_add ?_ ?_
    · refine Ob_mono (Ob_mul (Ob_mul hx ha) (Ob_pow hDW 2)) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_mul hx hWO) h2DW) ?_; omega
  have t4 : Ob p (3 * (s : ℤ) + 6) (W * (3 * D ^ 2 + 3 * D * W + W ^ 2)) := by
    have hq : Ob p (2 * ((s : ℤ) - v + 2)) (3 * D ^ 2 + 3 * D * W + W ^ 2) := by
      refine Ob_add (Ob_add (Ob_unit_mul Ob_three (Ob_pow hD 2)) ?_) ?_
      · refine Ob_mono (Ob_mul (Ob_unit_mul Ob_three hD) hWO) ?_; omega
      · refine Ob_mono (Ob_pow hWO 2) ?_; omega
    refine Ob_mono (Ob_mul hWO hq) ?_; omega
  exact Ob_add (Ob_sub (Ob_add (Ob_unit_mul Ob_three t1) (Ob_unit_mul h32 t2)) (Ob_unit_mul Ob_three t3)) t4

/-- the deep-level inner estimate (pure `Ob`-algebra) -/
lemma Ob_deep_inner (E : EData p e) {s : ℕ} (hs : 1 ≤ s) {u : ℕ} {x y xu Du ρ₁ ρ₂ h : ℚ_[p]}
    (hx : Ob p 1 x) (hD : Ob p 2 (x + y)) (hxu : Ob p 3 (x - xu)) (hDu : Ob p 3 (x + y - Du))
    (hh : Ob p e h)
    (ha : Ob p (3 * (s : ℤ) + 1 + e) (ρ₁ - 1 + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h))
    (hb : Ob p (3 * (s : ℤ) + 1 + e) (ρ₂ - 1 + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h))
    (hc : Ob p (3 * (s : ℤ) + 2 + e) (ρ₁ - ρ₂ + 2 * (u : ℚ_[p]) * h * (p : ℚ_[p]) ^ (3 * s + 1))) :
    Ob p (3 * (s : ℤ) + 5 + e)
      ((x * ρ₁) ^ 2 * (x * ρ₁ + y * ρ₂) - x ^ 2 * (x + y)
        + 1 / 2 * ((x * ρ₁ + y * ρ₂) ^ 2 - (x + y) ^ 2)
        - (x * ρ₁ * (x * ρ₁ + y * ρ₂) ^ 2 - x * (x + y) ^ 2)
        + 1 / 2 * h * (p : ℚ_[p]) ^ (3 * s)
          * (3 * (u : ℚ_[p]) ^ 2 * xu ^ 2 * Du + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu * Du + (u : ℚ_[p]) ^ 2 * Du ^ 2)) := by
  have he := E.he
  obtain ⟨a, rfl⟩ : ∃ a, ρ₁ = a + 1 := ⟨ρ₁ - 1, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, ρ₂ = b + 1 := ⟨ρ₂ - 1, by ring⟩
  simp only [add_sub_cancel_right] at ha hb
  have hc' : Ob p (3 * (s : ℤ) + 2 + e) (a - b + 2 * (u : ℚ_[p]) * h * (p : ℚ_[p]) ^ (3 * s + 1)) :=
    Ob_of_eq hc (by ring)
  set D := x + y with hDdef
  set A := a + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h with hA
  set B := b + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h with hB
  set C := a - b + 2 * (u : ℚ_[p]) * h * (p : ℚ_[p]) ^ (3 * s + 1) with hC
  set W := x * (a - b) + D * b with hW
  have hu2 : Ob p 0 ((u : ℚ_[p]) ^ 2 / 2) := by
    rw [div_eq_mul_inv]; exact Ob_mul_unit (Ob_pow (Ob_natCast u) 2) (Ob_inv_two E.hp2)
  have hlead : Ob p (3 * (s : ℤ) + e) ((u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h) := by
    have := Ob_mul (Ob_unit_mul hu2 (Ob_p_pow (3 * s))) hh
    refine Ob_mono this ?_; push_cast; omega
  have haO : Ob p (3 * (s : ℤ) + e) a := by
    have := Ob_sub (Ob_mono ha (by omega)) hlead; exact Ob_of_eq this (by rw [hA]; ring)
  have hbO : Ob p (3 * (s : ℤ) + e) b := by
    have := Ob_sub (Ob_mono hb (by omega)) hlead; exact Ob_of_eq this (by rw [hB]; ring)
  have hcO : Ob p (3 * (s : ℤ) + 1 + e) (a - b) := by
    have h2 : Ob p (3 * (s : ℤ) + 1 + e) (2 * (u : ℚ_[p]) * h * (p : ℚ_[p]) ^ (3 * s + 1)) := by
      have := Ob_mul (Ob_mul (Ob_unit_mul Ob_two (Ob_natCast u)) hh) (Ob_p_pow (3 * s + 1))
      refine Ob_mono this ?_; push_cast; omega
    have := Ob_sub (Ob_mono hc' (by omega)) h2; exact Ob_of_eq this (by rw [hC]; ring)
  have hWO : Ob p (3 * (s : ℤ) + 2 + e) W := by
    refine Ob_add ?_ ?_
    · refine Ob_mono (Ob_mul hx hcO) ?_; omega
    · refine Ob_mono (Ob_mul hD hbO) ?_; omega
  have hDW : Ob p 2 (D + W) := Ob_add hD (Ob_mono hWO (by omega))
  have h2DW : Ob p 2 (2 * D + W) := Ob_add (Ob_unit_mul Ob_two hD) (Ob_mono hWO (by omega))
  have hxuO : Ob p 1 xu := by have := Ob_sub hx (Ob_mono hxu (by norm_num)); exact Ob_of_eq this (by ring)
  have hDuO : Ob p 2 Du := by have := Ob_sub hD (Ob_mono hDu (by norm_num)); exact Ob_of_eq this (by ring)
  have hhalf : Ob p 0 ((1 : ℚ_[p]) / 2) := by rw [one_div]; exact Ob_inv_two E.hp2
  -- the difference of the `T` polynomials
  have hT : Ob p 5 ((3 * (u : ℚ_[p]) ^ 2 * x ^ 2 * D + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * x ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * x * D + (u : ℚ_[p]) ^ 2 * D ^ 2)
      - (3 * (u : ℚ_[p]) ^ 2 * xu ^ 2 * Du + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu * Du + (u : ℚ_[p]) ^ 2 * Du ^ 2)) := by
    have e1 : Ob p 5 (x ^ 2 * D - xu ^ 2 * Du) := by
      have a1 : Ob p 5 ((x - xu) * (x + xu) * D) := Ob_mono (Ob_mul (Ob_mul hxu (Ob_add hx hxuO)) hD) (by norm_num)
      have a2 : Ob p 5 (xu ^ 2 * (D - Du)) := Ob_mono (Ob_mul (Ob_pow hxuO 2) hDu) (by norm_num)
      exact Ob_of_eq (Ob_add a1 a2) (by ring)
    have e2 : Ob p 5 ((p : ℚ_[p]) * (x ^ 3 - xu ^ 3)) := by
      have hq : Ob p 2 (x ^ 2 + x * xu + xu ^ 2) :=
        Ob_add (Ob_add (Ob_pow hx 2) (Ob_mul hx hxuO)) (Ob_pow hxuO 2)
      have := Ob_mul Ob_p (Ob_mul hxu hq)
      exact Ob_of_eq (Ob_mono this (by norm_num)) (by ring)
    have e3 : Ob p 5 ((p : ℚ_[p]) * (x * D - xu * Du)) := by
      have a1 : Ob p 4 ((x - xu) * D) := Ob_mono (Ob_mul hxu hD) (by norm_num)
      have a2 : Ob p 4 (xu * (D - Du)) := Ob_mono (Ob_mul hxuO hDu) (by norm_num)
      have := Ob_mul Ob_p (Ob_add a1 a2)
      exact Ob_of_eq this (by ring)
    have e4 : Ob p 5 (D ^ 2 - Du ^ 2) := by
      have := Ob_mul hDu (Ob_add hD hDuO)
      exact Ob_of_eq (Ob_mono this (by norm_num)) (by ring)
    have hu0 : Ob p 0 (u : ℚ_[p]) := Ob_natCast u
    have := Ob_add (Ob_add (Ob_add (Ob_unit_mul (Ob_unit_mul Ob_three (Ob_pow hu0 2)) e1)
      (Ob_unit_mul (Ob_unit_mul (Ob_ofNat 4) hu0) e2)) (Ob_unit_mul (Ob_unit_mul (Ob_ofNat 4) hu0) e3))
      (Ob_unit_mul (Ob_pow hu0 2) e4)
    exact Ob_of_eq this (by ring)
  have key : (x * (a + 1)) ^ 2 * (x * (a + 1) + y * (b + 1)) - x ^ 2 * (x + y)
        + 1 / 2 * ((x * (a + 1) + y * (b + 1)) ^ 2 - (x + y) ^ 2)
        - (x * (a + 1) * (x * (a + 1) + y * (b + 1)) ^ 2 - x * (x + y) ^ 2)
        + 1 / 2 * h * (p : ℚ_[p]) ^ (3 * s)
          * (3 * (u : ℚ_[p]) ^ 2 * xu ^ 2 * Du + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu * Du + (u : ℚ_[p]) ^ 2 * Du ^ 2)
      = (2 * x ^ 2 * D * A + x ^ 3 * C + x ^ 2 * D * B + x * D * C + D ^ 2 * B)
        - 1 / 2 * h * (p : ℚ_[p]) ^ (3 * s) *
          ((3 * (u : ℚ_[p]) ^ 2 * x ^ 2 * D + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * x ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * x * D + (u : ℚ_[p]) ^ 2 * D ^ 2)
            - (3 * (u : ℚ_[p]) ^ 2 * xu ^ 2 * Du + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu * Du + (u : ℚ_[p]) ^ 2 * Du ^ 2))
        + (a ^ 2 * x ^ 2 * D + x ^ 2 * (2 * a + a ^ 2) * W + 1 / 2 * W ^ 2 - x * a * (D + W) ^ 2
            - x * W * (2 * D + W)) := by
    rw [hW, hA, hB, hC, hDdef]; ring
  rw [key]
  have m1 : Ob p (3 * (s : ℤ) + 5 + e) (2 * x ^ 2 * D * A + x ^ 3 * C + x ^ 2 * D * B + x * D * C + D ^ 2 * B) := by
    refine Ob_add (Ob_add (Ob_add (Ob_add ?_ ?_) ?_) ?_) ?_
    · refine Ob_mono (Ob_mul (Ob_mul (Ob_unit_mul Ob_two (Ob_pow hx 2)) hD) ha) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_pow hx 3) hc') ?_; omega
    · refine Ob_mono (Ob_mul (Ob_mul (Ob_pow hx 2) hD) hb) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_mul hx hD) hc') ?_; omega
    · refine Ob_mono (Ob_mul (Ob_pow hD 2) hb) ?_; omega
  have m2 : Ob p (3 * (s : ℤ) + 5 + e) (1 / 2 * h * (p : ℚ_[p]) ^ (3 * s) *
          ((3 * (u : ℚ_[p]) ^ 2 * x ^ 2 * D + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * x ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * x * D + (u : ℚ_[p]) ^ 2 * D ^ 2)
            - (3 * (u : ℚ_[p]) ^ 2 * xu ^ 2 * Du + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * xu * Du + (u : ℚ_[p]) ^ 2 * Du ^ 2))) := by
    have := Ob_mul (Ob_mul (Ob_unit_mul hhalf hh) (Ob_p_pow (3 * s))) hT
    refine Ob_mono this ?_; push_cast; omega
  have m3 : Ob p (3 * (s : ℤ) + 5 + e) (a ^ 2 * x ^ 2 * D + x ^ 2 * (2 * a + a ^ 2) * W + 1 / 2 * W ^ 2
      - x * a * (D + W) ^ 2 - x * W * (2 * D + W)) := by
    have ha2 : Ob p (3 * (s : ℤ) + e) (2 * a + a ^ 2) :=
      Ob_add (Ob_unit_mul Ob_two haO) (Ob_mono (Ob_pow haO 2) (by omega))
    refine Ob_sub (Ob_sub (Ob_add (Ob_add ?_ ?_) ?_) ?_) ?_
    · refine Ob_mono (Ob_mul (Ob_mul (Ob_pow haO 2) (Ob_pow hx 2)) hD) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_mul (Ob_pow hx 2) ha2) hWO) ?_; omega
    · refine Ob_mono (Ob_unit_mul hhalf (Ob_pow hWO 2)) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_mul hx haO) (Ob_pow hDW 2)) ?_; omega
    · refine Ob_mono (Ob_mul (Ob_mul hx hWO) h2DW) ?_; omega
  exact Ob_add (Ob_sub m1 m2) m3

lemma U_p_eq_Ico : U p p = Ico 1 p := by
  ext i; simp only [mem_U, Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Nat.pos_of_ne_zero (fun h => h2 (h ▸ dvd_zero p)), h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => absurd (Nat.le_of_dvd h1 h) (by omega)⟩

lemma mem_U_p_of {u : ℕ} (hu1 : 1 ≤ u) (hup : u < p) : u ∈ U p p := by
  rw [U_p_eq_Ico, Finset.mem_Ico]; exact ⟨hu1, hup⟩

/-- `D_u = b(p,u) + b(p,p-u) ≡ -2p²/u²  mod p³` (half range) -/
lemma Ob_Du_half (E : EData p e) {u : ℕ} (hu1 : 1 ≤ u) (h2u : 2 * u + 1 ≤ p) :
    Ob p 3 (bb p p u + bb p p (p - u) + 2 * (p : ℚ_[p]) ^ 2 / (u : ℚ_[p]) ^ 2) := by
  have hodd : Odd p := hp.out.odd_of_ne_two E.hp2
  have hu : u ∈ U p p := mem_U_p_of hu1 (by omega)
  have hu' : p - u ∈ U p p := U_p_sub hu
  rw [D_eq hodd hu1 h2u, eps_eq hodd h2u]
  have hmu : Ob p 2 (mu p p u) := by
    have := Ob_mu (p := p) (s := 1) le_rfl u; rwa [pow_one] at this
  rw [bb_eq p hu1]
  have hA : Ob p 1 (cc p p (u - 1) - 1) := by
    have := Ob_cc_sub_one (p := p) (s := 1) le_rfl (k := u - 1) (by rw [pow_one]; omega)
    rwa [pow_one] at this
  set A := cc p p (u - 1)
  have hu0 : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have hpu : ((p : ℚ_[p]) - (u : ℚ_[p])) ≠ 0 := by
    have : ((p - u : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show p - u ≠ 0 by omega)
    rwa [Nat.cast_sub (by omega)] at this
  have hpu_unit : Ob p 0 (((p : ℚ_[p]) - (u : ℚ_[p]))⁻¹) := by
    rw [← Nat.cast_sub (by omega)]
    have := Ob_inv_U hu' 1; rwa [pow_one] at this
  have hu_unit : Ob p 0 (((u : ℚ_[p]) ^ 2)⁻¹) := Ob_inv_U hu 2
  have hu_unit1 : Ob p 0 ((u : ℚ_[p])⁻¹) := by have := Ob_inv_U hu 1; rwa [pow_one] at this
  have hAO : Ob p 0 A := Ob_cc _ _
  have key : (p : ℚ_[p]) / (u : ℚ_[p]) * A * (2 * (p : ℚ_[p]) / ((p : ℚ_[p]) - (u : ℚ_[p]))
        - ((p : ℚ_[p]) + (u : ℚ_[p])) / ((p : ℚ_[p]) - (u : ℚ_[p])) * mu p p u) + 2 * (p : ℚ_[p]) ^ 2 / (u : ℚ_[p]) ^ 2
      = 2 * (p : ℚ_[p]) ^ 2 * ((u : ℚ_[p]) * (A - 1) + (p : ℚ_[p])) * (((u : ℚ_[p]) ^ 2)⁻¹ * ((p : ℚ_[p]) - (u : ℚ_[p]))⁻¹)
        - (p : ℚ_[p]) * ((u : ℚ_[p])⁻¹ * A * ((p : ℚ_[p]) + (u : ℚ_[p])) * (((p : ℚ_[p]) - (u : ℚ_[p]))⁻¹ * mu p p u)) := by
    field_simp; ring
  rw [key]
  refine Ob_sub ?_ ?_
  · have h1 : Ob p 3 (2 * (p : ℚ_[p]) ^ 2 * ((u : ℚ_[p]) * (A - 1) + (p : ℚ_[p]))) := by
      have := Ob_mul (Ob_unit_mul Ob_two (Ob_p_pow 2)) (Ob_add (Ob_unit_mul (Ob_natCast u) hA) Ob_p)
      refine Ob_mono this ?_; norm_num
    exact Ob_mul_unit h1 (Ob_mul_unit hu_unit hpu_unit)
  · have h2 : Ob p 2 ((u : ℚ_[p])⁻¹ * A * ((p : ℚ_[p]) + (u : ℚ_[p])) * (((p : ℚ_[p]) - (u : ℚ_[p]))⁻¹ * mu p p u)) :=
      Ob_unit_mul (Ob_mul_unit (Ob_mul_unit hu_unit1 hAO) (Ob_add (Ob_natCast p) (Ob_natCast u)))
        (Ob_unit_mul hpu_unit hmu)
    have := Ob_mul Ob_p h2
    refine Ob_mono this ?_; norm_num

/-- `D_u ≡ -2p²/u²  mod p³` for all `u ∈ U p` -/
lemma Ob_Du (E : EData p e) {u : ℕ} (hu : u ∈ U p p) :
    Ob p 3 (bb p p u + bb p p (p - u) + 2 * (p : ℚ_[p]) ^ 2 / (u : ℚ_[p]) ^ 2) := by
  have hu' : p - u ∈ U p p := U_p_sub hu
  have hu2 := hu
  rw [mem_U] at hu2
  have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu2.2 (h ▸ dvd_zero p))
  have hodd : Odd p := hp.out.odd_of_ne_two E.hp2
  by_cases h2u : 2 * u + 1 ≤ p
  · exact Ob_Du_half E hu1 h2u
  · have h2u' : 2 * (p - u) + 1 ≤ p := by obtain ⟨t, ht⟩ := hodd; omega
    have hh := Ob_Du_half E (u := p - u) (by omega) h2u'
    rw [show p - (p - u) = u by omega] at hh
    have hdiff : Ob p 3 (2 * (p : ℚ_[p]) ^ 2 / (u : ℚ_[p]) ^ 2 - 2 * (p : ℚ_[p]) ^ 2 / ((p - u : ℕ) : ℚ_[p]) ^ 2) := by
      have hu0 : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
      have hpu0 : ((p - u : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show p - u ≠ 0 by omega)
      have key : 2 * (p : ℚ_[p]) ^ 2 / (u : ℚ_[p]) ^ 2 - 2 * (p : ℚ_[p]) ^ 2 / ((p - u : ℕ) : ℚ_[p]) ^ 2
          = 2 * (p : ℚ_[p]) ^ 2 * (((p - u : ℕ) : ℚ_[p]) - (u : ℚ_[p])) * (((p - u : ℕ) : ℚ_[p]) + (u : ℚ_[p]))
            * ((((u : ℚ_[p]) ^ 2)⁻¹ * (((p - u : ℕ) : ℚ_[p]) ^ 2)⁻¹)) := by
        field_simp; ring
      rw [key]
      have h1 : Ob p 1 (((p - u : ℕ) : ℚ_[p]) + (u : ℚ_[p])) := by
        rw [Nat.cast_sub (by omega)]; exact Ob_of_eq Ob_p (by ring)
      have := Ob_mul_unit (Ob_mul (Ob_mul_unit (Ob_unit_mul Ob_two (Ob_p_pow 2))
        (Ob_sub (Ob_natCast (p - u)) (Ob_natCast u))) h1) (Ob_mul_unit (Ob_inv_U hu 2) (Ob_inv_U hu' 2))
      refine Ob_mono this ?_; norm_num
    have := Ob_add hh hdiff
    exact Ob_of_eq this (by ring)

/-- **ATOM** (per `u`): `T_u ≡ -6 p⁴ / u²  mod p⁵` -/
lemma Ob_Tu (E : EData p e) {u : ℕ} (hu : u ∈ U p p) :
    Ob p 5 (3 * (u : ℚ_[p]) ^ 2 * (bb p p u) ^ 2 * (bb p p u + bb p p (p - u))
      + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * (bb p p u) ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * bb p p u * (bb p p u + bb p p (p - u))
      + (u : ℚ_[p]) ^ 2 * (bb p p u + bb p p (p - u)) ^ 2 + 6 * (p : ℚ_[p]) ^ 4 / (u : ℚ_[p]) ^ 2) := by
  have hDu := Ob_Du E hu
  have hu2 := hu
  rw [mem_U] at hu2
  have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu2.2 (h ▸ dvd_zero p))
  rw [bb_eq p hu1] at hDu ⊢
  have hA : Ob p 1 (cc p p (u - 1) - 1) := by
    have := Ob_cc_sub_one (p := p) (s := 1) le_rfl (k := u - 1) (by rw [pow_one]; omega)
    rwa [pow_one] at this
  set A := cc p p (u - 1)
  have hAO : Ob p 0 A := Ob_cc _ _
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu0 : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  obtain ⟨d, hd⟩ : ∃ d, (p : ℚ_[p]) / u * A + bb p p (p - u) = (p : ℚ_[p]) ^ 2 * d :=
    ⟨((p : ℚ_[p]) / u * A + bb p p (p - u)) / (p : ℚ_[p]) ^ 2, by field_simp⟩
  rw [hd] at hDu ⊢
  have hu_unit : Ob p 0 (((u : ℚ_[p]) ^ 2)⁻¹) := Ob_inv_U hu 2
  have hdO : Ob p 1 (d + 2 / (u : ℚ_[p]) ^ 2) := by
    have := Ob_div_p_pow hDu 2
    refine Ob_of_eq (Ob_mono this (by norm_num)) ?_
    field_simp
  have hd0 : Ob p 0 d := by
    have := Ob_sub (Ob_mono hdO (by norm_num)) (Ob_of_eq (Ob_unit_mul Ob_two hu_unit) (show (2 : ℚ_[p]) / (u : ℚ_[p]) ^ 2 = 2 * ((u : ℚ_[p]) ^ 2)⁻¹ by rw [div_eq_mul_inv]))
    exact Ob_of_eq this (by ring)
  have key : 3 * (u : ℚ_[p]) ^ 2 * ((p : ℚ_[p]) / u * A) ^ 2 * ((p : ℚ_[p]) ^ 2 * d)
      + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * ((p : ℚ_[p]) / u * A) ^ 3 + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * ((p : ℚ_[p]) / u * A) * ((p : ℚ_[p]) ^ 2 * d)
      + (u : ℚ_[p]) ^ 2 * ((p : ℚ_[p]) ^ 2 * d) ^ 2 + 6 * (p : ℚ_[p]) ^ 4 / (u : ℚ_[p]) ^ 2
      = (p : ℚ_[p]) ^ 4 * (3 * ((A - 1) * (A + 1)) * d + (u : ℚ_[p]) ^ 2 * ((d + 2 / (u : ℚ_[p]) ^ 2) * (d - 2 / (u : ℚ_[p]) ^ 2))
          + 4 * ((A - 1) * (A ^ 2 + A + 1)) * ((u : ℚ_[p]) ^ 2)⁻¹ + 4 * (A - 1) * d + 7 * (d + 2 / (u : ℚ_[p]) ^ 2)) := by
    field_simp; ring
  rw [key]
  have hdm : Ob p 0 (d - 2 / (u : ℚ_[p]) ^ 2) := by
    have := Ob_sub hd0 (Ob_of_eq (Ob_unit_mul Ob_two hu_unit) (show (2 : ℚ_[p]) / (u : ℚ_[p]) ^ 2 = 2 * ((u : ℚ_[p]) ^ 2)⁻¹ by rw [div_eq_mul_inv]))
    exact this
  have hin : Ob p 1 (3 * ((A - 1) * (A + 1)) * d + (u : ℚ_[p]) ^ 2 * ((d + 2 / (u : ℚ_[p]) ^ 2) * (d - 2 / (u : ℚ_[p]) ^ 2))
          + 4 * ((A - 1) * (A ^ 2 + A + 1)) * ((u : ℚ_[p]) ^ 2)⁻¹ + 4 * (A - 1) * d + 7 * (d + 2 / (u : ℚ_[p]) ^ 2)) := by
    refine Ob_add (Ob_add (Ob_add (Ob_add ?_ ?_) ?_) ?_) ?_
    · exact Ob_mul_unit (Ob_unit_mul Ob_three (Ob_mul_unit hA (Ob_add hAO Ob_one))) hd0
    · exact Ob_unit_mul (Ob_pow (Ob_natCast u) 2) (Ob_mul_unit hdO hdm)
    · exact Ob_mul_unit (Ob_unit_mul (Ob_ofNat 4) (Ob_mul_unit hA (Ob_add (Ob_add (Ob_pow hAO 2) hAO) Ob_one))) hu_unit
    · exact Ob_mul_unit (Ob_unit_mul (Ob_ofNat 4) hA) hd0
    · exact Ob_unit_mul (Ob_ofNat 7) hdO
  have := Ob_mul (Ob_p_pow 4) hin
  refine Ob_mono this ?_; norm_num

/-- deep level: `b(p^s, p^{s-1} u) ≡ b(p, u)  mod p³` -/
lemma Ob_bb_deep (E : EData p e) {s : ℕ} (hs : 1 ≤ s) {u : ℕ} (hu1 : 1 ≤ u) :
    Ob p 3 (bb p (p ^ s) (p ^ (s - 1) * u) - bb p p u) := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0
      simp only [zero_add, pow_one, Nat.sub_self, pow_zero, one_mul, sub_self]
      exact Ob_zero 3
    · have ih' := ih h0
      have hdesc : bb p (p ^ (s + 1)) (p ^ s * u)
          = bb p (p ^ s) (p ^ (s - 1) * u) * rho p 1 (p ^ (s + 1)) (p ^ s * u) := by
        have h1 : p ^ (s + 1) = p * p ^ s := by ring
        have h2 : p ^ s * u = p * (p ^ (s - 1) * u) := by
          rw [← mul_assoc, ← pow_succ']; congr 2; omega
        rw [h1, h2, bb_descent_mul (p ^ s) (Nat.mul_pos (pow_pos hp.out.pos _) hu1), ← h1, ← h2]
      rw [Nat.add_sub_cancel, hdesc]
      have hρ : Ob p 3 (rho p 1 (p ^ (s + 1)) (p ^ s * u) - 1) := by
        have := Ob_rho_top E (s := s) (v := s - 1) (by omega) u
        rw [show s - 1 + 1 = s by omega] at this
        refine Ob_mono this ?_; have := E.he; omega
      have := Ob_add (Ob_mul_unit hρ (Ob_bb (p ^ s) (p ^ (s - 1) * u))) ih'
      exact Ob_of_eq this (by ring)

end A357565Proof

-- ===== Dev12 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

/-- middle levels of the `Mt` sum -/
lemma Ob_Mt_term_mid (E : EData p e) {s k' : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k') (hkN : k' < p ^ s)
    (hnd : ¬ p ^ (s - 1) ∣ k') :
    Ob p (3 * (s : ℤ) + 6) (Gk p (p * p ^ s) (p * k') - Gk p (p ^ s) k') := by
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show k' ≠ 0 by omega) p hp.out.ne_one
  have hv : v + 2 ≤ s := by
    by_contra h; push_neg at h
    apply hnd
    exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) u
  have hodd : Odd (p ^ s) := odd_pow_of_EData E s
  obtain ⟨u', hu', hsub⟩ := sub_pow_eq hu (by omega) hkN
  rw [Gk_descent hk hkN]
  unfold Gk
  rw [hsub]
  have hx := Ob_bb_level (p := p) (s := s) hu (by omega : v ≤ s)
  have hy := Ob_bb_level (p := p) (s := s) hu' (by omega : v ≤ s)
  have hD : Ob p ((s : ℤ) - v + 2) (bb p (p ^ s) (p ^ v * u) + bb p (p ^ s) (p ^ v * u')) := by
    have := Ob_D hs hu hodd hkN (t := 2) le_rfl (by omega)
    rw [hsub] at this
    exact Ob_mono this (by push_cast; omega)
  have hpn : p * p ^ s = p ^ (s + 1) := by ring
  have hm1 : p * (p ^ v * u) = p ^ (v + 1) * u := by ring
  have hm2 : p * (p ^ v * u') = p ^ (v + 1) * u' := by ring
  rw [hpn, hm1, hm2]
  have ha : Ob p ((s : ℤ) + 2 + e + 2 * v) (rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u) - 1) :=
    Ob_rho_top E (s := s) (v := v) (by omega) u
  have hb : Ob p ((s : ℤ) + 2 + e + 2 * v) (rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u') - 1) :=
    Ob_rho_top E (s := s) (v := v) (by omega) u'
  have hle : p ^ (v + 1) * u ≤ p ^ (s + 1) := by
    rw [← hm1, ← hpn]; exact Nat.mul_le_mul_left p hkN.le
  have hsub' : p ^ (s + 1) - p ^ (v + 1) * u = p ^ (v + 1) * u' := by
    rw [← hpn, ← hm1, ← hm2, ← Nat.mul_sub, hsub]
  have hab : Ob p (2 * (s : ℤ) + 2 + v + e)
      (rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u) - rho p 1 (p ^ (s + 1)) (p ^ (v + 1) * u')) :=
    Ob_rho_diff_gen E (s := s) (v := v) (u := u) (u' := u') (by omega) hle hsub'
  exact Ob_gg_termwise E hv hx hy hD ha hb hab

/-- deep level term of the `Mt` sum -/
lemma Ob_Mt_term_deep (E : EData p e) {s u : ℕ} (hs : 1 ≤ s) (hu : u ∈ U p p) :
    Ob p (3 * (s : ℤ) + 6) (Gk p (p * p ^ s) (p * (p ^ (s - 1) * u)) - Gk p (p ^ s) (p ^ (s - 1) * u)
      + 3 / 2 * Hs p 2 p * (p : ℚ_[p]) ^ (3 * s) *
        (3 * (u : ℚ_[p]) ^ 2 * (bb p p u) ^ 2 * (bb p p u + bb p p (p - u))
          + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * (bb p p u) ^ 3
          + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * bb p p u * (bb p p u + bb p p (p - u))
          + (u : ℚ_[p]) ^ 2 * (bb p p u + bb p p (p - u)) ^ 2 + 6 * (p : ℚ_[p]) ^ 4 / (u : ℚ_[p]) ^ 2)
      - 9 * Hs p 2 p * (p : ℚ_[p]) ^ (3 * s + 4) / (u : ℚ_[p]) ^ 2) := by
  have hu2 := hu; rw [mem_U] at hu2
  have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu2.2 (h ▸ dvd_zero p))
  have hup : u < p := hu2.1
  have hodd : Odd (p ^ s) := odd_pow_of_EData E s
  have he := E.he
  have hk1 : 1 ≤ p ^ (s - 1) * u := Nat.mul_pos (pow_pos hp.out.pos _) hu1
  have hps : p ^ s = p ^ (s - 1) * p := by rw [← pow_succ]; congr 1; omega
  have hkN : p ^ (s - 1) * u < p ^ s := by
    rw [hps]; exact Nat.mul_lt_mul_of_pos_left hup (pow_pos hp.out.pos _)
  have hsub : p ^ s - p ^ (s - 1) * u = p ^ (s - 1) * (p - u) := by rw [Nat.mul_sub, ← hps]
  have hpn : p * p ^ s = p ^ (s + 1) := by ring
  have hm1 : p * (p ^ (s - 1) * u) = p ^ s * u := by rw [← mul_assoc, ← pow_succ']; congr 2; omega
  have hm2 : p * (p ^ (s - 1) * (p - u)) = p ^ s * (p - u) := by
    rw [← mul_assoc, ← pow_succ']; congr 2; omega
  rw [Gk_descent hk1 hkN, hsub, hpn, hm1, hm2]
  unfold Gk; rw [hsub]
  set x := bb p (p ^ s) (p ^ (s - 1) * u) with hxdef
  set y := bb p (p ^ s) (p ^ (s - 1) * (p - u)) with hydef
  set ρ₁ := rho p 1 (p ^ (s + 1)) (p ^ s * u)
  set ρ₂ := rho p 1 (p ^ (s + 1)) (p ^ s * (p - u))
  set xu := bb p p u
  set Du := bb p p u + bb p p (p - u) with hDu_def
  set h := Hs p 2 p
  have hx : Ob p 1 x := by
    have := Ob_bb_level (p := p) (s := s) (v := s - 1) hu2.2 (by omega)
    refine Ob_mono this ?_; omega
  have hD : Ob p 2 (x + y) := by
    have := Ob_D hs hu2.2 hodd hkN (t := 1) (by norm_num) (by omega)
    rw [hsub] at this
    refine Ob_mono this ?_; push_cast; omega
  have hxu : Ob p 3 (x - xu) := Ob_bb_deep E hs hu1
  have hDu : Ob p 3 (x + y - Du) := by
    have h2 := Ob_bb_deep E hs (u := p - u) (by omega)
    have := Ob_add hxu h2
    exact Ob_of_eq this (by rw [hDu_def]; ring)
  have ha := Ob_rho_deep E hs u
  have hb : Ob p (3 * (s : ℤ) + 1 + e) (ρ₂ - 1 + (u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h) := by
    have h1 := Ob_rho_deep E hs (p - u)
    push_cast [Nat.cast_sub hup.le] at h1
    have h2 : Ob p (3 * (s : ℤ) + 1 + e)
        ((p : ℚ_[p]) * ((p : ℚ_[p]) - 2 * (u : ℚ_[p])) / 2 * (p : ℚ_[p]) ^ (3 * s) * h) := by
      have := Ob_mul (Ob_mul (Ob_mul_unit (Ob_mul_unit Ob_p
        (Ob_sub (Ob_natCast p) (Ob_unit_mul Ob_two (Ob_natCast u)))) (Ob_inv_two E.hp2)) (Ob_p_pow (3 * s))) E.hh
      refine Ob_of_eq (Ob_mono this ?_) ?_
      · push_cast; omega
      · ring
    have := Ob_sub h1 h2
    exact Ob_of_eq this (by ring)
  have hc := Ob_rho_deep_diff E hs hup.le
  have hI := Ob_deep_inner E hs hx hD hxu hDu E.hh ha hb hc
  have hL : Ob p (3 * (s : ℤ) + e) ((u : ℚ_[p]) ^ 2 / 2 * (p : ℚ_[p]) ^ (3 * s) * h) := by
    have := Ob_mul (Ob_unit_mul (Ob_mul_unit (Ob_pow (Ob_natCast u) 2) (Ob_inv_two E.hp2)) (Ob_p_pow (3 * s))) E.hh
    refine Ob_of_eq (Ob_mono this ?_) ?_
    · push_cast; omega
    · ring
  have hbO : Ob p (3 * (s : ℤ) + e) (ρ₂ - 1) := by
    have := Ob_sub (Ob_mono hb (by omega)) hL; exact Ob_of_eq this (by ring)
  have hcO : Ob p (3 * (s : ℤ) + 1 + e) (ρ₁ - ρ₂) := by
    have h2 : Ob p (3 * (s : ℤ) + 1 + e) (2 * (u : ℚ_[p]) * h * (p : ℚ_[p]) ^ (3 * s + 1)) := by
      have := Ob_mul (Ob_mul (Ob_unit_mul Ob_two (Ob_natCast u)) E.hh) (Ob_p_pow (3 * s + 1))
      refine Ob_mono this ?_; push_cast; omega
    have := Ob_sub (Ob_mono hc (by omega)) h2; exact Ob_of_eq this (by ring)
  set W := x * (ρ₁ - ρ₂) + (x + y) * (ρ₂ - 1) with hW
  have hWO : Ob p (3 * (s : ℤ) + 2 + e) W := by
    refine Ob_add ?_ ?_
    · refine Ob_mono (Ob_mul hx hcO) ?_; omega
    · refine Ob_mono (Ob_mul hD hbO) ?_; omega
  have hcubic : Ob p (3 * (s : ℤ) + 6) ((x * ρ₁ + y * ρ₂) ^ 3 - (x + y) ^ 3) := by
    have hq : Ob p 4 (3 * (x + y) ^ 2 + 3 * (x + y) * W + W ^ 2) := by
      refine Ob_add (Ob_add (Ob_unit_mul Ob_three (Ob_pow hD 2)) ?_) ?_
      · refine Ob_mono (Ob_mul (Ob_unit_mul Ob_three hD) hWO) ?_; omega
      · refine Ob_mono (Ob_pow hWO 2) ?_; omega
    have := Ob_mul hWO hq
    refine Ob_of_eq (Ob_mono this ?_) ?_
    · omega
    · rw [hW]; ring
  have h3I := Ob_mono (Ob_mul E.h3 hI) (show (3 * (s : ℤ) + 6) ≤ (1 - (e : ℤ)) + (3 * (s : ℤ) + 5 + e) by omega)
  have := Ob_add h3I hcubic
  refine Ob_of_eq this ?_
  unfold gg; ring

lemma Ico_filter_pow_dvd {s : ℕ} (hs : 1 ≤ s) :
    (Ico 1 (p ^ s)).filter (fun k => p ^ (s - 1) ∣ k) = (U p p).image (fun u => p ^ (s - 1) * u) := by
  rw [U_p_eq_Ico]
  ext k; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
  have hpos : 0 < p ^ (s - 1) := pow_pos hp.out.pos _
  have hps : p ^ s = p ^ (s - 1) * p := by rw [← pow_succ]; congr 1; omega
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨u, rfl⟩⟩
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos u with h0 | h0
      · subst h0; simp at h1
      · exact h0
    · rw [hps] at h2; exact Nat.lt_of_mul_lt_mul_left h2
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hpos h1, ?_⟩, dvd_mul_right _ _⟩
    rw [hps]; exact Nat.mul_lt_mul_of_pos_left h2 hpos

/-- the deep part of the `Mt` sum -/
lemma Ob_Mt_deep (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6)
      (∑ u ∈ U p p, (Gk p (p * p ^ s) (p * (p ^ (s - 1) * u)) - Gk p (p ^ s) (p ^ (s - 1) * u))) := by
  have he := E.he
  have h1 := Ob_sum (U p p) (fun u hu => Ob_Mt_term_deep E hs hu)
  have h32 : Ob p (1 - (e : ℤ)) ((3 : ℚ_[p]) / 2) := by
    rw [div_eq_mul_inv]; exact Ob_mul_unit E.h3 (Ob_inv_two E.hp2)
  have h2 : Ob p (3 * (s : ℤ) + 6) (3 / 2 * Hs p 2 p * (p : ℚ_[p]) ^ (3 * s) *
      ∑ u ∈ U p p, (3 * (u : ℚ_[p]) ^ 2 * (bb p p u) ^ 2 * (bb p p u + bb p p (p - u))
          + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * (bb p p u) ^ 3
          + 4 * (p : ℚ_[p]) * (u : ℚ_[p]) * bb p p u * (bb p p u + bb p p (p - u))
          + (u : ℚ_[p]) ^ 2 * (bb p p u + bb p p (p - u)) ^ 2 + 6 * (p : ℚ_[p]) ^ 4 / (u : ℚ_[p]) ^ 2)) := by
    have := Ob_mul (Ob_mul (Ob_mul h32 E.hh) (Ob_p_pow (3 * s))) (Ob_sum (U p p) (fun u hu => Ob_Tu E hu))
    refine Ob_mono this ?_; push_cast; omega
  have h3 : Ob p (3 * (s : ℤ) + 6) (∑ u ∈ U p p, 9 * Hs p 2 p * (p : ℚ_[p]) ^ (3 * s + 4) / (u : ℚ_[p]) ^ 2) := by
    have h9 : Ob p (2 * (1 - (e : ℤ))) (9 : ℚ_[p]) := by
      have := Ob_pow E.h3 2; exact Ob_of_eq this (by norm_num)
    have := Ob_mul (Ob_mul (Ob_mul h9 E.hh) (Ob_p_pow (3 * s + 4))) E.hh
    refine Ob_of_eq (Ob_mono this ?_) ?_
    · push_cast; omega
    · show _ = 9 * Hs p 2 p * (p : ℚ_[p]) ^ (3 * s + 4) * ∑ u ∈ U p p, ((u : ℚ_[p]) ^ 2)⁻¹
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; rw [div_eq_mul_inv]
  have := Ob_add (Ob_sub h1 h2) h3
  refine Ob_of_eq this ?_
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  ring

/-- **Mt**: the multiples-of-`p` part -/
theorem Ob_Mt (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6) (∑ k' ∈ Ico 1 (p ^ s), (Gk p (p * p ^ s) (p * k') - Gk p (p ^ s) k')) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Ico 1 (p ^ s)) (fun k => p ^ (s - 1) ∣ k),
    Ico_filter_pow_dvd hs, Finset.sum_image (by
      intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h)]
  refine Ob_add (Ob_Mt_deep E hs) (Ob_sum _ ?_)
  intro k' hk'
  simp only [Finset.mem_filter, Finset.mem_Ico] at hk'
  exact Ob_Mt_term_mid E hs hk'.1.1 hk'.1.2 hk'.2

end A357565Proof

-- ===== Dev13 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

lemma norm_M_sub {M k : ℕ} (hM : p ∣ M) (hk : k ∈ U p M) : ‖(M : ℚ_[p]) - (k : ℚ_[p])‖ = 1 := by
  have h := U_reflect_mem hM k hk
  have hle : k ≤ M := (mem_U.1 hk).1.le
  rw [← Nat.cast_sub hle]; exact norm_U h

lemma Ob_rho_n {s : ℕ} (k : ℕ) : Ob p ((s : ℤ) + 1) (rho p 1 (p * p ^ s) k - 1) := by
  have := Ob_rho_sub_one_pow (p := p) 1 (s + 1) k
  rw [pow_succ'] at this
  exact Ob_cast (by push_cast; ring) this

lemma odd_n_of_EData (E : EData p e) (s : ℕ) : Odd (p * p ^ s) := by
  have := odd_pow_of_EData E (s + 1); rwa [pow_succ'] at this

lemma eps_expand (E : EData p e) {s k : ℕ} (hk : k ∈ U p (p * p ^ s)) (h2k : 2 * k + 1 ≤ p * p ^ s) :
    eps p (p * p ^ s) k = 2 * ((p * p ^ s : ℕ) : ℚ_[p]) / (((p * p ^ s : ℕ) : ℚ_[p]) - k)
      - ((((p * p ^ s : ℕ) : ℚ_[p]) + k) / (((p * p ^ s : ℕ) : ℚ_[p]) - k))
        * (mu p (p ^ s) (k / p) + (1 - mu p (p ^ s) (k / p)) * (1 - Phi p (p ^ s) k)) := by
  rw [eps_eq (odd_n_of_EData E s) h2k]
  have hm := mu_descent (p := p) (N := p ^ s) (k' := k / p) (k₀ := k % p) (Nat.mod_lt k hp.out.pos)
    (odd_pow_of_EData E s)
  rw [Nat.div_add_mod] at hm
  rw [hm]

lemma sum_U_eq_half {M : ℕ} (hM : p ∣ M) (hodd : Odd M) (f : ℕ → ℚ_[p])
    (hf : ∀ k ∈ U p ((M + 1) / 2), f (M - k) = 0) :
    ∑ k ∈ U p M, f k = ∑ k ∈ U p ((M + 1) / 2), f k := by
  rw [sum_U_half hM hodd]
  apply Finset.sum_congr rfl; intro k hk; rw [hf k hk, add_zero]

lemma mu_eq_zero {N k' : ℕ} (h : N ≤ 2 * k' + 1) : mu p N k' = 0 := by
  unfold mu Psi
  rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty, sub_self]

lemma mu_div_eq_zero {N k : ℕ} (hk : p * N + 1 ≤ 2 * k) : mu p N (k / p) = 0 := by
  apply mu_eq_zero
  by_contra h; push_neg at h
  have h1 : p * (2 * (k / p) + 2) ≤ p * N := Nat.mul_le_mul_left p (by omega)
  have h2 := Nat.div_add_mod k p
  have h3 := Nat.mod_lt k hp.out.pos
  have : p * (2 * (k / p) + 2) = 2 * (p * (k / p)) + 2 * p := by ring
  omega

lemma sum_U_div (N : ℕ) (F : ℕ → ℚ_[p]) (j : ℕ) :
    ∑ k ∈ U p (p * N), F (k / p) * ((k : ℚ_[p]) ^ j)⁻¹
      = ∑ k' ∈ range N, F k' * ∑ k₀ ∈ U p p, ((((p * k' + k₀ : ℕ) : ℚ_[p])) ^ j)⁻¹ := by
  rw [sum_U_mul (dvd_refl p)]
  apply Finset.sum_congr rfl; intro k' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k₀ hk₀
  have hdiv : (p * k' + k₀) / p = k' := by
    rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt (mem_U.1 hk₀).1]; simp
  rw [hdiv]

lemma Ob_Lam3 (hp2 : p ≠ 2) (k' : ℕ) :
    Ob p 1 (∑ k₀ ∈ U p p, ((((p * k' + k₀ : ℕ) : ℚ_[p])) ^ 3)⁻¹) := by
  have hj : Ob p 1 (2 * ((p : ℚ_[p]) * (k' : ℚ_[p])) + (p : ℚ_[p])) := by
    have := Ob_mul_unit (Ob_p (p := p)) (Ob_add (Ob_unit_mul Ob_two (Ob_natCast k')) Ob_one)
    exact Ob_of_eq this (by ring)
  have := Ob_sum_inv_cube_pair (p := p) hp2 (dvd_refl p) ((p : ℚ_[p]) * (k' : ℚ_[p]))
    (Ob_unit_mul (Ob_natCast p) (Ob_natCast k'))
    (fun i hi => by have := norm_block (dvd_refl p) hi k'; rwa [add_comm] at this) hj
  refine Ob_of_eq this ?_
  apply Finset.sum_congr rfl; intro k₀ _; push_cast; ring_nf

lemma sum_Lam1 (k' : ℕ) : ∑ k₀ ∈ U p p, ((((p * k' + k₀ : ℕ) : ℚ_[p])) ^ 2)⁻¹ = Lam p 1 k' := by
  unfold Lam; rw [pow_one]
  apply Finset.sum_congr rfl; intro k₀ _; push_cast; ring_nf

/-- `∑_{k ∈ U((p²+1)/2)} k^{-4} = O(p)` -/
lemma Ob_half_inv4 (E : EData p e) : Ob p 1 (∑ k ∈ U p ((p * p + 1) / 2), ((k : ℚ_[p]) ^ 4)⁻¹) := by
  have hM : p ∣ p * p := dvd_mul_right p p
  have hodd : Odd (p * p) := by have := odd_pow_of_EData E 2; rwa [pow_two] at this
  have hH : Ob p 1 (Hs p 4 (p * p)) := by
    have := Ob_Hs_pow_succ E.hp2 3 (m := 1) le_rfl
    rw [pow_succ, pow_one] at this
    have h2 : Ob p 1 ((p : ℚ_[p]) * Hs p 4 p) := Ob_mul_unit Ob_p (Ob_Hs _ _)
    exact Ob_of_sub (Ob_mono this (by norm_num)) h2
  have hsplit : Hs p 4 (p * p) = ∑ k ∈ U p ((p * p + 1) / 2), (((k : ℚ_[p]) ^ 4)⁻¹ + (((p * p - k : ℕ) : ℚ_[p]) ^ 4)⁻¹) := by
    unfold Hs; exact sum_U_half hM hodd _
  have hdiff : Ob p 1 (∑ k ∈ U p ((p * p + 1) / 2), ((((p * p - k : ℕ) : ℚ_[p]) ^ 4)⁻¹ - ((k : ℚ_[p]) ^ 4)⁻¹)) := by
    apply Ob_sum; intro k hk
    have hk' : k ∈ U p (p * p) := U_mono (by omega) hk
    have hkle : k ≤ p * p := (mem_U.1 hk').1.le
    have hn : ‖(-(k : ℚ_[p]))‖ = 1 := by rw [norm_neg]; exact norm_U hk'
    have hnx : ‖-(k : ℚ_[p]) + ((p * p : ℕ) : ℚ_[p])‖ = 1 := by
      rw [add_comm, ← sub_eq_add_neg]; exact norm_M_sub hM hk'
    have hx : Ob p 2 ((p * p : ℕ) : ℚ_[p]) := by push_cast; exact Ob_of_eq (Ob_p_pow 2) (by ring)
    have := Ob_inv_pow_sub hn hnx hx 4
    refine Ob_of_eq (Ob_mono this (by norm_num)) ?_
    rw [Nat.cast_sub hkle]; push_cast; ring_nf
  have key : 2 * ∑ k ∈ U p ((p * p + 1) / 2), ((k : ℚ_[p]) ^ 4)⁻¹
      = Hs p 4 (p * p) - ∑ k ∈ U p ((p * p + 1) / 2), ((((p * p - k : ℕ) : ℚ_[p]) ^ 4)⁻¹ - ((k : ℚ_[p]) ^ 4)⁻¹) := by
    rw [hsplit, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  have h2 := Ob_sub hH hdiff
  rw [← key] at h2
  have := Ob_unit_mul (Ob_inv_two E.hp2) h2
  exact Ob_of_eq this (by field_simp)

end A357565Proof

-- ===== Dev14 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

noncomputable def nq (p : ℕ) [Fact p.Prime] (s : ℕ) : ℚ_[p] := (p : ℚ_[p]) * (p : ℚ_[p]) ^ s
noncomputable def cq (p : ℕ) [Fact p.Prime] (s k : ℕ) : ℚ_[p] := cc p (p ^ s) (k / p)
noncomputable def mq (p : ℕ) [Fact p.Prime] (s k : ℕ) : ℚ_[p] := mu p (p ^ s) (k / p)
noncomputable def dq (p : ℕ) [Fact p.Prime] (s k : ℕ) : ℚ_[p] :=
  (1 - mu p (p ^ s) (k / p)) * (1 - Phi p (p ^ s) k)
noncomputable def rq (p : ℕ) [Fact p.Prime] (s k : ℕ) : ℚ_[p] := rho p 1 (p * p ^ s) k

/-- data at `k ∈ U((n+1)/2)`, `n = p^{s+1}` -/
structure KD (p : ℕ) [Fact p.Prime] (s k : ℕ) : Prop where
  hkU : k ∈ U p (p * p ^ s)
  hnd : ¬ p ∣ k
  hk0 : (k : ℚ_[p]) ≠ 0
  hnk0 : nq p s - (k : ℚ_[p]) ≠ 0
  hkinv : Ob p 0 ((k : ℚ_[p])⁻¹)
  hnkinv : Ob p 0 ((nq p s - (k : ℚ_[p]))⁻¹)
  hcp : Ob p 1 (cq p s k - 1)
  hρ : Ob p ((s : ℤ) + 1) (rq p s k - 1)
  hμ : Ob p 2 (mq p s k)
  hδ : Ob p (2 * (s : ℤ) + 2) (dq p s k)
  hε : Ob p 2 (eps p (p * p ^ s) k)
  hb : bb p (p * p ^ s) k = nq p s / (k : ℚ_[p]) * cq p s k * rq p s k
  he : eps p (p * p ^ s) k = 2 * nq p s / (nq p s - (k : ℚ_[p]))
      - ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * (mq p s k + dq p s k)

lemma Ob_nq (s : ℕ) : Ob p ((s : ℤ) + 1) (nq p s) := by
  unfold nq
  have := Ob_p_pow (p := p) (s + 1)
  rw [pow_succ'] at this
  exact Ob_cast (by push_cast; ring) this

lemma KD_of (E : EData p e) {s k : ℕ} (hs : 1 ≤ s) (hk : k ∈ U p ((p * p ^ s + 1) / 2)) : KD p s k := by
  have hkU : k ∈ U p (p * p ^ s) := U_mono (by omega) hk
  have hk' := mem_U.1 hk
  have hnd : ¬ p ∣ k := hk'.2
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => hnd (h ▸ dvd_zero p))
  have h2k : 2 * k + 1 ≤ p * p ^ s := by omega
  have hnorm : ‖nq p s - (k : ℚ_[p])‖ = 1 := by
    have := norm_M_sub (dvd_mul_right p (p ^ s)) hkU
    push_cast at this; exact this
  have hε : Ob p 2 (eps p (p * p ^ s) k) := by
    have := Ob_eps (p := p) (s := s + 1) (v := 0) (u := k) (by omega) hnd (odd_pow_of_EData E (s + 1))
      (by rw [pow_zero, one_mul, pow_succ']; exact h2k) (t := 2) le_rfl (by omega)
    rw [pow_zero, one_mul, pow_succ'] at this
    exact Ob_mono this (by norm_num)
  refine ⟨hkU, hnd, by exact_mod_cast (show k ≠ 0 by omega), ?_, Ob_inv_of_norm_one (norm_U hkU),
    Ob_inv_of_norm_one hnorm, Ob_cc_sub_one hs (Nat.div_lt_of_lt_mul (mem_U.1 hkU).1), Ob_rho_n k, Ob_mu hs (k / p),
    Ob_unit_mul (Ob_sub Ob_one (Ob_mono (Ob_mu hs (k / p)) (by norm_num))) (Ob_one_sub_Phi s k), hε, ?_, ?_⟩
  · exact norm_ne_zero_iff.1 (by rw [hnorm]; exact one_ne_zero)
  · have := bb_descent_nondiv (p ^ s) hnd; push_cast at this; exact this
  · have := eps_expand E hkU h2k; push_cast at this; exact this

end A357565Proof

-- ===== Dev15 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

lemma Ob_cq0 (s k : ℕ) : Ob p 0 (cq p s k) := Ob_cc _ _
lemma Ob_rq0 (s k : ℕ) : Ob p 0 (rq p s k) := Ob_rho

lemma half_sub_ge {s k : ℕ} (hk : k ∈ U p ((p * p ^ s + 1) / 2)) : p * p ^ s + 1 ≤ 2 * (p * p ^ s - k) := by
  have := (mem_U.1 hk).1; omega

lemma mq_reflect_zero {s k : ℕ} (hk : k ∈ U p ((p * p ^ s + 1) / 2)) : mq p s (p * p ^ s - k) = 0 := by
  unfold mq; exact mu_div_eq_zero (half_sub_ge hk)

/-- **U-a**: `∑_{half} x³ ε = O(p^{3s+6})` -/
lemma Ob_Ua (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6)
      (∑ k ∈ U p ((p * p ^ s + 1) / 2), (bb p (p * p ^ s) k) ^ 3 * eps p (p * p ^ s) k) := by
  have he := E.he
  have hodd := odd_n_of_EData E s
  have hM : p ∣ p * p ^ s := dvd_mul_right _ _
  have hnO := Ob_nq (p := p) s
  have hdec : ∀ k ∈ U p ((p * p ^ s + 1) / 2),
      (bb p (p * p ^ s) k) ^ 3 * eps p (p * p ^ s) k
        = nq p s ^ 3 * ((cq p s k ^ 3 * (rq p s k ^ 3 - 1) * eps p (p * p ^ s) k * ((k : ℚ_[p]) ^ 3)⁻¹
              - cq p s k ^ 3 * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * dq p s k * ((k : ℚ_[p]) ^ 3)⁻¹
              - cq p s k ^ 3 * (2 * nq p s / (nq p s - (k : ℚ_[p]))) * mq p s k * ((k : ℚ_[p]) ^ 3)⁻¹)
            + 2 * nq p s * cq p s k ^ 3 / ((nq p s - (k : ℚ_[p])) * (k : ℚ_[p]) ^ 3)
            + cq p s k ^ 3 * mq p s k * ((k : ℚ_[p]) ^ 3)⁻¹) := by
    intro k hk
    have K := KD_of E hs hk
    have hk0 := K.hk0; have hnk0 := K.hnk0
    rw [K.hb, K.he]
    field_simp; ring
  rw [Finset.sum_congr rfl hdec, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hR : Ob p 3 (∑ k ∈ U p ((p * p ^ s + 1) / 2),
      (cq p s k ^ 3 * (rq p s k ^ 3 - 1) * eps p (p * p ^ s) k * ((k : ℚ_[p]) ^ 3)⁻¹
        - cq p s k ^ 3 * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * dq p s k * ((k : ℚ_[p]) ^ 3)⁻¹
        - cq p s k ^ 3 * (2 * nq p s / (nq p s - (k : ℚ_[p]))) * mq p s k * ((k : ℚ_[p]) ^ 3)⁻¹)) := by
    apply Ob_sum; intro k hk
    have K := KD_of E hs hk
    have hc3 : Ob p 0 (cq p s k ^ 3) := Ob_pow (Ob_cq0 s k) 3
    have hk3 : Ob p 0 (((k : ℚ_[p]) ^ 3)⁻¹) := Ob_inv_U K.hkU 3
    have hρ3 : Ob p ((s : ℤ) + 1) (rq p s k ^ 3 - 1) := by
      have := Ob_mul_unit K.hρ (Ob_add (Ob_add (Ob_pow (Ob_rq0 s k) 2) (Ob_rq0 s k)) Ob_one)
      exact Ob_of_eq this (by ring)
    have hβ : Ob p 0 ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) := by
      rw [div_eq_mul_inv]; exact Ob_mul_unit (Ob_add (Ob_nonneg_to_zero (by omega) hnO) (Ob_natCast k)) K.hnkinv
    have hα : Ob p ((s : ℤ) + 1) (2 * nq p s / (nq p s - (k : ℚ_[p]))) := by
      rw [div_eq_mul_inv]; exact Ob_mul_unit (Ob_unit_mul Ob_two hnO) K.hnkinv
    have t1 : Ob p 3 (cq p s k ^ 3 * (rq p s k ^ 3 - 1) * eps p (p * p ^ s) k * ((k : ℚ_[p]) ^ 3)⁻¹) := by
      have := Ob_mul_unit (Ob_mul (Ob_unit_mul hc3 hρ3) K.hε) hk3
      refine Ob_mono this ?_; omega
    have t2 : Ob p 3 (cq p s k ^ 3 * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * dq p s k * ((k : ℚ_[p]) ^ 3)⁻¹) := by
      have := Ob_mul_unit (Ob_unit_mul (Ob_mul_unit hc3 hβ) K.hδ) hk3
      refine Ob_mono this ?_; omega
    have t3 : Ob p 3 (cq p s k ^ 3 * (2 * nq p s / (nq p s - (k : ℚ_[p]))) * mq p s k * ((k : ℚ_[p]) ^ 3)⁻¹) := by
      have := Ob_mul_unit (Ob_mul (Ob_unit_mul hc3 hα) K.hμ) hk3
      refine Ob_mono this ?_; omega
    exact Ob_sub (Ob_sub t1 t2) t3
  have hA : Ob p 3 (∑ k ∈ U p ((p * p ^ s + 1) / 2), 2 * nq p s * cq p s k ^ 3 / ((nq p s - (k : ℚ_[p])) * (k : ℚ_[p]) ^ 3)) := by
    rcases Nat.lt_or_ge 1 s with hs2 | hs1
    · apply Ob_sum; intro k hk
      have K := KD_of E hs hk
      have hc3 : Ob p 0 (cq p s k ^ 3) := Ob_pow (Ob_cq0 s k) 3
      have hk3 : Ob p 0 (((k : ℚ_[p]) ^ 3)⁻¹) := Ob_inv_U K.hkU 3
      have := Ob_mul_unit (Ob_mul_unit (Ob_unit_mul Ob_two hnO) hc3) (Ob_mul_unit K.hnkinv hk3)
      refine Ob_of_eq (Ob_mono this (by omega)) ?_
      rw [div_eq_mul_inv, mul_inv]
    · have hs1' : s = 1 := by omega
      subst hs1'
      have h4 : Ob p 1 (∑ k ∈ U p ((p * p ^ 1 + 1) / 2), ((k : ℚ_[p]) ^ 4)⁻¹) := by
        rw [pow_one]; exact Ob_half_inv4 E
      have hn2 : Ob p 2 (nq p 1) := Ob_mono hnO (by norm_num)
      have hdec2 : ∀ k ∈ U p ((p * p ^ 1 + 1) / 2),
          2 * nq p 1 * cq p 1 k ^ 3 / ((nq p 1 - (k : ℚ_[p])) * (k : ℚ_[p]) ^ 3)
            = -(2 * nq p 1) * ((k : ℚ_[p]) ^ 4)⁻¹
              + 2 * nq p 1 * ((k : ℚ_[p]) * (cq p 1 k ^ 3 - 1) + nq p 1) * ((nq p 1 - (k : ℚ_[p]))⁻¹ * ((k : ℚ_[p]) ^ 4)⁻¹) := by
        intro k hk
        have K := KD_of E hs hk
        have hk0 := K.hk0; have hnk0 := K.hnk0
        field_simp; ring
      rw [Finset.sum_congr rfl hdec2, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine Ob_add ?_ ?_
      · have := Ob_mul (Ob_neg (Ob_unit_mul Ob_two hn2)) h4
        refine Ob_mono this ?_; norm_num
      · apply Ob_sum; intro k hk
        have K := KD_of E hs hk
        have hc3 : Ob p 1 (cq p 1 k ^ 3 - 1) := by
          have := Ob_mul_unit K.hcp (Ob_add (Ob_add (Ob_pow (Ob_cq0 1 k) 2) (Ob_cq0 1 k)) Ob_one)
          exact Ob_of_eq this (by ring)
        have hin : Ob p 1 ((k : ℚ_[p]) * (cq p 1 k ^ 3 - 1) + nq p 1) :=
          Ob_add (Ob_unit_mul (Ob_natCast k) hc3) (Ob_mono hn2 (by norm_num))
        have := Ob_mul_unit (Ob_mul (Ob_unit_mul Ob_two hn2) hin) (Ob_mul_unit K.hnkinv (Ob_inv_U K.hkU 4))
        refine Ob_mono this ?_; norm_num
  have hMs : Ob p 3 (∑ k ∈ U p ((p * p ^ s + 1) / 2), cq p s k ^ 3 * mq p s k * ((k : ℚ_[p]) ^ 3)⁻¹) := by
    rw [← sum_U_eq_half hM hodd _ (fun k hk => by rw [mq_reflect_zero hk]; ring)]
    unfold cq mq
    rw [sum_U_div (p ^ s) (fun k' => (cc p (p ^ s) k') ^ 3 * mu p (p ^ s) k') 3]
    apply Ob_sum; intro k' _
    have := Ob_mul (Ob_unit_mul (Ob_pow (Ob_cc (p ^ s) k') 3) (Ob_mu hs k')) (Ob_Lam3 E.hp2 k')
    refine Ob_mono this ?_; norm_num
  have := Ob_mul (Ob_pow hnO 3) (Ob_add (Ob_add hR hA) hMs)
  refine Ob_mono this ?_; push_cast; omega

/-- **U-b**: `∑_{half} x² ε² = O(p^{3s+5+e})` -/
lemma Ob_Ub (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 5 + e)
      (∑ k ∈ U p ((p * p ^ s + 1) / 2), (bb p (p * p ^ s) k) ^ 2 * eps p (p * p ^ s) k ^ 2) := by
  have he := E.he
  have hodd := odd_n_of_EData E s
  have hM : p ∣ p * p ^ s := dvd_mul_right _ _
  have hnO := Ob_nq (p := p) s
  have hdec : ∀ k ∈ U p ((p * p ^ s + 1) / 2),
      (bb p (p * p ^ s) k) ^ 2 * eps p (p * p ^ s) k ^ 2
        = nq p s ^ 2 * (cq p s k ^ 2 * ((k : ℚ_[p]) ^ 2)⁻¹ *
              ((rq p s k ^ 2 - 1) * eps p (p * p ^ s) k ^ 2
                + ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 * dq p s k ^ 2
                - 2 * (2 * nq p s / (nq p s - (k : ℚ_[p]))) * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * dq p s k
                + 2 * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 * mq p s k * dq p s k
                + (((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 - 1) * mq p s k ^ 2
                + 4 * nq p s ^ 2 * (nq p s - 3 * (k : ℚ_[p])) * mq p s k * ((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]))⁻¹)
            + 4 * nq p s ^ 2 * cq p s k ^ 2 * ((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]) ^ 2)⁻¹
            + (-4 * nq p s * cq p s k ^ 2 * mq p s k) * ((k : ℚ_[p]) ^ 3)⁻¹
            + (cq p s k ^ 2 * mq p s k ^ 2) * ((k : ℚ_[p]) ^ 2)⁻¹) := by
    intro k hk
    have K := KD_of E hs hk
    have hk0 := K.hk0; have hnk0 := K.hnk0
    rw [K.hb, K.he]
    field_simp; ring
  rw [Finset.sum_congr rfl hdec, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hR : Ob p ((s : ℤ) + 3 + e) (∑ k ∈ U p ((p * p ^ s + 1) / 2),
      cq p s k ^ 2 * ((k : ℚ_[p]) ^ 2)⁻¹ *
              ((rq p s k ^ 2 - 1) * eps p (p * p ^ s) k ^ 2
                + ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 * dq p s k ^ 2
                - 2 * (2 * nq p s / (nq p s - (k : ℚ_[p]))) * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * dq p s k
                + 2 * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 * mq p s k * dq p s k
                + (((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 - 1) * mq p s k ^ 2
                + 4 * nq p s ^ 2 * (nq p s - 3 * (k : ℚ_[p])) * mq p s k * ((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]))⁻¹)) := by
    apply Ob_sum; intro k hk
    have K := KD_of E hs hk
    have hk0 := K.hk0; have hnk0 := K.hnk0
    have hc2 : Ob p 0 (cq p s k ^ 2 * ((k : ℚ_[p]) ^ 2)⁻¹) :=
      Ob_mul_unit (Ob_pow (Ob_cq0 s k) 2) (Ob_inv_U K.hkU 2)
    have hρ2 : Ob p ((s : ℤ) + 1) (rq p s k ^ 2 - 1) := by
      have := Ob_mul_unit K.hρ (Ob_add (Ob_rq0 s k) Ob_one)
      exact Ob_of_eq this (by ring)
    have hβ : Ob p 0 ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) := by
      rw [div_eq_mul_inv]; exact Ob_mul_unit (Ob_add (Ob_nonneg_to_zero (by omega) hnO) (Ob_natCast k)) K.hnkinv
    have hα : Ob p ((s : ℤ) + 1) (2 * nq p s / (nq p s - (k : ℚ_[p]))) := by
      rw [div_eq_mul_inv]; exact Ob_mul_unit (Ob_unit_mul Ob_two hnO) K.hnkinv
    have hβ1 : Ob p ((s : ℤ) + 1) (((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 - 1) := by
      have hid : ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 - 1 = 4 * nq p s * (k : ℚ_[p]) * ((nq p s - (k : ℚ_[p])) ^ 2)⁻¹ := by
        field_simp; ring
      rw [hid]
      have hnorm : ‖nq p s - (k : ℚ_[p])‖ = 1 := by
        have := norm_M_sub hM K.hkU; push_cast at this; exact this
      exact Ob_mul_unit (Ob_mul_unit (Ob_unit_mul (Ob_ofNat 4) hnO) (Ob_natCast k)) (Ob_inv_pow_of_norm_one hnorm 2)
    have t1 : Ob p ((s : ℤ) + 4) ((rq p s k ^ 2 - 1) * eps p (p * p ^ s) k ^ 2) := by
      have := Ob_mul hρ2 (Ob_pow K.hε 2); refine Ob_mono this ?_; omega
    have t2 : Ob p ((s : ℤ) + 4) (((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 * dq p s k ^ 2) := by
      have := Ob_unit_mul (Ob_pow hβ 2) (Ob_pow K.hδ 2); refine Ob_mono this ?_; omega
    have t3 : Ob p ((s : ℤ) + 4) (2 * (2 * nq p s / (nq p s - (k : ℚ_[p]))) * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) * dq p s k) := by
      have := Ob_mul (Ob_mul_unit (Ob_unit_mul Ob_two hα) hβ) K.hδ; refine Ob_mono this ?_; omega
    have t4 : Ob p ((s : ℤ) + 4) (2 * ((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 * mq p s k * dq p s k) := by
      have := Ob_mul (Ob_unit_mul (Ob_unit_mul Ob_two (Ob_pow hβ 2)) K.hμ) K.hδ; refine Ob_mono this ?_; omega
    have t5 : Ob p ((s : ℤ) + 4) ((((nq p s + (k : ℚ_[p])) / (nq p s - (k : ℚ_[p]))) ^ 2 - 1) * mq p s k ^ 2) := by
      have := Ob_mul hβ1 (Ob_pow K.hμ 2); refine Ob_mono this ?_; omega
    have t6 : Ob p ((s : ℤ) + 4) (4 * nq p s ^ 2 * (nq p s - 3 * (k : ℚ_[p])) * mq p s k * ((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]))⁻¹) := by
      have hu : Ob p 0 (((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]))⁻¹) := by
        rw [mul_inv]
        exact Ob_mul_unit (Ob_pow K.hnkinv 2 |> fun h => by simpa [inv_pow] using h) K.hkinv
      have hn3k : Ob p 0 (nq p s - 3 * (k : ℚ_[p])) :=
        Ob_sub (Ob_nonneg_to_zero (by omega) hnO) (Ob_unit_mul Ob_three (Ob_natCast k))
      have := Ob_mul_unit (Ob_mul (Ob_mul_unit (Ob_unit_mul (Ob_ofNat 4) (Ob_pow hnO 2)) hn3k) K.hμ) hu
      refine Ob_mono this ?_; omega
    have := Ob_unit_mul hc2 (Ob_add (Ob_add (Ob_add (Ob_sub (Ob_add t1 t2) t3) t4) t5) t6)
    refine Ob_mono this ?_; omega
  have hA : Ob p ((s : ℤ) + 3 + e) (∑ k ∈ U p ((p * p ^ s + 1) / 2),
      4 * nq p s ^ 2 * cq p s k ^ 2 * ((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]) ^ 2)⁻¹) := by
    rcases Nat.lt_or_ge 1 s with hs2 | hs1
    · apply Ob_sum; intro k hk
      have K := KD_of E hs hk
      have hu : Ob p 0 (((nq p s - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]) ^ 2)⁻¹) := by
        rw [mul_inv]
        exact Ob_mul_unit (Ob_pow K.hnkinv 2 |> fun h => by simpa [inv_pow] using h) (Ob_inv_U K.hkU 2)
      have := Ob_mul_unit (Ob_mul_unit (Ob_unit_mul (Ob_ofNat 4) (Ob_pow hnO 2)) (Ob_pow (Ob_cq0 s k) 2)) hu
      refine Ob_mono this ?_; push_cast; omega
    · have hs1' : s = 1 := by omega
      subst hs1'
      have h4 : Ob p 1 (∑ k ∈ U p ((p * p ^ 1 + 1) / 2), ((k : ℚ_[p]) ^ 4)⁻¹) := by
        rw [pow_one]; exact Ob_half_inv4 E
      have hn2 : Ob p 2 (nq p 1) := Ob_mono hnO (by norm_num)
      have hdec2 : ∀ k ∈ U p ((p * p ^ 1 + 1) / 2),
          4 * nq p 1 ^ 2 * cq p 1 k ^ 2 * ((nq p 1 - (k : ℚ_[p])) ^ 2 * (k : ℚ_[p]) ^ 2)⁻¹
            = 4 * nq p 1 ^ 2 * ((k : ℚ_[p]) ^ 4)⁻¹
              + 4 * nq p 1 ^ 2 * ((cq p 1 k ^ 2 - 1) * (k : ℚ_[p]) ^ 2 + nq p 1 * (2 * (k : ℚ_[p]) - nq p 1))
                * (((nq p 1 - (k : ℚ_[p])) ^ 2)⁻¹ * ((k : ℚ_[p]) ^ 4)⁻¹) := by
        intro k hk
        have K := KD_of E hs hk
        have hk0 := K.hk0; have hnk0 := K.hnk0
        field_simp; ring
      rw [Finset.sum_congr rfl hdec2, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine Ob_add ?_ ?_
      · have := Ob_mul (Ob_unit_mul (Ob_ofNat 4) (Ob_pow hn2 2)) h4
        refine Ob_mono this ?_; push_cast; omega
      · apply Ob_sum; intro k hk
        have K := KD_of E hs hk
        have hc2 : Ob p 1 (cq p 1 k ^ 2 - 1) := by
          have := Ob_mul_unit K.hcp (Ob_add (Ob_cq0 1 k) Ob_one)
          exact Ob_of_eq this (by ring)
        have hin : Ob p 1 ((cq p 1 k ^ 2 - 1) * (k : ℚ_[p]) ^ 2 + nq p 1 * (2 * (k : ℚ_[p]) - nq p 1)) :=
          Ob_add (Ob_mul_unit hc2 (Ob_pow (Ob_natCast k) 2))
            (Ob_mono (Ob_mul_unit hn2 (Ob_sub (Ob_unit_mul Ob_two (Ob_natCast k)) (Ob_nonneg_to_zero (by norm_num) hn2))) (by norm_num))
        have hu : Ob p 0 (((nq p 1 - (k : ℚ_[p])) ^ 2)⁻¹ * ((k : ℚ_[p]) ^ 4)⁻¹) :=
          Ob_mul_unit (Ob_pow K.hnkinv 2 |> fun h => by simpa [inv_pow] using h) (Ob_inv_U K.hkU 4)
        have := Ob_mul_unit (Ob_mul (Ob_unit_mul (Ob_ofNat 4) (Ob_pow hn2 2)) hin) hu
        refine Ob_mono this ?_; push_cast; omega
  have hB : Ob p ((s : ℤ) + 3 + e) (∑ k ∈ U p ((p * p ^ s + 1) / 2),
      (-4 * nq p s * cq p s k ^ 2 * mq p s k) * ((k : ℚ_[p]) ^ 3)⁻¹) := by
    rw [← sum_U_eq_half hM hodd _ (fun k hk => by rw [mq_reflect_zero hk]; ring)]
    unfold cq mq
    rw [sum_U_div (p ^ s) (fun k' => -4 * nq p s * (cc p (p ^ s) k') ^ 2 * mu p (p ^ s) k') 3]
    apply Ob_sum; intro k' _
    have := Ob_mul (Ob_mul (Ob_mul_unit (Ob_unit_mul (Ob_neg (Ob_ofNat 4)) hnO) (Ob_pow (Ob_cc (p ^ s) k') 2)) (Ob_mu hs k'))
      (Ob_Lam3 E.hp2 k')
    refine Ob_mono this ?_; omega
  have hMs : Ob p ((s : ℤ) + 3 + e) (∑ k ∈ U p ((p * p ^ s + 1) / 2),
      (cq p s k ^ 2 * mq p s k ^ 2) * ((k : ℚ_[p]) ^ 2)⁻¹) := by
    rw [← sum_U_eq_half hM hodd _ (fun k hk => by rw [mq_reflect_zero hk]; ring)]
    unfold cq mq
    rw [sum_U_div (p ^ s) (fun k' => (cc p (p ^ s) k') ^ 2 * mu p (p ^ s) k' ^ 2) 2]
    simp only [sum_Lam1]
    have := lemmaZ E hs (m := 1) le_rfl
    exact Ob_cast (by push_cast; ring) this
  have := Ob_mul (Ob_pow hnO 2) (Ob_add (Ob_add (Ob_add hR hA) hB) hMs)
  refine Ob_mono this ?_; push_cast; omega

/-- **U**: the non-multiples-of-`p` part -/
theorem Ob_Upart (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6) (∑ k ∈ U p ((p * p ^ s + 1) / 2), Uterm p (p * p ^ s) k) := by
  have he := E.he
  have hnO := Ob_nq (p := p) s
  have hdec : ∀ k ∈ U p ((p * p ^ s + 1) / 2),
      Uterm p (p * p ^ s) k = 3 * ((bb p (p * p ^ s) k) ^ 2 * eps p (p * p ^ s) k ^ 2)
        + 6 * ((bb p (p * p ^ s) k) ^ 3 * eps p (p * p ^ s) k)
        + (bb p (p * p ^ s) k) ^ 3 * eps p (p * p ^ s) k ^ 2 * (2 * eps p (p * p ^ s) k - 6) := by
    intro k _; unfold Uterm; ring
  rw [Finset.sum_congr rfl hdec, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  refine Ob_add (Ob_add ?_ ?_) ?_
  · have := Ob_mul E.h3 (Ob_Ub E hs)
    refine Ob_mono this ?_; omega
  · exact Ob_unit_mul (Ob_ofNat 6) (Ob_Ua E hs)
  · apply Ob_sum; intro k hk
    have K := KD_of E hs hk
    have hx : Ob p ((s : ℤ) + 1) (bb p (p * p ^ s) k) := by
      rw [K.hb, div_eq_mul_inv]
      exact Ob_mul_unit (Ob_mul_unit (Ob_mul_unit hnO K.hkinv) (Ob_cq0 s k)) (Ob_rq0 s k)
    have := Ob_mul_unit (Ob_mul (Ob_pow hx 3) (Ob_pow K.hε 2))
      (Ob_sub (Ob_unit_mul Ob_two (Ob_mono K.hε (by norm_num))) (Ob_ofNat 6))
    refine Ob_mono this ?_; omega

end A357565Proof

-- ===== Dev16 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

lemma U_succ_of_dvd {M : ℕ} (hM : p ∣ M) : U p (M + 1) = U p M := by
  ext i; simp only [mem_U]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases Nat.lt_or_ge i M with h | h
    · exact h
    · exfalso; have : i = M := by omega
      subst this; exact h2 hM
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma cc_self_descent (N : ℕ) : cc p (p * N) (p * N) = cc p N N * rho p 1 (p * N) (p * N) := by
  rw [cc_descent, Nat.mul_div_cancel_left N hp.out.pos]
  unfold rho; rw [U_succ_of_dvd (dvd_mul_right p N)]

lemma cc_two_descent (N : ℕ) : cc p (2 * (p * N)) (p * N) = cc p (2 * N) N * rho p 2 (p * N) (p * N) := by
  rw [show 2 * (p * N) = p * (2 * N) by ring, cc_descent, Nat.mul_div_cancel_left N hp.out.pos]
  unfold rho; rw [U_succ_of_dvd (dvd_mul_right p N)]
  congr 1
  apply Finset.prod_congr rfl; intro i _
  push_cast; ring

/-- product version of `sum_U_half` -/
lemma prod_U_half {M : ℕ} (hM : p ∣ M) (hodd : Odd M) (g : ℕ → ℚ_[p]) :
    ∏ i ∈ U p M, g i = ∏ i ∈ U p ((M+1)/2), (g i * g (M - i)) := by
  rw [Finset.prod_mul_distrib]
  have hsplit := Finset.prod_filter_mul_prod_filter_not (U p M) (fun i => 2 * i < M) g
  rw [← hsplit]
  have hset : (U p M).filter (fun i => 2 * i < M) = U p ((M+1)/2) := by
    ext i; simp only [Finset.mem_filter, mem_U]
    obtain ⟨t, ht⟩ := hodd
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩
  rw [hset]
  congr 1
  have key : ∀ i ∈ U p M, M - i ∈ U p M := U_reflect_mem hM
  obtain ⟨t, ht⟩ := hodd
  apply Finset.prod_nbij' (fun i => M - i) (fun i => M - i)
  · intro i hi
    simp only [Finset.mem_filter, mem_U] at hi ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hi
    refine ⟨by omega, ?_⟩
    have := key i (mem_U.2 ⟨h1, h2⟩)
    exact (mem_U.1 this).2
  · intro i hi
    have hpos := U_pos hi
    simp only [Finset.mem_filter, mem_U] at hi ⊢
    obtain ⟨h1, h2⟩ := hi
    have := key i (mem_U.2 ⟨by omega, h2⟩)
    exact ⟨⟨by omega, (mem_U.1 this).2⟩, by omega⟩
  · intro i hi; simp only [Finset.mem_filter, mem_U] at hi; omega
  · intro i hi; simp only [mem_U] at hi; omega
  · intro i hi; simp only [Finset.mem_filter, mem_U] at hi; rw [Nat.sub_sub_self hi.1.1.le]

/-- `ρ_{l,p^m}(p^m) - 1 = O(p⁴)` for `m ≥ 2` -/
lemma Ob_rho_pow_sub_one (E : EData p e) (l : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    Ob p 4 (rho p l (p ^ m) (p ^ m) - 1) := by
  have he := E.he
  have hM : Ob p m ((p ^ m : ℕ) : ℚ_[p]) := by push_cast; exact Ob_p_pow m
  have h1 := Ob_prod_sub_one_sub_sum (p := p) (U p (p ^ m)) (j := m)
    (x := fun i => (l : ℚ_[p]) * ((p ^ m : ℕ) : ℚ_[p]) / (i : ℚ_[p])) (by
      intro i hi
      exact Ob_of_eq (Ob_mul_unit (Ob_unit_mul (Ob_natCast l) hM) (Ob_inv_of_norm_one (norm_U hi))) (by ring))
  have e1 : ∑ i ∈ U p (p ^ m), (l : ℚ_[p]) * ((p ^ m : ℕ) : ℚ_[p]) / (i : ℚ_[p])
      = (l : ℚ_[p]) * ((p ^ m : ℕ) : ℚ_[p]) * Hs p 1 (p ^ m) := by
    unfold Hs; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [pow_one, div_eq_mul_inv]
  rw [e1] at h1
  have h2 : Ob p 4 ((l : ℚ_[p]) * ((p ^ m : ℕ) : ℚ_[p]) * Hs p 1 (p ^ m)) := by
    have := Ob_mul (Ob_unit_mul (Ob_natCast l) hM) (Ob_Hs1_pow_bound E (m := m) (by omega))
    refine Ob_mono this ?_; push_cast; omega
  have h3 : Ob p 4 (rho p l (p ^ m) (p ^ m) - 1 - (l : ℚ_[p]) * ((p ^ m : ℕ) : ℚ_[p]) * Hs p 1 (p ^ m)) := by
    unfold rho; refine Ob_mono h1 ?_; omega
  exact Ob_of_sub h3 h2

lemma Ob_cc_self_stable (E : EData p e) {s : ℕ} (hs : 1 ≤ s) : Ob p 4 (cc p (p ^ s) (p ^ s) - cc p p p) := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; simp only [zero_add, pow_one, sub_self]; exact Ob_zero 4
    · have ih' := ih h0
      have hd : cc p (p ^ (s + 1)) (p ^ (s + 1)) = cc p (p ^ s) (p ^ s) * rho p 1 (p ^ (s + 1)) (p ^ (s + 1)) := by
        rw [pow_succ', cc_self_descent]
      rw [hd]
      have := Ob_add (Ob_mul_unit (Ob_rho_pow_sub_one E 1 (m := s + 1) (by omega)) (Ob_cc (p ^ s) (p ^ s))) ih'
      exact Ob_of_eq this (by ring)

lemma Ob_cc_two_stable (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p 4 (cc p (2 * p ^ s) (p ^ s) - cc p (2 * p) p) := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; simp only [zero_add, pow_one, sub_self]; exact Ob_zero 4
    · have ih' := ih h0
      have hd : cc p (2 * p ^ (s + 1)) (p ^ (s + 1)) = cc p (2 * p ^ s) (p ^ s) * rho p 2 (p ^ (s + 1)) (p ^ (s + 1)) := by
        rw [pow_succ', cc_two_descent]
      rw [hd]
      have := Ob_add (Ob_mul_unit (Ob_rho_pow_sub_one E 2 (m := s + 1) (by omega)) (Ob_cc (2 * p ^ s) (p ^ s))) ih'
      exact Ob_of_eq this (by ring)

/-- `ρ_{l,p}(p) - 1 = O(p^{2+e})` -/
lemma Ob_rho_p_sub_one (E : EData p e) (l : ℕ) : Ob p (2 + (e : ℤ)) (rho p l p p - 1) := by
  have he := E.he
  have h := rho_second_order (p := p) l (M := p) (m := p) (j := 1) Ob_p
  have hH1 : Ob p (1 + (e : ℤ)) (Hs p 1 p) := by
    have := Ob_Hs1_pow_bound E (m := 1) le_rfl
    rw [pow_one] at this; refine Ob_mono this ?_; omega
  have t1 : Ob p (2 + (e : ℤ)) ((l : ℚ_[p]) * (p : ℚ_[p]) * Hs p 1 p) := by
    have := Ob_mul (Ob_unit_mul (Ob_natCast l) Ob_p) hH1; refine Ob_mono this ?_; omega
  have t2 : Ob p (2 + (e : ℤ)) (((l : ℚ_[p]) * (p : ℚ_[p])) ^ 2 * Hs p 2 p) := by
    have := Ob_mul (Ob_pow (Ob_unit_mul (Ob_natCast l) Ob_p) 2) E.hh; refine Ob_mono this ?_; push_cast; omega
  have t3 : Ob p (2 + (e : ℤ)) (((l : ℚ_[p]) * (p : ℚ_[p]) * Hs p 1 p) ^ 2) := by
    have := Ob_pow t1 2; refine Ob_mono this ?_; omega
  have h' : Ob p (2 + (e : ℤ)) (2 * (rho p l p p - 1 - (l : ℚ_[p]) * (p : ℚ_[p]) * Hs p 1 p)
      - (((l : ℚ_[p]) * (p : ℚ_[p]) * Hs p 1 p) ^ 2 - ((l : ℚ_[p]) * (p : ℚ_[p])) ^ 2 * Hs p 2 p)) :=
    Ob_mono h (by omega)
  have key : Ob p (2 + (e : ℤ)) (2 * (rho p l p p - 1)) := by
    have := Ob_add (Ob_add h' (Ob_unit_mul Ob_two t1)) (Ob_sub t3 t2)
    exact Ob_of_eq this (by ring)
  have := Ob_unit_mul (Ob_inv_two E.hp2) key
  exact Ob_of_eq this (by field_simp)

lemma cc_p_p : cc p p p = 2 * rho p 1 p p := by
  have := cc_self_descent (p := p) 1
  rw [mul_one] at this; rw [this]; unfold cc; norm_num

lemma cc_2p_p : cc p (2 * p) p = 3 * rho p 2 p p := by
  have := cc_two_descent (p := p) 1
  rw [mul_one] at this; rw [this]; unfold cc; norm_num

lemma p_eq_three_of_e_zero (E : EData p e) (he0 : e = 0) : p = 3 := by
  have h3 := E.h3
  rw [he0] at h3
  have : ‖((3 : ℕ) : ℚ_[p])‖ < 1 := by
    have h := h3; unfold Ob at h
    push_cast
    calc ‖(3 : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(1 - ((0 : ℕ) : ℤ))) := h
      _ < 1 := by
        simp only [Nat.cast_zero, sub_zero]
        rw [zpow_neg, zpow_one]
        exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hdvd : p ∣ 3 := Padic.norm_natCast_lt_one_iff.1 this
  exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 hdvd

/-- `K(C') - 6 C₃ = O(p^{4-e})` at level `p` -/
lemma Ob_K_level_p (E : EData p e) :
    Ob p (4 - (e : ℤ)) (3 * cc p p p + 3 / 2 * (cc p p p) ^ 2 + 3 / 4 * (cc p p p) ^ 3 - 6 * cc p (2 * p) p) := by
  have he := E.he
  rcases Nat.eq_zero_or_pos e with he0 | he1
  · have hp3 := p_eq_three_of_e_zero E he0
    subst hp3
    have h1 : cc 3 3 3 = 20 := by unfold cc; norm_num [Nat.choose]
    have h2 : cc 3 (2 * 3) 3 = 84 := by unfold cc; norm_num [Nat.choose]
    rw [h1, h2, he0]
    have : (3 : ℚ_[3]) * 20 + 3 / 2 * 20 ^ 2 + 3 / 4 * 20 ^ 3 - 6 * 84 = ((3 : ℕ) : ℚ_[3]) ^ 4 * 76 := by
      push_cast; norm_num
    rw [this]
    exact Ob_cast (by norm_num) (Ob_p_pow_mul (p := 3) 4 (Ob_ofNat 76))
  · have he1' : e = 1 := by omega
    subst he1'
    rw [cc_p_p, cc_2p_p]
    have hr1 : Ob p 3 (rho p 1 p p - 1) := Ob_mono (Ob_rho_p_sub_one E 1) (by norm_num)
    have hr2 : Ob p 3 (rho p 2 p p - 1) := Ob_mono (Ob_rho_p_sub_one E 2) (by norm_num)
    have hr1O : Ob p 0 (rho p 1 p p) := Ob_rho
    have key : 3 * (2 * rho p 1 p p) + 3 / 2 * (2 * rho p 1 p p) ^ 2 + 3 / 4 * (2 * rho p 1 p p) ^ 3
        - 6 * (3 * rho p 2 p p)
        = (rho p 1 p p - 1) * (6 + 6 * (rho p 1 p p + 1) + 6 * (rho p 1 p p ^ 2 + rho p 1 p p + 1))
          - 18 * (rho p 2 p p - 1) := by ring
    rw [key]
    have h1 : Ob p 3 ((rho p 1 p p - 1) * (6 + 6 * (rho p 1 p p + 1) + 6 * (rho p 1 p p ^ 2 + rho p 1 p p + 1))) :=
      Ob_mul_unit hr1 (Ob_add (Ob_add (Ob_ofNat 6) (Ob_unit_mul (Ob_ofNat 6) (Ob_add hr1O Ob_one)))
        (Ob_unit_mul (Ob_ofNat 6) (Ob_add (Ob_add (Ob_pow hr1O 2) hr1O) Ob_one)))
    have h2 : Ob p 3 (18 * (rho p 2 p p - 1)) := Ob_unit_mul (Ob_ofNat 18) hr2
    exact Ob_cast (by norm_num) (Ob_sub h1 h2)

/-- `K(C'(N)) - 6 C₃(N) = O(p^{4-e})`, `N = p^s` -/
lemma Ob_K (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (4 - (e : ℤ)) (3 * cc p (p ^ s) (p ^ s) + 3 / 2 * (cc p (p ^ s) (p ^ s)) ^ 2
      + 3 / 4 * (cc p (p ^ s) (p ^ s)) ^ 3 - 6 * cc p (2 * p ^ s) (p ^ s)) := by
  have he := E.he
  have h1 := Ob_cc_self_stable E hs
  have h2 := Ob_cc_two_stable E hs
  have h0 := Ob_K_level_p E
  set C := cc p (p ^ s) (p ^ s)
  set C₁ := cc p p p
  set D := cc p (2 * p ^ s) (p ^ s)
  set D₁ := cc p (2 * p) p
  have hC : Ob p 0 C := Ob_cc _ _
  have hC₁ : Ob p 0 C₁ := Ob_cc _ _
  have h4 : Ob p 0 ((1 : ℚ_[p]) / 4) := by
    rw [one_div, show (4 : ℚ_[p]) = 2 ^ 2 by norm_num, ← inv_pow]
    exact Ob_cast (by norm_num) (Ob_pow (Ob_inv_two E.hp2) 2)
  have h2' : Ob p 0 ((1 : ℚ_[p]) / 2) := by rw [one_div]; exact Ob_inv_two E.hp2
  have key : 3 * C + 3 / 2 * C ^ 2 + 3 / 4 * C ^ 3 - 6 * D
      = (3 * C₁ + 3 / 2 * C₁ ^ 2 + 3 / 4 * C₁ ^ 3 - 6 * D₁)
        + (C - C₁) * (3 + 3 * (1 / 2) * (C + C₁) + 3 * (1 / 4) * (C ^ 2 + C * C₁ + C₁ ^ 2)) - 6 * (D - D₁) := by
    ring
  rw [key]
  have hpoly : Ob p 0 (3 + 3 * (1 / 2) * (C + C₁) + 3 * (1 / 4) * (C ^ 2 + C * C₁ + C₁ ^ 2)) :=
    Ob_add (Ob_add Ob_three (Ob_unit_mul (Ob_unit_mul Ob_three h2') (Ob_add hC hC₁)))
      (Ob_unit_mul (Ob_unit_mul Ob_three h4) (Ob_add (Ob_add (Ob_pow hC 2) (Ob_mul hC hC₁)) (Ob_pow hC₁ 2)))
  refine Ob_sub (Ob_add h0 ?_) ?_
  · refine Ob_mono (Ob_mul_unit h1 hpoly) ?_; omega
  · refine Ob_mono (Ob_unit_mul (Ob_ofNat 6) h2) ?_; omega

/-- `a = ρ_{1,n}(n) - 1 = O(p^{3s+2+e})` -/
lemma Ob_a (E : EData p e) (s : ℕ) : Ob p (3 * (s : ℤ) + 2 + e) (rho p 1 (p * p ^ s) (p * p ^ s) - 1) := by
  have := Ob_rho_top E (s := s) (v := s) le_rfl 1
  rw [mul_one, pow_succ'] at this
  exact Ob_cast (by ring) this

end A357565Proof

-- ===== Dev17 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

/-- `w_i = n²/(i(n-i))` -/
noncomputable def ww (p : ℕ) [Fact p.Prime] (s i : ℕ) : ℚ_[p] :=
  nq p s ^ 2 / ((i : ℚ_[p]) * (nq p s - (i : ℚ_[p])))

lemma rho_pair (E : EData p e) {s : ℕ} (hs : 1 ≤ s) (l : ℕ) :
    rho p l (p * p ^ s) (p * p ^ s)
      = ∏ i ∈ U p ((p * p ^ s + 1) / 2), (1 + ((l : ℚ_[p]) * ((l : ℚ_[p]) + 1)) * ww p s i) := by
  have hodd := odd_n_of_EData E s
  have hM : p ∣ p * p ^ s := dvd_mul_right _ _
  unfold rho
  rw [prod_U_half hM hodd]
  apply Finset.prod_congr rfl; intro i hi
  have K := KD_of E hs hi
  have hk0 := K.hk0; have hnk0 := K.hnk0
  have hile : i ≤ p * p ^ s := (mem_U.1 K.hkU).1.le
  unfold ww nq at hnk0 ⊢
  push_cast [Nat.cast_sub hile]
  field_simp; ring

lemma Ob_ww (E : EData p e) {s : ℕ} (hs : 1 ≤ s) {i : ℕ} (hi : i ∈ U p ((p * p ^ s + 1) / 2)) :
    Ob p (2 * (s : ℤ) + 2) (ww p s i) := by
  have K := KD_of E hs hi
  unfold ww
  rw [div_eq_mul_inv, mul_inv]
  have := Ob_mul_unit (Ob_pow (Ob_nq (p := p) s) 2) (Ob_mul_unit K.hkinv K.hnkinv)
  exact Ob_cast (by ring) this

lemma sum_ww (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    ∑ i ∈ U p ((p * p ^ s + 1) / 2), ww p s i = nq p s * Hs p 1 (p * p ^ s) := by
  have hodd := odd_n_of_EData E s
  have hM : p ∣ p * p ^ s := dvd_mul_right _ _
  unfold Hs
  rw [sum_U_half hM hodd, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  have K := KD_of E hs hi
  have hk0 := K.hk0; have hnk0 := K.hnk0
  have hile : i ≤ p * p ^ s := (mem_U.1 K.hkU).1.le
  unfold ww nq at hnk0 ⊢
  push_cast [Nat.cast_sub hile]
  field_simp; ring

lemma Ob_W1 (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 2 + e) (∑ i ∈ U p ((p * p ^ s + 1) / 2), ww p s i) := by
  rw [sum_ww E hs]
  have h := Ob_Hs1_pow_bound E (m := s + 1) (by omega)
  rw [pow_succ'] at h
  have := Ob_mul (Ob_nq (p := p) s) h
  exact Ob_cast (by push_cast; ring) this

lemma Ob_W2 (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6) (12 * ∑ i ∈ U p ((p * p ^ s + 1) / 2), ww p s i ^ 2) := by
  have he := E.he
  rcases Nat.lt_or_ge 1 s with hs2 | hs1
  · rw [Finset.mul_sum]; apply Ob_sum; intro i hi
    have := Ob_unit_mul (Ob_ofNat 12) (Ob_pow (Ob_ww E hs hi) 2)
    refine Ob_mono this ?_; omega
  · have hs1' : s = 1 := by omega
    subst hs1'
    have hnO : Ob p 2 (nq p 1) := Ob_mono (Ob_nq (p := p) 1) (by norm_num)
    have hM : p ∣ p * p ^ 1 := dvd_mul_right _ _
    have h4 : Ob p 1 (∑ k ∈ U p ((p * p ^ 1 + 1) / 2), ((k : ℚ_[p]) ^ 4)⁻¹) := by
      rw [pow_one]; exact Ob_half_inv4 E
    have hdec : ∀ i ∈ U p ((p * p ^ 1 + 1) / 2),
        ww p 1 i ^ 2 = nq p 1 ^ 4 * (((i : ℚ_[p]) ^ 4)⁻¹
          + ((i : ℚ_[p]) ^ 2)⁻¹ * (((-(i : ℚ_[p]) + nq p 1) ^ 2)⁻¹ - ((-(i : ℚ_[p])) ^ 2)⁻¹)) := by
      intro i hi
      have K := KD_of E le_rfl hi
      have hk0 := K.hk0; have hnk0 := K.hnk0
      have hnk0' : -(i : ℚ_[p]) + nq p 1 ≠ 0 := by rw [add_comm, ← sub_eq_add_neg]; exact hnk0
      unfold ww
      field_simp; ring
    rw [Finset.sum_congr rfl hdec, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsum2 : Ob p 1 (∑ i ∈ U p ((p * p ^ 1 + 1) / 2),
        ((i : ℚ_[p]) ^ 2)⁻¹ * (((-(i : ℚ_[p]) + nq p 1) ^ 2)⁻¹ - ((-(i : ℚ_[p])) ^ 2)⁻¹)) := by
      apply Ob_sum; intro i hi
      have K := KD_of E le_rfl hi
      have hn : ‖(-(i : ℚ_[p]))‖ = 1 := by rw [norm_neg]; exact norm_U K.hkU
      have hnx : ‖-(i : ℚ_[p]) + nq p 1‖ = 1 := by
        rw [add_comm, ← sub_eq_add_neg]
        have := norm_M_sub hM K.hkU; push_cast at this; exact this
      have := Ob_unit_mul (Ob_inv_U K.hkU 2) (Ob_inv_pow_sub hn hnx hnO 2)
      refine Ob_mono this ?_; norm_num
    have h12 : Ob p (1 - (e : ℤ)) (12 : ℚ_[p]) := by
      have := Ob_mul_unit E.h3 (Ob_ofNat 4); exact Ob_of_eq this (by norm_num)
    have := Ob_mul (Ob_mul h12 (Ob_pow hnO 4)) (Ob_add h4 hsum2)
    refine Ob_of_eq (Ob_mono this ?_) ?_
    · push_cast; omega
    · ring

/-- `b - 3a = O(p^{3s+6})` -/
lemma Ob_b3a (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6)
      (rho p 2 (p * p ^ s) (p * p ^ s) - 1 - 3 * (rho p 1 (p * p ^ s) (p * p ^ s) - 1)) := by
  have he := E.he
  have hp1 := rho_pair E hs 1
  have hp2 := rho_pair E hs 2
  push_cast at hp1 hp2
  rw [show ((1 : ℚ_[p]) * (1 + 1)) = 2 by norm_num] at hp1
  rw [show ((2 : ℚ_[p]) * (2 + 1)) = 6 by norm_num] at hp2
  have hw : ∀ i ∈ U p ((p * p ^ s + 1) / 2), Ob p (2 * s + 2) (ww p s i) := fun i hi => by
    have := Ob_ww E hs hi; exact Ob_cast (by push_cast; ring) this
  have SO₁ := Ob_prod_second_order (p := p) (U p ((p * p ^ s + 1) / 2)) (j := 2 * s + 2)
    (x := fun i => 2 * ww p s i) (fun i hi => Ob_unit_mul Ob_two (hw i hi))
  have SO₂ := Ob_prod_second_order (p := p) (U p ((p * p ^ s + 1) / 2)) (j := 2 * s + 2)
    (x := fun i => 6 * ww p s i) (fun i hi => Ob_unit_mul (Ob_ofNat 6) (hw i hi))
  simp only [mul_pow, ← Finset.mul_sum] at SO₁ SO₂
  rw [← hp1] at SO₁
  rw [← hp2] at SO₂
  set W₁ := ∑ i ∈ U p ((p * p ^ s + 1) / 2), ww p s i with hW₁
  set W₂ := ∑ i ∈ U p ((p * p ^ s + 1) / 2), ww p s i ^ 2 with hW₂
  have hW1 := Ob_W1 E hs
  have hW2 := Ob_W2 E hs
  rw [← hW₁] at hW1
  rw [← hW₂] at hW2
  have hW1sq : Ob p (3 * (s : ℤ) + 6) (12 * W₁ ^ 2) := by
    have := Ob_unit_mul (Ob_ofNat 12) (Ob_pow hW1 2)
    refine Ob_mono this ?_; omega
  have SO₁' : Ob p (3 * (s : ℤ) + 6) _ := Ob_mono SO₁ (by push_cast; omega)
  have SO₂' : Ob p (3 * (s : ℤ) + 6) _ := Ob_mono SO₂ (by push_cast; omega)
  have := Ob_sub (Ob_add (Ob_unit_mul (Ob_inv_two E.hp2) (Ob_sub SO₂' (Ob_unit_mul Ob_three SO₁'))) hW1sq) hW2
  refine Ob_of_eq this ?_
  field_simp; ring

/-- **ΔBnd**: `Bnd(pN) - Bnd(N) = O(p^{3s+6})` -/
theorem Ob_Bnd (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6) (Bnd p (p * p ^ s) - Bnd p (p ^ s)) := by
  have he := E.he
  unfold Bnd
  rw [cc_self_descent, cc_two_descent]
  set C := cc p (p ^ s) (p ^ s)
  set D := cc p (2 * p ^ s) (p ^ s)
  set ρ₁ := rho p 1 (p * p ^ s) (p * p ^ s)
  set ρ₂ := rho p 2 (p * p ^ s) (p * p ^ s)
  have ha := Ob_a E s
  have hb3a := Ob_b3a E hs
  have hK := Ob_K E hs
  have hC : Ob p 0 C := Ob_cc _ _
  have hD : Ob p 0 D := Ob_cc _ _
  have h2' : Ob p 0 ((1 : ℚ_[p]) / 2) := by rw [one_div]; exact Ob_inv_two E.hp2
  have key : 5 + ff (C * ρ₁ / 2) + 3 * (C * ρ₁) - 2 * (D * ρ₂) - (5 + ff (C / 2) + 3 * C - 2 * D)
      = (ρ₁ - 1) * (3 * C + 3 / 2 * C ^ 2 + 3 / 4 * C ^ 3 - 6 * D)
        - 2 * D * (ρ₂ - 1 - 3 * (ρ₁ - 1))
        + (ρ₁ - 1) ^ 2 * (3 * (C * (1 / 2)) ^ 2 + 6 * (C * (1 / 2)) ^ 3)
        + 2 * (C * (1 / 2)) ^ 3 * (ρ₁ - 1) ^ 3 := by
    unfold ff; ring
  rw [key]
  have hx : Ob p 0 (C * (1 / 2)) := Ob_mul_unit hC h2'
  have t1 : Ob p (3 * (s : ℤ) + 6) ((ρ₁ - 1) * (3 * C + 3 / 2 * C ^ 2 + 3 / 4 * C ^ 3 - 6 * D)) := by
    have := Ob_mul ha hK; refine Ob_mono this ?_; omega
  have t2 : Ob p (3 * (s : ℤ) + 6) (2 * D * (ρ₂ - 1 - 3 * (ρ₁ - 1))) :=
    Ob_unit_mul (Ob_unit_mul Ob_two hD) hb3a
  have t3 : Ob p (3 * (s : ℤ) + 6) ((ρ₁ - 1) ^ 2 * (3 * (C * (1 / 2)) ^ 2 + 6 * (C * (1 / 2)) ^ 3)) := by
    have := Ob_mul_unit (Ob_pow ha 2)
      (Ob_add (Ob_unit_mul Ob_three (Ob_pow hx 2)) (Ob_unit_mul (Ob_ofNat 6) (Ob_pow hx 3)))
    refine Ob_mono this ?_; omega
  have t4 : Ob p (3 * (s : ℤ) + 6) (2 * (C * (1 / 2)) ^ 3 * (ρ₁ - 1) ^ 3) := by
    have := Ob_unit_mul (Ob_unit_mul Ob_two (Ob_pow hx 3)) (Ob_pow ha 3)
    refine Ob_mono this ?_; omega
  exact Ob_add (Ob_add (Ob_sub t1 t2) t3) t4

end A357565Proof

-- ===== Dev18 =====


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace A357565Proof
open Finset

variable {p : ℕ} [hp : Fact p.Prime] {e : ℕ}

theorem Ob_aa_diff (E : EData p e) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6) (aa p (p * p ^ s) - aa p (p ^ s)) := by
  rw [aa_diff (pow_pos hp.out.pos s) (odd_n_of_EData E s)]
  exact Ob_add (Ob_add (Ob_Bnd E hs) (Ob_Upart E hs)) (Ob_Mt E hs)

theorem Ob_aa_diff' (h3 : 3 ≤ p) {s : ℕ} (hs : 1 ≤ s) :
    Ob p (3 * (s : ℤ) + 6) (aa p (p * p ^ s) - aa p (p ^ s)) := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · have hp3 : p = 3 := by
      have := hp.out
      interval_cases p
      · rfl
      · norm_num at this
    exact Ob_aa_diff (EData_three hp3) hs
  · exact Ob_aa_diff (EData_ge5 h5) hs

end A357565Proof


open Finset Nat

/--
A357565: $a(n) = 3 \sum_{k = 0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n \binom{n+k-1}{k}^3$.
-/
def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^3$.
Note that $A357565(n) = A357565\_u(n, 1)$.
-/
def A357565_u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

namespace A357565Proof

variable {p : ℕ} [hp : Fact p.Prime]

lemma A357565_cast (M : ℕ) : ((A357565 M : ℕ) : ℚ_[p]) = aa p M := by
  unfold A357565 aa ff bb
  push_cast
  rfl

theorem main_nat (h3 : 3 ≤ p) {s : ℕ} (hs : 1 ≤ s) :
    A357565 (p ^ (s + 1)) ≡ A357565 (p ^ s) [MOD p ^ (3 * s + 6)] := by
  have h := Ob_aa_diff' h3 hs
  rw [← A357565_cast, ← A357565_cast] at h
  have h' : Ob p ((3 * s + 6 : ℕ) : ℤ)
      ((((A357565 (p * p ^ s) : ℕ) : ℤ) - ((A357565 (p ^ s) : ℕ) : ℤ) : ℤ) : ℚ_[p]) := by
    push_cast; exact h
  have hd : ((p : ℤ) ^ (3 * s + 6)) ∣ (((A357565 (p * p ^ s) : ℕ) : ℤ) - ((A357565 (p ^ s) : ℕ) : ℤ)) :=
    (Padic.norm_int_le_pow_iff_dvd _ _).1 h'
  rw [show p ^ (s + 1) = p * p ^ s from pow_succ' p s]
  rw [Nat.modEq_iff_dvd]
  push_cast
  rw [← neg_sub]
  exact dvd_neg.2 hd

end A357565Proof

-- Formalizing Conjecture 2
/--
Conjecture 2 for A357565: $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$.
-/
theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have := A357565Proof.main_nat (p := p) h_pge3 (s := s) (by omega)
  simpa [show 3 * (s + 1) + 3 = 3 * s + 6 by ring] using this

theorem A357565_conjecture_2.disproof : ¬ (type_of% @A357565_conjecture_2) := sorry
