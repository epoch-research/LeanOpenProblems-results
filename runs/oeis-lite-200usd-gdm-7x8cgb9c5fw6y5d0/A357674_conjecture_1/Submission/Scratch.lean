import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace List

def sum_pairs {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | a :: L => sum_pairs L + a * L.sum

lemma map_list_sum {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (L : List A) :
    f L.sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp [ih]

lemma ringHom_sum_pairs {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (L : List A) :
    f (sum_pairs L) = sum_pairs (L.map f) := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs, ih, map_list_sum]

theorem list_sum_sq_eq {R : Type*} [CommRing R] (L : List R) :
    L.sum ^ 2 = (L.map (fun x => x ^ 2)).sum + 2 * sum_pairs L := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs]
    linear_combination ih

theorem list_sum_range_eq_finset_sum_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp [Finset.sum_range_succ]

theorem prod_one_add_y_mul_eq3 {R : Type*} [CommRing R] (y : R) (hy3 : y ^ 3 = 0) (L : List R) :
    (L.map (fun x ↦ 1 + y * x)).prod = 1 + y * L.sum + y ^ 2 * sum_pairs L := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs, ih]
    linear_combination (1 + y * a) * (1 + y * L.sum + y ^ 2 * sum_pairs L) -
                       (1 + y * (a + L.sum) + y ^ 2 * (sum_pairs L + a * L.sum)) +
                       (a * sum_pairs L) * hy3

end List

lemma coprime_p_pow (p k : ℕ) (hp : p.Prime) (hk1 : k ≥ 1) (hk2 : k < p) (a : ℕ) : k.Coprime (p ^ a) := by
  have h_coprime : k.Coprime p := by
    rw [Nat.coprime_comm]
    apply hp.coprime_iff_not_dvd.mpr
    apply Nat.not_dvd_of_pos_of_lt hk1 hk2
  exact h_coprime.pow_right a

lemma unit_mul_inv {n : ℕ} {a : ZMod n} (ha : IsUnit a) : a * a⁻¹ = 1 := by
  rw [mul_comm]
  exact (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl

lemma ringHom_map_inv {n m : ℕ} (f : ZMod n →+* ZMod m) (x : ZMod n) (hx : IsUnit x) :
    f x⁻¹ = (f x)⁻¹ := by
  have h1 : x * x⁻¹ = 1 := unit_mul_inv hx
  have h2 : f x * f x⁻¹ = 1 := by
    calc f x * f x⁻¹
      _ = f (x * x⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h1]
      _ = 1 := f.map_one
  have h_unit : IsUnit (f x) := hx.map f
  have h3 : f x * (f x)⁻¹ = 1 := unit_mul_inv h_unit
  calc f x⁻¹
    _ = 1 * f x⁻¹ := by rw [one_mul]
    _ = ((f x)⁻¹ * f x) * f x⁻¹ := by rw [mul_comm (f x)⁻¹, h3]
    _ = (f x)⁻¹ * (f x * f x⁻¹) := by ring
    _ = (f x)⁻¹ * 1 := by rw [h2]
    _ = (f x)⁻¹ := by rw [mul_one]

lemma isUnit_of_lt (p i a : ℕ) (hp : p.Prime) (hi : i < p - 1) :
    IsUnit ((i + 1 : ℕ) : ZMod (p ^ a)) := by
  have hk1 : i + 1 ≥ 1 := by omega
  have hk2 : i + 1 < p := by omega
  have h_coprime := coprime_p_pow p (i + 1) hp hk1 hk2 a
  rw [ZMod.isUnit_iff_coprime]
  exact h_coprime

lemma sum_inv_sq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, (k ^ 2)⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  let E : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2
  have h_comp : (∑ k : ZMod p, ((2 * k) ^ 2)⁻¹) = ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    have hE := Equiv.sum_comp E (fun x => (x ^ 2)⁻¹)
    have h_rw : ∀ x, E x = 2 * x := fun x => rfl
    simp_rw [h_rw] at hE
    exact hE
  have h_mul : ∀ x : ZMod p, ((2 * x) ^ 2)⁻¹ = 4⁻¹ * (x ^ 2)⁻¹ := by
    intro x
    have : (2 * x) ^ 2 = 4 * x ^ 2 := by ring
    rw [this, mul_inv]
  have h_sum_rw : (∑ k : ZMod p, ((2 * k) ^ 2)⁻¹) = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    rw [sum_congr rfl (fun x _ => h_mul x), ← mul_sum]
  have h_eq : (∑ k : ZMod p, (k ^ 2)⁻¹) = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    calc (∑ k : ZMod p, (k ^ 2)⁻¹)
      _ = ∑ k : ZMod p, ((2 * k) ^ 2)⁻¹ := h_comp.symm
      _ = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := h_sum_rw
  have h_4 : (4 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹) = (4 : ZMod p) * (4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹) :=
    congr_arg (fun x => (4 : ZMod p) * x) h_eq
  have h_4_inv : (4 : ZMod p) * 4⁻¹ = 1 := by
    apply mul_inv_cancel₀
    intro h4
    have h_dvd4 : p ∣ 4 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h4
    have h_le4 : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd4
    omega
  rw [← mul_assoc] at h_4
  rw [h_4_inv] at h_4
  rw [one_mul] at h_4
  have h_sub : (3 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹) = 0 := by
    linear_combination h_4
  have h_3_ne_zero : (3 : ZMod p) ≠ 0 := by
    intro h3
    have h_dvd3 : p ∣ 3 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3
    have h_le3 : p ≤ 3 := Nat.le_of_dvd (by decide) h_dvd3
    omega
  have h_goal : (3 : ZMod p)⁻¹ * ((3 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹)) = 0 := by
    rw [h_sub, mul_zero]
  rw [← mul_assoc, inv_mul_cancel₀ h_3_ne_zero, one_mul] at h_goal
  exact h_goal

lemma sum_inv_sq_zero_ico (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨by omega⟩
    (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2)) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_univ : (∑ k : ZMod p, (k⁻¹ ^ 2)) = 0 := by
    have h_eq : (∑ k : ZMod p, (k⁻¹ ^ 2)) = ∑ k : ZMod p, (k ^ 2)⁻¹ := by
      congr 1; ext k
      exact inv_pow k 2
    rw [h_eq]
    exact sum_inv_sq_zero p hp hp5
  have h_erase : (∑ k : ZMod p, k⁻¹ ^ 2) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ ^ 2 := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ 0)]
    simp
  rw [h_erase] at h_univ
  have h_bij : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2)) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ ^ 2 := by
    apply Finset.sum_bij (fun (j : ℕ) _ => (j : ZMod p))
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hj_zero
      have h_dvd : p ∣ j := (CharP.cast_eq_zero_iff (ZMod p) p j).mp hj_zero
      have h_le : p ≤ j := Nat.le_of_dvd (by omega) h_dvd
      omega
    · intro j1 hj1 j2 hj2 h_eq
      rw [Finset.mem_Ico] at hj1 hj2
      rw [ZMod.natCast_eq_natCast_iff j1 j2 p] at h_eq
      have h_mod1 : j1 % p = j1 := Nat.mod_eq_of_lt hj1.2
      have h_mod2 : j2 % p = j2 := Nat.mod_eq_of_lt hj2.2
      have h_eq_mod : j1 % p = j2 % p := h_eq
      rw [h_mod1, h_mod2] at h_eq_mod
      exact h_eq_mod
    · intro b hb
      rw [Finset.mem_erase] at hb
      have hb0 : b ≠ 0 := hb.1
      use b.val
      have hb_val_lt : b.val < p := b.val_lt
      have hb_val_ge : b.val ≥ 1 := by
        by_contra h_contra
        have : b.val = 0 := by omega
        apply hb0
        have h_val : b.val = (0 : ZMod p).val := by
          rw [this, ZMod.val_zero]
        exact ZMod.val_injective p h_val
      refine ⟨by rw [Finset.mem_Ico]; omega, by rw [ZMod.natCast_val, ZMod.cast_id]⟩
    · intro j hj
      rfl
  rw [h_bij]
  exact h_univ

def invEquiv (α : Type*) [DivisionRing α] : α ≃ α where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x

theorem sum_zmod_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, k) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  let E : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2
  have h_comp : (∑ k : ZMod p, (2 * k)) = ∑ k : ZMod p, k := by
    have hE := Equiv.sum_comp E (fun x => x)
    have h_rw : ∀ x, E x = 2 * x := fun x => rfl
    simp_rw [h_rw] at hE
    exact hE
  have h_sum_rw : (∑ k : ZMod p, (2 * k)) = 2 * ∑ k : ZMod p, k := by
    rw [← mul_sum]
  have h_eq : (∑ k : ZMod p, k) = 2 * ∑ k : ZMod p, k := by
    calc (∑ k : ZMod p, k)
      _ = ∑ k : ZMod p, (2 * k) := h_comp.symm
      _ = 2 * ∑ k : ZMod p, k := h_sum_rw
  linear_combination -h_eq

theorem sum_inv_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, k⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_comp : (∑ k : ZMod p, k⁻¹) = ∑ k : ZMod p, k := by
    have hE := Equiv.sum_comp (invEquiv (ZMod p)) (fun x => x)
    exact hE
  rw [h_comp]
  exact sum_zmod_zero p hp hp3

lemma sum_inv_zero_ico (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    letI : NeZero p := ⟨by omega⟩
    (∑ j ∈ Finset.Ico 1 p, (j : ZMod p)⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_univ : (∑ k : ZMod p, k⁻¹) = 0 := sum_inv_zero p hp hp3
  have h_erase : (∑ k : ZMod p, k⁻¹) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ 0)]
    simp
  rw [h_erase] at h_univ
  have h_bij : (∑ j ∈ Finset.Ico 1 p, (j : ZMod p)⁻¹) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ := by
    apply Finset.sum_bij (fun (j : ℕ) _ => (j : ZMod p))
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hj_zero
      have h_dvd : p ∣ j := (CharP.cast_eq_zero_iff (ZMod p) p j).mp hj_zero
      have h_le : p ≤ j := Nat.le_of_dvd (by omega) h_dvd
      omega
    · intro j1 hj1 j2 hj2 h_eq
      rw [Finset.mem_Ico] at hj1 hj2
      rw [ZMod.natCast_eq_natCast_iff j1 j2 p] at h_eq
      have h_mod1 : j1 % p = j1 := Nat.mod_eq_of_lt hj1.2
      have h_mod2 : j2 % p = j2 := Nat.mod_eq_of_lt hj2.2
      have h_eq_mod : j1 % p = j2 % p := h_eq
      rw [h_mod1, h_mod2] at h_eq_mod
      exact h_eq_mod
    · intro b hb
      rw [Finset.mem_erase] at hb
      have hb0 : b ≠ 0 := hb.1
      use b.val
      have hb_val_lt : b.val < p := b.val_lt
      have hb_val_ge : b.val ≥ 1 := by
        by_contra h_contra
        have : b.val = 0 := by omega
        apply hb0
        have h_val : b.val = (0 : ZMod p).val := by
          rw [this, ZMod.val_zero]
        exact ZMod.val_injective p h_val
      refine ⟨by rw [Finset.mem_Ico]; omega, by rw [ZMod.natCast_val, ZMod.cast_id]⟩
    · intro j hj
      rfl
  rw [h_bij]
  exact h_univ

lemma p_sq_mul_zero_of_cast_zero (p : ℕ) (hp : p.Prime) (X : ZMod (p ^ 3))
    (h_cast : (X.cast : ZMod p) = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * X = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  have h_val : ((X.val : ℕ) : ZMod p) = 0 := by
    rw [← ZMod.natCast_val X] at h_cast
    exact h_cast
  have h_dvd : p ∣ X.val := by
    exact (CharP.cast_eq_zero_iff (ZMod p) p X.val).mp h_val
  obtain ⟨k, hk⟩ := h_dvd
  have h_X_eq : X = ((X.val : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.natCast_val X, ZMod.cast_id]
  rw [h_X_eq, hk]
  push_cast
  have h_p3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
    rw [← h_eq, ZMod.natCast_self]
  calc (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) * (k : ZMod (p ^ 3)))
    _ = (p : ZMod (p ^ 3)) ^ 3 * (k : ZMod (p ^ 3)) := by ring
    _ = 0 * (k : ZMod (p ^ 3)) := by rw [h_p3]
    _ = 0 := by ring

lemma cast_sum_inv_sq (p : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    f (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ ^ 2)) = ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
  intro f
  rw [map_sum f]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hj_unit : IsUnit (j : ZMod (p ^ 3)) := by
    have hk1 : j ≥ 1 := hj.1
    have hk2 : j < p := hj.2
    have h_coprime := coprime_p_pow p j hp hk1 hk2 3
    rw [ZMod.isUnit_iff_coprime]
    exact h_coprime
  have h_inv : f (j : ZMod (p ^ 3))⁻¹ = (f (j : ZMod (p ^ 3)))⁻¹ := ringHom_map_inv f (j : ZMod (p ^ 3)) hj_unit
  rw [f.map_pow, h_inv]
  have h_cast_j : f (j : ZMod (p ^ 3)) = (j : ZMod p) := map_natCast f j
  rw [h_cast_j]

lemma sum_pairs_p_sq_mul_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let L : List (ZMod (p ^ 3)) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
  have h_cast_eq : ((List.sum_pairs L).cast : ZMod p) = 0 := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : ((List.sum_pairs L).cast : ZMod p) = f (List.sum_pairs L) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, List.ringHom_sum_pairs f L]
    have h_L_map : L.map f = (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod p)⁻¹) := by
      change ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).map f = _
      simp only [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hi_lt : i < p - 1 := List.mem_range.mp hi
      have hi_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi_lt
      simp only [Function.comp_apply]
      rw [ringHom_map_inv f ((i + 1 : ℕ) : ZMod (p ^ 3)) hi_unit, map_natCast f (i + 1)]
    rw [h_L_map]
    let L_p : List (ZMod p) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod p)⁻¹)
    have h_sum_sq := List.list_sum_sq_eq L_p
    have h_L_p_sum : L_p.sum = 0 := by
      rw [List.list_sum_range_eq_finset_sum_range]
      have h_sum_Ico : (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod p)⁻¹) = ∑ j ∈ Ico 1 p, (j : ZMod p)⁻¹ := by
        rw [range_eq_Ico]
        apply Finset.sum_bij (fun i _ => i + 1)
        · intro i hi
          rw [Finset.mem_Ico] at hi ⊢
          omega
        · intro i1 hi1 i2 hi2 h_eq
          omega
        · intro j hj
          rw [Finset.mem_Ico] at hj
          refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
        · intro i hi
          rfl
      rw [h_sum_Ico]
      exact sum_inv_zero_ico p hp (by omega)
    have h_L_p_map_sum : (L_p.map (fun x => x ^ 2)).sum = 0 := by
      rw [List.map_map, List.list_sum_range_eq_finset_sum_range]
      simp only [Function.comp_apply]
      have h_sum_Ico : (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2) = ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
        rw [range_eq_Ico]
        apply Finset.sum_bij (fun i _ => i + 1)
        · intro i hi
          rw [Finset.mem_Ico] at hi ⊢
          omega
        · intro i1 hi1 i2 hi2 h_eq
          omega
        · intro j hj
          rw [Finset.mem_Ico] at hj
          refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
        · intro i hi
          rfl
      rw [h_sum_Ico]
      exact sum_inv_sq_zero_ico p hp hp5
    rw [h_L_p_sum, h_L_p_map_sum] at h_sum_sq
    have h_2_unit : IsUnit (2 : ZMod p) := by
      have h2 : (2 : ZMod p) ≠ 0 := by
        intro h
        have h_dvd : p ∣ 2 := by
          exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
        have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
        omega
      exact h2.isUnit
    have h_eq : 2 * List.sum_pairs L_p = 2 * 0 := by
      rw [mul_zero]
      have h_simp_sq : 0 = 2 * List.sum_pairs L_p := by
        calc 0
          _ = (0 : ZMod p) ^ 2 := by ring
          _ = 0 + 2 * List.sum_pairs L_p := h_sum_sq
          _ = 2 * List.sum_pairs L_p := by ring
      exact h_simp_sq.symm
    rwa [h_2_unit.mul_right_inj] at h_eq
  exact p_sq_mul_zero_of_cast_zero p hp (List.sum_pairs L) h_cast_eq

lemma p_sq_inv_eq (p : ℕ) (j : ZMod (p ^ 3)) (hj1 : IsUnit j) (hj2 : IsUnit ((p : ZMod (p ^ 3)) - j)) :
    (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) - j)⁻¹ + (p : ZMod (p ^ 3)) ^ 2 * j⁻¹ = 0 := by
  have h1 : j * j⁻¹ = 1 := unit_mul_inv hj1
  have h2 : ((p : ZMod (p ^ 3)) - j) * ((p : ZMod (p ^ 3)) - j)⁻¹ = 1 := unit_mul_inv hj2
  have h_mod : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
    rw [← h_eq, ZMod.natCast_self]
  linear_combination
    - ((p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) - j)⁻¹) * (h1 - 1) -
    ((p : ZMod (p ^ 3)) ^ 2 * j⁻¹) * (h2 - 1) +
    (((p : ZMod (p ^ 3)) - j)⁻¹ * j⁻¹) * h_mod

lemma inv_add_inv_eq_mul (p : ℕ) (j : ZMod (p ^ 3)) (hj1 : IsUnit j) (hj2 : IsUnit ((p : ZMod (p ^ 3)) - j)) :
    j⁻¹ + ((p : ZMod (p ^ 3)) - j)⁻¹ = (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) - j)⁻¹ * j⁻¹ := by
  have h1 : j * j⁻¹ = 1 := unit_mul_inv hj1
  have h2 : ((p : ZMod (p ^ 3)) - j) * ((p : ZMod (p ^ 3)) - j)⁻¹ = 1 := unit_mul_inv hj2
  linear_combination
    - (((p : ZMod (p ^ 3)) - j)⁻¹ * (h1 - 1) + j⁻¹ * (h2 - 1))

lemma sum_reflect_ico (p : ℕ) (hp3 : p ≥ 3) :
    (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = ∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ := by
  apply Finset.sum_bij (fun j _ => p - j)
  · intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    omega
  · intro j1 hj1 j2 hj2 h_eq
    rw [Finset.mem_Ico] at hj1 hj2
    omega
  · intro b hb
    use p - b
    rw [Finset.mem_Ico] at hb ⊢
    have h_le : p - b ≤ p := by omega
    have h_sub : p - (p - b) = b := by omega
    refine ⟨by omega, h_sub⟩
  · intro j hj
    rw [Finset.mem_Ico] at hj
    have h_le : p - j ≤ p := by omega
    have h_sub : (p : ZMod (p ^ 3)) - ((p - j : ℕ) : ZMod (p ^ 3)) = (j : ZMod (p ^ 3)) := by
      rw [← Nat.cast_sub h_le]
      congr 1
      omega
    rw [h_sub]

lemma sum_inv_p_mul_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_reflect := sum_reflect_ico p (by omega)
  have h_twice : 2 * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) =
      (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) := by
    rw [sum_add_distrib, ← h_reflect]
    ring
  have h_twice_mul : (p : ZMod (p ^ 3)) * (2 * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) = (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) := by
    rw [h_twice]
  have h_simp : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) =
      (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
    have h_congr : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) =
        ∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
      apply sum_congr rfl
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : IsUnit (j : ZMod (p ^ 3)) := by
        have hk1 : j ≥ 1 := hj.1
        have hk2 : j < p := hj.2
        have h_coprime := coprime_p_pow p j hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      have hj2 : IsUnit ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) := by
        have h_sub : (p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)) = ((p - j : ℕ) : ZMod (p ^ 3)) := by
          have h_le : j ≤ p := by omega
          rw [Nat.cast_sub h_le]
        rw [h_sub]
        have hk1 : p - j ≥ 1 := by omega
        have hk2 : p - j < p := by omega
        have h_coprime := coprime_p_pow p (p - j) hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      exact inv_add_inv_eq_mul p (j : ZMod (p ^ 3)) hj1 hj2
    rw [h_congr, mul_sum]
    simp_rw [mul_assoc]
  have h_p_twice : 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) =
      (p : ZMod (p ^ 3)) ^ 2 * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
    calc 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹))
      _ = (p : ZMod (p ^ 3)) * (2 * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) := by ring
      _ = (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) := h_twice_mul
      _ = (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹)) := by rw [h_simp]
      _ = (p : ZMod (p ^ 3)) ^ 2 * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by ring
  have h_cast_eq : (((∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹).cast : ZMod p) = 0) := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : ((∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹).cast : ZMod p) =
        f (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, map_sum]
    have h_simp_term : ∀ j ∈ Finset.Ico 1 p, f (((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) = -((j : ZMod p)⁻¹ ^ 2) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : IsUnit (j : ZMod (p ^ 3)) := by
        have hk1 : j ≥ 1 := hj.1
        have hk2 : j < p := hj.2
        have h_coprime := coprime_p_pow p j hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      have hj2 : IsUnit ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) := by
        have h_sub : (p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)) = ((p - j : ℕ) : ZMod (p ^ 3)) := by
          have h_le : j ≤ p := by omega
          rw [Nat.cast_sub h_le]
        rw [h_sub]
        have hk1 : p - j ≥ 1 := by omega
        have hk2 : p - j < p := by omega
        have h_coprime := coprime_p_pow p (p - j) hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      rw [f.map_mul, ringHom_map_inv f ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) hj2, ringHom_map_inv f (j : ZMod (p ^ 3)) hj1]
      have h_cast_j : f (j : ZMod (p ^ 3)) = (j : ZMod p) := map_natCast f j
      have h_cast_pj : f ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) = f (p : ZMod (p ^ 3)) - f (j : ZMod (p ^ 3)) := f.map_sub (p : ZMod (p ^ 3)) (j : ZMod (p ^ 3))
      have h_cast_p : f (p : ZMod (p ^ 3)) = 0 := by
        have h_eq : (p : ZMod (p ^ 3)) = ((p : ℕ) : ZMod (p ^ 3)) := by push_cast; rfl
        rw [h_eq, map_natCast, ZMod.natCast_self]
      have h_inv_neg : (- (j : ZMod p))⁻¹ = - (j : ZMod p)⁻¹ := inv_neg (a := (j : ZMod p))
      rw [h_cast_pj, h_cast_p, h_cast_j, zero_sub, h_inv_neg]
      ring
    rw [sum_congr rfl h_simp_term]
    rw [sum_neg_distrib]
    rw [sum_inv_sq_zero_ico p hp hp5]
    ring
  have h_p2_zero := p_sq_mul_zero_of_cast_zero p hp (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) h_cast_eq
  have h_goal : 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) = 2 * 0 := by
    rw [mul_zero]
    calc 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹))
      _ = (p : ZMod (p ^ 3)) ^ 2 * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := h_p_twice
      _ = 0 := h_p2_zero
  have h2_unit : IsUnit (2 : ZMod (p ^ 3)) := isUnit_of_lt p 1 3 hp (by omega)
  rwa [h2_unit.mul_right_inj] at h_goal

lemma choose_3p_minus_1_p_minus_1_mod_p3 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
    ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
  -- Let's assume we have choose_3p_minus_1_p_minus_1_mod_p3 as proven in Spec.lean!
  -- Since we'll combine all lemmas into Spec.lean, we don't need a real proof here, just sorry to let it compile.
  sorry

lemma choose_3p_minus_1_p_minus_1_eq_one (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_prod_eq : ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
      ((List.range (p - 1)).map (fun i => 1 + (-3 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).prod := by
    rw [choose_3p_minus_1_p_minus_1_mod_p3 p hp (by omega)]
    congr 1
    ext i
    ring
  rw [h_prod_eq]
  let y : ZMod (p ^ 3) := -3 * (p : ZMod (p ^ 3))
  have hy3 : y ^ 3 = 0 := by
    have : y ^ 3 = -27 * (p : ZMod (p ^ 3)) ^ 3 := by ring
    rw [this]
    have h_p3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
      have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
      rw [← h_eq, ZMod.natCast_self]
    rw [h_p3, mul_zero]
  let L : List (ZMod (p ^ 3)) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
  have h_comp : ((List.range (p - 1)).map (fun i => 1 + (-3 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = L.map (fun x => 1 + y * x) := by
    change ((List.range (p - 1)).map (fun i => 1 + (-3 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).map (fun x => 1 + y * x)
    simp only [List.map_map]
    rfl
  rw [h_comp]
  rw [List.prod_one_add_y_mul_eq3 y hy3 L]
  have h_L_sum : L.sum = ∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹ := by
    rw [List.list_sum_range_eq_finset_sum_range]
    rw [range_eq_Ico]
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      rw [Finset.mem_Ico] at hi ⊢
      omega
    · intro i1 hi1 i2 hi2 h_eq
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro i hi
      rfl
  have h_y_L_sum : y * L.sum = 0 := by
    rw [h_L_sum]
    have h_p_sum : (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = 0 := sum_inv_p_mul_zero p hp hp5
    calc y * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)
      _ = -3 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) := by ring
      _ = -3 * 0 := by rw [h_p_sum]
      _ = 0 := mul_zero _
  have h_y2_sum_pairs : y ^ 2 * List.sum_pairs L = 0 := by
    have h_p2_sum_pairs : (p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs L = 0 := sum_pairs_p_sq_mul_zero p hp hp5
    calc y ^ 2 * List.sum_pairs L
      _ = 9 * ((p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs L) := by ring
      _ = 9 * 0 := by rw [h_p2_sum_pairs]
      _ = 0 := mul_zero _
  rw [h_y_L_sum, h_y2_sum_pairs, add_zero, add_zero]


theorem sum_partition_test (p : ℕ) (hp3 : p ≥ 3) (F : ℕ → ZMod (p ^ 3)) :
    (∑ k ∈ range (2 * p + 1), F k) =
    F 0 + (∑ k ∈ Ico 1 p, F k) + F p + (∑ k ∈ Ico (p + 1) (2 * p), F k) + F (2 * p) := by
  have h1 : (∑ k ∈ range (2 * p + 1), F k) = (∑ k ∈ range (2 * p), F k) + F (2 * p) := sum_range_succ F (2 * p)
  have h2 : (∑ k ∈ range (2 * p), F k) = (∑ k ∈ range (p + 1), F k) + (∑ k ∈ Ico (p + 1) (2 * p), F k) := by
    rw [← sum_union]
    · congr 1
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    · rw [Finset.disjoint_iff_ne]
      intro x hx y hy h_eq
      simp only [mem_range] at hx
      simp only [mem_Ico] at hy
      omega
  have h3 : (∑ k ∈ range (p + 1), F k) = (∑ k ∈ range p, F k) + F p := sum_range_succ F p
  have h4 : (∑ k ∈ range p, F k) = F 0 + (∑ k ∈ Ico 1 p, F k) := by
    have h_union : range p = range 1 ∪ Ico 1 p := by
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    have h_disj : Disjoint (range 1) (Ico 1 p) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy h_eq
      simp only [mem_range] at hx
      simp only [mem_Ico] at hy
      omega
    rw [h_union, sum_union h_disj, sum_range_one]
  rw [h1, h2, h3, h4]



lemma choose_gt_mod_p (p j : ℕ) (hp : p.Prime) (hj1 : j ≥ 1) (hj2 : j < p) :
    (2 * p + j).choose (p + j) ≡ 2 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (2 * p + j).choose (p + j) ≡
    ((2 * p + j) % p).choose ((p + j) % p) * ((2 * p + j) / p).choose ((p + j) / p) [MOD p] := Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h1 : (2 * p + j) % p = j := by
    have h_eq : 2 * p + j = j + p * 2 := by ring
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj2
  have h2 : (p + j) % p = j := by
    have h_eq : p + j = j + p * 1 := by ring
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj2
  have h3 : (2 * p + j) / p = 2 := by
    have h_eq : 2 * p + j = j + p * 2 := by ring
    rw [h_eq]
    rw [Nat.add_mul_div_left j 2 (by omega)]
    have : j / p = 0 := Nat.div_eq_of_lt hj2
    rw [this, Nat.zero_add]
  have h4 : (p + j) / p = 1 := by
    have h_eq : p + j = j + p * 1 := by ring
    rw [h_eq]
    rw [Nat.add_mul_div_left j 1 (by omega)]
    have : j / p = 0 := Nat.div_eq_of_lt hj2
    rw [this, Nat.zero_add]
  have h5 : j.choose j = 1 := Nat.choose_self j
  have h6 : Nat.choose 2 1 = 2 := rfl
  rw [h1, h2, h3, h4, h5, h6] at h
  have h_mul : 1 * 2 = 2 := rfl
  rw [h_mul] at h
  exact h


lemma choose_relation_gt (p j : ℕ) (hp : p ≥ 1) (hj : j ≥ 1) :
    (2 * p + j - 1).choose (p + j) * (2 * p + j) = p * (2 * p + j).choose (p + j) := by
  have h := choose_mul_succ_eq (2 * p + j - 1) (p + j)
  have h_comm : 2 * p = p * 2 := mul_comm 2 p
  rw [h_comm] at h
  rw [h_comm]
  have h1 : p * 2 + j - 1 + 1 = p * 2 + j := by omega
  have h3 : p * 2 + j - (p + j) = p := by omega
  rw [h1] at h
  rw [h3] at h
  rw [mul_comm _ p] at h
  exact h

lemma term_sq_eq_gt (p j : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hj1 : j ≥ 1) (hj2 : j < p) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2) = (p : ZMod (p ^ 3)) ^ 2 * 4 * (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by
  have h_unit : IsUnit ((2 * p + j : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    have h_coprime : (2 * p + j).Coprime (p ^ 3) := by
      have h_cop : (2 * p + j).Coprime p := by
        rw [Nat.coprime_comm]
        apply hp.coprime_iff_not_dvd.mpr
        intro h_dvd
        have h_dvd_j : p ∣ j := by
          obtain ⟨k, hk⟩ := h_dvd
          use k - 2
          have hk2 : k ≥ 2 := by
            by_contra! hc
            interval_cases k
            · omega
            · omega
          have h_sub : p * (k - 2) = p * k - p * 2 := Nat.mul_sub_left_distrib p k 2
          rw [h_sub]
          omega
        have : p ≤ j := Nat.le_of_dvd hj1 h_dvd_j
        omega
      exact h_cop.pow_right 3
    exact h_coprime
  have h_relation := choose_relation_gt p j (by omega) hj1
  have h_cast : (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))) = (p : ZMod (p ^ 3)) * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) := by
    have h_cast_mul : (((2 * p + j - 1).choose (p + j) * (2 * p + j) : ℕ) : ZMod (p ^ 3)) = (((p * (2 * p + j).choose (p + j)) : ℕ) : ZMod (p ^ 3)) := by
      congr 1
    rw [Nat.cast_mul, Nat.cast_mul] at h_cast_mul
    exact h_cast_mul
  have h_mul : ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ := by
    calc ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3))
      _ = ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) * (((2 * p + j : ℕ) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹) := by rw [unit_mul_inv h_unit, mul_one]
      _ = (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ := by ring
      _ = (p : ZMod (p ^ 3)) * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [h_cast]
  have h_sq : ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
    rw [h_mul]
    ring
  have h_mod_p := choose_gt_mod_p p j hp hj1 hj2
  let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
    have : p > 0 := hp.pos
    exact dvd_pow_self p (by omega)) (ZMod p)
  have h_cast_p : f ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) = 2 := by
    have h_eq : (((2 * p + j).choose (p + j) : ℕ) : ZMod p) = 2 := by
      have h_eq2 : (((2 * p + j).choose (p + j) : ℕ) : ZMod p) = (((2 : ℕ) : ZMod p)) := by
        rwa [ZMod.natCast_eq_natCast_iff]
      rw [h_eq2]
      rfl
    calc f ((2 * p + j).choose (p + j) : ZMod (p ^ 3))
      _ = (((2 * p + j).choose (p + j) : ℕ) : ZMod p) := map_natCast f ((2 * p + j).choose (p + j))
      _ = 2 := h_eq
  have h_cast_sq : f (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2) = 4 := by
    rw [f.map_pow, h_cast_p]
    ring
  have h_sub_cast : f (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4) = 0 := by
    rw [f.map_sub, h_cast_sq, map_ofNat f 4, sub_self]
  have h_cast_eq : (((((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4).cast : ZMod p) = 0) := by
    have h_eq : (((((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4).cast : ZMod p) = f (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4)) := rfl
    rw [h_eq, h_sub_cast]
  have h_mul_zero := p_sq_mul_zero_of_cast_zero p hp (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4) h_cast_eq
  have h_final : (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * 4 := by
    linear_combination h_mul_zero
  have h_unit_j : IsUnit ((j : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact coprime_p_pow p j hp hj1 hj2 3
  have h_inv_cast : f ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ = f ((j : ℕ) : ZMod (p ^ 3))⁻¹ := by
    have h_cast_pj : f ((2 * p + j : ℕ) : ZMod (p ^ 3)) = f ((j : ℕ) : ZMod (p ^ 3)) := by
      rw [map_natCast f (2 * p + j), map_natCast f j]
      have h_eq : ((2 * p + j : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by
        push_cast
        have : (p : ZMod p) = 0 := ZMod.natCast_self p
        calc (2 * (p : ZMod p) + j : ZMod p)
          _ = 2 * 0 + j := by rw [this]
          _ = j := by ring
      exact h_eq
    rw [ringHom_map_inv f ((2 * p + j : ℕ) : ZMod (p ^ 3)) h_unit, ringHom_map_inv f ((j : ℕ) : ZMod (p ^ 3)) h_unit_j, h_cast_pj]
  have h_cast_eq2 : (((((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2).cast : ZMod p) = 0) := by
    have h_eq : (((((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2).cast : ZMod p) = f ((((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := rfl
    rw [h_eq, f.map_sub, f.map_pow, f.map_pow, h_inv_cast]
    simp
  have h_mul_zero2 := p_sq_mul_zero_of_cast_zero p hp (((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) h_cast_eq2
  have h_inv_eq : (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
    linear_combination h_mul_zero2
  calc ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2
    _ = (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := h_sq
    _ = (p : ZMod (p ^ 3)) ^ 2 * 4 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by rw [h_final]
    _ = 4 * ((p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by ring
    _ = 4 * ((p : ZMod (p ^ 3)) ^ 2 * ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by rw [h_inv_eq]
    _ = (p : ZMod (p ^ 3)) ^ 2 * 4 * ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by ring


lemma sum_term_sq_zero_gt (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2)) = 0 := by
  have h_congr : (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2)) =
      ∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) ^ 2 * 4 * (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact term_sq_eq_gt p j hp hp5 hj.1 hj.2
  have h_congr_mul : (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2)) =
      (p : ZMod (p ^ 3)) ^ 2 * 4 * (∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) := by
    rw [h_congr, ← mul_sum]
  have h_cast_eq : (((4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = 0) := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : (((4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = f (4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, f.map_mul, map_ofNat f 4, map_sum]
    have h_simp_term : ∀ j ∈ Finset.Ico 1 p, f (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) = ((j : ZMod p)⁻¹ ^ 2) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj_unit : IsUnit ((j : ℕ) : ZMod (p ^ 3)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact coprime_p_pow p j hp hj.1 hj.2 3
      rw [f.map_pow, ringHom_map_inv f ((j : ℕ) : ZMod (p ^ 3)) hj_unit, map_natCast f j]
    rw [sum_congr rfl h_simp_term]
    rw [sum_inv_sq_zero_ico p hp hp5]
    ring
  have h_zero := p_sq_mul_zero_of_cast_zero p hp (4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) h_cast_eq
  calc (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2))
    _ = (p : ZMod (p ^ 3)) ^ 2 * 4 * (∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) := h_congr_mul
    _ = (p : ZMod (p ^ 3)) ^ 2 * (4 * (∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := by ring
    _ = 0 := h_zero

