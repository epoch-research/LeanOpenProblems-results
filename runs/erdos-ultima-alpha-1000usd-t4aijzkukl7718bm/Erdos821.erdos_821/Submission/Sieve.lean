import FormalConjecturesUtil

/-!
# Sieve development for the totient multiplicity problem

This file does not settle Erdős problem 821. It develops finite upper-sieve
estimates, a logarithmic denominator lower bound, harmonic-average estimates,
and an unconditional supply of primes smooth at one fixed power scale.
Together with the counting lemmas this yields a fixed positive exponent,
not the arbitrary-exponent assertion in Erdős problem 821.
-/

open Finset

namespace Erdos821.Sieve

lemma sifted_card_le_square_sum {α ι : Type*} [DecidableEq α]
    (A : Finset α) (D : Finset ι) (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    (good : α → Prop) [DecidablePred good] (w : ι → ℝ)
    (hgood : ∀ x ∈ A, good x → (∑ i ∈ D, if E i x then w i else 0) = 1) :
    ((A.filter good).card : ℝ) ≤ ∑ x ∈ A, (∑ i ∈ D, if E i x then w i else 0) ^ 2 := by
  calc
    ((A.filter good).card : ℝ) = ∑ x ∈ A, if good x then (1 : ℝ) else 0 := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ x ∈ A, (∑ i ∈ D, if E i x then w i else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hg : good x
      · rw [if_pos hg, hgood x hx hg]
        norm_num
      · rw [if_neg hg]
        exact sq_nonneg _

lemma square_sum_expansion {α ι : Type*}
    (A : Finset α) (D : Finset ι) (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    (w : ι → ℝ) :
    (∑ x ∈ A, (∑ i ∈ D, if E i x then w i else 0) ^ 2) =
      ∑ i ∈ D, ∑ j ∈ D, w i * w j * ((A.filter (fun x => E i x ∧ E j x)).card : ℝ) := by
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ x ∈ A, (if E i x then w i else 0) * (if E j x then w j else 0)) =
        ∑ x ∈ A, if E i x ∧ E j x then w i * w j else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp_all
    _ = w i * w j * ((A.filter (fun x => E i x ∧ E j x)).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma sifted_card_le_main_error {α ι : Type*} [DecidableEq α]
    (A : Finset α) (D : Finset ι) (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    (good : α → Prop) [DecidablePred good] (w : ι → ℝ)
    (X : ℝ) (ν R : ι → ι → ℝ)
    (hgood : ∀ x ∈ A, good x → (∑ i ∈ D, if E i x then w i else 0) = 1)
    (hcount : ∀ i ∈ D, ∀ j ∈ D,
      ((A.filter (fun x => E i x ∧ E j x)).card : ℝ) = X * ν i j + R i j) :
    ((A.filter good).card : ℝ) ≤
      X * (∑ i ∈ D, ∑ j ∈ D, w i * w j * ν i j) +
        ∑ i ∈ D, ∑ j ∈ D, |w i * w j| * |R i j| := by
  apply (sifted_card_le_square_sum A D E good w hgood).trans
  rw [square_sum_expansion]
  calc
    (∑ i ∈ D, ∑ j ∈ D, w i * w j * ((A.filter (fun x => E i x ∧ E j x)).card : ℝ)) =
        ∑ i ∈ D, ∑ j ∈ D, (X * (w i * w j * ν i j) + w i * w j * R i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcount i hi j hj]
      ring
    _ ≤ ∑ i ∈ D, ∑ j ∈ D, (X * (w i * w j * ν i j) + |w i * w j| * |R i j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply add_le_add le_rfl
      simpa only [abs_mul] using le_abs_self (w i * w j * R i j)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

lemma weighted_square_sum_expansion {α ι : Type*}
    (A : Finset α) (D : Finset ι) (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    (w : ι → ℝ) (h : α → ℝ) :
    (∑ x ∈ A, h x * (∑ i ∈ D, if E i x then w i else 0) ^ 2) =
      ∑ i ∈ D, ∑ j ∈ D, w i * w j *
        ∑ x ∈ A, if E i x ∧ E j x then h x else 0 := by
  simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hi : E i x <;> by_cases hj : E j x <;> simp [hi, hj] <;> ring

lemma sieve_kernel_expansion {α : Type*} [DecidableEq α]
    (S T : Finset α) (v : α → ℝ) (hv : ∀ p ∈ S ∩ T, v p ≠ 0) :
    (∏ p ∈ S ∪ T, v p) = (∏ p ∈ S, v p) * (∏ p ∈ T, v p) *
      ∑ R ∈ (S ∩ T).powerset, ∏ p ∈ R, ((v p)⁻¹ - 1) := by
  have hsum : (∑ R ∈ (S ∩ T).powerset, ∏ p ∈ R, ((v p)⁻¹ - 1)) =
      (∏ p ∈ S ∩ T, v p)⁻¹ := by
    rw [← Finset.prod_one_add]
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    ring
  rw [hsum, ← Finset.prod_union_inter]
  exact (mul_inv_cancel_right₀ (Finset.prod_ne_zero_iff.mpr hv) _).symm

lemma sieve_quadratic_diagonalization {α : Type*} [DecidableEq α]
    (P : Finset α) (v : α → ℝ) (hv : ∀ p ∈ P, v p ≠ 0) (w : Finset α → ℝ) :
    (∑ S ∈ P.powerset, ∑ T ∈ P.powerset, w S * w T * (∏ p ∈ S ∪ T, v p)) =
      ∑ R ∈ P.powerset, (∏ p ∈ R, ((v p)⁻¹ - 1)) *
        (∑ S ∈ P.powerset, if R ⊆ S then w S * ∏ p ∈ S, v p else 0) ^ 2 := by
  rw [weighted_square_sum_expansion P.powerset P.powerset
    (fun S R => R ⊆ S) (fun S => w S * ∏ p ∈ S, v p)
    (fun R => ∏ p ∈ R, ((v p)⁻¹ - 1))]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hSP := Finset.mem_powerset.mp hS
  have hTP := Finset.mem_powerset.mp hT
  have hsum : (∑ R ∈ P.powerset,
      if R ⊆ S ∧ R ⊆ T then ∏ p ∈ R, ((v p)⁻¹ - 1) else 0) =
      ∑ R ∈ (S ∩ T).powerset, ∏ p ∈ R, ((v p)⁻¹ - 1) := by
    rw [← Finset.sum_filter]
    congr 1
    ext R
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.1.trans hSP, h⟩⟩
  rw [hsum, sieve_kernel_expansion S T v (fun p hp => hv p (hSP (Finset.mem_inter.mp hp).1))]
  ring

lemma alternating_superset_sum {α : Type*} [DecidableEq α] (S R : Finset α) :
    (∑ T ∈ R.powerset, if S ⊆ T then (-1 : ℝ) ^ T.card else 0) =
      if S = R then (-1 : ℝ) ^ S.card else 0 := by
  induction R using Finset.induction generalizing S with
  | empty =>
    by_cases hS : S = ∅ <;> simp [hS]
  | @insert a R ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have haT (T : Finset α) (hT : T ∈ R.powerset) : a ∉ T :=
      fun h => ha (Finset.mem_powerset.mp hT h)
    have hsum : (∑ T ∈ R.powerset, if S ⊆ insert a T then (-1 : ℝ) ^ (insert a T).card else 0) =
        -(∑ T ∈ R.powerset, if S.erase a ⊆ T then (-1 : ℝ) ^ T.card else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      simp only [Finset.subset_insert_iff, Finset.card_insert_of_notMem (haT T hT), pow_succ]
      split_ifs <;> ring
    rw [hsum, ih (S.erase a)]
    by_cases haS : a ∈ S
    · have hzero : (∑ T ∈ R.powerset, if S ⊆ T then (-1 : ℝ) ^ T.card else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        exact if_neg (fun h => haT T hT (h haS))
      rw [hzero, zero_add]
      have heq : S.erase a = R ↔ S = insert a R := Finset.erase_eq_iff_eq_insert haS ha
      simp only [heq]
      split_ifs with he
      · have hcard : S.card = (S.erase a).card + 1 := (Finset.card_erase_add_one haS).symm
        rw [hcard, pow_succ]
        ring
      · simp
    · rw [Finset.erase_eq_of_notMem haS]
      have hne : S ≠ insert a R := by
        intro h
        exact haS (h ▸ Finset.mem_insert_self a R)
      rw [if_neg hne, ih S]
      ring

/-- Boolean Möbius inversion for sums over supersets. -/
lemma alternating_superset_inversion {α : Type*} [DecidableEq α]
    (P S : Finset α) (hS : S ⊆ P) (f : Finset α → ℝ) :
    (∑ T ∈ P.powerset, if S ⊆ T then
      (-1 : ℝ) ^ T.card * (∑ R ∈ P.powerset, if T ⊆ R then f R else 0) else 0) =
      (-1 : ℝ) ^ S.card * f S := by
  calc
    _ = ∑ T ∈ P.powerset, ∑ R ∈ P.powerset,
        if S ⊆ T ∧ T ⊆ R then (-1 : ℝ) ^ T.card * f R else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hST : S ⊆ T
      · simp only [hST, true_and, if_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        by_cases hTR : T ⊆ R <;> simp [hTR]
      · simp [hST]
    _ = ∑ R ∈ P.powerset, ∑ T ∈ P.powerset,
        if S ⊆ T ∧ T ⊆ R then (-1 : ℝ) ^ T.card * f R else 0 := Finset.sum_comm
    _ = ∑ R ∈ P.powerset, (if S = R then (-1 : ℝ) ^ S.card else 0) * f R := by
      apply Finset.sum_congr rfl
      intro R hR
      have hRP := Finset.mem_powerset.mp hR
      rw [← alternating_superset_sum S R, Finset.sum_mul]
      have hfilter : P.powerset.filter (fun T => T ⊆ R) = R.powerset := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨h.trans hRP, h⟩⟩
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hST : S ⊆ T <;> by_cases hTR : T ⊆ R <;> simp [hST, hTR]
    _ = (-1 : ℝ) ^ S.card * f S := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_powerset,
        hS, if_true]

/-- Optimal finite Selberg weights on a downward-closed family of subsets. -/
lemma exists_selberg_weights {α : Type*} [DecidableEq α]
    (P : Finset α) (W : Finset (Finset α)) (hWP : W ⊆ P.powerset)
    (hW0 : ∅ ∈ W) (hdown : ∀ R ∈ W, ∀ S, S ⊆ R → S ∈ W)
    (v : α → ℝ) (hv : ∀ p ∈ P, 0 < v p ∧ v p < 1) :
    ∃ w : Finset α → ℝ,
      w ∅ = 1 ∧
      (∀ S ∈ P.powerset, S ∉ W → w S = 0) ∧
      (∀ S ∈ P.powerset, |w S| * (∏ p ∈ S, v p) ≤ 1) ∧
      (∑ S ∈ P.powerset, ∑ T ∈ P.powerset, w S * w T * (∏ p ∈ S ∪ T, v p)) =
        (∑ R ∈ W, (∏ p ∈ R, ((v p)⁻¹ - 1))⁻¹)⁻¹ := by
  classical
  let V : Finset α → ℝ := fun S => ∏ p ∈ S, v p
  let H : Finset α → ℝ := fun S => ∏ p ∈ S, ((v p)⁻¹ - 1)
  let f : Finset α → ℝ := fun S => if S ∈ W then (H S)⁻¹ else 0
  let G : ℝ := ∑ S ∈ W, (H S)⁻¹
  let F : Finset α → ℝ := fun S => ∑ R ∈ P.powerset, if S ⊆ R then f R else 0
  let w : Finset α → ℝ := fun S => (-1 : ℝ) ^ S.card * F S / (V S * G)
  have hV (S : Finset α) (hS : S ∈ P.powerset) : 0 < V S :=
    Finset.prod_pos (fun p hp => (hv p (Finset.mem_powerset.mp hS hp)).1)
  have hH (S : Finset α) (hS : S ∈ P.powerset) : 0 < H S := by
    apply Finset.prod_pos
    intro p hp
    obtain ⟨hpos, hlt⟩ := hv p (Finset.mem_powerset.mp hS hp)
    exact sub_pos.mpr ((one_lt_inv₀ hpos).mpr hlt)
  have hG : 0 < G := Finset.sum_pos
    (fun S hS => inv_pos.mpr (hH S (hWP hS))) ⟨∅, hW0⟩
  have hf (S : Finset α) : 0 ≤ f S := by
    dsimp only [f]
    split_ifs with hS
    · exact (inv_pos.mpr (hH S (hWP hS))).le
    · exact le_rfl
  have hsumf : (∑ S ∈ P.powerset, f S) = G := by
    dsimp only [G]
    symm
    calc
      (∑ S ∈ W, (H S)⁻¹) = ∑ S ∈ W, f S := by
        apply Finset.sum_congr rfl
        intro S hS
        simp only [f, if_pos hS]
      _ = ∑ S ∈ P.powerset, f S := Finset.sum_subset hWP (fun S _ hS => by simp [f, hS])
  have hFnonneg (S : Finset α) : 0 ≤ F S :=
    Finset.sum_nonneg (fun R _ => by split_ifs; exacts [hf R, le_rfl])
  have hFle (S : Finset α) : F S ≤ G := by
    rw [← hsumf]
    apply Finset.sum_le_sum
    intro R hR
    split_ifs
    · exact le_rfl
    · exact hf R
  have hw (S : Finset α) (hS : S ∈ P.powerset) :
      w S * V S = (-1 : ℝ) ^ S.card * F S / G := by
    dsimp only [w]
    field_simp [(hV S hS).ne', hG.ne']
  have htrans (R : Finset α) (hR : R ∈ P.powerset) :
      (∑ S ∈ P.powerset, if R ⊆ S then w S * V S else 0) =
        (-1 : ℝ) ^ R.card * f R / G := by
    calc
      _ = (∑ S ∈ P.powerset, if R ⊆ S then (-1 : ℝ) ^ S.card * F S else 0) / G := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hRS : R ⊆ S
        · simp only [if_pos hRS, hw S hS]
        · simp only [if_neg hRS, zero_div]
      _ = (-1 : ℝ) ^ R.card * f R / G := by
        rw [alternating_superset_inversion P R (Finset.mem_powerset.mp hR) f]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have hF0 : F ∅ = G := by
      simpa only [F, Finset.empty_subset, if_true] using hsumf
    simp only [w, V, Finset.card_empty, pow_zero, one_mul, Finset.prod_empty, hF0,
      div_self hG.ne']
  · intro S hS hSW
    have hF0 : F S = 0 := by
      apply Finset.sum_eq_zero
      intro R hR
      by_cases hSR : S ⊆ R
      · have hRW : R ∉ W := fun hRW => hSW (hdown R hRW S hSR)
        simp only [if_pos hSR, f, if_neg hRW]
      · simp only [if_neg hSR]
    simp only [w, hF0, mul_zero, zero_div]
  · intro S hS
    change |w S| * V S ≤ 1
    have heq : |w S| * V S = F S / G := by
      rw [← abs_of_pos (hV S hS), ← abs_mul, hw S hS, abs_div, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (hFnonneg S),
        abs_of_pos hG]
    rw [heq]
    exact (div_le_one hG).mpr (hFle S)
  · rw [sieve_quadratic_diagonalization P v (fun p hp => (hv p hp).1.ne') w]
    change (∑ R ∈ P.powerset, H R * (∑ S ∈ P.powerset, if R ⊆ S then w S * V S else 0) ^ 2) = G⁻¹
    calc
      _ = ∑ R ∈ P.powerset, f R / G ^ 2 := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [htrans R hR]
        by_cases hRW : R ∈ W
        · have hsign : ((-1 : ℝ) ^ R.card) ^ 2 = 1 := by
            rw [← pow_mul, mul_comm R.card 2, pow_mul, neg_one_sq, one_pow]
          simp only [f, if_pos hRW, div_pow, mul_pow, hsign, one_mul]
          field_simp [(hH R hR).ne', hG.ne']
        · simp only [f, if_neg hRW, mul_zero, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero]
      _ = G / G ^ 2 := by rw [← Finset.sum_div, hsumf]
      _ = G⁻¹ := by field_simp [hG.ne']

/-- A finite Selberg bound with a polynomial error term, using products of prime indices
as the level constraint. -/
lemma finite_selberg_bound {α : Type*} [DecidableEq α]
    (A : Finset α) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (bad : ℕ → α → Prop) [∀ p, DecidablePred (bad p)]
    (ρ : ℕ → ℝ) (hρ : ∀ p ∈ P, 1 ≤ ρ p ∧ ρ p < p)
    (X : ℝ) (z : ℕ) (hz : 1 ≤ z)
    (hcount : ∀ S ∈ P.powerset,
      |((A.filter (fun x => ∀ p ∈ S, bad p x)).card : ℝ) -
        X * (∏ p ∈ S, ρ p / p)| ≤ ∏ p ∈ S, ρ p) :
    ((A.filter (fun x => ∀ p ∈ P, ¬bad p x)).card : ℝ) ≤
      X * (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, ((ρ p / p)⁻¹ - 1))⁻¹)⁻¹ + (z : ℝ) ^ 4 := by
  classical
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  let v : ℕ → ℝ := fun p => ρ p / p
  let V : Finset ℕ → ℝ := fun S => ∏ p ∈ S, v p
  let R : Finset ℕ → ℝ := fun S => ∏ p ∈ S, ρ p
  let G : ℝ := ∑ S ∈ W, (∏ p ∈ S, ((v p)⁻¹ - 1))⁻¹
  have hWP : W ⊆ P.powerset := Finset.filter_subset _ _
  have hW0 : ∅ ∈ W := by simp only [W, Finset.mem_filter, Finset.empty_mem_powerset,
    Finset.prod_empty, true_and]; exact hz
  have hdown : ∀ T ∈ W, ∀ S, S ⊆ T → S ∈ W := by
    intro T hT S hST
    obtain ⟨hTP, hTz⟩ := Finset.mem_filter.mp hT
    have hTP' := Finset.mem_powerset.mp hTP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (hST.trans hTP'), le_trans ?_ hTz⟩
    exact Finset.prod_le_prod_of_subset_of_one_le' hST
      (fun p hp _ => (hP p (hTP' hp)).one_lt.le)
  have hv : ∀ p ∈ P, 0 < v p ∧ v p < 1 := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    exact ⟨div_pos (lt_of_lt_of_le zero_lt_one (hρ p hp).1) hpR,
      (div_lt_one hpR).mpr (hρ p hp).2⟩
  obtain ⟨w, hw0, hwzero, hwbound, hwmain⟩ :=
    exists_selberg_weights P W hWP hW0 hdown v hv
  have hWcard : W.card ≤ z := by
    have hmaps : Set.MapsTo (fun S : Finset ℕ => ∏ p ∈ S, p)
        (↑W : Set (Finset ℕ)) (↑(Finset.Icc 1 z) : Set ℕ) := by
      intro S hS
      obtain ⟨hSP, hSz⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_Icc.mpr ⟨Finset.prod_pos
        (fun p hp => (hP p (Finset.mem_powerset.mp hSP hp)).pos), hSz⟩
    have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (↑W : Set (Finset ℕ)) := by
      intro S hS T hT heq
      have hSP := Finset.mem_powerset.mp (hWP hS)
      have hTP := Finset.mem_powerset.mp (hWP hT)
      have h := congrArg Nat.primeFactors heq
      simpa only [Nat.primeFactors_prod (fun p hp => hP p (hSP hp)),
        Nat.primeFactors_prod (fun p hp => hP p (hTP hp))] using h
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card_of_injOn _ hmaps hinj
  have hRpos (S : Finset ℕ) (hS : S ⊆ P) : 0 < R S :=
    Finset.prod_pos (fun p hp => lt_of_lt_of_le zero_lt_one (hρ p (hS hp)).1)
  have hRunion (S T : Finset ℕ) (hS : S ⊆ P) (hT : T ⊆ P) : R (S ∪ T) ≤ R S * R T := by
    have hI : 1 ≤ R (S ∩ T) := calc
      1 = ∏ _p ∈ S ∩ T, (1 : ℝ) := by simp
      _ ≤ R (S ∩ T) := Finset.prod_le_prod (fun _ _ => zero_le_one)
        (fun p hp => (hρ p (hS (Finset.mem_inter.mp hp).1)).1)
    calc
      R (S ∪ T) = R (S ∪ T) * 1 := (mul_one _).symm
      _ ≤ R (S ∪ T) * R (S ∩ T) := mul_le_mul_of_nonneg_left hI
        (hRpos _ (Finset.union_subset hS hT)).le
      _ = R S * R T := Finset.prod_union_inter
  have hwR (S : Finset ℕ) (hS : S ∈ P.powerset) :
      |w S| * R S ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by
    have hSP := Finset.mem_powerset.mp hS
    have hpR : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun p hp => (hP p (hSP hp)).pos)
    have heq : V S = R S / ((∏ p ∈ S, p : ℕ) : ℝ) := by
      simp only [V, v, R, Finset.prod_div_distrib, Nat.cast_prod]
    have hb := hwbound S hS
    change |w S| * V S ≤ 1 at hb
    rw [heq, ← mul_div_assoc] at hb
    exact (div_le_one hpR).mp hb
  have hsumR : (∑ S ∈ P.powerset, |w S| * R S) ≤ (z : ℝ) ^ 2 := by
    have hsum : (∑ S ∈ P.powerset, |w S| * R S) = ∑ S ∈ W, |w S| * R S := by
      symm
      apply Finset.sum_subset hWP
      intro S hS hSW
      rw [hwzero S hS hSW, abs_zero, zero_mul]
    rw [hsum]
    calc
      (∑ S ∈ W, |w S| * R S) ≤ ∑ S ∈ W, (z : ℝ) := by
        apply Finset.sum_le_sum
        intro S hS
        exact (hwR S (hWP hS)).trans (by exact_mod_cast (Finset.mem_filter.mp hS).2)
      _ = (W.card : ℝ) * z := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (z : ℝ) * z := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hWcard) (Nat.cast_nonneg z)
      _ = (z : ℝ) ^ 2 := (pow_two _).symm
  let E : Finset ℕ → α → Prop := fun S x => ∀ p ∈ S, bad p x
  let good : α → Prop := fun x => ∀ p ∈ P, ¬bad p x
  let K : Finset ℕ → Finset ℕ → ℝ := fun S T => V (S ∪ T)
  let err : Finset ℕ → Finset ℕ → ℝ := fun S T =>
    ((A.filter (fun x => E S x ∧ E T x)).card : ℝ) - X * K S T
  have hgood : ∀ x ∈ A, good x → (∑ S ∈ P.powerset, if E S x then w S else 0) = 1 := by
    intro x hx hg
    rw [Finset.sum_eq_single ∅]
    · simp only [E, Finset.notMem_empty, false_implies, implies_true, if_true, hw0]
    · intro S hS hSne
      apply if_neg
      intro hE
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
      exact hg p (Finset.mem_powerset.mp hS hp) (hE p hp)
    · simp
  have hecount : ∀ S ∈ P.powerset, ∀ T ∈ P.powerset,
      ((A.filter (fun x => E S x ∧ E T x)).card : ℝ) = X * K S T + err S T := by
    intro S hS T hT
    dsimp only [err]
    ring
  have herr (S T : Finset ℕ) (hS : S ∈ P.powerset) (hT : T ∈ P.powerset) :
      |err S T| ≤ R (S ∪ T) := by
    have hunion : A.filter (fun x => E S x ∧ E T x) =
        A.filter (fun x => ∀ p ∈ S ∪ T, bad p x) := by
      ext x
      simp only [Finset.mem_filter, E, Finset.mem_union, or_imp, forall_and]
    dsimp only [err, K, V, v, R]
    rw [hunion]
    exact hcount (S ∪ T) (Finset.mem_powerset.mpr
      (Finset.union_subset (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)))
  have herrsum : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset, |w S * w T| * |err S T|) ≤
      (z : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ S ∈ P.powerset, ∑ T ∈ P.powerset, (|w S| * R S) * (|w T| * R T) := by
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        calc
          |w S * w T| * |err S T| ≤ |w S * w T| * (R S * R T) :=
            mul_le_mul_of_nonneg_left ((herr S T hS hT).trans
              (hRunion S T (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT))) (abs_nonneg _)
          _ = (|w S| * R S) * (|w T| * R T) := by rw [abs_mul]; ring
      _ = (∑ S ∈ P.powerset, |w S| * R S) ^ 2 := by rw [pow_two, Finset.sum_mul_sum]
      _ ≤ ((z : ℝ) ^ 2) ^ 2 := by
        apply pow_le_pow_left₀
        · exact Finset.sum_nonneg (fun S hS => mul_nonneg (abs_nonneg _)
            (hRpos S (Finset.mem_powerset.mp hS)).le)
        · exact hsumR
      _ = (z : ℝ) ^ 4 := by ring
  have hb := sifted_card_le_main_error A P.powerset E good w X K err hgood hecount
  change ((A.filter good).card : ℝ) ≤ X * G⁻¹ + (z : ℝ) ^ 4
  have hmain : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset, w S * w T * K S T) = G⁻¹ := hwmain
  rw [hmain] at hb
  exact hb.trans (add_le_add le_rfl herrsum)

lemma card_residue_filter (N d : ℕ) (hd : 0 < d) (B : Finset ℕ)
    (hB : ∀ r ∈ B, r < d) :
    ((Finset.range N).filter (fun n => n % d ∈ B)).card =
      (N / d) * B.card + (B.filter (fun r => r < N % d)).card := by
  let A := (Finset.range N).filter (fun n => n % d ∈ B)
  have hmaps : Set.MapsTo (fun n : ℕ => n % d) (↑A : Set ℕ) (↑B : Set ℕ) := by
    intro n hn
    change n ∈ A at hn
    change n % d ∈ B
    exact (Finset.mem_filter.mp hn).2
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (r : ℕ) (hr : r ∈ B) :
      A.filter (fun n => n % d = r) = (Finset.range N).filter (fun n => n ≡ r [MOD d]) := by
    ext n
    simp only [A, Finset.mem_filter, Finset.mem_range, Nat.ModEq, Nat.mod_eq_of_lt (hB r hr)]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2 ▸ hr⟩, h.2⟩
  calc
    A.card = ∑ r ∈ B, (A.filter (fun n => n % d = r)).card := hcard
    _ = ∑ r ∈ B, (N / d + if r < N % d then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hfiber r hr, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hd r,
        Nat.mod_eq_of_lt (hB r hr)]
    _ = (N / d) * B.card + (B.filter (fun r => r < N % d)).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm,
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      norm_cast

lemma abs_card_residue_filter_sub (N d : ℕ) (hd : 0 < d) (B : Finset ℕ)
    (hB : ∀ r ∈ B, r < d) :
    |(((Finset.range N).filter (fun n => n % d ∈ B)).card : ℝ) -
      (N : ℝ) / d * B.card| ≤ B.card := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrem0 : (0 : ℝ) ≤ (N % d : ℕ) / d := div_nonneg (Nat.cast_nonneg _) hdR.le
  have hrem1 : ((N % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hdR).mpr
    (by exact_mod_cast (Nat.mod_lt N hd).le)
  have hdiv : (N : ℝ) / d = ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) / d := by
    apply (div_eq_iff hdR.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hdR.ne']
    exact_mod_cast (show N = N / d * d + N % d by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hcount : ((B.filter (fun r => r < N % d)).card : ℝ) ≤ B.card :=
    Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hcount0 : (0 : ℝ) ≤ (B.filter (fun r => r < N % d)).card := Nat.cast_nonneg _
  have hmul0 := mul_nonneg hrem0 (Nat.cast_nonneg B.card)
  have hmul1 := mul_le_mul_of_nonneg_right hrem1 (Nat.cast_nonneg B.card)
  rw [card_residue_filter N d hd B hB, Nat.cast_add, Nat.cast_mul, hdiv]
  apply abs_le.mpr
  constructor <;> nlinarith

noncomputable def quadraticRootCount (a d : ℕ) : ℕ :=
  Nat.card {x : ZMod d // x * ((a : ZMod d) * x + 1) = 0}

lemma quadraticRootCount_mul (a m n : ℕ) (h : m.Coprime n) :
    quadraticRootCount a (m * n) = quadraticRootCount a m * quadraticRootCount a n := by
  let e := ZMod.chineseRemainder h
  have he (x : ZMod (m * n)) : x * ((a : ZMod (m * n)) * x + 1) = 0 ↔
      (e x).1 * ((a : ZMod m) * (e x).1 + 1) = 0 ∧
      (e x).2 * ((a : ZMod n) * (e x).2 + 1) = 0 := by
    have hi := e.injective.eq_iff (a := x * ((a : ZMod (m * n)) * x + 1)) (b := 0)
    simpa only [map_mul, map_add, map_natCast, map_one, map_zero, Prod.ext_iff,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_add, Prod.snd_add, Prod.fst_natCast,
      Prod.snd_natCast, Prod.fst_one, Prod.snd_one, Prod.fst_zero, Prod.snd_zero] using hi.symm
  let e' : {x : ZMod (m * n) // x * ((a : ZMod (m * n)) * x + 1) = 0} ≃
      {x : ZMod m × ZMod n // x.1 * ((a : ZMod m) * x.1 + 1) = 0 ∧
        x.2 * ((a : ZMod n) * x.2 + 1) = 0} := e.toEquiv.subtypeEquiv he
  have hc := Nat.card_congr (e'.trans (Equiv.subtypeProdEquivProd
    (p := fun x : ZMod m => x * ((a : ZMod m) * x + 1) = 0)
    (q := fun x : ZMod n => x * ((a : ZMod n) * x + 1) = 0)))
  simpa only [Nat.card_prod, quadraticRootCount] using hc

lemma quadraticRootCount_one (a : ℕ) : quadraticRootCount a 1 = 1 := by
  simp [quadraticRootCount, Subsingleton.elim (a : ZMod 1) 0,
    Subsingleton.elim (1 : ZMod 1) 0]

lemma quadraticRootCount_prime (a p : ℕ) (hp : p.Prime) (ha : ¬p ∣ a) :
    quadraticRootCount a p = 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff a p).not.mpr ha
  have hlinear (x : ZMod p) : (a : ZMod p) * x + 1 = 0 ↔ x = -(a : ZMod p)⁻¹ := by
    constructor
    · intro hx
      apply mul_left_cancel₀ ha0
      simpa only [mul_neg, mul_inv_cancel₀ ha0] using eq_neg_of_add_eq_zero_left hx
    · intro hx
      rw [hx]
      simp [ha0]
  have hset : {x : ZMod p | x * ((a : ZMod p) * x + 1) = 0} = {0, -(a : ZMod p)⁻¹} := by
    ext x
    simp only [Set.mem_setOf_eq, mul_eq_zero, hlinear, Set.mem_insert_iff, Set.mem_singleton_iff]
  change {x : ZMod p | x * ((a : ZMod p) * x + 1) = 0}.ncard = 2
  rw [hset]
  apply Set.ncard_pair
  exact fun h => ha0 (inv_eq_zero.mp (neg_eq_zero.mp h.symm))

lemma quadraticRootCount_prod_primes (a : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ a) :
    quadraticRootCount a (∏ p ∈ P, p) = 2 ^ P.card := by
  induction P using Finset.induction with
  | empty => simp only [Finset.prod_empty, Finset.card_empty, pow_zero, quadraticRootCount_one]
  | @insert p P hp ih =>
    have hpP := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime ∧ ¬q ∣ a := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr (by
      intro q hq
      exact (Nat.coprime_primes hpP.1 (hP' q hq).1).mpr
        (fun heq => hp (heq ▸ hq)))
    rw [Finset.prod_insert hp, quadraticRootCount_mul a p _ hcop,
      quadraticRootCount_prime a p hpP.1 hpP.2, ih hP', Finset.card_insert_of_notMem hp,
      pow_succ', Nat.mul_comm]

lemma card_quadratic_residues (a d : ℕ) (hd : 0 < d) :
    ((Finset.range d).filter (fun r => d ∣ r * (a * r + 1))).card = quadraticRootCount a d := by
  letI : NeZero d := ⟨hd.ne'⟩
  let B := (Finset.range d).filter (fun r => d ∣ r * (a * r + 1))
  have hcast (r : ℕ) : (r : ZMod d) * ((a : ZMod d) * r + 1) = 0 ↔ d ∣ r * (a * r + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      ZMod.natCast_eq_zero_iff (r * (a * r + 1)) d
  let e : {x : ZMod d // x * ((a : ZMod d) * x + 1) = 0} ≃ B := {
    toFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.val.val_lt,
      (hcast x.val.val).mp (by simpa only [ZMod.natCast_zmod_val] using x.property)⟩⟩
    invFun := fun r => ⟨(r.val : ZMod d), (hcast r.val).mpr (Finset.mem_filter.mp r.property).2⟩
    left_inv := fun x => Subtype.ext (ZMod.natCast_zmod_val x.val)
    right_inv := fun r => Subtype.ext (ZMod.val_natCast_of_lt
      (Finset.mem_range.mp (Finset.mem_filter.mp r.property).1)) }
  have hc := Nat.card_congr e
  simpa only [quadraticRootCount, Nat.card_eq_fintype_card, Fintype.card_coe, B] using hc.symm

lemma abs_card_quadratic_divisibility (N a d : ℕ) (hd : 0 < d) :
    |(((Finset.range N).filter (fun n => d ∣ n * (a * n + 1))).card : ℝ) -
      (N : ℝ) / d * quadraticRootCount a d| ≤ quadraticRootCount a d := by
  let B := (Finset.range d).filter (fun r => d ∣ r * (a * r + 1))
  have hB : ∀ r ∈ B, r < d := fun r hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hmem (n : ℕ) : n % d ∈ B ↔ d ∣ n * (a * n + 1) := by
    simp only [B, Finset.mem_filter, Finset.mem_range, Nat.mod_lt n hd, true_and,
      Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  have hfilter : (Finset.range N).filter (fun n => n % d ∈ B) =
      (Finset.range N).filter (fun n => d ∣ n * (a * n + 1)) := by
    ext n
    simp only [Finset.mem_filter, hmem]
  have hb := abs_card_residue_filter_sub N d hd B hB
  rw [hfilter, show B.card = quadraticRootCount a d from card_quadratic_residues a d hd] at hb
  exact hb

lemma prod_primes_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction P using Finset.induction with
    | empty => simp
    | @insert p P hp ih =>
      have hpP := hP p (Finset.mem_insert_self p P)
      have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr (by
        intro q hq
        exact (Nat.coprime_primes hpP (hP' q hq)).mpr (fun heq => hp (heq ▸ hq)))
      rw [Finset.prod_insert hp]
      exact hcop.mul_dvd_of_dvd_of_dvd (h p (Finset.mem_insert_self p P))
        (ih hP' (fun q hq => h q (Finset.mem_insert_of_mem hq)))

lemma abs_card_pair_conditions (N a : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ a) :
    |(((Finset.range N).filter (fun n => ∀ p ∈ P, p ∣ n * (a * n + 1))).card : ℝ) -
      (N : ℝ) * (∏ p ∈ P, (2 : ℝ) / p)| ≤ 2 ^ P.card := by
  let d := ∏ p ∈ P, p
  have hd : 0 < d := Finset.prod_pos (fun p hp => (hP p hp).1.pos)
  have hb := abs_card_quadratic_divisibility N a d hd
  have hfilter : (Finset.range N).filter (fun n => d ∣ n * (a * n + 1)) =
      (Finset.range N).filter (fun n => ∀ p ∈ P, p ∣ n * (a * n + 1)) := by
    ext n
    simp only [Finset.mem_filter, d, prod_primes_dvd_iff P (fun p hp => (hP p hp).1)]
  have hroot : quadraticRootCount a d = 2 ^ P.card := quadraticRootCount_prod_primes a P hP
  have hmain : (N : ℝ) / d * (2 ^ P.card : ℕ) = (N : ℝ) * ∏ p ∈ P, (2 : ℝ) / p := by
    simp only [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_pow, Nat.cast_ofNat,
      d, Nat.cast_prod]
    ring
  rw [hfilter, hroot, hmain, Nat.cast_pow, Nat.cast_ofNat] at hb
  exact hb

/-- The concrete finite sieve bound for simultaneous primality of `q` and `a*q+1`. -/
lemma prime_pair_sieve_bound (N a z : ℕ) (hz : 1 ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ z ∧ ¬p ∣ a) :
    (((Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime ∧
      z < q ∧ z < a * q + 1)).card : ℝ) ≤
      (N : ℝ) * (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹)⁻¹ + (z : ℝ) ^ 4 := by
  let bad : ℕ → ℕ → Prop := fun p q => p ∣ q * (a * q + 1)
  have hcount : ∀ S ∈ P.powerset,
      |(((Finset.range N).filter (fun q => ∀ p ∈ S, bad p q)).card : ℝ) -
        (N : ℝ) * (∏ p ∈ S, (2 : ℝ) / p)| ≤ ∏ _p ∈ S, (2 : ℝ) := by
    intro S hS
    rw [Finset.prod_const]
    exact abs_card_pair_conditions N a S (fun p hp =>
      ⟨(hP p (Finset.mem_powerset.mp hS hp)).1,
        (hP p (Finset.mem_powerset.mp hS hp)).2.2.2⟩)
  have hb := finite_selberg_bound (Finset.range N) P (fun p hp => (hP p hp).1)
    bad (fun _ => (2 : ℝ)) (fun p hp => ⟨by norm_num, by
      change (2 : ℝ) < p
      exact_mod_cast (hP p hp).2.1⟩)
    N z hz hcount
  apply le_trans ?_ hb
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqN, hqprime, hpairprime, hzq, hzaq⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨hqN, ?_⟩
  intro p hp hbad
  obtain ⟨hpprime, _, hpz, _⟩ := hP p hp
  rcases hpprime.dvd_mul.mp hbad with hdiv | hdiv
  · have heq := (Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp hdiv
    omega
  · have heq := (Nat.prime_dvd_prime_iff_eq hpprime hpairprime).mp hdiv
    omega

/-- The first moment of a product-weighted random subset. -/
lemma powerset_weighted_sum_moment {α : Type*} [DecidableEq α]
    (P : Finset α) (w f : α → ℝ) (hw : ∀ p ∈ P, 1 + w p ≠ 0) :
    (∑ S ∈ P.powerset, (∏ p ∈ S, w p) * (∑ p ∈ S, f p)) =
      (∏ p ∈ P, (1 + w p)) * ∑ p ∈ P, w p / (1 + w p) * f p := by
  induction P using Finset.induction with
  | empty => simp
  | @insert a P ha ih =>
    have hwa : 1 + w a ≠ 0 := hw a (Finset.mem_insert_self _ _)
    have hwP : ∀ p ∈ P, 1 + w p ≠ 0 := fun p hp => hw p (Finset.mem_insert_of_mem hp)
    have hsec : (∑ S ∈ P.powerset, (∏ p ∈ insert a S, w p) * (∑ p ∈ insert a S, f p)) =
        w a * f a * (∏ p ∈ P, (1 + w p)) +
          w a * (∑ S ∈ P.powerset, (∏ p ∈ S, w p) * (∑ p ∈ S, f p)) := by
      calc
        _ = ∑ S ∈ P.powerset, (w a * f a * (∏ p ∈ S, w p) +
            w a * ((∏ p ∈ S, w p) * (∑ p ∈ S, f p))) := by
          apply Finset.sum_congr rfl
          intro S hS
          have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
          rw [Finset.prod_insert haS, Finset.sum_insert haS]
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.prod_one_add]
    rw [Finset.sum_powerset_insert ha, hsec, ih hwP, Finset.prod_insert ha, Finset.sum_insert ha]
    field_simp
    ring

/-- A first-moment bound retains at least half of a finite Euler product below
a multiplicative level. -/
lemma half_euler_product_le_truncated_of_log_moment (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hw : ∀ p ∈ P, 0 ≤ w p)
    (z : ℕ) (hz : 1 < z)
    (hmoment : 2 * (∑ p ∈ P, w p / (1 + w p) * Real.log p) ≤ Real.log z) :
    (∏ p ∈ P, (1 + w p)) / 2 ≤
      ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z, ∏ p ∈ S, w p := by
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  let B := P.powerset.filter (fun S => ¬(∏ p ∈ S, p) ≤ z)
  let F := ∏ p ∈ P, (1 + w p)
  let M := ∑ p ∈ P, w p / (1 + w p) * Real.log p
  have hF : 0 ≤ F := Finset.prod_nonneg (fun p hp => add_nonneg zero_le_one (hw p hp))
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hweight (S : Finset ℕ) (hS : S ∈ P.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hS hp))
  have hlog (S : Finset ℕ) (hS : S ∈ P.powerset) :
      (∑ p ∈ S, Real.log p) = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (show p ≠ 0 by have := hP p (Finset.mem_powerset.mp hS hp); omega)
  have hlognonneg (S : Finset ℕ) (hS : S ∈ P.powerset) :
      0 ≤ ∑ p ∈ S, Real.log p :=
    Finset.sum_nonneg (fun p hp => Real.log_nonneg
      (by exact_mod_cast hP p (Finset.mem_powerset.mp hS hp)))
  have htail : Real.log z * (∑ S ∈ B, ∏ p ∈ S, w p) ≤ F * M := by
    calc
      Real.log z * (∑ S ∈ B, ∏ p ∈ S, w p) =
          ∑ S ∈ B, (∏ p ∈ S, w p) * Real.log z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ ≤ ∑ S ∈ B, (∏ p ∈ S, w p) * (∑ p ∈ S, Real.log p) := by
        apply Finset.sum_le_sum
        intro S hS
        obtain ⟨hSP, hSz⟩ := Finset.mem_filter.mp hS
        apply mul_le_mul_of_nonneg_left ?_ (hweight S hSP)
        rw [hlog S hSP]
        exact Real.log_le_log (by exact_mod_cast (show 0 < z by omega))
          (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hSz)))
      _ ≤ ∑ S ∈ P.powerset, (∏ p ∈ S, w p) * (∑ p ∈ S, Real.log p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S hS _ => mul_nonneg (hweight S hS) (hlognonneg S hS))
      _ = F * M := powerset_weighted_sum_moment P w (fun p => Real.log p)
        (fun p hp => ne_of_gt (lt_of_lt_of_le zero_lt_one (by linarith [hw p hp])))
  have htotal : (∑ S ∈ W, ∏ p ∈ S, w p) + (∑ S ∈ B, ∏ p ∈ S, w p) = F := by
    rw [Finset.sum_filter_add_sum_filter_not, ← Finset.prod_one_add]
  have hM : 2 * M ≤ Real.log z := hmoment
  have hmul := mul_le_mul_of_nonneg_left hM hF
  change F / 2 ≤ ∑ S ∈ W, ∏ p ∈ S, w p
  nlinarith

lemma theta_nat_eq_sum_primesBelow (n : ℕ) :
    Chebyshev.theta (n : ℝ) = ∑ p ∈ (n + 1).primesBelow, Real.log p := by
  rw [Chebyshev.theta, Nat.floor_natCast]
  have hfin : (Finset.Ioc 0 n).filter Nat.Prime = (n + 1).primesBelow := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by have := (Finset.mem_Ioc.mp hpI).2; omega, hprime⟩
    · intro hp
      obtain ⟨hpn, hprime⟩ := Nat.mem_primesBelow.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hprime.pos, by omega⟩, hprime⟩
  rw [hfin]

/-- A convenient dyadic Mertens-type upper bound, obtained just from
Chebyshev's upper bound. -/
lemma sum_prime_log_div_dyadic_le (L : ℕ) :
    (∑ p ∈ (2 ^ L + 1).primesBelow, Real.log ((p : ℕ) : ℝ) / (p : ℝ)) ≤
      2 * Real.log 4 * L := by
  induction L with
  | zero => norm_num [Nat.primesBelow, Finset.sum_filter, Finset.sum_range_succ]
  | succ L ih =>
    let P := (2 ^ L + 1).primesBelow
    let Q := (2 ^ (L + 1) + 1).primesBelow
    have hPQ : P ⊆ Q := by
      intro p hp
      obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hp
      have hpow : 2 ^ L ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    have hlognonneg (p : ℕ) (hp : p ∈ Q) : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt.le)
    have hblock : (∑ p ∈ Q \ P, Real.log (p : ℝ) / (p : ℝ)) ≤ 2 * Real.log 4 := by
      calc
        (∑ p ∈ Q \ P, Real.log (p : ℝ) / (p : ℝ)) ≤
            ∑ p ∈ Q \ P, Real.log (p : ℝ) / (2 : ℝ) ^ L := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpQ, hpP⟩ := Finset.mem_sdiff.mp hp
          have hprime := (Nat.mem_primesBelow.mp hpQ).2
          have hple : 2 ^ L ≤ p := by
            by_contra h
            exact hpP (Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩)
          exact div_le_div_of_nonneg_left (hlognonneg p hpQ) hpowpos (by exact_mod_cast hple)
        _ = (∑ p ∈ Q \ P, Real.log (p : ℝ)) / (2 : ℝ) ^ L := (Finset.sum_div _ _ _).symm
        _ ≤ (∑ p ∈ Q, Real.log (p : ℝ)) / (2 : ℝ) ^ L := by
          apply div_le_div_of_nonneg_right ?_ hpowpos.le
          exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
            (fun p hp _ => hlognonneg p hp)
        _ = Chebyshev.theta ((2 ^ (L + 1) : ℕ) : ℝ) / (2 : ℝ) ^ L := by
          rw [theta_nat_eq_sum_primesBelow]
        _ ≤ (Real.log 4 * ((2 ^ (L + 1) : ℕ) : ℝ)) / (2 : ℝ) ^ L :=
          div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)) hpowpos.le
        _ = 2 * Real.log 4 := by
          push_cast
          rw [pow_succ]
          field_simp
    have heq : (∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ)) =
        (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) + (∑ p ∈ Q \ P, Real.log (p : ℝ) / (p : ℝ)) := by
      exact (Finset.sum_sdiff hPQ).symm.trans (add_comm _ _)
    change (∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ)) ≤ _
    rw [heq]
    have hb := add_le_add ih hblock
    push_cast
    nlinarith

lemma pair_sieve_weight_eq (p : ℕ) :
    (((2 : ℝ) / p)⁻¹ - 1)⁻¹ = 2 / ((p : ℝ) - 2) := by
  rw [inv_div, show (p : ℝ) / 2 - 1 = ((p : ℝ) - 2) / 2 by ring, inv_div]

/-- Restricting the sifting primes to `2^L` retains half the full Euler product
at level `2^(16L)`. -/
lemma pair_sieve_denominator_ge_half_product (L : ℕ) (hL : 0 < L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ 2 ^ L) :
    (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 2)) / 2 ≤
      ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ 2 ^ (16 * L),
        (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹ := by
  let w : ℕ → ℝ := fun p => 2 / ((p : ℝ) - 2)
  have hpR (p : ℕ) (hp : p ∈ P) : (2 : ℝ) < p := by exact_mod_cast (hP p hp).2.1
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p := div_nonneg (by norm_num) (by linarith [hpR p hp])
  have hquot (p : ℕ) (hp : p ∈ P) : w p / (1 + w p) = 2 / (p : ℝ) := by
    dsimp [w]
    have hden : (p : ℝ) - 2 ≠ 0 := by linarith [hpR p hp]
    have hp0 : (p : ℝ) ≠ 0 := by linarith [hpR p hp]
    field_simp [hden, hp0]
    ring
  have hfull (p : ℕ) (hp : p ∈ P) : 1 + w p = (p : ℝ) / ((p : ℝ) - 2) := by
    dsimp [w]
    have hden : (p : ℝ) - 2 ≠ 0 := by linarith [hpR p hp]
    field_simp
    ring
  have hsub : P ⊆ (2 ^ L + 1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr ⟨by have := (hP p hp).2.2; omega, (hP p hp).1⟩
  have hsum : (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤ 2 * Real.log 4 * L := by
    apply le_trans ?_ (sum_prime_log_div_dyadic_le L)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt.le))
      (Nat.cast_nonneg p)
  have hmoment : 2 * (∑ p ∈ P, w p / (1 + w p) * Real.log p) ≤
      Real.log ((2 ^ (16 * L) : ℕ) : ℝ) := by
    have heq : (∑ p ∈ P, w p / (1 + w p) * Real.log p) =
        2 * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hquot p hp]
      ring
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    rw [hlog4] at hsum
    nlinarith
  have hhalf := half_euler_product_le_truncated_of_log_moment P w
    (fun p hp => (hP p hp).1.one_lt.le) hw (2 ^ (16 * L))
    (one_lt_pow₀ (by decide) (by omega)) hmoment
  have hprod : (∏ p ∈ P, (1 + w p)) = ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 2) :=
    Finset.prod_congr rfl hfull
  rw [hprod] at hhalf
  simpa only [← Finset.prod_inv_distrib, pair_sieve_weight_eq, w] using hhalf

/-- The finite prime Euler product dominates the harmonic sum. -/
lemma harmonic_le_prime_euler_product (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ (N + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  let f : ℕ →* ℝ := {
    toFun := fun n => (n : ℝ)⁻¹
    map_one' := by simp
    map_mul' := by intro a b; simp only [Nat.cast_mul, mul_inv] }
  have hsmall {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hsmall (N + 1)).2
  have hind := hasSum_subtype_iff_indicator.mp hsum
  have hmem (d : ℕ) (hd : d ∈ Finset.Icc 1 N) : d ∈ Nat.smoothNumbers (N + 1) := by
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpd
    have hpdle := Nat.le_of_dvd (by omega : 0 < d) hpd
    omega
  calc
    (harmonic N : ℝ) = ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ = ∑ d ∈ Finset.Icc 1 N, (Nat.smoothNumbers (N + 1)).indicator f d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (Set.indicator_of_mem (hmem d hd) f).symm
    _ ≤ ∑' d, (Nat.smoothNumbers (N + 1)).indicator f d :=
      Summable.sum_le_tsum _ (fun d _ => Set.indicator_nonneg
        (fun d _ => inv_nonneg.mpr (Nat.cast_nonneg d)) _) hind.summable
    _ = _ := hind.tsum_eq

lemma prod_inv_mul_prod_le_sdiff {α : Type*} [DecidableEq α]
    (Q R : Finset α) (f : α → ℝ) (hf : ∀ p ∈ Q ∪ R, 0 < f p ∧ f p ≤ 1) :
    (∏ p ∈ Q, (f p)⁻¹) * (∏ p ∈ R, f p) ≤ ∏ p ∈ Q \ R, (f p)⁻¹ := by
  have hext (S : Finset α) (hS : S ⊆ Q ∪ R) (g : α → ℝ) :
      (∏ p ∈ S, g p) = ∏ p ∈ Q ∪ R, if p ∈ S then g p else 1 := by
    rw [← Finset.prod_filter]
    have hfilter : (Q ∪ R).filter (fun p => p ∈ S) = S := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun hp => hp.2, fun hp => ⟨hS hp, hp⟩⟩
    rw [hfilter]
  rw [hext Q Finset.subset_union_left, hext R Finset.subset_union_right,
    hext (Q \ R) (Finset.sdiff_subset.trans Finset.subset_union_left), ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    have hpos := (hf p hp).1
    split_ifs <;> positivity
  · intro p hp
    obtain ⟨hpos, hle⟩ := hf p hp
    by_cases hpQ : p ∈ Q <;> by_cases hpR : p ∈ R
    · simp [hpQ, hpR, hpos.ne']
    · simp [hpQ, hpR]
    · simpa [hpQ, hpR] using hle
    · simp [hpQ, hpR]

lemma harmonic_mul_totient_ratio_le_euler_product (N M : ℕ) (hM : 0 < M) :
    (harmonic N : ℝ) * ((Nat.totient M : ℝ) / M) ≤
      ∏ p ∈ (N + 1).primesBelow \ M.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  let f : ℕ → ℝ := fun p => 1 - (p : ℝ)⁻¹
  have hf (p : ℕ) (hp : p.Prime) : 0 < f p ∧ f p ≤ 1 := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hpR
    have hnonneg : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
    dsimp [f]
    constructor <;> linarith
  have hphi : (Nat.totient M : ℝ) = (M : ℝ) * ∏ p ∈ M.primeFactors, f p := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    push_cast at h
    exact h
  have hratio : (Nat.totient M : ℝ) / M = ∏ p ∈ M.primeFactors, f p := by
    rw [hphi]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hM.ne')
  rw [hratio]
  calc
    (harmonic N : ℝ) * (∏ p ∈ M.primeFactors, f p) ≤
        (∏ p ∈ (N + 1).primesBelow, (f p)⁻¹) * (∏ p ∈ M.primeFactors, f p) :=
      mul_le_mul_of_nonneg_right (harmonic_le_prime_euler_product N)
        (Finset.prod_nonneg (fun p hp => (hf p (Nat.prime_of_mem_primeFactors hp)).1.le))
    _ ≤ _ := prod_inv_mul_prod_le_sdiff _ _ f (by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hf p (Nat.mem_primesBelow.mp hp).2
      · exact hf p (Nat.prime_of_mem_primeFactors hp))

lemma prime_euler_product_sq_le_pair_product (P : Finset ℕ) (hP : ∀ p ∈ P, 2 < p) :
    (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) ^ 2 ≤ ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 2) := by
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p _
    exact sq_nonneg _
  · intro p hp
    have hpR : (2 : ℝ) < p := by exact_mod_cast hP p hp
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have heq : (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
      rw [show 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p by field_simp, inv_div]
    rw [heq, div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith)) (by linarith)).mpr
    nlinarith

/-- A logarithmic lower bound for the concrete two-dimensional sieve denominator. -/
lemma pair_sieve_denominator_log_lower (L M : ℕ) (hL : 0 < L) (hM : 0 < M)
    (h2M : 2 ∣ M) :
    let P := (2 ^ L + 1).primesBelow \ M.primeFactors
    ((Nat.totient M : ℝ) / M * (L : ℝ) * Real.log 2) ^ 2 / 2 ≤
      ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ 2 ^ (16 * L),
        (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹ := by
  dsimp only
  let P := (2 ^ L + 1).primesBelow \ M.primeFactors
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 2 < p ∧ p ≤ 2 ^ L := by
    obtain ⟨hpQ, hpM⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hpM (Nat.prime_two.mem_primeFactors h2M hM.ne')
    exact ⟨hprime, by have := hprime.two_le; omega, by omega⟩
  have hratio : 0 ≤ (Nat.totient M : ℝ) / M := by positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH : ((Nat.totient M : ℝ) / M * L * Real.log 2) ≤
      (harmonic (2 ^ L) : ℝ) * ((Nat.totient M : ℝ) / M) := by
    have hlog : (L : ℝ) * Real.log 2 ≤ (harmonic (2 ^ L) : ℝ) := by
      have h := log_le_harmonic_floor (y := ((2 ^ L : ℕ) : ℝ)) (Nat.cast_nonneg _)
      rw [Nat.floor_natCast] at h
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
    have hmul := mul_le_mul_of_nonneg_right hlog hratio
    nlinarith
  have hE := hH.trans (harmonic_mul_totient_ratio_le_euler_product (2 ^ L) M hM)
  have hsq : ((Nat.totient M : ℝ) / M * L * Real.log 2) ^ 2 ≤
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg hratio (Nat.cast_nonneg L)) hlog2) hE 2
  exact (div_le_div_of_nonneg_right
    (hsq.trans (prime_euler_product_sq_le_pair_product P (fun p hp => (hP p hp).2.1)))
      (by norm_num)).trans (pair_sieve_denominator_ge_half_product L hL P hP)

/-- An explicit unconditional upper bound for simultaneous primality of
`q` and `a*q+1`, including the small-prime exceptions. -/
lemma prime_pair_explicit_bound (N a L : ℕ) (ha : 0 < a) (hL : 0 < L) :
    (((Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card : ℝ) ≤
      2 * (N : ℝ) /
        (((Nat.totient (2 * a) : ℝ) / (2 * a) * L * Real.log 2) ^ 2) +
      (2 : ℝ) ^ (64 * L) + (2 : ℝ) ^ (16 * L) + 1 := by
  let z := 2 ^ (16 * L)
  let P := (2 ^ L + 1).primesBelow \ (2 * a).primeFactors
  have hM : 0 < 2 * a := by omega
  have hz : 1 ≤ z := Nat.one_le_pow _ _ (by decide)
  have hyz : 2 ^ L ≤ z := Nat.pow_le_pow_right (by decide) (by omega)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 2 < p ∧ p ≤ z ∧ ¬p ∣ a := by
    obtain ⟨hpQ, hpM⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hpM (Nat.prime_two.mem_primeFactors (dvd_mul_right 2 a) hM.ne')
    refine ⟨hprime, by have := hprime.two_le; omega, by omega, ?_⟩
    intro hpa
    exact hpM (hprime.mem_primeFactors (dvd_mul_of_dvd_right hpa 2) hM.ne')
  let G := ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
    (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹
  let B : ℝ := (Nat.totient (2 * a) : ℝ) / (2 * a) * L * Real.log 2
  have hB : 0 < B := by
    apply mul_pos
    · apply mul_pos
      · exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hM) (by positivity)
      · exact_mod_cast hL
    · exact Real.log_pos (by norm_num)
  have hG : B ^ 2 / 2 ≤ G := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      pair_sieve_denominator_log_lower L (2 * a) hL hM (dvd_mul_right 2 a)
  have hGpos : 0 < G := (div_pos (sq_pos_of_pos hB) (by norm_num)).trans_le hG
  have hInv : G⁻¹ ≤ 2 / B ^ 2 := by
    rw [← inv_div]
    exact (inv_le_inv₀ hGpos (div_pos (sq_pos_of_pos hB) (by norm_num))).mpr hG
  have hb := prime_pair_sieve_bound N a z hz P hP
  let T := (Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime ∧
    z < q ∧ z < a * q + 1)
  have hT : (T.card : ℝ) ≤ 2 * (N : ℝ) / B ^ 2 + (z : ℝ) ^ 4 := by
    calc
      (T.card : ℝ) ≤ (N : ℝ) * G⁻¹ + (z : ℝ) ^ 4 := hb
      _ ≤ (N : ℝ) * (2 / B ^ 2) + (z : ℝ) ^ 4 :=
        add_le_add (mul_le_mul_of_nonneg_left hInv (Nat.cast_nonneg N)) le_rfl
      _ = _ := by ring
  let S := (Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime)
  have hsub : S ⊆ T ∪ Finset.range (z + 1) := by
    intro q hq
    obtain ⟨hqN, hqp, haqp⟩ := Finset.mem_filter.mp hq
    by_cases hzq : z < q
    · apply Finset.mem_union_left
      have hqaq : q ≤ a * q := Nat.le_mul_of_pos_left _ ha
      exact Finset.mem_filter.mpr ⟨hqN, hqp, haqp, hzq, by omega⟩
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  have hcard : S.card ≤ T.card + (z + 1) := by
    simpa only [Finset.card_range] using (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hzpow : (z : ℝ) ^ 4 = (2 : ℝ) ^ (64 * L) := by
    dsimp [z]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    congr 1
    ring
  calc
    (S.card : ℝ) ≤ (T.card : ℝ) + ((z + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (2 * (N : ℝ) / B ^ 2 + (z : ℝ) ^ 4) + ((z + 1 : ℕ) : ℝ) :=
      add_le_add hT le_rfl
    _ = _ := by rw [hzpow]; dsimp [B, z]; push_cast; ring

lemma sum_inv_multiples_le_harmonic (A d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 A with d ∣ n, (n : ℝ)⁻¹) ≤ (d : ℝ)⁻¹ * (harmonic A : ℝ) := by
  let E := (Finset.Icc 1 A).filter (fun n => d ∣ n)
  have hinj : Set.InjOn (fun n : ℕ => n / d) (↑E : Set ℕ) := by
    intro n hn m hm h
    change n ∈ E at hn
    change m ∈ E at hm
    have hdn := (Finset.mem_filter.mp hn).2
    have hdm := (Finset.mem_filter.mp hm).2
    change n / d = m / d at h
    rw [← Nat.mul_div_cancel' hdn, ← Nat.mul_div_cancel' hdm, h]
  have hsub : E.image (fun n => n / d) ⊆ Finset.Icc 1 A := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnA⟩ := Finset.mem_Icc.mp hnI
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd,
      (Nat.div_le_self _ _).trans hnA⟩
  have hH : (∑ n ∈ Finset.Icc 1 A, (n : ℝ)⁻¹) = (harmonic A : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  calc
    (∑ n ∈ E, (n : ℝ)⁻¹) = ∑ n ∈ E, (d : ℝ)⁻¹ * ((n / d : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      nth_rw 1 [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
      rw [Nat.cast_mul, mul_inv]
    _ = (d : ℝ)⁻¹ * ∑ m ∈ E.image (fun n => n / d), (m : ℝ)⁻¹ := by
      rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (d : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 A, (m : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)) (by positivity)
    _ = _ := by rw [hH]

/-- A harmonic average of a multiplicative prime-factor weight is bounded by
another finite Euler product. -/
lemma harmonic_average_prime_product_le (A : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ (A + 1).primesBelow, 0 ≤ w p) :
    (∑ n ∈ Finset.Icc 1 A, (∏ p ∈ n.primeFactors, (1 + w p)) / (n : ℝ)) ≤
      (harmonic A : ℝ) * ∏ p ∈ (A + 1).primesBelow, (1 + w p / (p : ℝ)) := by
  let Q := (A + 1).primesBelow
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have hsub (n : ℕ) (hn : n ∈ Finset.Icc 1 A) : n.primeFactors ⊆ Q := by
    intro p hp
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hpn := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.mem_primesBelow.mpr ⟨by have := (Finset.mem_Icc.mp hn).2; omega,
      Nat.prime_of_mem_primeFactors hp⟩
  have hexpand (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      (∏ p ∈ n.primeFactors, (1 + w p)) =
        ∑ S ∈ Q.powerset, if (∏ p ∈ S, p) ∣ n then ∏ p ∈ S, w p else 0 := by
    have hfilter : Q.powerset.filter (fun S => (∏ p ∈ S, p) ∣ n) = n.primeFactors.powerset := by
      ext S
      constructor
      · intro hS
        obtain ⟨hSQ, hdiv⟩ := Finset.mem_filter.mp hS
        apply Finset.mem_powerset.mpr
        intro p hp
        have hpQ := Finset.mem_powerset.mp hSQ hp
        exact (hQ p hpQ).mem_primeFactors ((Finset.dvd_prod_of_mem id hp).trans hdiv)
          (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
      · intro hS
        have hSn := Finset.mem_powerset.mp hS
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hSn.trans (hsub n hn)), ?_⟩
        exact (prod_primes_dvd_iff S (fun p hp => Nat.prime_of_mem_primeFactors (hSn hp)) n).mpr
          (fun p hp => Nat.dvd_of_mem_primeFactors (hSn hp))
    rw [← Finset.sum_filter, hfilter, ← Finset.prod_one_add]
  have hweight (S : Finset ℕ) (hS : S ∈ Q.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hS hp))
  calc
    (∑ n ∈ Finset.Icc 1 A, (∏ p ∈ n.primeFactors, (1 + w p)) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 A, ∑ S ∈ Q.powerset,
          (∏ p ∈ S, w p) * (if (∏ p ∈ S, p) ∣ n then (n : ℝ)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hexpand n hn, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs <;> simp [div_eq_mul_inv]
    _ = ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        ∑ n ∈ Finset.Icc 1 A with (∏ p ∈ S, p) ∣ n, (n : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter, Finset.mul_sum]
    _ ≤ ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        (((∏ p ∈ S, p : ℕ) : ℝ)⁻¹ * (harmonic A : ℝ)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply mul_le_mul_of_nonneg_left ?_ (hweight S hS)
      exact sum_inv_multiples_le_harmonic A _
        (Finset.prod_pos (fun p hp => (hQ p (Finset.mem_powerset.mp hS hp)).pos))
    _ = (harmonic A : ℝ) * ∑ S ∈ Q.powerset, ∏ p ∈ S, w p / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_div_distrib, Nat.cast_prod]
      ring
    _ = _ := by rw [← Finset.prod_one_add]

lemma centralBinom_le_pow_primesBelow (m : ℕ) (hm : 0 < m) :
    Nat.centralBinom m ≤ (2 * m) ^ (2 * m + 1).primesBelow.card := by
  have hprod : Nat.centralBinom m =
      ∏ p ∈ (2 * m + 1).primesBelow, p ^ (Nat.centralBinom m).factorization p := by
    nth_rw 1 [← Nat.prod_pow_factorization_centralBinom m]
    rw [Nat.primesBelow, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    split_ifs with hprime
    · rfl
    · simp [Nat.factorization_eq_zero_of_not_prime _ hprime]
  rw [hprod]
  apply Finset.prod_le_pow_card
  intro p hp
  exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * m)

/-- An elementary Chebyshev lower bound on dyadic scales, in an integer form. -/
lemma dyadic_prime_count_lower (L : ℕ) :
    2 ^ (L + 1) ≤ (L + 1) * ((2 ^ (L + 1) + 1).primesBelow.card + 1) := by
  let m := 2 ^ L
  have hm : 0 < m := by dsimp [m]; positivity
  have htwo : 2 * m = 2 ^ (L + 1) := by dsimp [m]; rw [pow_succ]; ring
  have hbound : 4 ^ m ≤ (2 * m) ^ ((2 * m + 1).primesBelow.card + 1) := by
    calc
      4 ^ m ≤ 2 * m * Nat.centralBinom m := Nat.four_pow_le_two_mul_self_mul_centralBinom m hm
      _ ≤ 2 * m * ((2 * m) ^ (2 * m + 1).primesBelow.card) :=
        Nat.mul_le_mul_left _ (centralBinom_le_pow_primesBelow m hm)
      _ = _ := (pow_succ' _ _).symm
  rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, htwo, ← pow_mul] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide)).mp hbound

noncomputable def totientRatioAverageConstant : ℝ :=
  Real.exp (8 * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹)

lemma totient_ratio_eq_prime_product (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / Nat.totient n = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hphi : (Nat.totient n : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  rw [hphi, div_mul_eq_div_div, div_self (by exact_mod_cast hn.ne'), one_div,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
  rw [show 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p by field_simp, inv_div]

lemma totient_ratio_harmonic_average (A : ℕ) :
    (∑ n ∈ Finset.Icc 1 A, ((n : ℝ) / Nat.totient n) ^ 2 / (n : ℝ)) ≤
      totientRatioAverageConstant * (harmonic A : ℝ) := by
  let w : ℕ → ℝ := fun p => ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1
  let Q := (A + 1).primesBelow
  have hw (p : ℕ) (hp : p.Prime) : 0 ≤ w p ∧ w p ≤ 8 / (p : ℝ) := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpm1 : 0 < (p : ℝ) - 1 := by linarith
    have hge : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := (one_le_div hpm1).mpr (by linarith)
    refine ⟨by dsimp [w]; nlinarith, ?_⟩
    have heq : w p = (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
      dsimp [w]
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hpm1) hp0).mpr
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hseries : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by decide)
  have hsum : (∑ p ∈ Q, w p / (p : ℝ)) ≤ 8 * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
    calc
      (∑ p ∈ Q, w p / (p : ℝ)) ≤ ∑ p ∈ Q, 8 * ((p : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := div_le_div_of_nonneg_right (hw p (Nat.mem_primesBelow.mp hp).2).2 (Nat.cast_nonneg p)
        convert h using 1 <;> ring
      _ = 8 * ∑ p ∈ Q, ((p : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun p _ => by positivity) hseries) (by norm_num)
  have hprod : (∏ p ∈ Q, (1 + w p / (p : ℝ))) ≤ totientRatioAverageConstant := by
    calc
      _ ≤ ∏ p ∈ Q, Real.exp (w p / (p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact add_nonneg zero_le_one (div_nonneg (hw p (Nat.mem_primesBelow.mp hp).2).1
            (Nat.cast_nonneg p))
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (w p / (p : ℝ))
      _ = Real.exp (∑ p ∈ Q, w p / (p : ℝ)) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  have havg := harmonic_average_prime_product_le A w
    (fun p hp => (hw p (Nat.mem_primesBelow.mp hp).2).1)
  have heq (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      ((n : ℝ) / Nat.totient n) ^ 2 = ∏ p ∈ n.primeFactors, (1 + w p) := by
    rw [totient_ratio_eq_prime_product n (Finset.mem_Icc.mp hn).1, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [w]
    ring
  have hH : 0 ≤ (harmonic A : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    (∑ n ∈ Finset.Icc 1 A, ((n : ℝ) / Nat.totient n) ^ 2 / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 A, (∏ p ∈ n.primeFactors, (1 + w p)) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [heq n hn]
    _ ≤ (harmonic A : ℝ) * ∏ p ∈ Q, (1 + w p / (p : ℝ)) := havg
    _ ≤ (harmonic A : ℝ) * totientRatioAverageConstant := mul_le_mul_of_nonneg_left hprod hH
    _ = _ := mul_comm _ _

lemma totient_ratio_two_mul_sq_le (a : ℕ) (ha : 0 < a) :
    ((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2 ≤ 4 * ((a : ℝ) / Nat.totient a) ^ 2 := by
  have hφa : (0 : ℝ) < Nat.totient a := by exact_mod_cast Nat.totient_pos.mpr ha
  have hφ2a : (0 : ℝ) < Nat.totient (2 * a) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < 2 * a by omega)
  have hφle : (Nat.totient a : ℝ) ≤ Nat.totient (2 * a) := by
    exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr (show 0 < 2 * a by omega))
      (Nat.totient_dvd_of_dvd (dvd_mul_left a 2))
  have hratio : 2 * (a : ℝ) / Nat.totient (2 * a) ≤ 2 * ((a : ℝ) / Nat.totient a) := by
    have h := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Nat.cast_nonneg a) hφa hφle) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc] using h
  have hsq := pow_le_pow_left₀ (by positivity) hratio 2
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq

lemma totient_ratio_two_mul_harmonic_average (A : ℕ) :
    (∑ a ∈ Finset.Icc 1 A, ((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2 / (a : ℝ)) ≤
      (4 * totientRatioAverageConstant) * (harmonic A : ℝ) := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 A, 4 * (((a : ℝ) / Nat.totient a) ^ 2 / (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      have h := div_le_div_of_nonneg_right
        (totient_ratio_two_mul_sq_le a (Finset.mem_Icc.mp ha).1) (Nat.cast_nonneg a)
      simpa only [mul_div_assoc] using h
    _ = 4 * ∑ a ∈ Finset.Icc 1 A, ((a : ℝ) / Nat.totient a) ^ 2 / (a : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * (totientRatioAverageConstant * (harmonic A : ℝ)) :=
      mul_le_mul_of_nonneg_left (totient_ratio_harmonic_average A) (by norm_num)
    _ = _ := by ring

lemma sum_prime_pair_explicit_bound (X A L : ℕ) (hAX : A ≤ X) (hL : 0 < L) :
    (∑ a ∈ Finset.Icc 1 A,
      (((Finset.range (X / a + 1)).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card : ℝ)) ≤
      16 * totientRatioAverageConstant * X * (harmonic A : ℝ) / ((L : ℝ) * Real.log 2) ^ 2 +
        (A : ℝ) * ((2 : ℝ) ^ (64 * L) + (2 : ℝ) ^ (16 * L) + 1) := by
  let D : ℝ := ((L : ℝ) * Real.log 2) ^ 2
  let E : ℝ := (2 : ℝ) ^ (64 * L) + (2 : ℝ) ^ (16 * L) + 1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hL) (Real.log_pos (by norm_num)))
  have hbound (a : ℕ) (ha : a ∈ Finset.Icc 1 A) :
      (((Finset.range (X / a + 1)).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card : ℝ) ≤
        (4 * (X : ℝ) / D) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2 / (a : ℝ)) + E := by
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have haX : a ≤ X := (Finset.mem_Icc.mp ha).2.trans hAX
    have haR : (0 : ℝ) < a := by exact_mod_cast ha0
    have hN : ((X / a + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) / a := by
      calc
        ((X / a + 1 : ℕ) : ℝ) = ((X / a : ℕ) : ℝ) + 1 := by push_cast; rfl
        _ ≤ (X : ℝ) / a + 1 := add_le_add (Nat.cast_div_le) le_rfl
        _ ≤ (X : ℝ) / a + (X : ℝ) / a :=
          add_le_add le_rfl ((one_le_div haR).mpr (by exact_mod_cast haX))
        _ = _ := by ring
    have hb := prime_pair_explicit_bound (X / a + 1) a L ha0 hL
    have heq : 2 * ((X / a + 1 : ℕ) : ℝ) /
        (((Nat.totient (2 * a) : ℝ) / (2 * a) * L * Real.log 2) ^ 2) =
          2 * ((X / a + 1 : ℕ) : ℝ) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2) / D := by
      dsimp [D]
      simp only [mul_pow, div_pow, div_eq_mul_inv, mul_inv, inv_pow, inv_inv]
      ring
    rw [heq] at hb
    calc
      _ ≤ 2 * ((X / a + 1 : ℕ) : ℝ) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2) / D + E := by
        simpa only [E, add_assoc] using hb
      _ ≤ 2 * (2 * (X : ℝ) / a) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2) / D + E := by
        apply add_le_add ?_ le_rfl
        apply div_le_div_of_nonneg_right ?_ hD.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 A,
        ((4 * (X : ℝ) / D) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2 / (a : ℝ)) + E) :=
      Finset.sum_le_sum hbound
    _ = (4 * (X : ℝ) / D) *
        (∑ a ∈ Finset.Icc 1 A, (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2 / (a : ℝ))) +
        (A : ℝ) * E := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ (4 * (X : ℝ) / D) * ((4 * totientRatioAverageConstant) * (harmonic A : ℝ)) + (A : ℝ) * E :=
      add_le_add (mul_le_mul_of_nonneg_left (totient_ratio_two_mul_harmonic_average A) (by positivity)) le_rfl
    _ = _ := by dsimp [D, E]; ring

/-- Every prime whose predecessor is not `Y`-smooth yields a prime pair
`q, a*q+1` with small cofactor `a`. -/
lemma rough_shifted_prime_card_le_pairs (X A Y : ℕ) (hY : 0 < Y) (hX : X ≤ A * Y) :
    (((X + 1).primesBelow).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)).card ≤
      ∑ a ∈ Finset.Icc 1 A,
        ((Finset.range (X / a + 1)).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card := by
  classical
  let Q : ℕ → Finset ℕ := fun a =>
    (Finset.range (X / a + 1)).filter (fun q => q.Prime ∧ (a * q + 1).Prime)
  let R := ((X + 1).primesBelow).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)
  have hsub : R ⊆ (Finset.Icc 1 A).biUnion (fun a => (Q a).image (fun q => a * q + 1)) := by
    intro p hp
    obtain ⟨hpQ, hpns⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpQ
    have hpred : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
    have hnot : ¬∀ q, q.Prime → q ∣ p - 1 → q < Y := fun h => hpns (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hnot
    obtain ⟨q, hq, hqd, hYq⟩ := hnot
    let a := (p - 1) / q
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hpred hqd) hq.pos
    have heq : a * q = p - 1 := Nat.div_mul_cancel hqd
    have hple : p - 1 ≤ X := by omega
    have haA : a ≤ A := by
      have hmul : a * Y ≤ A * Y := (Nat.mul_le_mul_left a hYq).trans
        (heq ▸ hple.trans hX)
      nlinarith
    have hqX : q ≤ X / a := (Nat.le_div_iff_mul_le ha).mpr (by nlinarith [hple])
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha, haA⟩, Finset.mem_image.mpr ⟨q, ?_, by omega⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), hq, ?_⟩
    have hp2 := hprime.two_le
    convert hprime using 1 <;> omega
  calc
    R.card ≤ ((Finset.Icc 1 A).biUnion (fun a => (Q a).image (fun q => a * q + 1))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ a ∈ Finset.Icc 1 A, ((Q a).image (fun q => a * q + 1)).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Icc 1 A, (Q a).card :=
      Finset.sum_le_sum (fun a _ => Finset.card_image_le)

lemma rough_shifted_prime_explicit_bound (X A Y L : ℕ)
    (hY : 0 < Y) (hX : X ≤ A * Y) (hAX : A ≤ X) (hL : 0 < L) :
    ((((X + 1).primesBelow).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)).card : ℝ) ≤
      16 * totientRatioAverageConstant * X * (harmonic A : ℝ) / ((L : ℝ) * Real.log 2) ^ 2 +
        (A : ℝ) * ((2 : ℝ) ^ (64 * L) + (2 : ℝ) ^ (16 * L) + 1) := by
  have hcard : ((((X + 1).primesBelow).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)).card : ℝ) ≤
      ∑ a ∈ Finset.Icc 1 A,
        (((Finset.range (X / a + 1)).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card : ℝ) := by
    exact_mod_cast rough_shifted_prime_card_le_pairs X A Y hY hX
  exact hcard.trans (sum_prime_pair_explicit_bound X A L hAX hL)

lemma sq_le_two_pow (L : ℕ) (hL : 4 ≤ L) : L ^ 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    calc
      (L + 1) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [pow_succ]; ring

set_option maxHeartbeats 2000000 in
/-- A fully unconditional supply of primes with predecessors smooth at a
fixed power slightly below one. The large numerical constants are inessential. -/
lemma smooth_shifted_primes_dyadic_count (u L : ℕ) (hu : 0 < u)
    (hL : 4 ≤ L) (hLu : 1536 * u ≤ L)
    (huC : 8192 * totientRatioAverageConstant * (1 + 5 * Real.log 2) ≤
      (u : ℝ) * (Real.log 2) ^ 2) :
    2 ^ ((128 * u - 1) * L) ≤
      (((2 ^ (128 * u * L) + 1).primesBelow).filter
        (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * u - 5) * L)))).card := by
  let t := 128 * u
  let X := 2 ^ (t * L)
  let A := 2 ^ (5 * L)
  let Y := 2 ^ ((t - 5) * L)
  let b := 2 ^ ((t - 1) * L)
  let J := u * L
  let Q := (X + 1).primesBelow
  let P := Q.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y)
  let R := Q.filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)
  have ht : 128 ≤ t := by dsimp [t]; omega
  have hL0 : 0 < L := by omega
  have hJ : 0 < J := Nat.mul_pos hu hL0
  have hTL : 0 < t * L := Nat.mul_pos (by omega) hL0
  have hXY : X = A * Y := by
    dsimp [X, A, Y]
    rw [← pow_add]
    congr 1
    have : t - 5 + 5 = t := by omega
    nlinarith
  have hXb : X = 2 ^ L * b := by
    dsimp [X, b]
    rw [← pow_add]
    congr 1
    have : t - 1 + 1 = t := by omega
    nlinarith
  have hAX : A ≤ X := by
    dsimp [A, X]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L (by omega))
  have hscale : 12 * (t * L) ≤ 2 ^ L := by
    calc
      12 * (t * L) ≤ L ^ 2 := by dsimp [t]; nlinarith
      _ ≤ _ := sq_le_two_pow L hL
  have hXscale : 12 * (t * L) * b ≤ X := by
    rw [hXb]
    exact Nat.mul_le_mul_right b hscale
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  have hTR : (0 : ℝ) < (t * L : ℕ) := by exact_mod_cast hTL
  have hK : 0 < totientRatioAverageConstant := Real.exp_pos _
  have hH : (harmonic A : ℝ) ≤ (1 + 5 * Real.log 2) * L := by
    have h := harmonic_le_one_add_log A
    have hlogA : Real.log (A : ℝ) = (5 * (L : ℝ)) * Real.log 2 := by
      dsimp [A]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast
      rfl
    rw [hlogA] at h
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    nlinarith
  have hmain : 16 * totientRatioAverageConstant * X * (harmonic A : ℝ) /
      ((J : ℝ) * Real.log 2) ^ 2 ≤ (X : ℝ) / (4 * (t * L : ℕ)) := by
    have hden : 0 < ((J : ℝ) * Real.log 2) ^ 2 :=
      sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) hc)
    calc
      _ ≤ 16 * totientRatioAverageConstant * X * ((1 + 5 * Real.log 2) * L) /
          ((J : ℝ) * Real.log 2) ^ 2 := by
        apply div_le_div_of_nonneg_right ?_ hden.le
        exact mul_le_mul_of_nonneg_left hH (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hTR)).mpr
        have h := mul_le_mul_of_nonneg_right huC
          (show 0 ≤ (X : ℝ) * (u : ℝ) * (L : ℝ) ^ 2 by positivity)
        dsimp [J, t]
        push_cast
        convert h using 1 <;> ring
  have herrorN : A * (2 ^ (64 * J) + 2 ^ (16 * J) + 1) ≤ 3 * b := by
    have hp16 : 2 ^ (16 * J) ≤ 2 ^ (64 * J) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp1 : 1 ≤ 2 ^ (64 * J) := Nat.one_le_pow _ _ (by decide)
    have hpow : A * 2 ^ (64 * J) ≤ b := by
      dsimp [A, J, b]
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      have hcoef : 64 * u + 5 ≤ t - 1 := by dsimp [t]; omega
      nlinarith
    nlinarith
  have herror : (A : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) ≤
      (X : ℝ) / (4 * (t * L : ℕ)) := by
    have h1 : (A : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) ≤ 3 * (b : ℝ) := by
      exact_mod_cast herrorN
    apply h1.trans
    apply (le_div_iff₀ (mul_pos (by norm_num) hTR)).mpr
    have h := (Nat.cast_le (α := ℝ)).mpr hXscale
    push_cast at h ⊢
    nlinarith
  have hrough : (R.card : ℝ) ≤ (X : ℝ) / (2 * (t * L : ℕ)) := by
    have hb := rough_shifted_prime_explicit_bound X A Y J (by dsimp [Y]; positivity)
      hXY.le hAX hJ
    calc
      (R.card : ℝ) ≤ _ := hb
      _ ≤ (X : ℝ) / (4 * (t * L : ℕ)) + (X : ℝ) / (4 * (t * L : ℕ)) :=
        add_le_add hmain herror
      _ = _ := by ring
  have hpartition : P.card + R.card = Q.card := by
    exact Finset.card_filter_add_card_filter_not _
  have hprime : X ≤ (t * L) * (Q.card + 1) := by
    have h := dyadic_prime_count_lower (t * L - 1)
    rwa [Nat.sub_add_cancel (show 1 ≤ t * L from hTL)] at h
  change b ≤ P.card
  by_contra h
  have hsmall : P.card + 1 ≤ b := by omega
  have hsmallmul : (t * L) * (P.card + 1) ≤ (t * L) * b := Nat.mul_le_mul_left _ hsmall
  have hprimeR : (X : ℝ) ≤ ((t * L : ℕ) : ℝ) * ((P.card : ℝ) + (R.card : ℝ) + 1) := by
    rw [← hpartition] at hprime
    exact_mod_cast hprime
  have hsmallR := (Nat.cast_le (α := ℝ)).mpr hsmallmul
  have hscaleR := (Nat.cast_le (α := ℝ)).mpr hXscale
  have hr := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hTR)).mp hrough
  have hXpos : (0 : ℝ) < X := by dsimp [X]; positivity
  push_cast at hprimeR hsmallR hscaleR hr
  nlinarith

/-- The elementary sieve supplies a fixed smoothness exponent with almost
full prime-counting exponent on arbitrarily large dyadic scales. -/
lemma exists_fixed_smooth_shifted_prime_density :
    ∃ t : ℕ, 6 ≤ t ∧ ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨u, hu⟩ := exists_nat_gt (max 1
    (8192 * totientRatioAverageConstant * (1 + 5 * Real.log 2) / (Real.log 2) ^ 2))
  have hu1 : (1 : ℝ) < u := (le_max_left _ _).trans_lt hu
  have hu0 : 0 < u := by exact_mod_cast (show (0 : ℝ) < u by linarith)
  have huC : 8192 * totientRatioAverageConstant * (1 + 5 * Real.log 2) ≤
      (u : ℝ) * (Real.log 2) ^ 2 :=
    ((div_lt_iff₀ (sq_pos_of_pos hc)).mp ((le_max_right _ _).trans_lt hu)).le
  refine ⟨128 * u, by omega, ?_⟩
  intro M
  let L := max M (max 4 (1536 * u))
  have hLM : M ≤ L := le_max_left _ _
  have hL4 : 4 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLu : 1536 * u ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  let P := ((2 ^ (128 * u * L) + 1).primesBelow).filter
    (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * u - 5) * L)))
  refine ⟨L, hLM, P, ?_, smooth_shifted_primes_dyadic_count u L hu0 hL4 hLu huC⟩
  intro p hp
  obtain ⟨hpQ, hpS⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
  exact ⟨hprime, by omega, hpS⟩

#print axioms exists_fixed_smooth_shifted_prime_density
#print axioms smooth_shifted_primes_dyadic_count
#print axioms rough_shifted_prime_explicit_bound
#print axioms totient_ratio_two_mul_harmonic_average
#print axioms harmonic_average_prime_product_le
#print axioms dyadic_prime_count_lower
#print axioms prime_pair_explicit_bound
#print axioms pair_sieve_denominator_log_lower
#print axioms pair_sieve_denominator_ge_half_product
#print axioms harmonic_le_prime_euler_product
#print axioms sum_prime_log_div_dyadic_le
#print axioms powerset_weighted_sum_moment
#print axioms half_euler_product_le_truncated_of_log_moment
#print axioms prime_pair_sieve_bound
#print axioms abs_card_pair_conditions
#print axioms quadraticRootCount_prod_primes
#print axioms abs_card_residue_filter_sub
#print axioms finite_selberg_bound
#print axioms exists_selberg_weights
#print axioms alternating_superset_inversion
#print axioms sieve_quadratic_diagonalization
#print axioms sifted_card_le_main_error

end Erdos821.Sieve
