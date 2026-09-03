import Submission.Sieve

/-!
# Selberg weights with the local denominator retained

Auxiliary finite estimates. These do not prove the shifted-prime lower
bounds required to settle Erdős 821.
-/

open Finset Filter
open scoped Classical BigOperators

namespace Erdos821.Sieve

set_option maxHeartbeats 3000000

lemma downward_upset_product_sum_le {α : Type*} [DecidableEq α]
    (W : Finset (Finset α))
    (hdown : ∀ R ∈ W, ∀ S, S ⊆ R → S ∈ W)
    (u : α → ℝ) (hu : ∀ p, 0 ≤ u p) (S : Finset α) :
    (∑ R ∈ W with S ⊆ R, ∏ p ∈ R, u p) ≤
      (∏ p ∈ S, u p) * ∑ R ∈ W, ∏ p ∈ R, u p := by
  let A := W.filter (fun R => S ⊆ R)
  have hinj : Set.InjOn (fun R : Finset α => R \ S) (A : Set (Finset α)) := by
    intro R hR T hT he
    change R \ S = T \ S at he
    have hSR := (Finset.mem_filter.mp hR).2
    have hST := (Finset.mem_filter.mp hT).2
    rw [← Finset.sdiff_union_of_subset hSR, ← Finset.sdiff_union_of_subset hST, he]
  have hsub : A.image (fun R => R \ S) ⊆ W := by
    intro R hR
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hR
    exact hdown T (Finset.mem_filter.mp hT).1 _ Finset.sdiff_subset
  have hsum : (∑ R ∈ A, ∏ p ∈ R \ S, u p) ≤ ∑ R ∈ W, ∏ p ∈ R, u p := by
    rw [← Finset.sum_image (f := fun R : Finset α => ∏ p ∈ R, u p) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun R _ _ =>
      Finset.prod_nonneg (fun p _ => hu p))
  calc
    _ = (∏ p ∈ S, u p) * ∑ R ∈ A, ∏ p ∈ R \ S, u p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      exact (Finset.prod_sdiff (f := u) (Finset.mem_filter.mp hR).2).symm.trans (mul_comm _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Finset.prod_nonneg (fun p _ => hu p))

lemma exists_selberg_weights_local {α : Type*} [DecidableEq α]
    (P : Finset α) (W : Finset (Finset α)) (hWP : W ⊆ P.powerset)
    (hW0 : ∅ ∈ W) (hdown : ∀ R ∈ W, ∀ S, S ⊆ R → S ∈ W)
    (v : α → ℝ) (hv : ∀ p ∈ P, 0 < v p ∧ v p < 1) :
    ∃ w : Finset α → ℝ,
      w ∅ = 1 ∧
      (∀ S ∈ P.powerset, S ∉ W → w S = 0) ∧
      (∀ S ∈ P.powerset, |w S| ≤ ∏ p ∈ S, (1 - v p)⁻¹) ∧
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
  have hFlocal (S : Finset α) (hS : S ∈ P.powerset) :
      F S ≤ (H S)⁻¹ * G := by
    let u : α → ℝ := fun p => if p ∈ P then ((v p)⁻¹ - 1)⁻¹ else 0
    have hu : ∀ p, 0 ≤ u p := by
      intro p
      dsimp [u]
      split_ifs with hp
      · exact inv_nonneg.mpr (sub_nonneg.mpr
          (le_of_lt ((one_lt_inv₀ (hv p hp).1).mpr (hv p hp).2)))
      · exact le_rfl
    have hprod (R : Finset α) (hR : R ∈ P.powerset) :
        (∏ p ∈ R, u p) = (H R)⁻¹ := by
      dsimp only [H]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl (fun p hp => if_pos (Finset.mem_powerset.mp hR hp))
    have hFsum : F S = ∑ R ∈ W with S ⊆ R, ∏ p ∈ R, u p := by
      dsimp only [F]
      rw [Finset.sum_filter]
      symm
      apply (Finset.sum_congr rfl (fun R hR => ?_)).trans
        (Finset.sum_subset hWP (fun R _ hRW => by simp [f, hRW]))
      by_cases hSR : S ⊆ R
      · simp only [if_pos hSR, f, if_pos hR, hprod R (hWP hR)]
      · simp only [if_neg hSR]
    rw [hFsum]
    apply (downward_upset_product_sum_le W hdown u hu S).trans_eq
    rw [hprod S hS]
    congr 1
    exact Finset.sum_congr rfl (fun R hR => hprod R (hWP hR))
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
    have heq : |w S| = F S / (V S * G) := by
      dsimp only [w]
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (hFnonneg S), abs_of_pos (mul_pos (hV S hS) hG)]
    rw [heq]
    calc
      _ ≤ ((H S)⁻¹ * G) / (V S * G) :=
        div_le_div_of_nonneg_right (hFlocal S hS) (mul_pos (hV S hS) hG).le
      _ = (H S)⁻¹ / V S := by field_simp [hG.ne']
      _ = ∏ p ∈ S, (1 - v p)⁻¹ := by
        dsimp only [H, V]
        rw [← Finset.prod_inv_distrib, ← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        have hv0 := (hv p (Finset.mem_powerset.mp hS hp)).1.ne'
        have hv1 : 1 - v p ≠ 0 := ne_of_gt (sub_pos.mpr (hv p (Finset.mem_powerset.mp hS hp)).2)
        field_simp
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


lemma finite_selberg_bound_local {α : Type*} [DecidableEq α]
    (A : Finset α) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (bad : ℕ → α → Prop) [∀ p, DecidablePred (bad p)]
    (ρ : ℕ → ℝ) (hρ : ∀ p ∈ P, 1 ≤ ρ p ∧ ρ p < p)
    (X : ℝ) (z : ℕ) (hz : 1 ≤ z)
    (hcount : ∀ S ∈ P.powerset,
      |((A.filter (fun x => ∀ p ∈ S, bad p x)).card : ℝ) -
        X * (∏ p ∈ S, ρ p / p)| ≤ ∏ p ∈ S, ρ p) :
    ((A.filter (fun x => ∀ p ∈ P, ¬bad p x)).card : ℝ) ≤
      X * (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, ((ρ p / p)⁻¹ - 1))⁻¹)⁻¹ + (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
          ∏ p ∈ S, ρ p / (1 - ρ p / p)) ^ 2 := by
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
    exists_selberg_weights_local P W hWP hW0 hdown v hv
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
  let B : ℝ := ∑ S ∈ W, ∏ p ∈ S, ρ p / (1 - ρ p / p)
  have hwR (S : Finset ℕ) (hS : S ∈ P.powerset) :
      |w S| * R S ≤ ∏ p ∈ S, ρ p / (1 - ρ p / p) := by
    apply (mul_le_mul_of_nonneg_right (hwbound S hS)
      (hRpos S (Finset.mem_powerset.mp hS)).le).trans_eq
    dsimp only [R, v]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun p _ => by ring)
  have hsumR : (∑ S ∈ P.powerset, |w S| * R S) ≤ B := by
    have hsum : (∑ S ∈ P.powerset, |w S| * R S) = ∑ S ∈ W, |w S| * R S := by
      symm
      apply Finset.sum_subset hWP
      intro S hS hSW
      rw [hwzero S hS hSW, abs_zero, zero_mul]
    rw [hsum]
    exact Finset.sum_le_sum (fun S hS => hwR S (hWP hS))
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
      B ^ 2 := by
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
      _ ≤ B ^ 2 := by
        apply pow_le_pow_left₀
        · exact Finset.sum_nonneg (fun S hS => mul_nonneg (abs_nonneg _)
            (hRpos S (Finset.mem_powerset.mp hS)).le)
        · exact hsumR
  have hb := sifted_card_le_main_error A P.powerset E good w X K err hgood hecount
  change ((A.filter good).card : ℝ) ≤ X * G⁻¹ + B ^ 2
  have hmain : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset, w S * w T * K S T) = G⁻¹ := hwmain
  rw [hmain] at hb
  exact hb.trans (add_le_add le_rfl herrsum)


end Erdos821.Sieve
