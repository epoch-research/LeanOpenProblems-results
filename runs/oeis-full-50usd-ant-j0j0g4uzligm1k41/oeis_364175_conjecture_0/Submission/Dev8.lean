import Mathlib
open Finset

lemma sq_sum_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p:ℤ) ∣ ∑ r ∈ Finset.Icc 1 (p-1), (r:ℤ)^2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hfield : ∑ a : ZMod p, a^2 = 0 := by
    have h2 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
    simpa using h2
  have herase : (∑ a ∈ (univ : Finset (ZMod p)).erase 0, a^2) = 0 :=
    (Finset.sum_erase (univ : Finset (ZMod p)) (f := fun x : ZMod p => x^2) (a := 0)
      (by simp)).trans hfield
  rw [show (∑ x ∈ Icc 1 (p-1), ((x:ZMod p))^2)
        = ∑ a ∈ (univ:Finset (ZMod p)).erase 0, a^2 from ?_, herase]
  apply Finset.sum_bij' (fun (x:ℕ) _ => (x:ZMod p)) (fun (a:ZMod p) _ => a.val)
  · intro x hx; rw [Finset.mem_Icc] at hx
    rw [Finset.mem_erase]
    refine ⟨?_, mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  · intro a ha; rw [Finset.mem_erase] at ha
    rw [Finset.mem_Icc]
    have hv : a.val < p := ZMod.val_lt a
    have hv0 : a.val ≠ 0 := fun h0 => ha.1 ((ZMod.val_eq_zero a).mp h0)
    omega
  · intro x hx; rw [Finset.mem_Icc] at hx
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · intro a _; rw [ZMod.natCast_val, ZMod.cast_id]
  · intro x _; rfl

-- Product perturbation: order 1
lemma perturb1 (a : ℕ → ℤ) (B : ℤ) (s : Finset ℕ) :
    B ∣ (∏ i ∈ s, (a i + B)) - ∏ i ∈ s, a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k t hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    have e : (a k + B) * ∏ i ∈ t, (a i + B) - a k * ∏ i ∈ t, a i
        = a k * ((∏ i ∈ t, (a i + B)) - ∏ i ∈ t, a i) + B * ∏ i ∈ t, (a i + B) := by ring
    rw [e]
    exact dvd_add (ih.mul_left (a k)) (dvd_mul_right B _)

-- Product perturbation: order 2
lemma perturb2 (a : ℕ → ℤ) (B : ℤ) (s : Finset ℕ) :
    B^2 ∣ (∏ i ∈ s, (a i + B)) - (∏ i ∈ s, a i)
          - B * ∑ j ∈ s, ∏ i ∈ s.erase j, a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k t hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk]
    -- Σ over insert: j=k gives ∏_{t} a; j∈t gives a k * ∏_{t.erase j} a
    have hj : ∀ j ∈ t, (insert k t).erase j = insert k (t.erase j) := by
      intro j hj; rw [Finset.erase_insert_of_ne (by rintro rfl; exact hk hj)]
    have hsum : ∑ j ∈ t, ∏ i ∈ (insert k t).erase j, a i
        = a k * ∑ j ∈ t, ∏ i ∈ t.erase j, a i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hjt
      rw [hj j hjt, Finset.prod_insert (by simp [Finset.mem_erase, hk])]
    rw [Finset.erase_insert hk, hsum]
    -- now algebra + IH + perturb1
    have hp1 : B ∣ (∏ i ∈ t, (a i + B)) - ∏ i ∈ t, a i := perturb1 a B t
    obtain ⟨c, hc⟩ := hp1
    obtain ⟨d, hd⟩ := ih
    set Pt := ∏ i ∈ t, (a i + B)
    set Qt := ∏ i ∈ t, a i
    set St := ∑ j ∈ t, ∏ i ∈ t.erase j, a i
    -- goal: B^2 ∣ (a k+B)*Pt - a k*Qt - B*(Qt + a k*St)
    refine ⟨a k * d + c, ?_⟩
    linear_combination (a k) * hd + B * hc
