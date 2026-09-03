import FormalConjecturesUtil

/-! Distinct odd divisor resources have a quadratic reciprocal cost.
These inequalities constrain a proposed repair construction, not arbitrary
covering systems. -/
namespace Erdos7OddDivisorRank
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma ordered_odd_lower {n : ℕ} (e : Fin n → ℕ) (hm : StrictMono e)
    (ho : ∀ i, Odd (e i)) (i : Fin n) : 2*i.val+1 ≤ e i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero => simpa using (ho 0).pos
    | succ i ih =>
      have hl := hm (Fin.castSucc_lt_succ (i := i))
      obtain ⟨u,hu⟩ := ho i.castSucc
      obtain ⟨v,hv⟩ := ho i.succ
      simp only [Fin.val_castSucc, Fin.val_succ] at *
      omega

lemma sum_first_odds (n : ℕ) : (∑ i : Fin n, (2*i.val+1)) = n^2 := by
  rw [← Finset.sum_range (fun i : ℕ => 2*i+1)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- A finite set of positive odd integers has sum at least its squared size. -/
theorem card_sq_le_sum (s : Finset ℕ) (ho : ∀ x ∈ s, Odd x) :
    s.card^2 ≤ ∑ x ∈ s, x := by
  let e := s.orderEmbOfFin rfl
  have he (i : Fin s.card) : Odd (e i) := ho _ (s.orderEmbOfFin_mem rfl i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s.card))) =>
    ordered_odd_lower e e.strictMono he i)
  rw [sum_first_odds] at h
  have hs : (∑ i : Fin s.card, e i) = ∑ x ∈ s, x := by
    have hm := s.map_orderEmbOfFin_univ rfl
    calc
      _ = ∑ x ∈ Finset.univ.map e.toEmbedding, x := (Finset.sum_map _ _ _).symm
      _ = _ := congrArg (fun t : Finset ℕ => ∑ x ∈ t, x) hm
  exact h.trans_eq hs

/-- The same bound for an injective indexed family. -/
theorem card_sq_le_sum_of_injective {K : Type*} [Fintype K]
    (e : K → ℕ) (hi : Function.Injective e) (ho : ∀ k, Odd (e k)) :
    (Fintype.card K)^2 ≤ ∑ k, e k := by
  classical
  have h := card_sq_le_sum (Finset.univ.image e) (by
    intro x hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
    exact ho k)
  rw [Finset.card_image_of_injective _ hi, Finset.card_univ,
    Finset.sum_image (by intro a _ b _ h; exact hi h)] at h
  exact h

/-- Complementary divisors remain distinct, and are positive odd integers. -/
theorem complement_sum_lower {K : Type*} [Fintype K]
    (d : ℕ) (hd : Odd d) (e : K → ℕ) (hi : Function.Injective e)
    (he : ∀ k, e k ∣ d) :
    (Fintype.card K)^2 ≤ ∑ k, d / e k := by
  apply card_sq_le_sum_of_injective (fun k => d / e k)
  · intro a b h
    apply hi
    have hh := congrArg (fun n => d/n) h
    simpa only [Nat.div_div_self (he a) hd.pos.ne',
      Nat.div_div_self (he b) hd.pos.ne'] using hh
  · intro k
    exact hd.of_dvd_nat (Nat.div_dvd_of_dvd (he k))

/-- k distinct divisor resources of an odd cofactor d cost at least k²/d
in reciprocal weight. Positivity of the divisor follows from oddness. -/
theorem reciprocal_sum_lower {K : Type*} [Fintype K]
    (d : ℕ) (hd : Odd d) (e : K → ℕ) (hi : Function.Injective e)
    (he : ∀ k, e k ∣ d) :
    (Fintype.card K : ℚ)^2 / d ≤ ∑ k, 1 / (e k : ℚ) := by
  apply (div_le_iff₀ (show (0 : ℚ) < d by exact_mod_cast hd.pos)).mpr
  rw [Finset.sum_mul]
  have h : (Fintype.card K : ℚ)^2 ≤ ∑ k, ((d / e k : ℕ) : ℚ) := by
    exact_mod_cast complement_sum_lower d hd e hi he
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  have hp : (e k : ℚ) ≠ 0 := by exact_mod_cast (hd.of_dvd_nat (he k)).pos.ne'
  rw [Nat.cast_div (he k) hp]
  ring

/-- A globally injective resource assignment cannot exceed the reciprocal
budget of the finite set from which its resources are drawn. -/
theorem reciprocal_budget {K : Type*} [Fintype K]
    (R : Finset ℕ) (e : K → ℕ) (hi : Function.Injective e)
    (he : ∀ k, e k ∈ R) :
    (∑ k, 1 / (e k : ℚ)) ≤ ∑ r ∈ R, 1 / (r : ℚ) := by
  classical
  have hs : Finset.univ.image e ⊆ R := by
    intro r hr
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hr
    exact he k
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r : ℕ => 1/(r : ℚ))
    hs (by intro r _ _; positivity)
  rw [Finset.sum_image (by intro a _ b _ h; exact hi h)] at h
  exact h

/-- Global divisor distinctness yields a quadratic budget for all cofactor
blocks simultaneously. This is stronger than multiplying each block size
by the smallest available reciprocal weight. -/
theorem global_quadratic_budget {J : Type*} [Fintype J]
    (d count : J → ℕ) (hd : ∀ j, Odd (d j)) (R : Finset ℕ)
    (e : ((j : J) × Fin (count j)) → ℕ) (hi : Function.Injective e)
    (he : ∀ j t, e ⟨j,t⟩ ∣ d j) (hR : ∀ k, e k ∈ R) :
    (∑ j, (count j : ℚ)^2 / d j) ≤ ∑ r ∈ R, 1 / (r : ℚ) := by
  have hj (j : J) : (count j : ℚ)^2 / d j ≤ ∑ t, 1/(e ⟨j,t⟩ : ℚ) := by
    have hin : Function.Injective (fun t => e ⟨j,t⟩) := by
      intro a b h
      have hh := hi h
      cases hh
      rfl
    simpa only [Fintype.card_fin] using
      reciprocal_sum_lower (d j) (hd j) (fun t => e ⟨j,t⟩) hin (he j)
  calc
    _ ≤ ∑ j, ∑ t, 1/(e ⟨j,t⟩ : ℚ) := Finset.sum_le_sum (fun j _ => hj j)
    _ = ∑ k, 1/(e k : ℚ) := (Fintype.sum_sigma (fun k : (j : J) × Fin (count j) => 1/(e k : ℚ))).symm
    _ ≤ _ := reciprocal_budget R e hi hR

#print axioms card_sq_le_sum
#print axioms complement_sum_lower
#print axioms reciprocal_sum_lower
#print axioms global_quadratic_budget
end Erdos7OddDivisorRank
