import FormalConjecturesUtil

/-! Exact covariance of alternating residue signs for odd moduli.
This concerns complete periods, not a short-interval Jacobsthal bound. -/
namespace Erdos970.ParityDiscrepancy
open Finset

def residueSign (d a : ℕ) : ℚ := (-1) ^ (a % d)

lemma sum_blocks (f : ℕ → ℚ) (n m : ℕ) :
    (∑ a ∈ range (n * m), f a) = ∑ j ∈ range m, ∑ i ∈ range n, f (i + n * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    simp only [Nat.add_comm]

lemma sum_mod_product (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hde : d.Coprime e)
    (f g : ℕ → ℚ) :
    (∑ a ∈ range (d * e), f (a % d) * g (a % e)) =
      (∑ u ∈ range d, f u) * (∑ v ∈ range e, g v) := by
  rw [sum_mul_sum, ← sum_product (range d) (range e) (fun x => f x.1 * g x.2)]
  apply sum_bij (fun a _ => (a % d, a % e))
  · intro a ha
    exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd), mem_range.mpr (Nat.mod_lt _ he)⟩
  · intro a ha b hb hab
    have hmod : a ≡ b [MOD d * e] := (Nat.modEq_and_modEq_iff_modEq_mul hde).mp
      ⟨congrArg Prod.fst hab, congrArg Prod.snd hab⟩
    exact hmod.eq_of_lt_of_lt (mem_range.mp ha) (mem_range.mp hb)
  · intro b hb
    let a := Nat.chineseRemainder hde b.1 b.2
    refine ⟨a.val, mem_range.mpr (Nat.chineseRemainder_lt_mul hde b.1 b.2 hd.ne' he.ne'), ?_⟩
    apply Prod.ext
    · exact Eq.trans a.property.1 (Nat.mod_eq_of_lt (mem_range.mp (mem_product.mp hb).1))
    · exact Eq.trans a.property.2 (Nat.mod_eq_of_lt (mem_range.mp (mem_product.mp hb).2))
  · intro a ha
    rfl

lemma sum_alternating_odd {d : ℕ} (hd : Odd d) : (∑ a ∈ range d, (-1 : ℚ) ^ a) = 1 := by
  have h := geom_sum_mul_neg (-1 : ℚ) d
  rw [hd.neg_one_pow] at h
  linarith

lemma residueSign_period (d a t : ℕ) : residueSign d (a + d * t) = residueSign d a := by
  simp only [residueSign, Nat.add_mul_mod_self_left]

lemma residueSign_mod (d a N : ℕ) (hd : d ∣ N) : residueSign d (a % N) = residueSign d a := by
  simp only [residueSign, Nat.mod_mod_of_dvd _ hd]

lemma residueSign_succ (d a : ℕ) (hd : Odd d) :
    residueSign d a + residueSign d (a + 1) = if d ∣ a + 1 then 2 else 0 := by
  have hdpos := hd.pos
  have hm := Nat.mod_lt a hdpos
  by_cases hdiv : d ∣ a + 1
  · rw [if_pos hdiv]
    have hmod : a % d + 1 = d := by
      have hz := Nat.mod_eq_zero_of_dvd hdiv
      have hh := Nat.mod_add_mod a d 1
      by_contra hne
      have hl : a % d + 1 < d := by omega
      have hsmall := Nat.mod_eq_of_lt hl
      omega
    have he : Even (a % d) := by
      obtain ⟨t, ht⟩ := hd
      refine ⟨t, ?_⟩
      omega
    simp only [residueSign, Nat.mod_eq_zero_of_dvd hdiv, pow_zero, he.neg_one_pow]
    norm_num
  · rw [if_neg hdiv]
    have hmod : (a + 1) % d = a % d + 1 := by
      have hn : (a + 1) % d ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
      have hh := Nat.mod_add_mod a d 1
      have hl : a % d + 1 < d := by
        by_contra h
        have heq : a % d + 1 = d := by omega
        rw [heq, Nat.mod_self] at hh
        exact hn hh.symm
      rw [Nat.mod_eq_of_lt hl] at hh
      exact hh.symm
    simp only [residueSign, hmod, pow_succ]
    ring

lemma residueSign_common_factor (g d a t : ℕ) (hg : Odd g) (ha : a < g) :
    residueSign (g * d) (a + g * t) = (-1 : ℚ) ^ a * residueSign d t := by
  have hmod : (a + g * t) % (g * d) = a + g * (t % d) := by
    by_cases hd : d = 0
    · simp [hd]
    · have hlt : a + g * (t % d) < g * d := by
        have htd := Nat.mod_lt t (Nat.pos_of_ne_zero hd)
        nlinarith [hg.pos]
      have hh : a + g * t ≡ a + g * (t % d) [MOD g * d] :=
        (Nat.ModEq.mul_left' g (Nat.mod_modEq t d).symm).add_left a
      exact Eq.trans hh (Nat.mod_eq_of_lt hlt)
  simp only [residueSign, hmod, pow_add, pow_mul, hg.neg_one_pow]

/-- Averaging a product of the two signs over their joint period removes the
private coprime coordinates, leaving exactly the common factor. -/
theorem covariance_joint_period (g d e : ℕ) (hg : Odd g) (hd : Odd d) (he : Odd e)
    (hde : d.Coprime e) :
    (∑ a ∈ range (g * (d * e)), residueSign (g * d) a * residueSign (g * e) a) = g := by
  rw [sum_blocks]
  have hinner (t : ℕ) : (∑ a ∈ range g,
      residueSign (g * d) (a + g * t) * residueSign (g * e) (a + g * t)) =
        (g : ℚ) * (residueSign d t * residueSign e t) := by
    have hh (a : ℕ) (ha : a ∈ range g) :
        residueSign (g * d) (a + g * t) * residueSign (g * e) (a + g * t) =
          residueSign d t * residueSign e t := by
      rw [residueSign_common_factor g d a t hg (mem_range.mp ha),
        residueSign_common_factor g e a t hg (mem_range.mp ha)]
      have hs : ((-1 : ℚ) ^ a) ^ 2 = 1 := by rw [← pow_mul, mul_comm a 2, pow_mul]; norm_num
      linear_combination (residueSign d t * residueSign e t) * hs
    rw [sum_congr rfl hh]
    simp
  simp_rw [hinner]
  rw [← mul_sum]
  have hsum : (∑ t ∈ range (d * e), residueSign d t * residueSign e t) = 1 := by
    rw [show (fun t => residueSign d t * residueSign e t) =
      (fun t => (-1 : ℚ) ^ (t % d) * (-1 : ℚ) ^ (t % e)) by rfl,
      sum_mod_product d e hd.pos he.pos hde, sum_alternating_odd hd, sum_alternating_odd he]
    norm_num
  rw [hsum, mul_one]

/-- The same covariance in any multiple of the joint period. -/
theorem covariance_multiple (g d e t : ℕ) (hg : Odd g) (hd : Odd d) (he : Odd e)
    (hde : d.Coprime e) :
    (∑ a ∈ range ((g * (d * e)) * t), residueSign (g * d) a * residueSign (g * e) a) =
      (t : ℚ) * g := by
  rw [sum_blocks]
  have hdvd : g * d ∣ g * (d * e) := ⟨e, by ring⟩
  have hevd : g * e ∣ g * (d * e) := ⟨d, by ring⟩
  have hperiod (a j : ℕ) (d' : ℕ) (h : d' ∣ g * (d * e)) :
      residueSign d' (a + g * (d * e) * j) = residueSign d' a := by
    obtain ⟨v, hv⟩ := h
    rw [hv, mul_assoc, residueSign_period]
  simp_rw [hperiod _ _ _ hdvd, hperiod _ _ _ hevd,
    covariance_joint_period g d e hg hd he hde]
  simp

#print axioms covariance_multiple
end Erdos970.ParityDiscrepancy
