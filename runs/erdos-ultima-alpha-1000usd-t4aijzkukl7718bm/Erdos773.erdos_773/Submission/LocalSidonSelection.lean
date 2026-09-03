import Submission.LocalCollisionBounds
import Submission.LowCollisionSelection

/-!
Local Sidon extraction from the ordered collision count. The square values
need not first be made progression-free. This is a local bound, not a way of
controlling mixed collisions between intervals and not a proof of Erdős 773.
-/
namespace Erdos773.LocalSidonSelection
open Finset LocalCollisionBounds LowCollisionSelection
set_option maxHeartbeats 1000000

private lemma ordered_presentation {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    ∃ u v w x : ℕ, u < v ∧ v < w ∧ w < x ∧
      u ^ 2 + x ^ 2 = v ^ 2 + w ^ 2 ∧
      ({u,v,w,x} : Finset ℕ) = {a,b,c,d} := by
  let u := min a b
  let v := max a b
  let w := min c d
  let x := max c d
  have huv : u < v := min_lt_max.mpr hab
  have hwx : w < x := min_lt_max.mpr hcd
  have huw : u ≠ w := by dsimp [u,w]; omega
  have he' : u ^ 2 + v ^ 2 = w ^ 2 + x ^ 2 := by
    dsimp [u,v,w,x]
    simp only [min_def, max_def]
    split_ifs <;> omega
  have hs : ({u,v,w,x} : Finset ℕ) = {a,b,c,d} := by
    ext n
    dsimp [u,v,w,x]
    simp only [min_def, max_def]
    split_ifs <;> simp [or_comm, or_left_comm]
  rcases lt_or_gt_of_ne huw with huw | hwu
  · have hxv : x < v := by
      by_contra! h
      have hh := Nat.pow_lt_pow_left huw (by decide : (2 : ℕ) ≠ 0)
      have hh' := Nat.pow_le_pow_left h 2
      omega
    refine ⟨u,w,x,v,huw,hwx,hxv,he', ?_⟩
    calc
      _ = ({u,v,w,x} : Finset ℕ) := by ext n; simp [or_comm, or_left_comm, or_assoc]
      _ = _ := hs
  · have hvx : v < x := by
      by_contra! h
      have hh := Nat.pow_lt_pow_left hwu (by decide : (2 : ℕ) ≠ 0)
      have hh' := Nat.pow_le_pow_left h 2
      omega
    refine ⟨w,u,v,x,hwu,huv,hvx,he'.symm, ?_⟩
    calc
      _ = ({u,v,w,x} : Finset ℕ) := by ext n; simp [or_comm, or_left_comm, or_assoc]
      _ = _ := hs

private def support (q : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ :=
  {q.1.1 ^ 2, q.1.2 ^ 2, q.2.1 ^ 2, q.2.2 ^ 2}

/-- Each four-entry support has a strictly increasing collision presentation.
Thus no factor for ordered presentations is lost in the local count. -/
theorem fourSupports_card_le (L H : ℕ) :
    (fourSupports ((Icc L (L+H)).image (fun n : ℕ => n ^ 2))).card ≤
      (collisions L H).card := by
  classical
  let S := (Icc L (L+H)).image (fun n : ℕ => n ^ 2)
  apply le_trans _ (card_image_le (f := support) (s := collisions L H))
  apply card_le_card_of_injOn (fun e : Finset S => e.image Subtype.val)
  · intro e he
    change e ∈ (sidonObstructions S).filter (fun e => e.card = 4) at he
    obtain ⟨he, hcard⟩ := mem_filter.mp he
    obtain ⟨_, a, b, c, d, rfl, heq, hnt⟩ := mem_filter.mp he
    have hac : a ≠ c := by
      intro h
      subst c
      have hh : ({a,b,a,d} : Finset S).card ≤ 3 := by
        simpa [Finset.insert_comm] using (card_le_three (a := a) (b := b) (c := d))
      omega
    have hbd : b ≠ d := by
      intro h
      subst d
      have hh : ({a,b,c,b} : Finset S).card ≤ 3 := by
        simpa [Finset.insert_comm] using (card_le_three (a := a) (b := c) (c := b))
      omega
    have hnt' : ¬((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
      simpa only [Subtype.ext_iff] using hnt
    have hcross : a.val ≠ b.val ∧ a.val ≠ d.val ∧ c.val ≠ b.val ∧ c.val ≠ d.val := by omega
    have hac' : a.val ≠ c.val := fun h => hac (Subtype.ext h)
    have hbd' : b.val ≠ d.val := fun h => hbd (Subtype.ext h)
    obtain ⟨r, hr, hra⟩ := mem_image.mp a.property
    obtain ⟨s, hs, hsb⟩ := mem_image.mp b.property
    obtain ⟨t, ht, htc⟩ := mem_image.mp c.property
    obtain ⟨v, hv, hvd⟩ := mem_image.mp d.property
    have hrt : r ≠ t := by intro h; apply hac'; rw [← hra, ← htc, h]
    have hrs : r ≠ s := by intro h; apply hcross.1; rw [← hra, ← hsb, h]
    have hrv : r ≠ v := by intro h; apply hcross.2.1; rw [← hra, ← hvd, h]
    have hts : t ≠ s := by intro h; apply hcross.2.2.1; rw [← htc, ← hsb, h]
    have htv : t ≠ v := by intro h; apply hcross.2.2.2; rw [← htc, ← hvd, h]
    have hsv : s ≠ v := by intro h; apply hbd'; rw [← hsb, ← hvd, h]
    have hnorm : r ^ 2 + t ^ 2 = s ^ 2 + v ^ 2 := by rw [hra, htc, hsb, hvd]; exact heq
    obtain ⟨u,w,x,y,huw,hwx,hxy,hnew,he⟩ :=
      ordered_presentation hrt hrs hrv hts htv hsv hnorm
    have hsub : ({u,w,x,y} : Finset ℕ) ⊆ Icc L (L+H) := by
      rw [he]
      intro n hn
      simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> assumption
    apply mem_image.mpr
    refine ⟨((u,w),(x,y)), mem_filter.mpr ⟨?_,huw,hwx,hxy,hnew⟩, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨hsub (by simp), hsub (by simp)⟩,
        mem_product.mpr ⟨hsub (by simp), hsub (by simp)⟩⟩
    · have hh := congrArg (Finset.image (fun n : ℕ => n ^ 2)) he
      simpa [support, hra, hsb, htc, hvd, Finset.insert_comm] using hh
  · exact (Finset.image_injective Subtype.val_injective).injOn

/-- A local Sidon subset bound with all three-entry obstructions included. -/
theorem local_alteration (L H : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (p * ((H : ℝ) + 1) - p ^ 4 * (collisions L H).card) / 4 ≤
      (maxSidonSubsetCard ((Icc L (L+H)).image (fun n : ℕ => n ^ 2)) : ℝ) := by
  let S := (Icc L (L+H)).image (fun n : ℕ => n ^ 2)
  have hs : S.card = H + 1 := by
    dsimp [S]
    rw [card_image_of_injective _ (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0))]
    simp only [Nat.card_Icc]
    omega
  have hh := finite_max_bound (Subset.refl S) p hp hp1
  have hc : ((fourSupports S).card : ℝ) ≤ (collisions L H).card := by
    exact_mod_cast fourSupports_card_le L H
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg hp 4)
  rw [hs, Nat.cast_add, Nat.cast_one] at hh
  linarith

/-- Uniform local extraction using any divisor bound on the interval scale. -/
theorem local_divisor_alteration (L H : ℕ) (p K : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hK : 0 ≤ K)
    (hdiv : ∀ D : ℕ, 0 < D → D ≤ H ^ 2 → (D.divisors.card : ℝ) ≤ K) :
    (p * ((H : ℝ) + 1) - p ^ 4 * ((H : ℝ) + 1) *
      (H ^ 2 / (8 * L + 4) : ℕ) * K) / 4 ≤
      (maxSidonSubsetCard ((Icc L (L+H)).image (fun n : ℕ => n ^ 2)) : ℝ) := by
  have hh := local_alteration L H p hp hp1
  have hc := uniform_divisor_bound L H K hK hdiv
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg hp 4)
  nlinarith only [hh, hm]

/-- An explicit local lower bound after optimizing the sampling probability.
The maximum with one also handles intervals with no four-entry collisions. -/
theorem local_finite_lower (L H : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hdiv : ∀ D : ℕ, 0 < D → D ≤ H ^ 2 → (D.divisors.card : ℝ) ≤ K) :
    7 * ((H : ℝ) + 1) /
      (64 * (max 1 ((H ^ 2 / (8 * L + 4) : ℕ) * K)) ^ (1/3 : ℝ)) ≤
      (maxSidonSubsetCard ((Icc L (L+H)).image (fun n : ℕ => n ^ 2)) : ℝ) := by
  let T : ℝ := (H ^ 2 / (8 * L + 4) : ℕ)
  let R : ℝ := (max 1 (T * K)) ^ (1/3 : ℝ)
  let p : ℝ := 1 / (2 * R)
  have hR1 : 1 ≤ R := Real.one_le_rpow (le_max_left _ _) (by norm_num)
  have hR : 0 < R := by linarith
  have hR3 : R ^ 3 = max 1 (T * K) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ max 1 (T * K))]
    norm_num
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hpr : p * R = 1 / 2 := by dsimp [p]; field_simp
  have hTK : T * K ≤ R ^ 3 := by rw [hR3]; exact le_max_right _ _
  have hcost : p ^ 4 * ((H : ℝ) + 1) * T * K ≤ p * ((H : ℝ) + 1) / 8 := by
    calc
      _ = p ^ 4 * ((H : ℝ) + 1) * (T * K) := by ring
      _ ≤ p ^ 4 * ((H : ℝ) + 1) * R ^ 3 :=
        mul_le_mul_of_nonneg_left hTK (by positivity)
      _ = p * ((H : ℝ) + 1) * (p * R) ^ 3 := by ring
      _ = _ := by rw [hpr]; ring
  have hh := local_divisor_alteration L H p K hp hp1 hK hdiv
  change (p * ((H : ℝ) + 1) - p ^ 4 * ((H : ℝ) + 1) * T * K) / 4 ≤ _ at hh
  change 7 * ((H : ℝ) + 1) / (64 * R) ≤ _
  have he : 7 * ((H : ℝ) + 1) / (64 * R) = (7/32 : ℝ) * p * ((H : ℝ) + 1) := by
    dsimp [p]
    ring
  rw [he]
  linarith

#print axioms local_finite_lower

#print axioms fourSupports_card_le
#print axioms local_alteration
#print axioms local_divisor_alteration
end Erdos773.LocalSidonSelection
