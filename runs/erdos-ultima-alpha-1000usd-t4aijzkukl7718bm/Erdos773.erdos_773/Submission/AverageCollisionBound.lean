import FormalConjecturesUtil
import Submission.CollisionBounds

/-! Average multiplicative-energy bounds, for use in counting square-sum collisions.
This file does not settle Erdős 773. -/
namespace Erdos773.AverageCollision
open Finset
set_option maxHeartbeats 1000000

lemma product_parametrization {a b c d M : ℕ}
    (ha : a ∈ Icc 1 M) (hb : b ∈ Icc 1 M)
    (hc : c ∈ Icc 1 M) (hd : d ∈ Icc 1 M) (he : a * b = c * d) :
    ∃ r ∈ Icc 1 M, ∃ s ∈ Icc 1 M,
      ∃ g ∈ Icc 1 (M / max r s), ∃ h ∈ Icc 1 (M / max r s),
        a = r * g ∧ c = s * g ∧ b = s * h ∧ d = r * h := by
  simp only [Finset.mem_Icc] at ha hb hc hd
  have hg0 : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨g, r, s, hg, hrs, har, hcs⟩ := Nat.exists_coprime' hg0
  have hr : 0 < r := by
    by_contra! hh0
    have hz : r = 0 := by omega
    rw [hz, zero_mul] at har
    omega
  have hs : 0 < s := by
    by_contra! hh0
    have hz : s = 0 := by omega
    rw [hz, zero_mul] at hcs
    omega
  have he' : r * b = s * d := by
    apply Nat.eq_of_mul_eq_mul_right hg
    simpa only [har, hcs, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using he
  have hsb : s ∣ b := hrs.symm.dvd_of_dvd_mul_left ⟨d, he'⟩
  obtain ⟨h, hbh⟩ := hsb
  have hh : 0 < h := by
    by_contra! hh0
    have hz : h = 0 := by omega
    rw [hz, mul_zero] at hbh
    omega
  have hdh : d = r * h := by
    apply Nat.eq_of_mul_eq_mul_left hs
    simpa only [hbh, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using he'.symm
  have hrM : r ≤ M := by
    have hle := Nat.mul_le_mul_left r (show 1 ≤ g by omega)
    have hle' : r ≤ r * g := by simpa only [mul_one] using hle
    exact hle'.trans (har ▸ ha.2)
  have hsM : s ≤ M := by
    have hle := Nat.mul_le_mul_left s (show 1 ≤ g by omega)
    have hle' : s ≤ s * g := by simpa only [mul_one] using hle
    exact hle'.trans (hcs ▸ hc.2)
  have hmax : 0 < max r s := lt_of_lt_of_le hr (le_max_left _ _)
  have hgM : g ≤ M / max r s := by
    rw [Nat.le_div_iff_mul_le hmax, mul_max]
    exact max_le (by rw [mul_comm, ← har]; exact ha.2)
      (by rw [mul_comm, ← hcs]; exact hc.2)
  have hhM : h ≤ M / max r s := by
    rw [Nat.le_div_iff_mul_le hmax, mul_max]
    exact max_le (by rw [mul_comm, ← hdh]; exact hd.2)
      (by rw [mul_comm, ← hbh]; exact hb.2)
  exact ⟨r, mem_Icc.mpr ⟨hr, hrM⟩, s, mem_Icc.mpr ⟨hs, hsM⟩,
    g, mem_Icc.mpr ⟨hg, hgM⟩, h, mem_Icc.mpr ⟨hh, hhM⟩, har, hcs, hbh, hdh⟩

def productQuads (M : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Icc 1 M) ×ˢ (Icc 1 M)) ×ˢ ((Icc 1 M) ×ˢ (Icc 1 M))).filter
    (fun t => t.1.1 * t.2.1 = t.1.2 * t.2.2)

def parameterImage (M : ℕ) (rs : ℕ × ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Icc 1 (M / max rs.1 rs.2)) ×ˢ (Icc 1 (M / max rs.1 rs.2))).image
    (fun gh : ℕ × ℕ => ((rs.1 * gh.1, rs.2 * gh.1), (rs.2 * gh.2, rs.1 * gh.2))))

lemma productQuads_card_le (M : ℕ) :
    (productQuads M).card ≤ ∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, (M / max r s) ^ 2 := by
  have hsub : productQuads M ⊆ ((Icc 1 M) ×ˢ (Icc 1 M)).biUnion (parameterImage M) := by
    rintro ⟨⟨a,c⟩,⟨b,d⟩⟩ ht
    obtain ⟨ht, he⟩ := mem_filter.mp ht
    obtain ⟨⟨ha,hc⟩,⟨hb,hd⟩⟩ := (by simpa only [mem_product] using ht :
      (a ∈ Icc 1 M ∧ c ∈ Icc 1 M) ∧ (b ∈ Icc 1 M ∧ d ∈ Icc 1 M))
    obtain ⟨r,hr,s,hs,g,hg,h,hh,har,hcs,hbh,hdh⟩ := product_parametrization ha hb hc hd he
    apply mem_biUnion.mpr
    refine ⟨(r,s), mem_product.mpr ⟨hr,hs⟩, ?_⟩
    apply mem_image.mpr
    exact ⟨(g,h), mem_product.mpr ⟨hg,hh⟩, by simp [har,hcs,hbh,hdh]⟩
  calc
    _ ≤ (((Icc 1 M) ×ˢ (Icc 1 M)).biUnion (parameterImage M)).card := card_le_card hsub
    _ ≤ ∑ rs ∈ (Icc 1 M) ×ˢ (Icc 1 M), (parameterImage M rs).card := card_biUnion_le
    _ ≤ ∑ rs ∈ (Icc 1 M) ×ˢ (Icc 1 M), (M / max rs.1 rs.2) ^ 2 := by
      apply sum_le_sum
      intro rs hrs
      exact (card_image_le).trans_eq (by simp [card_product, sq])
    _ = _ := by rw [sum_product]

lemma max_sum_bound (M : ℕ) :
    (∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, (M / max r s) ^ 2) ≤
      2 * ∑ r ∈ Icc 1 M, r * (M / r) ^ 2 := by
  have hpoint (r s : ℕ) : (M / max r s) ^ 2 ≤
      (if s ≤ r then (M / r) ^ 2 else 0) + (if r ≤ s then (M / s) ^ 2 else 0) := by
    rcases le_total r s with h | h
    · simp [max_eq_right h, h]
    · simp [max_eq_left h, h]
  have hsum (r : ℕ) (hr : r ∈ Icc 1 M) :
      ∑ s ∈ Icc 1 M, (if s ≤ r then (M / r) ^ 2 else 0) = r * (M / r) ^ 2 := by
    have hf : (Icc 1 M).filter (fun s => s ≤ r) = Icc 1 r := by
      ext s
      simp only [mem_filter, mem_Icc]
      have := (mem_Icc.mp hr).2
      omega
    rw [← sum_filter, hf]
    simp
  calc
    _ ≤ ∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M,
        ((if s ≤ r then (M / r) ^ 2 else 0) + (if r ≤ s then (M / s) ^ 2 else 0)) := by
      exact sum_le_sum (fun r hr => sum_le_sum (fun s hs => hpoint r s))
    _ = (∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, if s ≤ r then (M / r) ^ 2 else 0) +
        (∑ s ∈ Icc 1 M, ∑ r ∈ Icc 1 M, if r ≤ s then (M / s) ^ 2 else 0) := by
      simp only [sum_add_distrib]
      congr 1
      exact sum_comm
    _ = _ := by
      rw [sum_congr rfl hsum]
      omega

lemma sum_floor_sq_bound (M : ℕ) :
    (∑ r ∈ Icc 1 M, (r : ℝ) * (M / r : ℕ) ^ 2) ≤ (M : ℝ) ^ 2 * harmonic M := by
  have hp (r : ℕ) (hr : r ∈ Icc 1 M) :
      (r : ℝ) * (M / r : ℕ) ^ 2 ≤ (M : ℝ) ^ 2 / r := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    have hprod : (r : ℝ) * (M / r : ℕ) ≤ M := by exact_mod_cast Nat.mul_div_le M r
    apply (le_div_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (show (0:ℝ) ≤ r * (M / r : ℕ) by positivity)
      (sub_nonneg.mpr hprod)]
  calc
    _ ≤ ∑ r ∈ Icc 1 M, (M : ℝ) ^ 2 / r := sum_le_sum hp
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [div_eq_mul_inv, mul_sum]

lemma productQuads_log_bound (M : ℕ) :
    ((productQuads M).card : ℝ) ≤ 2 * (M : ℝ) ^ 2 * (1 + Real.log M) := by
  have hnat := (productQuads_card_le M).trans (max_sum_bound M)
  have hreal : ((productQuads M).card : ℝ) ≤
      2 * ∑ r ∈ Icc 1 M, (r : ℝ) * (M / r : ℕ) ^ 2 := by exact_mod_cast hnat
  have h := sum_floor_sq_bound M
  have hh := harmonic_le_one_add_log M
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (M : ℝ))
  nlinarith

lemma squareCollisions_card_le_productQuads (N : ℕ) :
    (squareCollisions N).card ≤ (productQuads (2 * N)).card := by
  apply Finset.card_le_card_of_injOn
    (fun t : (ℕ × ℕ) × (ℕ × ℕ) =>
      ((t.1.1 - t.1.2, t.2.2 - t.2.1), (t.1.1 + t.1.2, t.2.2 + t.2.1)))
  · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ht
    obtain ⟨ht, hab, he⟩ := mem_filter.mp ht
    dsimp only at hab he
    simp only [mem_product, mem_Icc] at ht
    have hcd : c < d := by nlinarith
    apply mem_filter.mpr
    constructor
    · simp only [mem_product, mem_Icc]
      exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
        ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
    · have hab' := Nat.sub_add_cancel hab.le
      have hcd' := Nat.sub_add_cancel hcd.le
      dsimp
      nlinarith only [he, hab', hcd']
  · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ht ⟨⟨a',b'⟩,⟨c',d'⟩⟩ ht' hh
    obtain ⟨_, hab, he⟩ := mem_filter.mp ht
    obtain ⟨_, hab', he'⟩ := mem_filter.mp ht'
    dsimp only at hab he hab' he' hh
    have hcd : c < d := by nlinarith
    have hcd' : c' < d' := by nlinarith
    simp only [Prod.mk.injEq] at hh
    obtain ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ := hh
    have haa : a = a' := by omega
    have hbb : b = b' := by omega
    have hcc : c = c' := by omega
    have hdd : d = d' := by omega
    simp [haa,hbb,hcc,hdd]

lemma squareCollisions_log_bound (N : ℕ) :
    ((squareCollisions N).card : ℝ) ≤
      8 * (N : ℝ) ^ 2 * (1 + Real.log (2 * N)) := by
  have h1 : ((squareCollisions N).card : ℝ) ≤ (productQuads (2 * N)).card := by
    exact_mod_cast squareCollisions_card_le_productQuads N
  have h2 := productQuads_log_bound (2 * N)
  push_cast at h2
  nlinarith only [h1,h2]

#print axioms productQuads_log_bound
#print axioms squareCollisions_log_bound
end Erdos773.AverageCollision
