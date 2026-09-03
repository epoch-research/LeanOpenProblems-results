import FormalConjecturesUtil

/-!
Elementary packing estimates for ordered intervals in narrow quadratic bands.
Auxiliary to a construction-specific counting investigation; this is not a
proof or disproof of the square-Sidon conjecture.
-/
namespace Erdos773.QuadraticBandPacking
open Finset
set_option maxHeartbeats 1500000

/-- Widths in later intervals can be charged to the preceding gaps. -/
theorem ordered_width_sum (K : Finset ℤ) (lo hi : ℤ → ℝ)
    (P Q A : ℝ) (hP : 0 < P) (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hbase : ∀ k ∈ K, 0 ≤ lo k ∧ lo k ≤ hi k ∧ hi k-lo k ≤ Q)
    (horder : ∀ i ∈ K, ∀ j ∈ K, i < j → hi i ≤ lo j)
    (hcharge : ∀ i ∈ K, ∀ j ∈ K, i < j →
      P*(hi j-lo j) ≤ 2*A*(lo j-hi i))
    (M : ℝ) (hM : 0 ≤ M) (hupper : ∀ k ∈ K, hi k ≤ M) :
    P*(∑ k ∈ K, (hi k-lo k)) ≤ P*Q+2*A*M := by
  induction K using Finset.induction_on_max generalizing M with
  | h0 => simp; positivity
  | step a K hmax ih =>
    have haK : a ∉ K := fun ha => (lt_irrefl a) (hmax a ha)
    have ha : a ∈ insert a K := mem_insert_self _ _
    have hsub {k : ℤ} (hk : k ∈ K) : k ∈ insert a K := mem_insert_of_mem hk
    have hbaseK : ∀ k ∈ K, 0 ≤ lo k ∧ lo k ≤ hi k ∧ hi k-lo k ≤ Q :=
      fun k hk => hbase k (hsub hk)
    have horderK : ∀ i ∈ K, ∀ j ∈ K, i < j → hi i ≤ lo j :=
      fun i hi j hj hij => horder i (hsub hi) j (hsub hj) hij
    have hchargeK : ∀ i ∈ K, ∀ j ∈ K, i < j →
        P*(hi j-lo j) ≤ 2*A*(lo j-hi i) :=
      fun i hi j hj hij => hcharge i (hsub hi) j (hsub hj) hij
    rw [sum_insert haK,mul_add]
    rcases K.eq_empty_or_nonempty with rfl | hK
    · simp only [sum_empty,mul_zero,add_zero]
      have hh := mul_le_mul_of_nonneg_left (hbase a ha).2.2 hP.le
      have hm := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hA) hM
      linarith only [hh,hm]
    · let b := K.max' hK
      have hb : b ∈ K := max'_mem K hK
      have hb₀ : 0 ≤ hi b := (hbaseK b hb).1.trans (hbaseK b hb).2.1
      have hhi : ∀ k ∈ K, hi k ≤ hi b := by
        intro k hk
        have hkb : k ≤ b := le_max' K k hk
        rcases lt_or_eq_of_le hkb with h | h
        · exact (horderK k hk b hb h).trans (hbaseK b hb).2.1
        · simpa only [h] using (le_refl (hi b))
      have hprev := ih hbaseK horderK hchargeK (hi b) hb₀ hhi
      have hnext := hcharge b (hsub hb) a ha (hmax b hb)
      have hloM : lo a ≤ M := (hbase a ha).2.1.trans (hupper a ha)
      have hmul := mul_le_mul_of_nonneg_left hloM
        (mul_nonneg (by norm_num : (0:ℝ)≤2) hA)
      nlinarith only [hprev,hnext,hmul]

def quad (A B x : ℝ) : ℝ := A*x^2+B*x

/-- The exact convexity inequality needed to charge one band's width. -/
lemma secant_order (A B u v w : ℝ) (hA : 0 ≤ A) (huv : u ≤ v) (hvw : v ≤ w) :
    (w-v)*(quad A B v-quad A B u) ≤ (v-u)*(quad A B w-quad A B v) := by
  have h := mul_nonneg hA (mul_nonneg (sub_nonneg.mpr huv)
    (mul_nonneg (sub_nonneg.mpr hvw) (sub_nonneg.mpr (huv.trans hvw))))
  dsimp [quad]
  nlinarith only [h]

/-- On the increasing branch, a band of height A*p has width at most Q
whenever p<=Q². -/
lemma band_width {A B p Q u v : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q)
    (hpQ : p ≤ Q^2) (huv : u ≤ v) (hderiv : 0 ≤ 2*A*u+B)
    (hband : quad A B v-quad A B u ≤ A*p) : v-u ≤ Q := by
  have h := mul_nonneg hderiv (sub_nonneg.mpr huv)
  have hquad : A*(v-u)^2 ≤ A*p := by
    dsimp [quad] at hband
    nlinarith only [h,hband]
  have hs := (mul_le_mul_iff_right₀ hA).mp hquad
  nlinarith only [hs,hpQ,hQ,huv]

/-- A later band's width is charged to the gap before it. The band period
is p² and its height is A*p. -/
lemma band_charge {A B p u v w : ℝ} (hA : 0 ≤ A) (hp : 0 < p)
    (hsmall : 2*A ≤ p) (huv : u ≤ v) (hvw : v ≤ w)
    (hgap : p^2-A*p ≤ quad A B v-quad A B u)
    (hband : quad A B w-quad A B v ≤ A*p) :
    p*(w-v) ≤ 2*A*(v-u) := by
  have h₁ := mul_le_mul_of_nonneg_left hgap (sub_nonneg.mpr hvw)
  have h₂ := secant_order A B u v w hA huv hvw
  have h₃ := mul_le_mul_of_nonneg_left hband (sub_nonneg.mpr huv)
  have hmain := h₁.trans (h₂.trans h₃)
  have hextra := mul_nonneg (sub_nonneg.mpr hsmall)
    (mul_nonneg hp.le (sub_nonneg.mpr hvw))
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [hmain,hextra]

/-- Monotonicity on the increasing branch, stated in the form needed to
order bands. -/
lemma quad_strict {A B x y : ℝ} (hA : 0 < A) (hxy : x < y)
    (hderiv : 0 ≤ 2*A*x+B) : quad A B x < quad A B y := by
  have hp := mul_pos hA (sq_pos_of_pos (sub_pos.mpr hxy))
  have hn := mul_nonneg hderiv (sub_nonneg.mpr hxy.le)
  dsimp [quad]
  nlinarith only [hp,hn]

#print axioms ordered_width_sum
#print axioms band_width

/-- Count integer points on one increasing quadratic branch. Each integer
band has period p² and height A*p. The number of occupied bands is retained
explicitly, so no unproved distribution estimate is hidden here. -/
theorem branch_card (S : Finset ℤ) (key : ℤ → ℤ)
    (A B p Q L C : ℝ) (hA : 0 < A) (hp : 0 < p) (hQ : 0 ≤ Q)
    (hsmall : 2*A ≤ p) (hpQ : p ≤ Q^2)
    (hcoords : ∀ x ∈ S, L ≤ (x:ℝ) ∧ (x:ℝ) ≤ L+p)
    (hderiv : ∀ x ∈ S, 0 ≤ 2*A*(x:ℝ)+B)
    (hbands : ∀ x ∈ S, (key x:ℝ)*p^2+C ≤ quad A B x ∧
      quad A B x ≤ (key x:ℝ)*p^2+C+A*p) :
    (S.card:ℝ) ≤ (S.image key).card+Q+2*A := by
  classical
  let K := S.image key
  let F (k : ℤ) := S.filter (fun x => key x=k)
  have hF (k : ℤ) (hk : k ∈ K) : (F k).Nonempty := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
    exact ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩
  let lo (k : ℤ) : ℤ := if h : (F k).Nonempty then (F k).min' h else 0
  let hi (k : ℤ) : ℤ := if h : (F k).Nonempty then (F k).max' h else 0
  have hlomem (k : ℤ) (hk : k ∈ K) : lo k ∈ F k := by
    dsimp only [lo]
    rw [dif_pos (hF k hk)]
    exact min'_mem _ _
  have hhimem (k : ℤ) (hk : k ∈ K) : hi k ∈ F k := by
    dsimp only [hi]
    rw [dif_pos (hF k hk)]
    exact max'_mem _ _
  have hbetween (k : ℤ) (hk : k ∈ K) (x : ℤ) (hx : x ∈ F k) :
      lo k ≤ x ∧ x ≤ hi k := by
    dsimp only [lo,hi]
    rw [dif_pos (hF k hk),dif_pos (hF k hk)]
    exact ⟨min'_le _ _ hx,le_max' _ _ hx⟩
  have hlow (k : ℤ) (hk : k ∈ K) : lo k ≤ hi k :=
    (hbetween k hk (hi k) (hhimem k hk)).1
  have hlos (k : ℤ) (hk : k ∈ K) : lo k ∈ S := (mem_filter.mp (hlomem k hk)).1
  have hhis (k : ℤ) (hk : k ∈ K) : hi k ∈ S := (mem_filter.mp (hhimem k hk)).1
  have hloband (k : ℤ) (hk : k ∈ K) :
      (k:ℝ)*p^2+C ≤ quad A B (lo k) ∧ quad A B (lo k) ≤ (k:ℝ)*p^2+C+A*p := by
    simpa only [(mem_filter.mp (hlomem k hk)).2] using hbands (lo k) (hlos k hk)
  have hhiband (k : ℤ) (hk : k ∈ K) :
      (k:ℝ)*p^2+C ≤ quad A B (hi k) ∧ quad A B (hi k) ≤ (k:ℝ)*p^2+C+A*p := by
    simpa only [(mem_filter.mp (hhimem k hk)).2] using hbands (hi k) (hhis k hk)
  have hgap (i : ℤ) (hiK : i ∈ K) (j : ℤ) (hjK : j ∈ K) (hij : i < j) :
      p^2-A*p ≤ quad A B (lo j)-quad A B (hi i) := by
    have hijZ : i+1 ≤ j := by omega
    have hijR : (i:ℝ)+1 ≤ j := by exact_mod_cast hijZ
    have hm := mul_le_mul_of_nonneg_right hijR (sq_nonneg p)
    have hu := (hhiband i hiK).2
    have hl := (hloband j hjK).1
    nlinarith only [hm,hu,hl]
  have horder (i : ℤ) (hiK : i ∈ K) (j : ℤ) (hjK : j ∈ K) (hij : i < j) :
      (hi i:ℝ) ≤ lo j := by
    have hg := hgap i hiK j hjK hij
    have hpos : 0 < p^2-A*p := by
      have hh := mul_pos hp (show 0 < p-A by linarith only [hsmall,hp])
      nlinarith only [hh]
    by_contra hn
    have hh := quad_strict hA (lt_of_not_ge hn) (hderiv (lo j) (hlos j hjK))
    linarith only [hg,hpos,hh]
  have hwidth := ordered_width_sum K
    (fun k => (lo k:ℝ)-L) (fun k => (hi k:ℝ)-L) p Q A hp hQ hA.le
    (fun k hk => ?_) (fun i hiK j hjK hij => ?_)
    (fun i hiK j hjK hij => ?_) p hp.le (fun k hk => ?_)
  · have heq : (∑ k ∈ K, (((hi k:ℝ)-L)-((lo k:ℝ)-L))) =
        ∑ k ∈ K, ((hi k:ℝ)-lo k) := by
      apply sum_congr rfl
      intro k hk
      ring
    rw [heq] at hwidth
    have hs : (∑ k ∈ K, ((hi k:ℝ)-lo k)) ≤ Q+2*A := by
      apply (mul_le_mul_iff_right₀ hp).mp
      nlinarith only [hwidth]
    have hcard (k : ℤ) (hk : k ∈ K) : (F k).card ≤ hi k-lo k+1 := by
      have hsub : F k ⊆ Icc (lo k) (hi k) := by
        intro x hx
        exact mem_Icc.mpr (hbetween k hk x hx)
      have hc := card_le_card hsub
      rw [Int.card_Icc] at hc
      have hnonneg : 0 ≤ hi k+1-lo k := by have := hlow k hk; omega
      have hcZ : ((F k).card:ℤ) ≤ ((hi k+1-lo k).toNat:ℤ) := by exact_mod_cast hc
      rw [Int.toNat_of_nonneg hnonneg] at hcZ
      omega
    have htotal : S.card = ∑ k ∈ K, (F k).card :=
      card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem key hx)
    calc
      (S.card:ℝ) = ∑ k ∈ K, ((F k).card:ℝ) := by exact_mod_cast htotal
      _ ≤ ∑ k ∈ K, ((hi k:ℝ)-lo k+1) := by
        apply sum_le_sum
        intro k hk
        exact_mod_cast hcard k hk
      _ = (∑ k ∈ K, ((hi k:ℝ)-lo k))+(K.card:ℝ) := by simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
      _ ≤ (S.image key).card+Q+2*A := by dsimp only [K] at hs ⊢; linarith only [hs]
  · have hlo := (hcoords (lo k) (hlos k hk)).1
    have hlh : (lo k:ℝ) ≤ hi k := by exact_mod_cast hlow k hk
    have hb : quad A B (hi k)-quad A B (lo k) ≤ A*p := by
      have hu := (hhiband k hk).2
      have hl := (hloband k hk).1
      linarith only [hu,hl]
    have hw := band_width hA hQ hpQ hlh (hderiv (lo k) (hlos k hk)) hb
    exact ⟨by linarith only [hlo],by linarith only [hlh],by linarith only [hw]⟩
  · have hh := horder i hiK j hjK hij
    linarith only [hh]
  · have hlh : (lo j:ℝ) ≤ hi j := by exact_mod_cast hlow j hjK
    have hb : quad A B (hi j)-quad A B (lo j) ≤ A*p := by
      have hu := (hhiband j hjK).2
      have hl := (hloband j hjK).1
      linarith only [hu,hl]
    have hh := band_charge hA.le hp hsmall (horder i hiK j hjK hij) hlh
      (hgap i hiK j hjK hij) hb
    linarith only [hh]
  · have hh := (hcoords (hi k) (hhis k hk)).2
    linarith only [hh]

#print axioms branch_card

#print axioms band_charge
end Erdos773.QuadraticBandPacking
