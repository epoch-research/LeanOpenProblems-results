import Submission.LowCollisionSelection

/-!
Finite Sidon extraction for strictly increasing images using four-entry
collision counts. Three-entry obstructions cost only a factor of four.
-/
namespace Erdos773.MonotoneSidonSelection
open Finset LowCollisionSelection
set_option maxHeartbeats 1000000

/-- Strictly ordered four-root collisions under an increasing map. -/
def collisions (A : Finset ℕ) (f : ℕ → ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun q =>
    q.1.1 < q.1.2 ∧ q.1.2 < q.2.1 ∧ q.2.1 < q.2.2 ∧
      f q.1.1+f q.2.2 = f q.1.2+f q.2.1)

private lemma ordered_presentation (f : ℕ → ℕ) (hf : StrictMono f) {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (he : f a + f b = f c + f d) :
    ∃ u v w x : ℕ, u < v ∧ v < w ∧ w < x ∧
      f u + f x = f v + f w ∧
      ({u,v,w,x} : Finset ℕ) = {a,b,c,d} := by
  let u := min a b
  let v := max a b
  let w := min c d
  let x := max c d
  have huv : u < v := min_lt_max.mpr hab
  have hwx : w < x := min_lt_max.mpr hcd
  have huw : u ≠ w := by dsimp [u,w]; omega
  have he' : f u + f v = f w + f x := by
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
      have hh := hf huw
      have hh' := hf.monotone h
      omega
    refine ⟨u,w,x,v,huw,hwx,hxv,he', ?_⟩
    calc
      _ = ({u,v,w,x} : Finset ℕ) := by ext n; simp [or_comm, or_left_comm, or_assoc]
      _ = _ := hs
  · have hvx : v < x := by
      by_contra! h
      have hh := hf hwu
      have hh' := hf.monotone h
      omega
    refine ⟨w,u,v,x,hwu,huv,hvx,he'.symm, ?_⟩
    calc
      _ = ({u,v,w,x} : Finset ℕ) := by ext n; simp [or_comm, or_left_comm, or_assoc]
      _ = _ := hs

private def support (f : ℕ → ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ :=
  {f q.1.1, f q.1.2, f q.2.1, f q.2.2}

/-- Each four-entry support has a strictly increasing collision presentation.
Thus no factor for ordered presentations is lost in the local count. -/
theorem fourSupports_card_le (A : Finset ℕ) (f : ℕ → ℕ) (hf : StrictMono f) :
    (fourSupports (A.image f)).card ≤
      (collisions A f).card := by
  classical
  let S := A.image f
  apply le_trans _ (card_image_le (f := support f) (s := collisions A f))
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
    have hnorm : f r + f t = f s + f v := by rw [hra, htc, hsb, hvd]; exact heq
    obtain ⟨u,w,x,y,huw,hwx,hxy,hnew,he⟩ :=
      ordered_presentation f hf hrt hrs hrv hts htv hsv hnorm
    have hsub : ({u,w,x,y} : Finset ℕ) ⊆ A := by
      rw [he]
      intro n hn
      simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> assumption
    apply mem_image.mpr
    refine ⟨((u,w),(x,y)), mem_filter.mpr ⟨?_,huw,hwx,hxy,hnew⟩, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨hsub (by simp), hsub (by simp)⟩,
        mem_product.mpr ⟨hsub (by simp), hsub (by simp)⟩⟩
    · have hh := congrArg (Finset.image f) he
      simpa [support, hra, hsb, htc, hvd, Finset.insert_comm] using hh
  · exact (Finset.image_injective Subtype.val_injective).injOn

/-- Alteration followed by weak-Sidon extraction. No AP-free assumption. -/
theorem alteration (A : Finset ℕ) (f : ℕ → ℕ) (hf : StrictMono f)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (p*A.card-p^4*(collisions A f).card)/4 ≤
      (maxSidonSubsetCard (A.image f) : ℝ) := by
  let S := A.image f
  have hs : S.card = A.card := card_image_of_injective _ hf.injective
  have hh := finite_max_bound (Subset.refl S) p hp hp1
  have hc : ((fourSupports S).card : ℝ) ≤ (collisions A f).card := by
    exact_mod_cast fourSupports_card_le A f hf
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg hp 4)
  rw [hs] at hh
  linarith

/-- An optimized finite bound given a four-entry collision estimate. -/
theorem finite_lower (A : Finset ℕ) (f : ℕ → ℕ) (hf : StrictMono f)
    (D : ℝ) (hcount : ((collisions A f).card : ℝ) ≤ (A.card : ℝ)*D) :
    7*A.card/(64*(max 1 D)^(1/3 : ℝ)) ≤
      (maxSidonSubsetCard (A.image f) : ℝ) := by
  let R : ℝ := (max 1 D)^(1/3 : ℝ)
  let p : ℝ := 1/(2*R)
  have hR1 : 1 ≤ R := Real.one_le_rpow (le_max_left _ _) (by norm_num)
  have hR : 0 < R := by linarith
  have hR3 : R^3 = max 1 D := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ max 1 D)]
    norm_num
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hpr : p*R = 1/2 := by dsimp [p]; field_simp
  have hDR : D ≤ R^3 := by rw [hR3]; exact le_max_right _ _
  have hcost : p^4*(collisions A f).card ≤ p*A.card/8 := by
    calc
      _ ≤ p^4*((A.card : ℝ)*D) := mul_le_mul_of_nonneg_left hcount (pow_nonneg hp _)
      _ ≤ p^4*((A.card : ℝ)*R^3) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hDR (Nat.cast_nonneg _)) (pow_nonneg hp _)
      _ = p*A.card*(p*R)^3 := by ring
      _ = _ := by rw [hpr]; ring
  have hh := alteration A f hf p hp hp1
  have ht : 7*A.card/(64*R) = 7*p*A.card/32 := by dsimp [p]; ring
  change 7*A.card/(64*R) ≤ _
  rw [ht]
  linarith

#print axioms fourSupports_card_le
#print axioms alteration
#print axioms finite_lower
end Erdos773.MonotoneSidonSelection
