import Submission.OrderedCollisionDefect
import Submission.PartialResidueFibers

/-!
# Coarsely separated blocks of integer squares

Ordinary Sidon marks can be rounded to square-root centers, with a buffer
large enough that every collision identifies the unordered pair of blocks.
This does not remove collisions between two matched blocks. The final
criterion retains their actual positive-difference compatibility explicitly.
-/
namespace Erdos773.RoundedSidonBlocks
open Finset PartialResidueFibers
set_option maxHeartbeats 1000000

/-- Spacing of the ideal square values. -/
def scale (L H : ℕ) : ℕ := 1024*L*(H+1)^2

def center (L H a : ℕ) : ℕ := Nat.sqrt (scale L H*(L+a))

def error (L H : ℕ) : ℕ := 130*L*(H+1)^2

def block (L H a : ℕ) : Finset ℕ := Icc (center L H a) (center L H a+H)

def values (L H a : ℕ) : Finset ℕ := (block L H a).image (fun n => n^2)

lemma center_lower (L H a : ℕ) : 32*L*(H+1) ≤ center L H a := by
  apply Nat.le_sqrt'.mpr
  change (32*L*(H+1))^2 ≤ scale L H*(L+a)
  calc
    _ = scale L H*L := by dsimp [scale]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

lemma center_upper (L H a : ℕ) (ha : a ≤ L) :
    center L H a ≤ 64*L*(H+1) := by
  have ht : scale L H*(L+a) ≤ (64*L*(H+1))^2 := by
    calc
      _ ≤ scale L H*(2*L) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := by dsimp [scale]; nlinarith
  have hs := Nat.sqrt_le' (scale L H*(L+a))
  change center L H a ^ 2 ≤ _ at hs
  by_contra! h
  have hh := Nat.pow_lt_pow_left h (by decide : (2 : ℕ) ≠ 0)
  exact (not_lt_of_ge (hs.trans ht)) hh

/-- Both signs of the rounding and block-width error are controlled. -/
lemma square_bounds (L H a n : ℕ) (hL : 0 < L) (ha : a ≤ L)
    (hn : n ∈ block L H a) :
    scale L H*(L+a) ≤ n^2+error L H ∧
      n^2 ≤ scale L H*(L+a)+error L H := by
  obtain ⟨hn0, hn1⟩ := mem_Icc.mp hn
  have hc := center_upper L H a ha
  have hs := Nat.sqrt_le' (scale L H*(L+a))
  have ht := Nat.sqrt_le_add (scale L H*(L+a))
  change center L H a ^ 2 ≤ _ at hs
  change scale L H*(L+a) ≤ center L H a*center L H a+
    center L H a+center L H a at ht
  have hn2 := Nat.pow_le_pow_left hn0 2
  have hn3 := Nat.pow_le_pow_left hn1 2
  have hH2 : H^2 ≤ L*(H+1)^2 := by
    calc
      _ ≤ (H+1)^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ _ := Nat.le_mul_of_pos_left _ hL
  have hcross := Nat.mul_le_mul_right H hc
  constructor
  · dsimp [error]
    have hf := Nat.mul_le_mul_left (128*L)
      (show H+1 ≤ (H+1)^2 by nlinarith)
    nlinarith only [ht, hn2, hc, hf]
  · dsimp [error]
    nlinarith only [hn3, hs, hcross, hH2]

lemma four_errors_lt_scale (L H : ℕ) (hL : 0 < L) :
    4*error L H < scale L H := by
  have hp : 0 < L*(H+1)^2 := by positivity
  dsimp [error, scale]
  nlinarith only [hp]

/-- Rounding cannot change the sum of the ordinary integer marks. -/
theorem mark_sum_eq (L H a b c d x y z w : ℕ) (hL : 0 < L)
    (ha : a ≤ L) (hb : b ≤ L) (hc : c ≤ L) (hd : d ≤ L)
    (hx : x ∈ block L H a) (hy : y ∈ block L H b)
    (hz : z ∈ block L H c) (hw : w ∈ block L H d)
    (he : x^2+y^2=z^2+w^2) : a+b=c+d := by
  obtain ⟨hxa,hax⟩ := square_bounds L H a x hL ha hx
  obtain ⟨hyb,hby⟩ := square_bounds L H b y hL hb hy
  obtain ⟨hzc,hcz⟩ := square_bounds L H c z hL hc hz
  obtain ⟨hwd,hdw⟩ := square_bounds L H d w hL hd hw
  have hgap := four_errors_lt_scale L H hL
  have hleft : scale L H*(a+b) ≤ scale L H*(c+d)+4*error L H := by
    nlinarith only [hxa, hyb, hcz, hdw, he]
  have hright : scale L H*(c+d) ≤ scale L H*(a+b)+4*error L H := by
    nlinarith only [hzc, hwd, hax, hby, he]
  rcases lt_trichotomy (a+b) (c+d) with hh | hh | hh
  · have hm := Nat.mul_le_mul_left (scale L H) (show a+b+1 ≤ c+d by omega)
    nlinarith only [hm, hright, hgap]
  · exact hh
  · have hm := Nat.mul_le_mul_left (scale L H) (show c+d+1 ≤ a+b by omega)
    nlinarith only [hm, hleft, hgap]

/-- A Sidon mark set supplies exact matching of the block labels. -/
theorem pair_matching (L H : ℕ) (A : Finset ℕ) (hL : 0 < L)
    (hbound : ∀ a ∈ A, a ≤ L) (hA : IsSidon (A : Set ℕ))
    {a b c d x y z w : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hd : d ∈ A)
    (hx : x ∈ block L H a) (hy : y ∈ block L H b)
    (hz : z ∈ block L H c) (hw : w ∈ block L H d)
    (he : x^2+y^2=z^2+w^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  exact hA a ha c hc b hb d hd
    (mark_sum_eq L H a b c d x y z w hL
      (hbound a ha) (hbound b hb) (hbound c hc) (hbound d hd) hx hy hz hw he)

lemma blocks_disjoint (L H a b : ℕ) (hL : 0 < L)
    (ha : a ≤ L) (hb : b ≤ L) (hne : a ≠ b) :
    Disjoint (block L H a) (block L H b) := by
  apply disjoint_left.mpr
  intro n hna hnb
  have hh := mark_sum_eq L H a a b b n n n n hL ha ha hb hb hna hna hnb hnb rfl
  omega

lemma values_disjoint (L H a b : ℕ) (hL : 0 < L)
    (ha : a ≤ L) (hb : b ≤ L) (hne : a ≠ b) :
    Disjoint (values L H a) (values L H b) := by
  apply disjoint_left.mpr
  intro v hva hvb
  obtain ⟨x,hx,hxv⟩ := mem_image.mp hva
  obtain ⟨y,hy,hyv⟩ := mem_image.mp hvb
  have hxy : x=y := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) (hxv.trans hyv.symm)
  subst y
  exact disjoint_left.mp (blocks_disjoint L H a b hL ha hb hne) hx hy

lemma root_height (L H a n : ℕ) (hL : 0 < L) (ha : a ≤ L)
    (hn : n ∈ block L H a) : 0 < n ∧ n ≤ 65*L*(H+1) := by
  obtain ⟨hn0,hn1⟩ := mem_Icc.mp hn
  have hlo := center_lower L H a
  have hhi := center_upper L H a ha
  have hp : 0 < L*(H+1) := by positivity
  have hH : H ≤ L*(H+1) := by
    calc
      _ ≤ H+1 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ hL
  constructor <;> nlinarith only [hn0,hn1,hlo,hhi,hp,hH]

lemma values_card (L H a : ℕ) : (values L H a).card = H+1 := by
  rw [values, card_image_of_injective _ (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0))]
  simp only [block, Nat.card_Icc]
  omega

/-- The coarse construction has no loss from overlaps between blocks. -/
theorem union_card (L H : ℕ) (A : Finset ℕ) (hL : 0 < L)
    (hbound : ∀ a ∈ A, a ≤ L) :
    (A.biUnion (values L H)).card = A.card*(H+1) := by
  rw [card_biUnion]
  · simp only [values_card, sum_const, smul_eq_mul]
  · intro a ha b hb hab
    exact values_disjoint L H a b hL (hbound a ha) (hbound b hb) hab

/-- All values in the construction are positive squares at the stated height. -/
theorem union_subset_squares (L H : ℕ) (A : Finset ℕ) (hL : 0 < L)
    (hbound : ∀ a ∈ A, a ≤ L) :
    A.biUnion (values L H) ⊆
      (Icc 1 (65*L*(H+1))).image (fun n : ℕ => n^2) := by
  intro v hv
  obtain ⟨a,ha,hv⟩ := mem_biUnion.mp hv
  obtain ⟨n,hn,rfl⟩ := mem_image.mp hv
  obtain ⟨hn0,hn1⟩ := root_height L H a n hL (hbound a ha) hn
  exact mem_image.mpr ⟨n,mem_Icc.mpr ⟨by omega,hn1⟩,rfl⟩

/-- Full blocks are individually Sidon when their width is at most `L`. -/
theorem block_sidon (L H a : ℕ) (hH : H ≤ L) :
    IsSidon (values L H a : Set ℕ) := by
  apply OrderedCollisionDefect.short_interval_squares_sidon
  have hlo := center_lower L H a
  have hh := Nat.mul_le_mul_right (H+1) hH
  nlinarith only [hlo, hh]

private lemma identify_aligned {A : Finset ℕ} {V : ℕ → Finset ℕ}
    (hV : ∀ a ∈ A, IsSidon (V a : Set ℕ)) (hC : Compatible A V)
    {a b x y z w : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hx : x ∈ V a) (hy : y ∈ V b) (hz : z ∈ V a) (hw : w ∈ V b)
    (he : x+y=z+w) : (x=z ∧ y=w) ∨ (x=w ∧ y=z) := by
  by_cases hab : a=b
  · subst b
    exact hV a ha x hx z hz y hy w hw he
  have hd := disjoint_left.mp (hC a ha b hb hab)
  rcases lt_trichotomy x z with h | h | h
  · exact (hd (mem_positiveDiffs.mpr ⟨x,hx,z,hz,h,rfl⟩)
      (mem_positiveDiffs.mpr ⟨w,hw,y,hy,by omega,by omega⟩)).elim
  · exact Or.inl ⟨h,by omega⟩
  · exact (hd (mem_positiveDiffs.mpr ⟨z,hz,x,hx,h,rfl⟩)
      (mem_positiveDiffs.mpr ⟨y,hy,w,hw,by omega,by omega⟩)).elim

/-- The criterion applies to arbitrary selected subsets of the blocks.
No fullness of the selected index sets is assumed. -/
theorem partial_union_sidon_iff (L H : ℕ) (A : Finset ℕ) (V : ℕ → Finset ℕ)
    (hL : 0 < L) (hH : H ≤ L) (hbound : ∀ a ∈ A, a ≤ L)
    (hA : IsSidon (A : Set ℕ)) (hsub : ∀ a ∈ A, V a ⊆ values L H a) :
    IsSidon (A.biUnion V : Set ℕ) ↔ Compatible A V := by
  have hV (a : ℕ) (ha : a ∈ A) : IsSidon (V a : Set ℕ) :=
    Set.IsSidon.subset (block_sidon L H a hH) (hsub a ha)
  have hdis (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ A) (hab : a ≠ b) :
      Disjoint (V a) (V b) :=
    (values_disjoint L H a b hL (hbound a ha) (hbound b hb) hab).mono
      (hsub a ha) (hsub b hb)
  have hinc (a : ℕ) (ha : a ∈ A) : V a ⊆ A.biUnion V := by
    intro v hv
    exact mem_biUnion.mpr ⟨a,ha,hv⟩
  constructor
  · intro hS a ha b hb hab
    apply disjoint_left.mpr
    intro D hDa hDb
    obtain ⟨x,hx,y,hy,hxy,hDxy⟩ := mem_positiveDiffs.mp hDa
    obtain ⟨z,hz,w,hw,hzw,hDzw⟩ := mem_positiveDiffs.mp hDb
    rcases hS x (hinc a ha hx) z (hinc b hb hz) w (hinc b hb hw)
      y (hinc a ha hy) (by omega) with h | h
    · exact disjoint_left.mp (hdis a ha b hb hab) hx (h.1 ▸ hz)
    · omega
  · intro hC x hx z hz y hy w hw he
    obtain ⟨a,ha,hx⟩ := mem_biUnion.mp hx
    obtain ⟨b,hb,hy⟩ := mem_biUnion.mp hy
    obtain ⟨c,hc,hz⟩ := mem_biUnion.mp hz
    obtain ⟨d,hd,hw⟩ := mem_biUnion.mp hw
    have hmatch : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
      obtain ⟨u,hu,hux⟩ := mem_image.mp (hsub a ha hx)
      obtain ⟨v,hv,hvy⟩ := mem_image.mp (hsub b hb hy)
      obtain ⟨s,hs,hsz⟩ := mem_image.mp (hsub c hc hz)
      obtain ⟨t,ht,htw⟩ := mem_image.mp (hsub d hd hw)
      apply pair_matching L H A hL hbound hA ha hb hc hd hu hv hs ht
      simpa only [hux,hvy,hsz,htw] using he
    rcases hmatch with ⟨hac,hbd⟩ | ⟨had,hbc⟩
    · subst c; subst d
      exact identify_aligned hV hC ha hb hx hy hz hw he
    · subst d; subst c
      rcases identify_aligned hV hC ha hb hx hy hw hz (by omega) with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- In the full-block case the only condition left is the actual overlap
of positive difference spectra, not a congruence or an approximate match. -/
theorem full_union_sidon_iff (L H : ℕ) (A : Finset ℕ) (hL : 0 < L)
    (hH : H ≤ L) (hbound : ∀ a ∈ A, a ≤ L) (hA : IsSidon (A : Set ℕ)) :
    IsSidon (A.biUnion (values L H) : Set ℕ) ↔ Compatible A (values L H) :=
  partial_union_sidon_iff L H A _ hL hH hbound hA (fun _ _ => Subset.refl _)

lemma partial_union_card (L H : ℕ) (A : Finset ℕ) (V : ℕ → Finset ℕ)
    (hL : 0 < L) (hbound : ∀ a ∈ A, a ≤ L)
    (hsub : ∀ a ∈ A, V a ⊆ values L H a) :
    (A.biUnion V).card = ∑ a ∈ A, (V a).card := by
  apply card_biUnion
  intro a ha b hb hab
  exact (values_disjoint L H a b hL (hbound a ha) (hbound b hb) hab).mono
    (hsub a ha) (hsub b hb)

/-- A genuine finite lower-bound certificate, conditional on the displayed
compatibility of the selected sets. Compatibility is not asserted to exist. -/
theorem selected_lower (L H : ℕ) (A : Finset ℕ) (V : ℕ → Finset ℕ)
    (hL : 0 < L) (hH : H ≤ L) (hbound : ∀ a ∈ A, a ≤ L)
    (hA : IsSidon (A : Set ℕ)) (hsub : ∀ a ∈ A, V a ⊆ values L H a)
    (hC : Compatible A V) :
    (∑ a ∈ A, (V a).card) ≤
      maxSidonSubsetCard ((Icc 1 (65*L*(H+1))).image (fun n : ℕ => n^2)) := by
  have hs := (partial_union_sidon_iff L H A V hL hH hbound hA hsub).mpr hC
  have hi : A.biUnion V ⊆ A.biUnion (values L H) := by
    intro v hv
    obtain ⟨a,ha,hv⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨a,ha,hsub a ha hv⟩
  have hb := hi.trans (union_subset_squares L H A hL hbound)
  rw [← partial_union_card L H A V hL hbound hsub]
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hb,hs⟩)

end Erdos773.RoundedSidonBlocks

#print axioms Erdos773.RoundedSidonBlocks.mark_sum_eq
#print axioms Erdos773.RoundedSidonBlocks.pair_matching
#print axioms Erdos773.RoundedSidonBlocks.union_card
#print axioms Erdos773.RoundedSidonBlocks.union_subset_squares
#print axioms Erdos773.RoundedSidonBlocks.block_sidon

#print axioms Erdos773.RoundedSidonBlocks.partial_union_sidon_iff
#print axioms Erdos773.RoundedSidonBlocks.full_union_sidon_iff
#print axioms Erdos773.RoundedSidonBlocks.selected_lower
