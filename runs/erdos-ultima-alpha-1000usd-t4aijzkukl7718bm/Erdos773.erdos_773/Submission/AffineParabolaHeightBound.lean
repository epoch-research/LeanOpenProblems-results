import Submission.AffineParabolaLevelBound

/-!
A two-thirds height ceiling for root representatives with an affine carry
target. The hypotheses describe a particular modular-lift mechanism, not
all Sidon subsets of squares.
-/
namespace Erdos773.AffineParabolaHeightBound
open Finset AffineParabolaLevelBound
set_option maxHeartbeats 2000000

lemma quadratic_div {p b a n : ℕ} (hp : 0 < p) (hn : n=b+p*a) :
    n^2/p=b^2/p+2*b*a+p*a^2 := by
  have he : n^2=b^2+p*(2*b*a+p*a^2) := by rw [hn]; ring
  rw [he,Nat.add_mul_div_left _ _ hp]
  omega

lemma carry_level {p b a n : ℕ} (hp : 0 < p) {lam μ : ℤ}
    (hmod : n%p=b) (ha : n/p=a)
    (hc : ((n^2/p : ℕ):ℤ) ≡ lam*b+μ [ZMOD (p:ℤ)]) :
    (b:ℤ)^2/(p:ℤ)+(2*(a:ℤ)-lam)*b ≡ μ [ZMOD (p:ℤ)] := by
  have hn := Nat.mod_add_div n p
  rw [hmod,ha] at hn
  have hd := quadratic_div hp hn.symm
  obtain ⟨k,hk⟩ := hc.dvd
  apply Int.modEq_iff_dvd.mpr
  refine ⟨k+(a:ℤ)^2,?_⟩
  rw [hd] at hk
  push_cast at hk
  linear_combination hk

/-- Partitioning by the root quotient gives a uniform square-root bound
per level, for any positive modulus and any integer affine target. -/
theorem height_square_bound (p N : ℕ) (hp : 0 < p) (lam μ : ℤ)
    (B : Finset ℕ) (f : ℕ → ℕ) (hB : ∀ b ∈ B, b < p)
    (hmod : ∀ b ∈ B, f b%p=b) (hN : ∀ b ∈ B, f b ≤ N)
    (hc : ∀ b ∈ B, (((f b)^2/p : ℕ):ℤ) ≡ lam*b+μ [ZMOD (p:ℤ)]) :
    B.card^2 ≤ 1600*p*(N/p+1)^2 := by
  let H := N/p
  let F (a : ℕ) := B.filter (fun b => f b/p=a)
  have hlevel (a : ℕ) : (F a).card^2 ≤ 1600*p := by
    let S := (F a).image (fun b : ℕ => (b:ℤ))
    have hScard : S.card=(F a).card := card_image_of_injective _ Int.ofNat_injective
    have hS : ∀ b ∈ S, 0 ≤ b ∧ b ≤ p := by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      have hh := hB c (mem_filter.mp hc).1
      constructor <;> omega
    have hcarry : ∀ b ∈ S, b^2/(p:ℤ)+(2*(a:ℤ)-lam)*b ≡ μ [ZMOD (p:ℤ)] := by
      intro b hb
      obtain ⟨c,hcMem,rfl⟩ := mem_image.mp hb
      obtain ⟨hcB,hca⟩ := mem_filter.mp hcMem
      exact carry_level hp (hmod c hcB) hca (hc c hcB)
    have hh := level_card_sq p hp (2*(a:ℤ)-lam) μ S hS hcarry
    simpa only [hScard] using hh
  have hsum : B.card=∑ a ∈ range (H+1), (F a).card := by
    apply card_eq_sum_card_fiberwise
    intro b hb
    apply mem_range.mpr
    have hh := Nat.div_le_div_right (hN b hb) (c:=p)
    dsimp only [H]
    omega
  have hCS := sq_sum_le_card_mul_sum_sq (s:=range (H+1)) (f:=fun a => (F a).card)
  have hsum2 : (∑ a ∈ range (H+1), (F a).card^2) ≤ (H+1)*(1600*p) := by
    calc
      _ ≤ ∑ _a ∈ range (H+1), 1600*p := sum_le_sum (fun a _ => hlevel a)
      _ = _ := by simp
  rw [← hsum,card_range] at hCS
  have hh := hCS.trans (Nat.mul_le_mul_left (H+1) hsum2)
  dsimp only [H] at hh
  nlinarith only [hh]

/-- Below the first modulus, the unit affine target makes the square
quotient injective. This handles a range not covered by the large-height
level estimate alone. -/
theorem small_height_card (p N : ℕ) (hNp : N < p) (lam μ : ℤ)
    (hunit : IsCoprime (p:ℤ) lam) (B : Finset ℕ) (f : ℕ → ℕ)
    (hB : ∀ b ∈ B, b < p) (hmod : ∀ b ∈ B, f b%p=b)
    (hN : ∀ b ∈ B, f b ≤ N)
    (hc : ∀ b ∈ B, (((f b)^2/p : ℕ):ℤ) ≡ lam*b+μ [ZMOD (p:ℤ)]) :
    B.card ≤ N^2/p+1 := by
  have hf (b : ℕ) (hb : b ∈ B) : f b=b := by
    have hm := hmod b hb
    rw [Nat.mod_eq_of_lt ((hN b hb).trans_lt hNp)] at hm
    exact hm
  have hh : B.card ≤ (range (N^2/p+1)).card := by
    apply card_le_card_of_injOn (fun b => b^2/p)
    · intro b hb
      apply mem_range.mpr
      have hbN : b ≤ N := by rw [← hf b hb]; exact hN b hb
      have hdiv := Nat.div_le_div_right (Nat.pow_le_pow_left hbN 2) (c:=p)
      dsimp only
      omega
    · intro b hb c hcB he
      dsimp only at he
      have hbcon := hc b hb
      have hccon := hc c hcB
      rw [hf b hb] at hbcon
      rw [hf c hcB,← he] at hccon
      have hmul : lam*(b:ℤ)+μ ≡ lam*c+μ [ZMOD (p:ℤ)] := hbcon.symm.trans hccon
      have hd : (p:ℤ) ∣ lam*((c:ℤ)-b) := by
        convert hmul.dvd using 1; ring
      have hdiff := hunit.dvd_of_dvd_mul_left hd
      have hcon : (b:ℤ) ≡ c [ZMOD (p:ℤ)] := Int.modEq_iff_dvd.mpr hdiff
      exact (Int.natCast_modEq_iff.mp hcon).eq_of_lt_of_lt (hB b hb) (hB c hcB)
  simpa only [card_range] using hh

/-- Arbitrary choices of root representatives with a fixed unit-affine
carry target obey a two-thirds height ceiling. Primality and Sidonness are
not assumed. The root's residue must equal its supplied nonzero label. -/
theorem affine_height_card_ceiling (p N : ℕ) (hp : 0 < p) (lam μ : ℤ)
    (hunit : IsCoprime (p:ℤ) lam) (B : Finset ℕ) (f : ℕ → ℕ)
    (hB : ∀ b ∈ B, 0 < b ∧ b < p) (hmod : ∀ b ∈ B, f b%p=b)
    (hN : ∀ b ∈ B, f b ≤ N)
    (hc : ∀ b ∈ B, (((f b)^2/p : ℕ):ℤ) ≡ lam*b+μ [ZMOD (p:ℤ)]) :
    B.card^3 ≤ 6400*N^2 := by
  have hlabels : B.card ≤ p := by
    have hh : B ⊆ range p := fun b hb => mem_range.mpr (hB b hb).2
    simpa only [card_range] using card_le_card hh
  have hsq := height_square_bound p N hp lam μ B f (fun b hb => (hB b hb).2) hmod hN hc
  by_cases hzero : N=0
  · subst N
    have he : B=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      have hn := hN b hb
      have hm := hmod b hb
      have hb₀ := (hB b hb).1
      have hz : f b=0 := by omega
      rw [hz,Nat.zero_mod] at hm
      omega
    simp [he]
  · have hN₁ : 1 ≤ N := Nat.pos_of_ne_zero hzero
    by_cases hpN : p ≤ N
    · have hpH : p*(N/p+1) ≤ 2*N := by
        have hh := Nat.mul_div_le N p
        nlinarith only [hh,hpN]
      calc
        B.card^3 = B.card*B.card^2 := by ring
        _ ≤ p*(1600*p*(N/p+1)^2) := Nat.mul_le_mul hlabels hsq
        _ = 1600*(p*(N/p+1))^2 := by ring
        _ ≤ 1600*(2*N)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpH 2)
        _ = 6400*N^2 := by ring
    · have hNp : N < p := by omega
      have hsmall := small_height_card p N hNp lam μ hunit B f
        (fun b hb => (hB b hb).2) hmod hN hc
      rw [Nat.div_eq_of_lt hNp,zero_add,one_pow,mul_one] at hsq
      by_cases hpN2 : p ≤ N^2
      · have hdiv := Nat.mul_div_le (N^2) p
        have hprod : p*(N^2/p+1) ≤ 2*N^2 := by nlinarith only [hdiv,hpN2]
        calc
          B.card^3 = B.card^2*B.card := by ring
          _ ≤ (1600*p)*(N^2/p+1) := Nat.mul_le_mul hsq hsmall
          _ = 1600*(p*(N^2/p+1)) := by ring
          _ ≤ 1600*(2*N^2) := Nat.mul_le_mul_left _ hprod
          _ ≤ 6400*N^2 := by omega
      · have hpN2' : N^2 < p := by omega
        rw [Nat.div_eq_of_lt hpN2',zero_add] at hsmall
        have hm : B.card^3 ≤ 1 := by simpa only [one_pow] using Nat.pow_le_pow_left hsmall 3
        have hn : 1 ≤ N^2 := Nat.one_le_pow _ _ hN₁
        omega

/-- The same construction ceiling, allowing an independent residue sign at
 every label. No prime modulus or Sidon hypothesis is needed. -/
theorem signed_affine_height_card_ceiling (p N : ℕ) (hp : 0 < p) (lam μ : ℤ)
    (hunit : IsCoprime (p:ℤ) lam) (B : Finset ℕ) (f : ℕ → ℕ)
    (hB : ∀ b ∈ B, 0 < b ∧ b < p)
    (hmod : ∀ b ∈ B, f b%p=b ∨ f b%p=p-b)
    (hN : ∀ b ∈ B, f b ≤ N)
    (hc : ∀ b ∈ B, (((f b)^2/p : ℕ):ℤ) ≡ lam*b+μ [ZMOD (p:ℤ)]) :
    B.card^3 ≤ 51200*N^2 := by
  let L := B.filter (fun b => f b%p=b)
  let R := B.filter (fun b => ¬ f b%p=b)
  have hLR : L.card+R.card=B.card := card_filter_add_card_filter_not _
  have hL : L.card^3 ≤ 6400*N^2 := by
    apply affine_height_card_ceiling p N hp lam μ hunit L f
    · exact fun b hb => hB b (mem_filter.mp hb).1
    · exact fun b hb => (mem_filter.mp hb).2
    · exact fun b hb => hN b (mem_filter.mp hb).1
    · exact fun b hb => hc b (mem_filter.mp hb).1
  let C := R.image (fun b => p-b)
  have hCcard : C.card=R.card := by
    apply card_image_of_injOn
    intro b hb c hc he
    have hb' := hB b (mem_filter.mp hb).1
    have hc' := hB c (mem_filter.mp hc).1
    dsimp only at he
    omega
  have hC : ∀ c ∈ C, 0 < c ∧ c < p := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
    have hh := hB b (mem_filter.mp hb).1
    omega
  have hR : R.card^3 ≤ 6400*N^2 := by
    rw [← hCcard]
    apply affine_height_card_ceiling p N hp (-lam) μ hunit.neg_right C
      (fun c => f (p-c)) hC
    · intro c hc
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
      obtain ⟨hbB,hbnot⟩ := mem_filter.mp hb
      rw [Nat.sub_sub_self (hB b hbB).2.le]
      exact (hmod b hbB).resolve_left hbnot
    · intro c hc
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
      have hbB := (mem_filter.mp hb).1
      rw [Nat.sub_sub_self (hB b hbB).2.le]
      exact hN b hbB
    · intro c hcMem
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hcMem
      have hbB := (mem_filter.mp hb).1
      rw [Nat.sub_sub_self (hB b hbB).2.le]
      apply (hc b hbB).trans
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-lam, ?_⟩
      rw [Nat.cast_sub (hB b hbB).2.le]
      ring
  have hcube : (L.card+R.card)^3 ≤ 4*(L.card^3+R.card^3) := by
    have hh : 0 ≤ ((L.card:ℤ)-R.card)^2*((L.card:ℤ)+R.card) :=
      mul_nonneg (sq_nonneg _) (by omega)
    have hh' : ((L.card:ℤ)+R.card)^3 ≤ 4*((L.card:ℤ)^3+(R.card:ℤ)^3) := by
      nlinarith only [hh]
    exact_mod_cast hh'
  rw [hLR] at hcube
  omega

#print axioms height_square_bound
#print axioms small_height_card
#print axioms affine_height_card_ceiling
#print axioms signed_affine_height_card_ceiling
end Erdos773.AffineParabolaHeightBound
