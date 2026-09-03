import FormalConjecturesUtil

/-!
A restriction on demanding Sidon behavior at every affine shift. This is not
an upper bound for the single unshifted square map in Erdős 773.
-/
namespace Erdos773.UniversalAffineSidonBound
open Finset
set_option maxHeartbeats 2000000

private def pairSum (p : ℕ × ℕ) : ℕ := p.1+p.2
private def squareSum (p : ℕ × ℕ) : ℕ := p.1^2+p.2^2
private def orderedPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun p => p.1 ≤ p.2)
private def fiber (A : Finset ℕ) (s : ℕ) : Finset (ℕ × ℕ) :=
  (orderedPairs A).filter (fun p => pairSum p = s)

private def hull (P : Finset (ℕ × ℕ)) : Finset ℕ :=
  if h : P.Nonempty then
    Icc ((P.image squareSum).min' (h.image _)) ((P.image squareSum).max' (h.image _))
  else ∅

private lemma hull_mem {P : Finset (ℕ × ℕ)} {t : ℕ} (ht : t ∈ hull P) :
    ∃ p ∈ P, ∃ q ∈ P, squareSum p ≤ t ∧ t ≤ squareSum q := by
  unfold hull at ht
  split_ifs at ht with h
  · obtain ⟨hp,hq⟩ := mem_Icc.mp ht
    obtain ⟨p,hpP,hpE⟩ := mem_image.mp (min'_mem (P.image squareSum) (h.image _))
    obtain ⟨q,hqP,hqE⟩ := mem_image.mp (max'_mem (P.image squareSum) (h.image _))
    exact ⟨p,hpP,q,hqP,by simpa [hpE] using hp,by simpa [hqE] using hq⟩
  · simp at ht

private lemma fiber_hull_bound (A : Finset ℕ) (s : ℕ) :
    (fiber A s).card^2 ≤ 2*(hull (fiber A s)).card := by
  by_cases hn : (fiber A s).Nonempty
  · let P := fiber A s
    let F := P.image Prod.fst
    have hF : F.Nonempty := hn.image _
    let a := F.min' hF
    let b := F.max' hF
    have ha : a ∈ F := min'_mem _ _
    have hb : b ∈ F := max'_mem _ _
    obtain ⟨ap,hap,hea⟩ := mem_image.mp ha
    obtain ⟨bp,hbp,heb⟩ := mem_image.mp hb
    have haS := (mem_filter.mp hap).2
    have hbS := (mem_filter.mp hbp).2
    have haO := (mem_filter.mp (mem_filter.mp hap).1).2
    have hbO := (mem_filter.mp (mem_filter.mp hbp).1).2
    have hab : a ≤ b := min'_le F b hb
    have hcard : P.card ≤ b-a+1 := by
      have hi : Set.InjOn Prod.fst (P : Set (ℕ × ℕ)) := by
        intro p hp q hq he
        have hpS := (mem_filter.mp hp).2
        have hqS := (mem_filter.mp hq).2
        apply Prod.ext he
        dsimp [pairSum] at hpS hqS
        omega
      have hc : F.card = P.card := card_image_of_injOn hi
      have hs : F ⊆ Icc a b := by
        intro t ht
        exact mem_Icc.mpr ⟨min'_le _ _ ht,le_max' _ _ ht⟩
      have hh := card_le_card hs
      rw [hc, Nat.card_Icc] at hh
      omega
    let T := P.image squareSum
    have hT : T.Nonempty := hn.image _
    let lo := T.min' hT
    let hi := T.max' hT
    have hlo : lo ≤ squareSum bp := min'_le T _ (mem_image.mpr ⟨bp,hbp,rfl⟩)
    have hhi : squareSum ap ≤ hi := le_max' T _ (mem_image.mpr ⟨ap,hap,rfl⟩)
    have hlh : lo ≤ hi := min'_le T _ (max'_mem _ _)
    have hgap : 2*(b-a)^2 ≤ hi-lo := by
      have hsub := Nat.sub_add_cancel hab
      have hsubT := Nat.sub_add_cancel hlh
      dsimp [pairSum] at haS hbS
      dsimp [squareSum] at hlo hhi
      have hh : 2*(b-a)^2 ≤ squareSum ap-squareSum bp := by
        have h1 : squareSum bp+2*(b-a)^2 ≤ squareSum ap := by
          dsimp [squareSum]
          nlinarith only [haS,hbS,hea,heb,haO,hbO,hsub,
            Nat.zero_le ((b-a)*(bp.2-bp.1)), Nat.sub_add_cancel hbO]
        omega
      dsimp [squareSum] at hh
      omega
    have hhcard : (hull P).card = hi-lo+1 := by
      rw [hull, dif_pos hn, Nat.card_Icc]
      change hi+1-lo = hi-lo+1
      omega
    change P.card^2 ≤ 2*(hull P).card
    rw [hhcard]
    have hc2 := Nat.pow_le_pow_left hcard 2
    have hpoly : (b-a+1)^2 ≤ 4*(b-a)^2+2 := by
      by_cases hh : b-a = 0
      · simp [hh]
      · have hp : 1 ≤ b-a := Nat.one_le_iff_ne_zero.mpr hh
        have hs := Nat.mul_le_mul_left (b-a) hp
        nlinarith only [hs]
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp [hull]

private lemma orderedPairs_card (A : Finset ℕ) :
    A.card^2 ≤ 2*(orderedPairs A).card := by
  have he : A ×ˢ A = orderedPairs A ∪ (orderedPairs A).image Prod.swap := by
    ext p
    constructor
    · intro hp
      by_cases hh : p.1 ≤ p.2
      · exact mem_union_left _ (mem_filter.mpr ⟨hp,hh⟩)
      · apply mem_union_right
        exact mem_image.mpr ⟨p.swap, mem_filter.mpr ⟨by
          simpa only [mem_product, Prod.fst_swap, Prod.snd_swap, and_comm] using hp,
          by dsimp; omega⟩, Prod.swap_swap p⟩
    · intro hp
      rcases mem_union.mp hp with hp | hp
      · exact (mem_filter.mp hp).1
      · obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
        simpa only [mem_product, Prod.fst_swap, Prod.snd_swap, and_comm] using
          (mem_filter.mp hq).1
  have hc := card_union_le (orderedPairs A) ((orderedPairs A).image Prod.swap)
  have hi := card_image_le (s := orderedPairs A) (f := Prod.swap)
  rw [← he, card_product] at hc
  nlinarith only [hc,hi]

/-- Compatible ordering of pair sums and square-pair sums is restrictive.
This condition is stronger than the Sidon property of the square values. -/
theorem monotone_pairs_bound (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hmono : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a+b < c+d → a^2+b^2 < c^2+d^2) :
    A.card^4 ≤ 48*(N+1)^3 := by
  let S := Icc 0 (2*N)
  have hmem {s : ℕ} {p : ℕ × ℕ} (hp : p ∈ fiber A s) :
      p.1 ∈ A ∧ p.2 ∈ A ∧ pairSum p = s := by
    have hh := mem_filter.mp hp
    have hpp := mem_product.mp (mem_filter.mp hh.1).1
    exact ⟨hpp.1,hpp.2,hh.2⟩
  have horder {s t : ℕ} (hst : s < t) {p q : ℕ × ℕ}
      (hp : p ∈ fiber A s) (hq : q ∈ fiber A t) : squareSum p < squareSum q := by
    obtain ⟨hp1,hp2,hps⟩ := hmem hp
    obtain ⟨hq1,hq2,hqs⟩ := hmem hq
    exact hmono _ hp1 _ hp2 _ hq1 _ hq2 (by simpa only [pairSum] using hps.trans_lt (hst.trans_eq hqs.symm))
  have hdisjoint : (S : Set ℕ).PairwiseDisjoint (fun s => hull (fiber A s)) := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro x hxs hxt
    obtain ⟨p,hp,q,hq,hpx,hxq⟩ := hull_mem hxs
    obtain ⟨u,hu,v,hv,hux,hxv⟩ := hull_mem hxt
    rcases lt_or_gt_of_ne hst with hst | hts
    · have hh := horder hst hq hu
      omega
    · have hh := horder hts hv hp
      omega
  have hhull : S.biUnion (fun s => hull (fiber A s)) ⊆ Icc 0 (2*N^2) := by
    intro x hx
    obtain ⟨s,hs,hx⟩ := mem_biUnion.mp hx
    obtain ⟨p,hp,q,hq,hpx,hxq⟩ := hull_mem hx
    obtain ⟨hq1,hq2,_⟩ := hmem hq
    have h1 := Nat.pow_le_pow_left (mem_Icc.mp (hA hq1)).2 2
    have h2 := Nat.pow_le_pow_left (mem_Icc.mp (hA hq2)).2 2
    apply mem_Icc.mpr
    dsimp [squareSum] at hxq
    omega
  have hsumhull : (∑ s ∈ S, (hull (fiber A s)).card) ≤ 2*N^2+1 := by
    rw [← card_biUnion hdisjoint]
    simpa using card_le_card hhull
  have hsumsq : (∑ s ∈ S, (fiber A s).card^2) ≤ 2*(2*N^2+1) := by
    calc
      _ ≤ ∑ s ∈ S, 2*(hull (fiber A s)).card := sum_le_sum (fun s _ => fiber_hull_bound A s)
      _ = 2*(∑ s ∈ S, (hull (fiber A s)).card) := by rw [mul_sum]
      _ ≤ _ := Nat.mul_le_mul_left _ hsumhull
  have hcard : (orderedPairs A).card = ∑ s ∈ S, (fiber A s).card := by
    apply card_eq_sum_card_fiberwise (f := pairSum)
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp (mem_filter.mp hp).1
    have hp1 := (mem_Icc.mp (hA hp1)).2
    have hp2 := (mem_Icc.mp (hA hp2)).2
    change pairSum p ∈ Icc 0 (2*N)
    apply mem_Icc.mpr
    dsimp [pairSum]
    omega
  have hS : S.card = 2*N+1 := by simp [S]
  have hCS := sum_mul_sq_le_sq_mul_sq S (fun s => (fiber A s).card) (fun _ => (1 : ℕ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one, ← hcard, hS] at hCS
  have hpair : (orderedPairs A).card^2 ≤ 2*(2*N^2+1)*(2*N+1) :=
    hCS.trans (Nat.mul_le_mul_right _ hsumsq)
  have hP := Nat.pow_le_pow_left (orderedPairs_card A) 2
  have hexact : A.card^4 ≤ 8*(2*N^2+1)*(2*N+1) := by
    nlinarith only [hP,hpair]
  nlinarith only [hexact, Nat.zero_le N, Nat.zero_le (N^2), Nat.zero_le (N^3)]

/-- Sidon behavior for every affine shift in this polynomial-size family
forces a fixed exponent loss. It does not follow from Sidon behavior for
q=1,r=0 alone. -/
theorem universal_affine_bound (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hSidon : ∀ q : ℕ, 0 < q → q ≤ 4*N → ∀ r : ℕ, r ≤ 2*N^2 →
      IsSidon ((A.image (fun n => (q*n+r)^2) : Finset ℕ) : Set ℕ)) :
    A.card^4 ≤ 48*(N+1)^3 := by
  apply monotone_pairs_bound N A hA
  intro a ha b hb c hc d hd hsum
  by_contra! hsquare
  let L := c+d-(a+b)
  let q := 2*L
  let r := a^2+b^2-(c^2+d^2)
  have hL : 0 < L := Nat.sub_pos_of_lt hsum
  have hq : 0 < q := by dsimp [q]; omega
  have hS : c+d = a+b+L := by dsimp [L]; omega
  have hT : a^2+b^2 = c^2+d^2+r := by dsimp [r]; omega
  have haN := (mem_Icc.mp (hA ha)).2
  have hbN := (mem_Icc.mp (hA hb)).2
  have hcN := (mem_Icc.mp (hA hc)).2
  have hdN := (mem_Icc.mp (hA hd)).2
  have hqN : q ≤ 4*N := by dsimp [q]; omega
  have hrN : r ≤ 2*N^2 := by
    have hh1 := Nat.pow_le_pow_left haN 2
    have hh2 := Nat.pow_le_pow_left hbN 2
    omega
  have he : (q*a+r)^2+(q*b+r)^2 = (q*c+r)^2+(q*d+r)^2 := by
    calc
      _ = q^2*(a^2+b^2)+2*q*r*(a+b)+2*r^2 := by ring
      _ = q^2*(c^2+d^2)+2*q*r*(c+d)+2*r^2 := by
        dsimp [q]
        nlinarith only [congrArg (4*L^2*·) hT,congrArg (4*L*r*·) hS]
      _ = _ := by ring
  have hf : Function.Injective (fun n : ℕ => (q*n+r)^2) := by
    intro x y hxy
    have hxy := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hxy
    exact mul_left_cancel₀ hq.ne' (Nat.add_right_cancel hxy)
  have hmem {n : ℕ} (hn : n ∈ A) : (q*n+r)^2 ∈
      ((A.image (fun n => (q*n+r)^2) : Finset ℕ) : Set ℕ) := mem_image.mpr ⟨n,hn,rfl⟩
  have hh := hSidon q hq hqN r hrN _ (hmem ha) _ (hmem hc) _ (hmem hb) _ (hmem hd) he
  rcases hh with ⟨hac,hbd⟩ | ⟨had,hbc⟩
  · have := hf hac
    have := hf hbd
    omega
  · have := hf had
    have := hf hbc
    omega

/-- The universal affine-shift condition cannot hold on sets of exponent
strictly greater than 3/4. The original conjecture only asks for one map. -/
theorem eventually_card_lt (α : ℝ) (hα : 3/4 < α) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A ⊆ Icc 1 N,
      (∀ q : ℕ, 0 < q → q ≤ 4*N → ∀ r : ℕ, r ≤ 2*N^2 →
        IsSidon ((A.image (fun n => (q*n+r)^2) : Finset ℕ) : Set ℕ)) →
      (A.card : ℝ) < (N : ℝ)^α := by
  have hexp : 0 < 4*α-3 := by linarith
  have ht : Filter.Tendsto (fun N : ℕ => (N : ℝ)^(4*α-3)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.tendsto_atTop.mp ht 385]
    with N hN hbig
  intro A hA hSidon
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (A.card : ℝ)^4 ≤ 48*((N : ℝ)+1)^3 := by
    exact_mod_cast universal_affine_bound N A hA hSidon
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcube : ((N : ℝ)+1)^3 ≤ (2*(N : ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hupper : (A.card : ℝ)^4 ≤ 384*(N : ℝ)^3 := by nlinarith only [hc,hcube]
  have hlarge : 384*(N : ℝ)^3 < ((N : ℝ)^α)^4 := by
    calc
      _ < (N : ℝ)^(4*α-3)*(N : ℝ)^3 :=
        mul_lt_mul_of_pos_right (by linarith) (pow_pos hNpos _)
      _ = _ := by
        rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hNpos,
          ← Real.rpow_mul_natCast hNpos.le]
        congr 1
        norm_num
        ring
  by_contra! hnot
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hnot 4
  linarith

/-- Explicit negation of the stronger, all-shifts version of the conjecture.
This is deliberately NOT named erdos_773.disproof: it is not a negation of
the original statement. -/
theorem not_near_linear_universal_affine :
    ¬ (∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, ∃ A ⊆ Icc 1 N,
      (N : ℝ)^(1-ε) ≤ A.card ∧
      ∀ q ∈ Icc 1 (N^3), ∀ r ∈ Icc 0 (N^3),
        IsSidon ((A.image (fun n => (q*n+r)^2) : Finset ℕ) : Set ℕ)) := by
  intro h
  have hlower := h (1/8) (by norm_num)
  have hupper := eventually_card_lt (7/8) (by norm_num)
  have he : ∀ᶠ N : ℕ in Filter.atTop, False := by
    filter_upwards [hlower,hupper,Filter.eventually_ge_atTop 2] with N hl hu hN
    obtain ⟨A,hA,hcard,hS⟩ := hl
    have hN2 : 4*N ≤ N^3 := by
      have hh := Nat.pow_le_pow_left hN 2
      have hh' := Nat.mul_le_mul_left N hh
      nlinarith only [hh']
    have hN3 : 2*N^2 ≤ N^3 := by
      have hh := Nat.mul_le_mul_right (N^2) hN
      nlinarith only [hh]
    have hu := hu A hA (by
      intro q hq hqN r hrN
      exact hS q (mem_Icc.mpr ⟨hq,hqN.trans hN2⟩)
        r (mem_Icc.mpr ⟨Nat.zero_le _,hrN.trans hN3⟩))
    norm_num at hcard
    linarith
  exact Filter.Eventually.exists he |>.elim (fun _ h => h)

/-- Even a small ordinary square-Sidon set need not remain Sidon after
an affine shift. The shifted collision is 3²+11²=7²+9². -/
theorem single_shift_not_universal :
    IsSidon ((({1,3,4,5} : Finset ℕ).image (fun n => n^2) : Finset ℕ) : Set ℕ) ∧
    ¬ IsSidon ((({1,3,4,5} : Finset ℕ).image (fun n => (2*n+1)^2) : Finset ℕ) : Set ℕ) := by
  decide +kernel

#print axioms monotone_pairs_bound
#print axioms universal_affine_bound
#print axioms eventually_card_lt
#print axioms not_near_linear_universal_affine
#print axioms single_shift_not_universal
end Erdos773.UniversalAffineSidonBound
