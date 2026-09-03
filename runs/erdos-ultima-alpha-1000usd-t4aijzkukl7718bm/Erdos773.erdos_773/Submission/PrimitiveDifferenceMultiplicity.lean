import Submission.CollisionBounds

/-!
Coprime root pairs can still represent one positive square difference in
arbitrarily many ways. This auxiliary fact is not a disproof of Erdős 773.
-/
namespace Erdos773.PrimitiveDifferenceMultiplicity
open Finset
set_option maxHeartbeats 1000000

private def GoodFactors (D : ℕ) (uv : ℕ × ℕ) : Prop :=
  0 < uv.1 ∧ uv.1 < uv.2 ∧ Odd uv.1 ∧ Odd uv.2 ∧
    uv.1.Coprime uv.2 ∧ uv.1 * uv.2 = D

private lemma factor_bounds {D : ℕ} {uv : ℕ × ℕ} (h : GoodFactors D uv) :
    0 < D ∧ uv.1 ≤ D ∧ uv.2 ≤ D := by
  obtain ⟨hu, huv, ho, ho', hc, he⟩ := h
  have hv : 0 < uv.2 := by omega
  constructor
  · rw [← he]; positivity
  constructor
  · nlinarith
  · nlinarith

private lemma small_large {D : ℕ} {uv wz : ℕ × ℕ}
    (h : GoodFactors D uv) (h' : GoodFactors D wz) : uv.1 < wz.2 := by
  obtain ⟨hu, huv, _, _, _, he⟩ := h
  obtain ⟨hw, hwz, _, _, _, he'⟩ := h'
  nlinarith

private lemma next_factors {D : ℕ} {uv : ℕ × ℕ} (h : GoodFactors D uv) :
    GoodFactors (D * (2 * D + 1)) (uv.1, (2 * D + 1) * uv.2) ∧
    GoodFactors (D * (2 * D + 1)) (uv.2, (2 * D + 1) * uv.1) := by
  have hb := factor_bounds h
  obtain ⟨hu, huv, hou, hov, hc, he⟩ := h
  have hp : Odd (2 * D + 1) := ⟨D, by omega⟩
  have hcp : D.Coprime (2 * D + 1) := by simp [Nat.coprime_mul_right_add_right]
  have hucp : uv.1.Coprime (2 * D + 1) := hcp.of_dvd_left ⟨uv.2, he.symm⟩
  have hvcp : uv.2.Coprime (2 * D + 1) :=
    hcp.of_dvd_left ⟨uv.1, by nlinarith only [he]⟩
  constructor
  · refine ⟨hu, by nlinarith, hou, hp.mul hov, hucp.mul_right hc, ?_⟩
    dsimp only
    nlinarith only [he]
  · refine ⟨by omega, by nlinarith, hov, hp.mul hou, hvcp.mul_right hc.symm, ?_⟩
    dsimp only
    nlinarith only [he]

private lemma double_factor_family {D : ℕ} {A : Finset (ℕ × ℕ)}
    (hA : ∀ uv ∈ A, GoodFactors D uv) :
    ∃ B : Finset (ℕ × ℕ), B.card = 2 * A.card ∧
      ∀ uv ∈ B, GoodFactors (D * (2 * D + 1)) uv := by
  let f : ℕ × ℕ → ℕ × ℕ := fun uv => (uv.1, (2 * D + 1) * uv.2)
  let g : ℕ × ℕ → ℕ × ℕ := fun uv => (uv.2, (2 * D + 1) * uv.1)
  have hp : 0 < 2 * D + 1 := by omega
  have hf : Function.Injective f := by
    intro uv wz he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have he2' : uv.2 = wz.2 := Nat.eq_of_mul_eq_mul_left hp he2
    exact Prod.ext he1 he2'
  have hg : Function.Injective g := by
    intro uv wz he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have he2' : uv.1 = wz.1 := Nat.eq_of_mul_eq_mul_left hp he2
    exact Prod.ext he2' he1
  have hdis : Disjoint (A.image f) (A.image g) := by
    apply disjoint_left.mpr
    intro t ht ht'
    obtain ⟨uv, huv, rfl⟩ := mem_image.mp ht
    obtain ⟨wz, hwz, he⟩ := mem_image.mp ht'
    have he1 := congrArg Prod.fst he
    have hh := small_large (hA uv huv) (hA wz hwz)
    dsimp [f, g] at he1
    omega
  refine ⟨A.image f ∪ A.image g, ?_, ?_⟩
  · rw [card_union_of_disjoint hdis, card_image_of_injective _ hf,
      card_image_of_injective _ hg]
    omega
  · intro uv huv
    rcases mem_union.mp huv with huv | huv
    · obtain ⟨wz, hwz, rfl⟩ := mem_image.mp huv
      exact (next_factors (hA wz hwz)).1
    · obtain ⟨wz, hwz, rfl⟩ := mem_image.mp huv
      exact (next_factors (hA wz hwz)).2

private lemma factor_families (k : ℕ) :
    ∃ D : ℕ, ∃ A : Finset (ℕ × ℕ), 0 < D ∧ A.card = 2 ^ k ∧
      ∀ uv ∈ A, GoodFactors D uv := by
  induction k with
  | zero =>
    refine ⟨3, {(1, 3)}, by omega, by simp, ?_⟩
    intro uv huv
    have h : uv = (1, 3) := mem_singleton.mp huv
    subst uv
    norm_num [GoodFactors]
  | succ k ih =>
    obtain ⟨D, A, hD, hcard, hA⟩ := ih
    obtain ⟨B, hB, hgood⟩ := double_factor_family hA
    refine ⟨D * (2 * D + 1), B, by positivity, ?_, hgood⟩
    rw [hB, hcard, pow_succ']

private def roots (uv : ℕ × ℕ) : ℕ × ℕ :=
  ((uv.2 - uv.1) / 2, (uv.2 + uv.1) / 2)

private lemma roots_sum_diff {D : ℕ} {uv : ℕ × ℕ} (h : GoodFactors D uv) :
    0 < (roots uv).1 ∧ (roots uv).1 < (roots uv).2 ∧
      (roots uv).2 - (roots uv).1 = uv.1 ∧
      (roots uv).2 + (roots uv).1 = uv.2 := by
  obtain ⟨hu, huv, ⟨u, hu'⟩, ⟨v, hv'⟩, hc, he⟩ := h
  dsimp [roots]
  omega

private lemma roots_coprime {D : ℕ} {uv : ℕ × ℕ} (h : GoodFactors D uv) :
    (roots uv).1.Coprime (roots uv).2 := by
  obtain ⟨ha, hab, hdiff, hsum⟩ := roots_sum_diff h
  have hgu : Nat.gcd (roots uv).1 (roots uv).2 ∣ uv.1 := by
    rw [← hdiff]
    exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have hgv : Nat.gcd (roots uv).1 (roots uv).2 ∣ uv.2 := by
    rw [← hsum]
    exact dvd_add (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have hd := Nat.dvd_gcd hgu hgv
  rw [h.2.2.2.2.1.gcd_eq_one] at hd
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.eq_one_of_dvd_one hd)

private lemma roots_mem {D : ℕ} {uv : ℕ × ℕ} (h : GoodFactors D uv) :
    roots uv ∈ (squareDifferenceReps D D).filter (fun ab => ab.1.Coprime ab.2) := by
  obtain ⟨ha, hab, hdiff, hsum⟩ := roots_sum_diff h
  have hb := factor_bounds h
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨?_, hab, ?_⟩, roots_coprime h⟩
  · exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, by omega⟩,
      mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · have he := h.2.2.2.2.2
    have hdiff' := Nat.sub_add_cancel hab.le
    nlinarith only [he, hsum, hdiff, hdiff']

/-- Coprimality within each pair does not give a constant bound on the
    number of representations of a positive square difference. -/
theorem arbitrarily_many_primitive_representations (k : ℕ) :
    ∃ D : ℕ, 0 < D ∧ 2 ^ k ≤
      ((squareDifferenceReps D D).filter (fun ab => ab.1.Coprime ab.2)).card := by
  obtain ⟨D, A, hD, hcard, hA⟩ := factor_families k
  refine ⟨D, hD, ?_⟩
  rw [← hcard]
  apply card_le_card_of_injOn roots
  · intro uv huv
    exact roots_mem (hA uv huv)
  · intro uv huv wz hwz he
    obtain ⟨_, _, hd, hs⟩ := roots_sum_diff (hA uv huv)
    obtain ⟨_, _, hd', hs'⟩ := roots_sum_diff (hA wz hwz)
    rw [he] at hd hs
    exact Prod.ext (hd.symm.trans hd') (hs.symm.trans hs')

/-- A finite family of primitive linear forms with complementary coefficient
    supports can be made pairwise coprime by one even specialization. -/
private lemma coprime_linear_specialization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℕ) (hF : Odd F) (a : ι → ℕ) (b : ι → ℤ)
    (hc : ∀ i, (a i).Coprime (b i).natAbs)
    (hf : ∀ i, a i * (b i).natAbs = F)
    (hdet : ∀ i j, i ≠ j → (a i : ℤ) * b j - (a j : ℤ) * b i ≠ 0) :
    ∃ x : ℕ, 2 ≤ x ∧ Even x ∧ x.Coprime F ∧
      ∀ i j, i ≠ j →
        ((a i : ℤ) * x + b i).natAbs.Coprime ((a j : ℤ) * x + b j).natAbs := by
  let det (i j : ι) : ℤ := (a i : ℤ) * b j - (a j : ℤ) * b i
  let T : Finset ℕ :=
    (univ.biUnion (fun i : ι => univ.biUnion (fun j : ι => (det i j).natAbs.primeFactors))).filter (fun p => ¬p ∣ F)
  have hTp {p : ℕ} (hp : p ∈ T) : p.Prime := by
    obtain ⟨hp, _⟩ := mem_filter.mp hp
    obtain ⟨i, _, hp⟩ := mem_biUnion.mp hp
    obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
    exact (Nat.mem_primeFactors.mp hp).1
  let q := ∏ p ∈ T, p
  have hq : 0 < q := prod_pos (fun p hp => (hTp hp).pos)
  have hqF : q.Coprime F := by
    apply Nat.Coprime.prod_left
    intro p hp
    exact (hTp hp).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2
  let x := 2 * q
  have hxF : x.Coprime F := (Nat.coprime_two_left.mpr hF).mul_left hqF
  refine ⟨x, by dsimp [x]; omega, ⟨q, by dsimp [x]; omega⟩, hxF, ?_⟩
  intro i j hij
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hiZ : (p : ℤ) ∣ (a i : ℤ) * x + b i := Int.natCast_dvd.mpr hpi
  have hjZ : (p : ℤ) ∣ (a j : ℤ) * x + b j := Int.natCast_dvd.mpr hpj
  have hdetZ : (p : ℤ) ∣ det i j := by
    have h := dvd_sub (dvd_mul_of_dvd_right hjZ (a i : ℤ))
      (dvd_mul_of_dvd_right hiZ (a j : ℤ))
    convert h using 1; dsimp [det]; ring
  by_cases hpF : p ∣ F
  · have hnx : ¬p ∣ x := by
      intro hpx
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hxF hpx hpF)
    have hpf : p ∣ a i * (b i).natAbs := by rw [hf]; exact hpF
    rcases hp.dvd_mul.mp hpf with hpa | hpb
    · have hpaZ : (p : ℤ) ∣ (a i : ℤ) * x :=
        dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpa) _
      have hpbZ : (p : ℤ) ∣ b i := by
        convert dvd_sub hiZ hpaZ using 1; ring
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (hc i) hpa (Int.natCast_dvd.mp hpbZ))
    · have hpbZ := Int.natCast_dvd.mpr hpb
      have hpaZ : (p : ℤ) ∣ (a i : ℤ) * x := by
        convert dvd_sub hiZ hpbZ using 1; ring
      have hpa : p ∣ a i * x := by exact_mod_cast hpaZ
      rcases hp.dvd_mul.mp hpa with hpa | hpx
      · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (hc i) hpa hpb)
      · exact hnx hpx
  · have hpT : p ∈ T := by
      refine mem_filter.mpr ⟨?_, hpF⟩
      apply mem_biUnion.mpr
      refine ⟨i, mem_univ _, mem_biUnion.mpr ⟨j, mem_univ _, ?_⟩⟩
      exact Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hdetZ,
        Int.natAbs_ne_zero.mpr (hdet i j hij)⟩
    have hpq : p ∣ q := dvd_prod_of_mem (fun p : ℕ => p) hpT
    have hpx : p ∣ x := dvd_mul_of_dvd_right hpq 2
    have hpxZ : (p : ℤ) ∣ (a i : ℤ) * x :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hpx) _
    have hpbZ : (p : ℤ) ∣ b i := by
      convert dvd_sub hiZ hpxZ using 1; ring
    have hpb := Int.natCast_dvd.mp hpbZ
    exact hpF (by rw [← hf i]; exact dvd_mul_of_dvd_right hpb _)

private lemma factor_ratio_unique {D : ℕ} {uv wz : ℕ × ℕ}
    (h : GoodFactors D uv) (h' : GoodFactors D wz)
    (he : uv.2 * wz.1 = wz.2 * uv.1) : uv = wz := by
  have hp : uv.1 * uv.2 = wz.1 * wz.2 := h.2.2.2.2.2.trans h'.2.2.2.2.2.symm
  have hs : wz.2 * uv.1 ^ 2 = wz.2 * wz.1 ^ 2 := by
    calc
      _ = uv.1 * (wz.2 * uv.1) := by ring
      _ = uv.1 * (uv.2 * wz.1) := by rw [he]
      _ = (uv.1 * uv.2) * wz.1 := by ring
      _ = (wz.1 * wz.2) * wz.1 := by rw [hp]
      _ = _ := by ring
  have hw : 0 < wz.2 := by have := h'.1; have := h'.2.1; omega
  have hs' := Nat.eq_of_mul_eq_mul_left hw hs
  have hu : uv.1 = wz.1 := by nlinarith
  have hv : uv.2 = wz.2 := by rw [← hu] at hp; exact Nat.eq_of_mul_eq_mul_left h.1 hp
  exact Prod.ext hu hv

/-- Arbitrarily many representations of one positive square difference can
    coexist even when ALL the participating roots are pairwise coprime.
    No near-linear size relative to their largest root is asserted. -/
theorem pairwise_coprime_equal_difference_families (k : ℕ) :
    ∃ D : ℕ, ∃ S : Finset ℕ, ∃ P : Finset (ℕ × ℕ),
      0 < D ∧ S.card = 2 ^ (k + 1) ∧ P.card = 2 ^ k ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧
      ∀ ab ∈ P, ab.1 ∈ S ∧ ab.2 ∈ S ∧ 0 < ab.1 ∧ ab.1 < ab.2 ∧
        ab.2 ^ 2 = ab.1 ^ 2 + D := by
  classical
  obtain ⟨F, A, hFpos, hcard, hA⟩ := factor_families k
  have hne : A.Nonempty := card_pos.mp (by rw [hcard]; positivity)
  obtain ⟨uv, huv⟩ := hne
  have hFodd : Odd F := by
    rw [← (hA uv huv).2.2.2.2.2]
    exact (hA uv huv).2.2.1.mul (hA uv huv).2.2.2.1
  let I := ↥A × Bool
  let a : I → ℕ := fun i => i.1.val.2
  let b : I → ℤ := fun i => if i.2 then (i.1.val.1 : ℤ) else -(i.1.val.1 : ℤ)
  have hbabs (i : I) : (b i).natAbs = i.1.val.1 := by dsimp [b]; split <;> simp
  have hcoeff (i : I) : (a i).Coprime (b i).natAbs := by
    rw [hbabs]
    exact (hA i.1.val i.1.property).2.2.2.2.1.symm
  have hprod (i : I) : a i * (b i).natAbs = F := by
    rw [hbabs]
    dsimp [a]
    nlinarith only [(hA i.1.val i.1.property).2.2.2.2.2]
  have hdet (i j : I) (hij : i ≠ j) :
      (a i : ℤ) * b j - (a j : ℤ) * b i ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    have heabs := congrArg Int.natAbs he
    simp only [Int.natAbs_mul, Int.natAbs_natCast, hbabs] at heabs
    have hf := factor_ratio_unique (hA i.1.val i.1.property)
      (hA j.1.val j.1.property) heabs
    have hf' : i.1 = j.1 := Subtype.ext hf
    have ha0 : (a i : ℤ) ≠ 0 := by
      have hh := hA i.1.val i.1.property
      have hh' : 0 < a i := lt_trans hh.1 hh.2.1
      exact_mod_cast hh'.ne'
    have hab : a i = a j := by dsimp [a]; rw [hf']
    rw [← hab] at he
    have hb : b j = b i := mul_left_cancel₀ ha0 he
    have hs : i.2 = j.2 := by
      have hu0 := (hA i.1.val i.1.property).1
      dsimp [b] at hb
      rw [← hf'] at hb
      cases hi : i.2 <;> cases hj : j.2 <;> simp_all
    exact hij (Prod.ext hf' hs)
  obtain ⟨x, hx, hxeven, hxF, hcop⟩ :=
    coprime_linear_specialization F hFodd a b hcoeff hprod hdet
  let value (i : I) : ℕ := ((a i : ℤ) * x + b i).natAbs
  have hpos (i : I) : (2 : ℤ) ≤ (a i : ℤ) * x + b i := by
    have hi := hA i.1.val i.1.property
    have hu : (1 : ℤ) ≤ i.1.val.1 := by exact_mod_cast hi.1
    have hv : (i.1.val.1 : ℤ) + 1 ≤ i.1.val.2 := by exact_mod_cast hi.2.1
    have hx' : (2 : ℤ) ≤ x := by exact_mod_cast hx
    dsimp [a, b]
    split <;> nlinarith
  have hcast (i : I) : (value i : ℤ) = (a i : ℤ) * x + b i := by
    dsimp [value]
    rw [Int.natCast_natAbs, abs_of_nonneg (by have := hpos i; omega)]
  have htwo (i : I) : 2 ≤ value i := by
    have hh := hpos i
    rw [← hcast] at hh
    exact_mod_cast hh
  have hinj : Function.Injective value := by
    intro i j he
    by_contra hij
    have hh := hcop i j hij
    change (value i).Coprime (value j) at hh
    rw [he, Nat.coprime_self] at hh
    have := htwo j
    omega
  let S := univ.image value
  let pair (uv : ↥A) : ℕ × ℕ := (value (uv, false), value (uv, true))
  let P := univ.image pair
  have hpairinj : Function.Injective pair := by
    intro uv wz he
    have he' := hinj (congrArg Prod.fst he)
    exact congrArg Prod.fst he'
  refine ⟨4 * F * x, S, P, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj]
    simp [I, hcard, pow_succ]
  · rw [card_image_of_injective _ hpairinj]
    simp [hcard]
  · intro m hm n hn hmn
    obtain ⟨i, _, rfl⟩ := mem_image.mp hm
    obtain ⟨j, _, rfl⟩ := mem_image.mp hn
    exact hcop i j (fun he => hmn (congrArg value he))
  · intro ab hab
    obtain ⟨uv, _, rfl⟩ := mem_image.mp hab
    refine ⟨mem_image.mpr ⟨(uv, false), mem_univ _, rfl⟩,
      mem_image.mpr ⟨(uv, true), mem_univ _, rfl⟩,
      by have := htwo (uv, false); dsimp [pair]; omega, ?_, ?_⟩
    · have hh := (hA uv.val uv.property).1
      have hl := hcast (uv, false)
      have hr := hcast (uv, true)
      dsimp [a, b] at hl hr
      dsimp [pair]
      omega
    · apply (Nat.cast_inj (R := ℤ)).mp
      push_cast
      dsimp [pair]
      rw [hcast, hcast]
      dsimp [a, b]
      have hfZ : (uv.val.1 : ℤ) * uv.val.2 = F := by
        exact_mod_cast (hA uv.val uv.property).2.2.2.2.2
      nlinarith only [congrArg (fun z : ℤ => 4 * z * x) hfZ]

#print axioms arbitrarily_many_primitive_representations
#print axioms pairwise_coprime_equal_difference_families
end Erdos773.PrimitiveDifferenceMultiplicity
