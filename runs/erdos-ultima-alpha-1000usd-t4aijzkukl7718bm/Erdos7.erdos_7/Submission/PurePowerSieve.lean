import FormalConjecturesUtil

/-! Product-set counting tools for a pure-prime-power sieve. -/

namespace Erdos7Reduction
open Finset

/-- The sum of the relative volumes of boxes covering a finite product is at least one. -/
theorem finite_product_cover_density {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)]
    (U : ∀ i, Finset (A i)) (hU : ∀ i, (U i).Nonempty)
    (K : Finset κ) (B : κ → ∀ i, Finset (A i))
    (hcover : ∀ x ∈ Fintype.piFinset U, ∃ k ∈ K, ∀ i, x i ∈ B k i) :
    (1 : ℚ) ≤ ∑ k ∈ K, ∏ i, (((U i ∩ B k i).card : ℚ) / (U i).card) := by
  classical
  let C (k : κ) := Fintype.piFinset (fun i => U i ∩ B k i)
  have hsub : Fintype.piFinset U ⊆ K.biUnion C := by
    intro x hx
    obtain ⟨k, hk, hxi⟩ := hcover x hx
    refine Finset.mem_biUnion.mpr ⟨k, hk, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    exact Finset.mem_inter.mpr ⟨Fintype.mem_piFinset.mp hx i, hxi i⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  simp only [C, Fintype.card_piFinset] at hcard
  have hpos : (0 : ℚ) < ∏ i, ((U i).card : ℚ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast (hU i).card_pos
  simp_rw [Finset.prod_div_distrib]
  rw [← Finset.sum_div, le_div_iff₀ hpos, one_mul]
  exact_mod_cast hcard

/-- A finite union of small sets leaves a quantitatively large complement. -/
theorem relative_complement_bound {A κ : Type*} [Fintype A] [DecidableEq A]
    (K : Finset κ) (B : κ → Finset A) (w : κ → ℚ) (r : ℚ)
    (hB : ∀ k ∈ K, (B k).card ≤ (Fintype.card A : ℚ) * w k)
    (hw : ∑ k ∈ K, w k ≤ r) :
    (Fintype.card A : ℚ) * (1 - r) ≤
      ((Finset.univ \ K.biUnion B).card : ℚ) := by
  have hcard : ((K.biUnion B).card : ℚ) ≤ ∑ k ∈ K, (B k).card := by
    exact_mod_cast (Finset.card_biUnion_le (s := K) (t := B))
  push_cast at hcard
  have hsum : (∑ k ∈ K, (B k).card : ℚ) ≤ (Fintype.card A : ℚ) * r := by
    calc
      _ ≤ ∑ k ∈ K, (Fintype.card A : ℚ) * w k :=
        Finset.sum_le_sum (fun k hk => hB k hk)
      _ = (Fintype.card A : ℚ) * ∑ k ∈ K, w k := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  have heq : (Finset.univ \ K.biUnion B).card + (K.biUnion B).card = Fintype.card A := by
    simpa only [Finset.univ_inter, Finset.card_univ] using
      Finset.card_sdiff_add_card_inter Finset.univ (K.biUnion B)
  have heq' : ((Finset.univ \ K.biUnion B).card : ℚ) + (K.biUnion B).card =
      Fintype.card A := by exact_mod_cast heq
  nlinarith

/-- A geometric bound for distinct positive exponents. -/
theorem positive_geometric_sum_le (p : ℕ) (hp : 1 < p) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 0 < a) :
    (∑ a ∈ s, ((p : ℚ)⁻¹)^a) ≤ 1 / (p - 1 : ℚ) := by
  let N := s.sup id + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hsub : s ⊆ (Finset.range N).erase 0 := by
    intro a ha
    refine Finset.mem_erase.mpr ⟨by have := hs a ha; omega, ?_⟩
    have hle : a ≤ s.sup id := Finset.le_sup (f := id) ha
    exact Finset.mem_range.mpr (by dsimp [N]; omega)
  have hle : (∑ a ∈ s, ((p : ℚ)⁻¹)^a) ≤
      ∑ a ∈ (Finset.range N).erase 0, ((p : ℚ)⁻¹)^a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have he := Finset.sum_erase_add (Finset.range N) (fun a => ((p : ℚ)⁻¹)^a)
    (Finset.mem_range.mpr hN)
  have hg := geom_sum_mul ((p : ℚ)⁻¹) N
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp
  have hn0 : (0 : ℚ) ≤ ((p : ℚ)⁻¹)^N := by positivity
  have hrecip : (p : ℚ)⁻¹ * p = 1 := inv_mul_cancel₀ (ne_of_gt hp0)
  have hbound : (∑ a ∈ (Finset.range N).erase 0, ((p : ℚ)⁻¹)^a) * (p - 1) ≤ 1 := by
    simp only [pow_zero] at he
    have hg' := congrArg (fun x : ℚ => x * p) hg
    dsimp only at hg'
    rw [mul_assoc, sub_mul, hrecip, one_mul] at hg'
    nlinarith [mul_nonneg hn0 hp0.le]
  rw [le_div_iff₀ (by linarith : (0 : ℚ) < p - 1)]
  exact (mul_le_mul_of_nonneg_right hle (by linarith)).trans hbound

#print axioms finite_product_cover_density
#print axioms relative_complement_bound
#print axioms positive_geometric_sum_le
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- Sum tensor-product weights over distinct vectors supported on at least two
coordinates, using an upper bound for the sum of positive-level weights. -/
theorem mixed_vector_weight_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset κ) (e : κ → ι → ℕ) (he : Set.InjOn e K)
    (E : ι → Finset ℕ) (hE : ∀ k ∈ K, ∀ i, e k i ∈ E i)
    (hmixed : ∀ k ∈ K, 2 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card)
    (w : ι → ℕ → ℚ) (hw : ∀ i n, 0 ≤ w i n) (hw0 : ∀ i, w i 0 = 1)
    (z : ι → ℚ) (hz : ∀ i, ∑ n ∈ (E i).erase 0, w i n ≤ z i) :
    (∑ k ∈ K, ∏ i, w i (e k i)) ≤
      ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card, ∏ i ∈ S, z i := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  let T := (Finset.univ : Finset ι).powerset.filter (fun S => 2 ≤ S.card)
  have hmemT (k : κ) (hk : k ∈ K) : supp k ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hmixed k hk⟩
  have hfiber : (∑ S ∈ T, ∑ k ∈ K with supp k = S, ∏ i, w i (e k i)) =
      ∑ k ∈ K, ∏ i, w i (e k i) := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hmemT
  rw [← hfiber]
  apply Finset.sum_le_sum
  intro S hS
  let L := K.filter (fun k => supp k = S)
  let Q (i : ι) := if i ∈ S then (E i).erase 0 else {0}
  have himg : L.image e ⊆ Fintype.piFinset Q := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hkK, hkS⟩ := Finset.mem_filter.mp hk
    apply Fintype.mem_piFinset.mpr
    intro i
    have hsi : i ∈ S ↔ e k i ≠ 0 := by rw [← hkS]; simp [supp]
    dsimp [Q]
    split_ifs with hi
    · exact Finset.mem_erase.mpr ⟨hsi.mp hi, hE k hkK i⟩
    · have h0 : e k i = 0 := by simpa only [not_not] using mt hsi.mpr hi
      simp [h0]
  have hsum_image : (∑ x ∈ L.image e, ∏ i, w i (x i)) =
      ∑ k ∈ L, ∏ i, w i (e k i) :=
    Finset.sum_image (fun k hk l hl hkl => he (Finset.mem_filter.mp hk).1
      (Finset.mem_filter.mp hl).1 hkl)
  have hle : (∑ k ∈ L, ∏ i, w i (e k i)) ≤
      ∑ x ∈ Fintype.piFinset Q, ∏ i, w i (x i) := by
    rw [← hsum_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg
      (by intro x _ _; exact Finset.prod_nonneg (fun i _ => hw i (x i)))
  rw [← Finset.prod_univ_sum] at hle
  have hcoord (i : ι) : (∑ n ∈ Q i, w i n) ≤ if i ∈ S then z i else 1 := by
    dsimp [Q]
    split_ifs
    · exact hz i
    · simp [hw0]
  have hprod : (∏ i, ∑ n ∈ Q i, w i n) ≤ ∏ i, if i ∈ S then z i else 1 :=
    Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun n _ => hw i n))
      (fun i _ => hcoord i)
  have heq : (∏ i, if i ∈ S then z i else 1) = ∏ i ∈ S, z i := by
    rw [← Finset.prod_filter]
    simp
  rw [heq] at hprod
  exact hle.trans hprod

#print axioms mixed_vector_weight_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem conditioned_geometric_sum_le (p : ℕ) (hp : 2 < p) (E : Finset ℕ) :
    (∑ n ∈ E.erase 0, if n = 0 then (1 : ℚ) else
      ((p : ℚ) - 1) / (p - 2) * ((p : ℚ)⁻¹)^n) ≤ 1 / (p - 2 : ℚ) := by
  have hp' : (2 : ℚ) < p := by exact_mod_cast hp
  have hp1 : (0 : ℚ) < p - 1 := by linarith
  have hp2 : (0 : ℚ) < p - 2 := by linarith
  have heq : (∑ n ∈ E.erase 0, if n = 0 then (1 : ℚ) else
      ((p : ℚ) - 1) / (p - 2) * ((p : ℚ)⁻¹)^n) =
      ((p : ℚ) - 1) / (p - 2) * ∑ n ∈ E.erase 0, ((p : ℚ)⁻¹)^n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_neg (Finset.mem_erase.mp hn).1]
  rw [heq]
  have hgeom := positive_geometric_sum_le p (by omega) (E.erase 0)
    (fun n hn => by have := (Finset.mem_erase.mp hn).1; omega)
  calc
    _ ≤ (((p : ℚ) - 1) / (p - 2)) * (1 / (p - 1)) :=
      mul_le_mul_of_nonneg_left hgeom (div_nonneg hp1.le hp2.le)
    _ = _ := by field_simp

private theorem conditioned_ratio_bound (N u b : ℕ) (p : ℕ) (hp : 2 < p)
    (hN : 0 < N) (hu : (N : ℚ) * (1 - 1 / (p - 1 : ℚ)) ≤ u)
    (r : ℚ) (hr : 0 ≤ r) (hb : (b : ℚ) ≤ N * r) :
    0 < u ∧ (b : ℚ) / u ≤ ((p : ℚ) - 1) / (p - 2) * r := by
  have hp' : (2 : ℚ) < p := by exact_mod_cast hp
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hp1 : (0 : ℚ) < p - 1 := by linarith
  have hp2 : (0 : ℚ) < p - 2 := by linarith
  have heq : (1 - 1 / (p - 1 : ℚ)) = (p - 2 : ℚ) / (p - 1) := by field_simp; ring
  rw [heq] at hu
  have hu' : (0 : ℚ) < u := lt_of_lt_of_le (mul_pos hN' (div_pos hp2 hp1)) hu
  refine ⟨by exact_mod_cast hu', ?_⟩
  rw [div_le_iff₀ hu']
  have hcancel : (N : ℚ) ≤ u * ((p - 1 : ℚ) / (p - 2)) := by
    have h := mul_le_mul_of_nonneg_right hu (div_nonneg hp1.le hp2.le)
    have hc : (p - 2 : ℚ) / (p - 1) * ((p - 1) / (p - 2)) = 1 := by field_simp
    rw [mul_assoc, hc, mul_one] at h
    exact h
  have h := hb.trans (mul_le_mul_of_nonneg_right hcancel hr)
  nlinarith

#print axioms conditioned_ratio_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- A finite product-space sieve for uniquely labelled prime-power boxes.
Removing all one-coordinate boxes gives a bound involving only mixed supports. -/
theorem pure_power_box_sieve {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (p : ι → ℕ) (hp : ∀ i, 2 < p i)
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (B : κ → ∀ i, Finset (A i))
    (hB0 : ∀ k i, e k i = 0 → B k i = Finset.univ)
    (hBcard : ∀ k i, ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i) :
    (1 : ℚ) ≤ ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / (p i - 2 : ℚ)) := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  have hmem (k : κ) (i : ι) : i ∈ supp k ↔ e k i ≠ 0 := by simp [supp]
  let Pure (i : ι) := Finset.univ.filter (fun k => supp k = {i})
  have hpure (i : ι) (k : κ) (hk : k ∈ Pure i) : supp k = {i} :=
    (Finset.mem_filter.mp hk).2
  have hppos (i : ι) (k : κ) (hk : k ∈ Pure i) : 0 < e k i := by
    have hh : i ∈ supp k := by rw [hpure i k hk]; simp
    have := (hmem k i).mp hh
    omega
  have hpinj (i : ι) : Set.InjOn (fun k => e k i) (Pure i) := by
    intro k hk l hl hkl
    apply he
    funext j
    by_cases hji : j = i
    · simpa [hji] using hkl
    · have hk0 : e k j = 0 := by
        by_contra hh
        have hmem' := (hmem k j).mpr hh
        rw [hpure i k hk] at hmem'
        exact hji (Finset.mem_singleton.mp hmem')
      have hl0 : e l j = 0 := by
        by_contra hh
        have hmem' := (hmem l j).mpr hh
        rw [hpure i l hl] at hmem'
        exact hji (Finset.mem_singleton.mp hmem')
      rw [hk0, hl0]
  have hpsum (i : ι) : (∑ k ∈ Pure i, ((p i : ℚ)⁻¹)^(e k i)) ≤
      1 / (p i - 1 : ℚ) := by
    have heq : (∑ n ∈ (Pure i).image (fun k => e k i), ((p i : ℚ)⁻¹)^n) =
        ∑ k ∈ Pure i, ((p i : ℚ)⁻¹)^(e k i) := Finset.sum_image (hpinj i)
    rw [← heq]
    apply positive_geometric_sum_le (p i) (by have := hp i; omega)
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact hppos i k hk
  let U (i : ι) := Finset.univ \ (Pure i).biUnion (fun k => B k i)
  have hUlower (i : ι) : (Fintype.card (A i) : ℚ) * (1 - 1 / (p i - 1 : ℚ)) ≤
      (U i).card :=
    relative_complement_bound (Pure i) (fun k => B k i)
      (fun k => ((p i : ℚ)⁻¹)^(e k i)) _ (fun k _ => hBcard k i) (hpsum i)
  have hU (i : ι) : (U i).Nonempty := by
    apply Finset.card_pos.mp
    exact (conditioned_ratio_bound (Fintype.card (A i)) (U i).card 0 (p i) (hp i)
      Fintype.card_pos (hUlower i) 0 (by norm_num) (by simp)).1
  let K := Finset.univ.filter (fun k => 2 ≤ (supp k).card)
  have hUcover : ∀ x ∈ Fintype.piFinset U, ∃ k ∈ K, ∀ i, x i ∈ B k i := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x
    have hkm : 2 ≤ (supp k).card := by
      by_contra hlt
      obtain ⟨i, hi⟩ := he0 k
      have hpos : 0 < (supp k).card :=
        Finset.card_pos.mpr ⟨i, (hmem k i).mpr hi⟩
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by omega : (supp k).card = 1)
      have hxj := Fintype.mem_piFinset.mp hx j
      have hnot := (Finset.mem_sdiff.mp hxj).2
      apply hnot
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hk j⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkm⟩, hk⟩
  let w (i : ι) (n : ℕ) : ℚ := if n = 0 then 1 else
    ((p i : ℚ) - 1) / (p i - 2) * ((p i : ℚ)⁻¹)^n
  have hw (i : ι) (n : ℕ) : 0 ≤ w i n := by
    have hpi : (2 : ℚ) < p i := by exact_mod_cast hp i
    dsimp [w]
    split_ifs
    · norm_num
    · exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  have hw0 (i : ι) : w i 0 = 1 := by simp [w]
  have hratio (k : κ) (i : ι) : (((U i ∩ B k i).card : ℚ) / (U i).card) ≤ w i (e k i) := by
    by_cases hzero : e k i = 0
    · rw [hB0 k i hzero, Finset.inter_univ, hzero, hw0]
      have hn : ((U i).card : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hU i).card_pos)
      rw [div_self hn]
    · have hc : ((U i ∩ B k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) *
          ((p i : ℚ)⁻¹)^(e k i) := by
        have hh : ((U i ∩ B k i).card : ℚ) ≤ (B k i).card := by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_right
        exact hh.trans (hBcard k i)
      simpa only [w, if_neg hzero] using
        (conditioned_ratio_bound (Fintype.card (A i)) (U i).card (U i ∩ B k i).card
          (p i) (hp i) Fintype.card_pos (hUlower i) _ (by positivity) hc).2
  have hbound := finite_product_cover_density A U hU K B hUcover
  have hprod : (∑ k ∈ K, ∏ i, (((U i ∩ B k i).card : ℚ) / (U i).card)) ≤
      ∑ k ∈ K, ∏ i, w i (e k i) := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hratio k i)
  have hmixed := mixed_vector_weight_bound K e he.injOn
    (fun i => Finset.univ.image (fun k => e k i))
    (fun k _ i => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    (fun k hk => (Finset.mem_filter.mp hk).2) w hw hw0
    (fun i => 1 / (p i - 2 : ℚ))
    (fun i => conditioned_geometric_sum_le (p i) (hp i) _)
  exact hbound.trans (hprod.trans hmixed)

#print axioms pure_power_box_sieve
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem fiber_card_rat {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (b : H) :
    ((Finset.univ.filter (fun x => f x = b)).card : ℚ) =
      (Fintype.card G : ℚ) / Fintype.card H := by
  classical
  have heq (y : H) : (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter (fun x => f x = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (f := f) (fun _ _ => Finset.mem_univ _)
    simpa only [heq, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] using h
  have hc : (Fintype.card H : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card H))
  apply (eq_div_iff hc).mpr
  exact_mod_cast (Nat.mul_comm _ _).trans hcard.symm

/-- A residue-independent necessary bound when the distinct moduli are products
of powers of pairwise coprime odd bases. -/
theorem coprime_power_cover_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 2 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) :
    (1 : ℚ) ≤ ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / (p i - 2 : ℚ)) := by
  classical
  let E (i : ι) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : ι) : e k i ≤ E i := Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i ^ E i)
  let f (k : κ) (i : ι) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : ι) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hB0 (k : κ) (i : ι) (hzero : e k i = 0) : B k i = Finset.univ := by
    haveI : Subsingleton (ZMod (p i ^ e k i)) := by rw [hzero, pow_zero]; infer_instance
    ext x
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Subsingleton.elim _ _
  have hBcard (k : κ) (i : ι) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : ι) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  exact pure_power_box_sieve A p hp e he he0 B hB0 hBcard hbox

#print axioms coprime_power_cover_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem factorization_product_superset (m : ℕ) (hm : m ≠ 0)
    (P : Finset ℕ) (hP : m.primeFactors ⊆ P) :
    m = ∏ r ∈ P, r ^ m.factorization r := by
  have heq : m = ∏ r ∈ m.primeFactors, r ^ m.factorization r := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hm).symm
  nth_rw 1 [heq]
  apply Finset.prod_subset hP
  intro r _ hr
  have hzero : m.factorization r = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rwa [Nat.support_factorization]
  simp [hzero]

private theorem sorted_four_odd_lower (p : Fin 4 → ℕ)
    (hp : ∀ i, 1 < p i) (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i : Fin 4, 2 * (i : ℕ) + 3 ≤ p i := by
  have H (k : ℕ) : ∀ hk : k < 4, 2 * k + 3 ≤ p ⟨k, hk⟩ := by
    induction k with
    | zero =>
      intro hk
      have h2 := hp ⟨0, hk⟩
      have hodd := Nat.odd_iff.mp (ho ⟨0, hk⟩)
      omega
    | succ k ih =>
      intro hk
      have hk' : k < 4 := by omega
      have hprev := ih hk'
      have hinc := hmono (show (⟨k, hk'⟩ : Fin 4) < ⟨k+1, hk⟩ by simp)
      have ho1 := Nat.odd_iff.mp (ho ⟨k, hk'⟩)
      have ho2 := Nat.odd_iff.mp (ho ⟨k+1, hk⟩)
      omega
  exact fun i => H i.val i.isLt

set_option maxHeartbeats 1000000 in
private theorem four_capacity_lt_one :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / ((2 * (i : ℕ) + 1 : ℕ) : ℚ))) < 1 := by
  let sets : Fin 11 → Finset (Fin 4) := ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3},
        {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, {0,1,2,3}]
  have hinj : Function.Injective sets := by decide
  let emb : Fin 11 ↪ Finset (Fin 4) := ⟨sets, hinj⟩
  have hsets : (Finset.univ : Finset (Fin 4)).powerset.filter (fun S => 2 ≤ S.card) =
      Finset.univ.map emb := by decide +revert
  rw [hsets, Finset.sum_map]
  norm_num [emb, sets, Fin.sum_univ_succ, Finset.prod_insert, Fin.ext_iff]

private theorem not_cover_four_odd_primes {κ : Type*} [Fintype κ]
    (P : Finset ℕ) (hPcard : P.card = 4) (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hmi : Function.Injective m)
    (hPF : ∀ k, (m k).primeFactors ⊆ P)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) : False := by
  classical
  let p := P.orderEmbOfFin hPcard
  have hprime (i : Fin 4) : (p i).Prime := (hP _ (P.orderEmbOfFin_mem hPcard i)).1
  have hodd (i : Fin 4) : Odd (p i) := (hP _ (P.orderEmbOfFin_mem hPcard i)).2
  have hlower := sorted_four_odd_lower p (fun i => (hprime i).one_lt) hodd p.strictMono
  have hp (i : Fin 4) : 2 < p i := by have := hlower i; omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (p.injective h))
  let e (k : κ) (i : Fin 4) := (m k).factorization (p i)
  have hprod (k : κ) : m k = ∏ i, p i ^ e k i := by
    have heq := factorization_product_superset (m k) (by have := hm k; omega) P (hPF k)
    rw [heq]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact Finset.prod_map _ _ (fun r : ℕ => r ^ (m k).factorization r)
  have he : Function.Injective e := by
    intro k l hkl
    apply hmi
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra h
    push_neg at h
    have hh := hm k
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hbound := coprime_power_cover_bound p hp hcop e he he0 a (by
    intro x
    obtain ⟨k, hk⟩ := hcover x
    exact ⟨k, by rwa [← hprod k]⟩)
  have hle : (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / (p i - 2 : ℚ))) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
        ∏ i ∈ S, (1 / ((2 * (i : ℕ) + 1 : ℕ) : ℚ)) := by
    apply Finset.sum_le_sum
    intro S _
    apply Finset.prod_le_prod
    · intro i _
      have hp' : (2 : ℚ) < p i := by exact_mod_cast hp i
      exact div_nonneg (by norm_num) (by linarith)
    · intro i _
      have hh : ((2 * (i : ℕ) + 3 : ℕ) : ℚ) ≤ p i := by exact_mod_cast hlower i
      apply one_div_le_one_div_of_le (by positivity)
      push_cast at hh ⊢
      linarith
  have hsmall : (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / ((2 * (i : ℕ) + 1 : ℕ) : ℚ))) < 1 := four_capacity_lt_one
  exact (not_lt_of_ge (hbound.trans hle)) hsmall

private theorem extend_odd_prime_set (P : Finset ℕ) (n : ℕ) (hcard : P.card ≤ n)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    ∃ T : Finset ℕ, P ⊆ T ∧ T.card = n ∧ ∀ p ∈ T, p.Prime ∧ Odd p := by
  classical
  let A : Set ℕ := {p | p.Prime} \ {2}
  have hA : A.Infinite := Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)
  have hAP : (A \ (P : Set ℕ)).Infinite := hA.diff P.finite_toSet
  obtain ⟨U, hU, hUc⟩ := hAP.exists_subset_card_eq (n - P.card)
  have hdis : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro p hp hu
    exact (hU hu).2 hp
  refine ⟨P ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, hUc]
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · have hh := (hU hp).1
      exact ⟨hh.1, hh.1.odd_of_ne_two (by simpa using hh.2)⟩

/-- An odd arithmetic cover with distinct nontrivial moduli requires at least
five distinct prime factors, without any squarefreeness assumption. -/
theorem arithmetic_cover_prime_count {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hodd : ∀ k, Odd (m k))
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    5 ≤ (Finset.univ.biUnion (fun k => (m k).primeFactors)).card := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hpf := Nat.mem_primeFactors.mp hk
    exact ⟨hpf.1, (hodd k).of_dvd_nat hpf.2.1⟩
  by_contra hc
  have hcard : P.card ≤ 4 := by dsimp [P]; omega
  obtain ⟨T, hPT, hTc, hT⟩ := extend_odd_prime_set P 4 hcard hP
  apply not_cover_four_odd_primes T hTc hT m a hm hm_inj _ hcover
  intro k p hp
  exact hPT (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hp⟩)

#print axioms arithmetic_cover_prime_count
end Erdos7Reduction
