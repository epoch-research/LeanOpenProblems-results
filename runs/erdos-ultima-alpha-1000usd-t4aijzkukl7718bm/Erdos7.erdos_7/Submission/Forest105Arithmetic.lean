import Submission.NinetyFourModuli

/-! Reusing the verified forest certificate with its unused rational margin.
The eight-prime profile is excluded through105 classes. The unrestricted
conjecture remains unresolved. -/
namespace Erdos7Forest105
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression Erdos7CardinalitySieve
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7Forest93Profile
open Erdos7Forest93ShapeArithmetic Erdos7Forest93Concrete
open Erdos7ForestRestricted Erdos7ForestUnion Erdos7RootOverlapCompensation
open Erdos7ForestProduct Erdos7Forest93Events Erdos7ForestCapacity Erdos7ForestEvents
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option Elab.async false

/-- No new numeric table is needed: twelve more mixed classes cost12/864. -/
theorem selection_certificate (x : Index → ℚ) (hx : ∀ i,0 ≤ x i ∧ x i ≤ 1)
    (hcard : (∑ i,x i) ≤ 96) :
    (∑ i,weight i*x i)-(∑ e ∈ edges,coefficient e*x e.1*x e.2) < 1 := by
  have hh := forest_threshold_bound edges weight x coefficient coefficient 96 (1/864)
    hx hcard (by norm_num) (fun e he => ⟨coefficient_nonneg e,le_rfl⟩)
  have he : (96:ℚ)*(1/864)+(∑ i,max (weight i-incident edges coefficient i-1/864) 0)+
      (∑ e ∈ edges,coefficient e) = thresholdValue+12/864 := by
    unfold thresholdValue
    ring
  rw [he] at hh
  apply hh.trans_lt
  have hv := value_bound
  rw [total_checked] at hv
  norm_num only [denominator,Nat.cast_ofNat] at hv
  linarith

variable {Ω : Type*} [Fintype Ω]

theorem union_mass_lt_one (μ : Ω → ℚ) (hμ : ∀ z,0 ≤ μ z)
    (A : Index → Ω → Prop) (S : Finset Index) (hcard : S.card ≤ 96)
    (hw : ∀ i,mass μ (A i) ≤ weight i*selection S i)
    (hprod : ∀ e ∈ ordinary,mass μ (A e.1)*mass μ (A e.2) ≤
      mass μ (fun z => A e.1 z ∧ A e.2 z))
    (hroot : 192 ∈ S → 160 ∈ S → ∃ u v : ℚ,
      (u = 2/5 ∨ u = 3/5) ∧ (v = 2/5 ∨ v = 3/5) ∧
      mass μ (A 192) = u/4 ∧ mass μ (A 160) = v/6 ∧
      (if u = v then u/24 else 0) ≤ mass μ (fun z => A 160 z ∧ A 192 z)) :
    mass μ (fun z => ∃ i,A i z) < 1 := by
  classical
  let W (i : Index) := weight i*selection S i
  let overlap := mass μ (fun z => A 160 z ∧ A 192 z)
  let slack (i : Index) := (W i-mass μ (A i))*(1-neighbor ordinary W i)
  have hW (i : Index) : W i ≤ weight i := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (selection_bounds S i).2 (weight_nonneg i)
  have hd (i : Index) : neighbor ordinary W i ≤ 1 :=
    (neighbor_mono ordinary W weight hW i).trans (degree_bound i)
  have hn (i : Index) : 0 ≤ slack i :=
    mul_nonneg (sub_nonneg.mpr (hw i)) (sub_nonneg.mpr (hd i))
  have hsum : 0 ≤ ∑ i,slack i := Finset.sum_nonneg (fun i _ => hn i)
  have hoverlap : 0 ≤ overlap := mass_nonneg μ hμ _
  have hcomp : (1/40)*selection S 192*selection S 160 ≤ overlap+∑ i,slack i := by
    by_cases h₁ : 192 ∈ S
    · by_cases h₂ : 160 ∈ S
      · obtain ⟨u,v,hu,hv,ha,hb,hi⟩ := hroot h₁ h₂
        have hd₁ := (neighbor_mono ordinary W weight hW (192:Index)).trans pivot_degree.1
        have hd₂ := (neighbor_mono ordinary W weight hW (160:Index)).trans pivot_degree.2
        have hc := Erdos7RootOverlapCompensation.branch_overlap_charge u v
          (neighbor ordinary W 192) (neighbor ordinary W 160) hu hv hd₁ hd₂
        have hs := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({192,160}:Finset Index) ⊆ Finset.univ from Finset.subset_univ _)
          (fun i _ _ => hn i)
        rw [Finset.sum_pair (by decide : (192:Index) ≠ 160)] at hs
        have hw₁ : W 192 = 3/20 := by simp only [W,selection_mem S 192 h₁,Erdos7Forest93Events.pivot_weights.1,mul_one]
        have hw₂ : W 160 = 1/10 := by simp only [W,selection_mem S 160 h₂,Erdos7Forest93Events.pivot_weights.2,mul_one]
        dsimp only [slack] at hs
        rw [hw₁,hw₂,ha,hb] at hs
        rw [selection_mem S 192 h₁,selection_mem S 160 h₂]
        dsimp only [overlap] at *
        linarith
      · rw [selection_not_mem S 160 h₂,mul_zero]
        linarith
    · rw [selection_not_mem S 192 h₁,mul_zero,zero_mul]
      linarith
  have hb := compensated_forest_bound μ hμ A parent rank parent_lt edges edge_parent_iff
    forced forced_mem W hw overlap ((1/40)*selection S 192*selection S 160) hprod le_rfl hcomp
  have hsel := Erdos7Forest105.selection_certificate (selection S) (selection_bounds S)
    (by rw [selection_sum]; exact_mod_cast hcard)
  rw [← polynomial_selection S] at hsel
  exact hb.trans_lt hsel

lemma selected_union_lt_one (b : Fin 9) (hb : b.val%3 ≠ 0) (S : Finset Index)
    (hcard : S.card ≤ 96) (hmixed : ∀ i ∈ S,mixed i)
    (r : Index → Space) (hr : ∀ i ∈ S,good i (r i)) :
    mass (measure b) (fun x => ∃ i,selectedBox S r i x) < 1 := by
  apply Erdos7Forest105.union_mass_lt_one (measure b) (measure_nonneg b) (selectedBox S r) S hcard
  · intro i
    rw [selectedBox_mass]
    by_cases hi : i ∈ S
    · rw [selection_mem S i hi,mul_one,mul_one]
      exact residueBox_mass_le b hb i (hmixed i hi) (r i)
    · simp only [selection_not_mem S i hi,mul_zero,le_refl]
  · intro e he
    by_cases h₁ : e.1 ∈ S
    · by_cases h₂ : e.2 ∈ S
      · unfold selectedBox
        simp only [h₁,h₂,true_and]
        exact le_of_eq (residueBox_independent b hb e.1 e.2 (r e.1) (r e.2)
          (ordinary_disjoint ⟨e,he⟩)).symm
      · rw [selectedBox_mass b S r e.2,selection_not_mem S e.2 h₂,mul_zero,mul_zero]
        exact mass_nonneg _ (measure_nonneg b) _
    · rw [selectedBox_mass b S r e.1,selection_not_mem S e.1 h₁,mul_zero,zero_mul]
      exact mass_nonneg _ (measure_nonneg b) _
  · intro h₁ h₂
    refine ⟨rootProbability b (r 192 0),rootProbability b (r 160 0),?_,?_,?_,?_,?_⟩
    · exact rootProbability_cases b _ hb ((hr 192 h₁).1 (by rw [pivot_exponents.1]; decide))
    · exact rootProbability_cases b _ hb ((hr 160 h₂).1 (by rw [pivot_exponents.2]; decide))
    · unfold selectedBox
      simp only [h₁,true_and]
      exact pivot192_mass b hb _ (hr 192 h₁)
    · unfold selectedBox
      simp only [h₂,true_and]
      exact pivot160_mass b hb _ (hr 160 h₂)
    · simp only [selectedBox,h₁,h₂,true_and]
      exact pivot_intersection_lower b hb _ _ (hr 192 h₁) (hr 160 h₂)


theorem exists_uncovered (b : Fin 9) (hb : b.val%3 ≠ 0) (S : Finset Index)
    (hcard : S.card ≤ 96) (hmixed : ∀ i ∈ S,mixed i)
    (r : Index → Space) (hr : ∀ i ∈ S,good i (r i)) :
    ∃ x : Space,(∀ j,x j ∈ allowed b j) ∧ ∀ i ∈ S,¬residueBox i (r i) x := by
  classical
  by_contra h
  push_neg at h
  have he : mass (measure b) (fun x => ∃ i,selectedBox S r i x) =
      mass (measure b) (fun _ => True) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ j,x j ∈ allowed b j
    · obtain ⟨i,hi,hix⟩ := h x hx
      have hh : ∃ i,selectedBox S r i x := ⟨i,hi,hix⟩
      simp only [bit,if_pos hh,if_true]
    · rw [measure_zero_outside b x hx,zero_mul,zero_mul]
  have hh := Erdos7Forest105.selected_union_lt_one b hb S hcard hmixed r hr
  rw [he,measure_full b hb] at hh
  exact lt_irrefl _ hh


lemma profile_not_cover {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hclosed : ∀ i d,1 < d → d ∣ m i → ∃ j,m j = d)
    (hpriv : ∀ i,∃ x : ℤ,∀ j,j ≠ i → ¬(m j:ℤ) ∣ x-a j)
    (hP : Finset.univ.biUnion (fun k => (m k).primeFactors) = primeSet)
    (hE : ∀ j,(Finset.univ.lcm m).factorization (primes j) = caps j)
    (hcard : Fintype.card κ ≤ 105) : False := by
  classical
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  obtain ⟨f,hfi,hfm,hfe⟩ := exists_encoding m hm0 hc.1 hP hE
  obtain ⟨t,hprime,hcop,hc'⟩ := composite_residues_coprime_after_normalization m a hc hclosed hpriv
  let a' (k : κ) := a k-t
  obtain ⟨k₉,hk₉⟩ : ∃ k,m k = 9 := by
    obtain ⟨k,hk⟩ := Erdos7No9Certificate.arithmetic_exists_nine m a hc
    exact hclosed k 9 (by decide) hk
  let b : Fin 9 := arithResidue (a' k₉) 0
  have hb : b.val%3 ≠ 0 := by
    intro hh
    have hdiv : (3:ℤ) ∣ a' k₉ := (residueFin_mod_zero 9 3 (by decide) (by decide) (a' k₉)).mp hh
    apply coprime_not_prime_dvd (a' k₉) (m k₉) 3 (by norm_num)
      (hcop k₉ (by rw [hk₉]; norm_num)) (by rw [hk₉]; decide) hdiv
  let T := Finset.univ.filter (fun k => mixed (f k))
  have hT : T.card ≤ 96 := by
    have hh := divisor_closed_mixed_card_bound m hm0 hclosed primes
      (fun j => (prime_properties.2 j).1) prime_properties.1 105 hcard
    have hmax (j : Fin 8) : Finset.univ.sup (fun k => (m k).factorization (primes j)) = caps j :=
      (factorization_finset_lcm Finset.univ m (fun k _ => hm0 k) (primes j)).symm.trans (hE j)
    simp_rw [hmax] at hh
    rw [cap_sum] at hh
    convert hh using 1
    congr 1
    ext k
    simp only [T,Finset.mem_filter,Finset.mem_univ,true_and,mixed,support,exponentSupport,hfe]
  let S : Finset Index := T.image f
  have hS : S.card ≤ 96 := Finset.card_image_le.trans hT
  have hSmixed (i : Index) (hi : i ∈ S) : mixed i := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hk).2
  let r : Index → Space := Function.extend f (fun k => arithResidue (a' k)) (fun _ => arithResidue 0)
  have hr (k : κ) : r (f k) = arithResidue (a' k) := hfi.extend_apply _ _ k
  have hgood (i : Index) (hi : i ∈ S) : good i (r i) := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    rw [hr]
    apply arithResidue_good
    rw [hfm]
    apply hcop k
    rw [← hfm k]
    exact mixed_not_prime (f k) (Finset.mem_filter.mp hk).2
  obtain ⟨x,hx,havoid⟩ := Erdos7Forest105.exists_uncovered b hb S hS hSmixed r hgood
  obtain ⟨z,hz⟩ := exists_crt x
  obtain ⟨k,hk⟩ := hc'.2.2 z
  change (m k:ℤ) ∣ z-a' k at hk
  by_cases hmix : mixed (f k)
  · have hmem : f k ∈ S := Finset.mem_image.mpr
      ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmix⟩,rfl⟩
    apply havoid (f k) hmem
    rw [hr]
    apply coverage_box (f k) (a' k) z x hz
    rwa [hfm]
  · rcases nonmixed_classification (f k) hmix with h1 | h9 | hp
    · have hgt := (hc.2.1 k).1
      rw [hfm] at h1
      omega
    · have heq : k = k₉ := hc.1 (by rw [← hfm k,h9,hk₉])
      subst k
      rw [hk₉] at hk
      exact allowed_not_nine (a' k₉) x hx z hz hk
    · obtain ⟨j,hj,_⟩ := prime_classification (f k) hp
      have hka : (m k:ℤ) ∣ a' k := hprime k (by rwa [hfm] at hp)
      have hdz : (m k:ℤ) ∣ z := by simpa only [sub_add_cancel] using dvd_add hk hka
      apply allowed_not_prime b x hx z hz j
      rwa [← hfm k,hj] at hdz


#print axioms selection_certificate
#print axioms profile_not_cover
end Erdos7Forest105
