import Submission.FullProgress
import Submission.TwistedHyperbola
import Submission.HyperbolaPascal

/-! A conditional hyperbola construction. Large square-entry product tuples
supply general-position subsets of at least half their size. No existence
of arbitrarily large arithmetic tuples is asserted. -/
open EuclideanGeometry
namespace Erdos213.HyperbolaTupleExtraction
set_option maxHeartbeats 2000000

lemma product_ne_of_fourths_lt {N a b c d : ℚ}
    (hN : 0 < N) (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (haN : a^4 < N) (hbN : b^4 < N) (hcN : c^4 < N) (hdN : d^4 < N) :
    a*b*c*d ≠ N := by
  intro he
  have h2 := mul_lt_mul haN hbN.le (pow_pos hb 4) hN.le
  have h3 := mul_lt_mul h2 hcN.le (pow_pos hc 4) (mul_pos hN hN).le
  have h4 := mul_lt_mul h3 hdN.le (pow_pos hd 4) (mul_pos (mul_pos hN hN) hN).le
  have hh : a^4*b^4*c^4*d^4 = N*N*N*N := by
    calc
      _ = (a*b*c*d)^4 := by ring
      _ = _ := by rw [he]; ring
  exact (ne_of_lt h4) hh

lemma product_ne_of_lt_fourths {N a b c d : ℚ}
    (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (_hd : 0 < d)
    (hNa : N < a^4) (hNb : N < b^4) (hNc : N < c^4) (hNd : N < d^4) :
    a*b*c*d ≠ N := by
  intro he
  have h2 := mul_lt_mul hNa hNb.le hN (pow_pos ha 4).le
  have h3 := mul_lt_mul h2 hNc.le hN (mul_pos (pow_pos ha 4) (pow_pos hb 4)).le
  have h4 := mul_lt_mul h3 hNd.le hN
    (mul_pos (mul_pos (pow_pos ha 4) (pow_pos hb 4)) (pow_pos hc 4)).le
  have hh : a^4*b^4*c^4*d^4 = N*N*N*N := by
    calc
      _ = (a*b*c*d)^4 := by ring
      _ = _ := by rw [he]; ring
  exact (ne_of_lt h4) hh.symm

def OneSide (N : ℚ) (T : Finset ℚ) : Prop :=
  (∀ a ∈ T, a^4 < N) ∨ (∀ a ∈ T, N < a^4)

lemma extract_half {S : Finset ℚ} {N : ℚ} {n : ℕ}
    (hpos : ∀ a ∈ S, 0 < a) (hcard : 2*n ≤ S.card) :
    ∃ T : Finset ℚ, T ⊆ S ∧ T.card = n ∧ OneSide N T := by
  classical
  let L := S.filter (fun a => a^4 < N)
  let U := (S \ L).filter (fun a => N < a^4)
  let E := (S \ L).filter (fun a => ¬ N < a^4)
  have hEeq : ∀ a ∈ E, a^4 = N := by
    intro a ha
    obtain ⟨haSL, han⟩ := Finset.mem_filter.mp ha
    obtain ⟨haS, haL⟩ := Finset.mem_sdiff.mp haSL
    have hnot : ¬ a^4 < N := by
      intro h
      exact haL (Finset.mem_filter.mpr ⟨haS,h⟩)
    exact le_antisymm (le_of_not_gt han) (le_of_not_gt hnot)
  have hES : E ⊆ S := fun _ h => Finset.sdiff_subset (Finset.mem_of_mem_filter _ h)
  have hEc : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (pow_left_inj₀ (hpos a (hES ha)).le (hpos b (hES hb)).le (by decide : 4 ≠ 0)).mp
      ((hEeq a ha).trans (hEeq b hb).symm)
  have hSL := Finset.card_sdiff_add_card_eq_card (show L ⊆ S from Finset.filter_subset _ _)
  have hUE : U.card + E.card = (S \ L).card :=
    Finset.card_filter_add_card_filter_not (fun a : ℚ => N < a^4)
  by_cases hnL : n ≤ L.card
  · obtain ⟨T,hTL,hTc⟩ := Finset.exists_subset_card_eq hnL
    exact ⟨T,hTL.trans (Finset.filter_subset _ _),hTc,Or.inl
      (fun a ha => (Finset.mem_filter.mp (hTL ha)).2)⟩
  · have hnU : n ≤ U.card := by omega
    obtain ⟨T,hTU,hTc⟩ := Finset.exists_subset_card_eq hnU
    refine ⟨T,?_,hTc,Or.inr (fun a ha => (Finset.mem_filter.mp (hTU ha)).2)⟩
    exact hTU.trans ((Finset.filter_subset _ _).trans Finset.sdiff_subset)

lemma OneSide.product_ne {N : ℚ} {T : Finset ℚ} (h : OneSide N T)
    (hN : 0 < N) (hpos : ∀ a ∈ T, 0 < a)
    {a b c d : ℚ} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) :
    a*b*c*d ≠ N := by
  rcases h with h | h
  · exact product_ne_of_fourths_lt hN (hpos a ha) (hpos b hb) (hpos c hc) (hpos d hd)
      (h a ha) (h b hb) (h c hc) (h d hd)
  · exact product_ne_of_lt_fourths hN (hpos a ha) (hpos b hb) (hpos c hc) (hpos d hd)
      (h a ha) (h b hb) (h c hc) (h d hd)

noncomputable def point (N a : ℚ) : ℝ² := HyperbolaPascal.embed N (a,a⁻¹)

lemma point_injective (N : ℚ) : Function.Injective (point N) := by
  intro a b h
  have hh := congrArg (fun p : ℝ² => p 0) h
  change (a : ℝ) = (b : ℝ) at hh
  exact_mod_cast hh

lemma point_dist_sq {N : ℚ} (hN : 0 ≤ N) (a b : ℚ) :
    dist (point N a) (point N b)^2 = (TwistedHyperbola.distanceSq N a b : ℝ) :=
  HyperbolaPascal.embed_dist_sq N hN (a,a⁻¹) (b,b⁻¹)

lemma point_rational_dist {N a b : ℚ} (hN : 0 ≤ N) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hsq : TwistedHyperbola.productCondition N a b) :
    dist (point N a) (point N b) ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply (HyperbolaPascal.rational_distance_iff N hN (a,a⁻¹) (b,b⁻¹)).mpr
  exact (TwistedHyperbola.distance_square_iff N a b ha hb hab).mpr hsq

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a,b,c}) :
    (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private def rdet (a b c d e f g h i : ℝ) : ℝ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

private lemma plane_dist_sq (a b : ℝ²) :
    dist a b^2 = (a 0-b 0)^2+(a 1-b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq]

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    rdet (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2)=0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [plane_dist_sq] at ha hb hc hd ⊢
  unfold rdet
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1))*(hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1))*(hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1))*(hd-ha)

lemma point_not_collinear {N a b c : ℚ} (hN : 0 < N)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ {point N a,point N b,point N c} := by
  have hn : TwistedHyperbola.triangle a b c ≠ 0 := by
    intro hz
    have hh := TwistedHyperbola.triangle_factor a b c ha hb hc
    rw [hz,zero_mul] at hh
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hab))
      (sub_ne_zero.mpr hac)) (sub_ne_zero.mpr hbc)) hh.symm
  intro h
  have hz := collinear_det_zero h
  have hz' : (TwistedHyperbola.triangle a b c : ℝ)*Real.sqrt (N : ℝ)=0 := by
    convert hz using 1
    simp only [point,HyperbolaPascal.embed,PiLp.toLp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,TwistedHyperbola.triangle]
    push_cast
    ring
  have hn' : (TwistedHyperbola.triangle a b c : ℝ) ≠ 0 := by exact_mod_cast hn
  exact (mul_ne_zero hn' (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN))) hz'

lemma point_not_cospherical {N a b c d : ℚ} (hN : 0 < N)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hp : a*b*c*d ≠ N) :
    ¬ Cospherical {point N a,point N b,point N c,point N d} := by
  have hn : TwistedHyperbola.circle N a b c d ≠ 0 := by
    intro hz
    have hh := TwistedHyperbola.circle_factor N a b c d ha hb hc hd
    rw [hz,zero_mul] at hh
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac)) (sub_ne_zero.mpr had))
      (sub_ne_zero.mpr hbc)) (sub_ne_zero.mpr hbd)) (sub_ne_zero.mpr hcd))
      (sub_ne_zero.mpr hp)) hh.symm
  intro h
  have hz := cospherical_det_zero h
  simp only [point_dist_sq hN.le] at hz
  have hz' : (TwistedHyperbola.circle N a b c d : ℝ)*Real.sqrt (N : ℝ)=0 := by
    convert hz using 1
    simp only [point,HyperbolaPascal.embed,PiLp.toLp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,TwistedHyperbola.circle,TwistedHyperbola.det3,rdet]
    push_cast
    ring
  have hn' : (TwistedHyperbola.circle N a b c d : ℝ) ≠ 0 := by exact_mod_cast hn
  exact (mul_ne_zero hn' (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN))) hz'

/-- A finite arithmetic certificate on a twisted rectangular hyperbola. -/
theorem certificate {n : ℕ} (N : ℚ) (hN : 0 < N) (t : Fin n → ℚ)
    (ht : Function.Injective t) (hpos : ∀ i, 0 < t i)
    (hsq : ∀ i j, i ≠ j → TwistedHyperbola.productCondition N (t i) (t j))
    (hprod : ∀ i j k l, t i*t j*t k*t l ≠ N) : Erdos213For n := by
  apply (erdos213For_iff_rational n).mpr
  let p : Fin n → ℝ² := fun i => point N (t i)
  have hp : Function.Injective p := (point_injective N).comp ht
  have hne (i : Fin n) : t i ≠ 0 := ne_of_gt (hpos i)
  refine ⟨Set.range p,Set.finite_range _,?_,⟨?_,?_⟩,?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact point_not_collinear hN (hne i) (hne j) (hne k)
      (fun he => hij (congrArg (point N) he))
      (fun he => hik (congrArg (point N) he))
      (fun he => hjk (congrArg (point N) he))
  · intro Q hQ h4 hcos
    obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp h4
    subst Q
    obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,d} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({p i,b,c,d} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({p i,p j,c,d} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ (by simp : d ∈ ({p i,p j,p k,d} : Set ℝ²))
    exact point_not_cospherical hN (hne i) (hne j) (hne k) (hne l)
      (fun he => hab (congrArg (point N) he)) (fun he => hac (congrArg (point N) he))
      (fun he => had (congrArg (point N) he)) (fun he => hbc (congrArg (point N) he))
      (fun he => hbd (congrArg (point N) he)) (fun he => hcd (congrArg (point N) he))
      (hprod i j k l) hcos
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hij
    exact point_rational_dist hN.le (hne i) (hne j)
      (fun he => hij (congrArg (point N) he)) (hsq i j (fun he => hij (he ▸ rfl)))

/-- From 2n positive parameters satisfying the product-square conditions,
extract n points in general position and clear their distance denominators.
There is no diagonal (antipodal) square condition in this theorem. -/
theorem erdos213For_of_square_product_tuple {n : ℕ} (N : ℚ) (hN : 0 < N)
    (S : Finset ℚ) (hpos : ∀ a ∈ S, 0 < a) (hcard : 2*n ≤ S.card)
    (hsq : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → TwistedHyperbola.productCondition N a b) :
    Erdos213For n := by
  classical
  obtain ⟨T,hTS,hTc,hside⟩ := extract_half (N := N) hpos hcard
  let e : Fin n ≃ T := (Fintype.equivFinOfCardEq (show Fintype.card T = n by simpa using hTc)).symm
  let t : Fin n → ℚ := fun i => e i
  have ht : Function.Injective t := Subtype.val_injective.comp e.injective
  have hmem (i : Fin n) : t i ∈ T := (e i).property
  apply certificate N hN t ht (fun i => hpos _ (hTS (hmem i)))
  · intro i j hij
    exact hsq _ (hTS (hmem i)) _ (hTS (hmem j)) (ht.ne hij)
  · intro i j k l
    exact hside.product_ne hN (fun a ha => hpos a (hTS ha))
      (hmem i) (hmem j) (hmem k) (hmem l)

/-- This is a sufficient hypothesis, NOT an established existence theorem. -/
def UnboundedSquareProductTuples : Prop :=
  ∀ m : ℕ, ∃ N : ℚ, 0 < N ∧ ∃ S : Finset ℚ, m ≤ S.card ∧
    (∀ a ∈ S, 0 < a) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → TwistedHyperbola.productCondition N a b)

/-- A conditional construction for all cardinalities. The arithmetic premise
is not proved here and is not replaced by ordinary Diophantine-tuple existence. -/
theorem conjecture_of_unbounded_square_product_tuples
    (h : UnboundedSquareProductTuples) : ∀ n : ℕ, n ≥ 4 → Erdos213For n := by
  intro n _
  obtain ⟨N,hN,S,hcard,hpos,hsq⟩ := h (2*n)
  exact erdos213For_of_square_product_tuple N hN S hpos hcard hsq

#print axioms extract_half
#print axioms OneSide.product_ne
#print axioms point_rational_dist
#print axioms point_not_collinear
#print axioms point_not_cospherical
#print axioms erdos213For_of_square_product_tuple
#print axioms conjecture_of_unbounded_square_product_tuples
end Erdos213.HyperbolaTupleExtraction
