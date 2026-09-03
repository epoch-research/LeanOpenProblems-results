import Submission.InversionReduction

/-! A covering-number reformulation of Erdős 213. No unbounded-cover
construction is asserted. Lines and circles are treated uniformly through
the previously verified generalized-circle predicate. -/
open EuclideanGeometry
namespace Erdos213.CircleCoverReduction
open InversionReduction
noncomputable section
set_option maxHeartbeats 3000000

def dx (a p : ℝ²) : ℝ := p 0-a 0
def dy (a p : ℝ²) : ℝ := p 1-a 1
def qnorm (a p : ℝ²) : ℝ := dx a p^2+dy a p^2

def ca (a b c : ℝ²) : ℝ := dx a b*dy a c-dy a b*dx a c
def cb (a b c : ℝ²) : ℝ := dy a b*qnorm a c-qnorm a b*dy a c
def cc (a b c : ℝ²) : ℝ := qnorm a b*dx a c-dx a b*qnorm a c

def circleEval (a b c p : ℝ²) : ℝ :=
  ca a b c*qnorm a p+cb a b c*dx a p+cc a b c*dy a p

lemma qnorm_eq_dist (a p : ℝ²) : qnorm a p = dist p a^2 := by
  rw [distance_sq]
  rfl

lemma coefficient_identity (a b c : ℝ²) :
    cb a b c^2+cc a b c^2 = qnorm a b*qnorm a c*qnorm b c := by
  simp only [cb,cc,qnorm,dx,dy]
  ring

lemma coefficients_nonzero {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cb a b c ≠ 0 ∨ cc a b c ≠ 0 := by
  have hp : 0 < qnorm a b*qnorm a c*qnorm b c := by
    simp only [qnorm_eq_dist]
    exact mul_pos (mul_pos (sq_pos_of_pos (dist_pos.mpr hab.symm))
      (sq_pos_of_pos (dist_pos.mpr hac.symm))) (sq_pos_of_pos (dist_pos.mpr hbc.symm))
  rw [← coefficient_identity] at hp
  by_contra! h
  simp [h.1,h.2] at hp

lemma circleEval_generalized {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    OnGeneralizedCircle {p : ℝ² | circleEval a b c p=0} := by
  refine ⟨ca a b c, cb a b c-2*ca a b c*a 0,
    cc a b c-2*ca a b c*a 1,
    ca a b c*radiusSq a-cb a b c*a 0-cc a b c*a 1, ?_, ?_⟩
  · by_cases h : ca a b c=0
    · simpa [h] using (coefficients_nonzero hab hac hbc)
    · exact Or.inl h
  · intro p hp
    change circleEval a b c p=0 at hp
    dsimp [circleEval,qnorm,dx,dy,radiusSq] at hp ⊢
    linear_combination hp

private lemma determinant_zero (a b c x y z u v w r s t : ℝ)
    (hn : a≠0 ∨ b≠0 ∨ c≠0)
    (h1 : a*x+b*y+c*z=0) (h2 : a*u+b*v+c*w=0) (h3 : a*r+b*s+c*t=0) :
    (y*w-z*v)*r+(z*u-x*w)*s+(x*v-y*u)*t=0 := by
  rcases hn with ha | hb | hc
  · apply (mul_eq_zero.mp (show a*((y*w-z*v)*r+(z*u-x*w)*s+(x*v-y*u)*t)=0 from ?_)).resolve_left ha
    linear_combination (v*t-w*s)*h1+(z*s-y*t)*h2+(y*w-z*v)*h3
  · apply (mul_eq_zero.mp (show b*((y*w-z*v)*r+(z*u-x*w)*s+(x*v-y*u)*t)=0 from ?_)).resolve_left hb
    linear_combination (w*r-u*t)*h1+(x*t-z*r)*h2+(z*u-x*w)*h3
  · apply (mul_eq_zero.mp (show c*((y*w-z*v)*r+(z*u-x*w)*s+(x*v-y*u)*t)=0 from ?_)).resolve_left hc
    linear_combination (u*s-v*r)*h1+(y*r-x*s)*h2+(x*v-y*u)*h3

lemma generalized_subset_circleEval {S : Set ℝ²} (hS : OnGeneralizedCircle S)
    {a b c : ℝ²} (ha : a∈S) (hb : b∈S) (hc : c∈S) :
    S ⊆ {p : ℝ² | circleEval a b c p=0} := by
  obtain ⟨u,v,w,d,hn,he⟩ := hS
  have hn' : u≠0 ∨ v+2*u*a 0≠0 ∨ w+2*u*a 1≠0 := by
    by_cases hu : u=0
    · simpa [hu] using hn
    · exact Or.inl hu
  have hh : ∀ p∈S, u*qnorm a p+(v+2*u*a 0)*dx a p+(w+2*u*a 1)*dy a p=0 := by
    intro p hp
    have hpa := he p hp
    have haa := he a ha
    simp only [qnorm,dx,dy,radiusSq] at hpa haa ⊢
    linear_combination hpa-haa
  intro p hp
  exact determinant_zero u (v+2*u*a 0) (w+2*u*a 1)
    (qnorm a b) (dx a b) (dy a b) (qnorm a c) (dx a c) (dy a c)
    (qnorm a p) (dx a p) (dy a p) hn' (hh b hb) (hh c hc) (hh p hp)

/-- Repeated anchors use a singleton, ensuring every member of our covering
family remains a generalized circle rather than the whole plane. -/
def through (a b c : ℝ²) : Set ℝ² :=
  if a≠b ∧ a≠c ∧ b≠c then {p | circleEval a b c p=0} else {a}

lemma through_generalized (a b c : ℝ²) : OnGeneralizedCircle (through a b c) := by
  unfold through
  split_ifs with h
  · exact circleEval_generalized h.1 h.2.1 h.2.2
  · exact generalized_of_cospherical (cospherical_singleton a)

lemma generalized_subset_through {S : Set ℝ²} (hS : OnGeneralizedCircle S)
    {a b c : ℝ²} (ha : a∈S) (hb : b∈S) (hc : c∈S)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) : S ⊆ through a b c := by
  simpa [through, hab,hac,hbc] using generalized_subset_circleEval hS ha hb hc

/-- A cover by at most k sets each lying on a line or circle. Allowing subsets
rather than full circles does not affect the existence of such a cover. -/
def CoveredBy (S : Set ℝ²) (k : ℕ) : Prop :=
  ∃ F : Finset (Set ℝ²), F.card≤k ∧ (∀ C∈F, OnGeneralizedCircle C) ∧
    ∀ p∈S, ∃ C∈F, p∈C

lemma CoveredBy.mono {S T : Set ℝ²} {k : ℕ} (h : CoveredBy T k) (hST : S⊆T) :
    CoveredBy S k := by
  obtain ⟨F,hF,hgen,hcov⟩ := h
  exact ⟨F,hF,hgen,fun p hp => hcov p (hST hp)⟩

lemma coveredBy_one {S : Set ℝ²} (h : OnGeneralizedCircle S) : CoveredBy S 1 := by
  classical
  refine ⟨{S},by simp,?_,?_⟩
  · intro C hC
    simpa only [Finset.mem_singleton.mp hC] using h
  · intro p hp
    exact ⟨S,by simp,hp⟩

lemma CoveredBy.union {S T : Set ℝ²} {k l : ℕ}
    (hS : CoveredBy S k) (hT : CoveredBy T l) : CoveredBy (S∪T) (k+l) := by
  classical
  obtain ⟨F,hF,hFg,hFc⟩ := hS
  obtain ⟨G,hG,hGg,hGc⟩ := hT
  refine ⟨F∪G,(Finset.card_union_le _ _).trans (Nat.add_le_add hF hG),?_,?_⟩
  · intro C hC
    exact (Finset.mem_union.mp hC).elim (hFg C) (hGg C)
  · intro p hp
    rcases hp with hp | hp
    · obtain ⟨C,hC,hpC⟩ := hFc p hp
      exact ⟨C,Finset.mem_union_left _ hC,hpC⟩
    · obtain ⟨C,hC,hpC⟩ := hGc p hp
      exact ⟨C,Finset.mem_union_right _ hC,hpC⟩

lemma coveredBy_line_circle {S L C : Set ℝ²} (hS : S⊆L∪C)
    (hL : Collinear ℝ L) (hC : Cospherical C) : CoveredBy S 2 :=
  ((coveredBy_one (generalized_of_collinear hL)).union
    (coveredBy_one (generalized_of_cospherical hC))).mono hS

lemma blocked_extension {A : Finset ℝ²} (hA : NoFourGeneralized (A : Set ℝ²))
    {p : ℝ²} (hp : ¬ NoFourGeneralized (insert p (A : Set ℝ²))) :
    ∃ a∈A, ∃ b∈A, ∃ c∈A, p∈through a b c := by
  classical
  unfold NoFourGeneralized at hp
  push_neg at hp
  obtain ⟨Q,hQ,hcard,hgen⟩ := hp
  have hpQ : p∈Q := by
    by_contra h
    exact hA Q (fun x hx => (hQ hx).resolve_left (fun he => h (he ▸ hx))) hcard hgen
  have hc3 : (Q \ {p}).ncard=3 := by rw [Set.ncard_diff_singleton_of_mem hpQ,hcard]
  obtain ⟨a,b,c,hab,hac,hbc,he⟩ := Set.ncard_eq_three.mp hc3
  have ha : a∈Q \ {p} := by rw [he]; simp
  have hb : b∈Q \ {p} := by rw [he]; simp
  have hc : c∈Q \ {p} := by rw [he]; simp
  have hm : ∀ x∈Q \ {p}, x∈A := by
    intro x hx
    exact (hQ hx.1).resolve_left (fun h => hx.2 (by simpa using h))
  exact ⟨a,hm a ha,b,hm b hb,c,hm c hc,
    generalized_subset_through hgen ha.1 hb.1 hc.1 hab hac hbc hpQ⟩

/-- Every finite set has a weak-general-position subset A whose singletons
and three-anchor generalized circles cover the original set. The deliberately
simple bound A.card + A.card^3 counts ordered triples. -/
theorem maximal_weak_cover (S : Finset ℝ²) :
    ∃ A ⊆ S, NoFourGeneralized (A : Set ℝ²) ∧
      CoveredBy (S : Set ℝ²) (A.card+A.card^3) := by
  classical
  let candidates : Finset (Finset ℝ²) :=
    S.powerset.filter (fun A : Finset ℝ² => NoFourGeneralized (A : Set ℝ²))
  have hne : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro Q hQ hn hg
    have he : Q=∅ := Set.subset_empty_iff.mp (by simpa using hQ)
    simp [he] at hn
  obtain ⟨A,hAc,hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hAS : A⊆S := Finset.mem_powerset.mp (Finset.mem_filter.mp hAc).1
  have hA : NoFourGeneralized (A : Set ℝ²) := (Finset.mem_filter.mp hAc).2
  let singles : Finset (Set ℝ²) := A.image (fun p => {p})
  let triples : Finset (Set ℝ²) := (A ×ˢ (A ×ˢ A)).image
    (fun abc => through abc.1 abc.2.1 abc.2.2)
  refine ⟨A,hAS,hA,singles∪triples,?_,?_,?_⟩
  · calc
      (singles∪triples).card ≤ singles.card+triples.card := Finset.card_union_le _ _
      _ ≤ A.card+(A ×ˢ (A ×ˢ A)).card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = A.card+A.card^3 := by rw [Finset.card_product,Finset.card_product]; ring
  · intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
      exact generalized_of_cospherical (cospherical_singleton p)
    · obtain ⟨abc,habc,rfl⟩ := Finset.mem_image.mp hC
      exact through_generalized _ _ _
  · intro p hp
    by_cases hpA : p∈A
    · exact ⟨{p},Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hpA,rfl⟩),by simp⟩
    · have hnot : ¬NoFourGeneralized (insert p (A : Set ℝ²)) := by
        intro h
        have hc : insert p A ∈ candidates := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hp hAS), ?_⟩
          simpa only [Finset.coe_insert] using h
        have hm := hmax _ hc
        rw [Finset.card_insert_of_notMem hpA] at hm
        omega
      obtain ⟨a,ha,b,hb,c,hc,hpC⟩ := blocked_extension hA hnot
      refine ⟨through a b c,Finset.mem_union_right _ ?_,hpC⟩
      exact Finset.mem_image.mpr ⟨(a,b,c),Finset.mem_product.mpr
        ⟨ha,Finset.mem_product.mpr ⟨hb,hc⟩⟩,rfl⟩

/-- A weak-general-position set contributes at most three points to each
member of a generalized-circle cover. -/
theorem weak_card_le_three_mul_cover {S : Finset ℝ²}
    (hS : NoFourGeneralized (S : Set ℝ²)) {k : ℕ}
    (hcover : CoveredBy (S : Set ℝ²) k) : S.card≤3*k := by
  classical
  obtain ⟨F,hF,hgen,hcover⟩ := hcover
  let part := fun C : Set ℝ² => S.filter (fun p => p∈C)
  have hpart : ∀ C∈F, (part C).card≤3 := by
    intro C hC
    by_contra! h
    have h4 : 4≤((part C : Finset ℝ²) : Set ℝ²).ncard := by
      rw [Set.ncard_coe_finset]
      omega
    obtain ⟨Q,hQ,hcard⟩ := Set.exists_subset_card_eq h4
    apply hS Q (fun p hp => (Finset.mem_filter.mp (hQ hp)).1) hcard
    exact generalized_mono (hgen C hC) (fun p hp => (Finset.mem_filter.mp (hQ hp)).2)
  have hsub : S⊆F.biUnion part := by
    intro p hp
    obtain ⟨C,hC,hpC⟩ := hcover p hp
    exact Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_filter.mpr ⟨hp,hpC⟩⟩
  calc
    S.card ≤ (F.biUnion part).card := Finset.card_le_card hsub
    _ ≤ ∑ C∈F, (part C).card := Finset.card_biUnion_le
    _ ≤ ∑ C∈F, 3 := Finset.sum_le_sum hpart
    _ = 3*F.card := by simp [Nat.mul_comm]
    _ ≤ 3*k := Nat.mul_le_mul_left _ hF

/-- Failure of a bounded cover gives a large weak-general-position subset.
This step makes no assumptions about distances. -/
theorem extract_weak_of_not_covered {S : Finset ℝ²} {n : ℕ}
    (h : ¬CoveredBy (S : Set ℝ²) (n+n^3)) :
    ∃ T : Set ℝ², T⊆(S : Set ℝ²) ∧ T.ncard=n+1 ∧ NoFourGeneralized T := by
  obtain ⟨A,hAS,hA,hcover⟩ := maximal_weak_cover S
  have hc : n+1≤A.card := by
    by_contra! hn
    have hn' : A.card≤n := by omega
    obtain ⟨F,hF,hgen,hcov⟩ := hcover
    exact h ⟨F,hF.trans (Nat.add_le_add hn' (Nat.pow_le_pow_left hn' 3)),hgen,hcov⟩
  obtain ⟨T,hTA,hcard⟩ := Set.exists_subset_card_eq
    (show n+1≤(A : Set ℝ²).ncard by simpa using hc)
  refine ⟨T,hTA.trans hAS,hcard,?_⟩
  intro Q hQT hQcard
  exact hA Q (hQT.trans hTA) hQcard

/-- Rational distances suffice: after extracting the weak subset, inversion
and a common positive scaling supply the integral configuration. -/
theorem erdos213For_of_not_covered_rational {S : Set ℝ²} (hfin : S.Finite)
    (hrat : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)))
    {n : ℕ} (h : ¬CoveredBy S (n+n^3)) : Erdos213For n := by
  have hc : ¬CoveredBy (hfin.toFinset : Set ℝ²) (n+n^3) := by simpa using h
  obtain ⟨T,hTS,hcard,hT⟩ := extract_weak_of_not_covered hc
  have hTS' : T⊆S := by simpa using hTS
  exact weak_to_strong ⟨T,hfin.subset hTS',hcard,hT,hrat.mono hTS'⟩

/-- A sufficient condition for n general-position integral-distance points,
allowing the input set to be arbitrarily degenerate. The missing arithmetic
problem is to construct input sets with the indicated covering complexity. -/
theorem erdos213For_of_not_covered {S : Set ℝ²} (hfin : S.Finite)
    (hint : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)))
    {n : ℕ} (h : ¬CoveredBy S (n+n^3)) : Erdos213For n := by
  have hc : ¬CoveredBy (hfin.toFinset : Set ℝ²) (n+n^3) := by simpa using h
  obtain ⟨T,hTS,hcard,hT⟩ := extract_weak_of_not_covered hc
  have hTS' : T⊆S := by simpa using hTS
  apply weak_to_strong
  refine ⟨T,hfin.subset hTS',hcard,hT,?_⟩
  intro p hp q hq hpq
  obtain ⟨z,hz⟩ := hint (hTS' hp) (hTS' hq) hpq
  exact ⟨(z : ℚ),by simpa using hz⟩

/-- An equivalent unrestricted existence question. It does not assert that
integral-distance sets of unbounded generalized-circle covering number exist. -/
theorem conjecture_iff_unbounded_covers :
    (∀ n : ℕ, n≥4 → Erdos213For n) ↔
    ∀ k : ℕ, ∃ S : Set ℝ², S.Finite ∧
      S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      ¬CoveredBy S k := by
  constructor
  · intro h k
    obtain ⟨S,hfin,hcard,htri,hcircle,hint⟩ := h (3*k+4) (by omega)
    refine ⟨S,hfin,hint,?_⟩
    intro hcover
    have hweak : NoFourGeneralized S :=
      noFour_of_general_position ⟨htri,fun Q hQ hn => hcircle Q ⟨hQ,hn⟩⟩
    have hb := weak_card_le_three_mul_cover
      (S := hfin.toFinset) (by simpa using hweak) (by simpa using hcover)
    have hcard' : hfin.toFinset.card=3*k+4 := by
      rw [← Set.ncard_eq_toFinset_card S hfin]
      exact hcard
    omega
  · intro h n hn
    obtain ⟨S,hfin,hint,hcover⟩ := h (n+n^3)
    exact erdos213For_of_not_covered hfin hint hcover

theorem conjecture_iff_unbounded_rational_covers :
    (∀ n : ℕ, n≥4 → Erdos213For n) ↔
    ∀ k : ℕ, ∃ S : Set ℝ², S.Finite ∧
      S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) ∧
      ¬CoveredBy S k := by
  constructor
  · intro h k
    obtain ⟨S,hfin,hint,hcov⟩ := conjecture_iff_unbounded_covers.mp h k
    refine ⟨S,hfin,?_,hcov⟩
    intro p hp q hq hpq
    obtain ⟨z,hz⟩ := hint hp hq hpq
    exact ⟨(z : ℚ),by simpa using hz⟩
  · intro h n hn
    obtain ⟨S,hfin,hrat,hcover⟩ := h (n+n^3)
    exact erdos213For_of_not_covered_rational hfin hrat hcover

#print axioms coveredBy_line_circle
#print axioms circleEval_generalized
#print axioms generalized_subset_through
#print axioms blocked_extension
#print axioms maximal_weak_cover
#print axioms weak_card_le_three_mul_cover
#print axioms extract_weak_of_not_covered
#print axioms erdos213For_of_not_covered
#print axioms conjecture_iff_unbounded_covers
#print axioms conjecture_iff_unbounded_rational_covers
end
end Erdos213.CircleCoverReduction
