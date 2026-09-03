import Submission.FullProgress

/-! An unrestricted inversion reduction. Existence of the input configurations
is not asserted: allowing collinear triples costs one point under inversion. -/
open EuclideanGeometry
namespace Erdos213.InversionReduction
set_option maxHeartbeats 2000000

noncomputable def radiusSq (p : ℝ²) : ℝ := (p 0)^2+(p 1)^2

def OnGeneralizedCircle (S : Set ℝ²) : Prop :=
  ∃ a b c d : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
    ∀ p ∈ S, a*radiusSq p+b*p 0+c*p 1+d=0

def NoFourGeneralized (S : Set ℝ²) : Prop :=
  ∀ Q : Set ℝ², Q ⊆ S → Q.ncard=4 → ¬ OnGeneralizedCircle Q

lemma distance_sq (p q : ℝ²) :
    dist p q^2=(p 0-q 0)^2+(p 1-q 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

lemma radiusSq_eq (p : ℝ²) : radiusSq p=dist p 0^2 := by
  rw [distance_sq]
  simp [radiusSq]

lemma line_equation {S : Set ℝ²} (h : Collinear ℝ S) :
    ∃ b c d : ℝ, (b ≠ 0 ∨ c ≠ 0) ∧ ∀ p ∈ S, b*p 0+c*p 1+d=0 := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨o,v,hv⟩ := h
  by_cases hv₀ : v 0=0
  · refine ⟨1,0,-o 0,Or.inl (by norm_num),?_⟩
    intro p hp
    obtain ⟨t,rfl⟩ := hv p hp
    simp [hv₀]
  · refine ⟨-v 1,v 0,v 1*o 0-v 0*o 1,Or.inr hv₀,?_⟩
    intro p hp
    obtain ⟨t,rfl⟩ := hv p hp
    simp
    ring

lemma generalized_of_collinear {S : Set ℝ²} (h : Collinear ℝ S) :
    OnGeneralizedCircle S := by
  obtain ⟨b,c,d,hbc,hp⟩ := line_equation h
  exact ⟨0,b,c,d,Or.inr hbc,by simpa using hp⟩

lemma generalized_of_cospherical {S : Set ℝ²} (h : Cospherical S) :
    OnGeneralizedCircle S := by
  obtain ⟨o,r,ho⟩ := h
  refine ⟨1,-2*o 0,-2*o 1,(o 0)^2+(o 1)^2-r^2,Or.inl (by norm_num),?_⟩
  intro p hp
  have hh := congrArg (fun z : ℝ => z^2) (ho p hp)
  dsimp only at hh
  rw [distance_sq] at hh
  dsimp [radiusSq]
  nlinarith only [hh]

lemma generalized_circle_or_line {S : Set ℝ²} (hS : S.Nonempty)
    (h : OnGeneralizedCircle S) : Collinear ℝ S ∨ Cospherical S := by
  obtain ⟨a,b,c,d,habc,hp⟩ := h
  by_cases ha : a=0
  · subst a
    simp only [ne_eq,not_true_eq_false,false_or] at habc
    left
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    by_cases hb : b=0
    · have hc : c≠0 := habc.resolve_left (by simpa using hb)
      refine ⟨!₂[0,-d/c],!₂[1,0],?_⟩
      intro p hps
      refine ⟨p 0,?_⟩
      have hh := hp p hps
      rw [hb] at hh
      ext i
      fin_cases i
      · simp
      · simp
        field_simp
        nlinarith only [hh]
    · refine ⟨!₂[-d/b,0],!₂[-c/b,1],?_⟩
      intro p hps
      refine ⟨p 1,?_⟩
      have hh := hp p hps
      ext i
      fin_cases i
      · simp
        field_simp
        nlinarith only [hh]
      · simp
  · right
    obtain ⟨p₀,hp₀⟩ := hS
    let o : ℝ² := !₂[-b/(2*a),-c/(2*a)]
    refine ⟨o,dist p₀ o,?_⟩
    intro p hps
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [distance_sq,distance_sq]
    have h₁ := hp p hps
    have h₀ := hp p₀ hp₀
    simp only [o,Matrix.cons_val_zero,Matrix.cons_val_one]
    dsimp [radiusSq] at h₁ h₀
    field_simp
    linear_combination 4*a*(h₁-h₀)

lemma generalized_mono {S T : Set ℝ²} (h : OnGeneralizedCircle T) (hST : S ⊆ T) :
    OnGeneralizedCircle S := by
  obtain ⟨a,b,c,d,hn,hp⟩ := h
  exact ⟨a,b,c,d,hn,fun p hpS => hp p (hST hpS)⟩

lemma noFour_of_general_position {S : Set ℝ²} (h : InGeneralPosition S) :
    NoFourGeneralized S := by
  intro Q hQ hn hgen
  have hQne : Q.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  rcases generalized_circle_or_line hQne hgen with hline | hcircle
  · obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hn
    subst Q
    exact h.1 (hQ (by simp)) (hQ (by simp)) (hQ (by simp)) hab hbc hac
      (hline.subset (by intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp ⊢; tauto))
  · exact h.2 Q hQ hn hcircle


lemma generalized_translation (v : ℝ²) {S : Set ℝ²}
    (h : OnGeneralizedCircle ((fun p : ℝ² => p-v) '' S)) :
    OnGeneralizedCircle S := by
  obtain ⟨a,b,c,d,hn,hp⟩ := h
  refine ⟨a,b-2*a*v 0,c-2*a*v 1,
    d+a*radiusSq v-b*v 0-c*v 1,?_,?_⟩
  · by_cases ha : a=0
    · simpa [ha] using hn
    · exact Or.inl ha
  · intro p hps
    have hh := hp (p-v) (Set.mem_image_of_mem _ hps)
    simp only [radiusSq,PiLp.sub_apply] at hh ⊢
    linear_combination hh

lemma noFour_translation (v : ℝ²) {S : Set ℝ²} (h : NoFourGeneralized S) :
    NoFourGeneralized ((fun p : ℝ² => p-v) '' S) := by
  let f : ℝ² → ℝ² := fun p => p-v
  have hi : Function.Injective f := by
    intro p q hh
    exact sub_left_inj.mp hh
  have hs : Function.Surjective f := fun p => ⟨p+v,by simp [f]⟩
  intro Q hQ hn hgen
  have hr : Q ⊆ Set.range f := by rw [hs.range_eq]; exact Set.subset_univ Q
  have he : f '' (f ⁻¹' Q) = Q := Set.image_preimage_eq_iff.mpr hr
  apply h (f ⁻¹' Q) ?_ ((Set.ncard_preimage_of_injective_subset_range hi hr).trans hn)
  · apply generalized_translation v
    change OnGeneralizedCircle (f '' (f ⁻¹' Q))
    rwa [he]
  · intro p hp
    obtain ⟨q,hq,hqp⟩ := hQ hp
    exact hi hqp ▸ hq

noncomputable def invert (p : ℝ²) : ℝ² := (radiusSq p)⁻¹ • p

lemma invert_apply (p : ℝ²) (i : Fin 2) : invert p i=p i/radiusSq p := by
  simp [invert,div_eq_mul_inv,mul_comm]

lemma radiusSq_ne_zero {p : ℝ²} (hp : p ≠ 0) : radiusSq p ≠ 0 := by
  rw [radiusSq_eq]
  exact pow_ne_zero 2 (dist_ne_zero.mpr hp)

lemma radiusSq_invert {p : ℝ²} (hp : p ≠ 0) :
    radiusSq (invert p) = 1/radiusSq p := by
  have hn := radiusSq_ne_zero hp
  unfold radiusSq
  rw [invert_apply,invert_apply,div_pow,div_pow,← add_div]
  change radiusSq p/(radiusSq p)^2=1/radiusSq p
  field_simp

lemma invert_eq_inversion (p : ℝ²) : invert p=inversion (0 : ℝ²) 1 p := by
  ext i
  simp [invert,EuclideanGeometry.inversion,radiusSq_eq]

lemma invert_injective : Function.Injective invert := by
  intro p q h
  apply inversion_injective (0 : ℝ²) (R := 1) (by norm_num)
  simpa only [← invert_eq_inversion] using h

lemma invert_involutive (p : ℝ²) : invert (invert p)=p := by
  simp only [invert_eq_inversion,inversion_inversion _ (by norm_num : (1 : ℝ)≠0)]

lemma invert_nonzero {p : ℝ²} (hp : p≠0) : invert p≠0 := by
  simpa [invert_eq_inversion] using hp

lemma inverse_equation {p : ℝ²} (hp : p≠0) (a b c d : ℝ) :
    (a*radiusSq (invert p)+b*(invert p) 0+c*(invert p) 1+d)*radiusSq p =
      d*radiusSq p+b*p 0+c*p 1+a := by
  rw [radiusSq_invert hp,invert_apply,invert_apply]
  have hn := radiusSq_ne_zero hp
  field_simp
  ring

lemma generalized_invert {S : Set ℝ²} (hS : S.Nonempty) (hzero : 0 ∉ S)
    (h : OnGeneralizedCircle (invert '' S)) : OnGeneralizedCircle S := by
  obtain ⟨a,b,c,d,hn,hp⟩ := h
  have hh (p : ℝ²) (hps : p ∈ S) : d*radiusSq p+b*p 0+c*p 1+a=0 := by
    have hz : p≠0 := fun he => hzero (he ▸ hps)
    rw [← inverse_equation hz, hp (invert p) (Set.mem_image_of_mem _ hps),zero_mul]
  refine ⟨d,b,c,a,?_,hh⟩
  by_contra hbad
  push_neg at hbad
  obtain ⟨p,hps⟩ := hS
  have ha : a=0 := by simpa [hbad.1,hbad.2.1,hbad.2.2] using hh p hps
  rcases hn with hn | hn | hn
  · exact hn ha
  · exact hn hbad.2.1
  · exact hn hbad.2.2

lemma line_invert_insert {S : Set ℝ²} (hzero : 0 ∉ S)
    (h : Collinear ℝ (invert '' S)) : OnGeneralizedCircle (insert 0 S) := by
  obtain ⟨b,c,d,hn,hp⟩ := line_equation h
  refine ⟨d,b,c,0,Or.inr hn,?_⟩
  intro p hps
  rcases hps with rfl | hps
  · simp [radiusSq]
  · have hz : p≠0 := fun he => hzero (he ▸ hps)
    have hh := hp (invert p) (Set.mem_image_of_mem _ hps)
    have he := inverse_equation hz 0 b c d
    simp only [zero_mul,zero_add,hh] at he
    simpa using he.symm


lemma inversion_general_position {S : Set ℝ²} (h₀ : (0 : ℝ²) ∈ S)
    (h : NoFourGeneralized S) :
    InGeneralPosition (invert '' (S \ {0})) := by
  constructor
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ _ ⟨r,hr,rfl⟩ hpq hqr hpr hcol
    have hp₀ : p≠0 := by simpa using hp.2
    have hq₀ : q≠0 := by simpa using hq.2
    have hr₀ : r≠0 := by simpa using hr.2
    have hpq' : p≠q := fun he => hpq (congrArg invert he)
    have hqr' : q≠r := fun he => hqr (congrArg invert he)
    have hpr' : p≠r := fun he => hpr (congrArg invert he)
    apply h {0,p,q,r} ?_ ?_
    · apply line_invert_insert
      · simp [Ne.symm hp₀,Ne.symm hq₀,Ne.symm hr₀]
      · simpa only [Set.image_insert_eq,Set.image_singleton] using hcol
    · intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact h₀
      · exact hp.1
      · exact hq.1
      · exact hr.1
    · exact Set.ncard_eq_four.mpr ⟨0,p,q,r,Ne.symm hp₀,Ne.symm hq₀,Ne.symm hr₀,
        hpq',hpr',hqr',rfl⟩
  · intro Q hQ hn hcos
    have hrange : Q ⊆ Set.range invert := by
      intro p hp
      exact ⟨invert p,(invert_involutive p)⟩
    have he : invert '' (invert ⁻¹' Q) = Q := Set.image_preimage_eq_iff.mpr hrange
    have hsub : invert ⁻¹' Q ⊆ S \ {0} := by
      intro p hp
      obtain ⟨q,hq,hqp⟩ := hQ hp
      exact invert_injective hqp ▸ hq
    have hcard : (invert ⁻¹' Q).ncard=4 :=
      (Set.ncard_preimage_of_injective_subset_range invert_injective hrange).trans hn
    apply h (invert ⁻¹' Q) (hsub.trans Set.diff_subset) hcard
    apply generalized_invert (Set.nonempty_of_ncard_ne_zero (by omega))
      (fun hz => (hsub hz).2 (by simp))
    rw [he]
    exact generalized_of_cospherical hcos

lemma inversion_rational_distances {S : Set ℝ²} (h₀ : (0 : ℝ²) ∈ S)
    (h : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ))) :
    (invert '' (S \ {0})).Pairwise
      (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
  have hp₀ : p≠0 := by simpa using hp.2
  have hq₀ : q≠0 := by simpa using hq.2
  have hpq' : p≠q := fun he => hpq (congrArg invert he)
  obtain ⟨a,ha⟩ := h hp.1 h₀ hp₀
  obtain ⟨b,hb⟩ := h hq.1 h₀ hq₀
  obtain ⟨c,hc⟩ := h hp.1 hq.1 hpq'
  refine ⟨c/(a*b),?_⟩
  rw [invert_eq_inversion,invert_eq_inversion,dist_inversion_inversion hp₀ hq₀]
  push_cast
  rw [ha,hb,hc]
  ring

def WeakRational (n : ℕ) : Prop :=
  ∃ S : Set ℝ², S.Finite ∧ S.ncard=n ∧ NoFourGeneralized S ∧
    S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ))

lemma weak_to_strong {n : ℕ} (h : WeakRational (n+1)) : Erdos213For n := by
  obtain ⟨S,hfin,hcard,hfour,hrat⟩ := h
  obtain ⟨a,ha⟩ : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  let T : Set ℝ² := (fun p : ℝ² => p-a) '' S
  have hinj : Function.Injective (fun p : ℝ² => p-a) := by
    intro p q hh
    exact sub_left_inj.mp hh
  have hTfin : T.Finite := hfin.image _
  have hTcard : T.ncard=n+1 := (Set.ncard_image_of_injective S hinj).trans hcard
  have hT₀ : (0 : ℝ²) ∈ T := ⟨a,ha,by simp⟩
  have hTfour : NoFourGeneralized T := noFour_translation a hfour
  have hTrat : T.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) := by
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
    have hd : dist (p-a) (q-a) = dist p q := by
      rw [dist_eq_norm,dist_eq_norm]
      congr 1
      abel
    rw [hd]
    exact hrat hp hq (fun he => hpq (he ▸ rfl))
  apply (erdos213For_iff_rational n).mpr
  refine ⟨invert '' (T \ {0}),hTfin.diff.image _,?_,
    inversion_general_position hT₀ hTfour,inversion_rational_distances hT₀ hTrat⟩
  rw [Set.ncard_image_of_injective _ invert_injective,
    Set.ncard_diff_singleton_of_mem hT₀,hTcard]
  omega

lemma strong_to_weak {n : ℕ} (h : Erdos213For n) : WeakRational n := by
  obtain ⟨S,hfin,hcard,hgen,hrat⟩ := (erdos213For_iff_rational n).mp h
  exact ⟨S,hfin,hcard,noFour_of_general_position hgen,hrat⟩

/-- An equivalent unrestricted existence problem, not an existence proof. -/
theorem conjecture_iff_weak :
    (∀ n : ℕ, n ≥ 4 → Erdos213For n) ↔
    (∀ n : ℕ, n ≥ 4 → WeakRational n) := by
  constructor
  · intro h n hn
    exact strong_to_weak (h n hn)
  · intro h n hn
    exact weak_to_strong (h (n+1) (by omega))

lemma noFour_iff {S : Set ℝ²} : NoFourGeneralized S ↔
    ∀ Q : Set ℝ², Q ⊆ S → Q.ncard=4 →
      ¬ Collinear ℝ Q ∧ ¬ Cospherical Q := by
  constructor
  · intro h Q hQ hn
    exact ⟨fun hline => h Q hQ hn (generalized_of_collinear hline),
      fun hcircle => h Q hQ hn (generalized_of_cospherical hcircle)⟩
  · intro h Q hQ hn hgen
    rcases generalized_circle_or_line
      (Set.nonempty_of_ncard_ne_zero (by omega)) hgen with hline | hcircle
    · exact (h Q hQ hn).1 hline
    · exact (h Q hQ hn).2 hcircle

theorem integral_input {n : ℕ} {S : Set ℝ²} (hfin : S.Finite)
    (hcard : S.ncard=n+1)
    (hfour : ∀ Q : Set ℝ², Q ⊆ S → Q.ncard=4 →
      ¬ Collinear ℝ Q ∧ ¬ Cospherical Q)
    (hint : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ))) :
    Erdos213For n := by
  apply weak_to_strong
  refine ⟨S,hfin,hcard,noFour_iff.mpr hfour,?_⟩
  intro p hp q hq hpq
  obtain ⟨z,hz⟩ := hint hp hq hpq
  exact ⟨(z : ℚ),by simpa using hz⟩

theorem conjecture_iff_weak_geometric :
    (∀ n : ℕ, n ≥ 4 → Erdos213For n) ↔
    (∀ n : ℕ, n ≥ 4 → ∃ S : Set ℝ², S.Finite ∧ S.ncard=n ∧
      (∀ Q : Set ℝ², Q ⊆ S → Q.ncard=4 →
        ¬ Collinear ℝ Q ∧ ¬ Cospherical Q) ∧
      S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ))) := by
  simpa only [WeakRational,noFour_iff] using conjecture_iff_weak

#print axioms generalized_circle_or_line
#print axioms inversion_general_position
#print axioms inversion_rational_distances
#print axioms weak_to_strong
#print axioms integral_input
#print axioms conjecture_iff_weak_geometric
#print axioms conjecture_iff_weak
end Erdos213.InversionReduction
