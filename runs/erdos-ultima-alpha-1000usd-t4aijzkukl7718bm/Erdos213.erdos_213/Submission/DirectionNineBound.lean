import Submission.DirectionInvolutionArithmetic

/-! A lower bound for norm-preserving completions of the old six directions,
without assuming that the involution is fixed-point-free. This is an auxiliary
construction restriction, not a bound on arbitrary rational-distance sets. -/
namespace Erdos213.DirectionInvolutions
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma no_rectangular_pair {u v w z : ℚ} (hu : u≠0) (hv : v≠0)
    (h₁ : u^2+v^2=w^2) (h₄ : u^2+4*v^2=z^2) : False := by
  apply OrthogonalGlobal.no_simultaneous_squares (div_ne_zero hu hv)
  constructor
  · refine ⟨w/v,?_⟩
    field_simp
    nlinarith only [h₁]
  · refine ⟨z/v,?_⟩
    field_simp
    nlinarith only [h₄]

lemma old_norm_more_exclusions {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    r≠ -x ∧ r≠2-x ∧ 2*r≠x+1 ∧ 2*r+5*x+2≠0 := by
  obtain ⟨a,ha⟩ := hsq 1
  obtain ⟨b,hb⟩ := hsq 2
  obtain ⟨c,hc⟩ := hsq 3
  obtain ⟨d,hd⟩ := hsq 4
  obtain ⟨e,he⟩ := hsq 5
  change (0 : ℚ)^2-2*x*0*1+r*1^2=a*a at ha
  change (-1 : ℚ)^2-2*x*(-1)*1+r*1^2=b*b at hb
  change (1 : ℚ)^2-2*x*1*1+r*1^2=c*c at hc
  change (-1 : ℚ)^2-2*x*(-1)*2+r*2^2=d*d at hd
  change (-2 : ℚ)^2-2*x*(-2)*1+r*1^2=e*e at he
  norm_num at ha hb hc hd he
  refine ⟨?_,?_,?_,?_⟩
  · intro hp
    have ha0 : a≠0 := by intro hz; nlinarith only [hr,ha,hp,hz,sq_nonneg x]
    have hb0 : b≠0 := by intro hz; nlinarith only [hr,hb,hp,hz,sq_nonneg (x+1)]
    exact no_rectangular_pair (w := 1) (z := c) hb0 ha0
      (by nlinarith only [ha,hb,hp]) (by nlinarith only [ha,hb,hc,hp])
  · intro hp
    have hc0 : c≠0 := by intro hz; nlinarith only [hr,hc,hp,hz,sq_nonneg (x-1)]
    have he0 : e≠0 := by intro hz; nlinarith only [hr,he,hp,hz,sq_nonneg (x+2)]
    exact no_rectangular_pair (w := 3) (z := 3*a) he0 hc0
      (by nlinarith only [he,hc,hp]) (by nlinarith only [ha,he,hc,hp])
  · intro hp
    have hc0 : c≠0 := by intro hz; nlinarith only [hr,hc,hp,hz,sq_nonneg (x-1)]
    have hd0 : d≠0 := by intro hz; nlinarith only [hr,hd,hp,hz,sq_nonneg (2*x+1)]
    exact no_rectangular_pair (w := 3*a) (z := 3) hd0 hc0
      (by nlinarith only [ha,hd,hc,hp]) (by nlinarith only [hd,hc,hp])
  · intro hp
    have hd0 : d≠0 := by intro hz; nlinarith only [hr,hd,hp,hz,sq_nonneg (2*x+1)]
    have he0 : e≠0 := by intro hz; nlinarith only [hr,he,hp,hz,sq_nonneg (x+2)]
    exact no_rectangular_pair (w := 3*b) (z := 3) hd0 he0
      (by nlinarith only [hb,hd,he,hp]) (by nlinarith only [hd,he,hp])

def twoFixed (i j : Fin 6) : Coeff :=
  cross (pairRow (oldRoot i) (oldRoot i)) (pairRow (oldRoot j) (oldRoot j))

def smallMatrix : Fin 9 → Coeff :=
  ![⟨1,1,0⟩,⟨0,1,1⟩,⟨1,0,-1⟩,⟨1,2,0⟩,⟨1,0,0⟩,
    ⟨1,0,-2⟩,⟨1,-4,-2⟩,⟨1,2,4⟩,⟨5,4,-4⟩]

def coeffProjection (v w : Coeff) : ℚ := dot v w / dot w w

lemma fixed_pair_nondegenerate : ∀ i j : Fin 6, i≠j → twoFixed i j≠zeroCoeff := by
  decide +kernel

lemma fixed_three_nondegenerate : ∀ i j k : Fin 6, i≠j → i≠k → j≠k →
    dot (pairRow (oldRoot k) (oldRoot k)) (twoFixed i j)≠0 := by
  decide +kernel

lemma fixed_two_pair_certificate : ∀ i j k l : Fin 6,
    i≠j → i≠k → i≠l → j≠k → j≠l → k≠l →
    pair (twoFixed i j) (oldRoot k) (oldRoot l)=0 →
      ∃ q : Fin 9, twoFixed i j=
        scale (coeffProjection (twoFixed i j) (smallMatrix q)) (smallMatrix q) := by
  decide +kernel

lemma scale_scale (s t : ℚ) (m : Coeff) : scale s (scale t m)=scale (s*t) m := by
  apply Coeff.ext <;> dsimp [scale] <;> ring

lemma dot_scale_right (a b : Coeff) (s : ℚ) : dot a (scale s b)=s*dot a b := by
  dsimp [dot,scale]; ring

lemma scale_nonzero {m v : Coeff} {s : ℚ} (hm : multiplier m≠0)
    (h : m=scale s v) : s≠0 := by
  intro hs
  apply hm
  rw [h,multiplier_scale,hs]
  ring

lemma no_three_old_fixed (m : Coeff) (hm : multiplier m≠0)
    (i j k : Fin 6) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hi : pair m (oldRoot i) (oldRoot i)=0)
    (hj : pair m (oldRoot j) (oldRoot j)=0)
    (hk : pair m (oldRoot k) (oldRoot k)=0) : False := by
  rw [pair_eq_dot] at hi hj hk
  obtain ⟨s,hs⟩ := proportional_of_two_rows _ _ m hi hj (fixed_pair_nondegenerate i j hij)
  change m=scale s (twoFixed i j) at hs
  have hs0 := scale_nonzero hm hs
  rw [hs,dot_scale_right] at hk
  exact (mul_ne_zero hs0 (fixed_three_nondegenerate i j k hij hik hjk)) hk

lemma smallMatrix_not_invariant {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) (q : Fin 9)
    (hp : (smallMatrix q).c*r-2*(smallMatrix q).a*x-(smallMatrix q).b=0) : False := by
  obtain ⟨h₁,h₂,h₃⟩ := old_norm_excludes_symmetry hr hsq
  obtain ⟨h₄,h₅,_⟩ := old_norm_excludes_midpoints hr hsq
  obtain ⟨h₆,h₇,h₈,h₉⟩ := old_norm_more_exclusions hr hsq
  fin_cases q
  · change (0 : ℚ)*r-2*1*x-1=0 at hp; apply h₁; linarith
  · change (1 : ℚ)*r-2*0*x-1=0 at hp; apply h₂; linarith
  · change (-1 : ℚ)*r-2*1*x-0=0 at hp; apply h₃; linarith
  · change (0 : ℚ)*r-2*1*x-2=0 at hp; apply h₅; linarith
  · change (0 : ℚ)*r-2*1*x-0=0 at hp; apply h₄; linarith
  · change (-2 : ℚ)*r-2*1*x-0=0 at hp; apply h₆; linarith
  · change (-2 : ℚ)*r-2*1*x-(-4)=0 at hp; apply h₇; linarith
  · change (4 : ℚ)*r-2*1*x-2=0 at hp; apply h₈; linarith
  · change (-4 : ℚ)*r-2*5*x-4=0 at hp; apply h₉; linarith

lemma norm_no_two_fixed_and_pair {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (m : Coeff) (hm : multiplier m≠0) (hphase : m.c*r-2*m.a*x-m.b=0)
    (i j k l : Fin 6) (hij : i≠j) (hik : i≠k) (hil : i≠l)
    (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
    (hi : pair m (oldRoot i) (oldRoot i)=0)
    (hj : pair m (oldRoot j) (oldRoot j)=0)
    (hkl' : pair m (oldRoot k) (oldRoot l)=0) : False := by
  rw [pair_eq_dot] at hi hj
  obtain ⟨s,hs⟩ := proportional_of_two_rows _ _ m hi hj (fixed_pair_nondegenerate i j hij)
  change m=scale s (twoFixed i j) at hs
  have hs0 := scale_nonzero hm hs
  have hp : pair (twoFixed i j) (oldRoot k) (oldRoot l)=0 := by
    rw [hs,pair_scale] at hkl'
    exact (mul_eq_zero.mp hkl').resolve_left hs0
  obtain ⟨q,hq⟩ := fixed_two_pair_certificate i j k l hij hik hil hjk hjl hkl hp
  have he : m=scale (s*coeffProjection (twoFixed i j) (smallMatrix q)) (smallMatrix q) := by
    calc
      m = scale s (twoFixed i j) := hs
      _ = scale s (scale (coeffProjection (twoFixed i j) (smallMatrix q)) (smallMatrix q)) :=
        congrArg (scale s) hq
      _ = _ := scale_scale _ _ _
  have hn := scale_nonzero hm he
  apply smallMatrix_not_invariant hr hsq q
  have hz : (s*coeffProjection (twoFixed i j) (smallMatrix q))*
      ((smallMatrix q).c*r-2*(smallMatrix q).a*x-(smallMatrix q).b)=0 := by
    rw [he] at hphase
    dsimp [scale] at hphase
    nlinarith only [hphase]
  exact (mul_eq_zero.mp hz).resolve_left hn

/-- Three elementary forbidden patterns bound the internal part of an
involution on a finite set. This lemma has no geometry or arithmetic. -/
lemma internal_card_le_three {ι : Type*} [DecidableEq ι]
    (f : ι → ι) (hf : Function.Involutive f) (A : Finset ι)
    (hfix3 : ∀ a∈A, ∀ b∈A, ∀ c∈A, a≠b → a≠c → b≠c →
      f a=a → f b=b → f c=c → False)
    (hpairs : ∀ a∈A, ∀ b∈A, ∀ c∈A, ∀ d∈A,
      a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → f a=b → f c=d → False)
    (hfixedpair : ∀ a∈A, ∀ b∈A, ∀ c∈A, ∀ d∈A,
      a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → f a=a → f b=b → f c=d → False) :
    (A∩A.image f).card≤3 := by
  classical
  let I := A∩A.image f
  by_contra hn
  change ¬ I.card≤3 at hn
  have hcI : 4≤I.card := by omega
  have partner (a : ι) (ha : a∈I) : a∈A ∧ f a∈A := by
    obtain ⟨ha,ha'⟩ := Finset.mem_inter.mp ha
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha'
    exact ⟨ha,by simpa [← hba,hf b] using hb⟩
  have hex : ∃ a∈I, f a≠a := by
    by_contra he
    push_neg at he
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<I.card by omega)
    obtain ⟨b,hb,hbn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({a} : Finset ι).card<I.card by simpa using (show 1<I.card by omega))
    have hba : b≠a := fun hh => hbn (by simp [hh])
    obtain ⟨c,hc,hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({a,b} : Finset ι).card<I.card from lt_of_le_of_lt Finset.card_le_two (by omega))
    have hca : c≠a := fun hh => hcn (by simp [hh])
    have hcb : c≠b := fun hh => hcn (by simp [hh])
    exact hfix3 a (partner a ha).1 b (partner b hb).1 c (partner c hc).1
      hba.symm hca.symm hcb.symm (he a ha) (he b hb) (he c hc)
  obtain ⟨a,ha,hfa⟩ := hex
  have fixed_else (c : ι) (hc : c∈I) (hca : c≠a) (hcf : c≠f a) : f c=c := by
    by_contra hfc
    have hafc : a≠f c := by
      intro hh
      have he := congrArg f hh
      rw [hf] at he
      exact hcf he.symm
    have hfac : f a≠f c := fun hh => hca (hf.injective hh).symm
    exact hpairs a (partner a ha).1 (f a) (partner a ha).2
      c (partner c hc).1 (f c) (partner c hc).2
      hfa.symm hca.symm hafc hcf.symm hfac (fun h => hfc h.symm) rfl rfl
  obtain ⟨c,hc,hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a,f a} : Finset ι).card<I.card from lt_of_le_of_lt Finset.card_le_two (by omega))
  have hca : c≠a := fun hh => hcn (by simp [hh])
  have hcf : c≠f a := fun hh => hcn (by simp [hh])
  have hsmall : ({a,f a,c} : Finset ι).card≤3 := by
    calc
      _ ≤ ({f a,c} : Finset ι).card+1 := Finset.card_insert_le _ _
      _ ≤ 2+1 := Nat.add_le_add_right Finset.card_le_two 1
      _ = _ := rfl
  obtain ⟨d,hd,hdn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a,f a,c} : Finset ι).card<I.card from lt_of_le_of_lt hsmall (by omega))
  have hda : d≠a := fun hh => hdn (by simp [hh])
  have hdf : d≠f a := fun hh => hdn (by simp [hh])
  have hdc : d≠c := fun hh => hdn (by simp [hh])
  exact hfixedpair c (partner c hc).1 d (partner d hd).1
    a (partner a ha).1 (f a) (partner a ha).2
    hdc.symm hca hcf hda hdf hfa.symm
    (fixed_else c hc hca hcf) (fixed_else d hd hda hdf) rfl

/-- Any faithful norm-preserving involution completion of the old six directions
has at least nine elements. Fixed directions are allowed. -/
theorem nine_le_card_of_norm_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x r : ℚ) (hr : x^2<r) (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (m : Coeff) (hm : multiplier m≠0) (hphase : m.c*r-2*m.a*x-m.b=0)
    (p : ι → Vec) (e : Fin 6 ↪ ι) (he : ∀ i, p (e i)=oldRoot i)
    (f : ι → ι) (hf : Function.Involutive f)
    (hact : ∀ i j, pair m (p i) (p j)=0 ↔ f i=j) :
    9≤Fintype.card ι := by
  classical
  let A : Finset ι := Finset.univ.image e
  have pairing (i j : Fin 6) (h : f (e i)=e j) : pair m (oldRoot i) (oldRoot j)=0 := by
    simpa only [he] using (hact (e i) (e j)).mpr h
  have hcI : (A∩A.image f).card≤3 := by
    apply internal_card_le_three f hf A
    · intro a ha b hb c hc hab hac hbc hfa hfb hfc
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hc
      exact no_three_old_fixed m hm i j k
        (fun h => hab (congrArg e h)) (fun h => hac (congrArg e h)) (fun h => hbc (congrArg e h))
        (pairing i i hfa) (pairing j j hfb) (pairing k k hfc)
    · intro a ha b hb c hc d hd hab hac had hbc hbd hcd hfab hfcd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hd
      exact norm_no_two_old_pairs hr hsq m hm hphase i j k l
        (fun h => hab (congrArg e h)) (fun h => hac (congrArg e h)) (fun h => had (congrArg e h))
        (fun h => hbc (congrArg e h)) (fun h => hbd (congrArg e h)) (fun h => hcd (congrArg e h))
        (pairing i j hfab) (pairing k l hfcd)
    · intro a ha b hb c hc d hd hab hac had hbc hbd hcd hfa hfb hfcd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hd
      exact norm_no_two_fixed_and_pair hr hsq m hm hphase i j k l
        (fun h => hab (congrArg e h)) (fun h => hac (congrArg e h)) (fun h => had (congrArg e h))
        (fun h => hbc (congrArg e h)) (fun h => hbd (congrArg e h)) (fun h => hcd (congrArg e h))
        (pairing i i hfa) (pairing j j hfb) (pairing k l hfcd)
  have hA : A.card=6 := by
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hB : (A.image f).card=6 := by rw [Finset.card_image_of_injective _ hf.injective,hA]
  have hU : (A∪A.image f).card≤Fintype.card ι := Finset.card_le_univ _
  have hh := Finset.card_union_add_card_inter A (A.image f)
  omega

#print axioms internal_card_le_three
#print axioms nine_le_card_of_norm_completion

#print axioms old_norm_more_exclusions
#print axioms fixed_two_pair_certificate
#print axioms no_three_old_fixed
#print axioms norm_no_two_fixed_and_pair
end Erdos213.DirectionInvolutions
