import Submission.CircleCoverReduction

/-! Iterating opposite-triangle circumcenters does not provide an
unbounded generalized-circle cover. This is a geometric restriction on one
operation, not a bound on arbitrary integral-distance configurations. -/
namespace Erdos213.CircumcenterOrbit
open EuclideanGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev V := ℝ × ℝ
def normSq (u : V) : ℝ := u.1^2+u.2^2
def dot (u v : V) : ℝ := u.1*v.1+u.2*v.2
def det (u v : V) : ℝ := u.1*v.2-u.2*v.1
def sqDist (a b : V) : ℝ := normSq (a-b)
def area (a b c : V) : ℝ := det (b-a) (c-a)
def center (a b c : V) : V := a+
  ((normSq (b-a)*(c-a).2-normSq (c-a)*(b-a).2)/(2*area a b c),
   (normSq (c-a)*(b-a).1-normSq (b-a)*(c-a).1)/(2*area a b c))
def opposite : Fin 4 → Fin 3 → Fin 4 := !![1,2,3;0,2,3;0,1,3;0,1,2]
def centers (p : Fin 4 → V) (i : Fin 4) : V :=
  center (p (opposite i 0)) (p (opposite i 1)) (p (opposite i 2))
def Noncollinear (p : Fin 4 → V) : Prop :=
  ∀ i, area (p (opposite i 0)) (p (opposite i 1)) (p (opposite i 2))≠0

def hom (a : V) (r : ℝ) (x : V) : V := a+r • x

def plane (p : V) : ℝ² := !₂[p.1,p.2]

lemma normSq_ne_zero {u : V} (hu : u≠0) : normSq u≠0 := by
  intro h
  have hx : u.1=0 := by dsimp [normSq] at h; nlinarith [sq_nonneg u.2]
  have hy : u.2=0 := by dsimp [normSq] at h; nlinarith [sq_nonneg u.1]
  exact hu (Prod.ext hx hy)

lemma center_incidence {a b c : V} (ha : area a b c≠0) :
    sqDist (center a b c) a=sqDist (center a b c) b ∧
    sqDist (center a b c) a=sqDist (center a b c) c := by
  constructor <;> dsimp [sqDist,normSq,center]
  all_goals field_simp
  all_goals dsimp [area,det,normSq]; ring

lemma centers_incidence {p : Fin 4 → V} (h : Noncollinear p)
    (i : Fin 4) (j k : Fin 3) :
    sqDist (centers p i) (p (opposite i j))=sqDist (centers p i) (p (opposite i k)) := by
  obtain ⟨h01,h02⟩ := center_incidence (h i)
  change sqDist (centers p i) (p (opposite i 0))=sqDist (centers p i) (p (opposite i 1)) at h01
  change sqDist (centers p i) (p (opposite i 0))=sqDist (centers p i) (p (opposite i 2)) at h02
  fin_cases j <;> fin_cases k <;> first | rfl | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h01.symm.trans h02 | exact h02.symm.trans h01

lemma opposite_mem : ∀ i j : Fin 4, j≠i → ∃ k : Fin 3, opposite i k=j := by decide
lemma shared_indices : ∀ i j : Fin 4, i≠j →
    ∃ k l : Fin 4, k≠l ∧ k≠i ∧ k≠j ∧ l≠i ∧ l≠j := by decide

lemma centers_incidence_of_ne {p : Fin 4 → V} (h : Noncollinear p)
    {i j k : Fin 4} (hj : j≠i) (hk : k≠i) :
    sqDist (centers p i) (p j)=sqDist (centers p i) (p k) := by
  obtain ⟨a,rfl⟩ := opposite_mem i j hj
  obtain ⟨b,rfl⟩ := opposite_mem i k hk
  exact centers_incidence h i a b

lemma noncollinear_injective {p : Fin 4 → V} (h : Noncollinear p) :
    Function.Injective p := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  change area (p 1) (p 2) (p 3)≠0 at h0
  change area (p 0) (p 2) (p 3)≠0 at h1
  change area (p 0) (p 1) (p 3)≠0 at h2
  change area (p 0) (p 1) (p 2)≠0 at h3
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl |
    (exfalso; apply h0)
  all_goals simp_all [area,det,mul_comm]

lemma shared_bisector_orthogonal {a b o z : V}
    (ho : sqDist o a=sqDist o b) (hz : sqDist z a=sqDist z b) :
    dot (z-o) (b-a)=0 := by
  dsimp [sqDist,normSq,dot] at *
  linear_combination (hz-ho)/2

lemma perpendicular_parallel {a b w : V} (hw : w≠0)
    (ha : dot a w=0) (hb : dot b w=0) : det a b=0 := by
  apply (mul_eq_zero.mp (show det a b*normSq w=0 from ?_)).resolve_right (normSq_ne_zero hw)
  dsimp [det,dot,normSq] at *
  linear_combination (a.1*w.2-a.2*w.1)*hb-(b.1*w.2-b.2*w.1)*ha

/-- Each twice-transformed edge is parallel to its corresponding original edge. -/
lemma twice_parallel {p : Fin 4 → V} (h : Noncollinear p)
    (hq : Noncollinear (centers p)) (i j : Fin 4) :
    det (centers (centers p) j-centers (centers p) i) (p j-p i)=0 := by
  by_cases hij : i=j
  · subst j; simp [det]
  obtain ⟨k,l,hkl,hki,hkj,hli,hlj⟩ := shared_indices i j hij
  have hw : centers p l-centers p k≠0 :=
    sub_ne_zero.mpr (fun hh => hkl (noncollinear_injective hq hh).symm)
  apply perpendicular_parallel hw
  · exact shared_bisector_orthogonal
      (centers_incidence_of_ne hq hki hli) (centers_incidence_of_ne hq hkj hlj)
  · have hh := shared_bisector_orthogonal
      (centers_incidence_of_ne h hki.symm hkj.symm)
      (centers_incidence_of_ne h hli.symm hlj.symm)
    simpa [dot,mul_comm] using hh

lemma two_parallel_scale (u v U W : V) (hD : det u v≠0)
    (hU : det U u=0) (hW : det W v=0) (hUW : det (W-U) (v-u)=0) :
    U=(det U v/det u v) • u ∧ W=(det U v/det u v) • v := by
  constructor <;> apply Prod.ext
  all_goals change _ = (det U v/det u v)*_
  all_goals field_simp
  all_goals dsimp [det] at *
  · linear_combination -v.1*hU
  · linear_combination -v.2*hU
  · linear_combination (u.1-v.1)*hW-v.1*hU+v.1*hUW
  · linear_combination (u.2-v.2)*hW-v.2*hU+v.2*hUW

lemma parallel_homothety {p q : Fin 4 → V} (h : Noncollinear p)
    (hpq : ∀ i j, det (q j-q i) (p j-p i)=0) :
    ∃ a r, q=hom a r ∘ p := by
  let u := p 1-p 0
  let v := p 2-p 0
  let w := p 3-p 0
  let U := q 1-q 0
  let W := q 2-q 0
  let Z := q 3-q 0
  have hD : det u v≠0 := h 3
  have hE : det u w≠0 := h 2
  have hu : u≠0 := by intro hz; apply hD; simp [hz,det]
  have hUW : det (W-U) (v-u)=0 := by
    simpa [U,W,u,v,sub_sub_sub_cancel_right] using hpq 1 2
  have hUZ : det (Z-U) (w-u)=0 := by
    simpa [U,Z,u,w,sub_sub_sub_cancel_right] using hpq 1 3
  obtain ⟨hU,hW⟩ := two_parallel_scale u v U W hD (hpq 0 1) (hpq 0 2) hUW
  obtain ⟨hU',hZ⟩ := two_parallel_scale u w U Z hE (hpq 0 1) (hpq 0 3) hUZ
  let r := det U v/det u v
  have hr : det U w/det u w=r := smul_left_injective ℝ hu (hU'.symm.trans hU)
  rw [hr] at hZ
  refine ⟨q 0-r • p 0,r,?_⟩
  funext i
  fin_cases i
  · simp [hom]
  · change q 1=q 0-r • p 0+r • p 1
    have hh : q 1-q 0=r • (p 1-p 0) := hU
    rw [smul_sub] at hh
    linear_combination hh
  · change q 2=q 0-r • p 0+r • p 2
    have hh : q 2-q 0=r • (p 2-p 0) := hW
    rw [smul_sub] at hh
    linear_combination hh
  · change q 3=q 0-r • p 0+r • p 3
    have hh : q 3-q 0=r • (p 3-p 0) := hZ
    rw [smul_sub] at hh
    linear_combination hh

/-- Opposite-triangle circumcenters applied twice produce a homothety. -/
theorem twice_homothety {p : Fin 4 → V} (h : Noncollinear p)
    (hq : Noncollinear (centers p)) :
    ∃ a r, centers (centers p)=hom a r ∘ p :=
  parallel_homothety h (twice_parallel h hq)

lemma scaled_div (r n d : ℝ) (hr : r≠0) : r^3*n/(r^2*d)=r*(n/d) := by
  rw [show r^3*n=r^2*(r*n) by ring, mul_div_mul_left _ _ (pow_ne_zero 2 hr)]
  ring

/-- The explicit formula is equivariant even in the zero-area case, where
Lean's division convention makes the formula return its first input. -/
lemma center_hom (a : V) (r : ℝ) (b c d : V) :
    center (hom a r b) (hom a r c) (hom a r d)=hom a r (center b c d) := by
  by_cases hr : r=0
  · simp [hom,hr,center,normSq,area,det]
  have hA : area (hom a r b) (hom a r c) (hom a r d)=r^2*area b c d := by
    dsimp [area,det,hom]; ring
  have hN₁ : normSq (hom a r c-hom a r b)*(hom a r d-hom a r b).2-
      normSq (hom a r d-hom a r b)*(hom a r c-hom a r b).2=
      r^3*(normSq (c-b)*(d-b).2-normSq (d-b)*(c-b).2) := by
    dsimp [normSq,hom]; ring
  have hN₂ : normSq (hom a r d-hom a r b)*(hom a r c-hom a r b).1-
      normSq (hom a r c-hom a r b)*(hom a r d-hom a r b).1=
      r^3*(normSq (d-b)*(c-b).1-normSq (c-b)*(d-b).1) := by
    dsimp [normSq,hom]; ring
  unfold center
  rw [hA,hN₁,hN₂,show 2*(r^2*area b c d)=r^2*(2*area b c d) by ring,
    scaled_div _ _ _ hr,scaled_div _ _ _ hr]
  apply Prod.ext <;> dsimp [hom] <;> ring

lemma centers_hom (a : V) (r : ℝ) (p : Fin 4 → V) :
    centers (hom a r ∘ p)=hom a r ∘ centers p := by
  funext i
  exact center_hom a r _ _ _

/-- All levels, not just the first two, satisfy the same homothetic
recurrence. Noncollinearity is needed only for the first two levels. -/
theorem orbit_recurrence {p : Fin 4 → V} {a : V} {r : ℝ}
    (hh : centers (centers p)=hom a r ∘ p) (n : ℕ) :
    centers^[n+2] p=hom a r ∘ centers^[n] p := by
  induction n with
  | zero => simpa [Function.iterate_succ_apply] using hh
  | succ n hn =>
    rw [show n+1+2=(n+2)+1 by omega,Function.iterate_succ_apply',hn,
      centers_hom,Function.iterate_succ_apply']

/-- A homothety, including a translation, preserves the line through a
point and its first image. The direction is allowed to be zero. -/
def orbitLine (a : V) (r : ℝ) (x : V) : Set V :=
  Set.range (fun t : ℝ => x+t • (hom a r x-x))

lemma mem_orbitLine (a : V) (r : ℝ) (x : V) : x∈orbitLine a r x := by
  exact ⟨0,by simp⟩

lemma hom_mem_orbitLine {a : V} {r : ℝ} {x y : V} (hy : y∈orbitLine a r x) :
    hom a r y∈orbitLine a r x := by
  obtain ⟨t,rfl⟩ := hy
  refine ⟨1+r*t,?_⟩
  apply Prod.ext <;> dsimp [hom] <;> ring

lemma plane_orbitLine_collinear (a : V) (r : ℝ) (x : V) :
    Collinear ℝ (plane '' orbitLine a r x) := by
  apply (collinear_iff_of_mem (show plane x∈plane '' orbitLine a r x from
    ⟨x,mem_orbitLine a r x,rfl⟩)).mpr
  refine ⟨plane (hom a r x-x),?_⟩
  rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
  refine ⟨t,?_⟩
  ext i
  fin_cases i <;> simp [plane,add_comm]

/-- Each labeled vertex stays on one line at even times and one line at odd times. -/
theorem orbit_mem_two_lines {p : Fin 4 → V} {a : V} {r : ℝ}
    (hh : centers (centers p)=hom a r ∘ p) (n : ℕ) (i : Fin 4) :
    centers^[n] p i∈orbitLine a r (p i) ∪ orbitLine a r (centers p i) := by
  induction n using Nat.twoStepInduction with
  | zero => exact Or.inl (mem_orbitLine _ _ _)
  | one => exact Or.inr (mem_orbitLine _ _ _)
  | more n hn _ =>
    rw [orbit_recurrence hh]
    rcases hn with hn | hn
    · exact Or.inl (hom_mem_orbitLine hn)
    · exact Or.inr (hom_mem_orbitLine hn)

def orbitSet (p : Fin 4 → V) : Set ℝ² :=
  {x | ∃ n i, plane (centers^[n] p i)=x}

/-- The entire infinite union of iterates lies on at most eight lines.
The source and its first circumcenter quadrilateral must have no collinear
triples, so that both rounds are geometric circumcenter operations. -/
theorem orbit_line_cover {p : Fin 4 → V} (h : Noncollinear p)
    (hq : Noncollinear (centers p)) :
    ∃ F : Finset (Set ℝ²), F.card≤8 ∧ (∀ C∈F, Collinear ℝ C) ∧
      ∀ x∈orbitSet p, ∃ C∈F, x∈C := by
  classical
  obtain ⟨a,r,hh⟩ := twice_homothety h hq
  let C : (Fin 4 ⊕ Fin 4) → Set ℝ² := fun j =>
    plane '' orbitLine a r (Sum.elim p (centers p) j)
  refine ⟨Finset.univ.image C,?_,?_,?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro L hL
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact plane_orbitLine_collinear _ _ _
  · rintro x ⟨n,i,rfl⟩
    rcases orbit_mem_two_lines hh n i with hm | hm
    · exact ⟨C (Sum.inl i),Finset.mem_image.mpr ⟨Sum.inl i,by simp,rfl⟩,
        Set.mem_image_of_mem _ hm⟩
    · exact ⟨C (Sum.inr i),Finset.mem_image.mpr ⟨Sum.inr i,by simp,rfl⟩,
        Set.mem_image_of_mem _ hm⟩

theorem orbit_coveredBy_eight {p : Fin 4 → V} (h : Noncollinear p)
    (hq : Noncollinear (centers p)) :
    CircleCoverReduction.CoveredBy (orbitSet p) 8 := by
  obtain ⟨F,hF,hline,hcov⟩ := orbit_line_cover h hq
  exact ⟨F,hF,fun C hC => InversionReduction.generalized_of_collinear (hline C hC),hcov⟩

lemma collinear_filter_card_le_two {S : Finset ℝ²} (hS : NonTrilinear (S : Set ℝ²))
    {C : Set ℝ²} (hC : Collinear ℝ C) [DecidablePred (fun x => x∈C)] :
    (S.filter (fun x => x∈C)).card≤2 := by
  classical
  by_contra! h
  obtain ⟨Q,hQ,hcard⟩ := Set.exists_subset_card_eq
    (show 3≤((S.filter (fun x => x∈C) : Finset ℝ²) : Set ℝ²).ncard by
      rw [Set.ncard_coe_finset]; omega)
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Set.ncard_eq_three.mp hcard
  have ha := Finset.mem_filter.mp (hQ (by simp : a∈({a,b,c} : Set ℝ²)))
  have hb := Finset.mem_filter.mp (hQ (by simp : b∈({a,b,c} : Set ℝ²)))
  have hc := Finset.mem_filter.mp (hQ (by simp : c∈({a,b,c} : Set ℝ²)))
  exact hS ha.1 hb.1 hc.1 hab hbc hac (hC.subset (by
    rintro x (rfl|rfl|rfl)
    · exact ha.2
    · exact hb.2
    · exact hc.2))

/-- No subset of these iterates with no collinear triple has more than 16
points. This bound is independent of the number of iterations or edge lengths. -/
theorem nontrilinear_orbit_card_le_sixteen {p : Fin 4 → V} (h : Noncollinear p)
    (hq : Noncollinear (centers p)) {S : Finset ℝ²}
    (hsub : (S : Set ℝ²)⊆orbitSet p) (hS : NonTrilinear (S : Set ℝ²)) : S.card≤16 := by
  classical
  obtain ⟨F,hF,hline,hcov⟩ := orbit_line_cover h hq
  let part : Set ℝ² → Finset ℝ² := fun C => S.filter (fun x => x∈C)
  have hp : ∀ C∈F, (part C).card≤2 := fun C hC =>
    collinear_filter_card_le_two hS (hline C hC)
  have hs : S⊆F.biUnion part := by
    intro x hx
    obtain ⟨C,hC,hxC⟩ := hcov x (hsub hx)
    exact Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_filter.mpr ⟨hx,hxC⟩⟩
  calc
    S.card ≤ (F.biUnion part).card := Finset.card_le_card hs
    _ ≤ ∑ C∈F, (part C).card := Finset.card_biUnion_le
    _ ≤ ∑ C∈F, 2 := Finset.sum_le_sum hp
    _ = 2*F.card := by simp [Nat.mul_comm]
    _ ≤ 16 := by omega

theorem weak_orbit_card_le_twentyfour {p : Fin 4 → V} (h : Noncollinear p)
    (hq : Noncollinear (centers p)) {S : Finset ℝ²}
    (hsub : (S : Set ℝ²)⊆orbitSet p)
    (hS : InversionReduction.NoFourGeneralized (S : Set ℝ²)) : S.card≤24 :=
  CircleCoverReduction.weak_card_le_three_mul_cover hS
    ((orbit_coveredBy_eight h hq).mono hsub)

#print axioms twice_homothety
#print axioms orbit_recurrence
#print axioms orbit_line_cover
#print axioms orbit_coveredBy_eight
#print axioms nontrilinear_orbit_card_le_sixteen
#print axioms weak_orbit_card_le_twentyfour
end
end Erdos213.CircumcenterOrbit
