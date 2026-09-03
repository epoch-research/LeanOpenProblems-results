import Submission.OddFieldExtensionExplore

/-! A finite-field-plane extension bound with an arbitrary prescribed old set.
This is not an integer-prefix construction. -/
namespace Erdos66FreshCurvePrefix
open Erdos66ParabolaRepair Erdos66OriginRepair Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 1600000

section Algebra
variable {E : Type*} [Field E]

lemma parabola_secant (u t a b : E) (hu : u ≠ 0) (hab : a ≠ b) :
    ((t-b)^2/u-(t-a)^2/u)/(a-b)=(2*t-a-b)/u := by
  field_simp [hu, sub_ne_zero.mpr hab]
  <;> ring

/-- Three distinct old-field inputs and old-field values determine all
coefficients of this nondegenerate quadratic, including its centre. -/
lemma three_old_values (k : Subfield E) (hE : (2:E) ≠ 0)
    (u t s a b c : E) (hu : u ≠ 0)
    (ha : a∈k) (hb : b∈k) (hc : c∈k)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hya : s-(t-a)^2/u∈k) (hyb : s-(t-b)^2/u∈k)
    (hyc : s-(t-c)^2/u∈k) : u∈k ∧ t∈k ∧ s∈k := by
  have hD (x : E) (hx : x∈k) (hax : a≠x)
      (hyx : s-(t-x)^2/u∈k) : (2*t-a-x)/u∈k := by
    have hh := k.div_mem (k.sub_mem hya hyx) (k.sub_mem ha hx)
    have he : ((s-(t-a)^2/u)-(s-(t-x)^2/u))/(a-x)=(2*t-a-x)/u := by
      rw [show (s-(t-a)^2/u)-(s-(t-x)^2/u)=(t-x)^2/u-(t-a)^2/u by ring]
      exact parabola_secant u t a x hu hax
    rwa [he] at hh
  have hDb := hD b hb hab hyb
  have hDc := hD c hc hac hyc
  have hui : u⁻¹∈k := by
    have hh := k.div_mem (k.sub_mem hDb hDc) (k.sub_mem hc hb)
    have he : ((2*t-a-b)/u-(2*t-a-c)/u)/(c-b)=u⁻¹ := by
      field_simp [hu, sub_ne_zero.mpr hbc.symm]
      <;> ring
    rwa [he] at hh
  have huk : u∈k := by simpa only [inv_inv] using k.inv_mem hui
  have ht : t∈k := by
    have hh := k.div_mem (k.add_mem (k.mul_mem hDb huk) (k.add_mem ha hb))
      (show (2:E)∈k from by simpa only [one_add_one_eq_two] using k.add_mem k.one_mem k.one_mem)
    have he : ((2*t-a-b)/u*u+(a+b))/2=t := by field_simp; ring
    rwa [he] at hh
  refine ⟨huk,ht,?_⟩
  have hh := k.add_mem hya (k.div_mem (k.pow_mem (k.sub_mem ht ha) 2) huk)
  simpa only [sub_add_cancel] using hh
end Algebra

section Finite
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

noncomputable def oldPlane (k : Subfield E) : Finset (E×E) :=
  Finset.univ.filter (fun z ↦ z.1∈k ∧ z.2∈k)

lemma mem_oldPlane (k : Subfield E) (z : E×E) :
    z∈oldPlane k ↔ z.1∈k ∧ z.2∈k := by simp [oldPlane]

noncomputable def freshCurve (k : Subfield E) (u : E) : Finset (E×E) :=
  curve u \ oldPlane k

/-- A translate of a parabola after deleting its old-plane slice meets the
old plane at most twice. The prescribed old set is completely arbitrary. -/
theorem arbitrary_old_fresh_curve_cap (k : Subfield E) (hE : ringChar E≠2)
    (A : Finset (E×E)) (hA : A⊆oldPlane k) (u : E) (hu : u≠0) (z : E×E) :
    pairCount A (freshCurve k u) z ≤ 2 := by
  classical
  by_contra hbad
  have hb : 2 < (A.filter (fun a ↦ z-a∈freshCurve k u)).card := by
    change ¬(A.filter (fun a ↦ z-a∈freshCurve k u)).card ≤ 2 at hbad
    omega
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hb
  have info (x : E×E) (hx : x∈A.filter (fun a ↦ z-a∈freshCurve k u)) :
      x.1∈k ∧ x.2∈k ∧ (z.2-x.2)=(z.1-x.1)^2/u ∧ z-x∉oldPlane k := by
    obtain ⟨hxA,hxf⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxcurve,hxnot⟩ := Finset.mem_sdiff.mp hxf
    exact ⟨(mem_oldPlane k x).mp (hA hxA) |>.1,
      (mem_oldPlane k x).mp (hA hxA) |>.2,
      (mem_curve u (z-x)).mp hxcurve,hxnot⟩
  obtain ⟨ha1,ha2,haeq,hanot⟩ := info a ha
  obtain ⟨hb1,hb2,hbeq,hbnot⟩ := info b hb
  obtain ⟨hc1,hc2,hceq,hcnot⟩ := info c hc
  have distinct (x y : E×E) (hxy : x≠y)
      (hx : z.2-x.2=(z.1-x.1)^2/u) (hy : z.2-y.2=(z.1-y.1)^2/u) : x.1≠y.1 := by
    intro he
    apply hxy
    apply Prod.ext he
    rw [he] at hx
    exact sub_right_injective (hx.trans hy.symm)
  have hya : z.2-(z.1-a.1)^2/u∈k := by
    convert ha2 using 1
    linear_combination haeq
  have hyb : z.2-(z.1-b.1)^2/u∈k := by
    convert hb2 using 1
    linear_combination hbeq
  have hyc : z.2-(z.1-c.1)^2/u∈k := by
    convert hc2 using 1
    linear_combination hceq
  obtain ⟨huk,ht,hs⟩ := three_old_values k (Ring.two_ne_zero hE) u z.1 z.2 a.1 b.1 c.1 hu
    ha1 hb1 hc1 (distinct a b hab haeq hbeq) (distinct a c hac haeq hceq)
    (distinct b c hbc hbeq hceq) hya hyb hyc
  exact hanot ((mem_oldPlane k (z-a)).mpr ⟨k.sub_mem ht ha1,k.sub_mem hs ha2⟩)


/-- A bounded number of fresh curves controls all mixed counts with an
arbitrary prescribed old set. -/
theorem arbitrary_old_fresh_union_cap (k : Subfield E) (hE : ringChar E≠2)
    (A B : Finset (E×E)) (hA : A⊆oldPlane k) (U : Finset E)
    (hU : ∀ u∈U, u≠0) (hB : B⊆U.biUnion (freshCurve k)) (z : E×E) :
    pairCount A B z ≤ 2*U.card := by
  calc
    _ ≤ pairCount A (U.biUnion (freshCurve k)) z :=
      pairCount_mono (Finset.Subset.refl A) hB z
    _ ≤ ∑ u∈U, pairCount A (freshCurve k u) z :=
      pairCount_biUnion_right_le U (freshCurve k) A z
    _ ≤ ∑ _u∈U, 2 := Finset.sum_le_sum (fun u hu ↦
      arbitrary_old_fresh_curve_cap k hE A hA u (hU u hu) z)
    _ = _ := by simp [mul_comm]

lemma fresh_union_disjoint (k : Subfield E) (A B : Finset (E×E))
    (hA : A⊆oldPlane k) (U : Finset E) (hB : B⊆U.biUnion (freshCurve k)) :
    Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨u,hu,hzu⟩ := Finset.mem_biUnion.mp (hB hzB)
  exact (Finset.mem_sdiff.mp hzu).2 (hA hzA)

/-- Exact membership preservation; the old set is chosen before the fresh
curves and need not have any parabola structure. -/
theorem prescribed_old_slice (k : Subfield E) (A B : Finset (E×E))
    (hA : A⊆oldPlane k) (U : Finset E) (hB : B⊆U.biUnion (freshCurve k)) :
    (A∪B)∩oldPlane k=A := by
  have hd := fresh_union_disjoint k (oldPlane k) B (Finset.Subset.refl _) U hB
  ext z
  constructor
  · intro hz
    obtain ⟨hzAB,hzk⟩ := Finset.mem_inter.mp hz
    rcases Finset.mem_union.mp hzAB with hzA | hzB
    · exact hzA
    · exact False.elim (Finset.disjoint_left.mp hd hzk hzB)
  · intro hz
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left B hz,hA hz⟩

/-- Conditional flatness transfer. The cost of retained old self-counts is
kept explicitly: it is not implied by the mixed-count bound. -/
theorem prescribed_old_flatness (k : Subfield E) (hE : ringChar E≠2)
    (A B : Finset (E×E)) (hA : A⊆oldPlane k) (U : Finset E)
    (hU : ∀ u∈U, u≠0) (hB : B⊆U.biUnion (freshCurve k))
    (μ err g : ℝ) (z : E×E)
    (hflat : |(pairCount B B z:ℝ)-μ|≤err)
    (hcap : (pairCount A A z:ℝ)≤g) :
    |(pairCount (A∪B) (A∪B) z:ℝ)-μ|≤err+4*U.card+g := by
  have hd := fresh_union_disjoint k A B hA U hB
  have hm := arbitrary_old_fresh_union_cap k hE A B hA U hU hB z
  rw [pairCount_comm A B] at hm
  have hm' : (pairCount B A z:ℝ) ≤ 2*U.card := by exact_mod_cast hm
  rw [pairCount_union_self A B z hd]
  push_cast
  rw [abs_le] at hflat ⊢
  have hAA : 0≤(pairCount A A z:ℝ) := Nat.cast_nonneg _
  have hBA : 0≤(pairCount B A z:ℝ) := Nat.cast_nonneg _
  have hUcard : 0≤(U.card:ℝ) := Nat.cast_nonneg _
  constructor <;> linarith [hflat.1,hflat.2]

end Finite
end Erdos66FreshCurvePrefix
