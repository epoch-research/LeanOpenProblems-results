import Submission.OrderedPipageGeometryExplore

/-! Pairwise pipage concavity of disjoint-monomial product potentials.
The coefficients may be negative, provided they have a common sign and
the two updated coordinates do not lie in the same monomial. -/
namespace Erdos66DisjointProductPipage
open Erdos66OrderedPipageGeometry
open scoped Classical
set_option maxHeartbeats 2200000

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
noncomputable def productPotential (T : Finset κ) (E : κ → Finset ι) (c : κ → ℝ)
    (x : ι → ℝ) : ℝ := ∏ r∈T, (1+c r*∏ i∈E r, x i)

lemma prod_one_add_of_card_le_one (S : Finset κ) (hS : S.card≤1) (f : κ → ℝ) :
    (∏ r∈S, (1+f r))=1+∑ r∈S, f r := by
  rcases S.eq_empty_or_nonempty with h | ⟨a,ha⟩
  · simp [h]
  · have he : S={a} := by
      ext r
      simp only [Finset.mem_singleton]
      exact ⟨fun hr ↦ Finset.card_le_one.mp hS r hr a ha,fun h ↦ h ▸ ha⟩
    simp only [he,Finset.prod_singleton,Finset.sum_singleton]

lemma support_filter_card (T : Finset κ) (E : κ → Finset ι)
    (hdis : (T : Set κ).Pairwise (fun r s ↦ Disjoint (E r) (E s))) (i : ι) :
    (T.filter (fun r ↦ i∈E r)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  obtain ⟨hrT,hir⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsT,his⟩ := Finset.mem_filter.mp hs
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hrT hsT hne) hir his

lemma product_factor_nonneg (E : Finset ι) (c : ℝ) (hc : -1≤c)
    (x : ι → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1) : 0≤1+c*∏ i∈E, x i := by
  have hp0 : 0≤∏ i∈E, x i := Finset.prod_nonneg (fun i _ ↦ (hx i).1)
  have hp1 : (∏ i∈E, x i)≤1 := Finset.prod_le_one (fun i _ ↦ (hx i).1) (fun i _ ↦ (hx i).2)
  have hh := mul_le_mul_of_nonneg_right hc hp0
  nlinarith

lemma factorization_distinct_supports (T : Finset κ) (E : κ → Finset ι) (c : κ → ℝ)
    (hdis : (T : Set κ).Pairwise (fun r s ↦ Disjoint (E r) (E s)))
    (hc : ∀ r∈T, -1≤c r) (hsign : ∀ r∈T, ∀ s∈T, 0≤c r*c s)
    (x : ι → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1) (i j : ι) (hij : i≠j)
    (hsep : ∀ r∈T, ¬(i∈E r ∧ j∈E r)) :
    ∃ B C R : ℝ, 0≤B*C ∧ 0≤R ∧ ∀ a b : ℝ,
      productPotential T E c (replaceTwo x i j a b)=(1+B*a)*(1+C*b)*R := by
  let I := T.filter (fun r ↦ i∈E r)
  let J := (T.filter (fun r ↦ i∉E r)).filter (fun r ↦ j∈E r)
  let Z := (T.filter (fun r ↦ i∉E r)).filter (fun r ↦ j∉E r)
  let Q : κ → ℝ := fun r ↦ ∏ k∈E r, if k=i ∨ k=j then 1 else x k
  let B := ∑ r∈I, c r*Q r
  let C := ∑ r∈J, c r*Q r
  let R := ∏ r∈Z, (1+c r*∏ k∈E r, x k)
  have hQ (r : κ) : 0≤Q r := Finset.prod_nonneg (fun k _ ↦ by
    split_ifs; exact zero_le_one; exact (hx k).1)
  have hJsub : J⊆T.filter (fun r ↦ j∈E r) := by
    intro r hr
    obtain ⟨hrI,hrj⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hrI).1,hrj⟩
  have hIc : I.card≤1 := support_filter_card T E hdis i
  have hJc : J.card≤1 := (Finset.card_le_card hJsub).trans (support_filter_card T E hdis j)
  have hBC : 0≤B*C := by
    dsimp [B,C]
    rw [Finset.sum_mul]
    apply Finset.sum_nonneg
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_nonneg
    intro s hs
    have hrT := (Finset.mem_filter.mp hr).1
    have hsT := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
    have hh := mul_nonneg (hsign r hrT s hsT) (mul_nonneg (hQ r) (hQ s))
    nlinarith only [hh]
  refine ⟨B,C,R,hBC,?_,?_⟩
  · apply Finset.prod_nonneg
    intro r hr
    have hrT := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
    exact product_factor_nonneg (E r) (c r) (hc r hrT) x hx
  · intro a b
    have hI : (∏ r∈I, (1+c r*∏ k∈E r, replaceTwo x i j a b k))=1+B*a := by
      have he (r : κ) (hr : r∈I) :
          (1+c r*∏ k∈E r, replaceTwo x i j a b k)=1+c r*Q r*a := by
        obtain ⟨hrT,hri⟩ := Finset.mem_filter.mp hr
        have hrj : j∉E r := fun hrj ↦ hsep r hrT ⟨hri,hrj⟩
        rw [monomial_replaceTwo (E r) x i j hij a b,if_pos hri,if_neg hrj,mul_one]
        dsimp [Q]
        ring
      rw [Finset.prod_congr rfl he,prod_one_add_of_card_le_one I hIc]
      simp only [B,Finset.sum_mul]
    have hJ : (∏ r∈J, (1+c r*∏ k∈E r, replaceTwo x i j a b k))=1+C*b := by
      have he (r : κ) (hr : r∈J) :
          (1+c r*∏ k∈E r, replaceTwo x i j a b k)=1+c r*Q r*b := by
        obtain ⟨hrI,hrj⟩ := Finset.mem_filter.mp hr
        have hri := (Finset.mem_filter.mp hrI).2
        rw [monomial_replaceTwo (E r) x i j hij a b,if_neg hri,if_pos hrj,one_mul]
        dsimp [Q]
        ring
      rw [Finset.prod_congr rfl he,prod_one_add_of_card_le_one J hJc]
      simp only [C,Finset.sum_mul]
    have hZ : (∏ r∈Z, (1+c r*∏ k∈E r, replaceTwo x i j a b k))=R := by
      apply Finset.prod_congr rfl
      intro r hr
      obtain ⟨hrI,hrj⟩ := Finset.mem_filter.mp hr
      have hri := (Finset.mem_filter.mp hrI).2
      congr 2
      apply Finset.prod_congr rfl
      intro k hk
      simp only [replaceTwo,if_neg (show k≠i from fun h ↦ hri (h ▸ hk)),
        if_neg (show k≠j from fun h ↦ hrj (h ▸ hk))]
    have hsplit := Finset.prod_filter_mul_prod_filter_not T (fun r ↦ i∈E r)
      (fun r ↦ 1+c r*∏ k∈E r, replaceTwo x i j a b k)
    have hsplit' := Finset.prod_filter_mul_prod_filter_not (T.filter (fun r ↦ i∉E r))
      (fun r ↦ j∈E r) (fun r ↦ 1+c r*∏ k∈E r, replaceTwo x i j a b k)
    change _=productPotential T E c (replaceTwo x i j a b) at hsplit
    rw [←hsplit,←hsplit']
    change (∏ r∈I, _)*((∏ r∈J, _)*(∏ r∈Z, _))=_
    rw [hI,hJ,hZ]
    ring

lemma product_pipage_distinct (T : Finset κ) (E : κ → Finset ι) (c : κ → ℝ)
    (hdis : (T : Set κ).Pairwise (fun r s ↦ Disjoint (E r) (E s)))
    (hc : ∀ r∈T, -1≤c r) (hsign : ∀ r∈T, ∀ s∈T, 0≤c r*c s)
    (x : ι → ℝ) (hx : ∀ i, 0≤x i ∧ x i≤1) (i j : ι) (hij : i≠j)
    (hsep : ∀ r∈T, ¬(i∈E r ∧ j∈E r))
    (a b d e w : ℝ) (hi : w*a+(1-w)*d=x i) (hj : w*b+(1-w)*e=x j)
    (hp : w*(a*b)+(1-w)*(d*e)≤x i*x j) :
    w*productPotential T E c (replaceTwo x i j a b)+
      (1-w)*productPotential T E c (replaceTwo x i j d e)≤productPotential T E c x := by
  obtain ⟨B,C,R,hBC,hR,hf⟩ := factorization_distinct_supports T E c hdis hc hsign x hx i j hij hsep
  have hfx := hf (x i) (x j)
  rw [replaceTwo_self] at hfx
  rw [hf,hf,hfx]
  have he : w*((1+B*a)*(1+C*b)*R)+(1-w)*((1+B*d)*(1+C*e)*R)=
      (1+B*(w*a+(1-w)*d)+C*(w*b+(1-w)*e)+B*C*(w*(a*b)+(1-w)*(d*e)))*R := by ring
  rw [he,hi,hj]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hBC) hR
  nlinarith only [hh]

end Erdos66DisjointProductPipage
