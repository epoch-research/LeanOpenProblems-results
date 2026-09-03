import FormalConjecturesUtil
import Submission.ThetaColumnPadding
import Submission.ThetaAnchorBudget
import Submission.ThetaRegularCounterexample

/-! An obstruction to reducing every oriented-theta-free relation to a
C4-free relation by a linear number of incidence deletions. Auxiliary only. -/
open Finset
namespace Erdos713ThetaC4Deletion
open Erdos713ThetaGram Erdos713ThetaHeavyShadow Erdos713ThetaAnchorPacking
open Erdos713ThetaAnchorBudget Erdos713ThetaSplit Erdos713ThetaColumnPadding
variable {A B : Type*}
set_option maxHeartbeats 2000000

def FourFree (R : A → B → Prop) : Prop :=
  ∀ a b x y, R a x → R a y → R b x → R b y → a = b ∨ x = y

noncomputable def edges (R : A → B → Prop) : ℕ :=
  Nat.card {p : A × B // R p.1 p.2}

noncomputable def loss (R Q : A → B → Prop) : ℕ :=
  Nat.card {p : A × B // R p.1 p.2 ∧ ¬ Q p.1 p.2}

lemma edge_split [Fintype A] [Fintype B] {R Q : A → B → Prop}
    (hQ : ∀ a b, Q a b → R a b) : edges Q+loss R Q = edges R := by
  classical
  have hsplit := card_filter_add_card_filter_not
    (s := (univ : Finset (A × B)).filter (fun p => R p.1 p.2))
    (fun p : A × B => Q p.1 p.2)
  have hkeep : ((univ : Finset (A × B)).filter (fun p => R p.1 p.2)).filter
      (fun p => Q p.1 p.2) = univ.filter (fun p => Q p.1 p.2) := by
    ext p
    simp only [mem_filter,mem_univ,true_and]
    exact and_iff_right_of_imp (hQ p.1 p.2)
  rw [hkeep,filter_filter] at hsplit
  simpa only [edges,loss,Nat.card_eq_fintype_card,Fintype.card_subtype] using hsplit

lemma four_free_pair_bound [Fintype A] [Fintype B] {Q : A → B → Prop}
    (hQ : FourFree Q) (x y : B) (hxy : x ≠ y) :
    (commonRows Q univ (x,y)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro a ha b hb
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  exact (hQ a b x y ha'.1 ha'.2 hb'.1 hb'.2).resolve_right hxy

/-- The standard second-moment estimate for a C4-free relation. -/
theorem four_free_second_moment [Fintype A] [Fintype B] {Q : A → B → Prop}
    (hQ : FourFree Q) :
    (edges Q)^2 ≤ Nat.card A*(edges Q+(Nat.card B)^2) := by
  classical
  let m := Nat.card A
  let k := Nat.card B
  let E := ∑ a : A, (row Q a).card
  let P := ∑ a : A, (row Q a).offDiag.card
  let Z := ∑ a : A, (row Q a).card^2
  have he : edges Q = E := by
    rw [edges,edge_card_eq_rows]
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,E,row]
  have hp : P ≤ k^2 := by
    have hs := pair_incidence_sum Q (univ : Finset A)
    change P = _ at hs
    rw [hs]
    calc
      _ ≤ ∑ _p ∈ (univ : Finset B).offDiag, 1 := by
        apply sum_le_sum
        intro p hp
        exact four_free_pair_bound hQ p.1 p.2 (mem_offDiag.mp hp).2.2
      _ = (univ : Finset B).offDiag.card := by simp
      _ ≤ k^2 := by
        simp only [offDiag_card,card_univ,k,Nat.card_eq_fintype_card,pow_two]
        exact Nat.sub_le _ _
  have hz : Z = E+P := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [offDiag_card]
    have hle : (row Q a).card ≤ (row Q a).card*(row Q a).card := Nat.le_mul_self _
    have hh := Nat.sub_add_cancel hle
    nlinarith only [hh]
  have hc : E^2 ≤ m*Z := by
    simpa only [E,Z,m,card_univ,Nat.card_eq_fintype_card] using
      (sq_sum_le_card_mul_sum_sq (s := (univ : Finset A)) (f := fun a => (row Q a).card))
  rw [he]
  rw [hz] at hc
  exact hc.trans (Nat.mul_le_mul_left m (Nat.add_le_add_left hp E))

/-- The unbalanced C4 estimate in the range `k^2<=m`. -/
theorem four_free_edges_le_two_rows [Fintype A] [Fintype B] {Q : A → B → Prop}
    (hQ : FourFree Q) (hsize : (Nat.card B)^2 ≤ Nat.card A) :
    edges Q ≤ 2*Nat.card A := by
  let m := Nat.card A
  let E := edges Q
  have hbound : E^2 ≤ m*(E+m) := (four_free_second_moment hQ).trans
    (Nat.mul_le_mul_left m (Nat.add_le_add_left hsize E))
  change E ≤ 2*m
  by_contra hbad
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    rw [hm0,zero_mul] at hbound
    nlinarith
  have h1 := Nat.mul_le_mul_left E (show 2*m ≤ E from by omega)
  have h2 := Nat.mul_lt_mul_of_pos_left (show 2*m < E from by omega) hm
  nlinarith only [hbound,h1,h2]

/-- An integer square-root version valid for all finite shore sizes. -/
theorem four_free_edges_le_sqrt [Fintype A] [Fintype B] {Q : A → B → Prop}
    (hQ : FourFree Q) :
    edges Q ≤ Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1) := by
  let m := Nat.card A
  let k := Nat.card B
  let E := edges Q
  let s := Nat.sqrt m+1
  have hc : E^2 ≤ m*(E+k^2) := four_free_second_moment hQ
  have hs : m ≤ s^2 := by
    simpa only [s,Nat.succ_eq_add_one,pow_two] using (Nat.lt_succ_sqrt m).le
  change E ≤ m+k*s
  by_contra hbad
  have hsub : E-m+m = E := Nat.sub_add_cancel (by omega)
  have hpow := Nat.pow_le_pow_left (show k*s+1 ≤ E-m from by omega) 2
  have hprod := Nat.mul_le_mul_left (k^2) hs
  have hsq : (E-m)^2 ≤ m*k^2 := by
    rw [← hsub] at hc
    nlinarith only [hc,Nat.zero_le (m*(E-m))]
  nlinarith only [hsq,hpow,hprod,Nat.zero_le (k*s)]

/-- Every C4-free subrelation of the Gram example must lose an arbitrarily
large multiple of the total size of its two shores. -/
theorem exists_deletion_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ (Nat.card B)^2 < Nat.card A ∧
      ∀ Q : A → B → Prop, (∀ a b, Q a b → R a b) → FourFree Q →
        N*(Nat.card A+Nat.card B) < loss R Q := by
  classical
  obtain ⟨A,B,instA,instB,R,hf,hsize,_,he⟩ := exists_oriented_counterexamples (2*N+3) 1
  simp only [one_mul] at hsize
  have hm : 0 < Nat.card A := by omega
  have hk : Nat.card B ≤ Nat.card A := (Nat.le_mul_self (Nat.card B)).trans
    (by simpa only [pow_two] using hsize.le)
  refine ⟨A,B,instA,instB,R,hf,hm,hsize,?_⟩
  intro Q hQ hfour
  have hu := four_free_edges_le_two_rows hfour hsize.le
  have hs := edge_split hQ
  change edges R = Nat.card A*(2*N+3) at he
  have hn := Nat.mul_le_mul_left N (Nat.add_le_add_left hk (Nat.card A))
  nlinarith only [hu,hs,he,hn,hm]

lemma four_free_comap {C : Type*} {Q : A → C → Prop} (hQ : FourFree Q)
    {f : B → C} (hf : Function.Injective f) : FourFree (fun a b => Q a (f b)) := by
  intro a b x y hax hay hbx hby
  rcases hQ a b (f x) (f y) hax hay hbx hby with hab | hxy
  · exact Or.inl hab
  · exact Or.inr (hf hxy)

lemma edges_of_supported_columns [Fintype A] [Fintype B] {C : Type*} [Fintype C]
    (f : B → C) (hf : Function.Injective f) (Q : A → C → Prop)
    (hs : ∀ a c, Q a c → ∃ b, f b = c) :
    edges (fun a b => Q a (f b)) = edges Q := by
  classical
  let g : {p : A × B // Q p.1 (f p.2)} → {p : A × C // Q p.1 p.2} :=
    fun p => ⟨(p.val.1,f p.val.2),p.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro p q he
      have hpq := congrArg Subtype.val he
      change (p.val.1,f p.val.2) = (q.val.1,f q.val.2) at hpq
      have h1 : p.val.1 = q.val.1 := congrArg (fun z : A × C => z.1) hpq
      have h2 : f p.val.2 = f q.val.2 := congrArg (fun z : A × C => z.2) hpq
      exact Subtype.ext (Prod.ext h1 (hf h2))
    · rintro ⟨⟨a,c⟩,hc⟩
      obtain ⟨b,rfl⟩ := hs a c hc
      exact ⟨⟨(a,b),hc⟩,rfl⟩
  exact Nat.card_congr (Equiv.ofBijective g hg)

/-- Isolated-column padding makes the shores equal and enforces the column
cap `degree<=|B|`, without reducing the necessary C4-deletion cost. -/
theorem exists_balanced_deletion_counterexample (N : ℕ) :
    ∃ (A : Type) (_ : Fintype A) (R : A → A → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card A) ∧
      ∀ Q : A → A → Prop, (∀ a b, Q a b → R a b) → FourFree Q →
        N*(2*Nat.card A) < loss R Q := by
  classical
  obtain ⟨A,B,instA,instB,R,hf,hsize,hrow,he⟩ := exists_oriented_counterexamples (2*N+3) 1
  simp only [one_mul] at hsize
  have hm : 0 < Nat.card A := by omega
  have hA : Nonempty A := (Nat.card_pos_iff.mp hm).1
  letI := hA
  have hB : Nonempty B := by
    let a : A := Classical.choice hA
    have hr := hrow a
    have hc : Nat.card {b // R a b} ≤ Nat.card B :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hp : 0 < Nat.card B := by omega
    exact (Nat.card_pos_iff.mp hp).1
  letI := hB
  have hk : Nat.card B ≤ Nat.card A := (Nat.le_mul_self (Nat.card B)).trans
    (by simpa only [pow_two] using hsize.le)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card B ≤ Fintype.card A by simpa only [Nat.card_eq_fintype_card] using hk)
  let T := pad f R
  have ht : ¬ HasTheta T := pad_no_theta f.injective hf
  have het : edges T = Nat.card A*(2*N+3) := (pad_edge_card f.injective R).trans he
  refine ⟨A,instA,T,ht,hm,?_,?_⟩
  · intro b
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  · intro Q hQ hfour
    let Q' : A → B → Prop := fun a b => Q a (f b)
    have hQ' : FourFree Q' := four_free_comap hfour f.injective
    have hu := four_free_edges_le_two_rows hQ' hsize.le
    have heq : edges Q' = edges Q := edges_of_supported_columns f f.injective Q (by
      intro a c hc
      obtain ⟨b,_,hb⟩ := hQ a c hc
      exact ⟨b,hb⟩)
    rw [heq] at hu
    have hs := edge_split hQ
    nlinarith only [hu,hs,het,hm]

/-- The obstruction also persists without isolated vertices, with bounded
row-degree ratio, a positive column minimum, and the column-degree cap. -/
theorem exists_regular_deletion_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      0 < r ∧ N ≤ r ∧ ¬ HasTheta R ∧ 0 < Nat.card A ∧ 0 < Nat.card B ∧
      Nat.card A ≤ (Nat.card B)^2 ∧
      (∀ a, r ≤ Nat.card {b // R a b} ∧ Nat.card {b // R a b} ≤ 16*r) ∧
      (∀ b, Nat.card B ≤ 1152*Nat.card {a // R a b} ∧ Nat.card {a // R a b} ≤ Nat.card B) ∧
      ∀ Q : A → B → Prop, (∀ a b, Q a b → R a b) → FourFree Q →
        N*(Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1)) < loss R Q := by
  classical
  obtain ⟨A,B,instA,instB,R,r,hr,hrN,hf,hm,hk,hsize,hrow,hcol,he⟩ :=
    Erdos713ThetaRegular.exists_regular_counterexample (N+1)
  refine ⟨A,B,instA,instB,R,r,hr,by omega,hf,hm,hk,hsize,hrow,hcol,?_⟩
  intro Q hQ hfour
  have hu := four_free_edges_le_sqrt hfour
  have hs := edge_split hQ
  change (N+1)*(Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1)) < edges R at he
  nlinarith only [hu,hs,he]

/-- Negation of the linear-deletion proposal, even on equal-sized shores. -/
theorem no_balanced_linear_deletion_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A : Type) [Fintype A] (R : A → A → Prop),
      ¬ HasTheta R → ∃ Q : A → A → Prop,
        (∀ a b, Q a b → R a b) ∧ FourFree Q ∧
        (loss R Q : ℝ) ≤ C*(2*Nat.card A) := by
  rintro ⟨C,hC,hbound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,instA,R,hf,hm,_,hbad⟩ := exists_balanced_deletion_counterexample N
  obtain ⟨Q,hQ,hfour,hsmall⟩ := hbound A R hf
  have hlarge : (N : ℝ)*(2*Nat.card A) < loss R Q := by
    exact_mod_cast hbad Q hQ hfour
  have hcn : C*(2*Nat.card A : ℝ) ≤ N*(2*Nat.card A) :=
    mul_le_mul_of_nonneg_right hN.le (by positivity)
  linarith

#print axioms four_free_second_moment
#print axioms four_free_edges_le_sqrt
#print axioms exists_regular_deletion_counterexample
#print axioms no_balanced_linear_deletion_bound
#print axioms four_free_edges_le_two_rows
#print axioms exists_deletion_counterexample
#print axioms exists_balanced_deletion_counterexample
end Erdos713ThetaC4Deletion
