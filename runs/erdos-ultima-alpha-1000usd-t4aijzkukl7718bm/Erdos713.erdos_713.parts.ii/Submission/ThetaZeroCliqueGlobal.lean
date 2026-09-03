import FormalConjecturesUtil
import Submission.ThetaZeroClique
import Submission.ThetaZeroTriangleGlobal

/-! Larger codegree-one fans forced by theta-free links and high density.
These are structural statements, not a rational-exponent conclusion. -/
open Finset
namespace Erdos713ThetaZeroCliqueGlobal
open Erdos713ThetaGram Erdos713GlobalLight Erdos713GlobalTheta
open Erdos713ConditionalThetaWeighted Erdos713ThetaZeroClique
variable {A B : Type*}
set_option maxHeartbeats 2000000

/-- Distinct neighbours of a root, each pair having that root as its
unique common supporting row. -/
def OneFan (R : A → B → Prop) (a : A) (s : ℕ) : Prop :=
  ∃ x : Fin s → B, Function.Injective x ∧ (∀ i, R a (x i)) ∧
    ∀ i j, i ≠ j → codegree R (x i) (x j) = 1

lemma zeroClique_link_iff [Fintype A] (R : A → B → Prop) (a : A) (s : ℕ) :
    ZeroClique (link R a) s ↔ OneFan R a s := by
  constructor
  · rintro ⟨x,hi,hz⟩
    refine ⟨fun i => (x i).val,Subtype.val_injective.comp hi,fun i => (x i).property,?_⟩
    intro i j hij
    have h := link_codegree_add_one R a (x i) (x j)
    have h0 := hz i j hij
    simpa only [h0,zero_add] using h.symm
  · rintro ⟨x,hi,ha,hc⟩
    let y : Fin s → {b // R a b} := fun i => ⟨x i,ha i⟩
    refine ⟨y,?_,?_⟩
    · intro i j he
      exact hi (congrArg Subtype.val he)
    · intro i j hij
      have h := link_codegree_add_one R a (y i) (y j)
      have h1 := hc i j hij
      change codegree (link R a) (y i) (y j)+1 = codegree R (x i) (x j) at h
      omega

lemma link_lightCountAt [Fintype A] [Fintype B]
    (R : A → B → Prop) (a : A) (s : ℕ) :
    lightCountAt (link R a) s = (lightPairs R s a).card := by
  classical
  let e : {p : {b // R a b} × {b // R a b} // codegree (link R a) p.1 p.2 < s} ≃
      ↥(lightPairs R s a) :=
    { toFun := fun p => ⟨(p.val.1.val,p.val.2.val),by
        have hc := link_codegree_add_one R a p.val.1 p.val.2
        have hp := p.property
        simp only [lightPairs,mem_filter,mem_univ,true_and]
        exact ⟨p.val.1.property,p.val.2.property,by omega⟩⟩
      invFun := fun p => by
        have hp := p.property
        simp only [lightPairs,mem_filter,mem_univ,true_and] at hp
        let x : {b // R a b} := ⟨p.val.1,hp.1⟩
        let y : {b // R a b} := ⟨p.val.2,hp.2.1⟩
        exact ⟨(x,y),by
          change codegree (link R a) x y < s
          have hc := link_codegree_add_one R a x y
          have hp' : codegree R x.val y.val ≤ s := hp.2.2
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

/-- The degree-square budget of roots WITHOUT a given fan. No exclusion
of fans at other roots is assumed. -/
theorem restricted_row_squares [Fintype A] [Fintype B]
    (R : A → B → Prop) (S : Finset A) {s : ℕ} (hs : 3 ≤ s)
    (hf : ∀ a ∈ S, ¬ HasTheta (link R a)) (hz : ∀ a ∈ S, ¬ OneFan R a s) :
    (∑ a ∈ S, (Nat.card {b // R a b})^2) ≤
      12*S.card*Fintype.card A+2*s*(Fintype.card B)^2 := by
  classical
  have hlocal (a : A) (ha : a ∈ S) : (Nat.card {b // R a b})^2 ≤
      12*Fintype.card A+2*(lightPairs R s a).card := by
    have h := density_gap_at (hf a ha) hs
      (fun h => hz a ha ((zeroClique_link_iff R a s).mp h))
    rw [link_lightCountAt] at h
    have hm : Fintype.card {x : A // x ≠ a} ≤ Fintype.card A :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    simp only [Nat.card_eq_fintype_card] at h ⊢
    omega
  have hsum := sum_le_sum (s := S) (fun a ha => hlocal a ha)
  have ht : (∑ a ∈ S, (lightPairs R s a).card) ≤ s*(Fintype.card B)^2 := by
    apply le_trans _ (sum_lightPairs_le R s)
    exact sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)
  simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul,← mul_sum] at hsum
  nlinarith only [hsum,ht]

/-- Without an s-fan anywhere, the edge count has a square-scale bound. -/
theorem incidence_square_of_no_fan [Fintype A] [Fintype B]
    (R : A → B → Prop) {s : ℕ} (hs : 3 ≤ s)
    (hf : ∀ a, ¬ HasTheta (link R a)) (hz : ∀ a, ¬ OneFan R a s) :
    (Nat.card {p : A × B // R p.1 p.2})^2 ≤
      12*(Fintype.card A)^3+2*s*Fintype.card A*(Fintype.card B)^2 := by
  classical
  rw [Erdos713ThetaSplit.edge_card_eq_rows]
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset A))
    (f := fun a => Nat.card {b // R a b})
  rw [card_univ] at hc
  have h := restricted_row_squares R univ hs (fun a _ => hf a) (fun a _ => hz a)
  rw [card_univ] at h
  have hu := Nat.mul_le_mul_left (Fintype.card A) h
  nlinarith only [hc,hu]

/-- Arbitrarily large fixed fans are forced whenever E^2/n^3 diverges
along a sequence of theta-free-link hosts. This finite statement supplies
an explicit threshold and assumes no degree regularity. -/
theorem exists_fan_of_edges (n s : ℕ) (hs : 3 ≤ s)
    (R : Fin n → Fin n → Prop) (hf : ∀ a, ¬ HasTheta (link R a))
    (he : (12+2*s)*n^3 < (Nat.card {p : Fin n × Fin n // R p.1 p.2})^2) :
    ∃ a, OneFan R a s := by
  classical
  by_contra h
  have hz : ∀ a, ¬ OneFan R a s := fun a ha => h ⟨a,ha⟩
  have hu := incidence_square_of_no_fan R hs hf hz
  simp only [Fintype.card_fin] at hu
  nlinarith only [he,hu]

/-- Minimum degree controls the number of exceptional roots lacking a fan.
This is unconditional apart from theta-free links. -/
theorem count_roots_without_fans (n d s : ℕ) (hs : 3 ≤ s)
    (R : Fin n → Fin n → Prop) (hf : ∀ a, ¬ HasTheta (link R a))
    (hd : ∀ a, d ≤ Nat.card {b // R a b}) :
    Nat.card {a // ¬ OneFan R a s}*d^2 ≤
      12*Nat.card {a // ¬ OneFan R a s}*n+2*s*n^2 := by
  classical
  let S := (univ : Finset (Fin n)).filter (fun a => ¬ OneFan R a s)
  have hcard : S.card = Nat.card {a // ¬ OneFan R a s} := by
    simp only [S,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hlow : S.card*d^2 ≤ ∑ a ∈ S, (Nat.card {b // R a b})^2 := by
    calc
      _ = ∑ _a ∈ S, d^2 := by simp
      _ ≤ _ := sum_le_sum (fun a _ => Nat.pow_le_pow_left (hd a) 2)
  have hu := restricted_row_squares R S hs (fun a _ => hf a)
    (fun _ ha => (mem_filter.mp ha).2)
  simp only [Fintype.card_fin] at hu
  rw [← hcard]
  exact hlow.trans hu

/-- A fan has disjoint supporting-row sets after its root is removed.
This is a budget inequality, not an exclusion of large fans. -/
theorem fan_support_budget [Fintype A] [Fintype B] (R : A → B → Prop)
    (a : A) (s d : ℕ) (hfan : OneFan R a s)
    (hd : ∀ b, d ≤ Nat.card {x // R x b}) :
    s*(d-1)+1 ≤ Fintype.card A := by
  classical
  obtain ⟨x,_,hx⟩ := (zeroClique_link_iff R a s).mpr hfan
  have hu := Erdos713ThetaDisjointSupports.sum_column_degrees_le_rows (link R a) x hx
  have hlow : s*(d-1) ≤ ∑ i : Fin s, Nat.card {b // link R a b (x i)} := by
    calc
      _ = ∑ _i : Fin s, (d-1) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        have h := link_column_add_one R a (x i)
        have hl := hd (x i).val
        omega
  have ha : Fintype.card {x : A // x ≠ a}+1 = Fintype.card A := by
    have h := card_restrict_ne_add_one (fun _ : A => True) a True.intro
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype_true] using h
  omega

/-- A weak unconditional cubic degree bound. This does not improve the
previously checked 14/9 exponent for almost-regular apex-theta hosts. -/
theorem minimum_degree_cubic (n d : ℕ) (hn : 0 < n)
    (R : Fin n → Fin n → Prop) (hf : ∀ a, ¬ HasTheta (link R a))
    (hrow : ∀ a, d ≤ Nat.card {b // R a b})
    (hcol : ∀ b, d ≤ Nat.card {a // R a b}) : d^3 ≤ 21*n^2 := by
  classical
  have hdn : d ≤ n := by
    let a : Fin n := ⟨0,hn⟩
    apply (hrow a).trans
    rw [Nat.card_eq_fintype_card]
    simpa only [Fintype.card_fin] using (Fintype.card_subtype_le (fun b => R a b))
  by_cases hd : 2 ≤ d
  · let s := n/(d-1)+3
    have hs : 3 ≤ s := Nat.le_add_left 3 _
    have hpos : 0 < d-1 := by omega
    have hfan : ∀ a, ¬ OneFan R a s := by
      intro a ha
      have h := fan_support_budget R a s d ha hcol
      simp only [Fintype.card_fin] at h
      have hdiv := Nat.lt_mul_div_succ n hpos
      dsimp [s] at h
      nlinarith only [h,hdiv,hpos]
    have hsum := restricted_row_squares R univ hs (fun a _ => hf a) (fun a _ => hfan a)
    simp only [card_univ,Fintype.card_fin] at hsum
    have hlo : n*d^2 ≤ ∑ a : Fin n, (Nat.card {b // R a b})^2 := by
      calc
        _ = ∑ _a : Fin n, d^2 := by simp
        _ ≤ _ := sum_le_sum (fun a _ => Nat.pow_le_pow_left (hrow a) 2)
    have hmul : n*d^2 ≤ n*((12+2*s)*n) := by nlinarith only [hlo,hsum]
    have hsquare := Nat.le_of_mul_le_mul_left hmul hn
    have htimes := Nat.mul_le_mul_right (d-1) hsquare
    have hq := Nat.div_mul_le_self n (d-1)
    have hqn := Nat.mul_le_mul_left (2*n) hq
    have hdsub : d-1+1 = d := by omega
    have hdnd : n*d ≤ n*n := Nat.mul_le_mul_left n hdn
    have hdn2 := Nat.pow_le_pow_left hdn 2
    dsimp [s] at htimes
    nlinarith only [htimes,hqn,hdsub,hdnd,hdn2]
  · have hdsmall : d ≤ 1 := by omega
    have hn1 : 1 ≤ n := hn
    have hc : d^3 ≤ 1 := by simpa using Nat.pow_le_pow_left hdsmall 3
    nlinarith only [hc,hn1]

#print axioms zeroClique_link_iff
#print axioms link_lightCountAt
#print axioms restricted_row_squares
#print axioms incidence_square_of_no_fan
#print axioms exists_fan_of_edges
#print axioms count_roots_without_fans
#print axioms fan_support_budget
#print axioms minimum_degree_cubic
end Erdos713ThetaZeroCliqueGlobal
