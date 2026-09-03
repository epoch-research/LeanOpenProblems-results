import FormalConjecturesUtil
import Submission.ProductCoverObstructions

/-! Exact sheet counts for finite covers of connected bases.
These formulas quantify an ordinary cover's density loss, not an
amplification theorem or a proof of Erdős 713. -/
open SimpleGraph Finset
namespace Erdos713CoverSheetCounts
open Erdos713ProductCover
variable {V W : Type*} {G : SimpleGraph V} {F : SimpleGraph W}
set_option maxHeartbeats 2000000

lemma unique_lift (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    {u v : W} (huv : F.Adj u v) (x : {x // f x=u}) :
    ∃! y : {y // f y=v}, G.Adj x.val y.val := by
  let z : F.neighborSet (f x.val) := ⟨v,by rw [x.property]; exact huv⟩
  obtain ⟨y,hy⟩ := (h x.val).2 z
  let y' : {y // f y=v} := ⟨y.val,congrArg Subtype.val hy⟩
  refine ⟨y',y.property,?_⟩
  intro a ha
  have he : neighborMap f x.val ⟨a.val,ha⟩ = z := Subtype.ext a.property
  exact Subtype.ext (congrArg (fun z : G.neighborSet x.val => z.val) ((h x.val).1 (he.trans hy.symm)))

noncomputable def transport (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    {u v : W} (huv : F.Adj u v) (x : {x // f x=u}) : {y // f y=v} :=
  Classical.choose (unique_lift f h huv x)

lemma transport_adj (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    {u v : W} (huv : F.Adj u v) (x : {x // f x=u}) :
    G.Adj x.val (transport f h huv x).val :=
  (Classical.choose_spec (unique_lift f h huv x)).1

lemma transport_reverse (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    {u v : W} (huv : F.Adj u v) (x : {x // f x=u}) :
    transport f h huv.symm (transport f h huv x) = x := by
  exact ((Classical.choose_spec (unique_lift f h huv.symm (transport f h huv x))).2
    x (transport_adj f h huv x).symm).symm

noncomputable def fiberEquiv (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    {u v : W} (huv : F.Adj u v) : {x // f x=u} ≃ {y // f y=v} where
  toFun := transport f h huv
  invFun := transport f h huv.symm
  left_inv := transport_reverse f h huv
  right_inv := transport_reverse f h huv.symm

lemma fiber_card_adj (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    {u v : W} (huv : F.Adj u v) : Nat.card {x // f x=u} = Nat.card {x // f x=v} :=
  Nat.card_congr (fiberEquiv f h huv)

lemma fiber_card_eq (f : G →g F) (h : ∀ x, Function.Bijective (neighborMap f x))
    (hc : F.Preconnected) (u v : W) : Nat.card {x // f x=u} = Nat.card {x // f x=v} := by
  obtain ⟨p⟩ := hc u v
  induction p with
  | nil => rfl
  | cons huv p ih => exact (fiber_card_adj f h huv).trans ih

/-- Uniform fibers give the exact vertex and edge count formulas.
Connectivity is not needed when uniformity is stated explicitly. -/
theorem counts_of_uniform [Fintype V] [Fintype W] (f : G →g F) (hf : IsCover f)
    (t : ℕ) (ht : ∀ w, Nat.card {x // f x=w} = t) :
    Fintype.card V = t*Fintype.card W ∧ Nat.card G.edgeSet = t*Nat.card F.edgeSet := by
  classical
  have htc (w : W) : Fintype.card {x // f x=w} = t := by
    simpa only [Nat.card_eq_fintype_card] using ht w
  have hv : Fintype.card V = t*Fintype.card W := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f),Fintype.card_sigma]
    simp [htc,Nat.mul_comm]
  have hd (w : W) (x : {x // f x=w}) : G.degree x.val = F.degree w := by
    have hh := cover_degree f hf x.val
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,x.property] using hh
  have hs : (∑ x : V, G.degree x) = t*(∑ w : W, F.degree w) := by
    rw [← Fintype.sum_fiberwise f (fun x => G.degree x)]
    simp only [hd,sum_const,card_univ,htc,Nat.nsmul_eq_mul,← mul_sum]
  rw [G.sum_degrees_eq_twice_card_edges,F.sum_degrees_eq_twice_card_edges] at hs
  have he : G.edgeFinset.card = t*F.edgeFinset.card := by nlinarith only [hs]
  refine ⟨hv,?_⟩
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using he

/-- All fibers of a finite cover of a connected base have one positive
cardinality. In particular, the cover has exactly t times as many edges. -/
theorem connected_counts [Fintype V] [Fintype W] (f : G →g F)
    (hf : IsCover f) (hc : F.Connected) :
    ∃ t : ℕ, 0 < t ∧ (∀ w, Nat.card {x // f x=w} = t) ∧
      Fintype.card V = t*Fintype.card W ∧ Nat.card G.edgeSet = t*Nat.card F.edgeSet := by
  obtain ⟨w⟩ := hc.nonempty
  let t := Nat.card {x // f x=w}
  obtain ⟨x,hx⟩ := hf.1 w
  have ht : 0 < t := by
    letI : Nonempty {x // f x=w} := ⟨⟨x,hx⟩⟩
    exact Nat.card_pos
  have htc (v : W) : Nat.card {x // f x=v} = t :=
    fiber_card_eq f hf.2 hc.preconnected v w
  exact ⟨t,ht,htc,counts_of_uniform f hf t htc⟩

/-- The real-power normalization of a positive-sheet cover. -/
lemma normalized_formula {e n t α : ℝ} (hn : 0 < n) (ht : 0 < t) :
    (t*e)/(t*n)^α = (e/n^α)*t^(1-α) := by
  rw [Real.mul_rpow ht.le hn.le,Real.rpow_sub ht,Real.rpow_one]
  field_simp

/-- A nontrivial cover loses a fixed factor at every superlinear power. -/
lemma normalized_le {e n t α : ℝ} (he : 0 ≤ e) (hn : 0 < n)
    (ht : 2 ≤ t) (ha : 1 < α) :
    (t*e)/(t*n)^α ≤ (e/n^α)*2^(1-α) := by
  rw [normalized_formula hn (by linarith : 0 < t)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) ht (by linarith)

#print axioms fiber_card_eq
#print axioms counts_of_uniform
#print axioms connected_counts
#print axioms normalized_formula
#print axioms normalized_le
end Erdos713CoverSheetCounts
