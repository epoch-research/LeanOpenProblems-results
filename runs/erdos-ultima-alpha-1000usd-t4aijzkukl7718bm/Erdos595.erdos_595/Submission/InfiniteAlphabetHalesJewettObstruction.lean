import Submission.CountableHalesJewettObstruction

/-!
An infinite-alphabet Hales--Jewett statement fails even for TWO colors,
regardless of the dimension. This rules out another possible infinite
partite shortcut, not the conjecture in Spec.lean.
-/

open Set
open scoped BigOperators
namespace Erdos595InfiniteAlphabetHalesJewett
open Erdos595CountableHalesJewett

private noncomputable def fresh {A : Type*} (S : ℕ → Set A)
    (hS : ∀ n, (S n).Infinite) (n : ℕ) : A := by
  classical
  exact ((hS n).exists_notMem_finset ((Finset.range n).attach.image
    (fun k => fresh S hS k.val))).choose
termination_by n
decreasing_by all_goals exact Finset.mem_range.mp k.property

private lemma fresh_spec {A : Type*} (S : ℕ → Set A)
    (hS : ∀ n, (S n).Infinite) (n : ℕ) :
    fresh S hS n ∈ S n ∧ ∀ k < n, fresh S hS n ≠ fresh S hS k := by
  classical
  have h := ((hS n).exists_notMem_finset ((Finset.range n).attach.image
    (fun k => fresh S hS k.val))).choose_spec
  rw [fresh] at ⊢
  refine ⟨h.1, ?_⟩
  intro k hk he
  apply h.2
  exact Finset.mem_image.mpr ⟨⟨k,Finset.mem_range.mpr hk⟩,Finset.mem_attach _ _,he.symm⟩

private lemma fresh_injective {A : Type*} (S : ℕ → Set A)
    (hS : ∀ n, (S n).Infinite) : Function.Injective (fresh S hS) := by
  intro n m he
  rcases lt_trichotomy n m with h | h | h
  · exact ((fresh_spec S hS m).2 n h he.symm).elim
  · exact h
  · exact ((fresh_spec S hS n).2 m h he).elim

/-- A countable family of infinite sets has a simultaneous two-color splitter. -/
theorem split_countable_family {A I : Type*} [Countable I] [Nonempty I]
    (S : I → Set A) (hS : ∀ i, (S i).Infinite) :
    ∃ c : A → Bool, ∀ i, (∃ x ∈ S i, c x = false) ∧ (∃ x ∈ S i, c x = true) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat I
  let T : ℕ → Set A := fun n => S (e (n / 2))
  have hT : ∀ n, (T n).Infinite := fun n => hS _
  let f := fresh T hT
  let c : A → Bool := fun x => decide (∃ n, x = f (2*n))
  refine ⟨c,?_⟩
  intro i
  obtain ⟨n,rfl⟩ := he i
  constructor
  · refine ⟨f (2*n+1),?_,?_⟩
    · have hn : (2*n+1)/2 = n := by omega
      simpa only [T,hn] using (fresh_spec T hT (2*n+1)).1
    · apply decide_eq_false_iff_not.mpr
      rintro ⟨m,hm⟩
      have hh := fresh_injective T hT hm
      omega
  · refine ⟨f (2*n),?_,?_⟩
    · simpa [T] using (fresh_spec T hT (2*n)).1
    · exact decide_eq_true_iff.mpr ⟨n,rfl⟩

structure Quadratic where
  a : ℚ
  b : ℚ
  c : ℚ
  pos : 0 < a
  deriving Countable

instance : Nonempty Quadratic := ⟨⟨1,0,0,by norm_num⟩⟩

def Quadratic.eval (q : Quadratic) (n : ℕ) : ℚ :=
  q.a * (n : ℚ)^2 + q.b * n + q.c

lemma Quadratic.infinite_range (q : Quadratic) : (Set.range q.eval).Infinite := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-q.b / q.a)
  have hNa : -q.b < (N : ℚ) * q.a := (div_lt_iff₀ q.pos).mp hN
  have hmono : StrictMono (fun n : ℕ => q.eval (n+N)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [Quadratic.eval,Nat.cast_add,Nat.cast_one]
    have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg _
    have hN0 : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    have hprod : 0 ≤ q.a * (n : ℚ) := mul_nonneg q.pos.le hn
    have hprodN : 0 ≤ q.a * (N : ℚ) := mul_nonneg q.pos.le hN0
    nlinarith [q.pos]
  exact (Set.infinite_range_of_injective hmono.injective).mono (by
    rintro x ⟨n,rfl⟩
    exact ⟨n+N,rfl⟩)

/-- One two-coloring of Q splits every positive-leading rational quadratic ray. -/
theorem split_quadratics : ∃ c : ℚ → Bool,
    ∀ q : Quadratic, (∃ n, c (q.eval n) = false) ∧ (∃ n, c (q.eval n) = true) := by
  obtain ⟨c,hc⟩ := split_countable_family (fun q : Quadratic => Set.range q.eval)
    Quadratic.infinite_range
  refine ⟨c,?_⟩
  intro q
  obtain ⟨⟨_,⟨n,rfl⟩,hn⟩,⟨_,⟨m,rfl⟩,hm⟩⟩ := hc q
  exact ⟨⟨n,hn⟩,⟨m,hm⟩⟩

lemma sqNorm_pos {I : Type*} (v : I →₀ ℚ) (hv : v ≠ 0) : 0 < sqNorm v := by
  obtain ⟨i,hi⟩ := Finsupp.support_nonempty_iff.mpr hv
  apply Finset.sum_pos' (fun j _ => sq_nonneg (v j))
  exact ⟨i,hi,sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)⟩

/-- The squared coordinate norm along an affine ray is a positive-leading
quadratic, even when the ambient vector space has arbitrary dimension. -/
lemma sqNorm_affine {I : Type*} (x v : I →₀ ℚ) (hv : v ≠ 0) :
    ∃ q : Quadratic, ∀ n : ℕ, sqNorm (x + (n : ℚ) • v) = q.eval n := by
  classical
  let s := x.support ∪ v.support
  have hx : x.support ⊆ s := Finset.subset_union_left
  have hvs : v.support ⊆ s := Finset.subset_union_right
  let q : Quadratic := ⟨sqNorm v,∑ i ∈ s, 2 * x i * v i,sqNorm x,sqNorm_pos v hv⟩
  refine ⟨q,?_⟩
  intro n
  have hsup : (x + (n : ℚ) • v).support ⊆ s :=
    Finsupp.support_add.trans (Finset.union_subset hx (Finsupp.support_smul.trans hvs))
  rw [sqNorm_on _ s hsup]
  change (∑ i ∈ s, (x i + (n : ℚ) * v i)^2) =
    sqNorm v * (n : ℚ)^2 + (∑ i ∈ s, 2 * x i * v i) * n + sqNorm x
  have hp : ∀ i, (x i + (n : ℚ) * v i)^2 =
      (v i)^2 * (n : ℚ)^2 + (2 * x i * v i) * n + (x i)^2 := by intro i; ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← Finset.sum_mul,← Finset.sum_mul,← sqNorm_on v s hvs,← sqNorm_on x s hx]

/-- Every rational vector space has a TWO-coloring with no monochromatic
nonconstant full natural-number affine ray. -/
theorem affine_ray_two_coloring (E : Type*) [AddCommGroup E] [Module ℚ E] :
    ∃ c : E → Bool, ∀ x v, v ≠ 0 →
      ¬∃ k, ∀ n : ℕ, c (x + (n : ℚ) • v) = k := by
  classical
  obtain ⟨d,hd⟩ := split_quadratics
  let b := Module.Free.chooseBasis ℚ E
  refine ⟨fun x => d (sqNorm (b.repr x)),?_⟩
  intro x v hv
  have hv' : b.repr v ≠ 0 := fun h => hv (b.repr.injective (h.trans (map_zero b.repr).symm))
  obtain ⟨q,hq⟩ := sqNorm_affine (b.repr x) (b.repr v) hv'
  obtain ⟨⟨n,hn⟩,⟨m,hm⟩⟩ := hd q
  rintro ⟨k,hk⟩
  have hcol : ∀ j : ℕ, d (q.eval j) = k := by
    intro j
    simpa only [map_add,map_smul,hq] using hk j
  exact Bool.false_ne_true ((hn.symm.trans (hcol n)).trans ((hcol m).symm.trans hm))

/-- Increasing the dimension cannot give a finite-palette Hales--Jewett
theorem for the infinite alphabet N. The palette here has just TWO colors. -/
theorem natural_cube_two_coloring (I : Type*) :
    ∃ c : (I → ℕ) → Bool, ∀ l : Combinatorics.Line ℕ I, ¬l.IsMono c := by
  classical
  obtain ⟨d,hd⟩ := affine_ray_two_coloring (I → ℚ)
  let emb : (I → ℕ) → I → ℚ := fun x i => x i
  refine ⟨fun x => d (emb x),?_⟩
  intro l hl
  let x := emb (l 0)
  let v := emb (l 1) - x
  have hv : v ≠ 0 := by
    obtain ⟨i,hi⟩ := l.proper
    intro he
    have he' := congrFun he i
    norm_num [v,x,emb,Combinatorics.Line.coe_apply,hi] at he'
  have heq : ∀ n : ℕ, emb (l n) = x + (n : ℚ) • v := by
    intro n
    funext i
    cases hi : l.idxFun i with
    | none => simp [x,v,emb,Combinatorics.Line.coe_apply,hi]
    | some a => simp [x,v,emb,Combinatorics.Line.coe_apply,hi]
  apply hd x v hv
  obtain ⟨k,hk⟩ := hl
  refine ⟨k,?_⟩
  intro n
  rw [← heq n]
  exact hk n

#print axioms split_countable_family
#print axioms split_quadratics
#print axioms affine_ray_two_coloring
#print axioms natural_cube_two_coloring
end Erdos595InfiniteAlphabetHalesJewett
