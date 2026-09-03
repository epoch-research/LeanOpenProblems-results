import Submission.MvPolynomialPeriod
import Submission.GaussianQuadraticCurveObstruction

/-! An injective bounded-step Gaussian-prime ray has arbitrarily long blocks
avoiding any prescribed finite union of nonzero real algebraic curves.
The proof uses finite differences and induction on degree, not irreducible
factorization or an assumed classification of arbitrary prime paths. -/
namespace Erdos952Investigation.GaussianAlgebraicCurveObstruction
open MvPolynomial MvPolynomialTranslation MvPolynomialPeriod
open GaussianQuadraticCurveGeometry GaussianQuadraticCurveObstruction
open GaussianFinitePolynomialCover
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- The short edges on degree-at-most `D+1` curves start on finitely many
lower-degree curves or proper affine lines. -/
lemma short_edges_cover (D : ℕ) (S : Finset PlanePoly)
    (hS : ∀ p ∈ S, p ≠ 0 ∧ p.totalDegree ≤ D+1) (B : ℤ) :
    ∃ R : Finset PlanePoly, (∀ p ∈ R, p ≠ 0 ∧ p.totalDegree ≤ D) ∧
      ∃ T : Finset Line, (∀ l ∈ T, l.Valid) ∧
        ∀ p ∈ S, ∀ z w : GaussianInt, z ≠ w → (w-z).norm ≤ B →
          evalG p z = 0 → evalG p w = 0 →
            (∃ r ∈ R, evalG r z = 0) ∨ (∃ l ∈ T, l.eval z = 0) := by
  let V := {d : GaussianInt // d.norm ≤ B ∧ d ≠ 0}
  letI : Fintype V := ((norm_sublevel_finite B).subset (fun _ h => h.1)).fintype
  have hlocal (j : S × V) :
      ∃ R : Finset PlanePoly, (∀ p ∈ R, p ≠ 0 ∧ p.totalDegree ≤ D) ∧
        ∃ T : Finset Line, (∀ l ∈ T, l.Valid) ∧ ∀ z : GaussianInt,
          evalG j.1.val z = 0 → evalG j.1.val (z+j.2.val) = 0 →
            (∃ r ∈ R, evalG r z = 0) ∨ (∃ l ∈ T, l.eval z = 0) := by
    let r := shift j.2.val j.1.val-j.1.val
    by_cases hr : r = 0
    · have he : shift j.2.val j.1.val = j.1.val := sub_eq_zero.mp hr
      obtain ⟨T,hT,heval⟩ := invariant_line_cover j.1.val (hS _ j.1.property).1
        j.2.val j.2.property.2 he
      exact ⟨∅,by simp,T,hT,fun z hz _ => Or.inr (heval z hz)⟩
    · refine ⟨{r},?_,∅,by simp,?_⟩
      · intro p hp
        obtain rfl := Finset.mem_singleton.mp hp
        exact ⟨hr,Nat.lt_succ_iff.mp
          ((totalDegree_difference_lt _ _ hr).trans_le (hS _ j.1.property).2)⟩
      · intro z hz hw
        left
        refine ⟨r,Finset.mem_singleton_self _,?_⟩
        change eval (coords z) (shift j.2.val j.1.val-j.1.val) = 0
        rw [map_sub]
        change evalG (shift j.2.val j.1.val) z-evalG j.1.val z = 0
        rw [evalG_shift,hw,hz,sub_self]
  choose R hR T hT he using hlocal
  refine ⟨Finset.univ.biUnion R,?_,Finset.univ.biUnion T,?_,?_⟩
  · intro p hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    exact hR j p hj
  · intro l hl
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hl
    exact hT j l hj
  · intro p hp z w hzw hb hz hw
    let j : S × V := (⟨p,hp⟩,⟨w-z,hb,sub_ne_zero.mpr hzw.symm⟩)
    have hj : z+j.2.val = w := by dsimp [j]; abel
    rcases he j z hz (by simpa only [hj] using hw) with ⟨r,hr,hev⟩ | ⟨l,hl,hev⟩
    · exact Or.inl ⟨r,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hr⟩,hev⟩
    · exact Or.inr ⟨l,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hl⟩,hev⟩

def lineShift (l : Line) (d : GaussianInt) : Line :=
  (l.1,l.2.1,l.2.2+l.1*(d.re : ℝ)+l.2.1*(d.im : ℝ))

lemma lineShift_valid (l : Line) (hl : l.Valid) (d : GaussianInt) :
    (lineShift l d).Valid := hl

lemma lineShift_eval (l : Line) (z d : GaussianInt) :
    (lineShift l d).eval z = l.eval (z+d) := by
  simp only [lineShift,Line.eval,Zsqrtd.re_add,Zsqrtd.im_add,Int.cast_add]
  ring

def ClearAt (S : Finset PlanePoly) (T : Finset Line) (z : GaussianInt) : Prop :=
  (∀ p ∈ S, evalG p z ≠ 0) ∧ (∀ l ∈ T, l.eval z ≠ 0)

def Escape (D : ℕ) : Prop :=
  ∀ S : Finset PlanePoly, (∀ p ∈ S, p ≠ 0 ∧ p.totalDegree ≤ D) →
    ∀ T : Finset Line, (∀ l ∈ T, l.Valid) →
      ∀ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x →
        (∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) → ∀ N₀ : ℕ,
          ∃ N ≥ N₀, ClearAt S T (x N)

def Clear (D : ℕ) : Prop :=
  ∀ S : Finset PlanePoly, (∀ p ∈ S, p ≠ 0 ∧ p.totalDegree ≤ D) →
    ∀ T : Finset Line, (∀ l ∈ T, l.Valid) →
      ∀ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x →
        (∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) → ∀ L N₀ : ℕ,
          ∃ N ≥ N₀, ∀ j ≤ L, ClearAt S T (x (N+j))

lemma clear_of_escape (D : ℕ) (h : Escape D) : Clear D := by
  intro S hS T hT x C hx hp L N₀
  let B := max C 0*(L : ℤ)^2
  let V := {d : GaussianInt // d.norm ≤ B}
  letI : Fintype V := (norm_sublevel_finite B).fintype
  let R := Finset.univ.image (fun j : S × V => shift j.2.val j.1.val)
  let U := Finset.univ.image (fun j : T × V => lineShift j.1.val j.2.val)
  have hR : ∀ p ∈ R, p ≠ 0 ∧ p.totalDegree ≤ D := by
    intro p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨shift_ne_zero _ (hS _ j.1.property).1 _,?_⟩
    change (translate (coords j.2.val) j.1.val).totalDegree ≤ D
    rw [totalDegree_translate]
    exact (hS _ j.1.property).2
  have hU : ∀ l ∈ U, l.Valid := by
    intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact lineShift_valid _ (hT _ j.1.property) _
  obtain ⟨N,hN,hclear⟩ := h R hR U hU x C hx hp N₀
  refine ⟨N,hN,?_⟩
  intro j hj
  have hb : (x (N+j)-x N).norm ≤ B := by
    have hh := GaussianPathLargerSieve.norm_forward_displacement_le x (max C 0)
      (fun k => (hp k).2.le.trans (le_max_left _ _)) N j
    have hj' : (j : ℤ) ≤ (L : ℤ) := by exact_mod_cast hj
    have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hsq : (j : ℤ)^2 ≤ (L : ℤ)^2 := by nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_left hsq (le_max_right _ _))
  let v : V := ⟨x (N+j)-x N,hb⟩
  have hv : x N+v.val = x (N+j) := by dsimp [v]; abel
  constructor
  · intro p hps he
    have hm : shift v.val p ∈ R := Finset.mem_image.mpr ⟨(⟨p,hps⟩,v),Finset.mem_univ _,rfl⟩
    apply hclear.1 _ hm
    rw [evalG_shift,hv,he]
  · intro l hlt he
    have hm : lineShift l v.val ∈ U := Finset.mem_image.mpr ⟨(⟨l,hlt⟩,v),Finset.mem_univ _,rfl⟩
    apply hclear.2 _ hm
    rw [lineShift_eval,hv,he]

lemma escape_zero : Escape 0 := by
  intro S hS T hT x C hx hp N₀
  obtain ⟨N,hN,hclear⟩ := prime_ray_avoids_finite_lines T hT x C hx hp 0 N₀
  refine ⟨N,hN,?_,?_⟩
  · intro p hps hz
    have hd : p.totalDegree = 0 := Nat.eq_zero_of_le_zero (hS p hps).2
    have he := totalDegree_eq_zero_iff_eq_C.mp hd
    have hc : coeff 0 p ≠ 0 := by
      intro hc
      apply (hS p hps).1
      rw [he,hc,map_zero]
    apply hc
    change eval (coords (x N)) p = 0 at hz
    rwa [he,eval_C] at hz
  · intro l hl
    simpa only [Nat.add_zero] using hclear 0 le_rfl l hl

lemma escape_succ_of_clear (D : ℕ) (h : Clear D) : Escape (D+1) := by
  intro S hS T hT x C hx hp N₀
  by_contra hno
  have hbad (n : ℕ) (hn : N₀ ≤ n) : ¬ ClearAt S T (x n) := by
    intro he
    exact hno ⟨n,hn,he⟩
  let K := S.card
  let B := max C 0*(K : ℤ)^2
  obtain ⟨R,hR,U,hU,hcover⟩ := short_edges_cover D S hS B
  obtain ⟨N,hN,hclear⟩ := h R hR (T∪U)
    (fun l hl => (Finset.mem_union.mp hl).elim (hT l) (hU l)) x C hx hp K N₀
  have hm (i : Fin (K+1)) : ∃ p : S, evalG p.val (x (N+i.val)) = 0 := by
    by_contra! he
    apply hbad (N+i.val) (by omega)
    constructor
    · intro p hp
      exact he ⟨p,hp⟩
    · intro l hl
      exact (hclear i.val (by omega)).2 l (Finset.mem_union_left _ hl)
  choose f hf using hm
  have hn : ¬ Function.Injective f := by
    intro hi
    have hh := Fintype.card_le_of_injective f hi
    simp only [Fintype.card_fin,Fintype.card_coe] at hh
    change K+1 ≤ K at hh
    omega
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hn
  have hneq : x (N+i.val) ≠ x (N+j.val) := by
    intro he
    apply hne
    exact Fin.ext (Nat.add_left_cancel (hx he))
  have hb : (x (N+j.val)-x (N+i.val)).norm ≤ B :=
    norm_block_difference_le x (max C 0) (le_max_right _ _) (N+K)
      (fun n _ => (hp n).2.le.trans (le_max_left _ _)) N K i.val j.val
      (by omega) (by omega) le_rfl
  rcases hcover (f i).val (f i).property (x (N+i.val)) (x (N+j.val)) hneq hb
      (hf i) (by simpa only [hij] using hf j) with ⟨r,hr,he⟩ | ⟨l,hl,he⟩
  · exact (hclear i.val (by omega)).1 r hr he
  · exact (hclear i.val (by omega)).2 l (Finset.mem_union_right _ hl) he

lemma clear_all_degrees (D : ℕ) : Clear D := by
  induction D with
  | zero => exact clear_of_escape 0 escape_zero
  | succ D ih => exact clear_of_escape (D+1) (escape_succ_of_clear D ih)

/-- Arbitrarily long blocks avoid any finite family of nonzero real plane
polynomials, and any additional finite family of proper affine lines. -/
theorem prime_ray_avoids_finite_algebraic_curves (S : Finset PlanePoly)
    (hS : ∀ p ∈ S, p ≠ 0) (T : Finset Line) (hT : ∀ l ∈ T, l.Valid)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ j ≤ L, ClearAt S T (x (N+j)) := by
  apply clear_all_degrees (S.sup MvPolynomial.totalDegree) S _ T hT x C hx hp L N₀
  intro p hp
  exact ⟨hS p hp,Finset.le_sup (f := MvPolynomial.totalDegree) hp⟩

/-- In particular, the entire ray cannot lie in a finite algebraic union. -/
theorem no_prime_ray_in_finite_algebraic_union (S : Finset PlanePoly)
    (hS : ∀ p ∈ S, p ≠ 0) (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) :
    ¬ ∀ n, ∃ p ∈ S, evalG p (x n) = 0 := by
  intro hbad
  obtain ⟨N,_,hclear⟩ := prime_ray_avoids_finite_algebraic_curves S hS ∅ (by simp)
    x C hx hp 0 0
  obtain ⟨p,hps,he⟩ := hbad N
  exact (hclear 0 le_rfl).1 p hps (by simpa only [Nat.add_zero] using he)


/-- Arbitrarily long blocks also avoid fixed norm-neighborhoods of the
Gaussian lattice zeros. This does not assert a bound on distances to
non-lattice real points of the continuous curves. -/
theorem prime_ray_avoids_algebraic_lattice_neighborhoods (S : Finset PlanePoly)
    (hS : ∀ p ∈ S, p ≠ 0) (B : ℤ)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ j ≤ L, ∀ p ∈ S, ∀ w : GaussianInt,
      evalG p w = 0 → B < (x (N+j)-w).norm := by
  let V := {d : GaussianInt // d.norm ≤ B}
  letI : Fintype V := (norm_sublevel_finite B).fintype
  let R := Finset.univ.image (fun i : S × V => shift (-i.2.val) i.1.val)
  have hR : ∀ p ∈ R, p ≠ 0 := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact shift_ne_zero _ (hS _ i.1.property) _
  obtain ⟨N,hN,hclear⟩ := prime_ray_avoids_finite_algebraic_curves R hR ∅ (by simp)
    x C hx hp L N₀
  refine ⟨N,hN,?_⟩
  intro j hj p hps w hw
  by_contra! hb
  let v : V := ⟨x (N+j)-w,hb⟩
  have hv : x (N+j)+(-v.val) = w := by dsimp [v]; abel
  have hm : shift (-v.val) p ∈ R :=
    Finset.mem_image.mpr ⟨(⟨p,hps⟩,v),Finset.mem_univ _,rfl⟩
  apply (hclear j hj).1 _ hm
  rw [evalG_shift,hv,hw]

#print axioms prime_ray_avoids_algebraic_lattice_neighborhoods

#print axioms prime_ray_avoids_finite_algebraic_curves
#print axioms no_prime_ray_in_finite_algebraic_union
end
end Erdos952Investigation.GaussianAlgebraicCurveObstruction
