import Submission.GaussianQuadraticCurveGeometry
import Submission.GaussianFinitePolynomialCover

/-! A bounded-step injective Gaussian-prime ray cannot be covered by a finite
family of nonzero real plane quadratics. A finite-union argument uses repeated
curve labels in short blocks, not an invalid union of individual obstructions. -/
namespace Erdos952Investigation.GaussianQuadraticCurveObstruction
open GaussianQuadraticCurveGeometry GaussianFinitePolynomialCover PiecewiseModularObstruction
open scoped Classical
set_option maxHeartbeats 0
noncomputable section

lemma prime_ray_avoids_finite_lines (S : Finset Line) (hS : ∀ l ∈ S, l.Valid)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ j ≤ L, ∀ l ∈ S, l.eval (x (N+j)) ≠ 0 := by
  let M : S → ℝ := fun l => max |l.val.1| |l.val.2.1|
  have hM (l : S) : 0 < M l := by
    rcases hS l.val l.property with ha | hb
    · exact (abs_pos.mpr ha).trans_le (le_max_left _ _)
    · exact (abs_pos.mpr hb).trans_le (le_max_right _ _)
  let a : S → ℝ := fun l => l.val.1/M l
  let b : S → ℝ := fun l => l.val.2.1/M l
  let c : S → ℝ := fun l => l.val.2.2/M l
  have hab (l : S) : max |a l| |b l| = 1 := by
    dsimp only [a,b]
    rw [abs_div,abs_div,abs_of_pos (hM l),max_div_div_right (hM l).le]
    exact div_self (hM l).ne'
  have heval (l : S) (z : GaussianInt) :
      affine (a l) (b l) (c l) z = l.val.eval z/M l := by
    dsimp only [affine,a,b,c,Line.eval]
    ring
  obtain ⟨N,hN,hclear⟩ := prime_ray_avoids_finite_strips a b c hab x C hx hp 0 (by norm_num) L N₀
  refine ⟨N,hN,?_⟩
  intro j hj l hl he
  have hh := hclear j hj ⟨l,hl⟩
  rw [heval] at hh
  change 0 < |l.eval (x (N+j))/M ⟨l,hl⟩| at hh
  simp only [he,zero_div,abs_zero,lt_self_iff_false] at hh

/-- For a finite quadratic family, all nontrivial short same-curve edges
start on a common finite affine-line family. -/
theorem short_edges_line_cover {J : Type*} [Fintype J]
    (q : J → Quad) (hq : ∀ j, (q j).Nonzero) (B : ℤ) :
    ∃ S : Finset Line, (∀ l ∈ S, l.Valid) ∧
      ∀ j : J, ∀ z w : GaussianInt, z ≠ w → (w-z).norm ≤ B →
        (q j).eval z = 0 → (q j).eval w = 0 → ∃ l ∈ S, l.eval z = 0 := by
  let T := {d : GaussianInt // d.norm ≤ B ∧ d ≠ 0}
  have hTf : {d : GaussianInt | d.norm ≤ B ∧ d ≠ 0}.Finite :=
    (norm_sublevel_finite B).subset (fun _ h => h.1)
  letI : Fintype T := hTf.fintype
  have hlocal (i : J × T) := translated_intersection_line_cover
    (q i.1) (hq i.1) i.2.val i.2.property.2
  choose A hA hcover using hlocal
  let S := Finset.univ.biUnion A
  refine ⟨S,?_,?_⟩
  · intro l hl
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hl
    exact hA i l hi
  · intro j z w hne hb hz hw
    let t : T := ⟨w-z,hb,sub_ne_zero.mpr hne.symm⟩
    have hzw : z+t.val = w := by dsimp [t]; abel
    obtain ⟨l,hl,he⟩ := hcover (j,t) z hz (by simpa only [hzw] using hw)
    exact ⟨l,Finset.mem_biUnion.mpr ⟨(j,t),Finset.mem_univ _,hl⟩,he⟩

/-- No finite union of nonzero real quadratics can contain a Gaussian-prime
ray. This includes reducible quadratics, lines, parabolas and all conics. -/
theorem no_prime_ray_in_finite_quadratic_union {J : Type*} [Fintype J]
    (q : J → Quad) (hq : ∀ j, (q j).Nonzero)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) :
    ¬ ∀ n, ∃ j, (q j).eval (x n) = 0 := by
  intro hcurve
  let K := Fintype.card J
  let C' := max C 0
  let B := C'*(K : ℤ)^2
  obtain ⟨S,hS,hcover⟩ := short_edges_line_cover q hq B
  obtain ⟨N,_,hclear⟩ := prime_ray_avoids_finite_lines S hS x C hx hp K 0
  have hm (i : Fin (K+1)) : ∃ j, (q j).eval (x (N+i.val)) = 0 := hcurve _
  choose c hc using hm
  have hn : ¬ Function.Injective c := by
    intro hi
    have hh := Fintype.card_le_of_injective c hi
    simp only [Fintype.card_fin] at hh
    change K+1 ≤ K at hh
    omega
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hn
  have hneq : x (N+i.val) ≠ x (N+j.val) := by
    intro he
    apply hne
    exact Fin.ext (Nat.add_left_cancel (hx he))
  have hb : (x (N+j.val)-x (N+i.val)).norm ≤ B :=
    norm_block_difference_le x C' (le_max_right _ _) (N+K)
      (fun n _ => (hp n).2.le.trans (le_max_left _ _)) N K i.val j.val
      (by omega) (by omega) le_rfl
  obtain ⟨l,hl,he⟩ := hcover (c i) (x (N+i.val)) (x (N+j.val)) hneq hb (hc i)
    (by simpa only [hij] using hc j)
  exact hclear i.val (by omega) l hl he

/-- Every tail has a vertex outside the whole finite quadratic family. -/
theorem prime_ray_escapes_finite_quadratic_union {J : Type*} [Fintype J]
    (q : J → Quad) (hq : ∀ j, (q j).Nonzero)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (N : ℕ) :
    ∃ n ≥ N, ∀ j, (q j).eval (x n) ≠ 0 := by
  by_contra! hbad
  apply no_prime_ray_in_finite_quadratic_union q hq (fun n => x (N+n)) C
    (fun i j he => Nat.add_left_cancel (hx he))
    (fun n => by simpa only [Nat.add_assoc] using hp (N+n))
  intro n
  exact hbad (N+n) (by omega)

/-- Closure under translations upgrades escape at one vertex to arbitrarily
long blocks avoiding all the prescribed quadratic zero loci. -/
theorem prime_ray_avoids_finite_quadratics {J : Type*} [Fintype J]
    (q : J → Quad) (hq : ∀ j, (q j).Nonzero)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ n ≤ L, ∀ j, (q j).eval (x (N+n)) ≠ 0 := by
  let B := max C 0*(L : ℤ)^2
  let T := {d : GaussianInt // d.norm ≤ B}
  letI : Fintype T := (norm_sublevel_finite B).fintype
  let Q : J × T → Quad := fun j => (q j.1).shift j.2.val
  have hQ (j : J × T) : (Q j).Nonzero := (q j.1).shift_nonzero (hq j.1) j.2.val
  obtain ⟨N,hN,hclear⟩ := prime_ray_escapes_finite_quadratic_union Q hQ x C hx hp N₀
  refine ⟨N,hN,?_⟩
  intro n hn j hz
  have hb : (x (N+n)-x N).norm ≤ B := by
    have hh := GaussianPathLargerSieve.norm_forward_displacement_le x (max C 0)
      (fun k => (hp k).2.le.trans (le_max_left _ _)) N n
    have hn' : (n : ℤ) ≤ (L : ℤ) := by exact_mod_cast hn
    have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hsq : (n : ℤ)^2 ≤ (L : ℤ)^2 := by nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_left hsq (le_max_right _ _))
  let d : T := ⟨x (N+n)-x N,hb⟩
  have hd : x N+d.val = x (N+n) := by dsimp [d]; abel
  apply hclear (j,d)
  change ((q j).shift d.val).eval (x N) = 0
  rw [Quad.eval_shift,hd,hz]

/-- A fixed norm-neighborhood of the Gaussian lattice points on a quadratic
is a finite union of translated quadratic zero loci. This is a lattice-point
neighborhood, not an unproved assertion about tubes around all real points. -/
theorem prime_ray_avoids_quadratic_lattice_neighborhoods {J : Type*} [Fintype J]
    (q : J → Quad) (hq : ∀ j, (q j).Nonzero) (B : ℤ)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ n ≤ L, ∀ j, ∀ w : GaussianInt,
      (q j).eval w = 0 → B < (x (N+n)-w).norm := by
  let T := {d : GaussianInt // d.norm ≤ B}
  letI : Fintype T := (norm_sublevel_finite B).fintype
  let Q : J × T → Quad := fun j => (q j.1).shift (-j.2.val)
  have hQ (j : J × T) : (Q j).Nonzero := (q j.1).shift_nonzero (hq j.1) (-j.2.val)
  obtain ⟨N,hN,hclear⟩ := prime_ray_avoids_finite_quadratics Q hQ x C hx hp L N₀
  refine ⟨N,hN,?_⟩
  intro n hn j w hw
  by_contra! hb
  let d : T := ⟨x (N+n)-w,hb⟩
  have hd : x (N+n)+(-d.val) = w := by dsimp [d]; abel
  apply hclear n hn (j,d)
  change ((q j).shift (-d.val)).eval (x (N+n)) = 0
  rw [Quad.eval_shift,hd,hw]

#print axioms prime_ray_avoids_finite_quadratics
#print axioms prime_ray_avoids_quadratic_lattice_neighborhoods
#print axioms prime_ray_avoids_finite_lines
#print axioms short_edges_line_cover
#print axioms no_prime_ray_in_finite_quadratic_union
#print axioms prime_ray_escapes_finite_quadratic_union
end
end Erdos952Investigation.GaussianQuadraticCurveObstruction
