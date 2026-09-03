import Submission.SidonPairCertificate

/-! A finite norm-polynomial checksum example and its failure at another
prime base. Neither result is an asymptotic square-Sidon construction. -/
namespace Erdos773.NormChecksumExample
open Finset Polynomial
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

def cubicNorm (x y z : ℤ) : ℤ :=
  x^3+2*x^2*z-x*y^2-3*x*y*z+x*z^2+y^3-y*z^2+z^3

/-- Determinant of multiplication by x+yθ+zθ², with θ³=θ+1. -/
lemma norm_matrix (x y z : ℤ) :
    (Matrix.of ![![x,z,y],![y,x+z,y+z],![z,y,x+z]]).det=cubicNorm x y z := by
  rw [Matrix.det_fin_three]
  change x*(x+z)*(x+z)-x*(y+z)*y-z*y*(x+z)+z*(y+z)*z+y*y*y-y*(x+z)*z=cubicNorm x y z
  unfold cubicNorm
  ring

def checksumPolynomial (a b c : ℕ) : ℕ :=
  a^3+2*a^2*b+8*a^2*c+6*a^2+a*b^2+7*a*b*c+8*a*b+17*a*c^2+32*a*c+14*a+
  b^3+4*b^2*c+2*b^2+7*b*c^2+14*b*c+8*b+11*c^3+34*c^2+32*c+10

lemma checksum_norm_formula (a b c : ℕ) :
    (checksumPolynomial a b c:ℤ)=cubicNorm ((a:ℤ)+2+2*c) c (b+c)+2*a+2 := by
  unfold checksumPolynomial cubicNorm
  push_cast
  ring

def uniformRoot (q r : ℕ) : ℕ :=
  r+q^3*(checksumPolynomial (r%q) (r/q%q) (r/q^2)%q)

def root : Fin 27 → ℕ := ![27,28,29,3,58,59,6,7,62,9,10,38,12,13,68,15,70,44,45,73,74,48,22,77,24,79,80]
def roots : Finset ℕ := univ.image root

private def pairs : List (Fin 27 × Fin 27) :=
  [[(3,3), (3,6), (3,7), (6,6), (6,7), (3,9), (7,7), (3,10), (6,9), (7,9), (6,10), (7,10), (3,12), (9,9), (3,13), (6,12), (9,10), (7,12), (10,10), (6,13), (7,13), (9,12), (3,15), (10,12), (9,13), (6,15), (10,13), (7,15), (12,12), (9,15), (12,13), (10,15), (13,13), (12,15), (13,15), (15,15), (3,22), (6,22), (7,22), (9,22), (10,22), (3,24), (6,24), (7,24), (12,22), (13,22), (9,24), (10,24), (15,22), (12,24), (0,3), (13,24), (0,6), (0,7), (1,3), (15,24), (0,9), (1,6), (0,10), (1,7), (2,3), (1,9), (0,12)],
   [(2,6), (1,10), (2,7), (0,13), (2,9), (1,12), (2,10), (1,13), (0,15), (22,22), (2,12), (1,15), (2,13), (22,24), (2,15), (24,24), (0,22), (1,22), (0,24), (2,22), (1,24), (2,24), (3,11), (0,0), (6,11), (7,11), (0,1), (9,11), (10,11), (1,1), (0,2), (11,12), (11,13), (1,2), (11,15), (2,2), (11,22), (3,17), (6,17), (7,17), (9,17), (11,24), (3,18), (10,17), (6,18), (7,18), (12,17), (13,17), (9,18), (10,18), (15,17), (12,18), (0,11), (13,18), (1,11), (15,18), (2,11), (3,21), (6,21), (7,21), (9,21), (10,21), (17,22)],
   [(12,21), (13,21), (18,22), (17,24), (15,21), (18,24), (0,17), (1,17), (0,18), (2,17), (21,22), (1,18), (2,18), (21,24), (11,11), (0,21), (1,21), (2,21), (3,4), (11,17), (4,6), (4,7), (4,9), (4,10), (11,18), (3,5), (4,12), (5,6), (5,7), (4,13), (5,9), (5,10), (4,15), (5,12), (5,13), (5,15), (11,21), (4,22), (3,8), (17,17), (6,8), (7,8), (8,9), (4,24), (8,10), (17,18), (5,22), (8,12), (8,13), (18,18), (5,24), (8,15), (0,4), (1,4), (2,4), (0,5), (17,21), (1,5), (2,5), (8,22), (18,21), (8,24), (0,8)],
   [(21,21), (1,8), (3,14), (6,14), (7,14), (2,8), (9,14), (10,14), (12,14), (13,14), (4,11), (14,15), (3,16), (5,11), (6,16), (7,16), (9,16), (10,16), (12,16), (13,16), (14,22), (15,16), (14,24), (8,11), (4,17), (3,19), (0,14), (6,19), (7,19), (16,22), (4,18), (1,14), (9,19), (5,17), (10,19), (2,14), (12,19), (16,24), (3,20), (13,19), (5,18), (6,20), (7,20), (15,19), (9,20), (10,20), (12,20), (0,16), (13,20), (4,21), (1,16), (15,20), (2,16), (8,17), (5,21), (19,22), (8,18), (19,24), (3,23), (20,22), (6,23), (7,23), (9,23)],
   [(10,23), (20,24), (0,19), (11,14), (12,23), (13,23), (1,19), (8,21), (15,23), (2,19), (0,20), (3,25), (1,20), (6,25), (7,25), (2,20), (9,25), (10,25), (11,16), (12,25), (3,26), (13,25), (22,23), (6,26), (7,26), (15,25), (9,26), (10,26), (23,24), (12,26), (14,17), (13,26), (15,26), (14,18), (0,23), (1,23), (22,25), (4,4), (2,23), (11,19), (24,25), (16,17), (4,5), (22,26), (11,20), (16,18), (14,21), (5,5), (0,25), (24,26), (1,25), (2,25), (0,26), (1,26), (16,21), (4,8), (2,26), (17,19), (5,8), (18,19), (11,23), (17,20), (18,20)],
   [(19,21), (11,25), (8,8), (20,21), (11,26), (17,23), (18,23), (4,14), (5,14), (17,25), (21,23), (4,16), (18,25), (17,26), (5,16), (18,26), (8,14), (21,25), (4,19), (21,26), (8,16), (5,19), (4,20), (5,20), (8,19), (14,14), (4,23), (8,20), (5,23), (14,16), (4,25), (5,25), (4,26), (8,23), (16,16), (5,26), (14,19), (8,25), (14,20), (16,19), (8,26), (16,20), (14,23), (19,19), (19,20), (16,23), (14,25), (20,20), (14,26), (16,25), (19,23), (16,26), (20,23), (19,25), (20,25), (19,26), (23,23), (20,26), (23,25), (23,26), (25,25), (25,26), (26,26)]].flatten

private theorem pairs_valid : ∀ p ∈ pairs, p.1 ≤ p.2 := by
  have hh : pairs.all (fun p => decide (p.1 ≤ p.2))=true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using hh
private theorem pairs_length : (SidonPairCertificate.orderedPairs 27).card ≤ pairs.length := by decide +kernel
private theorem pairs_sorted : (pairs.map (SidonPairCertificate.pairSum root)).IsChain (· < ·) := by decide +kernel

theorem roots_card : roots.card=27 := by decide +kernel
theorem root_mem_interval : ∀ r : Fin 27, root r ∈ Icc 1 80 := by decide +kernel
theorem root_formula : ∀ r : Fin 27, root r=uniformRoot 3 r.val := by decide +kernel

theorem squares_sidon : IsSidon (((roots.image (fun n => n^2)) : Finset ℕ) : Set ℕ) := by
  have hh := SidonPairCertificate.squares_sidon root pairs pairs_valid pairs_length pairs_sorted
  simpa only [roots,Finset.image_image,Function.comp_def] using hh

lemma cubic_irreducible_three : Irreducible (X^3-X-1 : (ZMod 3)[X]) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hd : (X^3-X-1 : (ZMod 3)[X]).natDegree=3 := by compute_degree; norm_num
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide)
  have hh : ∀ x : ZMod 3, x^3-x-1 ≠ 0 := by decide +kernel
  intro x
  simpa only [IsRoot,eval_sub,eval_pow,eval_X,eval_one] using hh x

lemma cubic_irreducible_thirteen : Irreducible (X^3-X-1 : (ZMod 13)[X]) := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hd : (X^3-X-1 : (ZMod 13)[X]).natDegree=3 := by compute_degree; norm_num
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide)
  have hh : ∀ x : ZMod 13, x^3-x-1 ≠ 0 := by decide +kernel
  intro x
  simpa only [IsRoot,eval_sub,eval_pow,eval_X,eval_one] using hh x

private lemma collision_not_sidon (f : ℕ → ℕ) (A : Finset ℕ) (a b c d : ℕ)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (he : f a^2+f c^2=f b^2+f d^2) (hab : f a^2 ≠ f b^2) (had : f a^2 ≠ f d^2) :
    ¬IsSidon ((A.image (fun r => f r^2) : Finset ℕ) : Set ℕ) := by
  intro h
  have hm (r : ℕ) (hr : r ∈ A) : f r^2 ∈ A.image (fun r => f r^2) := mem_image.mpr ⟨r,hr,rfl⟩
  rcases h (f a^2) (hm a ha) (f b^2) (hm b hb) (f c^2) (hm c hc) (f d^2) (hm d hd) he with hh | hh
  · exact hab hh.1
  · exact had hh.1

/-- The same norm-polynomial checksum fails even when the cubic remains
irreducible over the new prime field. -/
theorem fails_at_thirteen :
    ¬IsSidon ((((range (13^3)).image (fun r => uniformRoot 13 r ^ 2)) : Finset ℕ) : Set ℕ) := by
  apply collision_not_sidon (uniformRoot 13) (range (13^3)) 3 8 2058 585
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · norm_num [uniformRoot,checksumPolynomial]
  · norm_num [uniformRoot,checksumPolynomial]
  · norm_num [uniformRoot,checksumPolynomial]

/-- The cubic norm checksum also fails at the first nontrivial
power-of-three modulus. This is a finite obstruction, not an asymptotic
statement about all such powers or about Sidon subsets of the family. -/
theorem fails_at_nine :
    ¬IsSidon ((((range (9^3)).image (fun r => uniformRoot 9 r ^ 2)) : Finset ℕ) : Set ℕ) := by
  apply collision_not_sidon (uniformRoot 9) (range (9^3)) 81 87 48 36
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · norm_num [uniformRoot,checksumPolynomial]
  · norm_num [uniformRoot,checksumPolynomial]
  · norm_num [uniformRoot,checksumPolynomial]

/-- An additional exact failure at modulus 27. -/
theorem fails_at_twentyseven :
    ¬IsSidon ((((range (27^3)).image (fun r => uniformRoot 27 r ^ 2)) : Finset ℕ) : Set ℕ) := by
  apply collision_not_sidon (uniformRoot 27) (range (27^3)) 248 286 146 32
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · exact mem_range.mpr (by decide)
  · norm_num [uniformRoot,checksumPolynomial]
  · norm_num [uniformRoot,checksumPolynomial]
  · norm_num [uniformRoot,checksumPolynomial]

#print axioms norm_matrix
#print axioms checksum_norm_formula
#print axioms roots_card
#print axioms root_formula
#print axioms squares_sidon
#print axioms cubic_irreducible_three
#print axioms cubic_irreducible_thirteen
#print axioms fails_at_thirteen
#print axioms fails_at_nine
#print axioms fails_at_twentyseven
end Erdos773.NormChecksumExample
