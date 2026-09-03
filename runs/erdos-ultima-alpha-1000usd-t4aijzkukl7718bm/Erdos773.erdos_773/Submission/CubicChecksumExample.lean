import Submission.SidonPairCertificate

/-! An exact finite checksum witness at q=3. No asymptotic construction is asserted. -/
namespace Erdos773.CubicChecksumExample
open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

def root : Fin 27 → ℕ := ![27,28,56,57,4,59,6,7,35,63,10,11,12,40,41,42,16,44,72,73,74,21,76,50,51,25,80]
def roots : Finset ℕ := univ.image root

private def pairs : List (Fin 27 × Fin 27) :=
  [[(4,4), (4,6), (4,7), (6,6), (6,7), (7,7), (4,10), (6,10), (4,11), (7,10), (6,11), (4,12), (7,11), (6,12), (7,12), (10,10), (10,11), (11,11), (10,12), (11,12), (4,16), (12,12), (6,16), (7,16), (10,16), (11,16), (12,16), (4,21), (6,21), (7,21), (16,16), (10,21), (11,21), (12,21), (4,25), (6,25), (7,25), (16,21), (10,25), (0,4), (11,25), (0,6), (12,25), (0,7), (1,4), (1,6), (0,10), (1,7), (0,11), (0,12), (16,25), (21,21), (1,10), (1,11), (1,12), (0,16), (1,16), (21,25), (0,21), (1,21), (4,8), (25,25), (6,8), (7,8), (8,10), (8,11), (0,25), (8,12), (1,25), (0,0), (8,16), (0,1), (1,1), (4,13), (6,13), (7,13), (8,21), (4,14), (10,13), (6,14), (11,13), (7,14), (12,13), (4,15), (10,14), (6,15), (11,14), (7,15), (12,14), (8,25), (13,16), (10,15), (11,15), (12,15), (14,16), (4,17), (0,8), (6,17), (7,17), (1,8)],
   [(15,16), (10,17), (13,21), (11,17), (12,17), (14,21), (16,17), (15,21), (13,25), (14,25), (0,13), (17,21), (1,13), (15,25), (0,14), (8,8), (1,14), (0,15), (4,23), (6,23), (1,15), (7,23), (17,25), (10,23), (4,24), (11,23), (6,24), (12,23), (7,24), (0,17), (10,24), (1,17), (11,24), (12,24), (16,23), (8,13), (16,24), (8,14), (21,23), (8,15), (21,24), (23,25), (2,4), (8,17), (2,6), (2,7), (13,13), (24,25), (0,23), (2,10), (2,11), (3,4), (2,12), (13,14), (1,23), (3,6), (3,7), (0,24), (3,10), (14,14), (13,15), (3,11), (1,24), (2,16), (3,12), (14,15), (4,5), (3,16), (5,6), (15,15), (5,7), (13,17), (2,21), (5,10), (5,11), (14,17), (5,12), (3,21), (15,17), (8,23), (5,16), (2,25), (8,24), (0,2), (17,17), (3,25), (1,2), (5,21), (0,3), (4,9), (6,9), (7,9), (1,3), (9,10), (9,11), (13,23), (5,25), (9,12), (14,23), (13,24)],
   [(0,5), (9,16), (15,23), (1,5), (14,24), (2,8), (15,24), (9,21), (17,23), (3,8), (17,24), (9,25), (0,9), (5,8), (2,13), (1,9), (2,14), (3,13), (2,15), (3,14), (23,23), (3,15), (2,17), (5,13), (23,24), (5,14), (3,17), (8,9), (4,18), (24,24), (6,18), (7,18), (5,15), (10,18), (11,18), (12,18), (4,19), (6,19), (7,19), (5,17), (10,19), (16,18), (11,19), (12,19), (4,20), (6,20), (7,20), (9,13), (10,20), (16,19), (11,20), (12,20), (18,21), (2,23), (9,14), (16,20), (9,15), (2,24), (3,23), (19,21), (4,22), (18,25), (6,22), (7,22), (3,24), (10,22), (11,22), (9,17), (0,18), (20,21), (12,22), (19,25), (1,18), (5,23), (16,22), (0,19), (5,24), (20,25), (1,19), (0,20), (21,22), (1,20), (2,2), (2,3), (22,25), (8,18), (4,26), (6,26), (7,26), (9,23), (3,3), (10,26), (0,22), (11,26), (12,26), (8,19), (1,22), (9,24), (2,5), (16,26)],
   [(8,20), (3,5), (13,18), (21,26), (14,18), (13,19), (15,18), (5,5), (8,22), (14,19), (25,26), (13,20), (15,19), (2,9), (17,18), (0,26), (14,20), (1,26), (3,9), (15,20), (17,19), (13,22), (17,20), (5,9), (14,22), (15,22), (8,26), (18,23), (17,22), (18,24), (19,23), (19,24), (9,9), (20,23), (13,26), (20,24), (14,26), (15,26), (22,23), (2,18), (17,26), (22,24), (3,18), (2,19), (3,19), (2,20), (5,18), (3,20), (5,19), (23,26), (2,22), (5,20), (24,26), (3,22), (9,18), (5,22), (9,19), (9,20), (2,26), (3,26), (9,22), (5,26), (18,18), (9,26), (18,19), (19,19), (18,20), (19,20), (20,20), (18,22), (19,22), (20,22), (22,22), (18,26), (19,26), (20,26), (22,26), (26,26)]].flatten

private theorem pairs_valid : ∀ p ∈ pairs, p.1 ≤ p.2 := by decide +kernel
private theorem pairs_length : (SidonPairCertificate.orderedPairs 27).card ≤ pairs.length := by
  decide +kernel
private theorem pairs_sorted : (pairs.map (SidonPairCertificate.pairSum root)).IsChain (· < ·) := by
  decide +kernel

theorem roots_card : roots.card = 27 := by decide +kernel

theorem root_mem_interval : ∀ r : Fin 27, root r ∈ Icc 1 80 := by decide +kernel

theorem root_residue : ∀ r : Fin 27, root r % 27 = r.val := by decide +kernel

theorem squares_sidon : IsSidon (((roots.image (fun n => n^2)) : Finset ℕ) : Set ℕ) := by
  have hh := SidonPairCertificate.squares_sidon root pairs pairs_valid pairs_length pairs_sorted
  simpa only [roots, Finset.image_image, Function.comp_def] using hh

/-- The table is the graph of this cubic checksum, not an arbitrary 27-root list. -/
def checksum (x y z : ℕ) : ℕ :=
  (1 + z^2 + y + x + 2*x*z^2 + 2*x*y + 2*x*y*z + 2*x*y^2 +
    2*x^2 + 2*x^2*z) % 3

theorem root_formula : ∀ r : Fin 27,
    root r = r.val + 27 * checksum (r.val % 3) (r.val / 3 % 3) (r.val / 9) := by
  decide +kernel

#print axioms root_formula

/-- The same positive-coefficient polynomial, with its modulus changed to q. -/
def uniformRoot (q r : ℕ) : ℕ :=
  let x := r % q
  let y := r / q % q
  let z := r / q^2
  r + q^3 * ((1 + z^2 + y + x + 2*x*z^2 + 2*x*y + 2*x*y*z + 2*x*y^2 +
    2*x^2 + 2*x^2*z) % q)

/-- The finite success at three does not supply a uniform construction. -/
theorem cubic_rule_fails_at_five :
    ¬ IsSidon ((((range 125).image (fun r => uniformRoot 5 r ^ 2)) : Finset ℕ) : Set ℕ) := by
  intro h
  have hmem (r : ℕ) (hr : r < 125) :
      uniformRoot 5 r ^ 2 ∈ (((range 125).image (fun r => uniformRoot 5 r ^ 2)) : Finset ℕ) :=
    mem_image.mpr ⟨r, mem_range.mpr hr, rfl⟩
  have hh := h (uniformRoot 5 0 ^ 2) (hmem 0 (by decide))
    (uniformRoot 5 3 ^ 2) (hmem 3 (by decide))
    (uniformRoot 5 28 ^ 2) (hmem 28 (by decide))
    (uniformRoot 5 45 ^ 2) (hmem 45 (by decide)) (by norm_num [uniformRoot])
  norm_num [uniformRoot] at hh

#print axioms cubic_rule_fails_at_five

theorem finite_lower : 27 ≤ maxSidonSubsetCard ((Icc 1 80).image (fun n : ℕ => n^2)) := by
  have hc : (roots.image (fun n => n^2)).card = 27 := by
    rw [Finset.card_image_of_injective _ (Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0))]
    exact roots_card
  have hsub : roots ⊆ Icc 1 80 := by
    intro n hn
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hn
    exact root_mem_interval r
  rw [← hc]
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.image_subset_image hsub), squares_sidon⟩

#print axioms finite_lower

#print axioms roots_card
#print axioms root_mem_interval
#print axioms root_residue
#print axioms squares_sidon

end Erdos773.CubicChecksumExample
