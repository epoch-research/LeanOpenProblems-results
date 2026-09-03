import Submission.NewmanWeightedQuotient
import Submission.NewmanFinitePrefix

/-! One exact application of the weighted quotient method. This excludes a
particular degree28 divisor, not arbitrary high-degree factors. -/
namespace Erdos406WeightedExample
open Polynomial Erdos406Quotient Erdos406WeightedQuotient Erdos406FinitePrefix
  Erdos406IntegerCuts
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def coefficients : Array ℤ := #[1, 1, 1, 2, 0, 2, -1, -1, -2, 2, 0, -1, -2, 1, -1, 2, 1, 1, 0, 1, -1, -1, 0, 1, -1, 0, 1, -1, 1]
noncomputable def qExample : ℤ[X] := listPoly [1, 1, 1, 2, 0, 2, -1, -1, -2, 2, 0, -1, -2, 1, -1, 2, 1, 1, 0, 1, -1, -1, 0, 1, -1, 0, 1, -1, 1]
def sExample : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, 2, 1, -1, 1, -3, -6, 5, 18, -7, -22, -4, 27, -18, 33, 11, -6, 40, -29, 7, 16, -29, 6, 35, -14, 11, 22, -38, 17, -13, -31, 27, -9, -7, 35, -14, -1, -5, -20, 5, -26, 25, -1, 0, 34, -25, -4, 17, -48, -2]
def eExample : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 1, 1, 0, -1, -2, 2, 1, 0, -2, 0, 0, 4, 1, 1, -1, 0, -1, 0, 0, 3, -2, 1, -5, 1, 1, 4, 0, 2, 1, 0, 0, 3, 0, 0, -2, 1, -1, 3, -1, 0, 1, 2, -2, -1, 0, 0, -1, -1, -49, 13, -40, -133, 116, -245, 130, 66, -134, 133, 178, -131, 100, -95, -59, -69, -6, 29, -82, 97, 56, -124, 101, -2, -69, 63, -46, -2]
def radius : ℚ := 15 / 16
def bounds (i : Fin 48) : ℤ := (#[9, 10, 11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 27, 29, 31, 33, 35, 37, 40, 42, 45, 48, 52, 55, 59, 63, 67, 71, 76, 81, 87, 92, 99, 105, 112, 120, 128, 136, 146, 155, 166, 177, 189, 201] : Array ℤ).getD i.val 0
lemma q_coeff (n : ℕ) : qExample.coeff n = coefficients.getD n 0 := by
  simp [qExample, listPoly_coeff_getD, coefficients]

lemma certificate :
    listPoly sExample * qExample = monomial 32 258 + listPoly eExample := by
  unfold qExample
  apply listPoly_certificate
  decide +kernel

lemma prefix_bound (P R : ℤ[X]) (hPR : P = qExample * R)
    (hP : ∀ i, |P.coeff i| ≤ 1) (i : Fin 48) : |R.coeff i.val| ≤ bounds i := by
  apply weighted_quotient_integer_bound radius (by norm_num [radius]) (by norm_num [radius])
    qExample P R sExample eExample 258 32 i.val (bounds i) hPR certificate hP
  · decide +kernel
  · have hh : ∀ j : Fin 48, weightedWeight radius sExample <
        (|(258 : ℚ)| * radius ^ 32 - weightedWeight radius eExample) *
          radius ^ j.val * ((bounds j : ℚ) + 1) := by decide +kernel
    exact hh i

def rows (i : Fin 82) : Fin 192 :=
  ⟨(#[5, 9, 10, 15, 16, 20, 21, 22, 23, 26, 27, 28, 32, 33, 34, 37, 38, 39, 44, 45, 48, 54, 55, 56, 59, 60, 61, 62, 65, 66, 67, 72, 73, 77, 78, 79, 83, 84, 88, 89, 90, 91, 94, 95, 104, 106, 107, 108, 111, 112, 115, 119, 120, 121, 125, 127, 128, 130, 131, 132, 134, 137, 140, 142, 143, 145, 148, 150, 151, 153, 158, 161, 165, 166, 170, 171, 172, 177, 184, 185, 187, 188] : Array ℕ).getD i.val 0 % 192, Nat.mod_lt _ (by decide)⟩
def weights (i : Fin 82) : ℤ := (#[1016440096, 410889391, 101175885, 38976729, 83276116, 14304750, 6433277, 4502095, 3661254, 2632491, 6305196, 663851, 146962, 936110, 656991, 73980, 362564, 126876, 76144, 87019, 4294967296, 171171736, 730457801, 131895431, 74686784, 16094743, 37916006, 72792501, 3664610, 51408714, 11222584, 6878405, 8065950, 2417446, 1139179, 237349, 558848, 711324, 30999, 93605, 109128, 13662, 23323, 63696, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 47058, 1, 87019, 63696, 3, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 102855, 12449] : Array ℤ).getD i.val 0

theorem not_dvd_newman (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) : ¬ qExample ∣ P := by
  rintro ⟨R, hPR⟩
  have hb := prefix_bound P R hPR (fun i => by
    rcases hP i with h | h <;> rw [h] <;> norm_num)
  have hp (i : ℕ) : 0 ≤ P.coeff i ∧ P.coeff i ≤ 1 := by
    rcases hP i with h | h <;> rw [h] <;> norm_num
  have hv := initial_valid (by decide : 0 < 48) coefficients bounds qExample P R
    q_coeff hPR h0 hp hb
  exact selected_contradiction (matrix coefficients) (state bounds) rows weights
    (fun j => R.coeff j.val) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hv

lemma eval_three : qExample.eval 3 = (2 : ℤ) ^ 44 := by
  norm_num [qExample, listPoly]

#print axioms prefix_bound
#print axioms not_dvd_newman
#print axioms eval_three
end Erdos406WeightedExample
