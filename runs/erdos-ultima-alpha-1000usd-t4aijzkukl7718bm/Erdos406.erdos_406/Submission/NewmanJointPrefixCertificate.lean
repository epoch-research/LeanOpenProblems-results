import Submission.NewmanJointFlipRigidity
import Submission.NewmanFinitePrefix

/-! Kernel-checkable finite-prefix exclusions using both a factor and its
reciprocal. Empty frontiers exclude all polynomial multiples, without any
bound on the degree or coefficients of the quotient. -/
namespace Erdos406JointPrefix
open Polynomial Erdos406ReciprocalFlip Erdos406FinitePrefix Erdos406Quotient

/-- Quotient coefficients already chosen, in increasing index order. -/
def quotPrefix (R : ℤ[X]) (n : ℕ) : List ℤ := List.ofFn (fun i : Fin n => R.coeff i.val)

@[simp] lemma length_prefix (R : ℤ[X]) (n : ℕ) : (quotPrefix R n).length = n := by
  simp [quotPrefix]

lemma prefix_getD (R : ℤ[X]) (n i : ℕ) (hi : i < n) :
    (quotPrefix R n).getD i 0 = R.coeff i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [quotPrefix]

lemma prefix_succ (R : ℤ[X]) (n : ℕ) :
    quotPrefix R (n+1) = quotPrefix R n ++ [R.coeff n] := by
  simp only [quotPrefix, List.ofFn_succ', List.concat_eq_append]
  rfl

def past (q w : List ℤ) : ℤ :=
  ∑ i ∈ Finset.range w.length, q.getD (w.length-i) 0 * w.getD i 0

def next (q a w : List ℤ) : List (List ℤ) :=
  (([-past q w, 1-past q w] : List ℤ).filter
    (fun v => decide (v+past a w = 0 ∨ v+past a w = 1))).map (fun v => w++[v])

def frontier (q a : List ℤ) : ℕ → List (List ℤ)
  | 0 => [[1]]
  | n+1 => (frontier q a n).flatMap (next q a)

lemma coefficient_from_past (Q R : ℤ[X]) (q : List ℤ) (n : ℕ)
    (hQ0 : Q.coeff 0 = 1) (hq : ∀ i ≤ n, Q.coeff i = q.getD i 0) :
    (Q*R).coeff n = R.coeff n + past q (quotPrefix R n) := by
  rw [mul_comm Q R, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => R.coeff i * Q.coeff j) n, Finset.sum_range_succ]
  simp only [Nat.sub_self, hQ0, mul_one]
  rw [add_comm]
  congr 1
  unfold past
  rw [length_prefix]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq (n-i) (Nat.sub_le n i), prefix_getD R n i (Finset.mem_range.mp hi)]
  ring

lemma next_contains (q a w : List ℤ) (v : ℤ)
    (hq : v+past q w = 0 ∨ v+past q w = 1)
    (ha : v+past a w = 0 ∨ v+past a w = 1) :
    w++[v] ∈ next q a w := by
  apply List.mem_map.mpr
  refine ⟨v, ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · simpa using ha

/-- Every genuine quotient gives a path through all the checked frontiers. -/
theorem frontier_contains (Q A R : ℤ[X]) (q a : List ℤ) (N : ℕ)
    (hQ0 : Q.coeff 0 = 1) (hA0 : A.coeff 0 = 1) (hR0 : R.coeff 0 = 1)
    (hq : ∀ i ≤ N, Q.coeff i = q.getD i 0)
    (ha : ∀ i ≤ N, A.coeff i = a.getD i 0)
    (hP : Binary (Q*R)) (hS : Binary (A*R)) :
    quotPrefix R (N+1) ∈ frontier q a N := by
  induction N with
  | zero => simp [quotPrefix, frontier, List.ofFn_succ, hR0]
  | succ N ih =>
    have hprev := ih (fun i hi => hq i (by omega)) (fun i hi => ha i (by omega))
    rw [frontier, List.mem_flatMap]
    refine ⟨quotPrefix R (N+1), hprev, ?_⟩
    rw [prefix_succ R (N+1)]
    apply next_contains
    · have hh := hP (N+1)
      rwa [coefficient_from_past Q R q (N+1) hQ0 hq] at hh
    · have hh := hS (N+1)
      rwa [coefficient_from_past A R a (N+1) hA0 ha] at hh

/-- This certificate excludes an entire class of end-coefficient patterns,
not only one fixed-degree polynomial. -/
theorem exclude_of_empty_frontier (q a : List ℤ) (N : ℕ)
    (hfirst : q.getD 0 0 = 1) (halast : a.getD 0 0 = 1)
    (hempty : frontier q a N = []) (Q : ℤ[X])
    (hq : ∀ i ≤ N, Q.coeff i = q.getD i 0)
    (ha : ∀ i ≤ N, Q.reverse.coeff i = a.getD i 0)
    (P : ℤ[X]) (hP : Binary P) (hP0 : P.coeff 0 = 1) : ¬ Q ∣ P := by
  rintro ⟨R, he⟩
  have hQ0 : Q.coeff 0 = 1 := (hq 0 (by omega)).trans hfirst
  have hA0 : Q.reverse.coeff 0 = 1 := (ha 0 (by omega)).trans halast
  have hR0 : R.coeff 0 = 1 := by
    rw [he, mul_coeff_zero, hQ0, one_mul] at hP0
    exact hP0
  have hQR : Binary (Q*R) := by rwa [← he]
  have hf := frontier_contains Q Q.reverse R q a N hQ0 hA0 hR0 hq ha hQR
    (binary_factor_flip Q R hQR)
  rw [hempty] at hf
  exact List.not_mem_nil hf

lemma listPoly_shape_of_last_one (q : List ℤ)
    (hlast : q.getD (q.length-1) 0 = 1) :
    (listPoly q).IsMonicOfDegree (q.length-1) := by
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [listPoly_coeff_getD, List.getD_eq_default _ _ (by omega)]
  · rwa [listPoly_coeff_getD]

lemma listPoly_reverse_of_last_one (q : List ℤ)
    (hlast : q.getD (q.length-1) 0 = 1) :
    (listPoly q).reverse = listPoly q.reverse := by
  have hlen : 0 < q.length := by
    by_contra hh
    have he : q = [] := List.length_eq_zero_iff.mp (by omega)
    simp [he] at hlast
  have hd := (listPoly_shape_of_last_one q hlast).natDegree_eq
  ext n
  by_cases hn : n < q.length
  · rw [coeff_reverse, hd, revAt_le (by omega), listPoly_coeff_getD,
      listPoly_coeff_getD, List.getD_reverse n hn]
  · have hb := (listPoly q).reverse_natDegree_le
    rw [coeff_eq_zero_of_natDegree_lt (by omega : (listPoly q).reverse.natDegree < n),
      listPoly_coeff_getD, List.getD_eq_default _ _ (by simp; omega)]

/-- A certificate for a fixed coefficient list, with no bound on the
putative binary multiple. -/
theorem listPoly_exclude_of_empty_frontier (q : List ℤ) (N : ℕ)
    (hfirst : q.getD 0 0 = 1) (hlast : q.getD (q.length-1) 0 = 1)
    (hempty : frontier q q.reverse N = [])
    (P : ℤ[X]) (hP : Binary P) (hP0 : P.coeff 0 = 1) : ¬ listPoly q ∣ P := by
  have hlen : 0 < q.length := by
    by_contra hh
    have he : q = [] := List.length_eq_zero_iff.mp (by omega)
    simp [he] at hfirst
  apply exclude_of_empty_frontier q q.reverse N hfirst _ hempty (listPoly q)
    (fun i _ => listPoly_coeff_getD q i) _ P hP hP0
  · rw [List.getD_reverse 0 hlen]
    simpa using hlast
  · intro i _
    rw [listPoly_reverse_of_last_one q hlast, listPoly_coeff_getD]

/-- Explicit intermediate frontiers avoid recomputing nested frontiers
inside kernel reduction. The last frontier must be empty. -/
def follows (q a : List ℤ) : List (List ℤ) → List (List (List ℤ)) → Bool
  | w, [] => decide (w = [])
  | w, v::vs => decide (w.flatMap (next q a) = v) && follows q a v vs

lemma follows_empty (q a : List ℤ) (vs : List (List (List ℤ))) :
    ∀ (w : List (List ℤ)) (n : ℕ), frontier q a n = w → follows q a w vs = true →
      frontier q a (n+vs.length) = [] := by
  induction vs with
  | nil =>
    intro w n hn hf
    have hw : w = [] := by simpa [follows] using hf
    simpa only [List.length_nil, Nat.add_zero] using hn.trans hw
  | cons v vs ih =>
    intro w n hn hf
    have hh : w.flatMap (next q a) = v ∧ follows q a v vs = true := by
      simpa only [follows, Bool.and_eq_true, decide_eq_true_eq] using hf
    have hnext : frontier q a (n+1) = v := by rw [frontier, hn, hh.1]
    have hs := ih v (n+1) hnext hh.2
    convert hs using 1; simp [Nat.add_comm, Nat.add_left_comm]

lemma frontier_empty_of_follows (q a : List ℤ) (vs : List (List (List ℤ)))
    (hf : follows q a [[1]] vs = true) : frontier q a vs.length = [] := by
  simpa only [Nat.zero_add] using follows_empty q a vs [[1]] 0 rfl hf

#print axioms frontier_contains
#print axioms exclude_of_empty_frontier
#print axioms listPoly_exclude_of_empty_frontier
#print axioms frontier_empty_of_follows
end Erdos406JointPrefix
