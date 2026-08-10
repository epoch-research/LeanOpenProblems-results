import FormalConjectures.Util.ProblemImports

open Nat List Finset

/-- A003415(n): The function $n \cdot \sum_{p \mid n} v_p(n)/p$, calculated as $\sum_{p \mid n} v_p(n) \cdot \frac{n}{p}$. -/
def A003415 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (n.factorization.support).sum fun p => (n / p) * (n.factorization p)

/-- A359550(n) is 1 if $n$ is not divisible by any $p^p$, and 0 otherwise. -/
def A359550 (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else if (Finset.filter (fun p => n.factorization p ≥ p) n.factorization.support).card > 0
  then 0 else 1

/-- A085731(n): $\gcd(\mathtt{A003415}(n), n)$. -/
def A085731 (n : ℕ) : ℕ := Nat.gcd (A003415 n) n

/-- A376418(n): Number of $k \ge 1$ such that $k^k \mid n$. -/
def A376418 (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => k ≥ 1 ∧ Pow.pow k k ∣ n) (Finset.range (n + 2))).card

/-- Intermediate type for the values of the function $f(n)$ used in the RGS transform. -/
inductive A379240_F_val : Type
  | case_n (val : ℕ) : A379240_F_val
  | case_pair (a b : ℕ) : A379240_F_val
deriving DecidableEq

/-- The function $f(n)$ whose Restricted Growth Sequence transform is A379240. -/
def A379240_f (n : ℕ) : A379240_F_val :=
  if n = 0 then A379240_F_val.case_n 0
  else
    if A359550 n = 1 then
      A379240_F_val.case_pair (A003415 n) (A085731 n)
    else
      A379240_F_val.case_n n

/--
The Restricted Growth Sequence (RGS) Transform of a sequence $f: \mathbb{N}_{\ge 1} \to \alpha$.
$a(n)$ is 1 plus the index of $f(n)$ in the list of distinct values of $f(1), \dots, f(n)$,
ordered by first appearance.
-/
def rgs_transform {α : Type} [DecidableEq α] (f : ℕ → α) (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let f_prefix : List α := (List.range n).map (fun i => f (i + 1))
    let distinct_f_values : List α := f_prefix.dedup
    let target_f_val : α := f n
    -- List.idxOf returns the 0-based index.
    distinct_f_values.idxOf target_f_val + 1

/--
A379240: Lexicographically earliest infinite sequence such that $a(i) = a(j) \Rightarrow f(i) = f(j)$,
for all $i, j$, where
$$f(n) = \begin{cases} [\mathtt{A003415}(n), \mathtt{A085731}(n)] & \text{if } \mathtt{A359550}(n) = 1 \\ n & \text{otherwise} \end{cases}$$
This is the Restricted Growth Sequence transform of $f$.
-/
def A379240 (n : ℕ) : ℕ :=
  rgs_transform A379240_f n

-- Auxiliary function for the conjectured RGS triple
def A379240_conj_f_triple (n : ℕ) : ℕ × ℕ × ℕ :=
  (A003415 n, A085731 n, A376418 n)

/--
The Restricted Growth Sequence transform of the triple
$[\mathtt{A003415}(n), \mathtt{A085731}(n), \mathtt{A376418}(n)]$.
-/
def A379240_conjecture (n : ℕ) : ℕ :=
  rgs_transform A379240_conj_f_triple n


@[simp] private lemma A376418_eval_1 : A376418 1 = 1 := by
  decide
@[simp] private lemma A376418_eval_2 : A376418 2 = 1 := by
  decide
@[simp] private lemma A376418_eval_3 : A376418 3 = 1 := by
  decide
@[simp] private lemma A376418_eval_4 : A376418 4 = 2 := by
  decide
@[simp] private lemma A376418_eval_5 : A376418 5 = 1 := by
  decide
@[simp] private lemma A376418_eval_6 : A376418 6 = 1 := by
  decide
@[simp] private lemma A376418_eval_7 : A376418 7 = 1 := by
  decide
@[simp] private lemma A376418_eval_8 : A376418 8 = 2 := by
  decide
@[simp] private lemma A376418_eval_9 : A376418 9 = 1 := by
  decide
@[simp] private lemma A376418_eval_10 : A376418 10 = 1 := by
  decide
@[simp] private lemma A376418_eval_11 : A376418 11 = 1 := by
  decide
@[simp] private lemma A376418_eval_12 : A376418 12 = 2 := by
  decide
@[simp] private lemma A376418_eval_13 : A376418 13 = 1 := by
  decide
@[simp] private lemma A376418_eval_14 : A376418 14 = 1 := by
  decide
@[simp] private lemma A376418_eval_15 : A376418 15 = 1 := by
  decide
@[simp] private lemma A376418_eval_16 : A376418 16 = 2 := by
  decide
@[simp] private lemma A376418_eval_17 : A376418 17 = 1 := by
  decide
@[simp] private lemma A376418_eval_18 : A376418 18 = 1 := by
  decide
@[simp] private lemma A376418_eval_19 : A376418 19 = 1 := by
  decide
@[simp] private lemma A376418_eval_20 : A376418 20 = 2 := by
  decide
@[simp] private lemma A376418_eval_21 : A376418 21 = 1 := by
  decide
@[simp] private lemma A376418_eval_22 : A376418 22 = 1 := by
  decide
@[simp] private lemma A376418_eval_23 : A376418 23 = 1 := by
  decide
@[simp] private lemma A376418_eval_24 : A376418 24 = 2 := by
  decide
@[simp] private lemma A376418_eval_25 : A376418 25 = 1 := by
  decide
@[simp] private lemma A376418_eval_26 : A376418 26 = 1 := by
  decide
@[simp] private lemma A376418_eval_27 : A376418 27 = 2 := by
  decide
@[simp] private lemma A376418_eval_28 : A376418 28 = 2 := by
  decide
@[simp] private lemma A376418_eval_29 : A376418 29 = 1 := by
  decide
@[simp] private lemma A376418_eval_30 : A376418 30 = 1 := by
  decide
@[simp] private lemma A376418_eval_31 : A376418 31 = 1 := by
  decide
@[simp] private lemma A376418_eval_32 : A376418 32 = 2 := by
  decide
@[simp] private lemma A376418_eval_33 : A376418 33 = 1 := by
  decide
@[simp] private lemma A376418_eval_34 : A376418 34 = 1 := by
  decide
@[simp] private lemma A376418_eval_35 : A376418 35 = 1 := by
  decide
@[simp] private lemma A376418_eval_36 : A376418 36 = 2 := by
  decide
@[simp] private lemma A376418_eval_37 : A376418 37 = 1 := by
  decide
@[simp] private lemma A376418_eval_38 : A376418 38 = 1 := by
  decide
@[simp] private lemma A376418_eval_39 : A376418 39 = 1 := by
  decide
@[simp] private lemma A376418_eval_40 : A376418 40 = 2 := by
  decide
@[simp] private lemma A376418_eval_41 : A376418 41 = 1 := by
  decide
@[simp] private lemma A376418_eval_42 : A376418 42 = 1 := by
  decide
@[simp] private lemma A376418_eval_43 : A376418 43 = 1 := by
  decide
@[simp] private lemma A376418_eval_44 : A376418 44 = 2 := by
  decide
@[simp] private lemma A376418_eval_45 : A376418 45 = 1 := by
  decide
@[simp] private lemma A376418_eval_46 : A376418 46 = 1 := by
  decide
@[simp] private lemma A376418_eval_47 : A376418 47 = 1 := by
  decide
@[simp] private lemma A376418_eval_48 : A376418 48 = 2 := by
  decide
@[simp] private lemma A376418_eval_49 : A376418 49 = 1 := by
  decide
@[simp] private lemma A376418_eval_50 : A376418 50 = 1 := by
  decide
@[simp] private lemma A376418_eval_51 : A376418 51 = 1 := by
  decide
@[simp] private lemma A376418_eval_52 : A376418 52 = 2 := by
  decide
@[simp] private lemma A376418_eval_53 : A376418 53 = 1 := by
  decide
@[simp] private lemma A376418_eval_54 : A376418 54 = 2 := by
  decide
@[simp] private lemma A376418_eval_55 : A376418 55 = 1 := by
  decide
@[simp] private lemma A376418_eval_56 : A376418 56 = 2 := by
  decide
@[simp] private lemma A376418_eval_57 : A376418 57 = 1 := by
  decide
@[simp] private lemma A376418_eval_58 : A376418 58 = 1 := by
  decide
@[simp] private lemma A376418_eval_59 : A376418 59 = 1 := by
  decide
@[simp] private lemma A376418_eval_60 : A376418 60 = 2 := by
  decide
@[simp] private lemma A379240_f_eval_1 : A379240_f 1 = A379240_F_val.case_pair 0 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_2 : A379240_f 2 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_3 : A379240_f 3 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_4 : A379240_f 4 = A379240_F_val.case_n 4 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_5 : A379240_f 5 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_6 : A379240_f 6 = A379240_F_val.case_pair 5 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_7 : A379240_f 7 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_8 : A379240_f 8 = A379240_F_val.case_n 8 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_9 : A379240_f 9 = A379240_F_val.case_pair 6 3 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_10 : A379240_f 10 = A379240_F_val.case_pair 7 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_11 : A379240_f 11 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_12 : A379240_f 12 = A379240_F_val.case_n 12 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_13 : A379240_f 13 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_14 : A379240_f 14 = A379240_F_val.case_pair 9 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_15 : A379240_f 15 = A379240_F_val.case_pair 8 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_16 : A379240_f 16 = A379240_F_val.case_n 16 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_17 : A379240_f 17 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_18 : A379240_f 18 = A379240_F_val.case_pair 21 3 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_19 : A379240_f 19 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_20 : A379240_f 20 = A379240_F_val.case_n 20 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_21 : A379240_f 21 = A379240_F_val.case_pair 10 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_22 : A379240_f 22 = A379240_F_val.case_pair 13 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_23 : A379240_f 23 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_24 : A379240_f 24 = A379240_F_val.case_n 24 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_25 : A379240_f 25 = A379240_F_val.case_pair 10 5 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_26 : A379240_f 26 = A379240_F_val.case_pair 15 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_27 : A379240_f 27 = A379240_F_val.case_n 27 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_28 : A379240_f 28 = A379240_F_val.case_n 28 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_29 : A379240_f 29 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_30 : A379240_f 30 = A379240_F_val.case_pair 31 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_31 : A379240_f 31 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_32 : A379240_f 32 = A379240_F_val.case_n 32 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_33 : A379240_f 33 = A379240_F_val.case_pair 14 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_34 : A379240_f 34 = A379240_F_val.case_pair 19 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_35 : A379240_f 35 = A379240_F_val.case_pair 12 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_36 : A379240_f 36 = A379240_F_val.case_n 36 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_37 : A379240_f 37 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_38 : A379240_f 38 = A379240_F_val.case_pair 21 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_39 : A379240_f 39 = A379240_F_val.case_pair 16 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_40 : A379240_f 40 = A379240_F_val.case_n 40 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_41 : A379240_f 41 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_42 : A379240_f 42 = A379240_F_val.case_pair 41 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_43 : A379240_f 43 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_44 : A379240_f 44 = A379240_F_val.case_n 44 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_45 : A379240_f 45 = A379240_F_val.case_pair 39 3 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_46 : A379240_f 46 = A379240_F_val.case_pair 25 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_47 : A379240_f 47 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_48 : A379240_f 48 = A379240_F_val.case_n 48 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_49 : A379240_f 49 = A379240_F_val.case_pair 14 7 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_50 : A379240_f 50 = A379240_F_val.case_pair 45 5 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_51 : A379240_f 51 = A379240_F_val.case_pair 20 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_52 : A379240_f 52 = A379240_F_val.case_n 52 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_53 : A379240_f 53 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_54 : A379240_f 54 = A379240_F_val.case_n 54 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_55 : A379240_f 55 = A379240_F_val.case_pair 16 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_56 : A379240_f 56 = A379240_F_val.case_n 56 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_57 : A379240_f 57 = A379240_F_val.case_pair 22 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_58 : A379240_f 58 = A379240_F_val.case_pair 31 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_59 : A379240_f 59 = A379240_F_val.case_pair 1 1 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_eval_60 : A379240_f 60 = A379240_F_val.case_n 60 := by
  norm_num [A379240_f, A359550, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_1 : A379240_conj_f_triple 1 = (0, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_2 : A379240_conj_f_triple 2 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_3 : A379240_conj_f_triple 3 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_4 : A379240_conj_f_triple 4 = (4, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_5 : A379240_conj_f_triple 5 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_6 : A379240_conj_f_triple 6 = (5, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_7 : A379240_conj_f_triple 7 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_8 : A379240_conj_f_triple 8 = (12, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_9 : A379240_conj_f_triple 9 = (6, 3, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_10 : A379240_conj_f_triple 10 = (7, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_11 : A379240_conj_f_triple 11 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_12 : A379240_conj_f_triple 12 = (16, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_13 : A379240_conj_f_triple 13 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_14 : A379240_conj_f_triple 14 = (9, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_15 : A379240_conj_f_triple 15 = (8, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_16 : A379240_conj_f_triple 16 = (32, 16, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_17 : A379240_conj_f_triple 17 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_18 : A379240_conj_f_triple 18 = (21, 3, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_19 : A379240_conj_f_triple 19 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_20 : A379240_conj_f_triple 20 = (24, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_21 : A379240_conj_f_triple 21 = (10, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_22 : A379240_conj_f_triple 22 = (13, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_23 : A379240_conj_f_triple 23 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_24 : A379240_conj_f_triple 24 = (44, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_25 : A379240_conj_f_triple 25 = (10, 5, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_26 : A379240_conj_f_triple 26 = (15, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_27 : A379240_conj_f_triple 27 = (27, 27, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_28 : A379240_conj_f_triple 28 = (32, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_29 : A379240_conj_f_triple 29 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_30 : A379240_conj_f_triple 30 = (31, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_31 : A379240_conj_f_triple 31 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_32 : A379240_conj_f_triple 32 = (80, 16, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_33 : A379240_conj_f_triple 33 = (14, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_34 : A379240_conj_f_triple 34 = (19, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_35 : A379240_conj_f_triple 35 = (12, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_36 : A379240_conj_f_triple 36 = (60, 12, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_37 : A379240_conj_f_triple 37 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_38 : A379240_conj_f_triple 38 = (21, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_39 : A379240_conj_f_triple 39 = (16, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_40 : A379240_conj_f_triple 40 = (68, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_41 : A379240_conj_f_triple 41 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_42 : A379240_conj_f_triple 42 = (41, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_43 : A379240_conj_f_triple 43 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_44 : A379240_conj_f_triple 44 = (48, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_45 : A379240_conj_f_triple 45 = (39, 3, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_46 : A379240_conj_f_triple 46 = (25, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_47 : A379240_conj_f_triple 47 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_48 : A379240_conj_f_triple 48 = (112, 16, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_49 : A379240_conj_f_triple 49 = (14, 7, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_50 : A379240_conj_f_triple 50 = (45, 5, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_51 : A379240_conj_f_triple 51 = (20, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_52 : A379240_conj_f_triple 52 = (56, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_53 : A379240_conj_f_triple 53 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_54 : A379240_conj_f_triple 54 = (81, 27, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_55 : A379240_conj_f_triple 55 = (16, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_56 : A379240_conj_f_triple 56 = (92, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_57 : A379240_conj_f_triple 57 = (22, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_58 : A379240_conj_f_triple 58 = (31, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_59 : A379240_conj_f_triple 59 = (1, 1, 1) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_triple_eval_60 : A379240_conj_f_triple 60 = (92, 4, 2) := by
  norm_num [A379240_conj_f_triple, A003415, A085731, Nat.factorization_eq_primeFactorsList_multiset, Nat.primeFactorsList, Finsupp.support_single_ne_zero]
@[simp] private lemma A379240_f_prefix_eval :
    List.map (fun i => A379240_f (i + 1)) (List.range 60) = [A379240_f 1, A379240_f 2, A379240_f 3, A379240_f 4, A379240_f 5, A379240_f 6, A379240_f 7, A379240_f 8, A379240_f 9, A379240_f 10, A379240_f 11, A379240_f 12, A379240_f 13, A379240_f 14, A379240_f 15, A379240_f 16, A379240_f 17, A379240_f 18, A379240_f 19, A379240_f 20, A379240_f 21, A379240_f 22, A379240_f 23, A379240_f 24, A379240_f 25, A379240_f 26, A379240_f 27, A379240_f 28, A379240_f 29, A379240_f 30, A379240_f 31, A379240_f 32, A379240_f 33, A379240_f 34, A379240_f 35, A379240_f 36, A379240_f 37, A379240_f 38, A379240_f 39, A379240_f 40, A379240_f 41, A379240_f 42, A379240_f 43, A379240_f 44, A379240_f 45, A379240_f 46, A379240_f 47, A379240_f 48, A379240_f 49, A379240_f 50, A379240_f 51, A379240_f 52, A379240_f 53, A379240_f 54, A379240_f 55, A379240_f 56, A379240_f 57, A379240_f 58, A379240_f 59, A379240_f 60] := by
  rfl
@[simp] private lemma A379240_triple_prefix_eval :
    List.map (fun i => A379240_conj_f_triple (i + 1)) (List.range 60) = [A379240_conj_f_triple 1, A379240_conj_f_triple 2, A379240_conj_f_triple 3, A379240_conj_f_triple 4, A379240_conj_f_triple 5, A379240_conj_f_triple 6, A379240_conj_f_triple 7, A379240_conj_f_triple 8, A379240_conj_f_triple 9, A379240_conj_f_triple 10, A379240_conj_f_triple 11, A379240_conj_f_triple 12, A379240_conj_f_triple 13, A379240_conj_f_triple 14, A379240_conj_f_triple 15, A379240_conj_f_triple 16, A379240_conj_f_triple 17, A379240_conj_f_triple 18, A379240_conj_f_triple 19, A379240_conj_f_triple 20, A379240_conj_f_triple 21, A379240_conj_f_triple 22, A379240_conj_f_triple 23, A379240_conj_f_triple 24, A379240_conj_f_triple 25, A379240_conj_f_triple 26, A379240_conj_f_triple 27, A379240_conj_f_triple 28, A379240_conj_f_triple 29, A379240_conj_f_triple 30, A379240_conj_f_triple 31, A379240_conj_f_triple 32, A379240_conj_f_triple 33, A379240_conj_f_triple 34, A379240_conj_f_triple 35, A379240_conj_f_triple 36, A379240_conj_f_triple 37, A379240_conj_f_triple 38, A379240_conj_f_triple 39, A379240_conj_f_triple 40, A379240_conj_f_triple 41, A379240_conj_f_triple 42, A379240_conj_f_triple 43, A379240_conj_f_triple 44, A379240_conj_f_triple 45, A379240_conj_f_triple 46, A379240_conj_f_triple 47, A379240_conj_f_triple 48, A379240_conj_f_triple 49, A379240_conj_f_triple 50, A379240_conj_f_triple 51, A379240_conj_f_triple 52, A379240_conj_f_triple 53, A379240_conj_f_triple 54, A379240_conj_f_triple 55, A379240_conj_f_triple 56, A379240_conj_f_triple 57, A379240_conj_f_triple 58, A379240_conj_f_triple 59, A379240_conj_f_triple 60] := by
  rfl
private lemma A379240_f_idx_eval :
    List.idxOf (A379240_F_val.case_n 60) ([A379240_F_val.case_pair 0 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 4, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 5 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 8, A379240_F_val.case_pair 6 3, A379240_F_val.case_pair 7 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 12, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 9 1, A379240_F_val.case_pair 8 1, A379240_F_val.case_n 16, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 21 3, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 20, A379240_F_val.case_pair 10 1, A379240_F_val.case_pair 13 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 24, A379240_F_val.case_pair 10 5, A379240_F_val.case_pair 15 1, A379240_F_val.case_n 27, A379240_F_val.case_n 28, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 31 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 32, A379240_F_val.case_pair 14 1, A379240_F_val.case_pair 19 1, A379240_F_val.case_pair 12 1, A379240_F_val.case_n 36, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 21 1, A379240_F_val.case_pair 16 1, A379240_F_val.case_n 40, A379240_F_val.case_pair 1 1, A379240_F_val.case_pair 41 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 44, A379240_F_val.case_pair 39 3, A379240_F_val.case_pair 25 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 48, A379240_F_val.case_pair 14 7, A379240_F_val.case_pair 45 5, A379240_F_val.case_pair 20 1, A379240_F_val.case_n 52, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 54, A379240_F_val.case_pair 16 1, A379240_F_val.case_n 56, A379240_F_val.case_pair 22 1, A379240_F_val.case_pair 31 1, A379240_F_val.case_pair 1 1, A379240_F_val.case_n 60].dedup) = 41 := by
  decide
private lemma A379240_triple_idx_eval :
    List.idxOf (92, 4, 2) ([(0, 1, 1), (1, 1, 1), (1, 1, 1), (4, 4, 2), (1, 1, 1), (5, 1, 1), (1, 1, 1), (12, 4, 2), (6, 3, 1), (7, 1, 1), (1, 1, 1), (16, 4, 2), (1, 1, 1), (9, 1, 1), (8, 1, 1), (32, 16, 2), (1, 1, 1), (21, 3, 1), (1, 1, 1), (24, 4, 2), (10, 1, 1), (13, 1, 1), (1, 1, 1), (44, 4, 2), (10, 5, 1), (15, 1, 1), (27, 27, 2), (32, 4, 2), (1, 1, 1), (31, 1, 1), (1, 1, 1), (80, 16, 2), (14, 1, 1), (19, 1, 1), (12, 1, 1), (60, 12, 2), (1, 1, 1), (21, 1, 1), (16, 1, 1), (68, 4, 2), (1, 1, 1), (41, 1, 1), (1, 1, 1), (48, 4, 2), (39, 3, 1), (25, 1, 1), (1, 1, 1), (112, 16, 2), (14, 7, 1), (45, 5, 1), (20, 1, 1), (56, 4, 2), (1, 1, 1), (81, 27, 2), (16, 1, 1), (92, 4, 2), (22, 1, 1), (31, 1, 1), (1, 1, 1), (92, 4, 2)].dedup) = 40 := by
  decide

/--
A379240 It is conjectured that this is also the lexicographically earliest infinite sequence such
that a(i) = a(j) => A003415(i) = A003415(j), A085731(i) = A085731(j) and A376418(i) = A376418(j),
for all i, j >= 1, i.e., the restricted growth sequence transform of the triple
[A003415(n), A085731(n), A376418(n)]. This is true if for every pair of $i$ and $j$ for which
$i \ne j$, and $\mathtt{A376418}(i) = \mathtt{A376418}(j) > 0$, the ordered pairs
$[\mathtt{A003415}(i), \mathtt{A085731}(i)]$ and $[\mathtt{A003415}(j), \mathtt{A085731}(j)]$
differ from each other.
-/
theorem A379240_conjecture_equality.disproof : ¬ (∀ n : ℕ, A379240 n = A379240_conjecture n) := by
  intro h
  have contra : A379240 60 ≠ A379240_conjecture 60 := by
    unfold A379240 A379240_conjecture rgs_transform
    norm_num
    rw [A379240_f_idx_eval]
    norm_num
  exact contra (h 60)
