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

/--
A379240 It is conjectured that this is also the lexicographically earliest infinite sequence such
that a(i) = a(j) => A003415(i) = A003415(j), A085731(i) = A085731(j) and A376418(i) = A376418(j),
for all i, j >= 1, i.e., the restricted growth sequence transform of the triple
[A003415(n), A085731(n), A376418(n)]. This is true if for every pair of $i$ and $j$ for which
$i \ne j$, and $\mathtt{A376418}(i) = \mathtt{A376418}(j) > 0$, the ordered pairs
$[\mathtt{A003415}(i), \mathtt{A085731}(i)]$ and $[\mathtt{A003415}(j), \mathtt{A085731}(j)]$
differ from each other.
-/


-- Generated Helper Proofs for disproving the conjecture

theorem A003415_eval (n : ℕ) (L : List ℕ) (h : n.primeFactorsList = L) :
    A003415 n = (if n = 0 then 0 else L.toFinset.sum fun p => (n / p) * (L.count p)) := by
  unfold A003415
  split_ifs with hn
  · rfl
  · rw [support_factorization, primeFactors, h]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← primeFactorsList_count_eq, h]

theorem A359550_eval (n : ℕ) (L : List ℕ) (h : n.primeFactorsList = L) :
    A359550 n = (if n ≤ 1 then 1
                 else if (Finset.filter (fun p => L.count p ≥ p) L.toFinset).card > 0
                 then 0 else 1) := by
  unfold A359550
  rw [support_factorization, primeFactors, h]
  have h_filter : Finset.filter (fun p => n.factorization p ≥ p) L.toFinset =
                  Finset.filter (fun p => L.count p ≥ p) L.toFinset := by
    refine Finset.filter_congr fun x hx => ?_
    rw [← primeFactorsList_count_eq, h]
  rw [h_filter]


theorem pf_2 : (2 : ℕ).primeFactorsList = [2] := by

  rw [primeFactorsList]

  have h1 : (0 + 2).minFac = 2 := by norm_num

  have h2 : (0 + 2) / 2 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_3 : (3 : ℕ).primeFactorsList = [3] := by

  rw [primeFactorsList]

  have h1 : (1 + 2).minFac = 3 := by norm_num

  have h2 : (1 + 2) / 3 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_4 : (4 : ℕ).primeFactorsList = [2, 2] := by

  rw [primeFactorsList]

  have h1 : (2 + 2).minFac = 2 := by norm_num

  have h2 : (2 + 2) / 2 = 2 := by norm_num

  rw [h1, h2]

  rw [pf_2]

theorem pf_5 : (5 : ℕ).primeFactorsList = [5] := by

  rw [primeFactorsList]

  have h1 : (3 + 2).minFac = 5 := by norm_num

  have h2 : (3 + 2) / 5 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_6 : (6 : ℕ).primeFactorsList = [2, 3] := by

  rw [primeFactorsList]

  have h1 : (4 + 2).minFac = 2 := by norm_num

  have h2 : (4 + 2) / 2 = 3 := by norm_num

  rw [h1, h2]

  rw [pf_3]

theorem pf_7 : (7 : ℕ).primeFactorsList = [7] := by

  rw [primeFactorsList]

  have h1 : (5 + 2).minFac = 7 := by norm_num

  have h2 : (5 + 2) / 7 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_8 : (8 : ℕ).primeFactorsList = [2, 2, 2] := by

  rw [primeFactorsList]

  have h1 : (6 + 2).minFac = 2 := by norm_num

  have h2 : (6 + 2) / 2 = 4 := by norm_num

  rw [h1, h2]

  rw [pf_4]

theorem pf_9 : (9 : ℕ).primeFactorsList = [3, 3] := by

  rw [primeFactorsList]

  have h1 : (7 + 2).minFac = 3 := by norm_num

  have h2 : (7 + 2) / 3 = 3 := by norm_num

  rw [h1, h2]

  rw [pf_3]

theorem pf_10 : (10 : ℕ).primeFactorsList = [2, 5] := by

  rw [primeFactorsList]

  have h1 : (8 + 2).minFac = 2 := by norm_num

  have h2 : (8 + 2) / 2 = 5 := by norm_num

  rw [h1, h2]

  rw [pf_5]

theorem pf_11 : (11 : ℕ).primeFactorsList = [11] := by

  rw [primeFactorsList]

  have h1 : (9 + 2).minFac = 11 := by norm_num

  have h2 : (9 + 2) / 11 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_12 : (12 : ℕ).primeFactorsList = [2, 2, 3] := by

  rw [primeFactorsList]

  have h1 : (10 + 2).minFac = 2 := by norm_num

  have h2 : (10 + 2) / 2 = 6 := by norm_num

  rw [h1, h2]

  rw [pf_6]

theorem pf_13 : (13 : ℕ).primeFactorsList = [13] := by

  rw [primeFactorsList]

  have h1 : (11 + 2).minFac = 13 := by norm_num

  have h2 : (11 + 2) / 13 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_14 : (14 : ℕ).primeFactorsList = [2, 7] := by

  rw [primeFactorsList]

  have h1 : (12 + 2).minFac = 2 := by norm_num

  have h2 : (12 + 2) / 2 = 7 := by norm_num

  rw [h1, h2]

  rw [pf_7]

theorem pf_15 : (15 : ℕ).primeFactorsList = [3, 5] := by

  rw [primeFactorsList]

  have h1 : (13 + 2).minFac = 3 := by norm_num

  have h2 : (13 + 2) / 3 = 5 := by norm_num

  rw [h1, h2]

  rw [pf_5]

theorem pf_16 : (16 : ℕ).primeFactorsList = [2, 2, 2, 2] := by

  rw [primeFactorsList]

  have h1 : (14 + 2).minFac = 2 := by norm_num

  have h2 : (14 + 2) / 2 = 8 := by norm_num

  rw [h1, h2]

  rw [pf_8]

theorem pf_17 : (17 : ℕ).primeFactorsList = [17] := by

  rw [primeFactorsList]

  have h1 : (15 + 2).minFac = 17 := by norm_num

  have h2 : (15 + 2) / 17 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_18 : (18 : ℕ).primeFactorsList = [2, 3, 3] := by

  rw [primeFactorsList]

  have h1 : (16 + 2).minFac = 2 := by norm_num

  have h2 : (16 + 2) / 2 = 9 := by norm_num

  rw [h1, h2]

  rw [pf_9]

theorem pf_19 : (19 : ℕ).primeFactorsList = [19] := by

  rw [primeFactorsList]

  have h1 : (17 + 2).minFac = 19 := by norm_num

  have h2 : (17 + 2) / 19 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_20 : (20 : ℕ).primeFactorsList = [2, 2, 5] := by

  rw [primeFactorsList]

  have h1 : (18 + 2).minFac = 2 := by norm_num

  have h2 : (18 + 2) / 2 = 10 := by norm_num

  rw [h1, h2]

  rw [pf_10]

theorem pf_21 : (21 : ℕ).primeFactorsList = [3, 7] := by

  rw [primeFactorsList]

  have h1 : (19 + 2).minFac = 3 := by norm_num

  have h2 : (19 + 2) / 3 = 7 := by norm_num

  rw [h1, h2]

  rw [pf_7]

theorem pf_22 : (22 : ℕ).primeFactorsList = [2, 11] := by

  rw [primeFactorsList]

  have h1 : (20 + 2).minFac = 2 := by norm_num

  have h2 : (20 + 2) / 2 = 11 := by norm_num

  rw [h1, h2]

  rw [pf_11]

theorem pf_23 : (23 : ℕ).primeFactorsList = [23] := by

  rw [primeFactorsList]

  have h1 : (21 + 2).minFac = 23 := by norm_num

  have h2 : (21 + 2) / 23 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_24 : (24 : ℕ).primeFactorsList = [2, 2, 2, 3] := by

  rw [primeFactorsList]

  have h1 : (22 + 2).minFac = 2 := by norm_num

  have h2 : (22 + 2) / 2 = 12 := by norm_num

  rw [h1, h2]

  rw [pf_12]

theorem pf_25 : (25 : ℕ).primeFactorsList = [5, 5] := by

  rw [primeFactorsList]

  have h1 : (23 + 2).minFac = 5 := by norm_num

  have h2 : (23 + 2) / 5 = 5 := by norm_num

  rw [h1, h2]

  rw [pf_5]

theorem pf_26 : (26 : ℕ).primeFactorsList = [2, 13] := by

  rw [primeFactorsList]

  have h1 : (24 + 2).minFac = 2 := by norm_num

  have h2 : (24 + 2) / 2 = 13 := by norm_num

  rw [h1, h2]

  rw [pf_13]

theorem pf_27 : (27 : ℕ).primeFactorsList = [3, 3, 3] := by

  rw [primeFactorsList]

  have h1 : (25 + 2).minFac = 3 := by norm_num

  have h2 : (25 + 2) / 3 = 9 := by norm_num

  rw [h1, h2]

  rw [pf_9]

theorem pf_28 : (28 : ℕ).primeFactorsList = [2, 2, 7] := by

  rw [primeFactorsList]

  have h1 : (26 + 2).minFac = 2 := by norm_num

  have h2 : (26 + 2) / 2 = 14 := by norm_num

  rw [h1, h2]

  rw [pf_14]

theorem pf_29 : (29 : ℕ).primeFactorsList = [29] := by

  rw [primeFactorsList]

  have h1 : (27 + 2).minFac = 29 := by norm_num

  have h2 : (27 + 2) / 29 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_30 : (30 : ℕ).primeFactorsList = [2, 3, 5] := by

  rw [primeFactorsList]

  have h1 : (28 + 2).minFac = 2 := by norm_num

  have h2 : (28 + 2) / 2 = 15 := by norm_num

  rw [h1, h2]

  rw [pf_15]

theorem pf_31 : (31 : ℕ).primeFactorsList = [31] := by

  rw [primeFactorsList]

  have h1 : (29 + 2).minFac = 31 := by norm_num

  have h2 : (29 + 2) / 31 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_32 : (32 : ℕ).primeFactorsList = [2, 2, 2, 2, 2] := by

  rw [primeFactorsList]

  have h1 : (30 + 2).minFac = 2 := by norm_num

  have h2 : (30 + 2) / 2 = 16 := by norm_num

  rw [h1, h2]

  rw [pf_16]

theorem pf_33 : (33 : ℕ).primeFactorsList = [3, 11] := by

  rw [primeFactorsList]

  have h1 : (31 + 2).minFac = 3 := by norm_num

  have h2 : (31 + 2) / 3 = 11 := by norm_num

  rw [h1, h2]

  rw [pf_11]

theorem pf_34 : (34 : ℕ).primeFactorsList = [2, 17] := by

  rw [primeFactorsList]

  have h1 : (32 + 2).minFac = 2 := by norm_num

  have h2 : (32 + 2) / 2 = 17 := by norm_num

  rw [h1, h2]

  rw [pf_17]

theorem pf_35 : (35 : ℕ).primeFactorsList = [5, 7] := by

  rw [primeFactorsList]

  have h1 : (33 + 2).minFac = 5 := by norm_num

  have h2 : (33 + 2) / 5 = 7 := by norm_num

  rw [h1, h2]

  rw [pf_7]

theorem pf_36 : (36 : ℕ).primeFactorsList = [2, 2, 3, 3] := by

  rw [primeFactorsList]

  have h1 : (34 + 2).minFac = 2 := by norm_num

  have h2 : (34 + 2) / 2 = 18 := by norm_num

  rw [h1, h2]

  rw [pf_18]

theorem pf_37 : (37 : ℕ).primeFactorsList = [37] := by

  rw [primeFactorsList]

  have h1 : (35 + 2).minFac = 37 := by norm_num

  have h2 : (35 + 2) / 37 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_38 : (38 : ℕ).primeFactorsList = [2, 19] := by

  rw [primeFactorsList]

  have h1 : (36 + 2).minFac = 2 := by norm_num

  have h2 : (36 + 2) / 2 = 19 := by norm_num

  rw [h1, h2]

  rw [pf_19]

theorem pf_39 : (39 : ℕ).primeFactorsList = [3, 13] := by

  rw [primeFactorsList]

  have h1 : (37 + 2).minFac = 3 := by norm_num

  have h2 : (37 + 2) / 3 = 13 := by norm_num

  rw [h1, h2]

  rw [pf_13]

theorem pf_40 : (40 : ℕ).primeFactorsList = [2, 2, 2, 5] := by

  rw [primeFactorsList]

  have h1 : (38 + 2).minFac = 2 := by norm_num

  have h2 : (38 + 2) / 2 = 20 := by norm_num

  rw [h1, h2]

  rw [pf_20]

theorem pf_41 : (41 : ℕ).primeFactorsList = [41] := by

  rw [primeFactorsList]

  have h1 : (39 + 2).minFac = 41 := by norm_num

  have h2 : (39 + 2) / 41 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_42 : (42 : ℕ).primeFactorsList = [2, 3, 7] := by

  rw [primeFactorsList]

  have h1 : (40 + 2).minFac = 2 := by norm_num

  have h2 : (40 + 2) / 2 = 21 := by norm_num

  rw [h1, h2]

  rw [pf_21]

theorem pf_43 : (43 : ℕ).primeFactorsList = [43] := by

  rw [primeFactorsList]

  have h1 : (41 + 2).minFac = 43 := by norm_num

  have h2 : (41 + 2) / 43 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_44 : (44 : ℕ).primeFactorsList = [2, 2, 11] := by

  rw [primeFactorsList]

  have h1 : (42 + 2).minFac = 2 := by norm_num

  have h2 : (42 + 2) / 2 = 22 := by norm_num

  rw [h1, h2]

  rw [pf_22]

theorem pf_45 : (45 : ℕ).primeFactorsList = [3, 3, 5] := by

  rw [primeFactorsList]

  have h1 : (43 + 2).minFac = 3 := by norm_num

  have h2 : (43 + 2) / 3 = 15 := by norm_num

  rw [h1, h2]

  rw [pf_15]

theorem pf_46 : (46 : ℕ).primeFactorsList = [2, 23] := by

  rw [primeFactorsList]

  have h1 : (44 + 2).minFac = 2 := by norm_num

  have h2 : (44 + 2) / 2 = 23 := by norm_num

  rw [h1, h2]

  rw [pf_23]

theorem pf_47 : (47 : ℕ).primeFactorsList = [47] := by

  rw [primeFactorsList]

  have h1 : (45 + 2).minFac = 47 := by norm_num

  have h2 : (45 + 2) / 47 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_48 : (48 : ℕ).primeFactorsList = [2, 2, 2, 2, 3] := by

  rw [primeFactorsList]

  have h1 : (46 + 2).minFac = 2 := by norm_num

  have h2 : (46 + 2) / 2 = 24 := by norm_num

  rw [h1, h2]

  rw [pf_24]

theorem pf_49 : (49 : ℕ).primeFactorsList = [7, 7] := by

  rw [primeFactorsList]

  have h1 : (47 + 2).minFac = 7 := by norm_num

  have h2 : (47 + 2) / 7 = 7 := by norm_num

  rw [h1, h2]

  rw [pf_7]

theorem pf_50 : (50 : ℕ).primeFactorsList = [2, 5, 5] := by

  rw [primeFactorsList]

  have h1 : (48 + 2).minFac = 2 := by norm_num

  have h2 : (48 + 2) / 2 = 25 := by norm_num

  rw [h1, h2]

  rw [pf_25]

theorem pf_51 : (51 : ℕ).primeFactorsList = [3, 17] := by

  rw [primeFactorsList]

  have h1 : (49 + 2).minFac = 3 := by norm_num

  have h2 : (49 + 2) / 3 = 17 := by norm_num

  rw [h1, h2]

  rw [pf_17]

theorem pf_52 : (52 : ℕ).primeFactorsList = [2, 2, 13] := by

  rw [primeFactorsList]

  have h1 : (50 + 2).minFac = 2 := by norm_num

  have h2 : (50 + 2) / 2 = 26 := by norm_num

  rw [h1, h2]

  rw [pf_26]

theorem pf_53 : (53 : ℕ).primeFactorsList = [53] := by

  rw [primeFactorsList]

  have h1 : (51 + 2).minFac = 53 := by norm_num

  have h2 : (51 + 2) / 53 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_54 : (54 : ℕ).primeFactorsList = [2, 3, 3, 3] := by

  rw [primeFactorsList]

  have h1 : (52 + 2).minFac = 2 := by norm_num

  have h2 : (52 + 2) / 2 = 27 := by norm_num

  rw [h1, h2]

  rw [pf_27]

theorem pf_55 : (55 : ℕ).primeFactorsList = [5, 11] := by

  rw [primeFactorsList]

  have h1 : (53 + 2).minFac = 5 := by norm_num

  have h2 : (53 + 2) / 5 = 11 := by norm_num

  rw [h1, h2]

  rw [pf_11]

theorem pf_56 : (56 : ℕ).primeFactorsList = [2, 2, 2, 7] := by

  rw [primeFactorsList]

  have h1 : (54 + 2).minFac = 2 := by norm_num

  have h2 : (54 + 2) / 2 = 28 := by norm_num

  rw [h1, h2]

  rw [pf_28]

theorem pf_57 : (57 : ℕ).primeFactorsList = [3, 19] := by

  rw [primeFactorsList]

  have h1 : (55 + 2).minFac = 3 := by norm_num

  have h2 : (55 + 2) / 3 = 19 := by norm_num

  rw [h1, h2]

  rw [pf_19]

theorem pf_58 : (58 : ℕ).primeFactorsList = [2, 29] := by

  rw [primeFactorsList]

  have h1 : (56 + 2).minFac = 2 := by norm_num

  have h2 : (56 + 2) / 2 = 29 := by norm_num

  rw [h1, h2]

  rw [pf_29]

theorem pf_59 : (59 : ℕ).primeFactorsList = [59] := by

  rw [primeFactorsList]

  have h1 : (57 + 2).minFac = 59 := by norm_num

  have h2 : (57 + 2) / 59 = 1 := by norm_num

  rw [h1, h2]

  rw [primeFactorsList_one]

theorem pf_60 : (60 : ℕ).primeFactorsList = [2, 2, 3, 5] := by

  rw [primeFactorsList]

  have h1 : (58 + 2).minFac = 2 := by norm_num

  have h2 : (58 + 2) / 2 = 30 := by norm_num

  rw [h1, h2]

  rw [pf_30]

theorem A003415_1 : A003415 1 = 0 := by

  rw [A003415_eval 1 [] primeFactorsList_one]

  rfl

theorem A359550_1 : A359550 1 = 1 := by rfl

theorem A003415_2 : A003415 2 = 1 := by

  rw [A003415_eval 2 [2] pf_2]

  rfl

theorem A359550_2 : A359550 2 = 1 := by

  rw [A359550_eval 2 [2] pf_2]

  rfl

theorem A003415_3 : A003415 3 = 1 := by

  rw [A003415_eval 3 [3] pf_3]

  rfl

theorem A359550_3 : A359550 3 = 1 := by

  rw [A359550_eval 3 [3] pf_3]

  rfl

theorem A003415_4 : A003415 4 = 4 := by

  rw [A003415_eval 4 [2, 2] pf_4]

  rfl

theorem A359550_4 : A359550 4 = 0 := by

  rw [A359550_eval 4 [2, 2] pf_4]

  rfl

theorem A003415_5 : A003415 5 = 1 := by

  rw [A003415_eval 5 [5] pf_5]

  rfl

theorem A359550_5 : A359550 5 = 1 := by

  rw [A359550_eval 5 [5] pf_5]

  rfl

theorem A003415_6 : A003415 6 = 5 := by

  rw [A003415_eval 6 [2, 3] pf_6]

  rfl

theorem A359550_6 : A359550 6 = 1 := by

  rw [A359550_eval 6 [2, 3] pf_6]

  rfl

theorem A003415_7 : A003415 7 = 1 := by

  rw [A003415_eval 7 [7] pf_7]

  rfl

theorem A359550_7 : A359550 7 = 1 := by

  rw [A359550_eval 7 [7] pf_7]

  rfl

theorem A003415_8 : A003415 8 = 12 := by

  rw [A003415_eval 8 [2, 2, 2] pf_8]

  rfl

theorem A359550_8 : A359550 8 = 0 := by

  rw [A359550_eval 8 [2, 2, 2] pf_8]

  rfl

theorem A003415_9 : A003415 9 = 6 := by

  rw [A003415_eval 9 [3, 3] pf_9]

  rfl

theorem A359550_9 : A359550 9 = 1 := by

  rw [A359550_eval 9 [3, 3] pf_9]

  rfl

theorem A003415_10 : A003415 10 = 7 := by

  rw [A003415_eval 10 [2, 5] pf_10]

  rfl

theorem A359550_10 : A359550 10 = 1 := by

  rw [A359550_eval 10 [2, 5] pf_10]

  rfl

theorem A003415_11 : A003415 11 = 1 := by

  rw [A003415_eval 11 [11] pf_11]

  rfl

theorem A359550_11 : A359550 11 = 1 := by

  rw [A359550_eval 11 [11] pf_11]

  rfl

theorem A003415_12 : A003415 12 = 16 := by

  rw [A003415_eval 12 [2, 2, 3] pf_12]

  rfl

theorem A359550_12 : A359550 12 = 0 := by

  rw [A359550_eval 12 [2, 2, 3] pf_12]

  rfl

theorem A003415_13 : A003415 13 = 1 := by

  rw [A003415_eval 13 [13] pf_13]

  rfl

theorem A359550_13 : A359550 13 = 1 := by

  rw [A359550_eval 13 [13] pf_13]

  rfl

theorem A003415_14 : A003415 14 = 9 := by

  rw [A003415_eval 14 [2, 7] pf_14]

  rfl

theorem A359550_14 : A359550 14 = 1 := by

  rw [A359550_eval 14 [2, 7] pf_14]

  rfl

theorem A003415_15 : A003415 15 = 8 := by

  rw [A003415_eval 15 [3, 5] pf_15]

  rfl

theorem A359550_15 : A359550 15 = 1 := by

  rw [A359550_eval 15 [3, 5] pf_15]

  rfl

theorem A003415_16 : A003415 16 = 32 := by

  rw [A003415_eval 16 [2, 2, 2, 2] pf_16]

  rfl

theorem A359550_16 : A359550 16 = 0 := by

  rw [A359550_eval 16 [2, 2, 2, 2] pf_16]

  rfl

theorem A003415_17 : A003415 17 = 1 := by

  rw [A003415_eval 17 [17] pf_17]

  rfl

theorem A359550_17 : A359550 17 = 1 := by

  rw [A359550_eval 17 [17] pf_17]

  rfl

theorem A003415_18 : A003415 18 = 21 := by

  rw [A003415_eval 18 [2, 3, 3] pf_18]

  rfl

theorem A359550_18 : A359550 18 = 1 := by

  rw [A359550_eval 18 [2, 3, 3] pf_18]

  rfl

theorem A003415_19 : A003415 19 = 1 := by

  rw [A003415_eval 19 [19] pf_19]

  rfl

theorem A359550_19 : A359550 19 = 1 := by

  rw [A359550_eval 19 [19] pf_19]

  rfl

theorem A003415_20 : A003415 20 = 24 := by

  rw [A003415_eval 20 [2, 2, 5] pf_20]

  rfl

theorem A359550_20 : A359550 20 = 0 := by

  rw [A359550_eval 20 [2, 2, 5] pf_20]

  rfl

theorem A003415_21 : A003415 21 = 10 := by

  rw [A003415_eval 21 [3, 7] pf_21]

  rfl

theorem A359550_21 : A359550 21 = 1 := by

  rw [A359550_eval 21 [3, 7] pf_21]

  rfl

theorem A003415_22 : A003415 22 = 13 := by

  rw [A003415_eval 22 [2, 11] pf_22]

  rfl

theorem A359550_22 : A359550 22 = 1 := by

  rw [A359550_eval 22 [2, 11] pf_22]

  rfl

theorem A003415_23 : A003415 23 = 1 := by

  rw [A003415_eval 23 [23] pf_23]

  rfl

theorem A359550_23 : A359550 23 = 1 := by

  rw [A359550_eval 23 [23] pf_23]

  rfl

theorem A003415_24 : A003415 24 = 44 := by

  rw [A003415_eval 24 [2, 2, 2, 3] pf_24]

  rfl

theorem A359550_24 : A359550 24 = 0 := by

  rw [A359550_eval 24 [2, 2, 2, 3] pf_24]

  rfl

theorem A003415_25 : A003415 25 = 10 := by

  rw [A003415_eval 25 [5, 5] pf_25]

  rfl

theorem A359550_25 : A359550 25 = 1 := by

  rw [A359550_eval 25 [5, 5] pf_25]

  rfl

theorem A003415_26 : A003415 26 = 15 := by

  rw [A003415_eval 26 [2, 13] pf_26]

  rfl

theorem A359550_26 : A359550 26 = 1 := by

  rw [A359550_eval 26 [2, 13] pf_26]

  rfl

theorem A003415_27 : A003415 27 = 27 := by

  rw [A003415_eval 27 [3, 3, 3] pf_27]

  rfl

theorem A359550_27 : A359550 27 = 0 := by

  rw [A359550_eval 27 [3, 3, 3] pf_27]

  rfl

theorem A003415_28 : A003415 28 = 32 := by

  rw [A003415_eval 28 [2, 2, 7] pf_28]

  rfl

theorem A359550_28 : A359550 28 = 0 := by

  rw [A359550_eval 28 [2, 2, 7] pf_28]

  rfl

theorem A003415_29 : A003415 29 = 1 := by

  rw [A003415_eval 29 [29] pf_29]

  rfl

theorem A359550_29 : A359550 29 = 1 := by

  rw [A359550_eval 29 [29] pf_29]

  rfl

theorem A003415_30 : A003415 30 = 31 := by

  rw [A003415_eval 30 [2, 3, 5] pf_30]

  rfl

theorem A359550_30 : A359550 30 = 1 := by

  rw [A359550_eval 30 [2, 3, 5] pf_30]

  rfl

theorem A003415_31 : A003415 31 = 1 := by

  rw [A003415_eval 31 [31] pf_31]

  rfl

theorem A359550_31 : A359550 31 = 1 := by

  rw [A359550_eval 31 [31] pf_31]

  rfl

theorem A003415_32 : A003415 32 = 80 := by

  rw [A003415_eval 32 [2, 2, 2, 2, 2] pf_32]

  rfl

theorem A359550_32 : A359550 32 = 0 := by

  rw [A359550_eval 32 [2, 2, 2, 2, 2] pf_32]

  rfl

theorem A003415_33 : A003415 33 = 14 := by

  rw [A003415_eval 33 [3, 11] pf_33]

  rfl

theorem A359550_33 : A359550 33 = 1 := by

  rw [A359550_eval 33 [3, 11] pf_33]

  rfl

theorem A003415_34 : A003415 34 = 19 := by

  rw [A003415_eval 34 [2, 17] pf_34]

  rfl

theorem A359550_34 : A359550 34 = 1 := by

  rw [A359550_eval 34 [2, 17] pf_34]

  rfl

theorem A003415_35 : A003415 35 = 12 := by

  rw [A003415_eval 35 [5, 7] pf_35]

  rfl

theorem A359550_35 : A359550 35 = 1 := by

  rw [A359550_eval 35 [5, 7] pf_35]

  rfl

theorem A003415_36 : A003415 36 = 60 := by

  rw [A003415_eval 36 [2, 2, 3, 3] pf_36]

  rfl

theorem A359550_36 : A359550 36 = 0 := by

  rw [A359550_eval 36 [2, 2, 3, 3] pf_36]

  rfl

theorem A003415_37 : A003415 37 = 1 := by

  rw [A003415_eval 37 [37] pf_37]

  rfl

theorem A359550_37 : A359550 37 = 1 := by

  rw [A359550_eval 37 [37] pf_37]

  rfl

theorem A003415_38 : A003415 38 = 21 := by

  rw [A003415_eval 38 [2, 19] pf_38]

  rfl

theorem A359550_38 : A359550 38 = 1 := by

  rw [A359550_eval 38 [2, 19] pf_38]

  rfl

theorem A003415_39 : A003415 39 = 16 := by

  rw [A003415_eval 39 [3, 13] pf_39]

  rfl

theorem A359550_39 : A359550 39 = 1 := by

  rw [A359550_eval 39 [3, 13] pf_39]

  rfl

theorem A003415_40 : A003415 40 = 68 := by

  rw [A003415_eval 40 [2, 2, 2, 5] pf_40]

  rfl

theorem A359550_40 : A359550 40 = 0 := by

  rw [A359550_eval 40 [2, 2, 2, 5] pf_40]

  rfl

theorem A003415_41 : A003415 41 = 1 := by

  rw [A003415_eval 41 [41] pf_41]

  rfl

theorem A359550_41 : A359550 41 = 1 := by

  rw [A359550_eval 41 [41] pf_41]

  rfl

theorem A003415_42 : A003415 42 = 41 := by

  rw [A003415_eval 42 [2, 3, 7] pf_42]

  rfl

theorem A359550_42 : A359550 42 = 1 := by

  rw [A359550_eval 42 [2, 3, 7] pf_42]

  rfl

theorem A003415_43 : A003415 43 = 1 := by

  rw [A003415_eval 43 [43] pf_43]

  rfl

theorem A359550_43 : A359550 43 = 1 := by

  rw [A359550_eval 43 [43] pf_43]

  rfl

theorem A003415_44 : A003415 44 = 48 := by

  rw [A003415_eval 44 [2, 2, 11] pf_44]

  rfl

theorem A359550_44 : A359550 44 = 0 := by

  rw [A359550_eval 44 [2, 2, 11] pf_44]

  rfl

theorem A003415_45 : A003415 45 = 39 := by

  rw [A003415_eval 45 [3, 3, 5] pf_45]

  rfl

theorem A359550_45 : A359550 45 = 1 := by

  rw [A359550_eval 45 [3, 3, 5] pf_45]

  rfl

theorem A003415_46 : A003415 46 = 25 := by

  rw [A003415_eval 46 [2, 23] pf_46]

  rfl

theorem A359550_46 : A359550 46 = 1 := by

  rw [A359550_eval 46 [2, 23] pf_46]

  rfl

theorem A003415_47 : A003415 47 = 1 := by

  rw [A003415_eval 47 [47] pf_47]

  rfl

theorem A359550_47 : A359550 47 = 1 := by

  rw [A359550_eval 47 [47] pf_47]

  rfl

theorem A003415_48 : A003415 48 = 112 := by

  rw [A003415_eval 48 [2, 2, 2, 2, 3] pf_48]

  rfl

theorem A359550_48 : A359550 48 = 0 := by

  rw [A359550_eval 48 [2, 2, 2, 2, 3] pf_48]

  rfl

theorem A003415_49 : A003415 49 = 14 := by

  rw [A003415_eval 49 [7, 7] pf_49]

  rfl

theorem A359550_49 : A359550 49 = 1 := by

  rw [A359550_eval 49 [7, 7] pf_49]

  rfl

theorem A003415_50 : A003415 50 = 45 := by

  rw [A003415_eval 50 [2, 5, 5] pf_50]

  rfl

theorem A359550_50 : A359550 50 = 1 := by

  rw [A359550_eval 50 [2, 5, 5] pf_50]

  rfl

theorem A003415_51 : A003415 51 = 20 := by

  rw [A003415_eval 51 [3, 17] pf_51]

  rfl

theorem A359550_51 : A359550 51 = 1 := by

  rw [A359550_eval 51 [3, 17] pf_51]

  rfl

theorem A003415_52 : A003415 52 = 56 := by

  rw [A003415_eval 52 [2, 2, 13] pf_52]

  rfl

theorem A359550_52 : A359550 52 = 0 := by

  rw [A359550_eval 52 [2, 2, 13] pf_52]

  rfl

theorem A003415_53 : A003415 53 = 1 := by

  rw [A003415_eval 53 [53] pf_53]

  rfl

theorem A359550_53 : A359550 53 = 1 := by

  rw [A359550_eval 53 [53] pf_53]

  rfl

theorem A003415_54 : A003415 54 = 81 := by

  rw [A003415_eval 54 [2, 3, 3, 3] pf_54]

  rfl

theorem A359550_54 : A359550 54 = 0 := by

  rw [A359550_eval 54 [2, 3, 3, 3] pf_54]

  rfl

theorem A003415_55 : A003415 55 = 16 := by

  rw [A003415_eval 55 [5, 11] pf_55]

  rfl

theorem A359550_55 : A359550 55 = 1 := by

  rw [A359550_eval 55 [5, 11] pf_55]

  rfl

theorem A003415_56 : A003415 56 = 92 := by

  rw [A003415_eval 56 [2, 2, 2, 7] pf_56]

  rfl

theorem A359550_56 : A359550 56 = 0 := by

  rw [A359550_eval 56 [2, 2, 2, 7] pf_56]

  rfl

theorem A003415_57 : A003415 57 = 22 := by

  rw [A003415_eval 57 [3, 19] pf_57]

  rfl

theorem A359550_57 : A359550 57 = 1 := by

  rw [A359550_eval 57 [3, 19] pf_57]

  rfl

theorem A003415_58 : A003415 58 = 31 := by

  rw [A003415_eval 58 [2, 29] pf_58]

  rfl

theorem A359550_58 : A359550 58 = 1 := by

  rw [A359550_eval 58 [2, 29] pf_58]

  rfl

theorem A003415_59 : A003415 59 = 1 := by

  rw [A003415_eval 59 [59] pf_59]

  rfl

theorem A359550_59 : A359550 59 = 1 := by

  rw [A359550_eval 59 [59] pf_59]

  rfl

theorem A003415_60 : A003415 60 = 92 := by

  rw [A003415_eval 60 [2, 2, 3, 5] pf_60]

  rfl

theorem A359550_60 : A359550 60 = 0 := by

  rw [A359550_eval 60 [2, 2, 3, 5] pf_60]

  rfl

theorem A379240_f_1 : A379240_f 1 = A379240_F_val.case_pair 0 1 := by
  unfold A379240_f A085731
  rw [A359550_1, A003415_1]
  rfl

theorem A379240_conj_f_triple_1 : A379240_conj_f_triple 1 = (0, 1, 1) := by
  unfold A379240_conj_f_triple A085731
  rw [A003415_1]
  rfl

theorem A379240_f_2 : A379240_f 2 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_2, A003415_2]

  rfl

theorem A379240_conj_f_triple_2 : A379240_conj_f_triple 2 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_2]

  rfl

theorem A379240_f_3 : A379240_f 3 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_3, A003415_3]

  rfl

theorem A379240_conj_f_triple_3 : A379240_conj_f_triple 3 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_3]

  rfl

theorem A379240_f_4 : A379240_f 4 = A379240_F_val.case_n 4 := by

  unfold A379240_f A085731

  rw [A359550_4, A003415_4]

  rfl

theorem A379240_conj_f_triple_4 : A379240_conj_f_triple 4 = (4, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_4]

  rfl

theorem A379240_f_5 : A379240_f 5 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_5, A003415_5]

  rfl

theorem A379240_conj_f_triple_5 : A379240_conj_f_triple 5 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_5]

  rfl

theorem A379240_f_6 : A379240_f 6 = A379240_F_val.case_pair 5 1 := by

  unfold A379240_f A085731

  rw [A359550_6, A003415_6]

  rfl

theorem A379240_conj_f_triple_6 : A379240_conj_f_triple 6 = (5, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_6]

  rfl

theorem A379240_f_7 : A379240_f 7 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_7, A003415_7]

  rfl

theorem A379240_conj_f_triple_7 : A379240_conj_f_triple 7 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_7]

  rfl

theorem A379240_f_8 : A379240_f 8 = A379240_F_val.case_n 8 := by

  unfold A379240_f A085731

  rw [A359550_8, A003415_8]

  rfl

theorem A379240_conj_f_triple_8 : A379240_conj_f_triple 8 = (12, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_8]

  rfl

theorem A379240_f_9 : A379240_f 9 = A379240_F_val.case_pair 6 3 := by

  unfold A379240_f A085731

  rw [A359550_9, A003415_9]

  rfl

theorem A379240_conj_f_triple_9 : A379240_conj_f_triple 9 = (6, 3, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_9]

  rfl

theorem A379240_f_10 : A379240_f 10 = A379240_F_val.case_pair 7 1 := by

  unfold A379240_f A085731

  rw [A359550_10, A003415_10]

  rfl

theorem A379240_conj_f_triple_10 : A379240_conj_f_triple 10 = (7, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_10]

  rfl

theorem A379240_f_11 : A379240_f 11 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_11, A003415_11]

  rfl

theorem A379240_conj_f_triple_11 : A379240_conj_f_triple 11 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_11]

  rfl

theorem A379240_f_12 : A379240_f 12 = A379240_F_val.case_n 12 := by

  unfold A379240_f A085731

  rw [A359550_12, A003415_12]

  rfl

theorem A379240_conj_f_triple_12 : A379240_conj_f_triple 12 = (16, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_12]

  rfl

theorem A379240_f_13 : A379240_f 13 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_13, A003415_13]

  rfl

theorem A379240_conj_f_triple_13 : A379240_conj_f_triple 13 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_13]

  rfl

theorem A379240_f_14 : A379240_f 14 = A379240_F_val.case_pair 9 1 := by

  unfold A379240_f A085731

  rw [A359550_14, A003415_14]

  rfl

theorem A379240_conj_f_triple_14 : A379240_conj_f_triple 14 = (9, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_14]

  rfl

theorem A379240_f_15 : A379240_f 15 = A379240_F_val.case_pair 8 1 := by

  unfold A379240_f A085731

  rw [A359550_15, A003415_15]

  rfl

theorem A379240_conj_f_triple_15 : A379240_conj_f_triple 15 = (8, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_15]

  rfl

theorem A379240_f_16 : A379240_f 16 = A379240_F_val.case_n 16 := by

  unfold A379240_f A085731

  rw [A359550_16, A003415_16]

  rfl

theorem A379240_conj_f_triple_16 : A379240_conj_f_triple 16 = (32, 16, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_16]

  rfl

theorem A379240_f_17 : A379240_f 17 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_17, A003415_17]

  rfl

theorem A379240_conj_f_triple_17 : A379240_conj_f_triple 17 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_17]

  rfl

theorem A379240_f_18 : A379240_f 18 = A379240_F_val.case_pair 21 3 := by

  unfold A379240_f A085731

  rw [A359550_18, A003415_18]

  rfl

theorem A379240_conj_f_triple_18 : A379240_conj_f_triple 18 = (21, 3, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_18]

  rfl

theorem A379240_f_19 : A379240_f 19 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_19, A003415_19]

  rfl

theorem A379240_conj_f_triple_19 : A379240_conj_f_triple 19 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_19]

  rfl

theorem A379240_f_20 : A379240_f 20 = A379240_F_val.case_n 20 := by

  unfold A379240_f A085731

  rw [A359550_20, A003415_20]

  rfl

theorem A379240_conj_f_triple_20 : A379240_conj_f_triple 20 = (24, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_20]

  rfl

theorem A379240_f_21 : A379240_f 21 = A379240_F_val.case_pair 10 1 := by

  unfold A379240_f A085731

  rw [A359550_21, A003415_21]

  rfl

theorem A379240_conj_f_triple_21 : A379240_conj_f_triple 21 = (10, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_21]

  rfl

theorem A379240_f_22 : A379240_f 22 = A379240_F_val.case_pair 13 1 := by

  unfold A379240_f A085731

  rw [A359550_22, A003415_22]

  rfl

theorem A379240_conj_f_triple_22 : A379240_conj_f_triple 22 = (13, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_22]

  rfl

theorem A379240_f_23 : A379240_f 23 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_23, A003415_23]

  rfl

theorem A379240_conj_f_triple_23 : A379240_conj_f_triple 23 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_23]

  rfl

theorem A379240_f_24 : A379240_f 24 = A379240_F_val.case_n 24 := by

  unfold A379240_f A085731

  rw [A359550_24, A003415_24]

  rfl

theorem A379240_conj_f_triple_24 : A379240_conj_f_triple 24 = (44, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_24]

  rfl

theorem A379240_f_25 : A379240_f 25 = A379240_F_val.case_pair 10 5 := by

  unfold A379240_f A085731

  rw [A359550_25, A003415_25]

  rfl

theorem A379240_conj_f_triple_25 : A379240_conj_f_triple 25 = (10, 5, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_25]

  rfl

theorem A379240_f_26 : A379240_f 26 = A379240_F_val.case_pair 15 1 := by

  unfold A379240_f A085731

  rw [A359550_26, A003415_26]

  rfl

theorem A379240_conj_f_triple_26 : A379240_conj_f_triple 26 = (15, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_26]

  rfl

theorem A379240_f_27 : A379240_f 27 = A379240_F_val.case_n 27 := by

  unfold A379240_f A085731

  rw [A359550_27, A003415_27]

  rfl

theorem A379240_conj_f_triple_27 : A379240_conj_f_triple 27 = (27, 27, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_27]

  rfl

theorem A379240_f_28 : A379240_f 28 = A379240_F_val.case_n 28 := by

  unfold A379240_f A085731

  rw [A359550_28, A003415_28]

  rfl

theorem A379240_conj_f_triple_28 : A379240_conj_f_triple 28 = (32, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_28]

  rfl

theorem A379240_f_29 : A379240_f 29 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_29, A003415_29]

  rfl

theorem A379240_conj_f_triple_29 : A379240_conj_f_triple 29 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_29]

  rfl

theorem A379240_f_30 : A379240_f 30 = A379240_F_val.case_pair 31 1 := by

  unfold A379240_f A085731

  rw [A359550_30, A003415_30]

  rfl

theorem A379240_conj_f_triple_30 : A379240_conj_f_triple 30 = (31, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_30]

  rfl

theorem A379240_f_31 : A379240_f 31 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_31, A003415_31]

  rfl

theorem A379240_conj_f_triple_31 : A379240_conj_f_triple 31 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_31]

  rfl

theorem A379240_f_32 : A379240_f 32 = A379240_F_val.case_n 32 := by

  unfold A379240_f A085731

  rw [A359550_32, A003415_32]

  rfl

theorem A379240_conj_f_triple_32 : A379240_conj_f_triple 32 = (80, 16, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_32]

  rfl

theorem A379240_f_33 : A379240_f 33 = A379240_F_val.case_pair 14 1 := by

  unfold A379240_f A085731

  rw [A359550_33, A003415_33]

  rfl

theorem A379240_conj_f_triple_33 : A379240_conj_f_triple 33 = (14, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_33]

  rfl

theorem A379240_f_34 : A379240_f 34 = A379240_F_val.case_pair 19 1 := by

  unfold A379240_f A085731

  rw [A359550_34, A003415_34]

  rfl

theorem A379240_conj_f_triple_34 : A379240_conj_f_triple 34 = (19, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_34]

  rfl

theorem A379240_f_35 : A379240_f 35 = A379240_F_val.case_pair 12 1 := by

  unfold A379240_f A085731

  rw [A359550_35, A003415_35]

  rfl

theorem A379240_conj_f_triple_35 : A379240_conj_f_triple 35 = (12, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_35]

  rfl

theorem A379240_f_36 : A379240_f 36 = A379240_F_val.case_n 36 := by

  unfold A379240_f A085731

  rw [A359550_36, A003415_36]

  rfl

theorem A379240_conj_f_triple_36 : A379240_conj_f_triple 36 = (60, 12, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_36]

  rfl

theorem A379240_f_37 : A379240_f 37 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_37, A003415_37]

  rfl

theorem A379240_conj_f_triple_37 : A379240_conj_f_triple 37 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_37]

  rfl

theorem A379240_f_38 : A379240_f 38 = A379240_F_val.case_pair 21 1 := by

  unfold A379240_f A085731

  rw [A359550_38, A003415_38]

  rfl

theorem A379240_conj_f_triple_38 : A379240_conj_f_triple 38 = (21, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_38]

  rfl

theorem A379240_f_39 : A379240_f 39 = A379240_F_val.case_pair 16 1 := by

  unfold A379240_f A085731

  rw [A359550_39, A003415_39]

  rfl

theorem A379240_conj_f_triple_39 : A379240_conj_f_triple 39 = (16, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_39]

  rfl

theorem A379240_f_40 : A379240_f 40 = A379240_F_val.case_n 40 := by

  unfold A379240_f A085731

  rw [A359550_40, A003415_40]

  rfl

theorem A379240_conj_f_triple_40 : A379240_conj_f_triple 40 = (68, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_40]

  rfl

theorem A379240_f_41 : A379240_f 41 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_41, A003415_41]

  rfl

theorem A379240_conj_f_triple_41 : A379240_conj_f_triple 41 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_41]

  rfl

theorem A379240_f_42 : A379240_f 42 = A379240_F_val.case_pair 41 1 := by

  unfold A379240_f A085731

  rw [A359550_42, A003415_42]

  rfl

theorem A379240_conj_f_triple_42 : A379240_conj_f_triple 42 = (41, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_42]

  rfl

theorem A379240_f_43 : A379240_f 43 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_43, A003415_43]

  rfl

theorem A379240_conj_f_triple_43 : A379240_conj_f_triple 43 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_43]

  rfl

theorem A379240_f_44 : A379240_f 44 = A379240_F_val.case_n 44 := by

  unfold A379240_f A085731

  rw [A359550_44, A003415_44]

  rfl

theorem A379240_conj_f_triple_44 : A379240_conj_f_triple 44 = (48, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_44]

  rfl

theorem A379240_f_45 : A379240_f 45 = A379240_F_val.case_pair 39 3 := by

  unfold A379240_f A085731

  rw [A359550_45, A003415_45]

  rfl

theorem A379240_conj_f_triple_45 : A379240_conj_f_triple 45 = (39, 3, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_45]

  rfl

theorem A379240_f_46 : A379240_f 46 = A379240_F_val.case_pair 25 1 := by

  unfold A379240_f A085731

  rw [A359550_46, A003415_46]

  rfl

theorem A379240_conj_f_triple_46 : A379240_conj_f_triple 46 = (25, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_46]

  rfl

theorem A379240_f_47 : A379240_f 47 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_47, A003415_47]

  rfl

theorem A379240_conj_f_triple_47 : A379240_conj_f_triple 47 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_47]

  rfl

theorem A379240_f_48 : A379240_f 48 = A379240_F_val.case_n 48 := by

  unfold A379240_f A085731

  rw [A359550_48, A003415_48]

  rfl

theorem A379240_conj_f_triple_48 : A379240_conj_f_triple 48 = (112, 16, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_48]

  rfl

theorem A379240_f_49 : A379240_f 49 = A379240_F_val.case_pair 14 7 := by

  unfold A379240_f A085731

  rw [A359550_49, A003415_49]

  rfl

theorem A379240_conj_f_triple_49 : A379240_conj_f_triple 49 = (14, 7, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_49]

  rfl

theorem A379240_f_50 : A379240_f 50 = A379240_F_val.case_pair 45 5 := by

  unfold A379240_f A085731

  rw [A359550_50, A003415_50]

  rfl

theorem A379240_conj_f_triple_50 : A379240_conj_f_triple 50 = (45, 5, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_50]

  rfl

theorem A379240_f_51 : A379240_f 51 = A379240_F_val.case_pair 20 1 := by

  unfold A379240_f A085731

  rw [A359550_51, A003415_51]

  rfl

theorem A379240_conj_f_triple_51 : A379240_conj_f_triple 51 = (20, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_51]

  rfl

theorem A379240_f_52 : A379240_f 52 = A379240_F_val.case_n 52 := by

  unfold A379240_f A085731

  rw [A359550_52, A003415_52]

  rfl

theorem A379240_conj_f_triple_52 : A379240_conj_f_triple 52 = (56, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_52]

  rfl

theorem A379240_f_53 : A379240_f 53 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_53, A003415_53]

  rfl

theorem A379240_conj_f_triple_53 : A379240_conj_f_triple 53 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_53]

  rfl

theorem A379240_f_54 : A379240_f 54 = A379240_F_val.case_n 54 := by

  unfold A379240_f A085731

  rw [A359550_54, A003415_54]

  rfl

theorem A379240_conj_f_triple_54 : A379240_conj_f_triple 54 = (81, 27, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_54]

  rfl

theorem A379240_f_55 : A379240_f 55 = A379240_F_val.case_pair 16 1 := by

  unfold A379240_f A085731

  rw [A359550_55, A003415_55]

  rfl

theorem A379240_conj_f_triple_55 : A379240_conj_f_triple 55 = (16, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_55]

  rfl

theorem A379240_f_56 : A379240_f 56 = A379240_F_val.case_n 56 := by

  unfold A379240_f A085731

  rw [A359550_56, A003415_56]

  rfl

theorem A379240_conj_f_triple_56 : A379240_conj_f_triple 56 = (92, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_56]

  rfl

theorem A379240_f_57 : A379240_f 57 = A379240_F_val.case_pair 22 1 := by

  unfold A379240_f A085731

  rw [A359550_57, A003415_57]

  rfl

theorem A379240_conj_f_triple_57 : A379240_conj_f_triple 57 = (22, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_57]

  rfl

theorem A379240_f_58 : A379240_f 58 = A379240_F_val.case_pair 31 1 := by

  unfold A379240_f A085731

  rw [A359550_58, A003415_58]

  rfl

theorem A379240_conj_f_triple_58 : A379240_conj_f_triple 58 = (31, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_58]

  rfl

theorem A379240_f_59 : A379240_f 59 = A379240_F_val.case_pair 1 1 := by

  unfold A379240_f A085731

  rw [A359550_59, A003415_59]

  rfl

theorem A379240_conj_f_triple_59 : A379240_conj_f_triple 59 = (1, 1, 1) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_59]

  rfl

theorem A379240_f_60 : A379240_f 60 = A379240_F_val.case_n 60 := by

  unfold A379240_f A085731

  rw [A359550_60, A003415_60]

  rfl

theorem A379240_conj_f_triple_60 : A379240_conj_f_triple 60 = (92, 4, 2) := by

  unfold A379240_conj_f_triple A085731

  rw [A003415_60]

  rfl

theorem map_range_60 {α : Type} (f : ℕ → α) : (List.range 60).map (fun i => f (i + 1)) = [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31, f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39, f 40, f 41, f 42, f 43, f 44, f 45, f 46, f 47, f 48, f 49, f 50, f 51, f 52, f 53, f 54, f 55, f 56, f 57, f 58, f 59, f 60] := by rfl

theorem A379240_60 : A379240 60 = 42 := by
  unfold A379240 rgs_transform
  rw [map_range_60]
  rw [A379240_f_1, A379240_f_2, A379240_f_3, A379240_f_4, A379240_f_5, A379240_f_6, A379240_f_7, A379240_f_8, A379240_f_9, A379240_f_10, A379240_f_11, A379240_f_12, A379240_f_13, A379240_f_14, A379240_f_15, A379240_f_16, A379240_f_17, A379240_f_18, A379240_f_19, A379240_f_20, A379240_f_21, A379240_f_22, A379240_f_23, A379240_f_24, A379240_f_25, A379240_f_26, A379240_f_27, A379240_f_28, A379240_f_29, A379240_f_30, A379240_f_31, A379240_f_32, A379240_f_33, A379240_f_34, A379240_f_35, A379240_f_36, A379240_f_37, A379240_f_38, A379240_f_39, A379240_f_40, A379240_f_41, A379240_f_42, A379240_f_43, A379240_f_44, A379240_f_45, A379240_f_46, A379240_f_47, A379240_f_48, A379240_f_49, A379240_f_50, A379240_f_51, A379240_f_52, A379240_f_53, A379240_f_54, A379240_f_55, A379240_f_56, A379240_f_57, A379240_f_58, A379240_f_59, A379240_f_60]
  rfl

theorem A379240_conjecture_60 : A379240_conjecture 60 = 41 := by
  unfold A379240_conjecture rgs_transform
  rw [map_range_60]
  rw [A379240_conj_f_triple_1, A379240_conj_f_triple_2, A379240_conj_f_triple_3, A379240_conj_f_triple_4, A379240_conj_f_triple_5, A379240_conj_f_triple_6, A379240_conj_f_triple_7, A379240_conj_f_triple_8, A379240_conj_f_triple_9, A379240_conj_f_triple_10, A379240_conj_f_triple_11, A379240_conj_f_triple_12, A379240_conj_f_triple_13, A379240_conj_f_triple_14, A379240_conj_f_triple_15, A379240_conj_f_triple_16, A379240_conj_f_triple_17, A379240_conj_f_triple_18, A379240_conj_f_triple_19, A379240_conj_f_triple_20, A379240_conj_f_triple_21, A379240_conj_f_triple_22, A379240_conj_f_triple_23, A379240_conj_f_triple_24, A379240_conj_f_triple_25, A379240_conj_f_triple_26, A379240_conj_f_triple_27, A379240_conj_f_triple_28, A379240_conj_f_triple_29, A379240_conj_f_triple_30, A379240_conj_f_triple_31, A379240_conj_f_triple_32, A379240_conj_f_triple_33, A379240_conj_f_triple_34, A379240_conj_f_triple_35, A379240_conj_f_triple_36, A379240_conj_f_triple_37, A379240_conj_f_triple_38, A379240_conj_f_triple_39, A379240_conj_f_triple_40, A379240_conj_f_triple_41, A379240_conj_f_triple_42, A379240_conj_f_triple_43, A379240_conj_f_triple_44, A379240_conj_f_triple_45, A379240_conj_f_triple_46, A379240_conj_f_triple_47, A379240_conj_f_triple_48, A379240_conj_f_triple_49, A379240_conj_f_triple_50, A379240_conj_f_triple_51, A379240_conj_f_triple_52, A379240_conj_f_triple_53, A379240_conj_f_triple_54, A379240_conj_f_triple_55, A379240_conj_f_triple_56, A379240_conj_f_triple_57, A379240_conj_f_triple_58, A379240_conj_f_triple_59, A379240_conj_f_triple_60]
  rfl

theorem A379240_conjecture_equality.disproof : ¬ (∀ (n : ℕ), A379240 n = A379240_conjecture n) := by
  intro h
  have h_60 := h 60
  rw [A379240_60, A379240_conjecture_60] at h_60
  omega
