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



def my_factors_fuel (fuel n d : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if n < d * d then (if n > 1 then [n] else [])
    else if n % d = 0 then d :: my_factors_fuel fuel' (n / d) d
    else my_factors_fuel fuel' n (d + 1)

def my_factors (n : ℕ) := my_factors_fuel n n 2

lemma my_factors_eq_1 : primeFactorsList 1 = my_factors 1 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_2 : primeFactorsList 2 = my_factors 2 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_3 : primeFactorsList 3 = my_factors 3 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_4 : primeFactorsList 4 = my_factors 4 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_5 : primeFactorsList 5 = my_factors 5 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_6 : primeFactorsList 6 = my_factors 6 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_7 : primeFactorsList 7 = my_factors 7 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_8 : primeFactorsList 8 = my_factors 8 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_9 : primeFactorsList 9 = my_factors 9 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_10 : primeFactorsList 10 = my_factors 10 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_11 : primeFactorsList 11 = my_factors 11 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_12 : primeFactorsList 12 = my_factors 12 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_13 : primeFactorsList 13 = my_factors 13 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_14 : primeFactorsList 14 = my_factors 14 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_15 : primeFactorsList 15 = my_factors 15 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_16 : primeFactorsList 16 = my_factors 16 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_17 : primeFactorsList 17 = my_factors 17 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_18 : primeFactorsList 18 = my_factors 18 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_19 : primeFactorsList 19 = my_factors 19 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_20 : primeFactorsList 20 = my_factors 20 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_21 : primeFactorsList 21 = my_factors 21 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_22 : primeFactorsList 22 = my_factors 22 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_23 : primeFactorsList 23 = my_factors 23 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_24 : primeFactorsList 24 = my_factors 24 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_25 : primeFactorsList 25 = my_factors 25 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_26 : primeFactorsList 26 = my_factors 26 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_27 : primeFactorsList 27 = my_factors 27 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_28 : primeFactorsList 28 = my_factors 28 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_29 : primeFactorsList 29 = my_factors 29 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_30 : primeFactorsList 30 = my_factors 30 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_31 : primeFactorsList 31 = my_factors 31 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_32 : primeFactorsList 32 = my_factors 32 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_33 : primeFactorsList 33 = my_factors 33 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_34 : primeFactorsList 34 = my_factors 34 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_35 : primeFactorsList 35 = my_factors 35 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_36 : primeFactorsList 36 = my_factors 36 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_37 : primeFactorsList 37 = my_factors 37 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_38 : primeFactorsList 38 = my_factors 38 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_39 : primeFactorsList 39 = my_factors 39 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_40 : primeFactorsList 40 = my_factors 40 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_41 : primeFactorsList 41 = my_factors 41 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_42 : primeFactorsList 42 = my_factors 42 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_43 : primeFactorsList 43 = my_factors 43 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_44 : primeFactorsList 44 = my_factors 44 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_45 : primeFactorsList 45 = my_factors 45 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_46 : primeFactorsList 46 = my_factors 46 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_47 : primeFactorsList 47 = my_factors 47 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_48 : primeFactorsList 48 = my_factors 48 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_49 : primeFactorsList 49 = my_factors 49 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_50 : primeFactorsList 50 = my_factors 50 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_51 : primeFactorsList 51 = my_factors 51 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_52 : primeFactorsList 52 = my_factors 52 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_53 : primeFactorsList 53 = my_factors 53 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_54 : primeFactorsList 54 = my_factors 54 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_55 : primeFactorsList 55 = my_factors 55 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_56 : primeFactorsList 56 = my_factors 56 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_57 : primeFactorsList 57 = my_factors 57 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_58 : primeFactorsList 58 = my_factors 58 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_59 : primeFactorsList 59 = my_factors 59 := by simp [my_factors, my_factors_fuel]
lemma my_factors_eq_60 : primeFactorsList 60 = my_factors 60 := by simp [my_factors, my_factors_fuel]

lemma my_factors_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 60) : primeFactorsList n = my_factors n := by
  have h_1 : n = 1 ∨ n ≠ 1 := eq_or_ne n 1
  cases h_1 with | inl h => rw [h]; exact my_factors_eq_1 | inr hne_1 => 
  have h_2 : n = 2 ∨ n ≠ 2 := eq_or_ne n 2
  cases h_2 with | inl h => rw [h]; exact my_factors_eq_2 | inr hne_2 => 
  have h_3 : n = 3 ∨ n ≠ 3 := eq_or_ne n 3
  cases h_3 with | inl h => rw [h]; exact my_factors_eq_3 | inr hne_3 => 
  have h_4 : n = 4 ∨ n ≠ 4 := eq_or_ne n 4
  cases h_4 with | inl h => rw [h]; exact my_factors_eq_4 | inr hne_4 => 
  have h_5 : n = 5 ∨ n ≠ 5 := eq_or_ne n 5
  cases h_5 with | inl h => rw [h]; exact my_factors_eq_5 | inr hne_5 => 
  have h_6 : n = 6 ∨ n ≠ 6 := eq_or_ne n 6
  cases h_6 with | inl h => rw [h]; exact my_factors_eq_6 | inr hne_6 => 
  have h_7 : n = 7 ∨ n ≠ 7 := eq_or_ne n 7
  cases h_7 with | inl h => rw [h]; exact my_factors_eq_7 | inr hne_7 => 
  have h_8 : n = 8 ∨ n ≠ 8 := eq_or_ne n 8
  cases h_8 with | inl h => rw [h]; exact my_factors_eq_8 | inr hne_8 => 
  have h_9 : n = 9 ∨ n ≠ 9 := eq_or_ne n 9
  cases h_9 with | inl h => rw [h]; exact my_factors_eq_9 | inr hne_9 => 
  have h_10 : n = 10 ∨ n ≠ 10 := eq_or_ne n 10
  cases h_10 with | inl h => rw [h]; exact my_factors_eq_10 | inr hne_10 => 
  have h_11 : n = 11 ∨ n ≠ 11 := eq_or_ne n 11
  cases h_11 with | inl h => rw [h]; exact my_factors_eq_11 | inr hne_11 => 
  have h_12 : n = 12 ∨ n ≠ 12 := eq_or_ne n 12
  cases h_12 with | inl h => rw [h]; exact my_factors_eq_12 | inr hne_12 => 
  have h_13 : n = 13 ∨ n ≠ 13 := eq_or_ne n 13
  cases h_13 with | inl h => rw [h]; exact my_factors_eq_13 | inr hne_13 => 
  have h_14 : n = 14 ∨ n ≠ 14 := eq_or_ne n 14
  cases h_14 with | inl h => rw [h]; exact my_factors_eq_14 | inr hne_14 => 
  have h_15 : n = 15 ∨ n ≠ 15 := eq_or_ne n 15
  cases h_15 with | inl h => rw [h]; exact my_factors_eq_15 | inr hne_15 => 
  have h_16 : n = 16 ∨ n ≠ 16 := eq_or_ne n 16
  cases h_16 with | inl h => rw [h]; exact my_factors_eq_16 | inr hne_16 => 
  have h_17 : n = 17 ∨ n ≠ 17 := eq_or_ne n 17
  cases h_17 with | inl h => rw [h]; exact my_factors_eq_17 | inr hne_17 => 
  have h_18 : n = 18 ∨ n ≠ 18 := eq_or_ne n 18
  cases h_18 with | inl h => rw [h]; exact my_factors_eq_18 | inr hne_18 => 
  have h_19 : n = 19 ∨ n ≠ 19 := eq_or_ne n 19
  cases h_19 with | inl h => rw [h]; exact my_factors_eq_19 | inr hne_19 => 
  have h_20 : n = 20 ∨ n ≠ 20 := eq_or_ne n 20
  cases h_20 with | inl h => rw [h]; exact my_factors_eq_20 | inr hne_20 => 
  have h_21 : n = 21 ∨ n ≠ 21 := eq_or_ne n 21
  cases h_21 with | inl h => rw [h]; exact my_factors_eq_21 | inr hne_21 => 
  have h_22 : n = 22 ∨ n ≠ 22 := eq_or_ne n 22
  cases h_22 with | inl h => rw [h]; exact my_factors_eq_22 | inr hne_22 => 
  have h_23 : n = 23 ∨ n ≠ 23 := eq_or_ne n 23
  cases h_23 with | inl h => rw [h]; exact my_factors_eq_23 | inr hne_23 => 
  have h_24 : n = 24 ∨ n ≠ 24 := eq_or_ne n 24
  cases h_24 with | inl h => rw [h]; exact my_factors_eq_24 | inr hne_24 => 
  have h_25 : n = 25 ∨ n ≠ 25 := eq_or_ne n 25
  cases h_25 with | inl h => rw [h]; exact my_factors_eq_25 | inr hne_25 => 
  have h_26 : n = 26 ∨ n ≠ 26 := eq_or_ne n 26
  cases h_26 with | inl h => rw [h]; exact my_factors_eq_26 | inr hne_26 => 
  have h_27 : n = 27 ∨ n ≠ 27 := eq_or_ne n 27
  cases h_27 with | inl h => rw [h]; exact my_factors_eq_27 | inr hne_27 => 
  have h_28 : n = 28 ∨ n ≠ 28 := eq_or_ne n 28
  cases h_28 with | inl h => rw [h]; exact my_factors_eq_28 | inr hne_28 => 
  have h_29 : n = 29 ∨ n ≠ 29 := eq_or_ne n 29
  cases h_29 with | inl h => rw [h]; exact my_factors_eq_29 | inr hne_29 => 
  have h_30 : n = 30 ∨ n ≠ 30 := eq_or_ne n 30
  cases h_30 with | inl h => rw [h]; exact my_factors_eq_30 | inr hne_30 => 
  have h_31 : n = 31 ∨ n ≠ 31 := eq_or_ne n 31
  cases h_31 with | inl h => rw [h]; exact my_factors_eq_31 | inr hne_31 => 
  have h_32 : n = 32 ∨ n ≠ 32 := eq_or_ne n 32
  cases h_32 with | inl h => rw [h]; exact my_factors_eq_32 | inr hne_32 => 
  have h_33 : n = 33 ∨ n ≠ 33 := eq_or_ne n 33
  cases h_33 with | inl h => rw [h]; exact my_factors_eq_33 | inr hne_33 => 
  have h_34 : n = 34 ∨ n ≠ 34 := eq_or_ne n 34
  cases h_34 with | inl h => rw [h]; exact my_factors_eq_34 | inr hne_34 => 
  have h_35 : n = 35 ∨ n ≠ 35 := eq_or_ne n 35
  cases h_35 with | inl h => rw [h]; exact my_factors_eq_35 | inr hne_35 => 
  have h_36 : n = 36 ∨ n ≠ 36 := eq_or_ne n 36
  cases h_36 with | inl h => rw [h]; exact my_factors_eq_36 | inr hne_36 => 
  have h_37 : n = 37 ∨ n ≠ 37 := eq_or_ne n 37
  cases h_37 with | inl h => rw [h]; exact my_factors_eq_37 | inr hne_37 => 
  have h_38 : n = 38 ∨ n ≠ 38 := eq_or_ne n 38
  cases h_38 with | inl h => rw [h]; exact my_factors_eq_38 | inr hne_38 => 
  have h_39 : n = 39 ∨ n ≠ 39 := eq_or_ne n 39
  cases h_39 with | inl h => rw [h]; exact my_factors_eq_39 | inr hne_39 => 
  have h_40 : n = 40 ∨ n ≠ 40 := eq_or_ne n 40
  cases h_40 with | inl h => rw [h]; exact my_factors_eq_40 | inr hne_40 => 
  have h_41 : n = 41 ∨ n ≠ 41 := eq_or_ne n 41
  cases h_41 with | inl h => rw [h]; exact my_factors_eq_41 | inr hne_41 => 
  have h_42 : n = 42 ∨ n ≠ 42 := eq_or_ne n 42
  cases h_42 with | inl h => rw [h]; exact my_factors_eq_42 | inr hne_42 => 
  have h_43 : n = 43 ∨ n ≠ 43 := eq_or_ne n 43
  cases h_43 with | inl h => rw [h]; exact my_factors_eq_43 | inr hne_43 => 
  have h_44 : n = 44 ∨ n ≠ 44 := eq_or_ne n 44
  cases h_44 with | inl h => rw [h]; exact my_factors_eq_44 | inr hne_44 => 
  have h_45 : n = 45 ∨ n ≠ 45 := eq_or_ne n 45
  cases h_45 with | inl h => rw [h]; exact my_factors_eq_45 | inr hne_45 => 
  have h_46 : n = 46 ∨ n ≠ 46 := eq_or_ne n 46
  cases h_46 with | inl h => rw [h]; exact my_factors_eq_46 | inr hne_46 => 
  have h_47 : n = 47 ∨ n ≠ 47 := eq_or_ne n 47
  cases h_47 with | inl h => rw [h]; exact my_factors_eq_47 | inr hne_47 => 
  have h_48 : n = 48 ∨ n ≠ 48 := eq_or_ne n 48
  cases h_48 with | inl h => rw [h]; exact my_factors_eq_48 | inr hne_48 => 
  have h_49 : n = 49 ∨ n ≠ 49 := eq_or_ne n 49
  cases h_49 with | inl h => rw [h]; exact my_factors_eq_49 | inr hne_49 => 
  have h_50 : n = 50 ∨ n ≠ 50 := eq_or_ne n 50
  cases h_50 with | inl h => rw [h]; exact my_factors_eq_50 | inr hne_50 => 
  have h_51 : n = 51 ∨ n ≠ 51 := eq_or_ne n 51
  cases h_51 with | inl h => rw [h]; exact my_factors_eq_51 | inr hne_51 => 
  have h_52 : n = 52 ∨ n ≠ 52 := eq_or_ne n 52
  cases h_52 with | inl h => rw [h]; exact my_factors_eq_52 | inr hne_52 => 
  have h_53 : n = 53 ∨ n ≠ 53 := eq_or_ne n 53
  cases h_53 with | inl h => rw [h]; exact my_factors_eq_53 | inr hne_53 => 
  have h_54 : n = 54 ∨ n ≠ 54 := eq_or_ne n 54
  cases h_54 with | inl h => rw [h]; exact my_factors_eq_54 | inr hne_54 => 
  have h_55 : n = 55 ∨ n ≠ 55 := eq_or_ne n 55
  cases h_55 with | inl h => rw [h]; exact my_factors_eq_55 | inr hne_55 => 
  have h_56 : n = 56 ∨ n ≠ 56 := eq_or_ne n 56
  cases h_56 with | inl h => rw [h]; exact my_factors_eq_56 | inr hne_56 => 
  have h_57 : n = 57 ∨ n ≠ 57 := eq_or_ne n 57
  cases h_57 with | inl h => rw [h]; exact my_factors_eq_57 | inr hne_57 => 
  have h_58 : n = 58 ∨ n ≠ 58 := eq_or_ne n 58
  cases h_58 with | inl h => rw [h]; exact my_factors_eq_58 | inr hne_58 => 
  have h_59 : n = 59 ∨ n ≠ 59 := eq_or_ne n 59
  cases h_59 with | inl h => rw [h]; exact my_factors_eq_59 | inr hne_59 => 
  have h_60 : n = 60 ∨ n ≠ 60 := eq_or_ne n 60
  cases h_60 with | inl h => rw [h]; exact my_factors_eq_60 | inr hne_60 => 
  omega


def my_A359550 (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else if (my_factors n).any (fun p => (my_factors n).count p ≥ p) then 0
  else 1

def my_A003415 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (my_factors n).map (fun p => n / p) |>.sum

def my_A085731 (n : ℕ) : ℕ := Nat.gcd (my_A003415 n) n

def my_A379240_f (n : ℕ) : A379240_F_val :=
  if n = 0 then A379240_F_val.case_n 0
  else
    if my_A359550 n = 1 then
      A379240_F_val.case_pair (my_A003415 n) (my_A085731 n)
    else
      A379240_F_val.case_n n

def my_A379240_conj_f_triple (n : ℕ) : ℕ × ℕ × ℕ :=
  (my_A003415 n, my_A085731 n, A376418 n)

def my_A379240 (n : ℕ) : ℕ := rgs_transform my_A379240_f n
def my_A379240_conjecture (n : ℕ) : ℕ := rgs_transform my_A379240_conj_f_triple n

theorem A359550_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 60) : A359550 n = my_A359550 n := by
  unfold A359550 my_A359550
  have h_factors : primeFactorsList n = my_factors n := my_factors_eq n h1 h2
  have h_iff : ((Finset.filter (fun p => n.factorization p ≥ p) n.factorization.support).card > 0) ↔ ((n.primeFactorsList.any (fun p => n.primeFactorsList.count p ≥ p)) = true) := by
    have h_card : ∀ s : Finset ℕ, s.card > 0 ↔ s.Nonempty := fun s => Finset.card_pos
    rw [h_card, Finset.filter_nonempty_iff, List.any_eq_true]
    simp [Nat.primeFactorsList_count_eq]
  have h_eq : (if (Finset.filter (fun p => n.factorization p ≥ p) n.factorization.support).card > 0 then 0 else 1) = (if (n.primeFactorsList.any (fun p => n.primeFactorsList.count p ≥ p)) then 0 else 1) := by
    by_cases hc : (Finset.filter (fun p => n.factorization p ≥ p) n.factorization.support).card > 0
    · rw [if_pos hc, if_pos (h_iff.mp hc)]
    · rw [if_neg hc, if_neg (mt h_iff.mpr hc)]
  by_cases hn : n ≤ 1
  · simp [hn]
  · simp only [hn, ite_false, h_eq, h_factors]

theorem A003415_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 60) : A003415 n = my_A003415 n := by
  have h_factors : primeFactorsList n = my_factors n := my_factors_eq n h1 h2
  unfold A003415 my_A003415
  split_ifs with hn
  · rfl
  · rw [Finset.sum_list_map_count]
    have h_supp : n.factorization.support = n.primeFactorsList.toFinset := by
      ext p
      simp
    rw [h_supp]
    have h_eq : (∑ p ∈ n.primeFactorsList.toFinset, n / p * n.factorization p) = (∑ m ∈ n.primeFactorsList.toFinset, List.count m n.primeFactorsList • (n / m)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.primeFactorsList_count_eq]
      exact Nat.mul_comm _ _
    rw [h_eq, h_factors]

theorem A085731_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 60) : A085731 n = my_A085731 n := by
  unfold A085731 my_A085731
  rw [A003415_eq n h1 h2]

theorem A379240_f_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 60) : A379240_f n = my_A379240_f n := by
  unfold A379240_f my_A379240_f
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    rw [A359550_eq n h1 h2]
    by_cases h359 : my_A359550 n = 1
    · rw [if_pos h359, if_pos h359]
      rw [A003415_eq n h1 h2, A085731_eq n h1 h2]
    · rw [if_neg h359, if_neg h359]

theorem A379240_conj_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 60) : A379240_conj_f_triple n = my_A379240_conj_f_triple n := by
  unfold A379240_conj_f_triple my_A379240_conj_f_triple
  rw [A003415_eq n h1 h2, A085731_eq n h1 h2]

lemma map_ext {α β : Type} (f g : α → β) (l : List α) (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  exact List.map_congr_left h

theorem rgs_eq {α : Type} [DecidableEq α] (f g : ℕ → α) (n : ℕ) (hn : n ≠ 0)
  (h_all : ∀ i < n, f (i + 1) = g (i + 1)) (h_n : f n = g n) :
  rgs_transform f n = rgs_transform g n := by
  dsimp [rgs_transform]
  simp only [hn, if_false]
  have h_map : (List.range n).map (fun i => f (i + 1)) = (List.range n).map (fun i => g (i + 1)) := by
    apply map_ext
    intro i hi
    exact h_all i (List.mem_range.mp hi)
  rw [h_map, h_n]

theorem main_neq : A379240 60 ≠ A379240_conjecture 60 := by
  have h_f : A379240 60 = my_A379240 60 := by
    unfold A379240 my_A379240
    apply rgs_eq
    · decide
    · intro i hi
      have h1 : 1 ≤ i + 1 := Nat.le_add_left 1 i
      have h2 : i + 1 ≤ 60 := by omega
      exact A379240_f_eq (i + 1) h1 h2
    · exact A379240_f_eq 60 (by decide) (by decide)
  have h_g : A379240_conjecture 60 = my_A379240_conjecture 60 := by
    unfold A379240_conjecture my_A379240_conjecture
    apply rgs_eq
    · decide
    · intro i hi
      have h1 : 1 ≤ i + 1 := Nat.le_add_left 1 i
      have h2 : i + 1 ≤ 60 := by omega
      exact A379240_conj_eq (i + 1) h1 h2
    · exact A379240_conj_eq 60 (by decide) (by decide)
  rw [h_f, h_g]
  have h_my_neq : my_A379240 60 ≠ my_A379240_conjecture 60 := by decide
  exact h_my_neq


theorem A379240_conjecture_equality (n : ℕ) : A379240 n = A379240_conjecture n := by
  sorry

theorem A379240_conjecture_equality.disproof : ¬ (type_of% @A379240_conjecture_equality) := by
  intro h
  have h60 := h 60
  exact main_neq h60
