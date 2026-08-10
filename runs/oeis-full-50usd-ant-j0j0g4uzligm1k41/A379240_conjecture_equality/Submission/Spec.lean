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

/- ### Helper lemmas about `rgs_transform` -/

section rgs
variable {α : Type} [DecidableEq α]

private lemma union_singleton_getLast? (l : List α) (a : α) :
    (l ∪ [a]).getLast? = some a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.cons_union, List.insert]
    split
    · exact ih
    · rw [List.getLast?_cons, ih]; rfl

private lemma idxOf_last_succ {M : List α} (hnd : M.Nodup) {a : α}
    (h : M.getLast? = some a) : M.idxOf a + 1 = M.length := by
  have hne : M ≠ [] := by rintro rfl; simp at h
  rw [List.getLast?_eq_getLast_of_ne_nil hne] at h
  have hlast : a = M.getLast hne := (Option.some_inj.mp h).symm
  have hlen : 0 < M.length := List.length_pos_of_ne_nil hne
  rw [hlast, List.getLast_eq_getElem, List.Nodup.idxOf_getElem hnd]
  omega

private lemma rgs_eq_len (f : ℕ → α) {n : ℕ} (hn : n ≠ 0) :
    rgs_transform f n = ((List.range n).map (fun i => f (i + 1))).dedup.length := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  unfold rgs_transform
  rw [if_neg hn]
  simp only
  set L := (List.range (m + 1)).map (fun i => f (i + 1)) with hL
  apply idxOf_last_succ (List.nodup_dedup L)
  have hLsplit : L = ((List.range m).map (fun i => f (i + 1))) ++ [f (m + 1)] := by
    rw [hL, List.range_succ, List.map_append]; simp
  rw [hLsplit, List.dedup_append]
  rw [show ([f (m + 1)] : List α).dedup = [f (m + 1)] from rfl]
  exact union_singleton_getLast? _ _

private lemma rgs_card (f : ℕ → α) {n : ℕ} (hn : n ≠ 0) :
    rgs_transform f n = ((Finset.range n).image (fun i => f (i + 1))).card := by
  rw [rgs_eq_len f hn, ← List.card_toFinset]
  congr 1

end rgs

/- ### Number-theoretic lemma: `A359550 m = 1 → A376418 m = 1` -/

private lemma no_big_pow (m : ℕ) (hm : m ≠ 0) (h : A359550 m = 1) (x : ℕ) (hx : 2 ≤ x)
    (hdvd : Pow.pow x x ∣ m) : False := by
  have hxx : x ^ x ∣ m := hdvd
  have hx0 : 0 < x := by omega
  have hx1 : x ≠ 1 := by omega
  set p := x.minFac with hp
  have ppr : p.Prime := Nat.minFac_prime hx1
  have hpx : p ∣ x := Nat.minFac_dvd x
  have hple : p ≤ x := Nat.minFac_le hx0
  have hpp_dvd : p ^ p ∣ m :=
    dvd_trans (dvd_trans (pow_dvd_pow_of_dvd hpx p) (pow_dvd_pow x hple)) hxx
  have hfp : p ≤ m.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization ppr hm).mp hpp_dvd
  have hpsupp : p ∈ m.factorization.support := by
    rw [Finsupp.mem_support_iff]
    have : 2 ≤ p := ppr.two_le
    omega
  have hmem : p ∈ Finset.filter (fun q => m.factorization q ≥ q) m.factorization.support := by
    rw [Finset.mem_filter]; exact ⟨hpsupp, hfp⟩
  have hcard : (Finset.filter (fun q => m.factorization q ≥ q) m.factorization.support).card > 0 :=
    Finset.card_pos.mpr ⟨p, hmem⟩
  have hm1 : ¬ m ≤ 1 := by
    intro hle
    interval_cases m
    · exact hm rfl
    · have hd1 : x ^ x = 1 := Nat.dvd_one.mp hxx
      have : x ≤ x ^ x := Nat.le_self_pow (by omega) x
      omega
  have : A359550 m = 0 := by unfold A359550; rw [if_neg hm1, if_pos hcard]
  omega

private lemma key1 (m : ℕ) (h : A359550 m = 1) : A376418 m = 1 := by
  unfold A376418
  have hfilt : (Finset.filter (fun k : ℕ => k ≥ 1 ∧ Pow.pow k k ∣ m)
      (Finset.range (m + 2))) = {1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ?_⟩
      exact one_dvd m
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxr, hx1, hxd⟩ := hx
      by_contra hne
      have hx2 : 2 ≤ x := by omega
      have hm0 : m ≠ 0 := by omega
      exact (no_big_pow m hm0 h x hx2 hxd).elim
  rw [hfilt, Finset.card_singleton]

/- ### Concrete values at 56 and 60 -/

open Finsupp in
private theorem fact56 : (56 : ℕ).factorization = single 2 3 + single 7 1 := by
  have : (56 : ℕ) = 2 ^ 3 * 7 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by norm_num), Nat.Prime.factorization (by norm_num)]

open Finsupp in
private theorem fact60 : (60 : ℕ).factorization = single 2 2 + single 3 1 + single 5 1 := by
  have : (60 : ℕ) = 2 ^ 2 * 3 * 5 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by norm_num),
      Nat.Prime.factorization (by norm_num), Nat.Prime.factorization (by norm_num)]

open Finsupp in
private theorem A003415_56 : A003415 56 = 92 := by
  have hsum : A003415 56 = (56 : ℕ).factorization.sum (fun p e => (56 / p) * e) := by
    rw [A003415, if_neg (by norm_num)]; rfl
  rw [hsum, fact56,
      Finsupp.sum_add_index' (by intro; simp) (by intros; ring),
      Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

open Finsupp in
private theorem A003415_60 : A003415 60 = 92 := by
  have hsum : A003415 60 = (60 : ℕ).factorization.sum (fun p e => (60 / p) * e) := by
    rw [A003415, if_neg (by norm_num)]; rfl
  rw [hsum, fact60,
      Finsupp.sum_add_index' (by intro; simp) (by intros; ring),
      Finsupp.sum_add_index' (by intro; simp) (by intros; ring),
      Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
      Finsupp.sum_single_index (by simp)]

private theorem A085731_56 : A085731 56 = 4 := by
  unfold A085731; rw [A003415_56]; decide

private theorem A085731_60 : A085731 60 = 4 := by
  unfold A085731; rw [A003415_60]; decide

private theorem A376418_56 : A376418 56 = 2 := by decide
private theorem A376418_60 : A376418 60 = 2 := by decide

open Finsupp in
private theorem A359550_56 : A359550 56 = 0 := by
  rw [A359550, if_neg (by norm_num), if_pos]
  apply Finset.card_pos.mpr
  refine ⟨2, ?_⟩
  rw [Finset.mem_filter]
  have hval : (56 : ℕ).factorization 2 = 3 := by
    rw [fact56]; simp [Finsupp.add_apply, Finsupp.single_apply]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff]; omega
  · omega

open Finsupp in
private theorem A359550_60 : A359550 60 = 0 := by
  rw [A359550, if_neg (by norm_num), if_pos]
  apply Finset.card_pos.mpr
  refine ⟨2, ?_⟩
  rw [Finset.mem_filter]
  have hval : (60 : ℕ).factorization 2 = 2 := by
    rw [fact60]; simp [Finsupp.add_apply, Finsupp.single_apply]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff]; omega
  · omega

/- ### The reduction map and the disproof -/

private def rho : A379240_F_val → ℕ × ℕ × ℕ
  | A379240_F_val.case_pair a b => (a, b, 1)
  | A379240_F_val.case_n m => (A003415 m, A085731 m, A376418 m)

private lemma rho_f (i : ℕ) :
    rho (A379240_f (i + 1)) = A379240_conj_f_triple (i + 1) := by
  unfold A379240_f
  rw [if_neg (Nat.succ_ne_zero i)]
  by_cases hc : A359550 (i + 1) = 1
  · rw [if_pos hc]
    show rho (A379240_F_val.case_pair (A003415 (i + 1)) (A085731 (i + 1)))
        = A379240_conj_f_triple (i + 1)
    unfold rho A379240_conj_f_triple
    rw [key1 (i + 1) hc]
  · rw [if_neg hc]
    rfl

/-
A379240 It is conjectured that this is also the lexicographically earliest infinite sequence such
that a(i) = a(j) => A003415(i) = A003415(j), A085731(i) = A085731(j) and A376418(i) = A376418(j),
for all i, j >= 1, i.e., the restricted growth sequence transform of the triple
[A003415(n), A085731(n), A376418(n)]. This is true if for every pair of $i$ and $j$ for which
$i \ne j$, and $\mathtt{A376418}(i) = \mathtt{A376418}(j) > 0$, the ordered pairs
$[\mathtt{A003415}(i), \mathtt{A085731}(i)]$ and $[\mathtt{A003415}(j), \mathtt{A085731}(j)]$
differ from each other.

This conjecture is FALSE: at n = 60 the two sequences differ.
-/
theorem A379240_conjecture_equality.disproof :
    ¬ ∀ (n : ℕ), A379240 n = A379240_conjecture n := by
  intro h
  have h60 := h 60
  rw [A379240, A379240_conjecture, rgs_card A379240_f (by norm_num),
      rgs_card A379240_conj_f_triple (by norm_num)] at h60
  set s := (Finset.range 60).image (fun i => A379240_f (i + 1)) with hs
  have himg : (Finset.range 60).image (fun i => A379240_conj_f_triple (i + 1))
      = s.image rho := by
    rw [hs, Finset.image_image]
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply]
    exact (rho_f i).symm
  rw [himg] at h60
  -- h60 : s.card = (s.image rho).card
  have hinj : Set.InjOn rho ↑s := Finset.injOn_of_card_image_eq h60.symm
  -- two distinct elements of s with equal rho
  have hf56 : A379240_f 56 = A379240_F_val.case_n 56 := by
    unfold A379240_f; rw [if_neg (by norm_num), if_neg (by rw [A359550_56]; norm_num)]
  have hf60 : A379240_f 60 = A379240_F_val.case_n 60 := by
    unfold A379240_f; rw [if_neg (by norm_num), if_neg (by rw [A359550_60]; norm_num)]
  have hmem56 : A379240_F_val.case_n 56 ∈ s := by
    rw [hs, Finset.mem_image]
    exact ⟨55, by rw [Finset.mem_range]; norm_num, by rw [← hf56]⟩
  have hmem60 : A379240_F_val.case_n 60 ∈ s := by
    rw [hs, Finset.mem_image]
    exact ⟨59, by rw [Finset.mem_range]; norm_num, by rw [← hf60]⟩
  have hrho : rho (A379240_F_val.case_n 56) = rho (A379240_F_val.case_n 60) := by
    show (A003415 56, A085731 56, A376418 56) = (A003415 60, A085731 60, A376418 60)
    rw [A003415_56, A003415_60, A085731_56, A085731_60, A376418_56, A376418_60]
  have := hinj hmem56 hmem60 hrho
  exact absurd this (by decide)

