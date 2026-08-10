import FormalConjectures.Util.ProblemImports

open Nat List Finset

/--
A251758: Let $n \ge 2$ be a positive integer with divisors $1 = d_1 < d_2 < \dots < d_k = n$,
and $s = d_1 d_2 + d_2 d_3 + \dots + d_{k-1} d_k$.
The sequence lists the values $a(n) = \lfloor n^2 / s \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Get the list of divisors in increasing order.
  let divisors_list : List ℕ := (Nat.divisors n).sort (· ≤ ·)

  -- Calculate s = sum of product of successive divisors: s = d₁d₂ + d₂d₃ + ...
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum

  -- The result is ⌊n^2 / s⌋. Since Nat.div is floor division, and s > 0 for n >= 2.
  if s = 0 then 0
  else n ^ 2 / s

/-- The set of integers $n \ge 2$ such that $a(n)=k$. -/
def first_occurrence_set (k : ℕ) : Set ℕ :=
  { n : ℕ | n ≥ 2 ∧ a n = k }

/-! ### Efficient, kernel-computable version of `a` and its correctness. -/

namespace A251758

/-- Kernel-reducible integer square root helper. -/
def isqrtUp : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k
  | (fuel+1), n, k => if (k+1)*(k+1) ≤ n then isqrtUp fuel n (k+1) else k

def isqrt (n : ℕ) : ℕ := isqrtUp n n 0

theorem isqrtUp_eq (n : ℕ) : ∀ (fuel k : ℕ), k ≤ Nat.sqrt n → Nat.sqrt n ≤ k + fuel →
    isqrtUp fuel n k = Nat.sqrt n := by
  intro fuel
  induction fuel with
  | zero => intro k h1 h2; simp at h2; unfold isqrtUp; omega
  | succ f ih =>
    intro k h1 h2; unfold isqrtUp
    by_cases hc : (k+1)*(k+1) ≤ n
    · simp only [hc, if_true]
      have : k+1 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
      exact ih (k+1) this (by omega)
    · simp only [hc, if_false]
      have : Nat.sqrt n < k + 1 := by rw [Nat.sqrt_lt]; omega
      omega

theorem isqrt_eq (n : ℕ) : isqrt n = Nat.sqrt n := by
  unfold isqrt; exact isqrtUp_eq n n 0 (Nat.zero_le _) (by have := Nat.sqrt_le_self n; omega)

def smallD (n : ℕ) : List ℕ := (List.range (isqrt n + 1)).filter (fun d => 1 ≤ d && decide (d ∣ n))
def largeD (n : ℕ) : List ℕ :=
  (smallD n).reverse.filterMap (fun d => if d*d = n then none else some (n/d))
def divFast (n : ℕ) : List ℕ := smallD n ++ largeD n
def aFast (n : ℕ) : ℕ :=
  let dl := divFast n
  let s := ((dl.zip dl.tail).map (fun p => p.1 * p.2)).sum
  if s = 0 then 0 else n^2 / s

theorem mem_smallD (n d : ℕ) : d ∈ smallD n ↔ 1 ≤ d ∧ d ∣ n ∧ d ≤ Nat.sqrt n := by
  simp only [smallD, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    isqrt_eq, Nat.lt_succ_iff]; tauto

theorem mem_largeD (n y : ℕ) (hn : 1 ≤ n) :
    y ∈ largeD n ↔ y ∣ n ∧ Nat.sqrt n < y := by
  simp only [largeD, List.mem_filterMap, List.mem_reverse, mem_smallD]
  constructor
  · rintro ⟨d, ⟨hd1, hddvd, hdle⟩, hcond⟩
    split at hcond
    · simp at hcond
    · rename_i hne; simp only [Option.some.injEq] at hcond; subst hcond
      obtain ⟨c, rfl⟩ := hddvd
      have hdpos : 0 < d := hd1
      have hdc : d * d ≤ d * c := Nat.le_sqrt.mp hdle
      have hne' : d * d ≠ d * c := by simpa [mul_comm] using hne
      have hdltc : d < c := Nat.lt_of_mul_lt_mul_left (a := d) (lt_of_le_of_ne hdc hne')
      rw [Nat.mul_div_cancel_left _ hdpos]
      refine ⟨Dvd.intro_left d rfl, ?_⟩
      rw [Nat.sqrt_lt]; nlinarith
  · rintro ⟨hydvd, hylt⟩
    obtain ⟨c, rfl⟩ := hydvd
    have hypos : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hcy : c < y := by rw [Nat.sqrt_lt] at hylt; nlinarith
    have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    refine ⟨c, ⟨hcpos, Dvd.intro_left y rfl, ?_⟩, ?_⟩
    · rw [Nat.le_sqrt]; nlinarith
    · have hne2 : c * c ≠ y * c := by nlinarith
      simp only [hne2, if_false, Nat.mul_div_cancel _ hcpos]

theorem pairwise_and_mem {α} {l : List α} {P : α → Prop} {R : α → α → Prop}
    (hP : ∀ x ∈ l, P x) (hR : l.Pairwise R) :
    l.Pairwise (fun a b => R a b ∧ P a ∧ P b) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hR ⊢
    refine ⟨fun b hb => ⟨hR.1 b hb, hP x (by simp), hP b (by simp [hb])⟩,
      ih (fun y hy => hP y (by simp [hy])) hR.2⟩

theorem smallD_pw (n : ℕ) : (smallD n).Pairwise (· < ·) := by
  unfold smallD; exact List.Pairwise.filter _ List.pairwise_lt_range

theorem smallD_dvd (n : ℕ) : ∀ x ∈ smallD n, x ∣ n := by
  intro x hx; rw [mem_smallD] at hx; exact hx.2.1

theorem largeD_pw (n : ℕ) (hn : 1 ≤ n) : (largeD n).Pairwise (· < ·) := by
  have hpw : (smallD n).reverse.Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr (smallD_pw n)
  have hmem : ∀ x ∈ (smallD n).reverse, x ∣ n := by
    intro x hx; rw [List.mem_reverse] at hx; exact smallD_dvd n x hx
  have hpair : (smallD n).reverse.Pairwise (fun a b => b < a ∧ a ∣ n ∧ b ∣ n) :=
    pairwise_and_mem hmem hpw
  unfold largeD
  apply List.Pairwise.filterMap _ _ hpair
  · intro a a' hR b hb b' hb'
    obtain ⟨haa', hadvd, ha'dvd⟩ := hR
    have hba : b = n / a := by
      by_cases hc : a * a = n
      · simp [hc] at hb
      · simp only [if_neg hc, Option.some.injEq] at hb; omega
    have hb'a : b' = n / a' := by
      by_cases hc : a' * a' = n
      · simp [hc] at hb'
      · simp only [if_neg hc, Option.some.injEq] at hb'; omega
    subst hba hb'a
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (by omega)
    have ha'pos : 0 < a' := Nat.pos_of_dvd_of_pos ha'dvd (by omega)
    have e1 : n / a * a = n := Nat.div_mul_cancel hadvd
    have e2 : n / a' * a' = n := Nat.div_mul_cancel ha'dvd
    have hq' : 0 < n / a' := Nat.pos_of_ne_zero (by rintro h; rw [h, Nat.zero_mul] at e2; omega)
    by_contra hc
    push_neg at hc
    nlinarith [e1, e2]

theorem divFast_pw (n : ℕ) (hn : 1 ≤ n) : (divFast n).Pairwise (· < ·) := by
  unfold divFast
  rw [List.pairwise_append]
  refine ⟨smallD_pw n, largeD_pw n hn, ?_⟩
  intro x hx y hy
  rw [mem_smallD] at hx; rw [mem_largeD n y hn] at hy
  omega

theorem mem_divFast (n d : ℕ) (hn : 1 ≤ n) : d ∈ divFast n ↔ d ∈ Nat.divisors n := by
  unfold divFast
  rw [List.mem_append, mem_smallD, mem_largeD n d hn, Nat.mem_divisors]
  constructor
  · rintro (⟨_, hd, _⟩ | ⟨hd, _⟩) <;> exact ⟨hd, by omega⟩
  · rintro ⟨hd, _⟩
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by omega)
    by_cases h : d ≤ Nat.sqrt n
    · exact Or.inl ⟨h1, hd, h⟩
    · exact Or.inr ⟨hd, by omega⟩

theorem divFast_eq (n : ℕ) (hn : 1 ≤ n) : divFast n = (Nat.divisors n).sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ => Nat.le_antisymm)
  · exact (divFast_pw n hn).imp (le_of_lt)
  · exact Finset.sort_sorted _ _
  · rw [List.perm_ext_iff_of_nodup ((divFast_pw n hn).imp (fun h => Nat.ne_of_lt h))
        (Finset.sort_nodup _ _)]
    intro x; rw [mem_divFast n x hn, Finset.mem_sort]

theorem aFast_eq (n : ℕ) (hn : 1 ≤ n) : aFast n = a n := by
  unfold aFast a; rw [divFast_eq n hn]

/-- Lower-bound helper: if no `m < A` has `aFast m = k`, then `A` is a lower bound. -/
theorem lower_of_range {k A : ℕ} (h : ∀ m ∈ Finset.range A, aFast m ≠ k) :
    ∀ b ∈ first_occurrence_set k, A ≤ b := by
  rintro b ⟨hb2, hab⟩
  by_contra hlt
  push_neg at hlt
  have hbk : aFast b = k := by rw [aFast_eq b (by omega)]; exact hab
  exact h b (Finset.mem_range.mpr hlt) hbk

/-- Membership helper. -/
theorem mem_set {k A : ℕ} (hA : 2 ≤ A) (h : aFast A = k) : A ∈ first_occurrence_set k := by
  refine ⟨hA, ?_⟩
  rw [← aFast_eq A (by omega)]; exact h

end A251758

open A251758

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il1 : IsLeast (first_occurrence_set 1) 4 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il2 : IsLeast (first_occurrence_set 2) 2 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il3 : IsLeast (first_occurrence_set 3) 3 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il4 : IsLeast (first_occurrence_set 4) 25 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il5 : IsLeast (first_occurrence_set 5) 5 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il6 : IsLeast (first_occurrence_set 6) 49 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il7 : IsLeast (first_occurrence_set 7) 7 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il10 : IsLeast (first_occurrence_set 10) 121 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il11 : IsLeast (first_occurrence_set 11) 11 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il12 : IsLeast (first_occurrence_set 12) 169 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il13 : IsLeast (first_occurrence_set 13) 13 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il16 : IsLeast (first_occurrence_set 16) 289 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem il17 : IsLeast (first_occurrence_set 17) 17 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk9_0 : ∀ m ∈ Finset.Ico 0 1000, aFast m ≠ 9 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk9_1 : ∀ m ∈ Finset.Ico 1000 2000, aFast m ≠ 9 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk9_2 : ∀ m ∈ Finset.Ico 2000 2431, aFast m ≠ 9 := by decide

theorem lbrange9 : ∀ m ∈ Finset.range 2431, aFast m ≠ 9 := by
  intro m hm; rw [Finset.mem_range] at hm
  by_cases h0 : m < 1000
  · exact chunk9_0 m (Finset.mem_Ico.mpr ⟨by omega, h0⟩)
  by_cases h1 : m < 2000
  · exact chunk9_1 m (Finset.mem_Ico.mpr ⟨by omega, h1⟩)
  · exact chunk9_2 m (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_0 : ∀ m ∈ Finset.Ico 0 1000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_1 : ∀ m ∈ Finset.Ico 1000 2000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_2 : ∀ m ∈ Finset.Ico 2000 3000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_3 : ∀ m ∈ Finset.Ico 3000 4000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_4 : ∀ m ∈ Finset.Ico 4000 5000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_5 : ∀ m ∈ Finset.Ico 5000 6000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_6 : ∀ m ∈ Finset.Ico 6000 7000, aFast m ≠ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem chunk15_7 : ∀ m ∈ Finset.Ico 7000 7429, aFast m ≠ 15 := by decide

theorem lbrange15 : ∀ m ∈ Finset.range 7429, aFast m ≠ 15 := by
  intro m hm; rw [Finset.mem_range] at hm
  by_cases h0 : m < 1000
  · exact chunk15_0 m (Finset.mem_Ico.mpr ⟨by omega, h0⟩)
  by_cases h1 : m < 2000
  · exact chunk15_1 m (Finset.mem_Ico.mpr ⟨by omega, h1⟩)
  by_cases h2 : m < 3000
  · exact chunk15_2 m (Finset.mem_Ico.mpr ⟨by omega, h2⟩)
  by_cases h3 : m < 4000
  · exact chunk15_3 m (Finset.mem_Ico.mpr ⟨by omega, h3⟩)
  by_cases h4 : m < 5000
  · exact chunk15_4 m (Finset.mem_Ico.mpr ⟨by omega, h4⟩)
  by_cases h5 : m < 6000
  · exact chunk15_5 m (Finset.mem_Ico.mpr ⟨by omega, h5⟩)
  by_cases h6 : m < 7000
  · exact chunk15_6 m (Finset.mem_Ico.mpr ⟨by omega, h6⟩)
  · exact chunk15_7 m (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

theorem il9 : IsLeast (first_occurrence_set 9) 2431 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range lbrange9⟩
theorem il15 : IsLeast (first_occurrence_set 15) 7429 :=
  ⟨mem_set (by norm_num) (by decide), lower_of_range lbrange15⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem il14_mem : (6678671 : ℕ) ∈ first_occurrence_set 14 :=
  mem_set (by norm_num) (by decide)

/- lb14: lower bound for a(n)=14 via reflection + AM-GM + sigma2 bounds -/
open ArithmeticFunction

theorem zip_tail_reverse (l : List ℕ) :
    l.reverse.zip l.reverse.tail = ((l.zip l.tail).map Prod.swap).reverse := by
  apply List.ext_getElem
  · simp only [List.length_zip, List.length_reverse, List.length_tail, List.length_map]
  · intro i h1 h2
    simp only [List.length_zip, List.length_reverse, List.length_tail, List.length_map,
      lt_min_iff] at h1 h2
    have hlen : (List.map Prod.swap (l.zip l.tail)).length = l.length - 1 := by
      simp only [List.length_map, List.length_zip, List.length_tail]; omega
    rw [List.getElem_zip, List.getElem_reverse]
    have ht : l.reverse.tail[i]'(by simp only [List.length_tail, List.length_reverse]; omega)
        = l.reverse[i+1]'(by simp only [List.length_reverse]; omega) := List.getElem_tail _
    rw [ht, List.getElem_reverse, List.getElem_reverse, List.getElem_map, List.getElem_zip]
    simp only [hlen]
    have ht2 : l.tail[l.length - 1 - 1 - i]'(by simp only [List.length_tail]; omega)
        = l[l.length - 1 - 1 - i + 1]'(by omega) := List.getElem_tail _
    rw [ht2]
    simp only [Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · congr 1; omega
    · congr 1; omega

theorem divisor_reflection (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.divisors n).sort (· ≤ ·)).map (fun d => n / d)
      = ((Nat.divisors n).sort (· ≤ ·)).reverse := by
  set D := (Nat.divisors n).sort (· ≤ ·) with hD
  have hsort : List.Pairwise (· ≤ ·) D := Finset.sort_sorted _ _
  have hpos : ∀ x ∈ D, 0 < x := by
    intro x hx
    rw [hD, Finset.mem_sort] at hx
    exact Nat.pos_of_mem_divisors hx
  -- perm: D.map (n/·) ~ D.reverse
  have hperm : (D.map (fun d => n / d)) ~ D.reverse := by
    refine List.Perm.trans ?_ (List.reverse_perm D).symm
    rw [← Multiset.coe_eq_coe]
    have hinj : Set.InjOn (fun d => n / d) ↑(Nat.divisors n) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Nat.mem_divisors] at ha hb
      have e1 := Nat.div_div_self ha.1 (by omega : n ≠ 0)
      have e2 := Nat.div_div_self hb.1 (by omega : n ≠ 0)
      simp only at hab
      rw [hab] at e1
      rw [e1] at e2
      exact e2
    calc (↑(D.map (fun d => n / d)) : Multiset ℕ)
        = (↑D : Multiset ℕ).map (fun d => n / d) := (Multiset.map_coe _ _).symm
      _ = (Nat.divisors n).val.map (fun d => n / d) := by rw [hD, Finset.sort_eq]
      _ = ((Nat.divisors n).image (fun d => n / d)).val := (Finset.image_val_of_injOn hinj).symm
      _ = (Nat.divisors n).val := by rw [Nat.image_div_divisors_eq_divisors]
      _ = (↑D : Multiset ℕ) := by rw [hD, Finset.sort_eq]
  -- both pairwise (≥)
  have hr1 : List.Pairwise (fun a b : ℕ => b ≤ a) (D.map (fun d => n / d)) := by
    rw [List.pairwise_map]
    rw [List.Pairwise.imp_mem] at hsort ⊢
    refine hsort.imp ?_
    intro a b h ha hb
    have : a ≤ b := h ha hb
    exact Nat.div_le_div_left this (hpos a ha)
  have hr2 : List.Pairwise (fun a b : ℕ => b ≤ a) D.reverse := by
    rw [List.pairwise_reverse]
    exact hsort
  exact List.Perm.eq_of_pairwise' hr1 hr2 hperm

theorem refl_sum (n : ℕ) (hn : 1 ≤ n) :
    ((((Nat.divisors n).sort (· ≤ ·)).zip (((Nat.divisors n).sort (· ≤ ·)).tail)).map
        (fun p => p.1 * p.2)).sum
    = ((((Nat.divisors n).sort (· ≤ ·)).zip (((Nat.divisors n).sort (· ≤ ·)).tail)).map
        (fun p => (n / p.1) * (n / p.2))).sum := by
  set D := (Nat.divisors n).sort (· ≤ ·) with hD
  have key : (D.zip D.tail).map (fun p => (n / p.1) * (n / p.2))
      = ((D.zip D.tail).map (fun q => q.2 * q.1)).reverse := by
    have e1 : (D.zip D.tail).map (fun p => (n / p.1) * (n / p.2))
        = ((D.map (fun d => n/d)).zip (D.tail.map (fun d => n/d))).map (fun q => q.1 * q.2) := by
      rw [List.zip_map, List.map_map]; rfl
    rw [e1, divisor_reflection n hn, map_tail, divisor_reflection n hn, zip_tail_reverse,
      map_reverse, List.map_map]
    rfl
  rw [key, List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro p _
  exact Nat.mul_comm _ _


theorem map_fst_zip_tail {α : Type*} (l : List α) :
    map Prod.fst (l.zip l.tail) = l.dropLast := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u =>
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.dropLast_cons₂]
      rw [← ih]; rfl

theorem amgm_bound (p : ℚ) (u : List ℚ) (hp : 0 < p) (hu : ∀ x ∈ u, 0 < x) :
    (((1 :: p :: u).zip (1 :: p :: u).tail).map (fun q => 1/(q.1 * q.2))).sum
      ≤ 1/p - 1/(2*p^2) + (((1 :: p :: u).map (fun x => 1/x^2)).sum - 1) := by
  set t : List ℚ := p :: u with ht
  have hpos_t : ∀ x ∈ t, 0 < x := by
    intro x hx; rw [ht, List.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; exact hp
    · exact hu x h
  have hzip : ((1 :: p :: u).zip (1 :: p :: u).tail) = (1, p) :: (t.zip t.tail) := by
    rw [ht]; rfl
  rw [hzip, List.map_cons, List.sum_cons]
  have hfirst : (1 : ℚ)/((1:ℚ) * p) = 1/p := by ring
  rw [hfirst]
  set P' := t.zip t.tail with hP'
  -- termwise AM-GM
  have hAM : (P'.map (fun q => 1/(q.1 * q.2))).sum
      ≤ (P'.map (fun q => 1/2*(1/q.1^2) + 1/2*(1/q.2^2))).sum := by
    apply List.sum_le_sum
    intro q hq
    obtain ⟨q1, q2⟩ := q
    have hm := List.of_mem_zip hq
    have hq1 : 0 < q1 := hpos_t q1 hm.1
    have hq2 : 0 < q2 := hpos_t q2 (List.mem_of_mem_tail hm.2)
    simp only
    have key : 1/2*(1/q1^2) + 1/2*(1/q2^2) - 1/(q1*q2) = (q1-q2)^2/(2*q1^2*q2^2) := by
      field_simp; ring
    have hnn : (0:ℚ) ≤ (q1-q2)^2/(2*q1^2*q2^2) := by positivity
    linarith [key]
  rw [List.sum_map_add] at hAM
  -- A2, B2
  have hB2 : (P'.map (fun q => 1/2*(1/q.2^2))).sum = 1/2 * (u.map (fun x => 1/x^2)).sum := by
    rw [List.sum_map_mul_left]
    congr 1
    rw [show (fun q : ℚ × ℚ => 1/q.2^2) = (fun x => 1/x^2) ∘ Prod.snd from rfl, ← List.map_map,
      hP', List.map_snd_zip (by rw [ht]; simp [List.length_tail])]
    simp only [ht, List.tail_cons]
  have hA2 : (P'.map (fun q => 1/2*(1/q.1^2))).sum ≤ 1/2 * (t.map (fun x => 1/x^2)).sum := by
    rw [List.sum_map_mul_left]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [show (fun q : ℚ × ℚ => 1/q.1^2) = (fun x => 1/x^2) ∘ Prod.fst from rfl, ← List.map_map,
      hP', map_fst_zip_tail]
    apply List.Sublist.sum_le_sum
    · exact (List.dropLast_sublist t).map _
    · intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; positivity
  -- St, SD relations
  have hSt : (t.map (fun x => 1/x^2)).sum = 1/p^2 + (u.map (fun x => 1/x^2)).sum := by
    rw [ht, List.map_cons, List.sum_cons]
  have hSD : ((1 :: p :: u).map (fun x => 1/x^2)).sum
      = 1 + (1/p^2 + (u.map (fun x => 1/x^2)).sum) := by
    simp only [List.map_cons, List.sum_cons]; ring
  rw [hSD]
  have hp2 : 1/(2*p^2) = 1/2 * (1/p^2) := by ring
  linarith [hAM, hB2, hA2, hSt, hp2]


noncomputable def gg (p : ℕ) : ℚ := (p:ℚ)^2/((p:ℚ)^2-1)

theorem gmono (k x : ℕ) (hk : 4 ≤ k) (hx : k ≤ x) : gg x ≤ gg k := by
  unfold gg
  have hck : (4:ℚ) ≤ (k:ℚ) := by exact_mod_cast hk
  have hcx : (4:ℚ) ≤ (x:ℚ) := by exact_mod_cast (le_trans hk hx)
  have hcxk : (k:ℚ) ≤ (x:ℚ) := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

theorem gpos (x : ℕ) (hx : 17 ≤ x) : 0 < gg x := by
  unfold gg
  have : (17:ℚ) ≤ (x:ℚ) := by exact_mod_cast hx
  apply _root_.div_pos <;> nlinarith

theorem list_g_bound (q : List ℕ) (hsort : q.Sorted (· < ·))
    (hmem : ∀ x ∈ q, x.Prime ∧ 17 ≤ x) (hlen : q.length ≤ 4) :
    (q.map gg).prod ≤ (289*361*529*841 : ℚ)/(288*360*528*840) := by
  have hB17 : gg 17 = 289/288 := by unfold gg; norm_num
  have hB19 : gg 19 = 361/360 := by unfold gg; norm_num
  have hB23 : gg 23 = 529/528 := by unfold gg; norm_num
  have hB29 : gg 29 = 841/840 := by unfold gg; norm_num
  rcases q with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨ee, rest⟩⟩⟩⟩⟩
  · norm_num
  · -- [a]
    have ha := (hmem a (by simp)).2
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    calc gg a ≤ gg 17 := gmono 17 a (by norm_num) ha
      _ = 289/288 := hB17
      _ ≤ _ := by norm_num
  · -- [a,b]
    have ha := (hmem a (by simp)).2
    have hbp := (hmem b (by simp)).1
    simp only [List.sorted_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil] at hsort
    have hab : a < b := hsort.1 b (by simp)
    have hb19 : 19 ≤ b := by
      by_contra h; push_neg at h
      have : 18 ≤ b := by omega
      interval_cases b <;> revert hbp <;> decide
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have g1 : gg a ≤ 289/288 := (gmono 17 a (by norm_num) ha).trans (le_of_eq hB17)
    have g2 : gg b ≤ 361/360 := (gmono 19 b (by norm_num) hb19).trans (le_of_eq hB19)
    have p2 : (0:ℚ) ≤ gg b := le_of_lt (gpos b (by omega))
    calc gg a * gg b ≤ (289/288) * (361/360) := by
            apply mul_le_mul g1 g2 p2 (by norm_num)
      _ ≤ _ := by norm_num
  · -- [a,b,c]
    have ha := (hmem a (by simp)).2
    have hbp := (hmem b (by simp)).1
    have hcp := (hmem c (by simp)).1
    simp only [List.sorted_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil] at hsort
    have hab : a < b := hsort.1 b (by simp)
    have hbc : b < c := hsort.2.1 c (by simp)
    have hb19 : 19 ≤ b := by
      by_contra h; push_neg at h; have : 18 ≤ b := by omega
      interval_cases b <;> revert hbp <;> decide
    have hc23 : 23 ≤ c := by
      by_contra h; push_neg at h; have : 20 ≤ c := by omega
      interval_cases c <;> revert hcp <;> decide
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have g1 : gg a ≤ 289/288 := (gmono 17 a (by norm_num) ha).trans (le_of_eq hB17)
    have g2 : gg b ≤ 361/360 := (gmono 19 b (by norm_num) hb19).trans (le_of_eq hB19)
    have g3 : gg c ≤ 529/528 := (gmono 23 c (by norm_num) hc23).trans (le_of_eq hB23)
    have p2 : (0:ℚ) ≤ gg b := le_of_lt (gpos b (by omega))
    have p3 : (0:ℚ) ≤ gg c := le_of_lt (gpos c (by omega))
    calc gg a * (gg b * gg c) ≤ (289/288) * ((361/360)*(529/528)) := by
            apply mul_le_mul g1 (mul_le_mul g2 g3 p3 (by norm_num)) (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  · -- [a,b,c,d]
    have ha := (hmem a (by simp)).2
    have hbp := (hmem b (by simp)).1
    have hcp := (hmem c (by simp)).1
    have hdp := (hmem d (by simp)).1
    simp only [List.sorted_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil] at hsort
    have hab : a < b := hsort.1 b (by simp)
    have hbc : b < c := hsort.2.1 c (by simp)
    have hcd : c < d := hsort.2.2.1 d (by simp)
    have hb19 : 19 ≤ b := by
      by_contra h; push_neg at h; have : 18 ≤ b := by omega
      interval_cases b <;> revert hbp <;> decide
    have hc23 : 23 ≤ c := by
      by_contra h; push_neg at h; have : 20 ≤ c := by omega
      interval_cases c <;> revert hcp <;> decide
    have hd29 : 29 ≤ d := by
      by_contra h; push_neg at h; have : 24 ≤ d := by omega
      interval_cases d <;> revert hdp <;> decide
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have g1 : gg a ≤ 289/288 := (gmono 17 a (by norm_num) ha).trans (le_of_eq hB17)
    have g2 : gg b ≤ 361/360 := (gmono 19 b (by norm_num) hb19).trans (le_of_eq hB19)
    have g3 : gg c ≤ 529/528 := (gmono 23 c (by norm_num) hc23).trans (le_of_eq hB23)
    have g4 : gg d ≤ 841/840 := (gmono 29 d (by norm_num) hd29).trans (le_of_eq hB29)
    have p2 : (0:ℚ) ≤ gg b := le_of_lt (gpos b (by omega))
    have p3 : (0:ℚ) ≤ gg c := le_of_lt (gpos c (by omega))
    have p4 : (0:ℚ) ≤ gg d := le_of_lt (gpos d (by omega))
    calc gg a * (gg b * (gg c * gg d))
          ≤ (289/288) * ((361/360)*((529/528)*(841/840))) := by
            apply mul_le_mul g1 (mul_le_mul g2 (mul_le_mul g3 g4 p4 (by norm_num)) (by positivity) (by norm_num)) (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  · -- length 5, contradiction
    simp only [List.length_cons] at hlen; omega


theorem prod_g_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 17 ≤ p) (hcard : P.card ≤ 4) :
    ∏ p ∈ P, gg p ≤ (289*361*529*841 : ℚ)/(288*360*528*840) := by
  have hconv : ((P.sort (·≤·)).map gg).prod = ∏ p ∈ P, gg p := by
    rw [Finset.prod]; rw [← Multiset.prod_coe, ← Multiset.map_coe]; congr 1
    rw [← Finset.sort_eq P (·≤·)]
  rw [← hconv]
  apply list_g_bound
  · have h1 : List.Sorted (·≤·) (P.sort (·≤·)) := Finset.sort_sorted P _
    have h2 : (P.sort (·≤·)).Pairwise (· ≠ ·) := P.sort_nodup _
    exact (h1.and h2).imp (fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne)
  · intro x hx; rw [Finset.mem_sort] at hx; exact hP x hx
  · rw [Finset.length_sort]; exact hcard

theorem factor_bound (p e : ℕ) (hp : p.Prime) :
    ((sigma 2) (p^e) : ℚ)/(p:ℚ)^(2*e) ≤ gg p := by
  unfold gg
  have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp.two_le
  have hpgt0 : (0:ℚ) < (p:ℚ) := by linarith
  have hppos : (0:ℚ) < (p:ℚ)^(2*e) := pow_pos hpgt0 _
  have hval : ((sigma 2) (p^e) : ℚ) = ∑ j ∈ Finset.range (e+1), ((p:ℚ)^2)^j := by
    rw [sigma_apply_prime_pow hp]; push_cast
    apply Finset.sum_congr rfl; intro j _; rw [← pow_mul]; ring_nf
  rw [hval, geom_sum_eq (by nlinarith : ((p:ℚ)^2) ≠ 1), div_div,
    div_le_div_iff₀ (mul_pos (by nlinarith) hppos) (by nlinarith)]
  have hpe : (p:ℚ)^(2*e) = ((p:ℚ)^2)^e := by rw [← pow_mul]
  rw [hpe]
  have heq : ((p:ℚ)^2)^(e+1) = (p:ℚ)^2 * ((p:ℚ)^2)^e := by ring
  rw [heq]
  nlinarith [pow_pos (by nlinarith : (0:ℚ) < (p:ℚ)^2) e]


theorem sigma2_bound (n : ℕ) (hn : 1 ≤ n)
    (hP : ∀ p ∈ n.primeFactors, 17 ≤ p) (hcard : n.primeFactors.card ≤ 4) :
    (∑ d ∈ n.divisors, (1:ℚ)/d^2) ≤ (289*361*529*841 : ℚ)/(288*360*528*840) := by
  have hne : n ≠ 0 := by omega
  -- reindex
  have hreindex : (∑ d ∈ n.divisors, (1:ℚ)/d^2) = ((sigma 2) n : ℚ)/(n:ℚ)^2 := by
    rw [show ((sigma 2) n : ℚ) = (∑ d ∈ n.divisors, (d:ℚ)^2) by rw [sigma_apply]; push_cast; rfl]
    rw [Finset.sum_div, ← Nat.sum_div_divisors n (fun d => (d:ℚ)^2/n^2)]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    rw [Nat.cast_div hdvd (by exact_mod_cast hd0.ne')]
    field_simp
  -- sigma factorization
  have hsig : ((sigma 2) n : ℚ) = ∏ p ∈ n.primeFactors, ((sigma 2) (p ^ (n.factorization p)) : ℚ) := by
    rw [IsMultiplicative.multiplicative_factorization _ isMultiplicative_sigma hne, Finsupp.prod,
      Nat.support_factorization]
    push_cast; rfl
  have hn2 : (n:ℚ)^2 = ∏ p ∈ n.primeFactors, (p:ℚ)^(2 * n.factorization p) := by
    have hnp : (n:ℚ) = ∏ p ∈ n.primeFactors, (p:ℚ)^(n.factorization p) := by
      conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hne]
      rw [Finsupp.prod, Nat.support_factorization]; push_cast; rfl
    rw [hnp, ← Finset.prod_pow]
    apply Finset.prod_congr rfl; intro p _; rw [← pow_mul]; congr 1; ring
  rw [hreindex, hsig, hn2, ← Finset.prod_div_distrib]
  calc (∏ p ∈ n.primeFactors, ((sigma 2) (p ^ n.factorization p) : ℚ) / (p:ℚ)^(2 * n.factorization p))
      ≤ ∏ p ∈ n.primeFactors, gg p := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpp := (Nat.prime_of_mem_primeFactors hp).two_le
          have hpq : (0:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 0 < p)
          positivity
        · intro p hp
          exact factor_bound p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)
    _ ≤ _ := prod_g_bound n.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hP p hp⟩) hcard


theorem divisors_cons (b : ℕ) (hb : 2 ≤ b) :
    ∃ u, (b.divisors.sort (·≤·)) = 1 :: b.minFac :: u := by
  have hbne : b ≠ 0 := by omega
  have hb1 : b ≠ 1 := by omega
  have hlen : 2 ≤ (b.divisors.sort (·≤·)).length := by
    rw [Finset.length_sort]
    have hsub : ({1, b} : Finset ℕ) ⊆ b.divisors := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]; exact Nat.one_mem_divisors.mpr hbne
      · rw [h]; exact Nat.mem_divisors.mpr ⟨dvd_refl b, hbne⟩
    have : ({1, b} : Finset ℕ).card = 2 := Finset.card_pair (show (1:ℕ) ≠ b by omega)
    calc 2 = ({1, b} : Finset ℕ).card := this.symm
      _ ≤ _ := Finset.card_le_card hsub
  obtain ⟨a0, a1, rest, hrest⟩ : ∃ a0 a1 rest, (b.divisors.sort (·≤·)) = a0 :: a1 :: rest := by
    match h : (b.divisors.sort (·≤·)), hlen with
    | a0 :: a1 :: rest, _ => exact ⟨a0, a1, rest, rfl⟩
  have hsort : (a0 :: a1 :: rest).Sorted (·≤·) := hrest ▸ Finset.sort_sorted _ _
  have hnodup : (a0 :: a1 :: rest).Nodup := hrest ▸ b.divisors.sort_nodup _
  have hmem : ∀ x, x ∈ (a0 :: a1 :: rest) ↔ x ∈ b.divisors := by
    intro x; rw [← hrest, Finset.mem_sort]
  rw [List.sorted_cons] at hsort
  have hsort2 := hsort.2
  rw [List.sorted_cons] at hsort2
  -- a0 = 1
  have ha0div : a0 ∈ b.divisors := (hmem a0).mp (by simp)
  have ha0le : ∀ x ∈ (a0 :: a1 :: rest), a0 ≤ x := by
    intro x hx; rcases List.mem_cons.mp hx with h | h
    · omega
    · exact hsort.1 x h
  have ha0 : a0 = 1 := by
    have h1 : a0 ≤ 1 := ha0le 1 ((hmem 1).mpr (Nat.one_mem_divisors.mpr hbne))
    have h2 : 1 ≤ a0 := Nat.pos_of_mem_divisors ha0div
    omega
  -- a1 = minFac
  have ha1div : a1 ∈ b.divisors := (hmem a1).mp (by simp)
  have ha1gt1 : 1 < a1 := by
    have hle : a0 ≤ a1 := hsort.1 a1 (by simp)
    have hne : a0 ≠ a1 := by
      have := hnodup; rw [List.nodup_cons] at this; intro hc; exact this.1 (hc ▸ by simp)
    omega
  have ha1dvd : a1 ∣ b := (Nat.mem_divisors.mp ha1div).1
  have hge : b.minFac ≤ a1 := Nat.minFac_le_of_dvd ha1gt1 ha1dvd
  have hmfmem : b.minFac ∈ (a0 :: a1 :: rest) := (hmem b.minFac).mpr (Nat.mem_divisors.mpr ⟨Nat.minFac_dvd b, hbne⟩)
  have hle : a1 ≤ b.minFac := by
    rcases List.mem_cons.mp hmfmem with h | h
    · rw [ha0] at h; have := (Nat.minFac_prime hb1).two_le; omega
    · rcases List.mem_cons.mp h with h2 | h2
      · omega
      · exact hsort2.1 b.minFac h2
  have ha1 : a1 = b.minFac := le_antisymm hle hge
  exact ⟨rest, by rw [hrest, ha0, ha1]⟩

-- ==== F2 lemmas ====
theorem list_prod_lb (q : List ℕ) (hsort : q.Sorted (· < ·))
    (hmem : ∀ x ∈ q, x.Prime ∧ 17 ≤ x) (hlen : 5 ≤ q.length) :
    6678671 ≤ q.prod := by
  match q, hsort, hmem, hlen with
  | a :: b :: c :: d :: e :: rest, hsort, hmem, _ =>
    have ha := (hmem a (by simp)).2
    have hbp := (hmem b (by simp)).1
    have hcp := (hmem c (by simp)).1
    have hdp := (hmem d (by simp)).1
    have hep := (hmem e (by simp)).1
    simp only [List.sorted_cons, List.mem_cons] at hsort
    have hab : a < b := hsort.1 b (by simp)
    have hbc : b < c := hsort.2.1 c (by simp)
    have hcd : c < d := hsort.2.2.1 d (by simp)
    have hde : d < e := hsort.2.2.2.1 e (by simp)
    have hb19 : 19 ≤ b := by
      by_contra h; push_neg at h; have : 18 ≤ b := by omega
      interval_cases b <;> revert hbp <;> decide
    have hc23 : 23 ≤ c := by
      by_contra h; push_neg at h; have : 20 ≤ c := by omega
      interval_cases c <;> revert hcp <;> decide
    have hd29 : 29 ≤ d := by
      by_contra h; push_neg at h; have : 24 ≤ d := by omega
      interval_cases d <;> revert hdp <;> decide
    have he31 : 31 ≤ e := by
      by_contra h; push_neg at h; have : 30 ≤ e := by omega
      interval_cases e <;> revert hep <;> decide
    have hrest : 1 ≤ rest.prod := by
      apply List.one_le_prod
      intro x hx
      exact ((hmem x (by simp [hx])).1).one_lt.le
    simp only [List.prod_cons]
    calc 6678671 = 17 * (19 * (23 * (29 * (31 * 1)))) := by norm_num
      _ ≤ a * (b * (c * (d * (e * rest.prod)))) := by
          apply Nat.mul_le_mul ha
          apply Nat.mul_le_mul hb19
          apply Nat.mul_le_mul hc23
          apply Nat.mul_le_mul hd29
          apply Nat.mul_le_mul he31 hrest

theorem card_le_four (b : ℕ) (hb : 1 ≤ b) (hP : ∀ p ∈ b.primeFactors, 17 ≤ p)
    (hlt : b < 6678671) : b.primeFactors.card ≤ 4 := by
  by_contra hc
  push_neg at hc
  have hrad : (∏ p ∈ b.primeFactors, p) ∣ b := Nat.prod_primeFactors_dvd b
  have hradle : (∏ p ∈ b.primeFactors, p) ≤ b := Nat.le_of_dvd (by omega) hrad
  have hconv : (b.primeFactors.sort (·≤·)).prod = ∏ p ∈ b.primeFactors, p := by
    rw [Finset.prod_eq_multiset_prod, ← Finset.sort_eq b.primeFactors (·≤·), Multiset.map_id', Multiset.prod_coe]
  have hsort : List.Sorted (· < ·) (b.primeFactors.sort (·≤·)) := by
    have h1 : List.Sorted (·≤·) (b.primeFactors.sort (·≤·)) := Finset.sort_sorted _ _
    have h2 : (b.primeFactors.sort (·≤·)).Pairwise (· ≠ ·) := b.primeFactors.sort_nodup _
    exact (h1.and h2).imp (fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne)
  have hmem : ∀ x ∈ (b.primeFactors.sort (·≤·)), x.Prime ∧ 17 ≤ x := by
    intro x hx; rw [Finset.mem_sort] at hx
    exact ⟨Nat.prime_of_mem_primeFactors hx, hP x hx⟩
  have hlen : 5 ≤ (b.primeFactors.sort (·≤·)).length := by
    rw [Finset.length_sort]; omega
  have := list_prod_lb _ hsort hmem hlen
  rw [hconv] at this
  omega

-- ==== helpers ====
theorem sum_sort_map (s : Finset ℕ) (f : ℕ → ℚ) :
    ((s.sort (·≤·)).map f).sum = ∑ x ∈ s, f x := by
  rw [Finset.sum]; rw [← Multiset.sum_coe, ← Multiset.map_coe]; congr 1
  rw [← Finset.sort_eq s (·≤·)]

theorem fmono (x : ℚ) (hx : 17 ≤ x) : 1/x - 1/(2*x^2) ≤ 1/17 - 1/(2*17^2) := by
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_sub_div _ _ (by norm_num) (by norm_num),
    div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg x, sq_nonneg (x-17)]

theorem lb14_core (b : ℕ) (hb : 2 ≤ b) (ha : a b = 14) (hlt : b < 6678671) : False := by
  have hb1 : (1:ℕ) ≤ b := by omega
  have hbne : b ≠ 0 := by omega
  have hbne1 : b ≠ 1 := by omega
  obtain ⟨u, hDeq⟩ := divisors_cons b hb
  set D := b.divisors.sort (·≤·) with hDdef
  set p := b.minFac with hpdef
  set s := ((D.zip D.tail).map (fun pp : ℕ × ℕ => pp.fst * pp.snd)).sum with hsdef
  have hzipD : D.zip D.tail = (1, p) :: ((p :: u).zip u) := by rw [hDeq]; rfl
  have hp_prime : p.Prime := Nat.minFac_prime hbne1
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hs_pos : 0 < s := by
    rw [hsdef, hzipD]; simp only [List.map_cons, List.sum_cons]
    have : 0 < 1 * p := by omega
    omega
  have haval : a b = b ^ 2 / s := by
    unfold a; simp only [← hsdef]; rw [if_neg (by omega : ¬ s = 0)]
  have h14 : b ^ 2 / s = 14 := by rw [← haval]; exact ha
  have hlt2 : b ^ 2 < 15 * s := by
    rw [← Nat.div_lt_iff_lt_mul hs_pos, h14]; norm_num
  -- membership helper
  have hmemD : ∀ x ∈ D, x ∣ b ∧ 0 < x := by
    intro x hx
    have : x ∈ b.divisors := (Finset.mem_sort _).mp (hDdef ▸ hx)
    exact ⟨Nat.dvd_of_mem_divisors this, Nat.pos_of_mem_divisors this⟩
  -- F1
  have hpdvd : p ∣ b := Nat.minFac_dvd b
  have hbp_eq : (b / p) * p = b := Nat.div_mul_cancel hpdvd
  have hrefl : s = ((D.zip D.tail).map (fun q => (b / q.1) * (b / q.2))).sum := by
    rw [hsdef]; exact refl_sum b hb1
  have hs_ge : b * (b / p) ≤ s := by
    rw [hrefl, hzipD]; simp only [List.map_cons, List.sum_cons, Nat.div_one]; omega
  have hb2le : b ^ 2 ≤ s * p := by
    have : b ^ 2 = (b * (b / p)) * p := by rw [mul_assoc, hbp_eq]; ring
    rw [this]; exact Nat.mul_le_mul_right p hs_ge
  have hdvle : b ^ 2 / s ≤ p := by
    have h1 := Nat.div_le_div_right (c := s) hb2le
    rwa [Nat.mul_div_cancel_left p hs_pos] at h1
  have hp14 : 14 ≤ p := by omega
  have hp17 : 17 ≤ p := by
    by_cases h : p < 17
    · interval_cases p <;> revert hp_prime <;> decide
    · omega
  have hPF : ∀ q ∈ b.primeFactors, 17 ≤ q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have := Nat.minFac_le_of_dvd hqp.two_le hqd
    omega
  have hcard := card_le_four b hb1 hPF hlt
  -- main inequality, in ℚ
  set M := ((D.zip D.tail).map (fun q => 1 / ((q.1:ℚ) * (q.2:ℚ)))).sum with hMdef
  -- (s:ℚ) = b² * M
  have hsQ : (s:ℚ) = (b:ℚ) ^ 2 * M := by
    rw [hrefl, hMdef, ← List.sum_map_mul_left, Nat.cast_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    obtain ⟨x, y⟩ := q
    have hx := hmemD x (List.of_mem_zip hq).1
    have hy := hmemD y (List.mem_of_mem_tail (List.of_mem_zip hq).2)
    simp only [Function.comp]
    rw [Nat.cast_mul, Nat.cast_div hx.1 (by exact_mod_cast hx.2.ne'),
      Nat.cast_div hy.1 (by exact_mod_cast hy.2.ne')]
    have hxq : (x:ℚ) ≠ 0 := by exact_mod_cast hx.2.ne'
    have hyq : (y:ℚ) ≠ 0 := by exact_mod_cast hy.2.ne'
    field_simp
  -- Dq = D.map cast
  have hDq : (1:ℚ) :: (p:ℚ) :: (u.map (Nat.cast : ℕ → ℚ)) = D.map (Nat.cast : ℕ → ℚ) := by
    rw [hDeq]; simp only [List.map_cons, Nat.cast_one]
  -- amgm
  have hpQ : (0:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 0 < p)
  have hu_pos : ∀ x ∈ u.map (Nat.cast : ℕ → ℚ), 0 < x := by
    intro x hx; rw [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    have hyD : y ∈ D := by rw [hDeq]; simp [hy]
    have := (hmemD y hyD).2
    exact_mod_cast this
  have hamgm := amgm_bound (p:ℚ) (u.map (Nat.cast : ℕ → ℚ)) hpQ hu_pos
  -- amgm LHS = M
  have hLHS : ((((1:ℚ) :: (p:ℚ) :: (u.map (Nat.cast:ℕ→ℚ))).zip
        ((1:ℚ) :: (p:ℚ) :: (u.map (Nat.cast:ℕ→ℚ))).tail).map (fun q => 1 / (q.1 * q.2))).sum = M := by
    rw [hMdef, hDq, ← List.map_tail, List.zip_map, List.map_map]
    rfl
  -- S part = sigma2 sum
  have hSeq : (((1:ℚ) :: (p:ℚ) :: (u.map (Nat.cast:ℕ→ℚ))).map (fun x => 1 / x ^ 2)).sum
        = ∑ d ∈ b.divisors, (1:ℚ) / d ^ 2 := by
    rw [hDq, List.map_map, ← sum_sort_map b.divisors (fun d => 1 / (d:ℚ) ^ 2)]
    rfl
  have hSle := sigma2_bound b hb1 hPF hcard
  -- M ≤ 1/15
  have hT : M ≤ 1 / 15 := by
    rw [← hLHS]
    refine le_trans hamgm ?_
    rw [hSeq]
    have hf := fmono (p:ℚ) (by exact_mod_cast hp17)
    have : ∑ d ∈ b.divisors, (1:ℚ) / d ^ 2 ≤ (289*361*529*841 : ℚ)/(288*360*528*840) := hSle
    nlinarith [hf, this]
  -- conclude 15*s ≤ b²
  have hfin : 15 * (s:ℚ) ≤ (b:ℚ) ^ 2 := by
    rw [hsQ]
    have hbsq : (0:ℚ) ≤ (b:ℚ) ^ 2 := by positivity
    nlinarith [hT, hbsq]
  have hfinN : 15 * s ≤ b ^ 2 := by exact_mod_cast hfin
  omega

theorem lb14 : ∀ b ∈ first_occurrence_set 14, 6678671 ≤ b := by
  intro b hb
  obtain ⟨hb2, hba⟩ := hb
  by_contra hlt
  push_neg at hlt
  exact lb14_core b hb2 hba hlt
theorem il14 : IsLeast (first_occurrence_set 14) 6678671 := ⟨il14_mem, lb14⟩

/--
A251758 Conjecture: Terms $x$, where $a(x)=n$, $x=p_{\#k}/p_{\#j}$, $p_{\#i}$ is the $i$-th primorial, $k>j$ is suitable large $k$ and $j$ is the number of primes less than $n$.
First occurrence of $n \ge 1$: 4, 2, 3, 25, 5, 49, 7, ??? $\le 35336848261$, 2431, 121, 11, 169, 13, 6678671, 7429, 289, 17, 361, 19, 31367009, 20677, 529, 23, ... .
Formalizing the claim that the listed numbers are the smallest $n$ such that $a(n)=k$.
-/
theorem a251758_conjecture_first_occurrences :
  (IsLeast (first_occurrence_set 1) 4) ∧
  (IsLeast (first_occurrence_set 2) 2) ∧
  (IsLeast (first_occurrence_set 3) 3) ∧
  (IsLeast (first_occurrence_set 4) 25) ∧
  (IsLeast (first_occurrence_set 5) 5) ∧
  (IsLeast (first_occurrence_set 6) 49) ∧
  (IsLeast (first_occurrence_set 7) 7) ∧
  (IsLeast (first_occurrence_set 9) 2431) ∧
  (IsLeast (first_occurrence_set 10) 121) ∧
  (IsLeast (first_occurrence_set 11) 11) ∧
  (IsLeast (first_occurrence_set 12) 169) ∧
  (IsLeast (first_occurrence_set 13) 13) ∧
  (IsLeast (first_occurrence_set 14) 6678671) ∧
  (IsLeast (first_occurrence_set 15) 7429) ∧
  (IsLeast (first_occurrence_set 16) 289) ∧
  (IsLeast (first_occurrence_set 17) 17)
  := ⟨il1, il2, il3, il4, il5, il6, il7, il9, il10, il11, il12, il13, il14, il15, il16, il17⟩
