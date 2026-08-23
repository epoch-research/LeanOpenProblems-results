import FormalConjectures.Util.ProblemImports
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial Nat Finset

/--
A185895: Exponential generating function is $\prod_{k>0} (1 - x^k/k!).$
The $n$-th term is
$$ a(n) = n! \cdot \left[x^n\right] \left( \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right) \right) $$
The coefficients $a(n)$ are integers.
-/
noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  -- n! is defined for n=0, and Px_0 is 1, so a(0) = 1.
  -- We handle n=0 explicitly to avoid issues with 0.factorial.cast in the general case if k=0 were included.

  -- The finite product $\prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right)$ is equivalent to the infinite product for the coefficient of $x^n$.
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    -- Factor is $1 - x^k/k!$.
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)

  -- $[x^n] Px$ is the coefficient of $x^n$.
  let coeff_n : ℚ := Polynomial.coeff Px n

  -- $a(n) = n! \cdot [x^n] Px$.
  let a_n_q : ℚ := coeff_n * n.factorial.cast

  -- The result is an integer, so Rat.floor converts the rational value to ℤ.
  a_n_q.floor

/-- A natural number $n$ is a triangular number if it is of the form $k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

def ib : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ib k n - if k+1 ≤ n then (n.choose (k+1) : ℤ) * ib k (n-(k+1)) else 0

noncomputable def PP : ℕ → Polynomial ℚ
  | 0 => 1
  | k + 1 => PP k * (1 - C (1 / ((k+1).factorial : ℚ)) * X^(k+1))

lemma coeff_step (p : Polynomial ℚ) (k n : ℕ) :
    (p * (1 - C (1 / (k.factorial : ℚ)) * X^k)).coeff n =
      p.coeff n - if k ≤ n then p.coeff (n-k) / k.factorial else 0 := by
  rw [mul_sub, mul_one, coeff_sub]
  rw [← mul_assoc, coeff_mul_X_pow']
  simp only [coeff_mul_C]
  split <;> simp_all [div_eq_mul_inv]

lemma ib_cast_coeff : ∀ k n : ℕ, (ib k n : ℚ) = (PP k).coeff n * n.factorial := by
  intro k
  induction k with
  | zero =>
      intro n
      by_cases hn : n = 0
      · subst n; simp [ib, PP]
      · simp [ib, PP, hn, coeff_one]
  | succ k ih =>
      intro n
      rw [ib, PP, coeff_step]
      split_ifs with h
      · rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ih, ih]
        rw [sub_mul]
        congr 1
        rw [Nat.cast_choose ℚ h]
        field_simp
      · rw [Int.cast_sub, Int.cast_zero, sub_zero, ih]
        simp [h]

lemma PP_eq_prod (n : ℕ) : PP n = (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k) := by
  induction n with
  | zero => simp [PP]
  | succ n ih => rw [PP, ih, Finset.prod_Icc_succ_top (by omega)]

lemma A_eq_ib (n : ℕ) : A185895 n = ib n n := by
  by_cases hn : n = 0
  · subst n; simp [A185895, ib]
  · simp only [A185895, hn, ↓reduceIte]
    rw [← PP_eq_prod, ← ib_cast_coeff]
    exact Rat.floor_intCast _

lemma ib_succ_of_lt (k n : ℕ) (h : n < k+1) : ib (k+1) n = ib k n := by
  simp [ib, show ¬ k+1 ≤ n by omega]

lemma ib_stable (n k : ℕ) (h : n ≤ k) : ib k n = ib n n := by
  induction k with
  | zero => simp_all
  | succ k ih =>
      by_cases he : n = k+1
      · subst n; rfl
      · rw [ib_succ_of_lt k n (by omega)]
        exact ih (by omega)

def step (k : Nat) (a : List Int) : List Int :=
  (List.range a.length).map fun i => a[i]! - (if k ≤ i then (i.choose k : Int) * a[i-k]! else 0)

def comp (N : Nat) : List Int :=
  (List.range N).foldl (fun a k => step (k+1) a) (1::List.replicate N 0)

def triB (n : Nat) : Bool :=
  (List.range (n+1)).any fun k => n == k*(k+1)/2

def chk (N : Nat) : Bool :=
  let a := comp N
  (List.range N).all fun j => decide (a[j+1]! * a[j]! < 0) == triB (j+1)

lemma length_step (k : ℕ) (a : List ℤ) : (step k a).length = a.length := by
  simp [step]

lemma get_step (k : ℕ) (a : List ℤ) (i : ℕ) (hi : i < a.length) :
    (step k a)[i]! = a[i]! - if k ≤ i then (i.choose k : ℤ) * a[i-k]! else 0 := by
  simp [step, hi]

lemma length_fold (N : ℕ) (k : ℕ) (hk : k ≤ N) :
    ((List.range k).foldl (fun a i => step (i+1) a)
      (1 :: List.replicate N 0 : List ℤ)).length = N+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]
      rw [length_step, ih (by omega)]

lemma get_fold_ib (N k n : ℕ) (hk : k ≤ N) (hn : n ≤ N) :
    ((List.range k).foldl (fun a i => step (i+1) a)
      (1 :: List.replicate N 0 : List ℤ))[n]! = ib k n := by
  induction k generalizing n with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      cases n with
      | zero => simp [ib]
      | succ n => simp [ib, show n < N by omega]
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]
      rw [get_step _ _ _ (by rw [length_fold N k (by omega)]; omega), ib]
      rw [ih (n:=n) (by omega) hn]
      split_ifs with h
      · rw [ih (n:=n-(k+1)) (by omega) (by omega)]
      · rfl

lemma comp_get (N n : ℕ) (hn : n ≤ N) : (comp N)[n]! = ib N n := by
  exact get_fold_ib N N n le_rfl hn

lemma le_tri (k : ℕ) (hk : 0 < k) : k ≤ k*(k+1)/2 := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  nlinarith

lemma triB_iff (n : ℕ) (hn : 0 < n) : triB n ↔ ∃ k : ℕ, n = k*(k+1)/2 := by
  simp only [triB, List.any_eq_true, beq_iff_eq, List.mem_range]
  constructor
  · rintro ⟨k, hk, he⟩; exact ⟨k, he⟩
  · rintro ⟨k, rfl⟩
    have hk : 0 < k := by by_contra h; simp_all
    exact ⟨k, by have := le_tri k hk; omega, rfl⟩

lemma chk_sound (N n : ℕ) (hc : chk N = true) (hn0 : 0 < n) (hn : n ≤ N) :
    (ib n n * ib (n-1) (n-1) < 0 ↔ ∃ k : ℕ, n = k*(k+1)/2) := by
  have hm : n-1 < N := by omega
  have h := (List.all_eq_true.mp hc) (n-1) (by simpa using hm)
  have heq := beq_iff_eq.mp h
  simp only [show n - 1 + 1 = n by omega] at heq
  rw [comp_get N n hn, ib_stable n N hn] at heq
  rw [comp_get N (n-1) (by omega), ib_stable (n-1) N (by omega)] at heq
  rw [← triB_iff n hn0]
  have heq' : decide (ib n n * ib (n - 1) (n - 1) < 0) = decide (triB n = true) := by
    simpa only [Bool.decide_coe] using heq
  exact decide_eq_decide.mp heq'

def stepFast (k : Nat) (a : List Int) : List Int :=
  let sh := List.replicate k 0 ++ a
  (List.range a.length).zipWith
    (fun i xy => xy.1 - if k ≤ i then (i.choose k : Int) * xy.2 else 0)
    (a.zip sh)

def compFast (N : Nat) : List Int :=
  (List.range N).foldl (fun a k => stepFast (k+1) a) (1::List.replicate N 0)

def chkFast (N : Nat) : Bool :=
  let a := compFast N
  (List.range N).all fun j => decide (a[j+1]! * a[j]! < 0) == triB (j+1)

lemma length_stepFast (k : ℕ) (a : List ℤ) : (stepFast k a).length = a.length := by
  simp [stepFast]

lemma get_stepFast (k : ℕ) (a : List ℤ) (i : ℕ) (hi : i < a.length) :
    (stepFast k a)[i]! = a[i]! - if k ≤ i then (i.choose k : ℤ) * a[i-k]! else 0 := by
  simp [stepFast, hi]
  split <;> rename_i h
  · have hik : i-k < a.length := by omega
    rw [List.getElem_append]
    simp only [List.length_replicate]
    rw [dif_neg (by omega)]
    rw [List.getElem?_eq_getElem hik]
    simp
  · simp [h]
lemma stepFast_eq_step (k : ℕ) (a : List ℤ) : stepFast k a = step k a := by
  apply List.ext_getElem
  · rw [length_stepFast, length_step]
  · intro i h1 h2
    have hf := get_stepFast k a i (by simpa [length_stepFast] using h1)
    have hs := get_step k a i (by simpa [length_step] using h2)
    convert hf.trans hs.symm <;>
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, h1, h2]

lemma compFast_eq_comp (N : ℕ) : compFast N = comp N := by
  unfold compFast _root_.comp
  simp_rw [stepFast_eq_step]

lemma chkFast_eq_chk (N : ℕ) : chkFast N = chk N := by
  simp [chkFast, chk, compFast_eq_comp]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma check104 : chk 104 = true := by
  rw [← chkFast_eq_chk]
  rfl


noncomputable def wt (S : Finset ℕ) : ℚ := ∏ k ∈ S, (1 / (k.factorial : ℚ))

noncomputable def layer (l j n : ℕ) : ℚ :=
  ∑ S ∈ (Icc l n).powersetCard j, if ∑ k ∈ S, k = n then wt S else 0

lemma wt_nonneg (S : Finset ℕ) : 0 ≤ wt S := by
  unfold wt
  apply Finset.prod_nonneg
  intro i hi
  positivity

lemma layer_nonneg (l j n : ℕ) : 0 ≤ layer l j n := by
  unfold layer
  apply Finset.sum_nonneg
  intro S hS
  split_ifs
  · exact wt_nonneg S
  · norm_num

lemma prod_factor_expand (n : ℕ) :
    (Icc 1 n).prod (fun k : ℕ =>
      (1 : Polynomial ℚ) - C (1 / (k.factorial : ℚ)) * X ^ k) =
    ∑ S ∈ (Icc 1 n).powerset,
      C ((-1 : ℚ) ^ S.card * wt S) * X ^ (∑ k ∈ S, k) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [prod_const, one_pow, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  simp [wt]
  rw [Finset.prod_pow_eq_pow_sum]
  ring


lemma coeff_eq_layers (n : ℕ) :
    (PP n).coeff n = ∑ j ∈ range (n+1), (-1 : ℚ)^j * layer 1 j n := by
  rw [PP_eq_prod, prod_factor_expand]
  rw [finset_sum_coeff]
  rw [Finset.sum_powerset]
  simp only [card_Icc, Nat.add_sub_cancel, layer]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(mem_powersetCard.mp hS).2]
  rw [coeff_C_mul_X_pow]
  by_cases hsum : ∑ k ∈ S, k = n
  · rw [if_pos hsum, if_pos hsum.symm]
  · rw [if_neg hsum, if_neg (by exact fun h => hsum h.symm)]
    ring

/-- Weight of profiles with `j` distinct sizes, all at least `l`, and total `n`. -/
noncomputable def lay (l j n : ℕ) : ℚ :=
  if h : n < l then if j = 0 ∧ n = 0 then 1 else 0
  else
    lay (l+1) j n +
      if j = 0 then 0 else (1 / (l.factorial : ℚ)) * lay (l+1) (j-1) (n-l)
termination_by n + 1 - l
 decreasing_by all_goals omega

lemma lay_of_lt (l j n : ℕ) (h : n < l) :
    lay l j n = if j = 0 ∧ n = 0 then 1 else 0 := by
  rw [lay]; simp [h]

lemma lay_rec (l j n : ℕ) (h : l ≤ n) :
    lay l j n = lay (l+1) j n +
      if j = 0 then 0 else (1 / (l.factorial : ℚ)) * lay (l+1) (j-1) (n-l) := by
  rw [lay]; simp [h]

lemma lay_nonneg (l j n : ℕ) : 0 ≤ lay l j n := by
  generalize hM : n + 1 - l = M
  induction M using Nat.strong_induction_on generalizing l j n with
  | h M ih =>
    rw [lay]
    by_cases hn : n < l
    · rw [dif_pos hn]
      split_ifs <;> norm_num
    · rw [dif_neg hn]
      have hlt : n+1-(l+1) < M := by omega
      have hfirst := ih (n+1-(l+1)) hlt (l+1) j n rfl
      by_cases hj : j = 0
      · simpa [hj] using hfirst
      · rw [if_neg hj]
        exact add_nonneg hfirst (mul_nonneg (by positivity)
          (ih ((n-l)+1-(l+1)) (by omega) (l+1) (j-1) (n-l) rfl))

def tri (k : ℕ) : ℕ := k * (k+1) / 2

lemma tri_eq_sum_range (k : ℕ) : tri k = ∑ i ∈ range (k+1), i := by
  rw [Finset.sum_range_id]
  simp [tri]
  congr 1
  ring

lemma tri_succ (k : ℕ) : tri (k+1) = tri k + (k+1) := by
  rw [tri_eq_sum_range, tri_eq_sum_range, Finset.sum_range_succ]

attribute [irreducible] tri

lemma orderEmb_lower (S : Finset ℕ) (hpos : ∀ x ∈ S, 0 < x)
    (i : Fin S.card) : i.val + 1 ≤ S.orderEmbOfFin rfl i := by
  generalize hv : i.val = v
  induction v using Nat.strong_induction_on generalizing i with
  | h v ih =>
    by_cases hv0 : v = 0
    · have hp := hpos _ (S.orderEmbOfFin_mem rfl i)
      omega
    · let j : Fin S.card := ⟨v-1, by omega⟩
      have hj := ih (v-1) (by omega) j rfl
      have hs := (S.orderEmbOfFin rfl).strictMono (show j < i by change v-1 < i.val; omega)
      omega

lemma tri_card_le_sum (S : Finset ℕ) (hpos : ∀ x ∈ S, 0 < x) :
    tri S.card ≤ ∑ x ∈ S, x := by
  rw [← Finset.sum_attach]
  rw [show S.attach = Finset.univ by ext; simp]
  rw [← Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv
    (fun i : Fin S.card => S.orderEmbOfFin rfl i) (fun x : S => (x : ℕ)) (fun i => rfl)]
  calc
    tri S.card = ∑ i : Fin S.card, (i.val + 1) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i+1) S.card]
      rw [tri_eq_sum_range, Finset.sum_range_succ]
      simp [Finset.sum_add_distrib]
    _ ≤ _ := Finset.sum_le_sum fun i _ => orderEmb_lower S hpos i

lemma layer_eq_zero_of_tri_lt (l j n : ℕ) (hl : 0 < l) (h : n < tri j) :
    layer l j n = 0 := by
  unfold layer
  apply Finset.sum_eq_zero
  intro S hS
  have hc := (mem_powersetCard.mp hS).2
  split_ifs with hs
  · have hsub := (mem_powersetCard.mp hS).1
    have hp : ∀ x ∈ S, 0 < x := by
      intro x hx
      have := (mem_Icc.mp (hsub hx)).1
      omega
    have ht := tri_card_le_sum S hp
    rw [hc, hs] at ht
    omega
  · rfl

lemma sum_Icc_one (m : ℕ) : ∑ k ∈ Icc 1 m, k = tri m := by
  induction m with
  | zero => simp [tri]
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, tri_succ]

lemma layer_pos_of_tri_le (m n : ℕ) (hm : 0 < m) (hlo : tri m ≤ n) :
    0 < layer 1 m n := by
  let a := n - tri (m-1)
  let S : Finset ℕ := insert a (Icc 1 (m-1))
  have ha : m ≤ a := by
    dsimp [a]
    have hmEq : m-1+1=m := by omega
    have ht := tri_succ (m-1)
    rw [hmEq] at ht
    omega
  have hnot : a ∉ Icc 1 (m-1) := by simp only [mem_Icc]; omega
  have hcard : S.card = m := by
    have hmEq : m-1+1=m := by omega
    simp [S, hnot, hmEq]
  have hsum : ∑ k ∈ S, k = n := by
    rw [sum_insert hnot, sum_Icc_one]
    dsimp [a]
    have hmEq : m-1+1=m := by omega
    have ht := tri_succ (m-1)
    rw [hmEq] at ht
    have hle : tri (m-1) ≤ n := le_trans (by
      have hmEq : m=(m-1)+1 := by omega
      have : tri (m-1) ≤ tri m := by
        rw [ht]
        omega
      exact this) hlo
    omega
  have hsub : S ⊆ Icc 1 n := by
    intro x hx
    rw [mem_Icc]
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · constructor
      · omega
      · dsimp [a]; omega
    · have hxi := mem_Icc.mp hx
      constructor
      · exact hxi.1
      · have : m-1 ≤ n := by
          have hmt : m ≤ tri m := by
            rw [tri]
            exact le_tri m hm
          have := le_trans hmt hlo
          omega
        omega
  unfold layer
  apply Finset.sum_pos'
  · intro T hT
    split <;> simp_all [wt_nonneg]
  · refine ⟨S, mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩
    simp [hsum]
    exact (Finset.prod_pos fun k hk => by positivity : 0 < wt S)

noncomputable def altSum (f : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ range (m+1), (-1 : ℚ)^j * f j

lemma altSum_sign_nonneg (f : ℕ → ℚ) (m : ℕ)
    (hn : ∀ j, j ≤ m → 0 ≤ f j)
    (hinc : ∀ j, j < m → f j < f (j+1)) :
    0 ≤ (-1 : ℚ)^m * altSum f m := by
  induction m using Nat.twoStepInduction with
  | zero => simpa [altSum] using hn 0 (by omega)
  | one =>
      simp only [altSum, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, pow_zero, one_mul, pow_one]
      have hh := hinc 0 (by omega)
      nlinarith
  | more m ih0 ih1 =>
      have hnm : ∀ j, j ≤ m → 0 ≤ f j := fun j hj => hn j (by omega)
      have him : ∀ j, j < m → f j < f (j+1) := fun j hj => hinc j (by omega)
      have ih := ih0 hnm him
      have hp : (-1 : ℚ)^(m+2) = (-1 : ℚ)^m := by ring
      have hs : altSum f (m+2) = altSum f m +
          (-1 : ℚ)^(m+1)*f (m+1)+(-1 : ℚ)^(m+2)*f (m+2) := by
        simp [altSum, Finset.sum_range_succ]
      rw [hs, hp]
      have hpair := hinc (m+1) (by omega)
      have hpow : (-1 : ℚ)^m = 1 ∨ (-1 : ℚ)^m = -1 := neg_one_pow_eq_or ℚ m
      rcases hpow with hpow | hpow <;> rw [hpow] at ih ⊢ <;>
        simp only [one_mul, neg_one_mul] at ih ⊢ <;>
        rw [show (-1 : ℚ)^(m+1) = -((-1 : ℚ)^m) by rw [pow_succ]; ring] <;>
        simp [hpow] <;> nlinarith

lemma altSum_sign (f : ℕ → ℚ) (m : ℕ)
    (hn : ∀ j, j ≤ m → 0 ≤ f j)
    (ht : 0 < f m)
    (hinc : ∀ j, j < m → f j < f (j+1)) :
    0 < (-1 : ℚ)^m * altSum f m := by
  induction m using Nat.twoStepInduction with
  | zero => simpa [altSum] using ht
  | one =>
      simp only [altSum, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, pow_zero, one_mul, pow_one]
      have hh := hinc 0 (by omega)
      nlinarith
  | more m ih0 ih1 =>
      have hnm : ∀ j, j ≤ m → 0 ≤ f j := fun j hj => hn j (by omega)
      have him : ∀ j, j < m → f j < f (j+1) := fun j hj => hinc j (by omega)
      have ih := altSum_sign_nonneg f m hnm him
      have hp : (-1 : ℚ)^(m+2) = (-1 : ℚ)^m := by ring
      have hs : altSum f (m+2) = altSum f m +
          (-1 : ℚ)^(m+1)*f (m+1)+(-1 : ℚ)^(m+2)*f (m+2) := by
        simp [altSum, Finset.sum_range_succ]
      rw [hs, hp]
      have hpair := hinc (m+1) (by omega)
      have hpow : (-1 : ℚ)^m = 1 ∨ (-1 : ℚ)^m = -1 := neg_one_pow_eq_or ℚ m
      rcases hpow with hpow | hpow <;> rw [hpow] at ih ⊢ <;>
        simp only [one_mul, neg_one_mul] at ih ⊢ <;>
        rw [show (-1 : ℚ)^(m+1) = -((-1 : ℚ)^m) by rw [pow_succ]; ring] <;>
        simp [hpow] <;> nlinarith


lemma tri_strictMono : StrictMono tri := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => rw [tri_succ]; omega
  | succ b hab ih => rw [tri_succ]; omega

lemma exists_tri_interval (n : ℕ) : ∃ m, tri m ≤ n ∧ n < tri (m+1) := by
  let P : ℕ → Prop := fun m => n < tri (m+1)
  have he : ∃ m, P m := by
    refine ⟨n, ?_⟩
    have hle : n+1 ≤ tri (n+1) := by
      rw [tri]
      exact le_tri (n+1) (by omega)
    exact lt_of_lt_of_le (by omega) hle
  let m := Nat.find he
  refine ⟨m, ?_, Nat.find_spec he⟩
  by_cases hm : m = 0
  · simp [hm, tri]
  · have hprev : ¬ P (m-1) := Nat.find_min he (by omega)
    dsimp [P] at hprev
    have : m - 1 + 1 = m := by omega
    rw [this] at hprev
    omega

lemma tri_interval_unique {n a b : ℕ}
    (ha : tri a ≤ n ∧ n < tri (a+1))
    (hb : tri b ≤ n ∧ n < tri (b+1)) : a = b := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hab : tri (a+1) ≤ tri b := tri_strictMono.monotone (by omega)
    exact (not_lt_of_ge (le_trans hab hb.1)) ha.2
  · have hba : tri (b+1) ≤ tri a := tri_strictMono.monotone (by omega)
    exact (not_lt_of_ge (le_trans hba ha.1)) hb.2

noncomputable def triIdx (n : ℕ) : ℕ := Classical.choose (exists_tri_interval n)

lemma triIdx_spec (n : ℕ) : tri (triIdx n) ≤ n ∧ n < tri (triIdx n + 1) :=
  Classical.choose_spec (exists_tri_interval n)

lemma triIdx_eq {n m : ℕ} (h : tri m ≤ n ∧ n < tri (m+1)) : triIdx n = m := by
  exact tri_interval_unique (triIdx_spec n) h

lemma triangular_iff_left_endpoint (n : ℕ) (hn : 0 < n) :
    (∃ k, n = tri k) ↔ n = tri (triIdx n) := by
  constructor
  · rintro ⟨k, rfl⟩
    have hk : 0 < k := by
      by_contra h; simp_all [tri]
    have hi : tri k ≤ tri k ∧ tri k < tri (k+1) := ⟨le_rfl, tri_strictMono (by omega)⟩
    rw [triIdx_eq hi]
  · intro h
    exact ⟨triIdx n, h⟩

lemma triIdx_pred (n : ℕ) (hn : 0 < n) :
    triIdx (n-1) = if n = tri (triIdx n) then triIdx n - 1 else triIdx n := by
  let m := triIdx n
  have hs := triIdx_spec n
  change tri m ≤ n ∧ n < tri (m+1) at hs
  change triIdx (n-1) = if n = tri m then m-1 else m
  by_cases he : n = tri m
  · have hm : 0 < m := by
      by_cases hmz : m = 0
      · have hz : tri 0 = 0 := by rw [tri]
        rw [hmz, hz] at he
        omega
      · omega
    have hmEq : m-1+1=m := by omega
    have ht := tri_succ (m-1)
    rw [hmEq] at ht
    have hp : tri (m-1) ≤ n-1 ∧ n-1 < tri (m-1+1) := by
      rw [hmEq]
      constructor
      · rw [he, ht]
        omega
      · rw [he]
        omega
    rw [if_pos he]
    exact triIdx_eq hp
  · have hp : tri m ≤ n-1 ∧ n-1 < tri (m+1) := by
      constructor
      · have hle := hs.1
        have hlt : tri m < n := lt_of_le_of_ne hle (Ne.symm he)
        omega
      · exact lt_of_le_of_lt (Nat.sub_le _ _) hs.2
    rw [if_neg he]
    exact triIdx_eq hp

noncomputable def layerU (l u j n : ℕ) : ℚ :=
  ∑ S ∈ (Icc l u).powersetCard j, if ∑ k ∈ S, k = n then wt S else 0

lemma layerU_eq_layer (l u j n : ℕ) (hu : n ≤ u) : layerU l u j n = layer l j n := by
  unfold layerU layer
  symm
  apply Finset.sum_subset
  · intro S hS
    rw [mem_powersetCard] at hS ⊢
    exact ⟨fun x hx => by
      have hi := mem_Icc.mp (hS.1 hx)
      exact mem_Icc.mpr ⟨hi.1, le_trans hi.2 hu⟩, hS.2⟩
  · intro S hbig hsmall
    have hsub := (mem_powersetCard.mp hbig).1
    have hx : ∃ x ∈ S, n < x := by
      by_contra h
      push_neg at h
      have hs : S ⊆ Icc l n := fun x hx =>
        mem_Icc.mpr ⟨(mem_Icc.mp (hsub hx)).1, h x hx⟩
      exact hsmall (mem_powersetCard.mpr ⟨hs, (mem_powersetCard.mp hbig).2⟩)
    rcases hx with ⟨x, hxS, hx⟩
    have hle : x ≤ ∑ k ∈ S, k := Finset.single_le_sum (fun k _ => Nat.zero_le k) hxS
    have hne : ∑ k ∈ S, k ≠ n := by omega
    simp [hne]

lemma layer_zero (l n : ℕ) (hn : 0 < n) : layer l 0 n = 0 := by
  have hne : 0 ≠ n := by omega
  simp [layer, powersetCard_zero, hne, wt]

lemma wt_insert (l : ℕ) (S : Finset ℕ) (hl : l ∉ S) :
    wt (insert l S) = (1 / (l.factorial : ℚ)) * wt S := by
  simp [wt, hl]
  ring

lemma layer_succ_rec (l j n : ℕ) (hl : 0 < l) (hln : l ≤ n) :
    layer l (j+1) n = layer (l+1) (j+1) n +
      (1 / (l.factorial : ℚ)) * layer (l+1) j (n-l) := by
  have hI : Icc l n = insert l (Icc (l+1) n) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [← layerU_eq_layer (l+1) n j (n-l) (by omega)]
  unfold layer layerU
  rw [hI, powersetCard_succ_insert (by simp) j]
  rw [sum_union (by
    rw [Finset.disjoint_left]
    intro S hS hi
    have hmem := mem_powersetCard.mp hS
    have hi' := mem_image.mp hi
    rcases hi' with ⟨T, hT, rfl⟩
    have := hmem.1 (mem_insert_self l T)
    simp at this)]
  rw [sum_image]
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    have hnot : l ∉ S := by
      have hsub := (mem_powersetCard.mp hS).1
      intro hx
      have := mem_Icc.mp (hsub hx)
      omega
    rw [sum_insert hnot, wt_insert l S hnot]
    have heq : l + (∑ k ∈ S, k) = n ↔ ∑ k ∈ S, k = n-l := by omega
    by_cases hs : ∑ k ∈ S, k = n-l
    · rw [if_pos hs, if_pos (heq.mpr hs)]
    · rw [if_neg hs, if_neg (by exact fun h => hs (heq.mp h))]
      ring
  · intro A hA B hB he
    have hAf : A ∈ powersetCard j (Icc (l+1) n) := hA
    have hBf : B ∈ powersetCard j (Icc (l+1) n) := hB
    have hnotA : l ∉ A := by
      have hs := (mem_powersetCard.mp hAf).1
      intro h; have := mem_Icc.mp (hs h); omega
    have hnotB : l ∉ B := by
      have hs := (mem_powersetCard.mp hBf).1
      intro h; have := mem_Icc.mp (hs h); omega
    apply Finset.ext
    intro x
    by_cases hx : x = l
    · subst x; simp [hnotA, hnotB]
    · have hh := congrArg (fun T : Finset ℕ => x ∈ T) he
      simpa [hx] using hh

def minSum (l k : ℕ) : ℕ := k*l + tri (k-1)

lemma orderEmb_lower_l (l : ℕ) (S : Finset ℕ) (hlow : ∀ x ∈ S, l ≤ x)
    (i : Fin S.card) : l + i.val ≤ S.orderEmbOfFin rfl i := by
  generalize hv : i.val = v
  induction v using Nat.strong_induction_on generalizing i with
  | h v ih =>
    by_cases hv0 : v = 0
    · have hp := hlow _ (S.orderEmbOfFin_mem rfl i)
      omega
    · let j : Fin S.card := ⟨v-1, by omega⟩
      have hj := ih (v-1) (by omega) j rfl
      have hs := (S.orderEmbOfFin rfl).strictMono
        (show j < i by change v-1 < i.val; omega)
      omega

lemma minSum_eq_sum_range (l k : ℕ) : minSum l k = ∑ i ∈ range k, (l+i) := by
  cases k with
  | zero => simp [minSum, tri]
  | succ k =>
      rw [minSum, tri_eq_sum_range]
      simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_range_id]

lemma minSum_card_le_sum (l : ℕ) (S : Finset ℕ) (hlow : ∀ x ∈ S, l ≤ x) :
    minSum l S.card ≤ ∑ x ∈ S, x := by
  rw [← Finset.sum_attach]
  rw [show S.attach = Finset.univ by ext; simp]
  rw [← Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv
    (fun i : Fin S.card => S.orderEmbOfFin rfl i) (fun x : S => (x : ℕ)) (fun i => rfl)]
  calc
    minSum l S.card = ∑ i : Fin S.card, (l+i.val) := by
      rw [minSum_eq_sum_range, Fin.sum_univ_eq_sum_range (fun i : ℕ => l+i) S.card]
    _ ≤ _ := Finset.sum_le_sum fun i _ => orderEmb_lower_l l S hlow i

lemma layer_eq_zero_of_lt_minSum (l j n : ℕ) (h : n < minSum l j) :
    layer l j n = 0 := by
  unfold layer
  apply Finset.sum_eq_zero
  intro S hS
  have hc := (mem_powersetCard.mp hS).2
  split_ifs with hs
  · have hsub := (mem_powersetCard.mp hS).1
    have ht := minSum_card_le_sum l S (fun x hx => (mem_Icc.mp (hsub hx)).1)
    rw [hc, hs] at ht
    omega
  · rfl

lemma minSum_succ_l (l k : ℕ) : minSum (l+1) k = minSum l k + k := by
  rw [minSum_eq_sum_range, minSum_eq_sum_range]
  simp_rw [show ∀ i, l+1+i=(l+i)+1 by intro; omega]
  rw [Finset.sum_add_distrib]
  simp

lemma minSum_succ_k (l k : ℕ) : minSum l (k+1) = minSum (l+1) k + l := by
  rw [minSum_eq_sum_range, minSum_eq_sum_range, Finset.sum_range_succ]
  have heq : ∑ i ∈ range k, (l+1+i) = (∑ i ∈ range k, (l+i)) + k := by
    simp_rw [show ∀ i, l+1+i=(l+i)+1 by intro; omega]
    rw [Finset.sum_add_distrib]
    simp
  rw [heq]
  omega


lemma minSum_succ_direct (l k : ℕ) :
    minSum l (k+1) = minSum l k + (l+k) := by
  rw [minSum_eq_sum_range, minSum_eq_sum_range]
  simp [Finset.sum_range_succ]

lemma layer_one_pos (l n : ℕ) (hl : 0 < l) (hln : l ≤ n) : 0 < layer l 1 n := by
  unfold layer
  apply Finset.sum_pos'
  · intro S hS
    split <;> simp_all [wt_nonneg]


  · refine ⟨{n}, mem_powersetCard.mpr ⟨?_, by simp⟩, ?_⟩
    · simp [hln]
    · simp [wt]
      positivity
structure Dev (k e : ℕ) where
  val : Fin k → ℕ
  mono : Monotone val
  sum_eq : ∑ i, val i = e

namespace Dev

@[ext] lemma ext {k e} {a b : Dev k e} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

instance (k e : ℕ) : Finite (Dev k e) := by
  let f : Dev k e → (Fin k → Fin (e+1)) := fun d i =>
    ⟨d.val i, by
      have hi : d.val i ≤ ∑ x, d.val x := Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [d.sum_eq] at hi
      omega⟩
  apply Finite.of_injective f
  intro a b h
  apply Dev.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance (k e : ℕ) : Fintype (Dev k e) := Fintype.ofFinite _
noncomputable instance (k e : ℕ) : DecidableEq (Dev k e) := Classical.decEq _

noncomputable def weight (l : ℕ) {k e : ℕ} (d : Dev k e) : ℚ :=
  ∏ i : Fin k, (l+i.val).factorial / (l+i.val+d.val i).factorial

lemma weight_pos (l : ℕ) {k e : ℕ} (d : Dev k e) : 0 < d.weight l := by
  unfold weight
  apply Finset.prod_pos
  intro i hi
  positivity

noncomputable def total (l k e : ℕ) : ℚ := ∑ d : Dev k e, d.weight l

lemma total_pos (l k e : ℕ) [Nonempty (Dev k e)] : 0 < total l k e := by
  unfold total
  apply Finset.sum_pos
  · intro i hi
    exact weight_pos l i
  · exact Finset.univ_nonempty

end Dev

structure Prof (l k n : ℕ) where
  set : Finset ℕ
  subset : set ⊆ Icc l n
  card_eq : set.card = k
  sum_eq : ∑ x ∈ set, x = n

namespace Prof

@[ext] lemma ext {l k n} {a b : Prof l k n} (h : a.set = b.set) : a = b := by
  cases a; cases b; simp_all

instance (l k n : ℕ) : Finite (Prof l k n) := by
  let f : Prof l k n → {S // S ∈ (Icc l n).powerset} := fun p =>
    ⟨p.set, mem_powerset.mpr p.subset⟩
  apply Finite.of_injective f
  intro a b h
  apply Prof.ext
  exact congrArg Subtype.val h

noncomputable instance (l k n : ℕ) : Fintype (Prof l k n) := Fintype.ofFinite _

noncomputable def weight {l k n : ℕ} (p : Prof l k n) : ℚ := wt p.set

lemma layer_eq_total_prof (l k n : ℕ) : layer l k n = ∑ p : Prof l k n, p.weight := by
  unfold layer
  rw [← Finset.sum_filter]
  let F := ((Icc l n).powersetCard k).filter fun S => ∑ x ∈ S, x = n
  let E : Prof l k n ≃ {S // S ∈ F} :=
    { toFun := fun p => ⟨p.set, by simp [F, p.subset, p.card_eq, p.sum_eq]⟩
      invFun := fun S => by
        have hp0 : S.val ∈ F := S.property
        have hp : S.val ∈ (Icc l n).powersetCard k ∧ ∑ x ∈ S.val, x = n := by
          exact Finset.mem_filter.mp hp0
        exact ⟨S, (mem_powersetCard.mp hp.1).1, (mem_powersetCard.mp hp.1).2, hp.2⟩
      left_inv := by intro p; ext; rfl
      right_inv := by intro S; ext; rfl }
  change (∑ S ∈ F, wt S) = ∑ p : Prof l k n, p.weight
  rw [Finset.sum_subtype F (fun _ => Iff.rfl) wt]
  exact (Fintype.sum_equiv E (fun p : Prof l k n => p.weight)
    (fun S : {S // S ∈ F} => wt S.val) (fun p => rfl)).symm


end Prof

namespace Prof

lemma orderEmb_lower_l_card (l : ℕ) (S : Finset ℕ) (hlow : ∀ x ∈ S, l ≤ x)
    {k : ℕ} (hk : S.card = k) (i : Fin k) : l+i.val ≤ S.orderEmbOfFin hk i := by
  have h := orderEmb_lower_l l S hlow (Fin.cast hk.symm i)
  simpa using h

noncomputable def toDev (l k e : ℕ) (p : Prof l k (minSum l k + e)) : Dev k e where
  val i := p.set.orderEmbOfFin p.card_eq i - (l+i.val)
  mono := by
    cases k with
    | zero => exact fun i => Fin.elim0 i
    | succ k =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      have hs := (p.set.orderEmbOfFin p.card_eq).strictMono i.castSucc_lt_succ
      have hb0 := orderEmb_lower_l_card l p.set
        (fun x hx => (mem_Icc.mp (p.subset hx)).1) p.card_eq i.castSucc
      have hb1 := orderEmb_lower_l_card l p.set
        (fun x hx => (mem_Icc.mp (p.subset hx)).1) p.card_eq i.succ
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  sum_eq := by
    rw [Finset.sum_tsub_distrib _ (fun i _ => orderEmb_lower_l_card l p.set
      (fun x hx => (mem_Icc.mp (p.subset hx)).1) p.card_eq i)]
    have hemb : (∑ i : Fin k, p.set.orderEmbOfFin p.card_eq i) = minSum l k + e := by
      calc
        _ = ∑ x : p.set, (x:ℕ) := Fintype.sum_equiv (p.set.orderIsoOfFin p.card_eq).toEquiv
          (fun i : Fin k => p.set.orderEmbOfFin p.card_eq i) (fun x : p.set => (x:ℕ)) (fun _ => rfl)
        _ = ∑ x ∈ p.set, x := by
          have hh := Finset.sum_attach p.set (fun x => x)
          rw [Finset.attach_eq_univ] at hh
          exact hh
        _ = _ := p.sum_eq
    rw [hemb]
    have hbase : (∑ i : Fin k, (l+i.val)) = minSum l k := by
      rw [minSum_eq_sum_range, Fin.sum_univ_eq_sum_range (fun i : ℕ => l+i) k]
    rw [hbase]
    omega

noncomputable def ofDev (l k e : ℕ) (d : Dev k e) : Prof l k (minSum l k + e) := by
  let f : Fin k → ℕ := fun i => l+i.val+d.val i
  have hstrict : StrictMono f := by
    intro a b hab
    have hd := d.mono hab.le
    simp [f]
    omega
  let S := Finset.image f Finset.univ
  have hsum : ∑ q : Fin k, f q = minSum l k + e := by
    dsimp [f]
    rw [Finset.sum_add_distrib, d.sum_eq]
    have hb : ∑ q : Fin k, (l+q.val) = minSum l k := by
      rw [minSum_eq_sum_range, Fin.sum_univ_eq_sum_range (fun i : ℕ => l+i) k]
    rw [hb]
  refine ⟨S, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_Icc]
    change x ∈ Finset.image f Finset.univ at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, hi, rfl⟩
    constructor
    · dsimp [f]
      omega
    · have hle : f i ≤ ∑ q : Fin k, f q := Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [hsum] at hle
      exact hle
  · dsimp [S]
    rw [Finset.card_image_of_injective _ hstrict.injective]
    simp
  · dsimp [S]
    rw [Finset.sum_image hstrict.injective.injOn]
    exact hsum

lemma ofDev_toDev (l k e : ℕ) (p : Prof l k (minSum l k + e)) :
    ofDev l k e (toDev l k e p) = p := by
  apply Prof.ext
  unfold ofDev
  simp only
  have hf : (fun i : Fin k => l+i.val+(toDev l k e p).val i) =
      p.set.orderEmbOfFin p.card_eq := by
    funext i
    simp only [toDev]
    have hb := orderEmb_lower_l_card l p.set
      (fun x hx => (mem_Icc.mp (p.subset hx)).1) p.card_eq i
    omega
  rw [hf, p.set.image_orderEmbOfFin_univ p.card_eq]

lemma toDev_ofDev (l k e : ℕ) (d : Dev k e) :
    toDev l k e (ofDev l k e d) = d := by
  apply Dev.ext
  funext i
  unfold toDev ofDev
  simp only
  let f : Fin k → ℕ := fun i => l+i.val+d.val i
  have hstrict : StrictMono f := by
    intro a b hab
    have hd := d.mono hab.le
    simp [f]
    omega
  have hmem (q : Fin k) : f q ∈ Finset.image f Finset.univ := by simp
  have hcard : (Finset.image f Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hstrict.injective]
    simp
  have hemb : (Finset.image f Finset.univ).orderEmbOfFin hcard = f :=
    (Finset.orderEmbOfFin_unique hcard hmem hstrict).symm
  rw [hemb]
  simp [f]

noncomputable def devEquiv (l k e : ℕ) :
    Prof l k (minSum l k + e) ≃ Dev k e where
  toFun := toDev l k e
  invFun := ofDev l k e
  left_inv := ofDev_toDev l k e
  right_inv := toDev_ofDev l k e

lemma weight_toDev (l k e : ℕ) (p : Prof l k (minSum l k + e)) :
    p.weight = (∏ i : Fin k, (1 / ((l+i.val).factorial : ℚ))) *
      (toDev l k e p).weight l := by
  unfold Prof.weight wt Dev.weight
  have hprod : (∏ x ∈ p.set, (1 / (x.factorial : ℚ))) =
      ∏ i : Fin k, (1 / ((p.set.orderEmbOfFin p.card_eq i).factorial : ℚ)) := by
    calc
      _ = ∏ x : p.set, (1 / (((x:ℕ).factorial : ℚ))) := by
        rw [← Finset.prod_attach]
        rw [show p.set.attach = Finset.univ by ext; simp]
      _ = _ := (Fintype.prod_equiv (p.set.orderIsoOfFin p.card_eq).toEquiv
        (fun i : Fin k => 1 / ((p.set.orderEmbOfFin p.card_eq i).factorial : ℚ))
        (fun x : p.set => 1 / (((x:ℕ).factorial : ℚ))) (fun _ => rfl)).symm
  rw [hprod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [toDev]
  have hb := orderEmb_lower_l_card l p.set
    (fun x hx => (mem_Icc.mp (p.subset hx)).1) p.card_eq i
  rw [show l+i.val+(p.set.orderEmbOfFin p.card_eq i-(l+i.val)) =
      p.set.orderEmbOfFin p.card_eq i by omega]
  field_simp

lemma layer_dev (l k e : ℕ) :
    layer l k (minSum l k + e) =
      (∏ i : Fin k, (1 / ((l+i.val).factorial : ℚ))) * Dev.total l k e := by
  rw [layer_eq_total_prof]
  unfold Dev.total
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (devEquiv l k e) (fun p : Prof l k (minSum l k+e) => p.weight)
    (fun d : Dev k e => (∏ i : Fin k, (1 / ((l+i.val).factorial : ℚ))) * d.weight l)
    (fun p => weight_toDev l k e p)


end Prof

namespace Dev

noncomputable def posSet {m e : ℕ} (d : Dev m (e+1)) : Finset (Fin m) :=
  Finset.univ.filter fun i => 0 < d.val i

lemma posSet_nonempty {m e : ℕ} (d : Dev m (e+1)) : (posSet d).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hz : ∀ i, d.val i = 0 := by
    intro i
    have : i ∉ posSet d := by simp [h]
    simp [posSet] at this
    omega
  have := d.sum_eq
  simp [hz] at this

noncomputable def firstPos {m e : ℕ} (d : Dev m (e+1)) : Fin m :=
  (posSet d).min' (posSet_nonempty d)

lemma firstPos_pos {m e : ℕ} (d : Dev m (e+1)) : 0 < d.val (firstPos d) := by
  have := Finset.min'_mem (posSet d) (posSet_nonempty d)
  simpa [posSet] using this

lemma val_eq_zero_of_lt_firstPos {m e : ℕ} (d : Dev m (e+1))
    (i : Fin m) (hi : i < firstPos d) : d.val i = 0 := by
  by_contra h
  have hip : i ∈ posSet d := by simp [posSet]; omega
  have hle := Finset.min'_le (posSet d) i hip
  exact (not_lt_of_ge hle) hi

noncomputable def down {m e : ℕ} (d : Dev m (e+1)) : Dev m e where
  val i := if i = firstPos d then d.val i - 1 else d.val i
  mono := by
    cases m with
    | zero => exact fun i => Fin.elim0 i
    | succ m =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      by_cases h0 : i.castSucc = firstPos d
      · have h1 : i.succ ≠ firstPos d := by
          intro h
          have hv0 := congrArg Fin.val h0
          have hv1 := congrArg Fin.val h
          simp at hv0 hv1
          omega
        have hle : d.val i.castSucc - 1 ≤ d.val i.succ :=
          le_trans (Nat.sub_le _ _) (d.mono i.castSucc_le_succ)
        simpa only [h0, h1, if_pos, if_neg] using hle
      · by_cases h1 : i.succ = firstPos d
        · have hlt : i.castSucc < firstPos d := by
            rw [← h1]
            exact Fin.castSucc_lt_succ
          have hz := val_eq_zero_of_lt_firstPos d i.castSucc hlt
          change (if i.castSucc = firstPos d then d.val i.castSucc-1 else d.val i.castSucc) ≤
            (if i.succ = firstPos d then d.val i.succ-1 else d.val i.succ)
          simp [h0, h1, hz]
        · simp only [h0, h1, if_neg]
          exact d.mono i.castSucc_le_succ
  sum_eq := by
    classical
    have herase : (∑ i ∈ Finset.univ.erase (firstPos d),
        (if i = firstPos d then d.val i - 1 else d.val i)) =
        ∑ i ∈ Finset.univ.erase (firstPos d), d.val i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_neg]
      simpa using hi
    rw [show (∑ i : Fin m, (if i = firstPos d then d.val i - 1 else d.val i)) =
        (d.val (firstPos d)-1) + ∑ i ∈ Finset.univ.erase (firstPos d), d.val i by
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ (firstPos d))]
      simp only [if_pos]
      rw [show (Finset.univ : Finset (Fin m)) \ {firstPos d} =
          Finset.univ.erase (firstPos d) by ext; simp, herase]]
    rw [show ∑ i ∈ Finset.univ.erase (firstPos d), d.val i =
        (∑ i, d.val i) - d.val (firstPos d) by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (firstPos d))]
      omega]
    rw [d.sum_eq]
    have hp := firstPos_pos d
    have hb : d.val (firstPos d) ≤ e+1 := by
      have hi : d.val (firstPos d) ≤ ∑ i : Fin m, d.val i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      rw [d.sum_eq] at hi
      exact hi
    omega


noncomputable def reindex {m e e' : ℕ} (h : e = e') (d : Dev m e) : Dev m e' where
  val := d.val
  mono := d.mono
  sum_eq := d.sum_eq.trans h

noncomputable def downN {m : ℕ} : ∀ H r, Dev m (H+r) → Dev m r
  | 0, r, d => ⟨d.val, d.mono, by simpa using d.sum_eq⟩
  | H+1, r, d =>
      downN H r (down (e := H+r) (reindex (by omega) d))



end Dev

namespace Dev

noncomputable def posAny {k e : ℕ} (d : Dev k e) : Finset (Fin k) :=
  Finset.univ.filter fun i => 0 < d.val i

lemma posAny_nonempty {k e : ℕ} (d : Dev k e) (he : 0 < e) : (posAny d).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hz : ∀ i, d.val i = 0 := by
    intro i
    have : i ∉ posAny d := by simp [h]
    simp [posAny] at this
    omega
  have := d.sum_eq
  simp [hz] at this
  omega

noncomputable def firstAny {k e : ℕ} (d : Dev k e) (he : 0 < e) : Fin k :=
  (posAny d).min' (posAny_nonempty d he)

lemma firstAny_pos {k e : ℕ} (d : Dev k e) (he : 0 < e) :
    0 < d.val (firstAny d he) := by
  have := Finset.min'_mem (posAny d) (posAny_nonempty d he)
  simpa [posAny] using this

lemma val_zero_before_firstAny {k e : ℕ} (d : Dev k e) (he : 0 < e)
    (i : Fin k) (hi : i < firstAny d he) : d.val i = 0 := by
  by_contra h
  have hip : i ∈ posAny d := by simp [posAny]; omega
  have hle := Finset.min'_le (posAny d) i hip
  exact (not_lt_of_ge hle) hi

noncomputable def cut {m r : ℕ} (p : Dev m r) : ℕ :=
  if h : 0 < r then (firstAny p h).val else m

lemma cut_le {m r : ℕ} (p : Dev m r) : cut p ≤ m := by
  unfold cut
  split <;> simp_all

lemma val_zero_before_cut {m r : ℕ} (p : Dev m r) (i : Fin m)
    (hi : i.val < cut p) : p.val i = 0 := by
  unfold cut at hi
  split at hi <;> rename_i h
  · exact val_zero_before_firstAny p h i (by simpa using hi)
  · have hr : r = 0 := by omega
    have hle : p.val i ≤ ∑ j : Fin m, p.val j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have : p.val i ≤ r := by simpa [p.sum_eq] using hle
    omega

lemma val_pos_at_cut {m r : ℕ} (p : Dev m r) (hcut : cut p < m) :
    0 < p.val ⟨cut p, hcut⟩ := by
  have hpos : 0 < r := by
    by_contra h
    have hc : cut p = m := by simp [cut, h]
    omega
  have hc : cut p = (firstAny p hpos).val := by simp [cut, hpos]
  simpa [hc] using firstAny_pos p hpos

end Dev

namespace Dev

noncomputable def finVal {n : ℕ} (f : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : j < n then f ⟨j,h⟩ else 0

lemma fin_sum_eq_range {n : ℕ} (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = ∑ j ∈ range n, finVal f j := by
  have hh := Fin.sum_univ_eq_sum_range (finVal f) n
  calc
    _ = ∑ i : Fin n, finVal f i.val := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [finVal, i.isLt]
    _ = _ := hh

noncomputable def liftH (l m r : ℕ) (d : Dev (m-1) (l+m-1+r)) : ℕ :=
  if hm : 1 < m then l + (firstAny d (by omega)).val else 0

noncomputable def lift (l m r : ℕ) (d : Dev (m-1) (l+m-1+r)) :
    Dev m (liftH l m r d + r) := by
  by_cases hm : 1 < m
  · have hLH : liftH l m r d = l + (firstAny d (by omega)).val := by simp [liftH, hm]
    let q := (firstAny d (by omega)).val
    have hq : q < m - 1 := by simpa [q] using (firstAny d (by omega)).isLt
    let v : Fin m → ℕ := fun i => if i.val ≤ q then 0 else
      d.val ⟨i.val-1, by have := i.isLt; omega⟩ - 1
    have hmono : Monotone v := by
      intro a b hab
      change (if a.val ≤ q then 0 else d.val ⟨a.val-1, by omega⟩-1) ≤
        (if b.val ≤ q then 0 else d.val ⟨b.val-1, by omega⟩-1)
      by_cases ha : a.val ≤ q
      · rw [if_pos ha]
        omega
      · have hb : ¬ b.val ≤ q := by omega
        rw [if_neg ha, if_neg hb]
        have hab' : (⟨a.val-1, by omega⟩ : Fin (m-1)) ≤ ⟨b.val-1, by omega⟩ :=
          Fin.mk_le_mk.mpr (Nat.sub_le_sub_right hab 1)
        exact Nat.sub_le_sub_right (d.mono hab') 1
    refine @Dev.mk m (liftH l m r d + r) v hmono ?_
    -- Sum the shifted positive tail.
    have hz (i : Fin (m-1)) (hi : i.val < q) : d.val i = 0 := by
      apply val_zero_before_firstAny d (by omega) i
      change i.val < (firstAny d (by omega)).val
      exact hi
    have hp (i : Fin (m-1)) (hi : q ≤ i.val) : 0 < d.val i := by
      have hfirst := firstAny_pos d (by omega)
      have hmono := d.mono (show firstAny d (by omega) ≤ i by change q ≤ i.val; exact hi)
      omega
    have hsumv : ∑ i : Fin m, v i = (∑ i : Fin (m-1), d.val i) - ((m-1)-q) := by
      rw [fin_sum_eq_range v, fin_sum_eq_range d.val]
      have hq : q < m-1 := (firstAny d (by omega)).isLt
      have hleft : (∑ i ∈ range m, finVal v i) =
          ∑ j ∈ Ico q (m-1), (finVal d.val j - 1) := by
        rw [show (∑ i ∈ range m, finVal v i) =
            ∑ i ∈ Ico (q+1) m, finVal v i by
          symm
          apply Finset.sum_subset
          · intro i hi
            simp only [mem_Ico, mem_range] at hi ⊢
            omega
          · intro i hi hsmall
            simp only [mem_range] at hi
            have hiq : i ≤ q := by simp only [mem_Ico] at hsmall; omega
            simp [finVal, v, hi, hiq]]
        refine Finset.sum_bij (fun i _ => i-1) (fun i hi => by
            simp only [mem_Ico] at hi ⊢; omega)
          (fun i hi i' hi' he => by
            simp only [mem_Ico] at hi hi'
            change i - 1 = i' - 1 at he
            omega)
          (fun j hj => by
            refine ⟨j+1, ?_, ?_⟩
            · simp only [mem_Ico] at hj ⊢
              omega
            · dsimp)
          (fun i hi => by
            simp only [mem_Ico] at hi
            simp [finVal, v, show i < m by omega, show i-1 < m-1 by omega,
              show ¬ i ≤ q by omega])
      rw [hleft]
      have htail : (∑ j ∈ Ico q (m-1), finVal d.val j) =
          ∑ i ∈ range (m-1), finVal d.val i := by
        apply Finset.sum_subset
        · intro i hi
          simp only [mem_Ico, mem_range] at hi ⊢
          omega
        · intro i hi hsmall
          simp only [mem_range] at hi
          have hiq : i < q := by simp only [mem_Ico] at hsmall; omega
          simp [finVal, hi, hz ⟨i,hi⟩ hiq]
      rw [Finset.sum_tsub_distrib _ (fun j hj => by
        have hj' := mem_Ico.mp hj
        have hpj := hp ⟨j, hj'.2⟩ hj'.1
        simpa [finVal, hj'.2] using hpj)]
      rw [htail]
      simp
    calc
      (∑ i : Fin m, v i) = l + (firstAny d (by omega)).val + r := by
        rw [hsumv, d.sum_eq]
        dsimp [q]
        omega
      _ = liftH l m r d + r :=
        congrArg (fun x => x + r) hLH.symm
  · have hmle : m ≤ 1 := by omega
    have hsumzero : (∑ i : Fin (m-1), d.val i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exfalso
      have hii := i.isLt
      omega
    have hE : l+m-1+r = 0 := by
      have hs := d.sum_eq
      rw [hsumzero] at hs
      omega
    have hr : r = 0 := by omega
    have hLH : liftH l m r d = 0 := by simp [liftH, hm]
    refine @Dev.mk m (liftH l m r d + r) (fun _ => 0) (fun _ _ _ => le_rfl) ?_
    simp [hLH, hr]

lemma lift_val_eq (l m r : ℕ) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) (i : Fin m) :
    (lift l m r d).val i =
      if i.val ≤ (firstAny d (by omega)).val then 0 else
        d.val ⟨i.val-1, by omega⟩ - 1 := by
  unfold lift
  simp only [dif_pos hm]

lemma liftH_spec (l m r : ℕ) (hm : 1 < m) (d : Dev (m-1) (l+m-1+r)) :
    liftH l m r d = l + (firstAny d (by omega)).val := by simp [liftH, hm]


lemma factorial_mul_prod_Ico (l q N : ℕ) (hq : q ≤ N) :
    ((l+q).factorial : ℚ) * (∏ j ∈ Ico q N, (l+j+1 : ℚ)) = (l+N).factorial := by
  induction N, hq using Nat.le_induction with
  | base => simp
  | succ N hq ih =>
      rw [Finset.prod_Ico_succ_top (by omega), ← mul_assoc, ih]
      rw [show l+(N+1)=(l+N)+1 by omega, Nat.factorial_succ]
      push_cast
      ring

lemma lift_weight (l m r : ℕ) (hm : 1 < m) (d : Dev (m-1) (l+m-1+r)) :
    ((l+m-1).factorial : ℚ) * d.weight l =
      ((liftH l m r d).factorial : ℚ) * (lift l m r d).weight l := by
  have hLH := liftH_spec l m r hm d
  let q := (firstAny d (by omega)).val
  have hq : q < m-1 := (firstAny d (by omega)).isLt
  have hz (i : Fin (m-1)) (hi : i.val < q) : d.val i = 0 := by
    apply val_zero_before_firstAny d (by omega) i
    simpa [q] using hi
  have hp (i : Fin (m-1)) (hi : q ≤ i.val) : 0 < d.val i := by
    have hfirst := firstAny_pos d (by omega)
    have hm := d.mono (show firstAny d (by omega) ≤ i by simp [q] at hi ⊢; omega)
    omega
  -- Rewrite both products as products over the common positive tail.
  have hdprod : (∏ i : Fin (m-1),
      ((l+i.val).factorial : ℚ) / (l+i.val+d.val i).factorial) =
      ∏ j ∈ Ico q (m-1),
        ((l+j).factorial : ℚ) / (l+j+finVal d.val j).factorial := by
    calc
      _ = ∏ i : Fin (m-1),
          ((l+i.val).factorial : ℚ) / (l+i.val+finVal d.val i.val).factorial := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [finVal, i.isLt]
      _ = ∏ j ∈ range (m-1),
          ((l+j).factorial : ℚ) / (l+j+finVal d.val j).factorial :=
        Fin.prod_univ_eq_prod_range
          (fun j : ℕ => ((l+j).factorial : ℚ) /
            (l+j+finVal d.val j).factorial) (m-1)
      _ = _ := by
        symm
        apply Finset.prod_subset
        · intro j hj
          simp only [mem_Ico, mem_range] at hj ⊢
          omega
        · intro j hj htail
          simp only [mem_range] at hj
          have hjq : j < q := by simp only [mem_Ico] at htail; omega
          have hjlt : j < m - 1 := by omega
          have hv : finVal d.val j = 0 := by
            simp [finVal, hjlt, hz ⟨j, hjlt⟩ hjq]
          rw [hv, add_zero, div_self]
          positivity
  have heprod : (∏ i : Fin m,
      ((l+i.val).factorial : ℚ) / (l+i.val+(lift l m r d).val i).factorial) =
      ∏ j ∈ Ico q (m-1),
        ((l+j+1).factorial : ℚ) / (l+j+finVal d.val j).factorial := by
    let e := (lift l m r d).val
    calc
      _ = ∏ i : Fin m,
          ((l+i.val).factorial : ℚ) / (l+i.val+finVal e i.val).factorial := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [finVal, e, i.isLt]
      _ = ∏ i ∈ range m,
          ((l+i).factorial : ℚ) / (l+i+finVal e i).factorial :=
        Fin.prod_univ_eq_prod_range
          (fun i : ℕ => ((l+i).factorial : ℚ) /
            (l+i+finVal e i).factorial) m
      _ = ∏ i ∈ Ico (q+1) m,
          ((l+i).factorial : ℚ) / (l+i+finVal e i).factorial := by
        symm
        apply Finset.prod_subset
        · intro i hi
          simp only [mem_Ico, mem_range] at hi ⊢
          omega
        · intro i hi htail
          simp only [mem_range] at hi
          have hiq : i ≤ q := by simp only [mem_Ico] at htail; omega
          have hv : finVal e i = 0 := by
            simp only [finVal]
            rw [dif_pos (by exact hi)]
            dsimp [e]
            rw [lift_val_eq l m r hm d ⟨i, hi⟩]
            rw [if_pos (by simpa [q] using hiq)]
          rw [hv, add_zero, div_self]
          positivity
      _ = _ := by
        refine Finset.prod_bij (fun i _ => i-1)
          (fun i hi => by simp only [mem_Ico] at hi ⊢; omega)
          (fun i hi i' hi' he => by
            simp only [mem_Ico] at hi hi'
            have hi0 : 0 < i := by omega
            have hi0' : 0 < i' := by omega
            change i - 1 = i' - 1 at he
            omega)
          (fun j hj => by
            refine ⟨j+1, ?_, ?_⟩
            · simp only [mem_Ico] at hj ⊢
              omega
            · simp)
          (fun i hi => ?_)
        simp only [mem_Ico] at hi
        have hi_lt : i < m := by omega
        have him1 : i - 1 < m - 1 := by omega
        have hqi : q ≤ i - 1 := by omega
        have hpos := hp ⟨i-1, him1⟩ hqi
        have hgt : ¬ i ≤ (firstAny d (by omega)).val := by simpa [q] using (show ¬ i ≤ q by omega)
        rw [show finVal e i = d.val ⟨i-1, him1⟩ - 1 by
          simp only [finVal]
          rw [dif_pos (by exact hi_lt)]
          dsimp [e]
          rw [lift_val_eq l m r hm d ⟨i, hi_lt⟩, if_neg hgt]]
        rw [show l+i+(d.val ⟨i-1, him1⟩-1) =
            l+(i-1)+d.val ⟨i-1, him1⟩ by omega]
        simp only [finVal, him1, if_pos]
        have hnum : l + i = l + (i - 1) + 1 := by omega
        rw [hnum]
        simp
  unfold weight
  rw [hdprod, heprod]
  have hfacNat := congrArg Nat.factorial hLH
  have hfac : ((liftH l m r d).factorial : ℚ) =
      ((l + (firstAny d (by omega)).val).factorial : ℚ) := by
    exact_mod_cast hfacNat
  rw [hfac]
  have hleft : ((l + m - 1).factorial : ℚ) =
      ((l + (m-1)).factorial : ℚ) := by
    congr 2 <;> omega
  simp only [hleft]
  rw [← factorial_mul_prod_Ico l q (m-1) (by omega)]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp only [q]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [show l + j + 1 = (l+j)+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp

noncomputable def nearMap (l m r : ℕ) (d : Dev (m-1) (l+m-1+r)) : Dev m r :=
  downN (liftH l m r d) r (lift l m r d)

end Dev




def rup (a x : ℕ) : ℚ :=
  if x = 0 then 1 else if x = 1 then 1 / (a+1) else
    1 / ((a+1 : ℚ) * (a+2) * (a+3)^(x-2))

lemma rup_pos (a x : ℕ) : 0 < rup a x := by
  unfold rup; split_ifs <;> positivity

lemma frac_pow_le (A : ℚ) (n : ℕ) (hA : 0 < A) :
    (A / (A+1))^n ≤ A / (A+n) := by
  have hb := one_add_mul_le_pow (a := 1 / A) (by
    have hp : 0 < 1/A := by positivity
    exact le_trans (by norm_num) hp.le) n
  rw [show 1 + 1/A = (A+1)/A by field_simp] at hb
  rw [div_pow] at hb
  rw [div_pow, div_le_div_iff₀] <;> try positivity
  field_simp at hb ⊢
  nlinarith [pow_pos hA n]

lemma rup_shift (a x : ℕ) :
    rup (a+1) x / rup a x ≤ (a+3 : ℚ) / (a+x+3) := by
  by_cases h0 : x = 0
  · subst x
    simp [rup]
    rw [div_self] <;> positivity
  by_cases h1 : x = 1
  · subst x
    norm_num [rup]
    field_simp
    nlinarith
  have hx : 2 ≤ x := by omega
  have hp := frac_pow_le (a+3 : ℚ) (x-2) (by positivity)
  have hform : rup (a+1) x / rup a x =
      ((a+1 : ℚ)/(a+3)) * (((a+3 : ℚ)/(a+4))^(x-2)) := by
    simp only [rup, h0, h1]
    norm_num [Nat.cast_add, Nat.cast_one]
    rw [div_pow]
    field_simp
    ring_nf
  rw [hform]
  have hpow : (((a+3 : ℚ)/(a+4))^(x-2)) ≤
      (a+3 : ℚ)/(a+3+(x-2 : ℕ)) := by
    convert hp using 1 <;> push_cast <;> ring
  calc
    _ ≤ ((a+1 : ℚ)/(a+3)) * ((a+3 : ℚ)/(a+3+(x-2 : ℕ))) := by
      gcongr
    _ = (a+1 : ℚ) / (a+x+1) := by
      have hc : ((x-2 : ℕ) : ℚ) = (x:ℚ)-2 := by
        rw [Nat.cast_sub hx]
        norm_num
      rw [hc]
      norm_num [Nat.cast_add, Nat.cast_one]
      rw [show (a:ℚ)+3+((x:ℚ)-2) = a+x+1 by ring]
      field_simp
    _ ≤ (a+3 : ℚ)/(a+x+3) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      push_cast
      nlinarith

def gg (A : ℕ) : (n : ℕ) → ℚ
  | 0 => 1
  | n+1 => rup (A+1) (n+1) +
      ∑ x ∈ range (n+1), rup A (x+1) * gg (A+1) (n-x)
termination_by n => n
 decreasing_by omega

lemma gg_pos (A n : ℕ) : 0 < gg A n := by
  cases n with
  | zero => simp [gg]
  | succ n =>
    rw [gg]
    exact add_pos_of_pos_of_nonneg (rup_pos _ _) (Finset.sum_nonneg fun x hx =>
      mul_nonneg (rup_pos _ _).le (gg_pos _ _).le)
termination_by n

-- A parameter shift for the recursively summed composition weights.
lemma gg_shift (A n : ℕ) :
    gg (A+1) n ≤ ((A+4 : ℚ)/(A+n+4)) * gg A n := by
  induction n using Nat.strong_induction_on generalizing A with
  | h N ih =>
    cases N with
    | zero =>
      simp [gg]
      rw [div_self] <;> positivity
    | succ n =>
      rw [gg, gg]
      let C : ℚ := (↑A+4 : ℚ)/(↑A+↑(n+1)+4)
      have hterm : rup (A+2) (n+1) ≤ C * rup (A+1) (n+1) := by
        have hr := rup_shift (A+1) (n+1)
        rw [div_le_iff₀ (rup_pos (A+1) (n+1))] at hr
        have heq : ((↑(A+1)+3 : ℚ)/(↑(A+1)+↑(n+1)+3)) = C := by
          dsimp [C]
          push_cast
          ring
        rw [heq] at hr
        rw [show A+1+1 = A+2 by omega] at hr
        simpa [mul_comm] using hr
      have hsum : (∑ x ∈ range (n+1), rup (A+1) (x+1) * gg (A+2) (n-x)) ≤
          C * (∑ x ∈ range (n+1), rup A (x+1) * gg (A+1) (n-x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        simp only [mem_range] at hx
        have hr := rup_shift A (x+1)
        rw [div_le_iff₀ (rup_pos A (x+1))] at hr
        have hr' : rup (A+1) (x+1) ≤
            ((↑A+3 : ℚ)/(↑A+↑x+4))*rup A (x+1) := by
          have heq : ((↑A+3 : ℚ)/(↑A+↑(x+1)+3)) =
              (↑A+3)/(↑A+↑x+4) := by push_cast; ring
          rw [heq] at hr
          simpa [mul_comm] using hr
        have hg := ih (n-x) (by omega) (A+1)
        have hg' : gg (A+2) (n-x) ≤
            ((↑A+5 : ℚ)/(↑A+↑(n-x)+5))*gg (A+1) (n-x) := by
          have heq : ((↑(A+1)+4 : ℚ)/(↑(A+1)+↑(n-x)+4)) =
              (↑A+5)/(↑A+↑(n-x)+5) := by push_cast; ring
          rw [heq] at hg
          simpa using hg
        have hprod : rup (A+1) (x+1) * gg (A+2) (n-x) ≤
            (((↑A+3 : ℚ)/(↑A+↑x+4))*((↑A+5 : ℚ)/(↑A+↑(n-x)+5))) *
              (rup A (x+1)*gg (A+1) (n-x)) := by
          calc
            _ ≤ (((↑A+3 : ℚ)/(↑A+↑x+4))*rup A (x+1)) *
                (((↑A+5 : ℚ)/(↑A+↑(n-x)+5))*gg (A+1) (n-x)) := by
              exact mul_le_mul hr' hg' (gg_pos _ _).le
                (mul_nonneg (by positivity) (rup_pos _ _).le)
            _ = _ := by ring
        calc
          _ ≤ _ := hprod
          _ ≤ C * (rup A (x+1)*gg (A+1) (n-x)) := by
            apply mul_le_mul_of_nonneg_right
            · dsimp [C]
              rw [_root_.div_mul_div_comm]
              field_simp
              rw [Nat.cast_sub (by omega)]
              push_cast
              have hnx : (0:ℚ) ≤ (n:ℚ) - (x:ℚ) :=
                sub_nonneg.mpr (by exact_mod_cast (show x ≤ n by omega))
              rw [show
                ((A:ℚ)+3)*((A:ℚ)+5)*((A:ℚ)+((n:ℚ)+1)+4) =
                ((A:ℚ)+(x:ℚ)+4)*((A:ℚ)+(n:ℚ)-(x:ℚ)+5)*((A:ℚ)+4) -
                  (((A:ℚ)+4)*(x:ℚ)*((n:ℚ)-(x:ℚ)) +
                    ((A:ℚ)+4)*(x:ℚ) + (A:ℚ)+(n:ℚ)+5) by ring]
              have : (0:ℚ) ≤ ((A:ℚ)+4)*(x:ℚ)*((n:ℚ)-(x:ℚ)) +
                    ((A:ℚ)+4)*(x:ℚ) + (A:ℚ)+(n:ℚ)+5 := by positivity
              linarith
            · exact mul_nonneg (rup_pos _ _).le (gg_pos _ _).le
      calc
        _ ≤ C * rup (A+1) (n+1) +
            C * (∑ x ∈ range (n+1), rup A (x+1) * gg (A+1) (n-x)) :=
          add_le_add hterm hsum
        _ = C * (rup (A+1) (n+1) +
            ∑ x ∈ range (n+1), rup A (x+1) * gg (A+1) (n-x)) := by ring

lemma rup_diag (a x : ℕ) (hx : 0 < x) :
    rup (a+1) (x+1) / rup a x ≤ 1 / (a+3 : ℚ) := by
  by_cases hx1 : x = 1
  · subst x
    norm_num [rup]
    field_simp
    nlinarith
  have hx2 : 2 ≤ x := by omega
  have hform : rup (a+1) (x+1) / rup a x =
      ((a+1 : ℚ)/((a+3)*(a+4))) *
        (((a+3 : ℚ)/(a+4))^(x-2)) := by
    have hx0 : ¬ x = 0 := by omega
    have hx1 : ¬ x = 1 := by omega
    have hs0 : ¬ x+1 = 0 := by omega
    have hs1 : ¬ x+1 = 1 := by omega
    simp only [rup, hx0, hx1, hs0, hs1]
    rw [show x+1-2 = (x-2)+1 by omega, pow_succ]
    push_cast
    rw [div_pow]
    field_simp
    ring_nf
  rw [hform]
  have hb : (0:ℚ) ≤ (a+3)/(a+4) := by positivity
  have hb1 : (a+3 : ℚ)/(a+4) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  have hp : ((a+3 : ℚ)/(a+4))^(x-2) ≤ 1 := by
    simpa using pow_le_one₀ hb hb1
  calc
    _ ≤ ((a+1 : ℚ)/((a+3)*(a+4))) * 1 := by gcongr
    _ ≤ 1/(a+3 : ℚ) := by
      field_simp
      nlinarith

lemma rup_diag_frac (a x : ℕ) (hx : 2 ≤ x) :
    rup (a+1) (x+1) / rup a x ≤
      (a+1 : ℚ) / ((a+4) * (a+x+1)) := by
  have hform : rup (a+1) (x+1) / rup a x =
      ((a+1 : ℚ)/((a+3)*(a+4))) *
        (((a+3 : ℚ)/(a+4))^(x-2)) := by
    have hx0 : ¬ x = 0 := by omega
    have hx1 : ¬ x = 1 := by omega
    have hs0 : ¬ x+1 = 0 := by omega
    have hs1 : ¬ x+1 = 1 := by omega
    simp only [rup, hx0, hx1, hs0, hs1]
    rw [show x+1-2 = (x-2)+1 by omega, pow_succ]
    push_cast
    rw [div_pow]
    field_simp
    ring_nf
  rw [hform]
  have hp := frac_pow_le (a+3 : ℚ) (x-2) (by positivity)
  have hpow : (((a+3 : ℚ)/(a+4))^(x-2)) ≤
      (a+3 : ℚ)/(a+x+1) := by
    rw [Nat.cast_sub hx] at hp
    norm_num [Nat.cast_add, Nat.cast_one] at hp ⊢
    convert hp using 1 <;> ring
  calc
    _ ≤ ((a+1 : ℚ)/((a+3)*(a+4))) * ((a+3 : ℚ)/(a+x+1)) := by gcongr
    _ = _ := by field_simp <;> ring

def CB (H : ℕ) : ℚ := H.factorial * gg (H+1) H

lemma prepend_bound (H : ℕ) (hH : 14 ≤ H) :
    (H+1 : ℚ) * rup (H+2) 1 * gg (H+3) H ≤
      (3/10 : ℚ) * gg (H+1) H := by
  have h2 := gg_shift (H+2) H
  have h1 := gg_shift (H+1) H
  have hchain : gg (H+3) H ≤
      (((H+6 : ℚ)/(2*H+6))*((H+5 : ℚ)/(2*H+5))) * gg (H+1) H := by
    calc
      _ ≤ ((H+6 : ℚ)/(2*H+6)) * gg (H+2) H := by
        convert h2 using 1 <;> push_cast <;> ring
      _ ≤ ((H+6 : ℚ)/(2*H+6)) *
          (((H+5 : ℚ)/(2*H+5))*gg (H+1) H) := by
        exact mul_le_mul_of_nonneg_left (by
          convert h1 using 1 <;> push_cast <;> ring) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (H+1 : ℚ) * rup (H+2) 1 *
        (((H+6 : ℚ)/(2*H+6))*((H+5 : ℚ)/(2*H+5)) * gg (H+1) H) := by
      exact mul_le_mul_of_nonneg_left hchain
        (mul_nonneg (by positivity) (rup_pos _ _).le)
    _ = (((H+1 : ℚ)/(H+3))*((H+6 : ℚ)/(2*H+6))*
          ((H+5 : ℚ)/(2*H+5))) * gg (H+1) H := by
      simp [rup]
      ring
    _ ≤ (3/10 : ℚ) * gg (H+1) H := by
      apply mul_le_mul_of_nonneg_right
      · field_simp
        let k : ℚ := H-14
        have hk : 0 ≤ k := by dsimp [k]; exact sub_nonneg.mpr (by exact_mod_cast hH)
        have hp : 0 ≤ k^3 + 33*k^2 + 275*k + 111 := by positivity
        dsimp [k] at hp
        nlinarith
      · exact (gg_pos _ _).le

lemma increment_bound (H y : ℕ) (hH : 14 ≤ H) (hy : y < H) :
    (H+1 : ℚ) * rup (H+2) (y+2) * gg (H+3) (H-1-y) ≤
      (1/2 : ℚ) * (rup (H+1) (y+1) * gg (H+2) (H-1-y)) := by
  have hg := gg_shift (H+2) (H-1-y)
  have hg' : gg (H+3) (H-1-y) ≤
      ((H+6 : ℚ)/(2*H+5-y))*gg (H+2) (H-1-y) := by
    have hc : ((H-1-y : ℕ) : ℚ) = (H:ℚ)-1-y := by
      rw [show H-1-y = H-(y+1) by omega, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hc] at hg
    convert hg using 1 <;> push_cast <;> ring
  by_cases hy0 : y = 0
  · subst y
    have hr : rup (H+2) 2 / rup (H+1) 1 =
        (H+2 : ℚ)/((H+3)*(H+4)) := by
      norm_num [rup]
      field_simp
      ring
    have hr' : rup (H+2) 2 ≤
        ((H+2 : ℚ)/((H+3)*(H+4))) * rup (H+1) 1 := by
      rw [div_eq_iff (ne_of_gt (rup_pos (H+1) 1))] at hr
      simpa [mul_comm] using hr.le
    calc
      _ ≤ (H+1 : ℚ) *
          (((H+2 : ℚ)/((H+3)*(H+4))) * rup (H+1) 1) *
          (((H+6 : ℚ)/(2*H+5))*gg (H+2) (H-1)) := by
        simp at hg'
        have hcp : (0:ℚ) ≤ (H+1) * ((H+2)/((H+3)*(H+4))*rup (H+1) 1) :=
          mul_nonneg (by positivity) (mul_nonneg (by positivity) (rup_pos _ _).le)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hr' (by positivity)) hg'
          (gg_pos _ _).le hcp
      _ = (((H+1 : ℚ)*(H+2)*(H+6))/
          ((H+3)*(H+4)*(2*H+5))) *
          (rup (H+1) 1*gg (H+2) (H-1)) := by field_simp <;> ring
      _ ≤ (1/2 : ℚ)*(rup (H+1) 1*gg (H+2) (H-1)) := by
        apply mul_le_mul_of_nonneg_right
        · field_simp
          nlinarith
        · exact mul_nonneg (rup_pos _ _).le (gg_pos _ _).le
  · have hy1 : 1 ≤ y := by omega
    have hr := rup_diag_frac (H+1) (y+1) (by omega)
    have hr' : rup (H+2) (y+2) ≤
        ((H+2 : ℚ)/((H+5)*(H+y+3))) * rup (H+1) (y+1) := by
      rw [div_le_iff₀ (rup_pos (H+1) (y+1))] at hr
      have heq : ((↑(H+1)+1 : ℚ)/
          ((↑(H+1)+4)*(↑(H+1)+↑(y+1)+1))) =
          (↑H+2)/((↑H+5)*(↑H+↑y+3)) := by push_cast; ring
      rw [heq] at hr
      rw [show H+1+1=H+2 by omega, show y+1+1=y+2 by omega] at hr
      simpa [mul_comm] using hr
    calc
      _ ≤ (H+1 : ℚ) *
          (((H+2 : ℚ)/((H+5)*(H+y+3))) * rup (H+1) (y+1)) *
          (((H+6 : ℚ)/(2*H+5-y))*gg (H+2) (H-1-y)) := by
        have hcp : (0:ℚ) ≤ (H+1) *
            ((H+2)/((H+5)*(H+y+3))*rup (H+1) (y+1)) :=
          mul_nonneg (by positivity) (mul_nonneg (by positivity) (rup_pos _ _).le)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hr' (by positivity)) hg'
          (gg_pos _ _).le hcp
      _ = (((H+1 : ℚ)*(H+2)*(H+6))/
          ((H+5)*(H+y+3)*(2*H+5-y))) *
          (rup (H+1) (y+1)*gg (H+2) (H-1-y)) := by field_simp <;> ring
      _ ≤ (1/2 : ℚ)*(rup (H+1) (y+1)*gg (H+2) (H-1-y)) := by
        apply mul_le_mul_of_nonneg_right
        · have hyq : (1:ℚ) ≤ (y:ℚ) := by exact_mod_cast hy1
          have hyH0 : (y:ℚ) ≤ (H:ℚ)-1 := by
            have hh : (y:ℚ)+1 ≤ (H:ℚ) := by
              exact_mod_cast (show y+1 ≤ H by omega)
            linarith
          have hden : (0:ℚ) < ((H:ℚ)+5)*(H+y+3)*(2*H+5-y) := by
            have : (0:ℚ) < 2*H+5-y := by nlinarith
            positivity
          apply (div_le_iff₀ hden).2
          have hprod : ((H:ℚ)+4)*(2*H+4) ≤
              ((H:ℚ)+y+3)*(2*H+5-y) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hyq) (sub_nonneg.mpr hyH0)]
          have hm := mul_le_mul_of_nonneg_left hprod (show (0:ℚ) ≤ H+5 by positivity)
          have hd : 2*((H:ℚ)+1)*(H+2)*(H+6) ≤
              (H+5)*(H+4)*(2*H+4) := by
            have hp : (0:ℚ) ≤ 4*(H+2)*(H+7) := by positivity
            nlinarith [show (H+5)*(H+4)*(2*H+4) -
                2*((H:ℚ)+1)*(H+2)*(H+6) = 4*(H+2)*(H+7) by ring]
          have hm' : ((H:ℚ)+5)*(H+4)*(2*H+4) ≤
              (H+5)*(H+y+3)*(2*H+5-y) := by
            simpa only [mul_assoc] using hm
          nlinarith
        · exact mul_nonneg (rup_pos _ _).le (gg_pos _ _).le

lemma terminal_bound (H : ℕ) (hH : 14 ≤ H) :
    (H+1 : ℚ) * rup (H+3) (H+1) ≤
      (1/2 : ℚ) * rup (H+2) H := by
  have hr := rup_diag_frac (H+2) H (by omega)
  rw [div_le_iff₀ (rup_pos (H+2) H)] at hr
  calc
    _ ≤ (H+1 : ℚ) *
        (((H+3 : ℚ)/((H+6)*(2*H+3))) * rup (H+2) H) := by
      gcongr
      convert hr using 1 <;> push_cast <;> ring
    _ = (((H+1 : ℚ)*(H+3))/((H+6)*(2*H+3))) * rup (H+2) H := by
      field_simp <;> ring
    _ ≤ (1/2 : ℚ)*rup (H+2) H := by
      apply mul_le_mul_of_nonneg_right
      · field_simp
        nlinarith
      · exact (rup_pos _ _).le

lemma gg_geometric (H : ℕ) (hH : 14 ≤ H) :
    (H+1 : ℚ) * gg (H+2) (H+1) ≤ (4/5 : ℚ) * gg (H+1) H := by
  let oldS : ℚ := ∑ y ∈ range H,
    rup (H+1) (y+1) * gg (H+2) (H-1-y)
  let newS : ℚ := ∑ y ∈ range H,
    rup (H+2) (y+2) * gg (H+3) (H-1-y)
  have hsum : (H+1 : ℚ) * newS ≤ (1/2 : ℚ) * oldS := by
    dsimp [newS, oldS]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    simp only [mem_range] at hy
    simpa [mul_assoc] using increment_bound H y hH hy
  have hterm := terminal_bound H hH
  have hrem : (H+1 : ℚ) * (rup (H+3) (H+1) + newS) ≤
      (1/2 : ℚ) * (rup (H+2) H + oldS) := by
    calc
      _ = (H+1 : ℚ)*rup (H+3) (H+1) + (H+1)*newS := by ring
      _ ≤ (1/2 : ℚ)*rup (H+2) H + (1/2)*oldS := add_le_add hterm hsum
      _ = _ := by ring
  have hpre := prepend_bound H hH
  have hdecompNew : gg (H+2) (H+1) =
      rup (H+3) (H+1) + newS + rup (H+2) 1 * gg (H+3) H := by
    rw [gg]
    rw [Finset.sum_range_succ']
    have hs : (∑ y ∈ range H,
        rup (H+2) (y+1+1) * gg (H+3) (H-(y+1))) = newS := by
      dsimp [newS]
      apply Finset.sum_congr rfl
      intro y hy
      congr 2 <;> omega
    rw [hs]
    norm_num [Nat.add_assoc]
    ring
  have hdecompOld : gg (H+1) H = rup (H+2) H + oldS := by
    rw [show H=(H-1)+1 by omega, gg]
    dsimp [oldS]
    congr 1
    apply Finset.sum_congr (by congr; omega)
    intro y hy
    congr 2 <;> omega
  rw [hdecompNew]
  calc
    (H+1 : ℚ) * (rup (H+3) (H+1) + newS +
        rup (H+2) 1 * gg (H+3) H) =
      (H+1)*(rup (H+3) (H+1)+newS) +
        (H+1)*rup (H+2) 1*gg (H+3) H := by ring
    _ ≤ (1/2 : ℚ)*(rup (H+2) H+oldS) +
        (3/10 : ℚ)*gg (H+1) H := add_le_add hrem hpre
    _ = (4/5 : ℚ)*gg (H+1) H := by rw [hdecompOld]; ring

lemma CB_geometric (H : ℕ) (hH : 14 ≤ H) :
    CB (H+1) ≤ (4/5 : ℚ) * CB H := by
  unfold CB
  rw [Nat.factorial_succ]
  push_cast
  have hg := gg_geometric H hH
  calc
    ((H:ℚ)+1) * H.factorial * gg (H+2) (H+1) =
        (H.factorial : ℚ) * ((H+1)*gg (H+2) (H+1)) := by ring
    _ ≤ (H.factorial : ℚ) * ((4/5 : ℚ)*gg (H+1) H) := by gcongr
    _ = (4/5 : ℚ) * ((H.factorial : ℚ)*gg (H+1) H) := by ring

namespace Dev
lemma down_le {m e : ℕ} (d : Dev m (e+1)) (i : Fin m) :
    (down d).val i ≤ d.val i := by
  simp only [down]
  split <;> omega
lemma firstPos_le_of_pos {m e : ℕ} (d : Dev m (e+1)) (i : Fin m)
    (hi : 0 < d.val i) : firstPos d ≤ i := by
  apply Finset.min'_le
  simp [posSet, hi]
lemma down_eq_of_pos_before {m e : ℕ} (d : Dev m (e+1)) (j i : Fin m)
    (hj : 0 < d.val j) (hji : j < i) : (down d).val i = d.val i := by
  have hf := firstPos_le_of_pos d j hj
  simp only [down]
  rw [if_neg]
  intro he
  subst i
  exact (not_lt_of_ge hf) hji
lemma downN_le {m H r : ℕ} (d : Dev m (H+r)) (i : Fin m) :
    (downN H r d).val i ≤ d.val i := by
  induction H with
  | zero => rfl
  | succ H ih =>
    rw [downN]
    exact le_trans (ih _) (down_le (reindex (by omega) d) i)
lemma downN_eq_after_pos {m H r : ℕ} (d : Dev m (H+r))
    (j i : Fin m) (hj : 0 < (downN H r d).val j) (hji : j < i) :
    (downN H r d).val i = d.val i := by
  induction H with
  | zero => rfl
  | succ H ih =>
    rw [downN] at hj ⊢
    let d' : Dev m (H+r) := down (e := H+r) (reindex (by omega) d)
    have hmid : (downN H r d').val i = d'.val i := ih d' (by simpa [d'] using hj)
    rw [show (downN H r (down (e := H+r) (reindex (by omega) d))).val i = d'.val i by
      simpa [d'] using hmid]
    have hj' : 0 < d'.val j := lt_of_lt_of_le (by simpa [d'] using hj) (downN_le d' j)
    exact down_eq_of_pos_before (reindex (by omega) d) j i
      (lt_of_lt_of_le hj' (down_le (reindex (by omega) d) j)) hji
lemma sum_sub_downN {m H r : ℕ} (d : Dev m (H+r)) :
    ∑ i : Fin m, (d.val i - (downN H r d).val i) = H := by
  have hle := downN_le d
  have hs : ∑ i : Fin m, (d.val i - (downN H r d).val i) =
      (∑ i : Fin m, d.val i) - ∑ i : Fin m, (downN H r d).val i := by
    rw [Finset.sum_tsub_distrib _ (fun i hi => hle i)]
  rw [hs, d.sum_eq, (downN H r d).sum_eq]
  omega
end Dev
namespace Dev

noncomputable def natVal {m e : ℕ} (d : Dev m e) (j : ℕ) : ℕ :=
  if h : j < m then d.val ⟨j, h⟩ else 0

lemma natVal_of_lt {m e : ℕ} (d : Dev m e) {j : ℕ} (hj : j < m) :
    natVal d j = d.val ⟨j, hj⟩ := by
  simp [natVal, hj]

noncomputable def allVals {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) : List ℕ :=
  List.ofFn fun j : Fin (cut p) => natVal e j.val

noncomputable def fullVals {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) : List ℕ :=
  (allVals p e).filter (0 < ·)

lemma mem_fullVals_pos {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r))
    {x : ℕ} (hx : x ∈ fullVals p e) : 0 < x := by
  have hh := (List.mem_filter.mp hx).2
  simpa using hh

lemma list_sum_filter_pos (L : List ℕ) : (L.filter (0 < ·)).sum = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : 0 < a
    · simp [ha, ih]
    · have : a = 0 := by omega
      simp [this, ih]

lemma fullVals_sum {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    (fullVals p e).sum = ∑ j ∈ range (cut p), natVal e j := by
  rw [fullVals, list_sum_filter_pos]
  unfold allVals
  rw [List.sum_ofFn]
  rw [Fin.sum_univ_eq_sum_range]

noncomputable def part {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) : ℕ :=
  if h : cut p < m then natVal e (cut p) - natVal p (cut p) else 0

lemma fullVals_sum_add_part {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) : (fullVals p e).sum + part p e = H := by
  have hsub := sum_sub_downN e
  rw [heq] at hsub
  have hsub' : ∑ j ∈ range m, (natVal e j - natVal p j) = H := by
    calc
      _ = ∑ i : Fin m, (natVal e i.val - natVal p i.val) :=
        (Fin.sum_univ_eq_sum_range (fun j => natVal e j - natVal p j) m).symm
      _ = ∑ i : Fin m, (e.val i - p.val i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [natVal, i.isLt]
      _ = H := hsub
  rw [fullVals_sum]
  let f : ℕ → ℕ := fun j => natVal e j - natVal p j
  have hz : (∑ j ∈ range (cut p), natVal e j) = ∑ j ∈ range (cut p), f j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mem_range] at hj
    have hmj : j < m := lt_of_lt_of_le hj (cut_le p)
    have hpz := val_zero_before_cut p ⟨j, hmj⟩ hj
    simp [f, natVal_of_lt e hmj, natVal_of_lt p hmj, hpz]
  rw [hz]
  have htail : ∑ j ∈ Ico (cut p) m, f j = part p e := by
    by_cases hc : cut p < m
    · have hpos := val_pos_at_cut p hc
      have hafter (j : ℕ) (hj : j ∈ Ico (cut p + 1) m) : f j = 0 := by
        simp only [mem_Ico] at hj
        have he := downN_eq_after_pos e ⟨cut p, hc⟩ ⟨j, by omega⟩
          (by simpa [heq] using hpos) (by simp; omega)
        have hev := congrArg (fun d : Dev m r => d.val ⟨j, by omega⟩) heq
        have hpEq : p.val ⟨j, by omega⟩ = e.val ⟨j, by omega⟩ := by
          calc
            _ = (downN H r e).val ⟨j, by omega⟩ := by simpa using hev.symm
            _ = _ := by simpa using he
        simp [f, natVal_of_lt e (show j < m by omega),
          natVal_of_lt p (show j < m by omega), hpEq]
      have hs : ∑ j ∈ Ico (cut p + 1) m, f j = 0 := by
        apply Finset.sum_eq_zero
        exact hafter
      rw [← Finset.sum_Ico_consecutive f (Nat.le_succ _) (by omega)]
      rw [show ∑ j ∈ Ico (cut p) (cut p+1), f j = f (cut p) by simp]
      rw [hs, add_zero]
      simp [part, hc, f]
    · have hcm : cut p = m := by have := cut_le p; omega
      simp [hcm, part, hc]
  have hall := Finset.sum_range_add_sum_Ico f (cut_le p)
  rw [htail] at hall
  calc
    _ = ∑ j ∈ range m, f j := hall
    _ = H := by simpa [f] using hsub'

end Dev

lemma monotoneList_eq_zeros_filter (L : List ℕ) (hL : L.Pairwise (· ≤ ·)) :
    L = List.replicate (L.length - (L.filter (0 < ·)).length) 0 ++ L.filter (0 < ·) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : 0 < a
    · have htail : L.filter (0 < ·) = L := by
        apply List.filter_eq_self.mpr
        intro x hx
        have := hL.1 x hx
        simp
        omega
      simp [ha, htail]
    · have ha0 : a = 0 := by omega
      subst a
      have hi := ih hL.2
      simp only [List.filter_cons]
      norm_num
      have hlen := List.length_filter_le (0 < ·) L
      rw [show L.length + 1 - (L.filter (0 < ·)).length =
          (L.length - (L.filter (0 < ·)).length) + 1 by omega]
      rw [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons 0) hi

lemma eq_of_pairwise_filter_eq {L K : List ℕ} (hL : L.Pairwise (· ≤ ·))
    (hK : K.Pairwise (· ≤ ·)) (hlen : L.length = K.length)
    (hf : L.filter (0 < ·) = K.filter (0 < ·)) : L = K := by
  rw [monotoneList_eq_zeros_filter L hL, monotoneList_eq_zeros_filter K hK]
  rw [hlen, hf]

namespace Dev

lemma allVals_pairwise {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    (allVals p e).Pairwise (· ≤ ·) := by
  unfold allVals
  rw [List.pairwise_ofFn]
  intro i j hij
  have hi : i.val < m := lt_of_lt_of_le i.isLt (cut_le p)
  have hj : j.val < m := lt_of_lt_of_le j.isLt (cut_le p)
  rw [natVal_of_lt e hi, natVal_of_lt e hj]
  exact e.mono (by simpa using hij.le)

noncomputable def code {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) : Composition (H+1) where
  blocks := fullVals p e ++ [part p e + 1]
  blocks_pos := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact mem_fullVals_pos p e hx
    · simp at hx
      omega
  blocks_sum := by
    rw [List.sum_append]
    simp
    have hs := fullVals_sum_add_part p e heq
    omega

lemma code_injective {m r H : ℕ} (p : Dev m r)
    {e e' : Dev m (H+r)} (he : downN H r e = p) (he' : downN H r e' = p)
    (hc : code p e he = code p e' he') : e = e' := by
  have hb := congrArg Composition.blocks hc
  dsimp [code] at hb
  have hb' : (fullVals p e).concat (part p e+1) =
      (fullVals p e').concat (part p e'+1) := by
    simpa only [List.concat_eq_append] using hb
  have hcj := List.concat_inj.mp hb' 
  have hfull : fullVals p e = fullVals p e' := hcj.1
  have hpart : part p e = part p e' := by omega
  have hall : allVals p e = allVals p e' := by
    apply eq_of_pairwise_filter_eq (allVals_pairwise p e) (allVals_pairwise p e')
    · simp [allVals]
    · exact hfull
  apply Dev.ext
  funext i
  by_cases hi : i.val < cut p
  · have hf := List.ofFn_injective hall
    have hv := congrFun hf ⟨i.val, hi⟩
    have him : i.val < m := lt_of_lt_of_le hi (cut_le p)
    simpa [allVals, natVal_of_lt e him, natVal_of_lt e' him] using hv
  · by_cases hc0 : cut p < m
    · by_cases hieq : i.val = cut p
      · have hle : p.val i ≤ e.val i := by
          have hh := downN_le e i
          simpa [he] using hh
        have hle' : p.val i ≤ e'.val i := by
          have hh := downN_le e' i
          simpa [he'] using hh
        have hne : natVal e (cut p) = e.val i := by
          rw [natVal_of_lt e hc0]
          congr 1
          exact Fin.ext hieq.symm
        have hne' : natVal e' (cut p) = e'.val i := by
          rw [natVal_of_lt e' hc0]
          congr 1
          exact Fin.ext hieq.symm
        have hnp : natVal p (cut p) = p.val i := by
          rw [natVal_of_lt p hc0]
          congr 1
          exact Fin.ext hieq.symm
        have hpform : part p e = e.val i - p.val i := by
          rw [part, dif_pos hc0, hne, hnp]
        have hpform' : part p e' = e'.val i - p.val i := by
          rw [part, dif_pos hc0, hne', hnp]
        omega
      · have hgt : (⟨cut p, hc0⟩ : Fin m) < i := by
          exact (show cut p < i.val by omega)
        have hpos := val_pos_at_cut p hc0
        have hx := downN_eq_after_pos e ⟨cut p, hc0⟩ i (by simpa [he] using hpos) hgt
        have hx' := downN_eq_after_pos e' ⟨cut p, hc0⟩ i (by simpa [he'] using hpos) hgt
        rw [he] at hx
        rw [he'] at hx'
        omega
    · have hcm : cut p = m := by have := cut_le p; omega
      omega

end Dev

structure Pattern where
  blocks : List ℕ
  blocks_pos : ∀ x ∈ blocks, 0 < x
  endpoint : ℕ

namespace Pattern

def total (c : Pattern) : ℕ := c.blocks.sum + c.endpoint

def weightAux : ℕ → List ℕ → ℕ → ℚ
  | A, [], t => rup (A+1) t
  | A, x::xs, t => rup A x * weightAux (A+1) xs t

def weight (A : ℕ) (c : Pattern) : ℚ := weightAux A c.blocks c.endpoint

lemma weight_pos (A : ℕ) (c : Pattern) : 0 < c.weight A := by
  unfold weight
  induction c.blocks generalizing A with
  | nil => simp [weightAux, rup_pos]
  | cons x xs ih =>
    simp only [weightAux]
    exact mul_pos (rup_pos _ _) (ih (A+1))

def head (c : Pattern) : ℕ := c.blocks.head?.getD 0

def tail (c : Pattern) : Pattern where
  blocks := c.blocks.tail
  blocks_pos := by
    intro x hx
    exact c.blocks_pos x (List.mem_of_mem_tail hx)
  endpoint := c.endpoint

lemma head_eq_zero_iff (c : Pattern) : c.head = 0 ↔ c.blocks = [] := by
  cases c with
  | mk blocks hp t =>
    cases blocks with
    | nil => simp [head]
    | cons x xs =>
      simp [head]
      exact Nat.ne_of_gt (hp x (by simp))

lemma total_tail (c : Pattern) (hc : c.blocks ≠ []) :
    c.tail.total = c.total - c.head := by
  cases c with
  | mk blocks hp t =>
    cases blocks with
    | nil => contradiction
    | cons x xs => simp [tail, total, head]; omega

lemma head_le_total (c : Pattern) : c.head ≤ c.total := by
  cases c with
  | mk blocks hp t =>
    cases blocks with
    | nil => simp [head, total]
    | cons x xs => simp [head, total]; omega

lemma weight_empty (c : Pattern) (hc : c.blocks = []) :
    c.weight A = rup (A+1) c.endpoint := by
  simp [weight, hc, weightAux]

lemma weight_cons (c : Pattern) (hc : c.blocks ≠ []) :
    c.weight A = rup A c.head * c.tail.weight (A+1) := by
  cases c with
  | mk blocks hp t =>
    cases blocks with
    | nil => contradiction
    | cons x xs => simp [weight, weightAux, head, tail]

lemma ext_of_head_tail {c d : Pattern} (hc : c.blocks ≠ []) (hd : d.blocks ≠ [])
    (hh : c.head = d.head) (ht : c.tail = d.tail) : c = d := by
  cases c with
  | mk cb cp ce =>
    cases d with
    | mk db dp de =>
      cases cb with
      | nil => contradiction
      | cons x xs =>
        cases db with
        | nil => contradiction
        | cons y ys =>
          simp [head, tail] at hh ht
          subst y
          rcases ht with ⟨rfl, rfl⟩
          congr

end Pattern

namespace Dev

noncomputable def pattern {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) : Pattern where
  blocks := fullVals p e
  blocks_pos := fun x hx => mem_fullVals_pos p e hx
  endpoint := part p e

lemma pattern_total {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (he : downN H r e = p) : (pattern p e).total = H := by
  exact fullVals_sum_add_part p e he

lemma pattern_injective {m r H : ℕ} (p : Dev m r)
    {e e' : Dev m (H+r)} (he : downN H r e = p) (he' : downN H r e' = p)
    (hc : pattern p e = pattern p e') : e = e' := by
  apply code_injective p he he'
  apply Composition.ext
  simpa [code, pattern] using congrArg (fun q : Pattern => q.blocks ++ [q.endpoint+1]) hc

end Dev

lemma gg_unified (A H : ℕ) : gg A H = rup (A+1) H +
    ∑ y ∈ range H, rup A (y+1) * gg (A+1) (H-1-y) := by
  cases H with
  | zero => simp [gg, rup]
  | succ H =>
    rw [gg]
    congr 1 <;> omega

namespace Pattern

lemma eq_of_empty_total {c d : Pattern} (hc : c.blocks = []) (hd : d.blocks = [])
    (ht : c.total = d.total) : c = d := by
  cases c with
  | mk cb cp ce =>
    cases d with
    | mk db dp de =>
      simp only at hc hd
      subst cb
      subst db
      simp [total] at ht
      subst de
      congr

/-- An injective family of patterns of total `H` has total weight bounded by `gg`. -/
lemma sum_weight_le_gg {E : Type*} [Fintype E] (S : Finset E)
    (c : E → Pattern) (w : E → ℚ) (A H : ℕ)
    (hinj : Set.InjOn c S) (htotal : ∀ e ∈ S, (c e).total = H)
    (hw0 : ∀ e ∈ S, 0 ≤ w e) (hw : ∀ e ∈ S, w e ≤ (c e).weight A) :
    ∑ e ∈ S, w e ≤ gg A H := by
  induction H using Nat.strong_induction_on generalizing E A S c w with
  | h H ih =>
    let tag : E → ℕ := fun e => (c e).head
    have htag : ∀ e ∈ S, tag e ∈ range (H+1) := by
      intro e he
      simp only [mem_range, tag]
      have hh := head_le_total (c e)
      rw [htotal e he] at hh
      omega
    rw [← Finset.sum_fiberwise_of_maps_to htag w]
    let B : ℕ → ℚ := fun x => if x = 0 then rup (A+1) H else
      rup A x * gg (A+1) (H-x)
    have hfiber (x : ℕ) (hx : x ∈ range (H+1)) :
        (∑ e ∈ S with tag e = x, w e) ≤ B x := by
      by_cases hx0 : x = 0
      · subst x
        simp only [B, if_pos]
        let S0 := S.filter fun e => tag e = 0
        change (∑ e ∈ S0, w e) ≤ rup (A+1) H
        by_cases hne : S0.Nonempty
        · rcases hne with ⟨e0, he0⟩
          have he0S : e0 ∈ S := (mem_filter.mp he0).1
          have he0t : tag e0 = 0 := (mem_filter.mp he0).2
          have hS0 : S0 = {e0} := by
            ext e
            constructor
            · intro he
              have heS := (mem_filter.mp he).1
              have het := (mem_filter.mp he).2
              have hc0 := (head_eq_zero_iff (c e0)).mp he0t
              have hc := (head_eq_zero_iff (c e)).mp het
              have hce : c e = c e0 := eq_of_empty_total hc hc0 (by
                rw [htotal e heS, htotal e0 he0S])
              have := hinj heS he0S hce
              simpa [this]
            · intro he
              simp only [mem_singleton] at he
              subst e
              exact he0
          rw [hS0]
          simp only [sum_singleton]
          calc
            w e0 ≤ (c e0).weight A := hw e0 he0S
            _ = rup (A+1) H := by
              rw [weight_empty (c e0) ((head_eq_zero_iff _).mp he0t)]
              have ht := htotal e0 he0S
              simp [total, (head_eq_zero_iff _).mp he0t] at ht
              rw [ht]
        · rw [not_nonempty_iff_eq_empty.mp hne]
          simp
          exact (rup_pos _ _).le
      · have hxpos : 0 < x := by omega
        have hxH : x ≤ H := by
          simp only [mem_range] at hx
          omega
        simp only [B, if_neg hx0]
        let Sx := S.filter fun e => tag e = x
        let ct : E → Pattern := fun e => (c e).tail
        let w' : E → ℚ := fun e => w e / rup A x
        have htot' : ∀ e ∈ Sx, (ct e).total = H-x := by
          intro e he
          have heS := (mem_filter.mp he).1
          have het := (mem_filter.mp he).2
          have hne : (c e).blocks ≠ [] := by
            intro hb
            have := (head_eq_zero_iff (c e)).mpr hb
            simp [tag, this] at het
            omega
          dsimp [ct]
          rw [total_tail (c e) hne, htotal e heS]
          have hh : (c e).head = x := by exact het
          rw [hh]
        have hinj' : Set.InjOn ct Sx := by
          intro e he d hd hed
          have heS := (mem_filter.mp he).1
          have hdS := (mem_filter.mp hd).1
          have het := (mem_filter.mp he).2
          have hdt := (mem_filter.mp hd).2
          have hne : (c e).blocks ≠ [] := by
            intro hb
            have := (head_eq_zero_iff (c e)).mpr hb
            simp [tag, this] at het
            omega
          have hnd : (c d).blocks ≠ [] := by
            intro hb
            have := (head_eq_zero_iff (c d)).mpr hb
            simp [tag, this] at hdt
            omega
          apply hinj heS hdS
          apply ext_of_head_tail hne hnd
          · simpa [tag] using het.trans hdt.symm
          · exact hed
        have hw0' : ∀ e ∈ Sx, 0 ≤ w' e := by
          intro e he
          exact div_nonneg (hw0 e (mem_filter.mp he).1) (rup_pos _ _).le
        have hw' : ∀ e ∈ Sx, w' e ≤ (ct e).weight (A+1) := by
          intro e he
          have heS := (mem_filter.mp he).1
          have het := (mem_filter.mp he).2
          have hne : (c e).blocks ≠ [] := by
            intro hb
            have hz := (head_eq_zero_iff (c e)).mpr hb
            simp [tag, hz] at het
            omega
          have hh := hw e heS
          rw [weight_cons (c e) hne] at hh
          have hhead : (c e).head = x := by exact het
          rw [hhead] at hh
          dsimp [w', ct]
          exact (div_le_iff₀ (rup_pos A x)).2 (by simpa [mul_comm] using hh)
        have hrec := ih (H-x) (by omega) Sx ct w' (A+1) hinj' htot' hw0' hw'
        have hsum : (∑ e ∈ Sx, w e) = rup A x * ∑ e ∈ Sx, w' e := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          dsimp [w']
          exact (mul_div_cancel₀ (w e) (ne_of_gt (rup_pos A x))).symm
        change (∑ e ∈ Sx, w e) ≤ rup A x * gg (A+1) (H-x)
        rw [hsum]
        exact mul_le_mul_of_nonneg_left hrec (rup_pos _ _).le
    calc
      (∑ x ∈ range (H+1), ∑ e ∈ S with tag e = x, w e) ≤
          ∑ x ∈ range (H+1), B x := by
        apply Finset.sum_le_sum
        exact hfiber
      _ = gg A H := by
        rw [Finset.sum_range_succ']
        rw [gg_unified]
        dsimp [B]
        have hs : (∑ y ∈ range H,
            rup A (y+1)*gg (A+1) (H-(y+1))) =
            ∑ y ∈ range H, rup A (y+1)*gg (A+1) (H-1-y) := by
          apply Finset.sum_congr rfl
          intro y hy
          simp only [mem_range] at hy
          congr 2 <;> omega
        rw [hs]
        ring

end Pattern

def rden (a x : ℕ) : ℕ :=
  if x = 0 then 1 else if x = 1 then a+1 else (a+1)*(a+2)*(a+3)^(x-2)

lemma rup_eq_inv_rden (a x : ℕ) : rup a x = 1 / (rden a x : ℚ) := by
  unfold rup rden
  split_ifs <;> push_cast <;> field_simp <;> ring

lemma rden_succ (a x : ℕ) (hx : 2 ≤ x) : rden a (x+1) = rden a x * (a+3) := by
  simp [rden, show x ≠ 0 by omega, show x ≠ 1 by omega,
    show x+1 ≠ 0 by omega, show x+1 ≠ 1 by omega]
  rw [show x-1=(x-2)+1 by omega, pow_succ]
  ring

lemma factorial_rden_le (a b x : ℕ) (hab : a ≤ b) :
    b.factorial * rden a x ≤ (b+x).factorial := by
  induction x using Nat.twoStepInduction with
  | zero => simp [rden]
  | one =>
    simp [rden, Nat.factorial_succ]
    nlinarith
  | more x ih0 ih1 =>
    by_cases hx : x = 0
    · subst x
      simp [rden]
      rw [show b+2=(b+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      calc
        b.factorial * ((a+1)*(a+2)) ≤ b.factorial * ((b+1)*(b+2)) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
        _ = (b+2)*((b+1)*b.factorial) := by ring
    have hx2 : 2 ≤ x+1 := by omega
    rw [rden_succ a (x+1) hx2]
    rw [show b+(x+2)=(b+(x+1))+1 by omega, Nat.factorial_succ]
    rw [← Nat.mul_assoc]
    calc
      b.factorial * rden a (x+1) * (a+3) ≤
          (b+(x+1)).factorial * (a+3) := Nat.mul_le_mul_right _ ih1
      _ ≤ (b+(x+1)).factorial * (b+(x+1)+1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (b+(x+1)+1) * (b+(x+1)).factorial := Nat.mul_comm _ _

lemma factorial_ratio_le_rup (a b x : ℕ) (hab : a ≤ b) :
    (b.factorial : ℚ) / (b+x).factorial ≤ rup a x := by
  rw [rup_eq_inv_rden]
  have hfac := factorial_rden_le a b x hab
  have hb : (0:ℚ) < b.factorial := by positivity
  have hr : (0:ℚ) < rden a x := by
    simp [rden]
    split_ifs <;> positivity
  have hbx : (0:ℚ) < (b+x).factorial := by positivity
  apply (div_le_div_iff₀ hbx hr).2
  norm_num
  exact_mod_cast hfac

def facRatio (b x : ℕ) : ℚ := (b.factorial : ℚ) / (b+x).factorial

def coordProd : ℕ → List ℕ → ℚ
  | _, [] => 1
  | b, x::xs => facRatio b x * coordProd (b+1) xs

def blockProd : ℕ → List ℕ → ℚ
  | _, [] => 1
  | A, x::xs => rup A x * blockProd (A+1) xs

lemma facRatio_zero (b : ℕ) : facRatio b 0 = 1 := by
  norm_num [facRatio]
  positivity

lemma coordProd_replicate_zero (b n : ℕ) : coordProd b (List.replicate n 0) = 1 := by
  induction n generalizing b with
  | zero => simp [coordProd]
  | succ n ih =>
    rw [List.replicate_succ, coordProd, facRatio_zero, one_mul]
    exact ih (b+1)

lemma coordProd_append (b : ℕ) (L K : List ℕ) :
    coordProd b (L ++ K) = coordProd b L * coordProd (b+L.length) K := by
  induction L generalizing b with
  | nil => simp [coordProd]
  | cons x xs ih =>
    simp [coordProd, ih]
    ring

lemma coordProd_pos (b : ℕ) (L : List ℕ) : 0 < coordProd b L := by
  induction L generalizing b with
  | nil => simp [coordProd]
  | cons x xs ih =>
    simp only [coordProd]
    exact mul_pos (by unfold facRatio; positivity) (ih (b+1))

lemma blockProd_pos (A : ℕ) (L : List ℕ) : 0 < blockProd A L := by
  induction L generalizing A with
  | nil => simp [blockProd]
  | cons x xs ih =>
    simp only [blockProd]
    exact mul_pos (rup_pos _ _) (ih (A+1))

lemma coordProd_le_blockProd (A b : ℕ) (L : List ℕ) (hAb : A ≤ b) :
    coordProd b L ≤ blockProd A L := by
  induction L generalizing A b with
  | nil => simp [coordProd, blockProd]
  | cons x xs ih =>
    simp only [coordProd, blockProd]
    exact mul_le_mul (factorial_ratio_le_rup A b x hAb) (ih (A+1) (b+1) (by omega))
      (coordProd_pos _ _).le (rup_pos _ _).le

lemma blockProd_weightAux (A : ℕ) (xs : List ℕ) (t : ℕ) :
    Pattern.weightAux A xs t = blockProd A xs * rup (A+xs.length+1) t := by
  induction xs generalizing A with
  | nil => simp [Pattern.weightAux, blockProd]
  | cons x xs ih =>
    simp [Pattern.weightAux, blockProd, ih]
    ring

namespace Dev

lemma allVals_length {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    (allVals p e).length = cut p := by simp [allVals]

lemma fullVals_length_le {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    (fullVals p e).length ≤ cut p := by
  rw [← allVals_length p e]
  exact List.length_filter_le _ _

lemma allVals_representation {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    allVals p e = List.replicate ((allVals p e).length - (fullVals p e).length) 0 ++
      fullVals p e := by
  exact monotoneList_eq_zeros_filter _ (allVals_pairwise p e)

lemma first_fullVals_index_pos {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (hne : fullVals p e ≠ []) :
    let d := cut p - (fullVals p e).length
    d < cut p ∧ 0 < natVal e d := by
  intro d
  have hlen := fullVals_length_le p e
  have hfp : 0 < (fullVals p e).length := by
    by_contra h
    have : (fullVals p e).length = 0 := by omega
    exact hne (List.eq_nil_of_length_eq_zero this)
  have hd : d < cut p := by dsimp [d]; omega
  have hrep := allVals_representation p e
  have halllen := allVals_length p e
  have hidx : d < (allVals p e).length := by omega
  have hget : (allVals p e)[d] = (fullVals p e)[0] := by
    have hdEq : (allVals p e).length - (fullVals p e).length = d := by
      dsimp [d]
      rw [halllen]
    have hgetq : (allVals p e)[d]? = (fullVals p e)[0]? := by
      rw [hrep, hdEq, List.getElem?_append_right (by simp)]
      simp
    rw [List.getElem?_eq_getElem hidx,
      List.getElem?_eq_getElem (show 0 < (fullVals p e).length by omega)] at hgetq
    exact Option.some.inj hgetq
  have hleft : (allVals p e)[d] = natVal e d := by
    unfold allVals
    exact List.getElem_ofFn hidx
  have hright : 0 < (fullVals p e)[0] := by
    apply mem_fullVals_pos p e
    exact List.getElem_mem (by omega)
  rw [hleft] at hget
  exact ⟨hd, by omega⟩

lemma zeros_count_bound {m r H q : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p)
    (hz : ∀ i : Fin m, i.val ≤ q → e.val i = 0)
    (hactive : fullVals p e ≠ [] ∨ cut p < m) :
    q+1 ≤ cut p - (fullVals p e).length := by
  let d := cut p - (fullVals p e).length
  by_cases hf : fullVals p e ≠ []
  · have hd := first_fullVals_index_pos p e hf
    dsimp only at hd
    by_contra h
    have hdm : cut p - (fullVals p e).length < m :=
      lt_of_lt_of_le hd.1 (cut_le p)
    have hdq : cut p - (fullVals p e).length ≤ q := by omega
    let j : Fin m := ⟨cut p - (fullVals p e).length, hdm⟩
    have hez := hz j (by simpa [j] using hdq)
    rw [natVal_of_lt e hdm] at hd
    change e.val j = _ at hez
    rw [hez] at hd
    omega
  · have hf0 : fullVals p e = [] := by simpa using hf
    have hflen : (fullVals p e).length = 0 := by simp [hf0]
    have hc : cut p < m := hactive.resolve_left hf
    have hp := val_pos_at_cut p hc
    have hle : p.val ⟨cut p, hc⟩ ≤ e.val ⟨cut p, hc⟩ := by
      have hh := downN_le e ⟨cut p, hc⟩
      simpa [heq] using hh
    rw [hflen]
    simp only [Nat.sub_zero]
    by_contra h
    have hq : cut p ≤ q := by omega
    have hez := hz ⟨cut p, hc⟩ hq
    omega

end Dev

lemma coordProd_ofFn (b n : ℕ) (f : Fin n → ℕ) :
    coordProd b (List.ofFn f) = ∏ i : Fin n, facRatio (b+i.val) (f i) := by
  induction n generalizing b with
  | zero => simp [List.ofFn_zero, coordProd]
  | succ n ih =>
    rw [List.ofFn_succ, coordProd, Fin.prod_univ_succ]
    rw [ih (b+1)]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

namespace Dev

lemma weight_factorization {m r H l : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) :
    e.weight l = p.weight l * ∏ i : Fin m,
      facRatio (l+i.val+p.val i) (e.val i-p.val i) := by
  unfold weight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hle : p.val i ≤ e.val i := by
    have hh := downN_le e i
    simpa [heq] using hh
  unfold facRatio
  have headd : p.val i + (e.val i-p.val i) = e.val i := by omega
  rw [show l+i.val+p.val i+(e.val i-p.val i) = l+i.val+e.val i by omega]
  field_simp

noncomputable def ratioAt {m r H : ℕ} (l : ℕ) (p : Dev m r) (e : Dev m (H+r))
    (j : ℕ) : ℚ :=
  facRatio (l+j+natVal p j) (natVal e j-natVal p j)

lemma coordProd_allVals {m r H l : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    coordProd l (allVals p e) = ∏ j ∈ range (cut p), facRatio (l+j) (natVal e j) := by
  unfold allVals
  rw [coordProd_ofFn]
  rw [Fin.prod_univ_eq_prod_range
    (fun j => facRatio (l+j) (natVal e j)) (cut p)]

lemma ratio_product_decomp {m r H l : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) :
    (∏ j ∈ range m, ratioAt l p e j) = coordProd l (allVals p e) *
      (if hc : cut p < m then
        facRatio (l+cut p+p.val ⟨cut p, hc⟩) (part p e) else 1) := by
  have hbefore : (∏ j ∈ range (cut p), ratioAt l p e j) =
      coordProd l (allVals p e) := by
    rw [coordProd_allVals]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [mem_range] at hj
    have hmj : j < m := lt_of_lt_of_le hj (cut_le p)
    have hpz := val_zero_before_cut p ⟨j, hmj⟩ hj
    simp [ratioAt, natVal_of_lt e hmj, natVal_of_lt p hmj, hpz]
  have htail : (∏ j ∈ Ico (cut p) m, ratioAt l p e j) =
      (if hc : cut p < m then
        facRatio (l+cut p+p.val ⟨cut p, hc⟩) (part p e) else 1) := by
    by_cases hc : cut p < m
    · have hpos := val_pos_at_cut p hc
      have hafter (j : ℕ) (hj : j ∈ Ico (cut p+1) m) : ratioAt l p e j = 1 := by
        simp only [mem_Ico] at hj
        have he := downN_eq_after_pos e ⟨cut p, hc⟩ ⟨j, by omega⟩
          (by simpa [heq] using hpos) (by exact (show cut p < j by omega))
        have hev := congrArg (fun d : Dev m r => d.val ⟨j, by omega⟩) heq
        have hep : e.val ⟨j, by omega⟩ = p.val ⟨j, by omega⟩ := by
          calc
            _ = (downN H r e).val ⟨j, by omega⟩ := by simpa using he.symm
            _ = _ := by simpa using hev
        simp [ratioAt, natVal_of_lt e (show j < m by omega),
          natVal_of_lt p (show j < m by omega), hep, facRatio_zero]
      have hs : ∏ j ∈ Ico (cut p+1) m, ratioAt l p e j = 1 := by
        apply Finset.prod_eq_one
        exact hafter
      rw [← Finset.prod_Ico_consecutive (ratioAt l p e) (Nat.le_succ _) (by omega)]
      rw [show ∏ j ∈ Ico (cut p) (cut p+1), ratioAt l p e j =
          ratioAt l p e (cut p) by simp]
      rw [hs, mul_one]
      simp only [dif_pos hc]
      have hpval : natVal p (cut p) = p.val ⟨cut p, hc⟩ := natVal_of_lt p hc
      have heval : natVal e (cut p) = e.val ⟨cut p, hc⟩ := natVal_of_lt e hc
      simp [ratioAt, part, hc, hpval, heval]
    · have hcm : cut p = m := by have := cut_le p; omega
      simp [hcm, hc]
  have hall := Finset.prod_range_mul_prod_Ico (ratioAt l p e) (cut_le p)
  rw [hbefore, htail] at hall
  exact hall.symm

lemma ratio_fin_eq_range {m r H l : ℕ} (p : Dev m r) (e : Dev m (H+r)) :
    (∏ i : Fin m, facRatio (l+i.val+p.val i) (e.val i-p.val i)) =
      ∏ j ∈ range m, ratioAt l p e j := by
  calc
    _ = ∏ i : Fin m, facRatio (l+i.val+natVal p i.val)
        (natVal e i.val-natVal p i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [natVal, i.isLt]
    _ = ∏ j ∈ range m, facRatio (l+j+natVal p j)
        (natVal e j-natVal p j) :=
      Fin.prod_univ_eq_prod_range
        (fun j => facRatio (l+j+natVal p j) (natVal e j-natVal p j)) m
    _ = _ := rfl

end Dev


namespace Dev

lemma coordProd_allVals_le {m r H l q : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) (hH : H = l+q)
    (hz : ∀ i : Fin m, i.val ≤ q → e.val i = 0) :
    coordProd l (allVals p e) ≤ blockProd (H+1) (fullVals p e) := by
  let d := cut p - (fullVals p e).length
  have hlen := fullVals_length_le p e
  have hdEq : (allVals p e).length - (fullVals p e).length = d := by
    dsimp [d]
    rw [allVals_length]
  have hrep := allVals_representation p e
  rw [hdEq] at hrep
  rw [hrep, coordProd_append, coordProd_replicate_zero, one_mul]
  simp only [List.length_replicate]
  by_cases hf : fullVals p e = []
  · simp [hf, blockProd, coordProd]
  · have hdb := zeros_count_bound p e heq hz (Or.inl hf)
    apply coordProd_le_blockProd
    dsimp [d] at hdb ⊢
    omega

lemma ratio_product_le_pattern {m r H l q : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) (hH : H = l+q)
    (hz : ∀ i : Fin m, i.val ≤ q → e.val i = 0) :
    (∏ i : Fin m, facRatio (l+i.val+p.val i) (e.val i-p.val i)) ≤
      (pattern p e).weight (H+1) := by
  rw [ratio_fin_eq_range, ratio_product_decomp p e heq]
  rw [Pattern.weight, blockProd_weightAux]
  dsimp [pattern]
  have hfull := coordProd_allVals_le p e heq hH hz
  by_cases hc : cut p < m
  · rw [dif_pos hc]
    have hdb := zeros_count_bound p e heq hz (Or.inr hc)
    have hp := val_pos_at_cut p hc
    have hab : H+1+(fullVals p e).length+1 ≤
        l+cut p+p.val ⟨cut p, hc⟩ := by
      omega
    have hend := factorial_ratio_le_rup (H+1+(fullVals p e).length+1)
      (l+cut p+p.val ⟨cut p, hc⟩) (part p e) hab
    exact mul_le_mul hfull hend (by unfold facRatio; positivity) (blockProd_pos _ _).le
  · rw [dif_neg hc]
    have hp0 : part p e = 0 := by simp [part, hc]
    rw [hp0]
    simp [rup, facRatio_zero]
    exact hfull

lemma weight_le_pattern {m r H l q : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (heq : downN H r e = p) (hH : H = l+q)
    (hz : ∀ i : Fin m, i.val ≤ q → e.val i = 0) :
    e.weight l ≤ (pattern p e).weight (H+1) * p.weight l := by
  rw [weight_factorization p e heq]
  have hr := ratio_product_le_pattern p e heq hH hz
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hr (weight_pos _ _).le

end Dev

namespace Dev

lemma restricted_fiber_bound (m r H l q : ℕ) (p : Dev m r) (hH : H = l+q) :
    (∑ e : Dev m (H+r),
      if downN H r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
      then e.weight l else 0) ≤ gg (H+1) H * p.weight l := by
  classical
  let S : Finset (Dev m (H+r)) := Finset.univ.filter fun e =>
    downN H r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
  let c : Dev m (H+r) → Pattern := fun e => pattern p e
  let w : Dev m (H+r) → ℚ := fun e => e.weight l / p.weight l
  have hinj : Set.InjOn c S := by
    intro e he e' he' hc
    have hef : e ∈ S := he
    have he'f : e' ∈ S := he'
    dsimp [S] at hef he'f
    have heq := (mem_filter.mp hef).2.1
    have heq' := (mem_filter.mp he'f).2.1
    exact pattern_injective p heq heq' hc
  have htotal : ∀ e ∈ S, (c e).total = H := by
    intro e he
    have hef := he
    dsimp [S] at hef
    exact pattern_total p e (mem_filter.mp hef).2.1
  have hw0 : ∀ e ∈ S, 0 ≤ w e := by
    intro e he
    exact div_nonneg (weight_pos _ _).le (weight_pos _ _).le
  have hw : ∀ e ∈ S, w e ≤ (c e).weight (H+1) := by
    intro e he
    have hef := he
    dsimp [S] at hef
    have hs := (mem_filter.mp hef).2
    have hh := weight_le_pattern p e hs.1 hH hs.2
    dsimp [w, c]
    exact (div_le_iff₀ (weight_pos l p)).2 (by simpa [mul_comm] using hh)
  have hsum := Pattern.sum_weight_le_gg S c w (H+1) H hinj htotal hw0 hw
  have hp := weight_pos l p
  have heqsum : (∑ e ∈ S, e.weight l) = p.weight l * ∑ e ∈ S, w e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    dsimp [w]
    exact (mul_div_cancel₀ (e.weight l) (ne_of_gt hp)).symm
  have hmain : (∑ e ∈ S, e.weight l) ≤ p.weight l * gg (H+1) H := by
    rw [heqsum]
    exact mul_le_mul_of_nonneg_left hsum hp.le
  rw [show (∑ e : Dev m (H+r),
      if downN H r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
      then e.weight l else 0) = ∑ e ∈ S, e.weight l by
    dsimp [S]
    rw [← Finset.sum_filter]]
  simpa [mul_comm] using hmain

lemma restricted_fiber_factorial_bound (m r H l q : ℕ) (p : Dev m r) (hH : H = l+q) :
    (∑ e : Dev m (H+r),
      if downN H r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
      then (H.factorial : ℚ) * e.weight l else 0) ≤ CB H * p.weight l := by
  classical
  have h := restricted_fiber_bound m r H l q p hH
  have hfac : (0:ℚ) ≤ H.factorial := by positivity
  have hh := mul_le_mul_of_nonneg_left h hfac
  have heqfac : (∑ e : Dev m (H+r),
      if downN H r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
      then (H.factorial : ℚ) * e.weight l else 0) =
      (H.factorial : ℚ) * (∑ e : Dev m (H+r),
      if downN H r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
      then e.weight l else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  rw [heqfac]
  unfold CB
  simpa [mul_assoc] using hh

end Dev
namespace Dev
lemma lift_zero_H (l m r q : ℕ) (hm : 1 < m) (d : Dev (m-1) (l+m-1+r))
    (hH : liftH l m r d = l+q) (i : Fin m) (hi : i.val ≤ q) :
    (lift l m r d).val i = 0 := by
  have hs := liftH_spec l m r hm d
  have hq : (firstAny d (by omega)).val = q := by omega
  rw [lift_val_eq l m r hm d i]
  rw [if_pos (by omega)]
end Dev

namespace Dev

noncomputable def srcQ (l m r : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) : ℕ := (firstAny d (by omega)).val

lemma srcQ_lt (l m r : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) : srcQ l m r hl hm d < m-1 :=
  (firstAny d (by omega)).isLt

lemma liftH_eq_srcQ (l m r : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) :
    liftH l m r d = l + srcQ l m r hl hm d := by
  rw [liftH_spec l m r hm]
  rfl

noncomputable def fixedLift (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) (hq : srcQ l m r hl hm d = q) :
    Dev m (l+q+r) where
  val := (lift l m r d).val
  mono := (lift l m r d).mono
  sum_eq := by
    rw [(lift l m r d).sum_eq, liftH_eq_srcQ l m r hl hm, hq]

lemma fixedLift_weight (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) (hq : srcQ l m r hl hm d = q) :
    (fixedLift l m r q hl hm d hq).weight l = (lift l m r d).weight l := by
  rfl

lemma fixedLift_zero (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) (hq : srcQ l m r hl hm d = q)
    (i : Fin m) (hi : i.val ≤ q) :
    (fixedLift l m r q hl hm d hq).val i = 0 := by
  apply lift_zero_H l m r q hm d
  · rw [liftH_eq_srcQ l m r hl hm, hq]
  · exact hi

lemma heq_dev_of_val {m e e' : ℕ} (d : Dev m e) (d' : Dev m e')
    (hee : e = e') (hv : d.val = d'.val) : HEq d d' := by
  subst e'
  exact (Dev.ext hv).heq

lemma fixedLift_injective (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    {d d' : Dev (m-1) (l+m-1+r)}
    (hq : srcQ l m r hl hm d = q) (hq' : srcQ l m r hl hm d' = q)
    (he : fixedLift l m r q hl hm d hq = fixedLift l m r q hl hm d' hq') : d = d' := by
  apply Dev.ext
  funext i
  change (firstAny d (by omega)).val = q at hq
  change (firstAny d' (by omega)).val = q at hq'
  by_cases hi : i.val < q
  · have hz := val_zero_before_firstAny d (by omega) i (by
      change i.val < (firstAny d (by omega)).val
      omega)
    have hz' := val_zero_before_firstAny d' (by omega) i (by
      change i.val < (firstAny d' (by omega)).val
      omega)
    omega
  · have hp := firstAny_pos d (by omega)
    have hp' := firstAny_pos d' (by omega)
    have hle : firstAny d (by omega) ≤ i := by
      apply Fin.mk_le_mk.mpr
      change (firstAny d (by omega)).val ≤ i.val
      omega
    have hle' : firstAny d' (by omega) ≤ i := by
      apply Fin.mk_le_mk.mpr
      change (firstAny d' (by omega)).val ≤ i.val
      omega
    have hdi : 0 < d.val i := lt_of_lt_of_le hp (d.mono hle)
    have hdi' : 0 < d'.val i := lt_of_lt_of_le hp' (d'.mono hle')
    let j : Fin m := ⟨i.val+1, by omega⟩
    have hv := congrArg (fun e : Dev m (l+q+r) => e.val j) he
    change (lift l m r d).val j = (lift l m r d').val j at hv
    rw [lift_val_eq l m r hm d j, lift_val_eq l m r hm d' j] at hv
    have hgt : ¬ j.val ≤ (firstAny d (by omega)).val := by
      change ¬ i.val + 1 ≤ (firstAny d (by omega)).val
      omega
    have hgt' : ¬ j.val ≤ (firstAny d' (by omega)).val := by
      change ¬ i.val + 1 ≤ (firstAny d' (by omega)).val
      omega
    rw [if_neg hgt, if_neg hgt'] at hv
    have hjval : j.val - 1 = i.val := by dsimp [j]
    have hv' : d.val i - 1 = d'.val i - 1 := by
      simpa only [hjval] using hv
    omega

end Dev

namespace Dev

noncomputable def canonical (m e : ℕ) (hm : 0 < m) : Dev m e where
  val i := if i.val = m-1 then e else 0
  mono := by
    cases m with
    | zero => omega
    | succ m =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      simp
      split_ifs <;> omega
  sum_eq := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i = m-1 then e else 0) m]
    rw [Finset.sum_eq_single (m-1)]
    · simp
    · intro b hb hne
      simp [hne]
    · simp
      omega

noncomputable def fixedLiftDefault (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) : Dev m (l+q+r) :=
  if hq : srcQ l m r hl hm d = q then fixedLift l m r q hl hm d hq
  else canonical m (l+q+r) (by omega)

lemma fixedLiftDefault_eq (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) (hq : srcQ l m r hl hm d = q) :
    fixedLiftDefault l m r q hl hm d = fixedLift l m r q hl hm d hq := by
  simp [fixedLiftDefault, hq]

lemma downN_val_eq_of {m H H' r : ℕ} (e : Dev m (H+r)) (e' : Dev m (H'+r))
    (hH : H = H') (hv : e.val = e'.val) :
    (downN H r e).val = (downN H' r e').val := by
  subst H'
  have he : e = e' := Dev.ext hv
  subst e'
  rfl
lemma fixedLift_downN (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (d : Dev (m-1) (l+m-1+r)) (hq : srcQ l m r hl hm d = q) :
    downN (l+q) r (fixedLift l m r q hl hm d hq) = nearMap l m r d := by
  apply Dev.ext
  apply downN_val_eq_of (fixedLift l m r q hl hm d hq) (lift l m r d)
  · rw [liftH_eq_srcQ l m r hl hm, hq]
  · rfl

lemma source_q_fiber_bound (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (p : Dev m r) :
    (∑ d : Dev (m-1) (l+m-1+r),
      if srcQ l m r hl hm d = q ∧ nearMap l m r d = p then
        ((l+m-1).factorial : ℚ) * d.weight l else 0) ≤ CB (l+q) * p.weight l := by
  classical
  let D : Finset (Dev (m-1) (l+m-1+r)) := Finset.univ.filter fun d =>
    srcQ l m r hl hm d = q ∧ nearMap l m r d = p
  let F : Dev (m-1) (l+m-1+r) → Dev m (l+q+r) :=
    fixedLiftDefault l m r q hl hm
  let T : Dev m (l+q+r) → ℚ := fun e =>
    if downN (l+q) r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
    then ((l+q).factorial : ℚ) * e.weight l else 0
  have hFinj : Set.InjOn F D := by
    intro d hd d' hd' he
    have hdf := hd
    have hd'f := hd'
    dsimp [D] at hdf hd'f
    have hq := (mem_filter.mp hdf).2.1
    have hq' := (mem_filter.mp hd'f).2.1
    dsimp [F] at he
    rw [fixedLiftDefault_eq l m r q hl hm d hq,
      fixedLiftDefault_eq l m r q hl hm d' hq'] at he
    exact fixedLift_injective l m r q hl hm hq hq' he
  have hterm (d : Dev (m-1) (l+m-1+r)) (hd : d ∈ D) :
      T (F d) = ((l+m-1).factorial : ℚ) * d.weight l := by
    have hdf := hd
    dsimp [D] at hdf
    have hs := (mem_filter.mp hdf).2
    have hq := hs.1
    have hmap := hs.2
    have hF := fixedLiftDefault_eq l m r q hl hm d hq
    have hvalid : downN (l+q) r (F d) = p ∧
        (∀ i : Fin m, i.val ≤ q → (F d).val i = 0) := by
      constructor
      · change downN (l+q) r (fixedLiftDefault l m r q hl hm d) = p
        rw [hF, fixedLift_downN l m r q hl hm d hq, hmap]
      · intro i hi
        change (fixedLiftDefault l m r q hl hm d).val i = 0
        rw [hF]
        exact fixedLift_zero l m r q hl hm d hq i hi
    dsimp [F] at hvalid
    dsimp [T, F]
    rw [if_pos hvalid, hF, fixedLift_weight l m r q hl hm d hq]
    have hw := lift_weight l m r hm d
    have hLH := liftH_eq_srcQ l m r hl hm d
    rw [hq] at hLH
    have hfac : (((liftH l m r d).factorial : ℕ) : ℚ) =
        (((l+q).factorial : ℕ) : ℚ) := congrArg (fun n : ℕ => (n.factorial : ℚ)) hLH
    calc
      ((l+q).factorial : ℚ) * (lift l m r d).weight l =
          ((liftH l m r d).factorial : ℚ) * (lift l m r d).weight l :=
        congrArg (fun z : ℚ => z * (lift l m r d).weight l) hfac.symm
      _ = _ := hw.symm
  have himage : ∑ e ∈ D.image F, T e =
      ∑ d ∈ D, ((l+m-1).factorial : ℚ) * d.weight l := by
    rw [Finset.sum_image hFinj]
    apply Finset.sum_congr rfl
    exact hterm
  have hle : (∑ e ∈ D.image F, T e) ≤ ∑ e : Dev m (l+q+r), T e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro e he hne
    dsimp [T]
    split_ifs
    · exact mul_nonneg (by positivity) (weight_pos _ _).le
    · norm_num
  have hfull := restricted_fiber_factorial_bound m r (l+q) l q p rfl
  rw [himage] at hle
  have hsource : (∑ d : Dev (m-1) (l+m-1+r),
      if srcQ l m r hl hm d = q ∧ nearMap l m r d = p then
        ((l+m-1).factorial : ℚ) * d.weight l else 0) =
      ∑ d ∈ D, ((l+m-1).factorial : ℚ) * d.weight l := by
    dsimp [D]
    rw [← Finset.sum_filter]
  rw [hsource]
  exact le_trans hle hfull

end Dev

lemma CB_tail_invariant (N : ℕ) (hN : 13 ≤ N) :
    (∑ H ∈ Icc 14 N, CB H) + 5 * CB (N+1) ≤ 5 * CB 14 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hg := CB_geometric (N+1) (by omega)
    calc
      (∑ H ∈ Icc 14 N, CB H) + CB (N+1) + 5 * CB (N+1+1) ≤
          (∑ H ∈ Icc 14 N, CB H) + CB (N+1) + 5 * ((4/5 : ℚ) * CB (N+1)) := by
            gcongr
      _ = (∑ H ∈ Icc 14 N, CB H) + 5 * CB (N+1) := by ring
      _ ≤ _ := ih

set_option maxHeartbeats 2000000 in
lemma gg_cert_29_0 : gg 29 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_28_0 : gg 28 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_28_1 : gg 28 1 = (59/870:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_29_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_27_0 : gg 27 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_27_1 : gg 27 1 = (57/812:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_28_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_27_2 : gg 27 2 = (39/8120:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_28_0, gg_cert_28_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_26_0 : gg 26 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_26_1 : gg 26 1 = (55/756:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_27_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_26_2 : gg 26 2 = (113/21924:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_27_0, gg_cert_27_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_26_3 : gg 26 3 = (1097/3069360:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_27_0, gg_cert_27_1, gg_cert_27_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_25_0 : gg 25 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_25_1 : gg 25 1 = (53/702:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_26_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_25_2 : gg 25 2 = (109/19656:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_26_0, gg_cert_26_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_25_3 : gg 25 3 = (6131/15390648:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_26_0, gg_cert_26_1, gg_cert_26_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_25_4 : gg 25 4 = (1760821/62486030880:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_26_0, gg_cert_26_1, gg_cert_26_2, gg_cert_26_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_24_0 : gg 24 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_24_1 : gg 24 1 = (51/650:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_25_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_24_2 : gg 24 2 = (7/1170:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_25_0, gg_cert_25_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_24_3 : gg 24 3 = (356/798525:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_25_0, gg_cert_25_1, gg_cert_25_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_24_4 : gg 24 4 = (1526363/46684965600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_25_0, gg_cert_25_1, gg_cert_25_2, gg_cert_25_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_24_5 : gg 24 5 = (36208037293/15352817787216000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_25_0, gg_cert_25_1, gg_cert_25_2, gg_cert_25_3, gg_cert_25_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_0 : gg 23 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_1 : gg 23 1 = (49/600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_24_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_2 : gg 23 2 = (101/15600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_24_0, gg_cert_24_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_3 : gg 23 3 = (1759/3510000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_24_0, gg_cert_24_1, gg_cert_24_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_4 : gg 23 4 = (329033/8624070000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_24_0, gg_cert_24_1, gg_cert_24_2, gg_cert_24_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_5 : gg 23 5 = (28072695493/9831853755360000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_24_0, gg_cert_24_1, gg_cert_24_2, gg_cert_24_3, gg_cert_24_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_23_6 : gg 23 6 = (588655938940037/2802196302522664320000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_24_0, gg_cert_24_1, gg_cert_24_2, gg_cert_24_3, gg_cert_24_4, gg_cert_24_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_0 : gg 22 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_1 : gg 22 1 = (47/552:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_2 : gg 22 2 = (97/13800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0, gg_cert_23_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_3 : gg 22 3 = (2437/4305600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0, gg_cert_23_1, gg_cert_23_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_4 : gg 22 4 = (376133/8395920000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0, gg_cert_23_1, gg_cert_23_2, gg_cert_23_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_5 : gg 22 5 = (224552063/64464923250000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0, gg_cert_23_1, gg_cert_23_2, gg_cert_23_3, gg_cert_23_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_6 : gg 22 6 = (488902400554849/1837327670532900000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0, gg_cert_23_1, gg_cert_23_2, gg_cert_23_3, gg_cert_23_4, gg_cert_23_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_22_7 : gg 22 7 = (523098044696532627001/26183021701696144740000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_23_0, gg_cert_23_1, gg_cert_23_2, gg_cert_23_3, gg_cert_23_4, gg_cert_23_5, gg_cert_23_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_0 : gg 21 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_1 : gg 21 1 = (45/506:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_2 : gg 21 2 = (31/4048:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_3 : gg 21 3 = (4487/6982800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1, gg_cert_22_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_4 : gg 21 4 = (87409/1650480000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1, gg_cert_22_2, gg_cert_22_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_5 : gg 21 5 = (910157857/212416776000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1, gg_cert_22_2, gg_cert_22_3, gg_cert_22_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_6 : gg 21 6 = (35527409759417/104381603726400000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1, gg_cert_22_2, gg_cert_22_3, gg_cert_22_4, gg_cert_22_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_7 : gg 21 7 = (39502065365914155383/1487500482063435840000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1, gg_cert_22_2, gg_cert_22_3, gg_cert_22_4, gg_cert_22_5, gg_cert_22_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_21_8 : gg 21 8 = (43163269842846809132929817/21197774369693198781504000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_22_0, gg_cert_22_1, gg_cert_22_2, gg_cert_22_3, gg_cert_22_4, gg_cert_22_5, gg_cert_22_6, gg_cert_22_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_0 : gg 20 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_1 : gg 20 1 = (43/462:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_2 : gg 20 2 = (89/10626:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_3 : gg 20 3 = (49/66792:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_4 : gg 20 4 = (271277/4301404800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2, gg_cert_21_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_5 : gg 20 5 = (12311708753/2315016063360000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2, gg_cert_21_3, gg_cert_21_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_6 : gg 20 6 = (60911006620201/138437960588928000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2, gg_cert_21_3, gg_cert_21_4, gg_cert_21_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_7 : gg 20 7 = (167715232681959200639/4693960554504546124800000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2, gg_cert_21_3, gg_cert_21_4, gg_cert_21_5, gg_cert_21_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_8 : gg 20 8 = (4384187233845835319064612103/1538510348394517155139722240000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2, gg_cert_21_3, gg_cert_21_4, gg_cert_21_5, gg_cert_21_6, gg_cert_21_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_20_9 : gg 20 9 = (930770988834960961590265978635911/4167504116769511090361858614272000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_21_0, gg_cert_21_1, gg_cert_21_2, gg_cert_21_3, gg_cert_21_4, gg_cert_21_5, gg_cert_21_6, gg_cert_21_7, gg_cert_21_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_0 : gg 19 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_1 : gg 19 1 = (41/420:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_2 : gg 19 2 = (17/1848:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_3 : gg 19 3 = (3761/4462920:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_4 : gg 19 4 = (48847/645210720:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_5 : gg 19 5 = (145083881/21765108288000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3, gg_cert_20_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_6 : gg 19 6 = (518978175422593/901976558606323200000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3, gg_cert_20_4, gg_cert_20_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_7 : gg 19 7 = (86707653488157079673/1779960540753718202880000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3, gg_cert_20_4, gg_cert_20_5, gg_cert_20_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_8 : gg 19 8 = (127960355760178948847646577/31613167180110487514070528000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3, gg_cert_20_4, gg_cert_20_5, gg_cert_20_6, gg_cert_20_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_9 : gg 19 9 = (37647620989763558384327620472492419/113978169854871275882107406978150400000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3, gg_cert_20_4, gg_cert_20_5, gg_cert_20_6, gg_cert_20_7, gg_cert_20_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_19_10 : gg 19 10 = (1554988384579050827618699433773682394978399/58705299822208376690520947558908001832960000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_20_0, gg_cert_20_1, gg_cert_20_2, gg_cert_20_3, gg_cert_20_4, gg_cert_20_5, gg_cert_20_6, gg_cert_20_7, gg_cert_20_8, gg_cert_20_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_0 : gg 18 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_1 : gg 18 1 = (39/380:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_2 : gg 18 2 = (27/2660:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_3 : gg 18 3 = (1711/1755600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_4 : gg 18 4 = (570107/6218335200:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_5 : gg 18 5 = (209262679/24778511188200:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_6 : gg 18 6 = (32101024205531/42127433581730112000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4, gg_cert_19_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_7 : gg 18 7 = (39212302023128376691/581939942011303421145600000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4, gg_cert_19_5, gg_cert_19_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_8 : gg 18 8 = (46975754640950812980110117/8038801970955743199021089280000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4, gg_cert_19_5, gg_cert_19_6, gg_cert_19_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_9 : gg 18 9 = (6136711565900860313043534455851/12338489185154271711404169232896000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4, gg_cert_19_5, gg_cert_19_6, gg_cert_19_7, gg_cert_19_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_10 : gg 18 10 = (16644706060560890576436526315357769074073/400366900056921700553871050518090718515200000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4, gg_cert_19_5, gg_cert_19_6, gg_cert_19_7, gg_cert_19_8, gg_cert_19_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_18_11 : gg 18 11 = (4929643423367570844931130856465149212069929723131/1443483542125645601635987682505815209097995407360000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_19_0, gg_cert_19_1, gg_cert_19_2, gg_cert_19_3, gg_cert_19_4, gg_cert_19_5, gg_cert_19_6, gg_cert_19_7, gg_cert_19_8, gg_cert_19_9, gg_cert_19_10]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_0 : gg 17 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_1 : gg 17 1 = (37/342:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_2 : gg 17 2 = (77/6840:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_3 : gg 17 3 = (1033/909720:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_4 : gg 17 4 = (471169/4202906400:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_5 : gg 17 5 = (402944699/37216736172000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_6 : gg 17 6 = (24279834921877/23727902313820320000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_7 : gg 17 7 = (59691628311941669/630331724966636800800000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5, gg_cert_18_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_8 : gg 17 8 = (59824237742982586892453/6965821105875301951112832000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5, gg_cert_18_6, gg_cert_18_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_9 : gg 17 9 = (2939990958933480569733213121/3848978383693609843691297547264000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5, gg_cert_18_6, gg_cert_18_7, gg_cert_18_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_10 : gg 17 10 = (5908316827306242810822854277782069/88615029327777979431304743430659072000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5, gg_cert_18_6, gg_cert_18_7, gg_cert_18_8, gg_cert_18_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_11 : gg 17 11 = (5478560274359095936846715866343395754085509/958478358736270551125967294940309180125388800000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5, gg_cert_18_6, gg_cert_18_7, gg_cert_18_8, gg_cert_18_9, gg_cert_18_10]
set_option maxHeartbeats 2000000 in
lemma gg_cert_17_12 : gg 17 12 = (1664239667428512352103611090530589452153789722938223/3455699599848795570316554511918921610580601005219840000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_18_0, gg_cert_18_1, gg_cert_18_2, gg_cert_18_3, gg_cert_18_4, gg_cert_18_5, gg_cert_18_6, gg_cert_18_7, gg_cert_18_8, gg_cert_18_9, gg_cert_18_10, gg_cert_18_11]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_0 : gg 16 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_1 : gg 16 1 = (35/306:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_2 : gg 16 2 = (73/5814:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_3 : gg 16 3 = (349/261630:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_4 : gg 16 4 = (385699/2783743200:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_5 : gg 16 5 = (1145450447/81452326032000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_6 : gg 16 6 = (229461652669769/164447359119046080000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_7 : gg 16 7 = (4996572325434605827/36889927913311876972800000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_8 : gg 16 8 = (8628738728380544553614521/670306959551716928059183488000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6, gg_cert_17_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_9 : gg 16 9 = (21091852167691344744799098858131/17593023927925463871565502846415360000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6, gg_cert_17_7, gg_cert_17_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_10 : gg 16 10 = (50562339453944541986009706781591674871/461750376477595868375159932117643749939200000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6, gg_cert_17_7, gg_cert_17_8, gg_cert_17_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_11 : gg 16 11 = (2379317313226010694760502898821914255748497/242384039322276124649309802270894874850584596480000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6, gg_cert_17_7, gg_cert_17_8, gg_cert_17_9, gg_cert_17_10]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_12 : gg 16 12 = (239188084802851013170780846604862178103471548887777239/276732419693538287970754544457290681975739604480400793600000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6, gg_cert_17_7, gg_cert_17_8, gg_cert_17_9, gg_cert_17_10, gg_cert_17_11]
set_option maxHeartbeats 2000000 in
lemma gg_cert_16_13 : gg 16 13 = (1418021591184579697028175854282452587523180463973825847188013517/18956899717547329444554858856945421110452623400173576633370501120000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_17_0, gg_cert_17_1, gg_cert_17_2, gg_cert_17_3, gg_cert_17_4, gg_cert_17_5, gg_cert_17_6, gg_cert_17_7, gg_cert_17_8, gg_cert_17_9, gg_cert_17_10, gg_cert_17_11, gg_cert_17_12]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_0 : gg 15 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_1 : gg 15 1 = (33/272:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_2 : gg 15 2 = (23/1632:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_3 : gg 15 3 = (2501/1581408:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_4 : gg 15 4 = (9763/56337660:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_5 : gg 15 5 = (2399616553/129477463718400:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_6 : gg 15 6 = (65992223982521/34096595295603456000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_7 : gg 15 7 = (40793977541628305501/206516940318316924369920000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_8 : gg 15 8 = (1451010306738876922532773/73578584379928724344836403200000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6, gg_cert_16_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_9 : gg 15 9 = (14603657432309229217798346388581/7576088104548678235166964401707008000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6, gg_cert_16_7, gg_cert_16_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_10 : gg 15 10 = (110141770719039193016866425882783832373/596531025394102829008211653258111522529280000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6, gg_cert_16_7, gg_cert_16_8, gg_cert_16_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_11 : gg 15 11 = (814731498940383604733040342437804279217831179/46970053587957628658315714573928335414515317964800000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6, gg_cert_16_7, gg_cert_16_8, gg_cert_16_9, gg_cert_16_10]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_12 : gg 15 12 = (34797403015410385477081005866722821563991001373641/21755053409670445984313983661726988626879298153072230400000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6, gg_cert_16_7, gg_cert_16_8, gg_cert_16_9, gg_cert_16_10, gg_cert_16_11]
set_option maxHeartbeats 2000000 in
lemma gg_cert_15_14 : gg 15 14 = (24877000164216514052452442128792616311591599297621351160070142193403453/1928328900102021753642671546602334748169657481640866117864095972080353280000000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_16_0, gg_cert_16_1, gg_cert_16_2, gg_cert_16_3, gg_cert_16_4, gg_cert_16_5, gg_cert_16_6, gg_cert_16_7, gg_cert_16_8, gg_cert_16_9, gg_cert_16_10, gg_cert_16_11, gg_cert_16_12, gg_cert_16_13]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_0 : gg 14 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_1 : gg 14 1 = (31/240:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_2 : gg 14 2 = (13/816:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_3 : gg 14 3 = (371/195840:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_4 : gg 14 4 = (250103/1138613760:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_5 : gg 14 5 = (205419011/8274875500800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_6 : gg 14 6 = (4607384397191/1683854415657792000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_7 : gg 14 7 = (8877388527464926421/30152983083713960279040000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5, gg_cert_15_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_8 : gg 14 8 = (96107654585597141819184367/3104730247018706611254015897600000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5, gg_cert_15_6, gg_cert_15_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_9 : gg 14 9 = (1017757563661558361127047790348899/319681468330713323811984325671327744000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5, gg_cert_15_6, gg_cert_15_7, gg_cert_15_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_10 : gg 14 10 = (10552789780739166481139912793585517525003/32916302887252128256825349358014392209039360000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5, gg_cert_15_6, gg_cert_15_7, gg_cert_15_8, gg_cert_15_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_11 : gg 14 11 = (1394025969479691274497730829222127672931803156383/44060354885438182238539585662192529555321384592179200000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5, gg_cert_15_6, gg_cert_15_7, gg_cert_15_8, gg_cert_15_9, gg_cert_15_10]
set_option maxHeartbeats 2000000 in
lemma gg_cert_14_13 : gg 14 13 = (4595210468425061349692095362708787119655362001338220004732829673/15788899792021622074415466117731370432458445242283727541948636921856000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_15_0, gg_cert_15_1, gg_cert_15_2, gg_cert_15_3, gg_cert_15_4, gg_cert_15_5, gg_cert_15_6, gg_cert_15_7, gg_cert_15_8, gg_cert_15_9, gg_cert_15_10, gg_cert_15_11, gg_cert_15_12]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_0 : gg 13 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_1 : gg 13 1 = (29/210:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_2 : gg 13 2 = (61/3360:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_3 : gg 13 3 = (281/122400:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_4 : gg 13 4 = (65869/233049600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_5 : gg 13 5 = (183544073/5419801497600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_6 : gg 13 6 = (996248176943/252085807256371200:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4, gg_cert_14_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_7 : gg 13 7 = (184525296335135551/410375527348791803904000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4, gg_cert_14_5, gg_cert_14_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_8 : gg 13 8 = (366962446684708470191077/7348643813298096687525396480000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4, gg_cert_14_5, gg_cert_14_6, gg_cert_14_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_9 : gg 13 9 = (16401607484698148871731729360321/3026640071845692102567754889743564800000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4, gg_cert_14_5, gg_cert_14_6, gg_cert_14_7, gg_cert_14_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_10 : gg 13 10 = (717113598607122547606814787972031912813/1246563360157036889165861183648170034331648000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4, gg_cert_14_5, gg_cert_14_6, gg_cert_14_7, gg_cert_14_8, gg_cert_14_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_13_12 : gg 13 12 = (16748401897067039881531481245567733462228682988971664561/2748937525719017029048053632231492035324540232122669360742400000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_14_0, gg_cert_14_1, gg_cert_14_2, gg_cert_14_3, gg_cert_14_4, gg_cert_14_5, gg_cert_14_6, gg_cert_14_7, gg_cert_14_8, gg_cert_14_9, gg_cert_14_10, gg_cert_14_11]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_0 : gg 12 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_1 : gg 12 1 = (27/182:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_2 : gg 12 2 = (19/910:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_3 : gg 12 3 = (431/152880:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_4 : gg 12 4 = (21977/59404800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_5 : gg 12 5 = (34296893/727114752000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3, gg_cert_13_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_6 : gg 12 6 = (2307509249183/394561549025280000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3, gg_cert_13_4, gg_cert_13_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_7 : gg 12 7 = (64781058824597657/91759233841319116800000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3, gg_cert_13_4, gg_cert_13_5, gg_cert_13_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_8 : gg 12 8 = (1772954595954206411503/21339527422137173803008000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3, gg_cert_13_4, gg_cert_13_5, gg_cert_13_6, gg_cert_13_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_9 : gg 12 9 = (3646904612813763068247922549/382129478291501027751320616960000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3, gg_cert_13_4, gg_cert_13_5, gg_cert_13_6, gg_cert_13_7, gg_cert_13_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_12_11 : gg 12 11 = (7626416670613432393791554693870778648767869/64821294728165918236624781549704841785245696000000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_13_0, gg_cert_13_1, gg_cert_13_2, gg_cert_13_3, gg_cert_13_4, gg_cert_13_5, gg_cert_13_6, gg_cert_13_7, gg_cert_13_8, gg_cert_13_9, gg_cert_13_10]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_0 : gg 11 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_1 : gg 11 1 = (25/156:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_2 : gg 11 2 = (53/2184:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_3 : gg 11 3 = (499/141960:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_4 : gg 11 4 = (6543/13249600:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2, gg_cert_12_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_5 : gg 11 5 = (458249531/6811354368000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2, gg_cert_12_3, gg_cert_12_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_6 : gg 11 6 = (1730922496619/194532280750080000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2, gg_cert_12_3, gg_cert_12_4, gg_cert_12_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_7 : gg 11 7 = (13417972123111441/11728999647358156800000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2, gg_cert_12_3, gg_cert_12_4, gg_cert_12_5, gg_cert_12_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_8 : gg 11 8 = (24606475162665474437257/171844857953345615560704000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2, gg_cert_12_3, gg_cert_12_4, gg_cert_12_5, gg_cert_12_6, gg_cert_12_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_11_10 : gg 11 10 = (10425900206610762944194553517818243/5009511110483301063264827575212441600000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_12_0, gg_cert_12_1, gg_cert_12_2, gg_cert_12_3, gg_cert_12_4, gg_cert_12_5, gg_cert_12_6, gg_cert_12_7, gg_cert_12_8, gg_cert_12_9]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_0 : gg 10 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_1 : gg 10 1 = (23/132:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_2 : gg 10 2 = (49/1716:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_3 : gg 10 3 = (643/144144:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1, gg_cert_11_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_4 : gg 10 4 = (8041/11924640:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1, gg_cert_11_2, gg_cert_11_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_5 : gg 10 5 = (3924449/39788548800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1, gg_cert_11_2, gg_cert_11_3, gg_cert_11_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_6 : gg 10 6 = (1238972560733/88636154390784000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1, gg_cert_11_2, gg_cert_11_3, gg_cert_11_4, gg_cert_11_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_7 : gg 10 7 = (63264961278389821/32908831402210283520000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1, gg_cert_11_2, gg_cert_11_3, gg_cert_11_4, gg_cert_11_5, gg_cert_11_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_10_9 : gg 10 9 = (164331069670168299802792311847/4912969048993509630155296210944000000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_11_0, gg_cert_11_1, gg_cert_11_2, gg_cert_11_3, gg_cert_11_4, gg_cert_11_5, gg_cert_11_6, gg_cert_11_7, gg_cert_11_8]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_0 : gg 9 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_1 : gg 9 1 = (21/110:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_2 : gg 9 2 = (3/88:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0, gg_cert_10_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_3 : gg 9 3 = (1091/188760:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0, gg_cert_10_1, gg_cert_10_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_4 : gg 9 4 = (64973/68708640:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0, gg_cert_10_1, gg_cert_10_2, gg_cert_10_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_5 : gg 9 5 = (21007381/140680940400:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0, gg_cert_10_1, gg_cert_10_2, gg_cert_10_3, gg_cert_10_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_6 : gg 9 6 = (70039677593/3072471738336000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0, gg_cert_10_1, gg_cert_10_2, gg_cert_10_3, gg_cert_10_4, gg_cert_10_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_9_8 : gg 9 8 = (204812384028749971307/423536660146446348902400000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_10_0, gg_cert_10_1, gg_cert_10_2, gg_cert_10_3, gg_cert_10_4, gg_cert_10_5, gg_cert_10_6, gg_cert_10_7]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_0 : gg 8 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_1 : gg 8 1 = (19/90:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_9_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_2 : gg 8 2 = (41/990:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_9_0, gg_cert_9_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_3 : gg 8 3 = (19/2475:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_9_0, gg_cert_9_1, gg_cert_9_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_4 : gg 8 4 = (46507/33976800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_9_0, gg_cert_9_1, gg_cert_9_2, gg_cert_9_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_5 : gg 8 5 = (3550199/15115900800:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_9_0, gg_cert_9_1, gg_cert_9_2, gg_cert_9_3, gg_cert_9_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_8_7 : gg 8 7 = (1829357382978101/294441111628215552000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_9_0, gg_cert_9_1, gg_cert_9_2, gg_cert_9_3, gg_cert_9_4, gg_cert_9_5, gg_cert_9_6]
set_option maxHeartbeats 2000000 in
lemma gg_cert_7_0 : gg 7 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_7_1 : gg 7 1 = (17/72:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_8_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_7_2 : gg 7 2 = (37/720:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_8_0, gg_cert_8_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_7_3 : gg 7 3 = (749/71280:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_8_0, gg_cert_8_1, gg_cert_8_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_7_4 : gg 7 4 = (8071/3920400:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_8_0, gg_cert_8_1, gg_cert_8_2, gg_cert_8_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_7_6 : gg 7 6 = (188187017881/2693653522560000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_8_0, gg_cert_8_1, gg_cert_8_2, gg_cert_8_3, gg_cert_8_4, gg_cert_8_5]
set_option maxHeartbeats 2000000 in
lemma gg_cert_6_0 : gg 6 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_6_1 : gg 6 1 = (15/56:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_7_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_6_2 : gg 6 2 = (11/168:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_7_0, gg_cert_7_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_6_3 : gg 6 3 = (43/2880:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_7_0, gg_cert_7_1, gg_cert_7_2]
set_option maxHeartbeats 2000000 in
lemma gg_cert_6_5 : gg 6 5 = (1665031/2469852000:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_7_0, gg_cert_7_1, gg_cert_7_2, gg_cert_7_3, gg_cert_7_4]
set_option maxHeartbeats 2000000 in
lemma gg_cert_5_0 : gg 5 0 = 1 := by simp [gg]
set_option maxHeartbeats 2000000 in
lemma gg_cert_5_1 : gg 5 1 = (13/42:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_6_0]
set_option maxHeartbeats 2000000 in
lemma gg_cert_5_2 : gg 5 2 = (29/336:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_6_0, gg_cert_6_1]
set_option maxHeartbeats 2000000 in
lemma gg_cert_5_4 : gg 5 4 = (1973/362880:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_6_0, gg_cert_6_1, gg_cert_6_2, gg_cert_6_3]
set_option maxHeartbeats 2000000 in
lemma gg_cert_4_3 : gg 4 3 = (89/2520:ℚ) := by
  norm_num [gg, rup, Finset.sum_range_succ, gg_cert_5_0, gg_cert_5_1, gg_cert_5_2]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma CB_pair_34 : CB 3 + CB 4 ≤ (342395/1000000 : ℚ) := by
  norm_num [CB, gg_cert_4_3, gg_cert_5_4]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma CB_pair_56 : CB 5 + CB 6 ≤ (131199/1000000 : ℚ) := by
  norm_num [CB, gg_cert_6_5, gg_cert_7_6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma CB_pair_78 : CB 7 + CB 8 ≤ (50812/1000000 : ℚ) := by
  norm_num [CB, gg_cert_8_7, gg_cert_9_8]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma CB_pair_910 : CB 9 + CB 10 ≤ (19691/1000000 : ℚ) := by
  norm_num [CB, gg_cert_10_9, gg_cert_11_10]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma CB_pair_1112 : CB 11 + CB 12 ≤ (7615/1000000 : ℚ) := by
  norm_num [CB, gg_cert_12_11, gg_cert_13_12]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
lemma CB_pair_13x : CB 13 + 5 * CB 14 ≤ (7436/1000000 : ℚ) := by
  norm_num [CB, gg_cert_14_13, gg_cert_15_14]

lemma CB_initial_bound :
    (∑ H ∈ Icc 3 13, CB H) + 5 * CB 14 < (14/25 : ℚ) := by
  norm_num [Finset.sum_Icc_succ_top]
  linarith [CB_pair_34, CB_pair_56, CB_pair_78, CB_pair_910, CB_pair_1112, CB_pair_13x]


set_option maxHeartbeats 5000000 in
lemma CB_tail_bound (N : ℕ) : (∑ H ∈ Icc 3 N, CB H) < (14/25 : ℚ) := by
  by_cases hN : N < 14
  · have hsub : Icc 3 N ⊆ Icc 3 13 := by
      intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    have hnon : ∀ x ∈ Icc 3 13, x ∉ Icc 3 N → (0:ℚ) ≤ CB x := by
      intro x hx hxn; exact mul_nonneg (by positivity) (gg_pos _ _).le
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnon
    have hp : (0:ℚ) < 5 * CB 14 := mul_pos (by norm_num) (mul_pos (by positivity) (gg_pos _ _))
    exact lt_of_le_of_lt hle (lt_trans (lt_add_of_pos_right _ hp) CB_initial_bound)
  · have hi := CB_tail_invariant N (by omega)
    have hu : Icc 3 13 ∪ Icc 14 N = Icc 3 N := by
      ext x
      simp only [mem_union, mem_Icc]
      omega
    have hd : Disjoint (Icc 3 13) (Icc 14 N) := by
      simp only [disjoint_left, mem_Icc]
      omega
    have hsplit : (∑ H ∈ Icc 3 N, CB H) =
        (∑ H ∈ Icc 3 13, CB H) + ∑ H ∈ Icc 14 N, CB H := by
      rw [← hu, sum_union hd]
    rw [hsplit]
    have htail : (∑ H ∈ Icc 14 N, CB H) ≤ 5 * CB 14 := by
      calc
        _ ≤ (∑ H ∈ Icc 14 N, CB H) + 5 * CB (N+1) :=
          le_add_of_nonneg_right (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (gg_pos _ _).le))
        _ ≤ _ := hi
    exact lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left htail (∑ H ∈ Icc 3 13, CB H)) CB_initial_bound

namespace Dev

set_option maxHeartbeats 2000000 in
lemma source_fiber_bound_by_CB (l m r : ℕ) (hl : 0 < l) (hm : 1 < m)
    (p : Dev m r) :
    (∑ d : Dev (m-1) (l+m-1+r),
      if nearMap l m r d = p then ((l+m-1).factorial : ℚ) * d.weight l else 0) ≤
      (∑ q ∈ range (m-1), CB (l+q)) * p.weight l := by
  classical
  let D : Finset (Dev (m-1) (l+m-1+r)) := Finset.univ
  let f : Dev (m-1) (l+m-1+r) → ℕ := srcQ l m r hl hm
  let g : Dev (m-1) (l+m-1+r) → ℚ := fun d =>
    if nearMap l m r d = p then ((l+m-1).factorial : ℚ) * d.weight l else 0
  have hmap : ∀ d ∈ D, f d ∈ range (m-1) := by
    intro d hd
    exact mem_range.mpr (srcQ_lt l m r hl hm d)
  rw [show (∑ d : Dev (m-1) (l+m-1+r),
      if nearMap l m r d = p then ((l+m-1).factorial : ℚ) * d.weight l else 0) =
      ∑ d ∈ D, g d by simp [D, g]]
  rw [← Finset.sum_fiberwise_of_maps_to hmap g]
  calc
    (∑ q ∈ range (m-1), ∑ d ∈ D with f d = q, g d) ≤
        ∑ q ∈ range (m-1), CB (l+q) * p.weight l := by
      apply Finset.sum_le_sum
      intro q hq
      have hs := source_q_fiber_bound l m r q hl hm p
      dsimp [D, f, g]
      rw [← Finset.sum_filter]
      rw [← Finset.sum_filter] at hs
      simpa [Finset.filter_filter, and_comm] using hs
    _ = (∑ q ∈ range (m-1), CB (l+q)) * p.weight l := by rw [Finset.sum_mul]

end Dev

namespace Dev

lemma tail_value_mul_le_sum {m e j : ℕ} (d : Dev m e) (hj : j < m) :
    (m-j) * d.val ⟨j, hj⟩ ≤ e := by
  have hlow : (m-j) * d.val ⟨j, hj⟩ ≤
      ∑ x ∈ Ico j m, natVal d x := by
    rw [← card_Ico]
    exact Finset.card_nsmul_le_sum _ _ _ (fun x hx => by
      simp only [mem_Ico] at hx
      rw [natVal_of_lt d hx.2]
      exact d.mono (by simp; omega))
  have hsub : (∑ x ∈ Ico j m, natVal d x) ≤
      ∑ x ∈ range m, natVal d x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_Ico, mem_range] at hx ⊢
      omega
    · intro x hx hxn
      omega
  calc
    _ ≤ _ := hlow
    _ ≤ _ := hsub
    _ = e := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [natVal_of_lt d (Fin.isLt _)]
      exact d.sum_eq

lemma small_pattern_one {m r : ℕ} (p : Dev m r) (e : Dev m (1+r))
    (he : downN 1 r e = p) :
    (fullVals p e = [] ∧ part p e = 1) ∨
    (fullVals p e = [1] ∧ part p e = 0) := by
  have hs := fullVals_sum_add_part p e he
  generalize hL : fullVals p e = L at hs ⊢
  have hp {x : ℕ} (hx : x ∈ L) : 0 < x := by
    apply mem_fullVals_pos p e
    simpa [hL] using hx
  cases L with
  | nil => simp_all
  | cons a L =>
    have ha : 0 < a := hp (x:=a) (by simp)
    cases L with
    | nil => simp at hs ⊢; omega
    | cons b L =>
      have hb : 0 < b := hp (x:=b) (by simp)
      simp at hs
      omega

lemma small_pattern_two {m r : ℕ} (p : Dev m r) (e : Dev m (2+r))
    (he : downN 2 r e = p) :
    (fullVals p e = [] ∧ part p e = 2) ∨
    (fullVals p e = [1] ∧ part p e = 1) ∨
    (fullVals p e = [2] ∧ part p e = 0) ∨
    (fullVals p e = [1,1] ∧ part p e = 0) := by
  have hs := fullVals_sum_add_part p e he
  generalize hL : fullVals p e = L at hs ⊢
  have hp {x : ℕ} (hx : x ∈ L) : 0 < x := by
    apply mem_fullVals_pos p e
    simpa [hL] using hx
  cases L with
  | nil => simp_all
  | cons a L =>
    have ha : 0 < a := hp (x:=a) (by simp)
    cases L with
    | nil =>
      simp at hs ⊢
      omega
    | cons b L =>
      have hb : 0 < b := hp (x:=b) (by simp)
      cases L with
      | nil =>
        simp at hs ⊢
        omega
      | cons c L =>
        have hc : 0 < c := hp (x:=c) (by simp)
        simp at hs
        omega

end Dev

namespace Dev

lemma coordProd_allVals_le_custom {m r H l A : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (hA : A ≤ l + (cut p - (fullVals p e).length)) :
    coordProd l (allVals p e) ≤ blockProd A (fullVals p e) := by
  have hrep := allVals_representation p e
  rw [hrep, coordProd_append, coordProd_replicate_zero, one_mul]
  apply coordProd_le_blockProd
  rw [allVals_length]
  simpa using hA

lemma weight_le_custom {m r H l A B t : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (he : downN H r e = p) (ht : part p e = t)
    (hA : A ≤ l + (cut p - (fullVals p e).length))
    (hB : ∀ hc : cut p < m, B ≤ l + cut p + p.val ⟨cut p, hc⟩) :
    e.weight l ≤ p.weight l * (blockProd A (fullVals p e) * rup B t) := by
  rw [weight_factorization p e he, ratio_fin_eq_range, ratio_product_decomp p e he]
  rw [ht]
  apply mul_le_mul_of_nonneg_left _ (weight_pos _ _).le
  have hb := coordProd_allVals_le_custom p e hA
  by_cases hc : cut p < m
  · rw [dif_pos hc]
    have hept := factorial_ratio_le_rup B
      (l + cut p + p.val ⟨cut p, hc⟩) t (hB hc)
    exact mul_le_mul hb hept (by unfold facRatio; positivity) (blockProd_pos _ _).le
  · rw [dif_neg hc]
    have ht0 : t = 0 := by
      rw [← ht]
      simp [part, hc]
    rw [ht0]
    norm_num [rup]
    exact hb

end Dev

namespace Dev

lemma part_add_le_next {m r H : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (he : downN H r e = p) (hc1 : cut p + 1 < m) :
    p.val ⟨cut p, by omega⟩ + part p e ≤ p.val ⟨cut p+1, hc1⟩ := by
  have hc : cut p < m := by omega
  have hpe : p.val ⟨cut p, hc⟩ ≤ e.val ⟨cut p, hc⟩ := by
    have h := downN_le e ⟨cut p, hc⟩
    simpa [he] using h
  have hpart : part p e = e.val ⟨cut p, hc⟩ - p.val ⟨cut p, hc⟩ := by
    simp [part, hc, natVal_of_lt]
  have hafter := downN_eq_after_pos e ⟨cut p, hc⟩ ⟨cut p+1, hc1⟩
    (by simpa [he] using val_pos_at_cut p hc) (by simp)
  have hnext : e.val ⟨cut p+1, hc1⟩ = p.val ⟨cut p+1, hc1⟩ := by
    rw [← hafter]
    exact congrArg (fun z : Dev m r => z.val ⟨cut p+1, hc1⟩) he
  have hmono := e.mono (show (⟨cut p, hc⟩ : Fin m) ≤ ⟨cut p+1, hc1⟩ by simp)
  rw [hpart, Nat.add_sub_of_le hpe]
  calc
    _ ≤ e.val ⟨cut p+1, hc1⟩ := hmono
    _ = _ := hnext

lemma full_member_le_cut {m r H x : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (hx : x ∈ fullVals p e) (hc : cut p < m) : x ≤ e.val ⟨cut p, hc⟩ := by
  have hxa : x ∈ allVals p e := (List.mem_filter.mp hx).1
  unfold allVals at hxa
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hxa
  have hjm : j.val < m := lt_of_lt_of_le j.isLt (cut_le p)
  rw [natVal_of_lt e hjm] at hj
  rw [← hj]
  exact e.mono (by simp)

lemma full_member_le_pcut_of_part_zero {m r H x : ℕ} (p : Dev m r) (e : Dev m (H+r))
    (he : downN H r e = p) (hx : x ∈ fullVals p e) (ht : part p e = 0)
    (hc : cut p < m) : x ≤ p.val ⟨cut p, hc⟩ := by
  have hxe := full_member_le_cut p e hx hc
  have hpe : p.val ⟨cut p, hc⟩ ≤ e.val ⟨cut p, hc⟩ := by
    have h := downN_le e ⟨cut p, hc⟩
    simpa [he] using h
  have hpform : part p e = e.val ⟨cut p, hc⟩ - p.val ⟨cut p, hc⟩ := by
    simp [part, hc, natVal_of_lt]
  rw [hpform] at ht
  omega

lemma one_block_bound_high {m r : ℕ} (p : Dev m r) (e : Dev m (1+r))
    (he : downN 1 r e = p) (hf : fullVals p e = [1])
    (ht : part p e = 0) (hc : 7 ≤ cut p) :
    e.weight 1 ≤ p.weight 1 * (1/8 : ℚ) := by
  have h := weight_le_custom (l:=1) (A:=7) (B:=0) p e he ht (by simp [hf]; omega) (by intro hcm; omega)
  norm_num [hf, blockProd, rup] at h ⊢
  exact h

lemma one_endpoint_bound_high {m r : ℕ} (p : Dev m r) (e : Dev m (1+r))
    (he : downN 1 r e = p) (hf : fullVals p e = [])
    (ht : part p e = 1) (hc : 7 ≤ cut p) :
    e.weight 1 ≤ p.weight 1 * (1/10 : ℚ) := by
  have h := weight_le_custom (l:=1) (A:=0) (B:=9) p e he ht (by simp [hf]) (by
    intro hcm
    have hp := val_pos_at_cut p hcm
    omega)
  norm_num [hf, blockProd, rup] at h ⊢
  exact h

lemma two_empty_bound_high {m r : ℕ} (p : Dev m r) (e : Dev m (2+r))
    (he : downN 2 r e = p) (hf : fullVals p e = []) (ht : part p e = 2)
    (hc : 8 ≤ cut p) :
    (2:ℚ) * e.weight 1 ≤ p.weight 1 * (1/66 : ℚ) := by
  have h := weight_le_custom (l:=1) (A:=0) (B:=10) p e he ht (by simp [hf]) (by
    intro hcm
    have hp := val_pos_at_cut p hcm
    omega)
  rw [hf] at h
  have hpw := (weight_pos 1 p).le
  calc
    2 * e.weight 1 ≤ 2 * (p.weight 1 * (blockProd 0 [] * rup 10 2)) := by gcongr
    _ = _ := by norm_num [blockProd, rup]; ring

lemma two_one_bound_at {m r c : ℕ} (p : Dev m r) (e : Dev m (2+r))
    (he : downN 2 r e = p) (hf : fullVals p e = [1]) (ht : part p e = 1)
    (hc : c ≤ cut p) (hcA : c ≤ 1 + (cut p - 1)) :
    (2:ℚ) * e.weight 1 ≤ p.weight 1 * (2 * (rup c 1 * rup (c+2) 1)) := by
  have h := weight_le_custom (l:=1) (A:=c) (B:=c+2) p e he ht (by simpa [hf] using hcA) (by
    intro hcm
    have hp := val_pos_at_cut p hcm
    omega)
  rw [hf] at h
  calc
    2 * e.weight 1 ≤ 2 * (p.weight 1 * (blockProd c [1] * rup (c+2) 1)) := by gcongr
    _ = _ := by simp [blockProd]; ring

lemma two_two_bound_high {m r : ℕ} (p : Dev m r) (e : Dev m (2+r))
    (he : downN 2 r e = p) (hf : fullVals p e = [2]) (ht : part p e = 0)
    (hc : 8 ≤ cut p) :
    (2:ℚ) * e.weight 1 ≤ p.weight 1 * (1/45 : ℚ) := by
  have h := weight_le_custom (l:=1) (A:=8) (B:=0) p e he ht (by simp [hf]; omega) (by intro hcm; omega)
  rw [hf] at h
  calc
    2 * e.weight 1 ≤ 2 * (p.weight 1 * (blockProd 8 [2] * rup 0 0)) := by gcongr
    _ = _ := by norm_num [blockProd, rup]; ring

lemma two_eleven_bound_at {m r A : ℕ} (p : Dev m r) (e : Dev m (2+r))
    (he : downN 2 r e = p) (hf : fullVals p e = [1,1]) (ht : part p e = 0)
    (hA : A ≤ 1 + (cut p - 2)) :
    (2:ℚ) * e.weight 1 ≤ p.weight 1 * (2 * (rup A 1 * rup (A+1) 1)) := by
  have h := weight_le_custom (l:=1) (A:=A) (B:=0) p e he ht (by simpa [hf] using hA) (by intro hcm; omega)
  rw [hf] at h
  calc
    2 * e.weight 1 ≤ 2 * (p.weight 1 * (blockProd A [1,1] * rup 0 0)) := by gcongr
    _ = _ := by simp [blockProd, rup]; ring

end Dev

namespace Dev

lemma eq_of_downN_fullVals_eq {m r H : ℕ} (p : Dev m r) {e e' : Dev m (H+r)}
    (he : downN H r e = p) (he' : downN H r e' = p)
    (hf : fullVals p e = fullVals p e') : e = e' := by
  apply pattern_injective p he he'
  have hs := fullVals_sum_add_part p e he
  have hs' := fullVals_sum_add_part p e' he'
  have ht : part p e = part p e' := by
    rw [hf] at hs
    omega
  unfold pattern
  congr

noncomputable def smallSet (m r H q : ℕ) (p : Dev m r) : Finset (Dev m (H+r)) :=
  Finset.univ.filter fun e => downN H r e = p ∧
    ∀ i : Fin m, i.val ≤ q → e.val i = 0

lemma smallSet_mem {m r H q : ℕ} {p : Dev m r} {e : Dev m (H+r)} :
    e ∈ smallSet m r H q p ↔ downN H r e = p ∧
      ∀ i : Fin m, i.val ≤ q → e.val i = 0 := by
  simp [smallSet]

lemma card_filter_fullVals_le_one {m r H q : ℕ} (p : Dev m r) (L : List ℕ) :
    ((smallSet m r H q p).filter fun e => fullVals p e = L).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he e' he'
  have heS := (mem_filter.mp he).1
  have he'S := (mem_filter.mp he').1
  have heq := (smallSet_mem.mp heS).1
  have heq' := (smallSet_mem.mp he'S).1
  apply eq_of_downN_fullVals_eq p heq heq'
  rw [(mem_filter.mp he).2, (mem_filter.mp he').2]

lemma sum_filter_fullVals_le {m r H q : ℕ} (p : Dev m r) (L : List ℕ)
    (w : Dev m (H+r) → ℚ) (B : ℚ) (hB : 0 ≤ B)
    (hw : ∀ e ∈ smallSet m r H q p, fullVals p e = L → w e ≤ B) :
    (∑ e ∈ (smallSet m r H q p).filter fun e => fullVals p e = L, w e) ≤ B := by
  let T := (smallSet m r H q p).filter fun e => fullVals p e = L
  have hs := Finset.sum_le_card_nsmul T w B (by
    intro e he
    exact hw e (mem_filter.mp he).1 (mem_filter.mp he).2)
  have hc := card_filter_fullVals_le_one (H:=H) (q:=q) p L
  have hn := nsmul_le_nsmul_left hB hc
  simpa [T] using le_trans hs hn

lemma smallSet_one_union (m r : ℕ) (p : Dev m r) :
    ((smallSet m r 1 0 p).filter fun e => fullVals p e = []) ∪
      ((smallSet m r 1 0 p).filter fun e => fullVals p e = [1]) =
      smallSet m r 1 0 p := by
  ext e
  simp only [mem_union, mem_filter]
  constructor
  · aesop
  · intro he
    have hc := small_pattern_one p e (smallSet_mem.mp he).1
    aesop

lemma smallSet_two_union (m r : ℕ) (p : Dev m r) :
    (((smallSet m r 2 1 p).filter fun e => fullVals p e = []) ∪
      ((smallSet m r 2 1 p).filter fun e => fullVals p e = [1])) ∪
      (((smallSet m r 2 1 p).filter fun e => fullVals p e = [2]) ∪
      ((smallSet m r 2 1 p).filter fun e => fullVals p e = [1,1])) =
      smallSet m r 2 1 p := by
  ext e
  simp only [mem_union, mem_filter]
  constructor
  · aesop
  · intro he
    have hc := small_pattern_two p e (smallSet_mem.mp he).1
    aesop

lemma endpoint_one_impossible_low (m r : ℕ) (hm : 14 ≤ m) (hr : r < m)
    (p : Dev m r) (hc : cut p < 7) (e : Dev m (1+r))
    (heS : e ∈ smallSet m r 1 0 p) (hf : fullVals p e = []) : False := by
  have he := (smallSet_mem.mp heS).1
  have ht : part p e = 1 := by
    rcases small_pattern_one p e he with h | h <;> simp_all
  have hc1 : cut p + 1 < m := by omega
  have hn := part_add_le_next p e he hc1
  rw [ht] at hn
  have hp2 : 2 ≤ p.val ⟨cut p+1, hc1⟩ := by
    have hp := val_pos_at_cut p (by omega)
    omega
  have htail := tail_value_mul_le_sum p hc1
  have hmul : (m-(cut p+1))*2 ≤ (m-(cut p+1))*p.val ⟨cut p+1, hc1⟩ :=
    Nat.mul_le_mul_left _ hp2
  omega

lemma two_empty_impossible_low (m r : ℕ) (hm : 14 ≤ m) (hr : r < m)
    (p : Dev m r) (hc : cut p < 8) (e : Dev m (2+r))
    (heS : e ∈ smallSet m r 2 1 p) (hf : fullVals p e = []) : False := by
  have he := (smallSet_mem.mp heS).1
  have ht : part p e = 2 := by
    rcases small_pattern_two p e he with h | h | h | h <;> simp_all
  have hc1 : cut p + 1 < m := by omega
  have hn := part_add_le_next p e he hc1
  rw [ht] at hn
  have hp3 : 3 ≤ p.val ⟨cut p+1, hc1⟩ := by
    have hp := val_pos_at_cut p (by omega)
    omega
  have htail := tail_value_mul_le_sum p hc1
  have hmul : (m-(cut p+1))*3 ≤ (m-(cut p+1))*p.val ⟨cut p+1, hc1⟩ :=
    Nat.mul_le_mul_left _ hp3
  omega

lemma two_two_impossible_low (m r : ℕ) (hm : 14 ≤ m) (hr : r < m)
    (p : Dev m r) (hc : cut p < 8) (e : Dev m (2+r))
    (heS : e ∈ smallSet m r 2 1 p) (hf : fullVals p e = [2]) : False := by
  have he := (smallSet_mem.mp heS).1
  have ht : part p e = 0 := by
    rcases small_pattern_two p e he with h | h | h | h <;> simp_all
  have hcm : cut p < m := by omega
  have hp2 := full_member_le_pcut_of_part_zero (x:=2) p e he (by rw [hf]; simp) ht hcm
  have htail := tail_value_mul_le_sum p hcm
  have hmul : (m-cut p)*2 ≤ (m-cut p)*p.val ⟨cut p,hcm⟩ := Nat.mul_le_mul_left _ hp2
  omega

lemma two_one_forces_cut_seven (m r : ℕ) (hm : 14 ≤ m) (hr : r < m)
    (p : Dev m r) (hc : cut p < 8) (e : Dev m (2+r))
    (heS : e ∈ smallSet m r 2 1 p) (hf : fullVals p e = [1]) : cut p = 7 := by
  have he := (smallSet_mem.mp heS).1
  have ht : part p e = 1 := by
    rcases small_pattern_two p e he with h | h | h | h <;> simp_all
  have hz := zeros_count_bound p e he (smallSet_mem.mp heS).2 (Or.inl (by simp [hf]))
  have hc1 : cut p + 1 < m := by omega
  have hn := part_add_le_next p e he hc1
  rw [ht] at hn
  have hp2 : 2 ≤ p.val ⟨cut p+1,hc1⟩ := by
    have hp := val_pos_at_cut p (by omega)
    omega
  have htail := tail_value_mul_le_sum p hc1
  have hmul : (m-(cut p+1))*2 ≤ (m-(cut p+1))*p.val ⟨cut p+1,hc1⟩ := Nat.mul_le_mul_left _ hp2
  simp [hf] at hz
  omega

end Dev

namespace Dev

lemma filter_fullVals_disjoint {m r H q : ℕ} (p : Dev m r) {L K : List ℕ} (hne : L ≠ K) :
    Disjoint ((smallSet m r H q p).filter fun e => fullVals p e = L)
      ((smallSet m r H q p).filter fun e => fullVals p e = K) := by
  rw [Finset.disjoint_left]
  intro e he he'
  exact hne ((mem_filter.mp he).2.symm.trans (mem_filter.mp he').2)

lemma small_one_bound (m r : ℕ) (hm : 14 ≤ m) (hr : r < m) (p : Dev m r) :
    (∑ e ∈ smallSet m r 1 0 p, e.weight 1) ≤ (1/3 : ℚ) * p.weight 1 := by
  let T0 := (smallSet m r 1 0 p).filter fun e => fullVals p e = []
  let T1 := (smallSet m r 1 0 p).filter fun e => fullVals p e = [1]
  have hd : Disjoint T0 T1 := filter_fullVals_disjoint p (by simp)
  have hdecomp : (∑ e ∈ smallSet m r 1 0 p, e.weight 1) =
      (∑ e ∈ T0, e.weight 1) + ∑ e ∈ T1, e.weight 1 := by
    rw [← Finset.sum_union hd, smallSet_one_union]
  rw [hdecomp]
  by_cases hc : 7 ≤ cut p
  · have h0 := sum_filter_fullVals_le (q:=0) p [] (fun e => e.weight 1)
      (p.weight 1 * (1/10 : ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        exact one_endpoint_bound_high p e (smallSet_mem.mp heS).1 hf
          (by rcases small_pattern_one p e (smallSet_mem.mp heS).1 with h|h <;> simp_all) hc)
    have h1 := sum_filter_fullVals_le (q:=0) p [1] (fun e => e.weight 1)
      (p.weight 1 * (1/8 : ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        exact one_block_bound_high p e (smallSet_mem.mp heS).1 hf
          (by rcases small_pattern_one p e (smallSet_mem.mp heS).1 with h|h <;> simp_all) hc)
    dsimp [T0, T1]
    calc
      _ ≤ p.weight 1 * (1/10 : ℚ) + p.weight 1 * (1/8 : ℚ) := add_le_add h0 h1
      _ = p.weight 1 * (9/40 : ℚ) := by ring
      _ ≤ p.weight 1 * (1/3 : ℚ) :=
        mul_le_mul_of_nonneg_left (by norm_num) (weight_pos 1 p).le
      _ = (1/3 : ℚ) * p.weight 1 := by ring
  · have hc' : cut p < 7 := by omega
    have hT0 : T0 = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      obtain ⟨e, he⟩ := hn
      exact endpoint_one_impossible_low m r hm hr p hc' e (mem_filter.mp he).1 (mem_filter.mp he).2
    rw [hT0]
    simp only [sum_empty, zero_add]
    have h1 := sum_filter_fullVals_le (q:=0) p [1] (fun e => e.weight 1)
      (p.weight 1 * (1/3 : ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        have hs := smallSet_mem.mp heS
        have ht : part p e = 0 := by rcases small_pattern_one p e hs.1 with h'|h' <;> simp_all
        have h := weight_le_pattern p e hs.1 (show 1=1+0 by omega) hs.2
        convert h using 1 <;>
          norm_num [pattern, hf, ht, Pattern.weight, Pattern.weightAux, rup, mul_comm])
    dsimp [T1]
    simpa [mul_comm] using h1

lemma small_two_bound (m r : ℕ) (hm : 14 ≤ m) (hr : r < m) (p : Dev m r) :
    (∑ e ∈ smallSet m r 2 1 p, (2:ℚ) * e.weight 1) ≤ (1/10 : ℚ) * p.weight 1 := by
  let T0 := (smallSet m r 2 1 p).filter fun e => fullVals p e = []
  let T1 := (smallSet m r 2 1 p).filter fun e => fullVals p e = [1]
  let T2 := (smallSet m r 2 1 p).filter fun e => fullVals p e = [2]
  let T11 := (smallSet m r 2 1 p).filter fun e => fullVals p e = [1,1]
  have hd01 : Disjoint T0 T1 := filter_fullVals_disjoint p (by simp)
  have hd211 : Disjoint T2 T11 := filter_fullVals_disjoint p (by simp)
  have hd : Disjoint (T0 ∪ T1) (T2 ∪ T11) := by
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [mem_union] at he he'
    rcases he with he|he <;> rcases he' with he'|he' <;>
      have := (mem_filter.mp he).2.symm.trans (mem_filter.mp he').2 <;> simp_all
  have hdecomp : (∑ e ∈ smallSet m r 2 1 p, (2:ℚ)*e.weight 1) =
      ((∑ e ∈ T0, (2:ℚ)*e.weight 1) + ∑ e ∈ T1, (2:ℚ)*e.weight 1) +
      ((∑ e ∈ T2, (2:ℚ)*e.weight 1) + ∑ e ∈ T11, (2:ℚ)*e.weight 1) := by
    rw [← Finset.sum_union hd01, ← Finset.sum_union hd211, ← Finset.sum_union hd,
      smallSet_two_union]
  rw [hdecomp]
  by_cases hc : 8 ≤ cut p
  · have h0 := sum_filter_fullVals_le (q:=1) p [] (fun e => (2:ℚ)*e.weight 1)
      (p.weight 1*(1/66:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        exact two_empty_bound_high p e (smallSet_mem.mp heS).1 hf
          (by rcases small_pattern_two p e (smallSet_mem.mp heS).1 with h|h|h|h <;> simp_all) hc)
    have h1 := sum_filter_fullVals_le (q:=1) p [1] (fun e => (2:ℚ)*e.weight 1)
      (p.weight 1*(2/99:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        have ht : part p e = 1 := by rcases small_pattern_two p e (smallSet_mem.mp heS).1 with h|h|h|h <;> simp_all
        have hh := two_one_bound_at (c:=8) p e (smallSet_mem.mp heS).1 hf ht (by omega) (by omega)
        norm_num [rup] at hh ⊢
        exact hh)
    have h2 := sum_filter_fullVals_le (q:=1) p [2] (fun e => (2:ℚ)*e.weight 1)
      (p.weight 1*(1/45:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        exact two_two_bound_high p e (smallSet_mem.mp heS).1 hf
          (by rcases small_pattern_two p e (smallSet_mem.mp heS).1 with h|h|h|h <;> simp_all) hc)
    have h11 := sum_filter_fullVals_le (q:=1) p [1,1] (fun e => (2:ℚ)*e.weight 1)
      (p.weight 1*(1/36:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
        intro e heS hf
        have ht : part p e = 0 := by rcases small_pattern_two p e (smallSet_mem.mp heS).1 with h|h|h|h <;> simp_all
        have hh := two_eleven_bound_at (A:=7) p e (smallSet_mem.mp heS).1 hf ht (by omega)
        norm_num [rup] at hh ⊢
        exact hh)
    dsimp [T0,T1,T2,T11]
    calc
      _ ≤ (p.weight 1*(1/66:ℚ)+p.weight 1*(2/99:ℚ))+
          (p.weight 1*(1/45:ℚ)+p.weight 1*(1/36:ℚ)) :=
        add_le_add (add_le_add h0 h1) (add_le_add h2 h11)
      _ = p.weight 1 * (169/1980 : ℚ) := by ring
      _ ≤ p.weight 1 * (1/10 : ℚ) :=
        mul_le_mul_of_nonneg_left (by norm_num) (weight_pos 1 p).le
      _ = (1/10:ℚ)*p.weight 1 := by ring
  · have hc' : cut p < 8 := by omega
    have hT0 : T0 = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      obtain ⟨e, he⟩ := hn
      exact two_empty_impossible_low m r hm hr p hc' e (mem_filter.mp he).1 (mem_filter.mp he).2
    have hT2 : T2 = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      obtain ⟨e, he⟩ := hn
      exact two_two_impossible_low m r hm hr p hc' e (mem_filter.mp he).1 (mem_filter.mp he).2
    rw [hT0, hT2]
    simp only [sum_empty, zero_add]
    by_cases hne : T1.Nonempty
    · obtain ⟨e0, he0⟩ := hne
      have hcut := two_one_forces_cut_seven m r hm hr p hc' e0
        (mem_filter.mp he0).1 (mem_filter.mp he0).2
      have h1 := sum_filter_fullVals_le (q:=1) p [1] (fun e => (2:ℚ)*e.weight 1)
        (p.weight 1*(1/40:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
          intro e heS hf
          have ht : part p e = 1 := by rcases small_pattern_two p e (smallSet_mem.mp heS).1 with h|h|h|h <;> simp_all
          have hh := two_one_bound_at (c:=7) p e (smallSet_mem.mp heS).1 hf ht (by omega) (by omega)
          norm_num [rup] at hh ⊢
          exact hh)
      have h11 := sum_filter_fullVals_le (q:=1) p [1,1] (fun e => (2:ℚ)*e.weight 1)
        (p.weight 1*(1/28:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
          intro e heS hf
          have ht : part p e = 0 := by rcases small_pattern_two p e (smallSet_mem.mp heS).1 with h|h|h|h <;> simp_all
          have hh := two_eleven_bound_at (A:=6) p e (smallSet_mem.mp heS).1 hf ht (by omega)
          norm_num [rup] at hh ⊢
          exact hh)
      dsimp [T1,T11]
      calc
        _ ≤ p.weight 1*(1/40:ℚ)+p.weight 1*(1/28:ℚ) := add_le_add h1 h11
        _ = p.weight 1 * (17/280 : ℚ) := by ring
        _ ≤ p.weight 1 * (1/10 : ℚ) :=
        mul_le_mul_of_nonneg_left (by norm_num) (weight_pos 1 p).le
        _ = (1/10:ℚ)*p.weight 1 := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [sum_empty, zero_add]
      have h11 := sum_filter_fullVals_le (q:=1) p [1,1] (fun e => (2:ℚ)*e.weight 1)
        (p.weight 1*(1/10:ℚ)) (mul_nonneg (weight_pos 1 p).le (by norm_num)) (by
          intro e heS hf
          have hs := smallSet_mem.mp heS
          have ht : part p e = 0 := by rcases small_pattern_two p e hs.1 with h'|h'|h'|h' <;> simp_all
          have h := weight_le_pattern p e hs.1 (show 2=1+1 by omega) hs.2
          have hm : (2:ℚ)*e.weight 1 ≤ (2:ℚ)*((pattern p e).weight 3*p.weight 1) := mul_le_mul_of_nonneg_left h (by norm_num)
          norm_num [pattern, hf, ht, Pattern.weight, Pattern.weightAux, rup] at hm ⊢
          have hp := (weight_pos 1 p).le
          nlinarith [hm])
      dsimp [T11]
      simpa [mul_comm] using h11

end Dev

namespace Dev

lemma source_q_le_smallSet (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m)
    (p : Dev m r) :
    (∑ d : Dev (m-1) (l+m-1+r),
      if srcQ l m r hl hm d = q ∧ nearMap l m r d = p then
        ((l+m-1).factorial : ℚ) * d.weight l else 0) ≤
      ∑ e ∈ smallSet m r (l+q) q p, ((l+q).factorial : ℚ) * e.weight l := by
  classical
  let D : Finset (Dev (m-1) (l+m-1+r)) := Finset.univ.filter fun d =>
    srcQ l m r hl hm d = q ∧ nearMap l m r d = p
  let F : Dev (m-1) (l+m-1+r) → Dev m (l+q+r) :=
    fixedLiftDefault l m r q hl hm
  let T : Dev m (l+q+r) → ℚ := fun e =>
    if downN (l+q) r e = p ∧ (∀ i : Fin m, i.val ≤ q → e.val i = 0)
    then ((l+q).factorial : ℚ) * e.weight l else 0
  have hFinj : Set.InjOn F D := by
    intro d hd d' hd' he
    have hdf := hd
    have hd'f := hd'
    dsimp [D] at hdf hd'f
    have hq := (mem_filter.mp hdf).2.1
    have hq' := (mem_filter.mp hd'f).2.1
    dsimp [F] at he
    rw [fixedLiftDefault_eq l m r q hl hm d hq,
      fixedLiftDefault_eq l m r q hl hm d' hq'] at he
    exact fixedLift_injective l m r q hl hm hq hq' he
  have hterm (d : Dev (m-1) (l+m-1+r)) (hd : d ∈ D) :
      T (F d) = ((l+m-1).factorial : ℚ) * d.weight l := by
    have hdf := hd
    dsimp [D] at hdf
    have hs := (mem_filter.mp hdf).2
    have hq := hs.1
    have hmap := hs.2
    have hF := fixedLiftDefault_eq l m r q hl hm d hq
    have hvalid : downN (l+q) r (F d) = p ∧
        (∀ i : Fin m, i.val ≤ q → (F d).val i = 0) := by
      constructor
      · change downN (l+q) r (fixedLiftDefault l m r q hl hm d) = p
        rw [hF, fixedLift_downN l m r q hl hm d hq, hmap]
      · intro i hi
        change (fixedLiftDefault l m r q hl hm d).val i = 0
        rw [hF]
        exact fixedLift_zero l m r q hl hm d hq i hi
    dsimp [F] at hvalid
    dsimp [T, F]
    rw [if_pos hvalid, hF, fixedLift_weight l m r q hl hm d hq]
    have hw := lift_weight l m r hm d
    have hLH := liftH_eq_srcQ l m r hl hm d
    rw [hq] at hLH
    have hfac : (((liftH l m r d).factorial : ℕ) : ℚ) =
        (((l+q).factorial : ℕ) : ℚ) := congrArg (fun n : ℕ => (n.factorial : ℚ)) hLH
    calc
      ((l+q).factorial : ℚ) * (lift l m r d).weight l =
          ((liftH l m r d).factorial : ℚ) * (lift l m r d).weight l :=
        congrArg (fun z : ℚ => z * (lift l m r d).weight l) hfac.symm
      _ = _ := hw.symm
  have himage : ∑ e ∈ D.image F, T e =
      ∑ d ∈ D, ((l+m-1).factorial : ℚ) * d.weight l := by
    rw [Finset.sum_image hFinj]
    apply Finset.sum_congr rfl
    exact hterm
  have hle : (∑ e ∈ D.image F, T e) ≤ ∑ e : Dev m (l+q+r), T e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro e he hne
    dsimp [T]
    split_ifs
    · exact mul_nonneg (by positivity) (weight_pos _ _).le
    · norm_num
  rw [himage] at hle
  have hsource : (∑ d : Dev (m-1) (l+m-1+r),
      if srcQ l m r hl hm d = q ∧ nearMap l m r d = p then
        ((l+m-1).factorial : ℚ) * d.weight l else 0) =
      ∑ d ∈ D, ((l+m-1).factorial : ℚ) * d.weight l := by
    dsimp [D]
    rw [← Finset.sum_filter]
  rw [hsource]
  have hsmall : (∑ e : Dev m (l+q+r), T e) =
      ∑ e ∈ smallSet m r (l+q) q p, ((l+q).factorial : ℚ) * e.weight l := by
    dsimp [T, smallSet]
    rw [← Finset.sum_filter]
  rw [hsmall] at hle
  exact hle

end Dev

lemma sum_range_shift_CB (l N : ℕ) :
    (∑ q ∈ range N, CB (l+q)) = ∑ H ∈ Ico l (l+N), CB H := by
  refine Finset.sum_bij (fun q _ => l+q) (fun q hq => by
      simp only [mem_range] at hq
      simp only [mem_Ico]
      omega) (fun q hq q' hq' he => by dsimp at he; omega) (fun H hH => ?_) (fun q hq => rfl)
  simp only [mem_Ico] at hH
  refine ⟨H-l, ?_, ?_⟩
  · simp only [mem_range]
    omega
  · exact Nat.add_sub_of_le hH.1

lemma CB_nonneg (H : ℕ) : (0:ℚ) ≤ CB H :=
  mul_nonneg (by positivity) (gg_pos _ _).le

lemma sum_shift_CB_le_Icc (l N a : ℕ) (ha : a ≤ l) :
    (∑ q ∈ range N, CB (l+q)) ≤ ∑ H ∈ Icc a (l+N), CB H := by
  rw [sum_range_shift_CB]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro H hH
    simp only [mem_Ico, mem_Icc] at hH ⊢
    omega
  · intro H hH hn
    exact CB_nonneg H

lemma CB_two : CB 2 = (7/20 : ℚ) := by
  norm_num [CB, gg, rup, Finset.sum_range_succ]

lemma CB_from_two_bound (N : ℕ) (hN : 2 ≤ N) :
    (∑ H ∈ Icc 2 N, CB H) < (91/100 : ℚ) := by
  have hu : {2} ∪ Icc 3 N = Icc 2 N := by
    ext H
    simp only [mem_union, mem_singleton, mem_Icc]
    omega
  have hd : Disjoint ({2} : Finset ℕ) (Icc 3 N) := by
    simp [Finset.disjoint_left]
  rw [← hu, sum_union hd]
  simp only [sum_singleton, CB_two]
  have ht := CB_tail_bound N
  norm_num at ht ⊢
  linarith

namespace Dev

noncomputable def sourceTerm (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m) (p : Dev m r) : ℚ :=
  ∑ d : Dev (m-1) (l+m-1+r),
    if srcQ l m r hl hm d = q ∧ nearMap l m r d = p then
      ((l+m-1).factorial : ℚ) * d.weight l else 0

lemma source_sum_eq_sum_q (l m r : ℕ) (hl : 0 < l) (hm : 1 < m) (p : Dev m r) :
    (∑ d : Dev (m-1) (l+m-1+r),
      if nearMap l m r d = p then ((l+m-1).factorial : ℚ)*d.weight l else 0) =
      ∑ q ∈ range (m-1), sourceTerm l m r q hl hm p := by
  classical
  let D : Finset (Dev (m-1) (l+m-1+r)) := Finset.univ
  let f : Dev (m-1) (l+m-1+r) → ℕ := srcQ l m r hl hm
  let g : Dev (m-1) (l+m-1+r) → ℚ := fun d =>
    if nearMap l m r d = p then ((l+m-1).factorial : ℚ)*d.weight l else 0
  have hmap : ∀ d ∈ D, f d ∈ range (m-1) := by
    intro d hd
    exact mem_range.mpr (srcQ_lt l m r hl hm d)
  have hfib := Finset.sum_fiberwise_of_maps_to hmap g
  rw [show (∑ d : Dev (m-1) (l+m-1+r),
      if nearMap l m r d = p then ((l+m-1).factorial : ℚ)*d.weight l else 0) =
      ∑ d ∈ D, g d by simp [D,g]]
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp [D,f,g,sourceTerm]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_filter]

lemma sourceTerm_nonneg (l m r q : ℕ) (hl : 0 < l) (hm : 1 < m) (p : Dev m r) :
    0 ≤ sourceTerm l m r q hl hm p := by
  unfold sourceTerm
  apply Finset.sum_nonneg
  intro d hd
  split_ifs
  · exact mul_nonneg (by positivity) (weight_pos _ _).le
  · norm_num

lemma near_fiber_bound_l_ge_two (l m r : ℕ) (hl : 2 ≤ l) (hm : 1 < m) (p : Dev m r) :
    (∑ d : Dev (m-1) (l+m-1+r),
      if nearMap l m r d = p then ((l+m-1).factorial : ℚ)*d.weight l else 0) <
      p.weight l := by
  have hp := weight_pos l p
  rw [source_sum_eq_sum_q l m r (by omega) hm p]
  have hq : (∑ q ∈ range (m-1), sourceTerm l m r q (by omega) hm p) ≤
      (∑ q ∈ range (m-1), CB (l+q)) * p.weight l := by
    calc
      _ ≤ ∑ q ∈ range (m-1), CB (l+q)*p.weight l := by
        apply Finset.sum_le_sum
        intro q hqm
        exact source_q_fiber_bound l m r q (by omega) hm p
      _ = _ := by rw [Finset.sum_mul]
  have hcoef0 := sum_shift_CB_le_Icc l (m-1) 2 hl
  have hcoef1 := CB_from_two_bound (l+(m-1)) (by omega)
  have hcoef : (∑ q ∈ range (m-1), CB (l+q)) < 1 := lt_of_le_of_lt hcoef0 (lt_trans hcoef1 (by norm_num))
  calc
    _ ≤ (∑ q ∈ range (m-1), CB (l+q))*p.weight l := hq
    _ < 1*p.weight l := mul_lt_mul_of_pos_right hcoef hp
    _ = _ := one_mul _

end Dev

lemma sum_Ico_shift_CB_one (N : ℕ) :
    (∑ q ∈ Ico 2 N, CB (1+q)) = ∑ H ∈ Ico 3 (N+1), CB H := by
  refine Finset.sum_bij (fun q _ => q+1) (fun q hq => by
      simp only [mem_Ico] at hq ⊢
      omega) (fun q hq q' hq' he => by dsimp at he; omega) (fun H hH => ?_) (fun q hq => by dsimp; congr 1; omega)
  simp only [mem_Ico] at hH
  refine ⟨H-1, ?_, ?_⟩
  · simp only [mem_Ico]
    omega
  · dsimp
    omega

lemma sum_Ico_CB_one_tail_bound (N : ℕ) :
    (∑ q ∈ Ico 2 N, CB (1+q)) < (14/25 : ℚ) := by
  rw [sum_Ico_shift_CB_one]
  have hle : (∑ H ∈ Ico 3 (N+1), CB H) ≤ ∑ H ∈ Icc 3 (N+1), CB H := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro H hH
      simp only [mem_Ico, mem_Icc] at hH ⊢
      omega
    · intro H hH hn
      exact CB_nonneg H
  exact lt_of_le_of_lt hle (CB_tail_bound (N+1))

namespace Dev

lemma sourceTerm_zero_bound (m r : ℕ) (hm : 14 ≤ m) (hr : r < m) (p : Dev m r) :
    sourceTerm 1 m r 0 (by omega) (by omega) p ≤ (1/3 : ℚ)*p.weight 1 := by
  have hs := source_q_le_smallSet 1 m r 0 (by omega) (by omega) p
  have hb := small_one_bound m r hm hr p
  have hb' : (∑ e ∈ smallSet m r (1+0) 0 p, ((1+0).factorial:ℚ)*e.weight 1) ≤
      (1/3:ℚ)*p.weight 1 := by simpa using hb
  have hmEq : 1+m-1 = m := by omega
  simpa [sourceTerm, hmEq] using le_trans hs hb'

lemma sourceTerm_one_bound (m r : ℕ) (hm : 14 ≤ m) (hr : r < m) (p : Dev m r) :
    sourceTerm 1 m r 1 (by omega) (by omega) p ≤ (1/10 : ℚ)*p.weight 1 := by
  have hs := source_q_le_smallSet 1 m r 1 (by omega) (by omega) p
  have hb := small_two_bound m r hm hr p
  have hb' : (∑ e ∈ smallSet m r (1+1) 1 p, ((1+1).factorial:ℚ)*e.weight 1) ≤
      (1/10:ℚ)*p.weight 1 := by simpa using hb
  have hmEq : 1+m-1 = m := by omega
  simpa [sourceTerm, hmEq] using le_trans hs hb'

lemma near_fiber_bound_l_one (m r : ℕ) (hm : 14 ≤ m) (hr : r < m) (p : Dev m r) :
    (∑ d : Dev (m-1) (1+m-1+r),
      if nearMap 1 m r d = p then ((1+m-1).factorial : ℚ)*d.weight 1 else 0) <
      p.weight 1 := by
  have hm1 : 1 < m := by omega
  have hp := weight_pos 1 p
  rw [source_sum_eq_sum_q 1 m r (by omega) hm1 p]
  let f : ℕ → ℚ := fun q => sourceTerm 1 m r q (by omega) hm1 p
  have hu : {0,1} ∪ Ico 2 (m-1) = range (m-1) := by
    ext q
    simp only [mem_union, mem_insert, mem_singleton, mem_Ico, mem_range]
    omega
  have hd : Disjoint ({0,1} : Finset ℕ) (Ico 2 (m-1)) := by
    simp [Finset.disjoint_left]
  rw [← hu, sum_union hd]
  have hsmall : (∑ q ∈ ({0,1} : Finset ℕ), f q) ≤
      ((1/3 : ℚ)+(1/10 : ℚ))*p.weight 1 := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    dsimp [f]
    have h0 := sourceTerm_zero_bound m r hm hr p
    have h1 := sourceTerm_one_bound m r hm hr p
    calc
      _ ≤ (1/3:ℚ)*p.weight 1+(1/10:ℚ)*p.weight 1 := add_le_add h0 h1
      _ = _ := by ring
  have htail : (∑ q ∈ Ico 2 (m-1), f q) < (14/25 : ℚ)*p.weight 1 := by
    have hq : (∑ q ∈ Ico 2 (m-1), f q) ≤
        (∑ q ∈ Ico 2 (m-1), CB (1+q))*p.weight 1 := by
      calc
        _ ≤ ∑ q ∈ Ico 2 (m-1), CB (1+q)*p.weight 1 := by
          apply Finset.sum_le_sum
          intro q hq
          dsimp [f]
          exact source_q_fiber_bound 1 m r q (by omega) hm1 p
        _ = _ := by rw [Finset.sum_mul]
    have hc := sum_Ico_CB_one_tail_bound (m-1)
    exact lt_of_le_of_lt hq (mul_lt_mul_of_pos_right hc hp)
  calc
    (∑ q ∈ ({0,1} : Finset ℕ), f q) + ∑ q ∈ Ico 2 (m-1), f q <
        ((1/3:ℚ)+(1/10:ℚ))*p.weight 1 + (14/25:ℚ)*p.weight 1 :=
      add_lt_add_of_le_of_lt hsmall htail
    _ = (149/150:ℚ)*p.weight 1 := by ring
    _ < 1*p.weight 1 := mul_lt_mul_of_pos_right (by norm_num) hp
    _ = _ := one_mul _

end Dev
lemma nearMap_fiber_bound (l m r : ℕ) (hl : 0 < l) (hm : 1 < m) (hr : r < m)
    (hlarge : 2 ≤ l ∨ 14 ≤ m) (p : Dev m r) :
    (∑ d : Dev (m-1) (l+m-1+r), if Dev.nearMap l m r d = p then
      ((l+m-1).factorial : ℚ) * d.weight l else 0) < p.weight l := by
  by_cases hl2 : 2 ≤ l
  · exact Dev.near_fiber_bound_l_ge_two l m r hl2 hm p
  · have hl1 : l = 1 := by omega
    subst l
    have hm14 : 14 ≤ m := hlarge.resolve_left hl2
    exact Dev.near_fiber_bound_l_one m r hm14 hr p

lemma dev_nonempty (m r : ℕ) (hm : 0 < m) : Nonempty (Dev m r) := by
  let v : Fin m → ℕ := fun i => if i.val = m-1 then r else 0
  refine ⟨⟨v, ?_, ?_⟩⟩
  · cases m with
    | zero => omega
    | succ m =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      simp [v]
      split_ifs <;> omega
  · rw [Fin.sum_univ_eq_sum_range (fun i => if i = m-1 then r else 0) m]
    rw [Finset.sum_eq_single (m-1)]
    · simp
    · intro b hb hne
      simp [hne]
    · simp
      omega

lemma near_layer (l m r : ℕ) (hl : 0 < l) (hm : 0 < m) (hr : r < m)
    (hlarge : 2 ≤ l ∨ 14 ≤ m) :
    layer l (m-1) (minSum l m + r) < layer l m (minSum l m + r) := by
  by_cases hm1 : m = 1
  · subst m
    have hr0 : r = 0 := by omega
    subst r
    norm_num [minSum, tri]
    rw [layer_zero l l (by omega)]
    exact layer_one_pos l l hl (by omega)
  have hm2 : 1 < m := by omega
  have hnorm : ((l+m-1).factorial : ℚ) * Dev.total l (m-1) (l+m-1+r) <
      Dev.total l m r := by
    unfold Dev.total
    rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Dev (m-1) (l+m-1+r)))
      (Dev.nearMap l m r) (fun d => ((l+m-1).factorial : ℚ) * d.weight l)]
    apply Finset.sum_lt_sum_of_nonempty
    · letI : Nonempty (Dev m r) := dev_nonempty m r hm
      exact Finset.univ_nonempty
    · intro p hp
      rw [Finset.sum_filter]
      simpa using nearMap_fiber_bound l m r hl hm2 hr hlarge p
  have hms : m = (m-1)+1 := by omega
  have hrec := minSum_succ_direct l (m-1)
  rw [← hms] at hrec
  have hsrc : minSum l m + r = minSum l (m-1) + (l+m-1+r) := by
    rw [hrec]
    omega
  rw [hsrc, Prof.layer_dev, show minSum l (m-1) + (l+m-1+r) = minSum l m+r by omega]
  rw [Prof.layer_dev]
  have hbase : (∏ i : Fin m, (1 / ((l+i.val).factorial : ℚ))) =
      (∏ i : Fin (m-1), (1 / ((l+i.val).factorial : ℚ))) *
        (1 / ((l+m-1).factorial : ℚ)) := by
    rw [Fin.prod_univ_eq_prod_range
      (fun i : ℕ => (1 / ((l+i).factorial : ℚ))) m]
    rw [Fin.prod_univ_eq_prod_range
      (fun i : ℕ => (1 / ((l+i).factorial : ℚ))) (m-1)]
    rw [hms, Finset.prod_range_succ]
    congr 1
  rw [hbase]
  have hbs : 0 < (∏ i : Fin (m-1), (1 / ((l+i.val).factorial : ℚ))) := by positivity
  have hf : 0 < ((l+m-1).factorial : ℚ) := by positivity
  let B : ℚ := ∏ i : Fin (m-1), (1 / ((l+i.val).factorial : ℚ))
  let F : ℚ := (l+m-1).factorial
  let X : ℚ := Dev.total l (m-1) (l+m-1+r)
  let Y : ℚ := Dev.total l m r
  have hBF : 0 < B * (1/F) := by dsimp [B, F]; positivity
  have hs := mul_lt_mul_of_pos_left hnorm hBF
  have hcancel : (B * (1/F)) * (F * X) = B * X := by
    have hFn : F ≠ 0 := by dsimp [F]; positivity
    field_simp
  rw [hcancel] at hs
  change B * X < B * (1/F) * Y
  simpa [Y] using hs

lemma layer_strict_general (l j n : ℕ) (hl : 0 < l)
    (hscope : 2 ≤ l ∨ 103 < n) (hfeas : minSum l (j+1) ≤ n) :
    layer l j n < layer l (j+1) n := by
  induction hgap : n + 1 - l using Nat.strong_induction_on generalizing l j n with
  | h gap ih =>
    let m := j+1
    have hfeasm : minSum l m ≤ n := by simpa [m] using hfeas
    by_cases hm1 : m = 1
    · have hj : j = 0 := by omega
      subst j
      have hmin1 : minSum l 1 = l := by
        rw [minSum_eq_sum_range]
        simp
      have hln : l ≤ n := by simpa [hmin1] using hfeas
      rw [layer_zero l n (by omega)]
      exact layer_one_pos l n hl hln
    · have hm : 0 < m := by omega
      by_cases hnear : n < minSum l m + m
      · let r := n - minSum l m
        have hr : r < m := by dsimp [r]; omega
        have hnrep : n = minSum l m + r := by dsimp [r]; omega
        have hlarge : 2 ≤ l ∨ 14 ≤ m := by
          rcases hscope with hscope | hn
          · exact Or.inl hscope
          · by_cases hl2 : 2 ≤ l
            · exact Or.inl hl2
            · right
              by_contra hsmall
              have hmlt : m < 14 := Nat.lt_of_not_ge hsmall
              have hl1 : l = 1 := by omega
              have hmle : m ≤ 13 := by omega
              have httri : tri (m-1) ≤ 78 := by
                calc
                  tri (m-1) ≤ tri 12 := tri_strictMono.monotone (by omega)
                  _ = 78 := by norm_num [tri]
              have ht : minSum 1 m + m ≤ 104 := by
                unfold minSum
                omega
              rw [hl1] at hnear
              omega
        simpa [m, hnrep] using near_layer l m r hl hm hr hlarge
      · have hmrec : minSum l m = minSum (l+1) (m-1) + l := by
          have hh := minSum_succ_k l (m-1)
          rw [← show m = (m-1)+1 by omega] at hh
          exact hh
        have hln : l ≤ n := by
          rw [hmrec] at hfeasm
          omega
        have hnext : minSum (l+1) m ≤ n := by rw [minSum_succ_l]; omega
        have hgap1 : n + 1 - (l+1) < gap := by omega
        have hA := ih _ hgap1 (l+1) (m-1) n (by omega) (Or.inl (by omega)) (by
          simpa [m] using hnext) rfl
        have hincfeas : minSum (l+1) (m-1) ≤ n-l := by
          rw [hmrec] at hfeasm
          omega
        have hgap2 : (n-l)+1-(l+1) < gap := by omega
        have hB := ih _ hgap2 (l+1) (m-2) (n-l) (by omega) (Or.inl (by omega)) (by
          have : m-2+1 = m-1 := by omega
          simpa [this] using hincfeas) rfl
        have hj1 : j = (m-2)+1 := by omega
        rw [hj1]
        rw [show (m-2)+1+1 = (m-1)+1 by omega]
        rw [layer_succ_rec l (m-2) n hl hln, layer_succ_rec l (m-1) n hl hln]
        have hw : 0 < (1 / (l.factorial : ℚ)) := by positivity
        have hmidx : m-2+1 = m-1 := by omega
        have hA' : layer (l+1) (m-2+1) n < layer (l+1) (m-1+1) n := by
          simpa [hmidx] using hA
        have hBw : (1 / (l.factorial : ℚ)) * layer (l+1) (m-2) (n-l) <
            (1 / (l.factorial : ℚ)) * layer (l+1) (m-1) (n-l) := by
          have := mul_lt_mul_of_pos_left hB hw
          simpa [hmidx] using this
        nlinarith

lemma coeff_eq_altSum (n m : ℕ) (hmn : m ≤ n) (hupper : n < tri (m+1)) :
    (PP n).coeff n = altSum (layer 1 · n) m := by
  rw [coeff_eq_layers]
  unfold altSum
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [mem_range] at hx ⊢
    omega
  intro j hj hnot
  have hjm : m < j := by simp_all
  change (-1 : ℚ)^j * layer 1 j n = 0
  rw [layer_eq_zero_of_tri_lt 1 j n (by omega) (by
    have ht := tri_strictMono.monotone (show m+1 ≤ j by omega)
    exact lt_of_lt_of_le hupper ht)]
  simp

lemma coeff_interval_sign (n m : ℕ) (hn : 103 < n)
    (hlo : tri m ≤ n) (hhi : n < tri (m+1)) :
    0 < (-1 : ℚ)^m * (PP n).coeff n := by
  have hm : 0 < m := by
    by_contra h; simp_all [tri]
  have hmn : m ≤ n := le_trans (le_tri m hm) (by simpa [tri] using hlo)
  rw [coeff_eq_altSum n m hmn hhi]
  apply altSum_sign
  · intro j hj
    exact layer_nonneg 1 j n
  · exact layer_pos_of_tri_le m n hm hlo
  · intro j hj
    apply layer_strict_general 1 j n (by omega) (Or.inr hn)
    have ht := tri_strictMono.monotone (show j+1 ≤ m by omega)
    have hmin : minSum 1 (j+1) = tri (j+1) := by
      unfold minSum
      simp only [Nat.mul_one, Nat.add_sub_cancel]
      rw [tri_succ]
      omega
    rw [hmin]
    exact le_trans ht hlo

lemma ib_interval_sign (n m : ℕ) (hn : 103 < n)
    (hlo : tri m ≤ n) (hhi : n < tri (m+1)) :
    0 < (-1 : ℚ)^m * (ib n n : ℚ) := by
  rw [ib_cast_coeff]
  have hc := coeff_interval_sign n m hn hlo hhi
  have hf : 0 < (n.factorial : ℚ) := by positivity
  nlinarith

lemma int_product_neg_iff_pow_ne {a b : ℤ} {i j : ℕ}
    (ha : 0 < (-1 : ℚ)^i * (a : ℚ))
    (hb : 0 < (-1 : ℚ)^j * (b : ℚ)) :
    a*b < 0 ↔ (-1 : ℚ)^i ≠ (-1 : ℚ)^j := by
  have hi := neg_one_pow_eq_or (R := ℚ) i
  have hj := neg_one_pow_eq_or (R := ℚ) j
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    rw [hi] at ha ⊢ <;> rw [hj] at hb ⊢ <;> norm_num at ha hb ⊢
  · exact mul_nonneg ha.le hb.le
  · exact mul_neg_of_pos_of_neg ha hb
  · exact mul_neg_of_neg_of_pos ha hb
  · exact mul_nonneg_of_nonpos_of_nonpos ha.le hb.le

lemma pow_pred_ne_iff (m : ℕ) :
    (-1 : ℚ)^m ≠ (-1 : ℚ)^(m-1) ↔ 0 < m := by
  by_cases hm : m = 0
  · simp [hm]
  · have : m = (m-1)+1 := by omega
    conv_lhs => lhs; rw [this, pow_succ]
    have hp : (-1 : ℚ)^(m-1) ≠ 0 := pow_ne_zero _ (by norm_num)
    constructor
    · omega
    · intro _ he
      apply hp
      nlinarith

lemma large_result (n : ℕ) (hn : 104 < n) :
    (ib n n * ib (n-1) (n-1) < 0 ↔ ∃ k, n = tri k) := by
  let m := triIdx n
  have hm := triIdx_spec n
  have hs1 := ib_interval_sign n m (by omega) hm.1 hm.2
  have hp := triIdx_pred n (by omega)
  let p := triIdx (n-1)
  have hps := triIdx_spec (n-1)
  have hs0 := ib_interval_sign (n-1) p (by omega) hps.1 hps.2
  rw [int_product_neg_iff_pow_ne hs1 hs0]
  rw [triangular_iff_left_endpoint n (by omega)]
  change ((-1 : ℚ)^m ≠ (-1 : ℚ)^p ↔ n = tri m)
  have hp' : p = if n = tri m then m-1 else m := by
    dsimp [p, m]
    exact hp
  by_cases he : n = tri m
  · have hm0 : 0 < m := by
      by_contra hz
      have hmm : m = 0 := by omega
      have ht0 : tri 0 = 0 := by norm_num [tri]
      rw [hmm, ht0] at he
      omega
    rw [if_pos he] at hp'
    rw [hp']
    rw [pow_pred_ne_iff]
    exact ⟨fun _ => he, fun _ => hm0⟩
  · rw [if_neg he] at hp'
    rw [hp']
    constructor
    · intro h
      exact (h rfl).elim
    · intro h
      exact (he h).elim


lemma full_result (n : ℕ) (hn : 0 < n) :
    (ib n n * ib (n-1) (n-1) < 0 ↔ ∃ k, n = tri k) := by
  by_cases hsmall : n ≤ 104
  · simpa [tri] using chk_sound 104 n check104 hn hsmall
  · exact large_result n (by omega)












/--
Conjectures: 1) a(n) differs in sign from a(n-1) iff n is a triangular number (checked up to n = 1225 = (50*51)/2)
The condition "differs in sign" for $a(n)$ and $a(n-1)$ is formalized as their product being strictly negative.
We only consider $n \ge 1$.
-/
theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  intro n hn
  rw [A_eq_ib n, A_eq_ib (n-1)]
  simpa [is_triangular, tri] using full_result n hn
