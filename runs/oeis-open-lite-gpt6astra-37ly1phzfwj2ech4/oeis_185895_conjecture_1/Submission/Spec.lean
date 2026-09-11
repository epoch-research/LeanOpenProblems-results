import FormalConjectures.Util.ProblemImports

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

/-!
## Sign proof

Write `level n r` for the sum of the positive weights `1 / ∏ k!` over
partitions of `n` into `r` distinct positive parts.  The key inequality is
`level n r < level n (r+1)` whenever `r+1` parts are possible.

To obtain it, insert the smallest missing part `t`, and subtract a total
of `t` from the remaining parts, from left to right, without destroying
strict increase.  Reverse moves at a target with initial segment
`1, ..., L` are indexed by the finite sets `patterns (L-t) t`.  Their total
weight is bounded by `fineBound L < 1`.  This bound uses exact rational
checks for `L < 12` and a uniform factorial estimate for larger `L`.
Pairing adjacent terms in the alternating sum then establishes the sign.
Finally, multinomial integrality identifies the rational coefficient with
its floor in the definition of `A185895`.
-/

open Finset Nat
namespace SignProof

-- A bound for the number and weight of inverse compression moves.
def crudeTerm (L t : ℕ) : ℚ :=
  (2 : ℚ)^t * (t.factorial : ℚ) / (max (t + 2) (L - t + 2) : ℕ)^t

def crudeBound (L : ℕ) : ℚ := ∑ t ∈ Finset.Icc 1 L, crudeTerm L t

def cubic (n : ℕ) (x : ℚ) : ℚ :=
  1 + n*x + (n:ℚ)*((n:ℚ)-1)/2*x^2 +
    (n:ℚ)*((n:ℚ)-1)*((n:ℚ)-2)/6*x^3

lemma cubic_coeff_nonneg (n : ℕ) :
    0 ≤ (n:ℚ)*((n:ℚ)-1)*((n:ℚ)-2) := by
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · have : (2:ℚ) ≤ (n+2:ℕ) := by exact_mod_cast (by omega : 2 ≤ n+2)
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)

lemma cubic_le_pow (n : ℕ) (x : ℚ) (hx : 0 ≤ x) : cubic n x ≤ (1+x)^n := by
  induction n with
  | zero => simp [cubic]
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+x by positivity)
    have hp := mul_nonneg (cubic_coeff_nonneg n) (show 0 ≤ x^4 by positivity)
    rw [pow_succ] at ⊢
    unfold cubic at *
    push_cast
    nlinarith

lemma cubic_lower (n : ℕ) :
    5*((n:ℚ)+1)/(2*((n:ℚ)+3)) ≤ cubic n (1/((n:ℚ)+2)) := by
  have hn : (0:ℚ) ≤ n := by positivity
  have h2 : (0:ℚ) < (n:ℚ)+2 := by positivity
  have h3 : (0:ℚ) < (n:ℚ)+3 := by positivity
  rw [div_le_iff₀ (by positivity : (0:ℚ) < 2*((n:ℚ)+3))]
  unfold cubic
  field_simp
  nlinarith [sq_nonneg (n:ℚ), pow_nonneg hn 3, pow_nonneg hn 4]

lemma factorial_step (n : ℕ) :
    5*((n:ℚ)+1)*((n:ℚ)+2)^n ≤ 2*((n:ℚ)+3)^(n+1) := by
  have h := (cubic_lower n).trans (cubic_le_pow n (1/((n:ℚ)+2)) (by positivity))
  have h2 : (0:ℚ) < (n:ℚ)+2 := by positivity
  have he : 1+1/((n:ℚ)+2) = ((n:ℚ)+3)/((n:ℚ)+2) := by field_simp; ring
  rw [he, div_pow, div_le_div_iff₀ (by positivity) (by positivity)] at h
  simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

lemma factorial_bound (n : ℕ) :
    (n.factorial : ℚ) * 5^n ≤ 2^n * ((n:ℚ)+2)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_left ih (show 0 ≤ 5*((n:ℚ)+1) by positivity)
    have h' := mul_le_mul_of_nonneg_left (factorial_step n)
      (show (0:ℚ) ≤ 2^n by positivity)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ (5:ℚ),
      pow_succ (2:ℚ)]
    convert h.trans (by convert h' using 1 <;> ring) using 1 <;> push_cast <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma crudeBound_small : ∀ L ∈ Finset.Icc 12 50, crudeBound L < 1 := by
  decide +kernel

lemma crudeTerm_mono (L t : ℕ) : crudeTerm (L+1) t ≤ crudeTerm L t := by
  unfold crudeTerm
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast (show max (t+2) (L-t+2) ≤ max (t+2) (L+1-t+2) from
    max_le_max (le_refl _) (by omega))

lemma crudeTerm_one (L : ℕ) (hL : 2 ≤ L) : crudeTerm L 1 = 2 / ((L:ℚ)+1) := by
  have he : max (1+2) (L-1+2) = L+1 := by omega
  simp [crudeTerm, he]

lemma crudeTerm_last (L : ℕ) : crudeTerm L L ≤ (4/5:ℚ)^L := by
  simp only [crudeTerm, Nat.sub_self, zero_add, max_eq_left (by omega : 2 ≤ L+2)]
  have h := factorial_bound L
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  calc
    2^L * (L.factorial : ℚ) * 5^L = 2^L * ((L.factorial : ℚ) * 5^L) := by ring
    _ ≤ 2^L * (2^L * ((L:ℚ)+2)^L) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4^L * ((L:ℚ)+2)^L := by rw [← mul_assoc, ← mul_pow]; norm_num

lemma geometric_le (L : ℕ) (hL : 50 ≤ L) :
    (4/5:ℚ)^(L+1) * ((L:ℚ)+1) * ((L:ℚ)+2) ≤ 2 := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have hLq : (50:ℚ) ≤ L := by exact_mod_cast hL
    have hh : (4/5:ℚ)*((L:ℚ)+3) ≤ (L:ℚ)+1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (4/5:ℚ)^(L+1)*((L:ℚ)+2) by positivity)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show L+1+1 = (L+1)+1 by omega, pow_succ]
    nlinarith

lemma crudeBound_step (L : ℕ) (hL : 50 ≤ L) : crudeBound (L+1) ≤ crudeBound L := by
  have h1 : 1 ∈ Finset.Icc 1 L := by simp; omega
  have he := Finset.sum_le_sum (s := (Finset.Icc 1 L).erase 1)
    (fun t _ => crudeTerm_mono L t)
  have e1 := Finset.sum_erase_add (Finset.Icc 1 L) (crudeTerm L) h1
  have e2 := Finset.sum_erase_add (Finset.Icc 1 L) (crudeTerm (L+1)) h1
  have hl := crudeTerm_last (L+1)
  have hg := geometric_le L hL
  rw [crudeTerm_one L (by omega)] at e1
  rw [crudeTerm_one (L+1) (by omega)] at e2
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, show (1:ℚ)+1=2 by norm_num] at e2
  have hpos : (0:ℚ) < ((L:ℚ)+1)*((L:ℚ)+2) := by positivity
  have hd : (4/5:ℚ)^(L+1) ≤ 2/((L:ℚ)+1)-2/((L:ℚ)+2) := by
    rw [le_sub_iff_add_le]
    field_simp
    nlinarith [hg]
  unfold crudeBound
  rw [Finset.sum_Icc_succ_top (by omega)]
  linarith

lemma crudeBound_lt_one (L : ℕ) (hL : 12 ≤ L) : crudeBound L < 1 := by
  by_cases h : L ≤ 50
  · exact crudeBound_small L (Finset.mem_Icc.mpr ⟨hL,h⟩)
  · have hb : ∀ K, 50 ≤ K → crudeBound K ≤ crudeBound 50 := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base => exact le_refl _
      | succ K hK ih => exact (crudeBound_step K hK).trans ih
    exact (hb L (by omega)).trans_lt (crudeBound_small 50 (by simp))

def patterns (p t : ℕ) : Finset (Fin (p+1) → ℕ) :=
  (Finset.Nat.antidiagonalTuple (p+1) t).filter
    (fun d => Monotone (fun i : Fin p => d i.castSucc))

def patternWeight (L t : ℕ) (d : Fin (L-t+1) → ℕ) : ℚ :=
  (t.factorial : ℚ) *
    (∏ i : Fin (L-t), ((t+i.val+1).factorial : ℚ) /
      ((t+i.val+1+d i.castSucc).factorial : ℚ)) *
    ((L+2).factorial : ℚ) / ((L+2+d (Fin.last (L-t))).factorial : ℚ)

def fineBound (L : ℕ) : ℚ :=
  ∑ t ∈ Finset.Icc 1 L, ∑ d ∈ patterns (L-t) t, patternWeight L t d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fineBound_small : ∀ L ∈ Finset.Icc 1 11, fineBound L < 1 := by
  decide +kernel

lemma filter_nonzero_sum (l : List ℕ) : (l.filter (· != 0)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = 0 <;> simp [h, ih]

lemma filter_nonzero_length (l : List ℕ) :
    l.count 0 + (l.filter (· != 0)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = 0
    · subst a
      simp only [List.count_cons_self, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]
      omega
    · simp [h, Ne.symm h, List.count_cons]
      omega

lemma monotone_filter_injective {p : ℕ} {a b : Fin p → ℕ}
    (ha : Monotone a) (hb : Monotone b)
    (he : (List.ofFn a).filter (· != 0) = (List.ofFn b).filter (· != 0)) : a = b := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_pairwise' ha.sortedLE_ofFn.pairwise hb.sortedLE_ofFn.pairwise
  rw [List.perm_iff_count]
  intro x
  by_cases hx : x = 0
  · subst x
    have h1 := filter_nonzero_length (List.ofFn a)
    have h2 := filter_nonzero_length (List.ofFn b)
    rw [he] at h1
    simp only [List.length_ofFn] at h1 h2
    omega
  · have h := congrArg (List.count x) he
    rw [List.count_filter (p := fun y : ℕ => y != 0) (by simp [hx]),
      List.count_filter (p := fun y : ℕ => y != 0) (by simp [hx])] at h
    exact h

lemma patterns_sum {p t : ℕ} {d : Fin (p+1) → ℕ} (hd : d ∈ patterns p t) :
    ∑ i, d i = t := (Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hd).1)

lemma patterns_mono {p t : ℕ} {d : Fin (p+1) → ℕ} (hd : d ∈ patterns p t) :
    Monotone (fun i : Fin p => d i.castSucc) := (Finset.mem_filter.mp hd).2

def patternCode {p t : ℕ} (d : ↥(patterns p t)) : Bool × Composition t :=
  (decide (d.val (Fin.last p) = 0),
    ⟨(List.ofFn d.val).filter (· != 0),
      by intro i hi; have h := (List.mem_filter.mp hi).2; simp only [bne_iff_ne] at h; omega,
      by rw [filter_nonzero_sum, List.sum_ofFn]; exact patterns_sum d.property⟩)

lemma patternCode_injective (p t : ℕ) : Function.Injective (@patternCode p t) := by
  intro a b he
  have hflag : (a.val (Fin.last p) = 0) ↔ (b.val (Fin.last p) = 0) := by
    have hh := congrArg Prod.fst he
    simpa [patternCode] using hh
  have hl : (List.ofFn a.val).filter (· != 0) = (List.ofFn b.val).filter (· != 0) := by
    exact congrArg (fun x => x.2.blocks) he
  rw [List.ofFn_succ', List.ofFn_succ', List.concat_eq_append, List.concat_eq_append,
    List.filter_append, List.filter_append] at hl
  have hp : (fun i : Fin p => a.val i.castSucc) = (fun i : Fin p => b.val i.castSucc) ∧
      a.val (Fin.last p) = b.val (Fin.last p) := by
    by_cases ha : a.val (Fin.last p) = 0
    · have hb := hflag.mp ha
      simp only [ha, hb, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, List.filter_nil, List.append_nil] at hl
      exact ⟨monotone_filter_injective (patterns_mono a.property) (patterns_mono b.property) hl,
        ha.trans hb.symm⟩
    · have hb : b.val (Fin.last p) ≠ 0 := fun h => ha (hflag.mpr h)
      simp [ha, hb] at hl
      exact ⟨monotone_filter_injective (patterns_mono a.property) (patterns_mono b.property) hl.1,
        hl.2⟩
  apply Subtype.ext
  funext i
  induction i using Fin.lastCases with
  | last => exact hp.2
  | cast j => exact congrFun hp.1 j

lemma patterns_card (p t : ℕ) (ht : 0 < t) : (patterns p t).card ≤ 2^t := by
  have h := Fintype.card_le_of_injective (@patternCode p t) (patternCode_injective p t)
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool, composition_card] at h
  have ht' : 2^t = 2*2^(t-1) := by
    conv_lhs => rw [show t = (t-1)+1 by omega]
    rw [pow_succ, mul_comm]
  rwa [ht']

lemma patterns_tail_bound {p t : ℕ} {d : Fin (p+1) → ℕ}
    (hd : d ∈ patterns p t) (i : Fin p) (hi : 0 < d i.castSucc) : p-i.val ≤ t := by
  have hsum : ∑ j ∈ Finset.Ici i, (1:ℕ) ≤ ∑ j ∈ Finset.Ici i, d j.castSucc := by
    apply Finset.sum_le_sum
    intro j hj
    exact hi.trans_le ((patterns_mono hd) (Finset.mem_Ici.mp hj))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ici] at hsum
  have hsum' : ∑ j ∈ Finset.Ici i, d j.castSucc ≤ ∑ j : Fin p, d j.castSucc :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hs := patterns_sum hd
  rw [Fin.sum_univ_castSucc] at hs
  omega

lemma factorial_ratio_bound (k d B : ℕ) (hB : 0 < B)
    (hd : 0 < d → B ≤ k+1) :
    (k.factorial : ℚ) / ((k+d).factorial : ℚ) ≤ (1 / (B:ℚ))^d := by
  by_cases h : d = 0
  · subst d; simp [Nat.factorial_ne_zero]
  · have hn : k.factorial * B^d ≤ (k+d).factorial :=
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hd (by omega)) d)).trans
        Nat.factorial_mul_pow_le_factorial
    rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
    simpa using hn

lemma patternWeight_bound (L t : ℕ) (ht : t ≤ L) (d : Fin (L-t+1) → ℕ)
    (hd : d ∈ patterns (L-t) t) :
    patternWeight L t d ≤ (t.factorial : ℚ) /
      (max (t+2) (L-t+2) : ℕ)^t := by
  let B := max (t+2) (L-t+2)
  have hB : 0 < B := by dsimp [B]; omega
  have hpre : ∀ i : Fin (L-t),
      ((t+i.val+1).factorial : ℚ) / ((t+i.val+1+d i.castSucc).factorial : ℚ)
        ≤ (1/(B:ℚ))^(d i.castSucc) := by
    intro i
    apply factorial_ratio_bound _ _ B hB
    intro hi
    have htail := patterns_tail_bound hd i hi
    dsimp [B]
    omega
  have hlast : ((L+2).factorial : ℚ) / ((L+2+d (Fin.last (L-t))).factorial : ℚ)
      ≤ (1/(B:ℚ))^(d (Fin.last (L-t))) := by
    apply factorial_ratio_bound _ _ B hB
    intro _
    dsimp [B]
    omega
  have hp := Finset.prod_le_prod (s := Finset.univ)
    (fun i _ => show (0:ℚ) ≤ ((t+i.val+1).factorial : ℚ) /
      ((t+i.val+1+d i.castSucc).factorial : ℚ) by positivity) (fun i _ => hpre i)
  have hh := mul_le_mul hp hlast (by positivity) (by positivity)
  have hs := patterns_sum hd
  rw [Fin.sum_univ_castSucc] at hs
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, hs] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℚ) ≤ t.factorial by positivity)
  simpa [patternWeight, one_div_pow, div_eq_mul_inv, mul_assoc, B] using hh'

lemma fineBound_le_crude (L : ℕ) : fineBound L ≤ crudeBound L := by
  unfold fineBound crudeBound
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨ht0,htL⟩ := Finset.mem_Icc.mp ht
  have h := Finset.sum_le_sum (s := patterns (L-t) t)
    (fun d hd => patternWeight_bound L t htL d hd)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have hc : ((patterns (L-t) t).card : ℚ) ≤ (2:ℚ)^t := by
    exact_mod_cast patterns_card (L-t) t ht0
  have hh := mul_le_mul_of_nonneg_right hc
    (show (0:ℚ) ≤ t.factorial / (max (t+2) (L-t+2) : ℕ)^t by positivity)
  exact h.trans (by simpa [crudeTerm, mul_div_assoc] using hh)

lemma fineBound_lt_one (L : ℕ) (hL : 0 < L) : fineBound L < 1 := by
  by_cases h : L ≤ 11
  · exact fineBound_small L (Finset.mem_Icc.mpr ⟨hL,h⟩)
  · exact (fineBound_le_crude L).trans_lt (crudeBound_lt_one L (by omega))

end SignProof

open Finset Nat
namespace SignProof

def stair (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => (b+a) :: stair (b+1) as

def unstair (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => (a-b) :: unstair (b+1) as

def trim (t : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => (a-t) :: trim (t-a) as

def bumpHead (d : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => (a+d) :: as

def stairPrefix (L : ℕ) := List.range' 1 L

@[simp] lemma stair_nil (b : ℕ) : stair b [] = [] := rfl
@[simp] lemma stair_cons (b a : ℕ) (as : List ℕ) :
    stair b (a::as) = (b+a)::stair (b+1) as := rfl
@[simp] lemma trim_nil (t : ℕ) : trim t [] = [] := rfl
@[simp] lemma trim_cons (t a : ℕ) (as : List ℕ) :
    trim t (a::as) = (a-t)::trim (t-a) as := rfl
@[simp] lemma bumpHead_nil (d : ℕ) : bumpHead d [] = [] := rfl
@[simp] lemma bumpHead_cons (d a : ℕ) (as : List ℕ) :
    bumpHead d (a::as) = (a+d)::as := rfl

@[simp] lemma stair_length (b : ℕ) (a : List ℕ) : (stair b a).length = a.length := by
  induction a generalizing b <;> simp_all

@[simp] lemma unstair_length (b : ℕ) (a : List ℕ) : (unstair b a).length = a.length := by
  induction a generalizing b <;> simp_all [unstair]

@[simp] lemma trim_length (t : ℕ) (a : List ℕ) : (trim t a).length = a.length := by
  induction a generalizing t <;> simp_all

@[simp] lemma bumpHead_length (t : ℕ) (a : List ℕ) : (bumpHead t a).length = a.length := by
  cases a <;> rfl

@[simp] lemma stairPrefix_length (L : ℕ) : (stairPrefix L).length = L := by simp [stairPrefix]

lemma stair_append (b : ℕ) (a c : List ℕ) :
    stair b (a++c) = stair b a ++ stair (b+a.length) c := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih => simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma stair_replicate (b p : ℕ) : stair b (List.replicate p 0) = List.range' b p := by
  induction p generalizing b with
  | zero => simp
  | succ p ih => simp [List.replicate_succ, ih, List.range'_succ]

lemma stair_bumpHead (b d : ℕ) (a : List ℕ) :
    stair b (bumpHead d a) = bumpHead d (stair b a) := by
  cases a <;> simp [Nat.add_assoc]

lemma stair_sum (b : ℕ) (a : List ℕ) :
    (stair b a).sum = (List.range' b a.length).sum + a.sum := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih => simp [ih, List.range'_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] lemma trim_zero (a : List ℕ) : trim 0 a = a := by
  induction a <;> simp_all

lemma trim_sum (t : ℕ) (a : List ℕ) : (trim t a).sum = a.sum-t := by
  induction a generalizing t with
  | nil => simp
  | cons x a ih => simp only [trim_cons, List.sum_cons, ih]; omega

lemma trim_append (t : ℕ) (a c : List ℕ) :
    trim t (a++c) = trim t a ++ trim (t-a.sum) c := by
  induction a generalizing t with
  | nil => simp
  | cons x a ih => simp [ih, Nat.sub_sub]

lemma bumpHead_zero (a : List ℕ) : bumpHead 0 a = a := by cases a <;> simp

lemma trim_weak (a : List ℕ) (ha : a.Pairwise (· ≤ ·)) (t : ℕ) :
    (trim t a).Pairwise (· ≤ ·) := by
  induction a generalizing t with
  | nil => simp
  | cons x a ih =>
    obtain ⟨hxa,ha⟩ := List.pairwise_cons.mp ha
    rw [trim_cons, List.pairwise_cons]
    refine ⟨?_, ih ha _⟩
    intro y hy
    by_cases ht : t ≤ x
    · have he : t-x=0 := by omega
      rw [he, trim_zero] at hy
      exact (Nat.sub_le _ _).trans (hxa y hy)
    · have he : x-t=0 := by omega
      rw [he]; omega

lemma stair_lower (b k : ℕ) (a : List ℕ) (ha : ∀ x ∈ a, k ≤ x) :
    ∀ y ∈ stair b a, b+k ≤ y := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have := ha x (by simp); omega
    · have := ih (b+1) (fun z hz => ha z (by simp [hz])) y hy
      omega

lemma stair_strict (b : ℕ) (a : List ℕ) (ha : a.Pairwise (· ≤ ·)) :
    (stair b a).Pairwise (· < ·) ∧ ∀ x ∈ stair b a, b ≤ x := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    obtain ⟨hxa,ha⟩ := List.pairwise_cons.mp ha
    obtain ⟨hs,hb⟩ := ih (b+1) ha
    have hmem := stair_lower (b+1) x a hxa
    simp only [stair_cons, List.pairwise_cons]
    refine ⟨⟨fun y hy => by have := hmem y hy; omega,hs⟩,?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · exact (Nat.le_succ b).trans (hb y hy)

lemma unstair_stair (b : ℕ) (a : List ℕ) : unstair b (stair b a) = a := by
  induction a generalizing b <;> simp_all [unstair]

lemma unstair_lower (b k : ℕ) (a : List ℕ) (ha : a.Pairwise (· < ·))
    (hb : ∀ x ∈ a, b+k ≤ x) : ∀ y ∈ unstair b a, k ≤ y := by
  induction a generalizing b with
  | nil => simp [unstair]
  | cons x a ih =>
    obtain ⟨hxa,ha⟩ := List.pairwise_cons.mp ha
    have hbx := hb x (by simp)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · apply ih (b+1) ha _ y hy
      intro z hz
      have := hxa z hz
      omega

lemma stair_unstair (b : ℕ) (a : List ℕ) (ha : a.Pairwise (· < ·))
    (hb : ∀ x ∈ a, b ≤ x) : stair b (unstair b a) = a ∧
      (unstair b a).Pairwise (· ≤ ·) := by
  induction a generalizing b with
  | nil => simp [unstair]
  | cons x a ih =>
    obtain ⟨hxa,ha⟩ := List.pairwise_cons.mp ha
    have hbx := hb x (by simp)
    have hba : ∀ y ∈ a, b+1 ≤ y := by
      intro y hy; have := hxa y hy; omega
    obtain ⟨he,hm⟩ := ih (b+1) ha hba
    refine ⟨by simp [unstair, he, Nat.add_sub_of_le hbx], ?_⟩
    simp only [unstair, List.pairwise_cons]
    refine ⟨?_,hm⟩
    apply unstair_lower (b+1) (x-b) a ha
    intro z hz
    have := hxa z hz
    omega

lemma zero_split (a : List ℕ) : ∃ p c, a = List.replicate p 0 ++ c ∧
    (∀ x xs, c = x::xs → 0 < x) := by
  induction a with
  | nil => exact ⟨0, [], by simp, by simp⟩
  | cons x a ih =>
    by_cases hx : x = 0
    · obtain ⟨p,c,he,hc⟩ := ih
      exact ⟨p+1,c,by simp [hx, List.replicate_succ, he],hc⟩
    · refine ⟨0,x::a,by simp,?_⟩
      intro y ys he
      cases he
      omega

lemma trim_inverse (a c : List ℕ) (t p : ℕ)
    (ht : t ≤ a.sum) (he : trim t a = List.replicate p 0 ++ c)
    (hc : ∀ x xs, c = x::xs → 0 < x) :
    ∃ ds d, ds.length = p ∧ ds.sum+d = t ∧ a = ds ++ bumpHead d c ∧
      (c = [] → d = 0) := by
  cases c with
  | nil =>
    have hlen := congrArg List.length he
    simp only [trim_length, List.length_append, List.length_replicate, List.length_nil,
      Nat.add_zero] at hlen
    have hsum := congrArg List.sum he
    simp only [trim_sum, List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero,
      List.sum_nil, zero_add] at hsum
    refine ⟨a,0,hlen,?_,by simp,by simp⟩
    omega
  | cons x c =>
    have hx := hc x c rfl
    clear hc
    induction p generalizing a t with
    | zero =>
      cases a with
      | nil => simp at he
      | cons y a =>
        simp only [trim_cons, List.replicate_zero, List.nil_append, List.cons.injEq] at he
        have hty : t ≤ y := by omega
        have hzero : t-y=0 := by omega
        rw [hzero, trim_zero] at he
        refine ⟨[],t,by simp,by simp,?_,by simp⟩
        simp only [List.nil_append, bumpHead_cons, List.cons.injEq]
        exact ⟨by omega,he.2⟩
    | succ p ih =>
      cases a with
      | nil => simp [List.replicate_succ] at he
      | cons y a =>
        simp only [trim_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at he
        have hyt : y ≤ t := by omega
        have hta : t-y ≤ a.sum := by simp only [List.sum_cons] at ht; omega
        obtain ⟨ds,d,hlen,hsum,ha,hd⟩ := ih a (t-y) hta he.2
        refine ⟨y::ds,d,by simp [hlen],?_,?_,by simp⟩
        · simp only [List.sum_cons]; omega
        · simp [ha]

lemma stairPrefix_append (L K : ℕ) :
    stairPrefix (L+K) = stairPrefix L ++ List.range' (L+1) K := by
  unfold stairPrefix
  simpa [Nat.add_comm] using (List.range'_append_1 (s := 1) (m := L) (n := K)).symm

lemma stairPrefix_strict (L : ℕ) : (stairPrefix L).Pairwise (· < ·) := by
  exact List.pairwise_lt_range' 

lemma stairPrefix_mem {L x : ℕ} : x ∈ stairPrefix L ↔ 1 ≤ x ∧ x ≤ L := by
  simp only [stairPrefix, List.mem_range', one_mul]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hx,hL⟩
    exact ⟨x-1,by omega,by omega⟩

lemma stairPrefix_sum (L : ℕ) : 2*(stairPrefix L).sum = L*(L+1) := by
  induction L with
  | zero => simp [stairPrefix]
  | succ L ih =>
    rw [stairPrefix_append L 1]
    simp only [List.sum_append, List.range'_one, List.sum_singleton]
    nlinarith

lemma stairPrefix_extend_strict (L : ℕ) (c : List ℕ) (hc : c.Pairwise (· < ·))
    (hb : ∀ x ∈ c, L+1 ≤ x) :
    (stairPrefix L ++ c).Pairwise (· < ·) ∧ ∀ x ∈ stairPrefix L ++ c, 1 ≤ x := by
  rw [List.pairwise_append]
  refine ⟨⟨stairPrefix_strict L,hc,?_⟩,?_⟩
  · intro x hx y hy
    have hx' := stairPrefix_mem.mp hx
    have hy' := hb y hy
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (stairPrefix_mem.mp hx).1
    · have := hb x hx; omega

lemma prefix_split_general (b : ℕ) (a : List ℕ) (ha : a.Pairwise (· < ·))
    (hb : ∀ x ∈ a, b ≤ x) : ∃ L c, a = List.range' b L ++ c ∧
      c.Pairwise (· < ·) ∧ ∀ x ∈ c, b+L+1 ≤ x := by
  induction a generalizing b with
  | nil => exact ⟨0,[],by simp,by simp,by simp⟩
  | cons x a ih =>
    obtain ⟨hxa,ha'⟩ := List.pairwise_cons.mp ha
    have hbx := hb x (by simp)
    by_cases hx : x = b
    · obtain ⟨L,c,he,hc,hbc⟩ := ih (b+1) ha' (by
        intro y hy; have := hxa y hy; omega)
      refine ⟨L+1,c,?_,hc,?_⟩
      · simp [List.range'_succ, hx, he]
      · intro y hy; have := hbc y hy; omega
    · refine ⟨0,x::a,by simp,ha,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hxa y hy; omega

lemma prefix_split (a : List ℕ) (ha : a.Pairwise (· < ·)) (hb : ∀ x ∈ a, 1 ≤ x) :
    ∃ L c, a = stairPrefix L ++ c ∧ c.Pairwise (· < ·) ∧ ∀ x ∈ c, L+2 ≤ x := by
  simpa [stairPrefix, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    prefix_split_general 1 a ha hb

lemma prefix_decomp_unique {L K : ℕ} {a b : List ℕ}
    (he : stairPrefix L ++ a = stairPrefix K ++ b)
    (ha : ∀ x ∈ a, L+2 ≤ x) (hb : ∀ x ∈ b, K+2 ≤ x) : L = K ∧ a = b := by
  have hL : L ≤ K := by
    by_contra h
    have hm : K+1 ∈ stairPrefix L ++ a := by
      apply List.mem_append_left
      exact stairPrefix_mem.mpr ⟨by omega,by omega⟩
    rw [he] at hm
    rcases List.mem_append.mp hm with hm | hm
    · have := stairPrefix_mem.mp hm; omega
    · have := hb (K+1) hm; omega
  have hK : K ≤ L := by
    by_contra h
    have hm : L+1 ∈ stairPrefix K ++ b := by
      apply List.mem_append_left
      exact stairPrefix_mem.mpr ⟨by omega,by omega⟩
    rw [← he] at hm
    rcases List.mem_append.mp hm with hm | hm
    · have := stairPrefix_mem.mp hm; omega
    · have := ha (L+1) hm; omega
  have h : L=K := by omega
  subst K
  exact ⟨rfl,List.append_cancel_left he⟩

lemma stair_eq_ofFn (b : ℕ) (a : List ℕ) :
    stair b a = List.ofFn (fun i : Fin a.length => b+i.val+a.get i) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    rw [List.ofFn_succ]
    simp only [stair_cons, Fin.val_zero, Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero,
      Fin.val_succ, List.getElem_cons_succ]
    congr 1
    convert ih (b+1) using 1 <;> congr 1 <;> funext i <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def inverseMove (L : ℕ) (c : List ℕ) (t : ℕ) (d : Fin (L-t+1) → ℕ) : List ℕ :=
  stairPrefix (t-1) ++
    List.ofFn (fun i : Fin (L-t) => t+i.val+1+d i.castSucc) ++
    bumpHead (d (Fin.last (L-t))) c

lemma compression_capacity (L : ℕ) (a : List ℕ)
    (hh : (L+a.length+1)*(L+a.length+2) ≤
      2*(stairPrefix L ++ stair (L+2) a).sum) : L+1 ≤ a.sum := by
  have hp := stairPrefix_sum (L+1+a.length)
  rw [stairPrefix_append (L+1) a.length, stairPrefix_append L 1] at hp
  simp only [List.sum_append, List.range'_one, List.sum_singleton] at hp
  simp only [List.sum_append, stair_sum] at hh
  have he : L+1+1=L+2 := by omega
  rw [he] at hp
  nlinarith

lemma compression_exists (s : List ℕ) (hs : s.Pairwise (· < ·))
    (hpos : ∀ x ∈ s, 1 ≤ x)
    (hroom : (s.length+1)*(s.length+2) ≤ 2*s.sum) :
    ∃ (L : ℕ) (c : List ℕ) (t : ℕ) (d : Fin (L-t+1) → ℕ),
      1 ≤ t ∧ t ≤ L ∧ d ∈ patterns (L-t) t ∧
      c.Pairwise (· < ·) ∧ (∀ x ∈ c, L+2 ≤ x) ∧
      (stairPrefix L ++ c).length = s.length+1 ∧
      (stairPrefix L ++ c).sum = s.sum ∧
      s = inverseMove L c t d ∧
      (c = [] → d (Fin.last (L-t)) = 0) := by
  obtain ⟨K,c0,hsc,hc0,hgap0⟩ := prefix_split s hs hpos
  let a := unstair (K+2) c0
  have ha := stair_unstair (K+2) c0 hc0 hgap0
  change stair (K+2) a = c0 ∧ a.Pairwise (· ≤ ·) at ha
  have hsA : s = stairPrefix K ++ stair (K+2) a := by rw [ha.1]; exact hsc
  have hcap : K+1 ≤ a.sum := by
    apply compression_capacity K a
    simpa only [hsA, List.length_append, stairPrefix_length, stair_length] using hroom
  let b := trim (K+1) a
  have hb : b.Pairwise (· ≤ ·) := trim_weak a ha.2 (K+1)
  obtain ⟨p,c1,hbc,hhead⟩ := zero_split b
  have hc1 : c1.Pairwise (· ≤ ·) := by
    rw [hbc, List.pairwise_append] at hb
    exact hb.2.1
  have hc1pos : ∀ x ∈ c1, 1 ≤ x := by
    cases c1 with
    | nil => simp
    | cons x c1 =>
      have hx := hhead x c1 rfl
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact hx.trans_le ((List.pairwise_cons.mp hc1).1 y hy)
  let L := K+1+p
  let c := stair (L+1) c1
  have hc := stair_strict (L+1) c1 hc1
  have hgap : ∀ x ∈ c, L+2 ≤ x := by
    simpa [c, Nat.add_assoc] using stair_lower (L+1) 1 c1 hc1pos
  have hu : stairPrefix L ++ c = stairPrefix (K+1) ++ stair (K+2) b := by
    rw [hbc, stair_append, stair_replicate]
    simp only [List.length_replicate]
    dsimp [L,c]
    rw [stairPrefix_append (K+1) p]
    simp [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hulen : (stairPrefix L ++ c).length = s.length+1 := by
    rw [hu, hsA]
    simp [b]
    omega
  have husum : (stairPrefix L ++ c).sum = s.sum := by
    rw [hu, hsA, stairPrefix_append K 1]
    simp only [List.sum_append, List.range'_one, List.sum_singleton, stair_sum,
      b, trim_length, trim_sum]
    omega
  obtain ⟨ds,dlast,hlen,hsum,hainv,hdlast⟩ :=
    trim_inverse a c1 (K+1) p hcap hbc hhead
  have hds : ds.Pairwise (· ≤ ·) := by
    rw [hainv, List.pairwise_append] at ha
    exact ha.2.1
  have hp : L-(K+1)=p := by dsimp [L]; omega
  have hdlen : ds.length = L-(K+1) := hlen.trans hp.symm
  let df : Fin (L-(K+1)) → ℕ := fun i => ds.get (Fin.cast hdlen.symm i)
  let d : Fin (L-(K+1)+1) → ℕ := Fin.snoc df dlast
  have hdf : List.ofFn df = ds := by
    exact (List.ofFn_congr hdlen ds.get).symm.trans (List.ofFn_get ds)
  have hdfmono : Monotone df := by
    intro i j hij
    apply hds.rel_get_of_le
    exact hij
  have hdpat : d ∈ patterns (L-(K+1)) (K+1) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.Nat.mem_antidiagonalTuple.mpr ?_, ?_⟩
    · rw [Fin.sum_univ_castSucc]
      simp only [d, Fin.snoc_castSucc, Fin.snoc_last]
      rw [← List.sum_ofFn, hdf]
      exact hsum
    · simpa only [d, Fin.snoc_castSucc] using hdfmono
  refine ⟨L,c,K+1,d,by omega,by dsimp [L]; omega,hdpat,hc.1,hgap,hulen,husum,?_,?_⟩
  · rw [hsA, hainv, stair_append, stair_bumpHead]
    unfold inverseMove
    simp only [Nat.add_sub_cancel, d, Fin.snoc_castSucc, Fin.snoc_last]
    have hstair : stair (K+2) ds = List.ofFn (fun i : Fin (L-(K+1)) => K+1+i.val+1+df i) := by
      rw [stair_eq_ofFn, List.ofFn_congr hdlen]
      congr 1
      funext i
      simp [df, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hstair, hdlen]
    dsimp [c]
    have he : K+2+(L-(K+1)) = L+1 := by dsimp [L]; omega
    rw [he]
    simp [List.append_assoc]
  · intro hcempty
    have hnil : c1 = [] := by
      have hh := congrArg List.length hcempty
      simp only [c, stair_length, List.length_nil, List.length_eq_zero_iff] at hh
      exact hh
    simpa [d] using hdlast hnil

def weight (a : List ℕ) : ℚ := (a.map (fun k => (k.factorial : ℚ)⁻¹)).prod

@[simp] lemma weight_nil : weight [] = 1 := rfl
@[simp] lemma weight_cons (x : ℕ) (a : List ℕ) :
    weight (x::a) = (x.factorial : ℚ)⁻¹ * weight a := rfl
@[simp] lemma weight_append (a b : List ℕ) : weight (a++b) = weight a * weight b := by
  simp [weight]

lemma weight_pos (a : List ℕ) : 0 < weight a := by
  induction a with
  | nil => simp
  | cons x a ih => rw [weight_cons]; exact mul_pos (by positivity) ih

lemma weight_ofFn {p : ℕ} (a : Fin p → ℕ) :
    weight (List.ofFn a) = ∏ i, (a i).factorial.cast⁻¹ := by
  simp [weight, List.map_ofFn, List.prod_ofFn, Function.comp_def]

lemma range'_ofFn (b p : ℕ) : List.range' b p = List.ofFn (fun i : Fin p => b+i.val) := by
  rw [← stair_replicate b p, stair_eq_ofFn]
  simp

lemma stairPrefix_split_at (L t : ℕ) (ht0 : 1 ≤ t) (htL : t ≤ L) :
    stairPrefix L = stairPrefix (t-1) ++ t :: List.range' (t+1) (L-t) := by
  conv_lhs => rw [show L = t+(L-t) by omega, stairPrefix_append t (L-t)]
  conv_lhs => rw [show t = (t-1)+1 by omega, stairPrefix_append (t-1) 1]
  simp [List.append_assoc, show t-1+1=t by omega]

lemma factorial_ratio_mono (a b d : ℕ) (hab : a ≤ b) :
    (b.factorial : ℚ) / ((b+d).factorial : ℚ) ≤
      (a.factorial : ℚ) / ((a+d).factorial : ℚ) := by
  induction d with
  | zero => simp [Nat.factorial_ne_zero]
  | succ d ih =>
    simp only [← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, div_mul_eq_div_div]
    have hh := div_le_div₀ (by positivity : (0:ℚ) ≤ a.factorial / (a+d).factorial)
      ih (by positivity : (0:ℚ) < (a+d+1:ℕ))
      (show ((a+d+1:ℕ):ℚ) ≤ ((b+d+1:ℕ):ℚ) by exact_mod_cast (by omega : a+d+1 ≤ b+d+1))
    push_cast at hh
    convert hh using 1 <;> ring

lemma bumpHead_weight_bound (c : List ℕ) (B d : ℕ)
    (hc : ∀ x ∈ c, B ≤ x) (hd : c = [] → d = 0) :
    weight (bumpHead d c) ≤ weight c * (B.factorial : ℚ) / ((B+d).factorial : ℚ) := by
  cases c with
  | nil => simp [hd rfl, Nat.factorial_ne_zero]
  | cons x c =>
    have h := factorial_ratio_mono B x d (hc x (by simp))
    have hh := mul_le_mul_of_nonneg_left h
      (show (0:ℚ) ≤ (x.factorial : ℚ)⁻¹ * weight c by
        exact mul_nonneg (by positivity) (weight_pos c).le)
    simpa [bumpHead, weight_cons, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      Nat.factorial_ne_zero] using hh

lemma weight_ofFn_ratio {p : ℕ} (a d : Fin p → ℕ) :
    weight (List.ofFn a) * ∏ i, ((a i).factorial : ℚ) / ((a i+d i).factorial : ℚ) =
      weight (List.ofFn (fun i => a i+d i)) := by
  rw [weight_ofFn, weight_ofFn, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp [div_eq_mul_inv, ← mul_assoc, Nat.factorial_ne_zero]

lemma inverseMove_weight (L : ℕ) (c : List ℕ) (t : ℕ) (d : Fin (L-t+1) → ℕ)
    (ht0 : 1 ≤ t) (htL : t ≤ L) (hc : ∀ x ∈ c, L+2 ≤ x)
    (hd : c = [] → d (Fin.last (L-t)) = 0) :
    weight (inverseMove L c t d) ≤ weight (stairPrefix L ++ c) * patternWeight L t d := by
  have htail := bumpHead_weight_bound c (L+2) (d (Fin.last (L-t))) hc hd
  let a : Fin (L-t) → ℕ := fun i => t+i.val+1
  let e : Fin (L-t) → ℕ := fun i => d i.castSucc
  have hpre := weight_ofFn_ratio a e
  have hfac : (t.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have heq : weight (stairPrefix L ++ c) * patternWeight L t d =
      weight (stairPrefix (t-1)) * weight (List.ofFn (fun i => a i+e i)) *
        (weight c * (L+2).factorial / (L+2+d (Fin.last (L-t))).factorial) := by
    rw [stairPrefix_split_at L t ht0 htL]
    simp only [weight_append, weight_cons, range'_ofFn]
    have hr : List.ofFn (fun i : Fin (L-t) => t+1+i.val) = List.ofFn a := by
      congr 1; funext i; dsimp [a]; omega
    rw [hr, ← hpre]
    unfold patternWeight
    dsimp [a,e]
    field_simp
    <;> ring
  rw [heq]
  unfold inverseMove
  simp only [weight_append]
  exact mul_le_mul_of_nonneg_left htail
    (mul_nonneg (weight_pos _).le (weight_pos _).le)

end SignProof

open Finset Nat
namespace SignProof

structure CPart (n r : ℕ) where
  L : ℕ
  tail : List ℕ
  strict : tail.Pairwise (· < ·)
  gap : ∀ x ∈ tail, L+2 ≤ x
  length_eq : L+tail.length = r
  sum_eq : (stairPrefix L ++ tail).sum = n

namespace CPart

variable {n r : ℕ}

def list (p : CPart n r) : List ℕ := stairPrefix p.L ++ p.tail

@[simp] lemma length_list (p : CPart n r) : p.list.length = r := by
  simpa [list] using p.length_eq

@[simp] lemma sum_list (p : CPart n r) : p.list.sum = n := p.sum_eq

lemma strict_list (p : CPart n r) : p.list.Pairwise (· < ·) :=
  (stairPrefix_extend_strict p.L p.tail p.strict (fun x hx => by have := p.gap x hx; omega)).1

lemma pos_list (p : CPart n r) : ∀ x ∈ p.list, 1 ≤ x :=
  (stairPrefix_extend_strict p.L p.tail p.strict (fun x hx => by have := p.gap x hx; omega)).2

lemma list_injective : Function.Injective (@list n r) := by
  intro p q he
  have hh := prefix_decomp_unique he p.gap q.gap
  cases p; cases q
  simp_all only [CPart.mk.injEq]

lemma exists_of_list (a : List ℕ) (ha : a.Pairwise (· < ·))
    (hpos : ∀ x ∈ a, 1 ≤ x) (hlen : a.length = r) (hsum : a.sum = n) :
    ∃ p : CPart n r, p.list = a := by
  obtain ⟨L,c,he,hc,hgap⟩ := prefix_split a ha hpos
  exact ⟨⟨L,c,hc,hgap,by simpa [he] using hlen,by simpa [he] using hsum⟩,he.symm⟩

def boundedTuple (p : CPart n r) : Fin r → Fin (n+1) := fun i =>
  ⟨p.list.get (Fin.cast p.length_list.symm i), by
    have h := List.le_sum_of_mem (List.get_mem p.list (Fin.cast p.length_list.symm i))
    rw [p.sum_list] at h
    omega⟩

lemma boundedTuple_injective : Function.Injective (@boundedTuple n r) := by
  intro p q he
  apply list_injective
  apply List.ext_get (p.length_list.trans q.length_list.symm)
  intro k hk hk'
  have hk0 : k < r := by simpa only [p.length_list] using hk
  have hh := congrArg Fin.val (congrFun he ⟨k,hk0⟩)
  exact hh

instance : Finite (CPart n r) := Finite.of_injective boundedTuple boundedTuple_injective
noncomputable instance : Fintype (CPart n r) := Fintype.ofFinite _
noncomputable instance : DecidableEq (CPart n r) := Classical.decEq _

end CPart

noncomputable def level (n r : ℕ) : ℚ := ∑ p : CPart n r, weight p.list

lemma level_nonneg (n r : ℕ) : 0 ≤ level n r := by
  apply Finset.sum_nonneg
  intro p _
  exact (weight_pos p.list).le

lemma fineBound_lt_one_all (L : ℕ) : fineBound L < 1 := by
  by_cases h : L=0
  · subst L; simp [fineBound]
  · exact fineBound_lt_one L (by omega)

lemma patternWeight_nonneg (L t : ℕ) (d : Fin (L-t+1) → ℕ) :
    0 ≤ patternWeight L t d := by unfold patternWeight; positivity

abbrev MoveCode {n r : ℕ} (q : CPart n r) :=
  (t : ↥(Finset.Icc 1 q.L)) × ↥(patterns (q.L-t.val) t.val)

noncomputable def moveCost {n r : ℕ} (z : (q : CPart n r) × MoveCode q) : ℚ :=
  weight z.1.list * patternWeight z.1.L z.2.1.val z.2.2.val

lemma compression_witness {n r : ℕ} (hroom : (r+1)*(r+2) ≤ 2*n) (p : CPart n r) :
    ∃ z : (q : CPart n (r+1)) × MoveCode q,
      p.list = inverseMove z.1.L z.1.tail z.2.1.val z.2.2.val ∧
      weight p.list ≤ moveCost z := by
  have hh : (p.list.length+1)*(p.list.length+2) ≤ 2*p.list.sum := by simpa using hroom
  obtain ⟨L,c,t,d,ht0,htL,hd,hc,hgap,hlen,hsum,he,hemp⟩ :=
    compression_exists p.list p.strict_list p.pos_list hh
  let q : CPart n (r+1) := ⟨L,c,hc,hgap,by simpa using hlen,by simpa using hsum⟩
  let z : (q : CPart n (r+1)) × MoveCode q := ⟨q,⟨⟨t,Finset.mem_Icc.mpr ⟨ht0,htL⟩⟩,⟨d,hd⟩⟩⟩
  refine ⟨z,he,?_⟩
  change weight p.list ≤ weight (stairPrefix L ++ c) * patternWeight L t d
  rw [he]
  exact inverseMove_weight L c t d ht0 htL hgap hemp

lemma sum_injective_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (a : α → ℚ) (b : β → ℚ)
    (hb : ∀ y, 0 ≤ b y) (ha : ∀ x, a x ≤ b (f x)) : ∑ x, a x ≤ ∑ y, b y := by
  classical
  calc
    ∑ x, a x ≤ ∑ x, b (f x) := Finset.sum_le_sum (fun x _ => ha x)
    _ = ∑ y ∈ Finset.univ.image f, b y := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ ∑ y, b y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hb y)

lemma level_le_cost (n r : ℕ) (hroom : (r+1)*(r+2) ≤ 2*n) :
    level n r ≤ ∑ z : (q : CPart n (r+1)) × MoveCode q, moveCost z := by
  classical
  choose f hf hfweight using compression_witness hroom
  apply sum_injective_le f _ _ moveCost _ hfweight
  · intro p q he
    apply CPart.list_injective
    rw [hf p, hf q, he]
  · intro z
    exact mul_nonneg (weight_pos _).le (patternWeight_nonneg _ _ _)

lemma sum_moveCost (n r : ℕ) :
    (∑ z : (q : CPart n r) × MoveCode q, moveCost z) =
      ∑ q : CPart n r, weight q.list * fineBound q.L := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.sum_sigma]
  simp only [moveCost]
  simp_rw [← Finset.mul_sum]
  congr 1
  simp only [fineBound]
  simp only [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort _ (fun t => ∑ d ∈ patterns (q.L-t) t, patternWeight q.L t d)

lemma partition_exists (n r : ℕ) (hr : 0 < r) (hroom : r*(r+1) ≤ 2*n) :
    Nonempty (CPart n r) := by
  have htri := stairPrefix_sum r
  have hle : (stairPrefix r).sum ≤ n := by omega
  have hr' : r-1+1=r := by omega
  have he := stairPrefix_append (r-1) 1
  rw [hr'] at he
  have he' := congrArg List.sum he
  simp only [List.sum_append, List.range'_one, List.sum_singleton, hr'] at he'
  let k := n-(stairPrefix (r-1)).sum
  have hk : r ≤ k := by dsimp [k]; omega
  let a := stairPrefix (r-1) ++ [k]
  have ha := stairPrefix_extend_strict (r-1) [k] (by simp)
    (by intro x hx; simp only [List.mem_singleton] at hx; subst x; omega)
  obtain ⟨p,hp⟩ := CPart.exists_of_list (n := n) (r := r) a ha.1 ha.2
    (by simp [a]; omega) (by simp only [a, List.sum_append, List.sum_singleton]; dsimp [k]; omega)
  exact ⟨p⟩

lemma level_strict (n r : ℕ) (hroom : (r+1)*(r+2) ≤ 2*n) : level n r < level n (r+1) := by
  have h := level_le_cost n r hroom
  rw [sum_moveCost] at h
  apply h.trans_lt
  unfold level
  apply Finset.sum_lt_sum
  · intro q _
    exact (mul_lt_of_lt_one_right (weight_pos _) (fineBound_lt_one_all q.L)).le
  · obtain ⟨q⟩ := partition_exists n (r+1) (by omega) hroom
    exact ⟨q,Finset.mem_univ _,mul_lt_of_lt_one_right (weight_pos _) (fineBound_lt_one_all q.L)⟩

end SignProof

open Finset Nat Polynomial
namespace SignProof

def sizeSets (n r : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powerset).filter (fun s => s.card = r ∧ ∑ k ∈ s, k = n)

lemma mem_sizeSets {n r : ℕ} {s : Finset ℕ} : s ∈ sizeSets n r ↔
    s ⊆ Finset.Icc 1 n ∧ s.card = r ∧ ∑ k ∈ s, k = n := by
  simp [sizeSets]

lemma CPart.toFinset_mem {n r : ℕ} (p : CPart n r) : p.list.toFinset ∈ sizeSets n r := by
  rw [mem_sizeSets]
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hm := List.mem_toFinset.mp hx
    have hpos := p.pos_list x hm
    have hle := List.le_sum_of_mem hm
    rw [p.sum_list] at hle
    exact Finset.mem_Icc.mpr ⟨hpos,hle⟩
  · rw [List.toFinset_card_of_nodup p.strict_list.nodup, p.length_list]
  · rw [List.sum_toFinset _ p.strict_list.nodup]
    simpa using p.sum_list

lemma CPart.toFinset_injective {n r : ℕ} :
    Function.Injective (fun p : CPart n r => p.list.toFinset) := by
  intro p q he
  change p.list.toFinset = q.list.toFinset at he
  apply CPart.list_injective
  have hp := (List.toFinset_sort (· ≤ ·) p.strict_list.nodup).mpr (p.strict_list.imp (fun h => h.le))
  have hq := (List.toFinset_sort (· ≤ ·) q.strict_list.nodup).mpr (q.strict_list.imp (fun h => h.le))
  rw [← hp, ← hq, he]

lemma CPart.toFinset_surjective {n r : ℕ} (s : Finset ℕ) (hs : s ∈ sizeSets n r) :
    ∃ p : CPart n r, p.list.toFinset = s := by
  obtain ⟨hsub,hcard,hsum⟩ := mem_sizeSets.mp hs
  let a := s.sort (· ≤ ·)
  have ha : a.Pairwise (· < ·) := s.sortedLT_sort.pairwise
  have hpos : ∀ x ∈ a, 1 ≤ x := by
    intro x hx
    exact (Finset.mem_Icc.mp (hsub (by simpa [a] using hx))).1
  have hlen : a.length = r := by simpa [a] using hcard
  have hasum : a.sum = n := by
    have h := List.sum_toFinset (fun k : ℕ => k) ha.nodup
    have he : ∑ k ∈ s, k = a.sum := by simpa [a] using h
    exact he.symm.trans hsum
  obtain ⟨p,hp⟩ := CPart.exists_of_list a ha hpos hlen hasum
  exact ⟨p,by rw [hp]; exact Finset.sort_toFinset _ _⟩

lemma level_eq_sets (n r : ℕ) : level n r =
    ∑ s ∈ sizeSets n r, ∏ k ∈ s, (k.factorial : ℚ)⁻¹ := by
  classical
  unfold level
  apply Finset.sum_bij (fun p _ => p.list.toFinset)
  · intro p _; exact p.toFinset_mem
  · intro p _ q _ he; exact CPart.toFinset_injective he
  · intro s hs
    obtain ⟨p,hp⟩ := CPart.toFinset_surjective s hs
    exact ⟨p,Finset.mem_univ _,hp⟩
  · intro p _
    exact (List.prod_toFinset _ p.strict_list.nodup).symm

noncomputable def seriesPoly (n : ℕ) : Polynomial ℚ :=
  ∏ k ∈ Finset.Icc 1 n, (1 - C ((k.factorial : ℚ)⁻¹) * X^k)

lemma coeff_product (S : Finset ℕ) (n : ℕ) :
    (∏ k ∈ S, (1 - C ((k.factorial : ℚ)⁻¹) * X^k)).coeff n =
      ∑ s ∈ S.powerset with ∑ k ∈ s, k = n,
        (-1:ℚ)^s.card * ∏ k ∈ s, (k.factorial : ℚ)⁻¹ := by
  classical
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Polynomial.finset_sum_coeff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod]
  have he : (-1 : Polynomial ℚ)^s.card = C ((-1:ℚ)^s.card) := by simp
  rw [he, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  split_ifs <;> simp_all [eq_comm]

lemma coeff_levels (n : ℕ) : (seriesPoly n).coeff n =
    ∑ r ∈ Finset.range (n+1), (-1:ℚ)^r * level n r := by
  rw [seriesPoly, coeff_product]
  have hm : ∀ s ∈ ((Finset.Icc 1 n).powerset).filter (fun s => ∑ k ∈ s, k = n),
      s.card ∈ Finset.range (n+1) := by
    intro s hs
    have hc := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [level_eq_sets, Finset.mul_sum]
  have he : (((Finset.Icc 1 n).powerset).filter (fun s => ∑ k ∈ s, k = n)).filter
      (fun s => s.card = r) = sizeSets n r := by
    ext s
    simp [sizeSets, and_assoc, and_comm, _root_.and_left_comm]
  rw [he]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(mem_sizeSets.mp hs).2.1]

lemma strict_list_triangle (a : List ℕ) (ha : a.Pairwise (· < ·))
    (hpos : ∀ x ∈ a, 1 ≤ x) : a.length*(a.length+1) ≤ 2*a.sum := by
  have h := stair_unstair 1 a ha hpos
  have hs := stair_sum 1 (unstair 1 a)
  rw [h.1, unstair_length] at hs
  have ht := stairPrefix_sum a.length
  change 2*(List.range' 1 a.length).sum = _ at ht
  omega

lemma CPart.triangle {n r : ℕ} (p : CPart n r) : r*(r+1) ≤ 2*n := by
  simpa using strict_list_triangle p.list p.strict_list p.pos_list

lemma level_zero (n r : ℕ) (h : 2*n < r*(r+1)) : level n r = 0 := by
  haveI : IsEmpty (CPart n r) := ⟨fun p => by have := p.triangle; omega⟩
  simp [level]

lemma triangle_rank_le (n m : ℕ) (h : m*(m+1) ≤ 2*n) : m ≤ n := by
  by_cases hm : m=0
  · omega
  · have : 1 ≤ m := by omega
    nlinarith

lemma coeff_levels_truncated (n m : ℕ) (hlo : m*(m+1) ≤ 2*n)
    (hhi : 2*n < (m+1)*(m+2)) : (seriesPoly n).coeff n =
      ∑ r ∈ Finset.range (m+1), (-1:ℚ)^r * level n r := by
  rw [coeff_levels]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (triangle_rank_le n m hlo)))
  intro r hr hrm
  have hm : m+1 ≤ r := by simp only [Finset.mem_range] at hrm; omega
  have hprod : (m+1)*(m+2) ≤ r*(r+1) := Nat.mul_le_mul hm (by omega)
  rw [level_zero n r (by omega), mul_zero]

lemma signed_sum_step (f : ℕ → ℚ) (m : ℕ) :
    (-1:ℚ)^(m+2) * (∑ r ∈ Finset.range (m+3), (-1:ℚ)^r*f r) =
      (-1:ℚ)^m * (∑ r ∈ Finset.range (m+1), (-1:ℚ)^r*f r) + f (m+2)-f (m+1) := by
  have hsign : (-1:ℚ)^m * (-1:ℚ)^m = 1 := by rw [← mul_pow]; norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [pow_add, pow_one, neg_one_sq, mul_one]
  calc
    _ = (-1:ℚ)^m * (∑ r ∈ Finset.range (m+1), (-1:ℚ)^r*f r) +
      ((-1:ℚ)^m * (-1:ℚ)^m)*(f (m+2)-f (m+1)) := by ring
    _ = _ := by rw [hsign]; ring

lemma signed_sum_pos (f : ℕ → ℚ) (m : ℕ) (hf0 : 0 ≤ f 0)
    (hf : ∀ r, r < m → f r < f (r+1)) :
    0 ≤ (-1:ℚ)^m * (∑ r ∈ Finset.range (m+1), (-1:ℚ)^r*f r) ∧
      (0 < m → 0 < (-1:ℚ)^m * (∑ r ∈ Finset.range (m+1), (-1:ℚ)^r*f r)) := by
  induction m using Nat.twoStepInduction with
  | zero => simpa using And.intro hf0 (by omega : 0 < 0 → 0 < f 0)
  | one =>
    have h := hf 0 (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, one_mul,
      zero_add, neg_mul, one_pow]
    constructor <;> (try intro) <;> linarith
  | more m ih _ =>
    have hsmall := (ih (fun r hr => hf r (by omega))).1
    have hgap := hf (m+1) (by omega)
    rw [signed_sum_step]
    constructor <;> (try intro) <;> linarith

lemma coeff_sign (n m : ℕ) (hlo : m*(m+1) ≤ 2*n)
    (hhi : 2*n < (m+1)*(m+2)) : 0 < (-1:ℚ)^m * (seriesPoly n).coeff n := by
  by_cases hm : m=0
  · subst m
    have hn : n=0 := by omega
    subst n
    norm_num [seriesPoly]
  · rw [coeff_levels_truncated n m hlo hhi]
    apply (signed_sum_pos (level n) m (level_nonneg n 0) ?_).2 (by omega)
    intro r hr
    apply level_strict n r
    have hh : (r+1)*(r+2) ≤ m*(m+1) := Nat.mul_le_mul (by omega) (by omega)
    omega

lemma coefficient_integral (n : ℕ) :
    ∃ z : ℤ, (seriesPoly n).coeff n * (n.factorial : ℚ) = (z:ℚ) := by
  let S := ((Finset.Icc 1 n).powerset).filter (fun s => ∑ k ∈ s, k = n)
  refine ⟨∑ s ∈ S, (-1:ℤ)^s.card * (Nat.multinomial s (fun k => k) : ℤ),?_⟩
  rw [seriesPoly, coeff_product, Finset.sum_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro s hs
  have hsum : ∑ k ∈ s, k = n := (Finset.mem_filter.mp hs).2
  have hspec := Nat.multinomial_spec s (fun k => k)
  rw [hsum] at hspec
  have hspec' : (∏ k ∈ s, (k.factorial : ℚ)) * (Nat.multinomial s (fun k => k) : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast hspec
  rw [← hspec', Finset.prod_inv_distrib]
  have hnz : (∏ k ∈ s, (k.factorial : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

lemma A185895_cast (n : ℕ) : (A185895 n : ℚ) = (seriesPoly n).coeff n * (n.factorial : ℚ) := by
  by_cases hn : n=0
  · subst n; norm_num [A185895, seriesPoly]
  · obtain ⟨z,hz⟩ := coefficient_integral n
    have he : A185895 n = ((seriesPoly n).coeff n * (n.factorial : ℚ)).floor := by
      simp [A185895, hn, seriesPoly, one_div]
    rw [he, hz, Rat.floor_intCast]

lemma A185895_sign (n m : ℕ) (hlo : m*(m+1) ≤ 2*n)
    (hhi : 2*n < (m+1)*(m+2)) : 0 < (-1:ℤ)^m * A185895 n := by
  have h := mul_pos (coeff_sign n m hlo hhi) (show (0:ℚ) < n.factorial by positivity)
  rw [mul_assoc, ← A185895_cast] at h
  exact_mod_cast h

end SignProof

open Finset Nat Polynomial
namespace SignProof

lemma triangle_interval (n : ℕ) : ∃ m : ℕ,
    m*(m+1) ≤ 2*n ∧ 2*n < (m+1)*(m+2) := by
  let P : ℕ → Prop := fun m => m*(m+1) ≤ 2*n
  let m := Nat.findGreatest P n
  have hlo : P m := Nat.findGreatest_spec (m := 0) (by omega) (by simp [P])
  refine ⟨m,hlo,?_⟩
  by_contra hh
  have hp : P (m+1) := by dsimp [P]; nlinarith
  have hmn : m+1 ≤ n := triangle_rank_le n (m+1) hp
  exact Nat.findGreatest_is_greatest (show Nat.findGreatest P n < m+1 by omega) hmn hp

lemma sign_product_same (m : ℕ) (a b : ℤ)
    (ha : 0 < (-1:ℤ)^m*a) (hb : 0 < (-1:ℤ)^m*b) : 0 < a*b := by
  have h := mul_pos ha hb
  have hs : (-1:ℤ)^m * (-1:ℤ)^m = 1 := by rw [← mul_pow]; norm_num
  have he : ((-1:ℤ)^m*a)*((-1:ℤ)^m*b) = a*b := by
    calc
      _ = ((-1:ℤ)^m * (-1:ℤ)^m)*(a*b) := by ring
      _ = _ := by rw [hs, one_mul]
  rwa [he] at h

lemma sign_product_opposite (m : ℕ) (a b : ℤ)
    (ha : 0 < (-1:ℤ)^(m+1)*a) (hb : 0 < (-1:ℤ)^m*b) : a*b < 0 := by
  have h := mul_pos ha hb
  have hs : (-1:ℤ)^m * (-1:ℤ)^m = 1 := by rw [← mul_pow]; norm_num
  have he : ((-1:ℤ)^(m+1)*a)*((-1:ℤ)^m*b) = -(a*b) := by
    rw [pow_succ]
    calc
      _ = -(((-1:ℤ)^m * (-1:ℤ)^m)*(a*b)) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [he] at h
  linarith

lemma conjecture_proof :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  intro n hn
  obtain ⟨m,hlo,hhi⟩ := triangle_interval (n-1)
  have hsign0 := A185895_sign (n-1) m hlo hhi
  have heven := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (m+1))
  norm_num only [Nat.add_assoc] at heven
  have hbound : 2*n ≤ (m+1)*(m+2) := by omega
  by_cases heq : 2*n = (m+1)*(m+2)
  · have htri : is_triangular n := by
      refine ⟨m+1,?_⟩
      norm_num only [Nat.add_assoc]
      omega
    have hsign1 := A185895_sign n (m+1) (by nlinarith) (by nlinarith)
    exact iff_of_true (sign_product_opposite m _ _ hsign1 hsign0) htri
  · have hlt : 2*n < (m+1)*(m+2) := by omega
    have hsign1 := A185895_sign n m (by omega) hlt
    have hp := sign_product_same m _ _ hsign1 hsign0
    have hnot : ¬ is_triangular n := by
      rintro ⟨k,hk⟩
      have hk2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self k)
      have he : 2*n = k*(k+1) := by omega
      by_cases hkm : k ≤ m
      · have hh := Nat.mul_le_mul hkm (Nat.succ_le_succ hkm)
        simp only [Nat.succ_eq_add_one] at hh
        omega
      · have hh : (m+1)*(m+2) ≤ k*(k+1) := Nat.mul_le_mul (by omega) (by omega)
        omega
    exact iff_of_false (by omega) hnot

end SignProof

/--
Conjectures: 1) a(n) differs in sign from a(n-1) iff n is a triangular number (checked up to n = 1225 = (50*51)/2)
The condition "differs in sign" for $a(n)$ and $a(n-1)$ is formalized as their product being strictly negative.
We only consider $n \ge 1$.
-/
theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  exact SignProof.conjecture_proof

theorem oeis_185895_conjecture_1.disproof : ¬ (type_of% @oeis_185895_conjecture_1) := sorry
