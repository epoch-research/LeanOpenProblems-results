import FormalConjectures.Util.ProblemImports
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))


open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

lemma complex_root_of_real_splits_mem_Icc
    {p : Polynomial ℝ} {a b : ℝ}
    (hp0 : p ≠ 0) (hs : p.Splits)
    (hr : ∀ x ∈ p.roots, x ∈ Set.Icc a b) :
    ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc a b := by
  intro z hz
  have hm0 : p.map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp0
  have hzmem : z ∈ (p.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hm0).2 hz
  rw [hs.map_roots (algebraMap ℝ ℂ)] at hzmem
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hzmem
  simpa using And.intro (Complex.ofReal_im x) (hr x hx)

lemma exists_root_between_of_mul_neg {p : Polynomial ℝ} {a b : ℝ}
    (hab : a < b) (hneg : p.eval a * p.eval b < 0) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  have hcont : Continuous fun x : ℝ => p.eval x :=
    p.continuous_eval₂ (RingHom.id ℝ)
  by_cases ha : p.eval a < 0
  · have hb : 0 < p.eval b := by nlinarith
    have hsub : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) := ⟨ha.le, hb.le⟩
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc hab.le hcont.continuousOn hsub
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hxe⟩
    · intro he; subst x; simp_all
    · intro he; subst x; simp_all
  · have ha' : 0 < p.eval a := by
      have : p.eval a ≠ 0 := by intro h; simp [h] at hneg
      exact lt_of_le_of_ne (le_of_not_gt ha) this.symm
    have hb : p.eval b < 0 := by nlinarith
    have hsub : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) := ⟨hb.le, ha'.le⟩
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc' hab.le hcont.continuousOn hsub
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hxe⟩
    · intro he; subst x; simp_all
    · intro he; subst x; simp_all

noncomputable def alternatingRoot (p : Polynomial ℝ) (d : ℕ)
    (h : ∀ k < d, p.eval (k : ℝ) * p.eval ((k + 1 : ℕ) : ℝ) < 0) (i : Fin d) : ℝ :=
  Classical.choose (exists_root_between_of_mul_neg
    (show (i : ℝ) < ((i : ℕ) + 1 : ℕ) by exact_mod_cast Nat.lt_succ_self i)
    (h i i.isLt))

lemma alternatingRoot_spec (p : Polynomial ℝ) (d : ℕ)
    (h : ∀ k < d, p.eval (k : ℝ) * p.eval ((k + 1 : ℕ) : ℝ) < 0) (i : Fin d) :
    alternatingRoot p d h i ∈ Set.Ioo (i : ℝ) ((i : ℕ) + 1 : ℕ) ∧
      p.eval (alternatingRoot p d h i) = 0 :=
  Classical.choose_spec (exists_root_between_of_mul_neg
    (show (i : ℝ) < ((i : ℕ) + 1 : ℕ) by exact_mod_cast Nat.lt_succ_self i)
    (h i i.isLt))

lemma splits_and_roots_mem_Icc_of_alternating
    (p : Polynomial ℝ) (d : ℕ) (hd : 0 < d) (hle : p.natDegree ≤ d)
    (h : ∀ k < d, p.eval (k : ℝ) * p.eval ((k + 1 : ℕ) : ℝ) < 0) :
    p.natDegree = d ∧ p.Splits ∧ ∀ x ∈ p.roots, x ∈ Set.Icc (0 : ℝ) d := by
  have hp0 : p ≠ 0 := by
    intro hp
    have hh := h 0 hd
    simp [hp] at hh
  let r : Fin d → ℝ := alternatingRoot p d h
  have hrspec (i : Fin d) : r i ∈ Set.Ioo (i : ℝ) ((i : ℕ) + 1 : ℕ) ∧ p.eval (r i) = 0 :=
    alternatingRoot_spec p d h i
  have hrinj : Function.Injective r := by
    intro i j hij
    apply Fin.ext
    by_contra hn
    have hne : i ≠ j := fun hh => hn (congrArg Fin.val hh)
    rcases lt_or_lt_iff_ne.mpr hne with hij' | hij'
    · have hi := (hrspec i).1.2
      have hj := (hrspec j).1.1
      rw [hij] at hi
      norm_num at hi hj
      have hc : ((i : ℕ) + 1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij'
      exact (not_lt_of_ge hc) (lt_trans hj hi)
    · have hj := (hrspec j).1.2
      have hi := (hrspec i).1.1
      rw [hij] at hi
      norm_num at hi hj
      have hc : ((j : ℕ) + 1 : ℝ) ≤ (i : ℕ) := by exact_mod_cast hij'
      exact (not_lt_of_ge hc) (lt_trans hi hj)
  have hrmem (i : Fin d) : r i ∈ p.roots :=
    (Polynomial.mem_roots hp0).2 (hrspec i).2
  let S : Finset ℝ := Finset.univ.image r
  have hScard : S.card = d := by
    rw [Finset.card_image_of_injective _ hrinj, Finset.card_univ, Fintype.card_fin]
  have hSsub : S ⊆ p.roots.toFinset := by
    intro x hx
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simpa using hrmem i
  have hcardlower : d ≤ p.roots.toFinset.card := hScard ▸ Finset.card_le_card hSsub
  have hnat : p.natDegree = d := by
    apply Nat.le_antisymm hle
    exact hcardlower.trans (Multiset.toFinset_card_le _ |>.trans (Polynomial.card_roots' p))
  have hrootcard : p.roots.card = d := by
    apply Nat.le_antisymm
    · simpa [hnat] using Polynomial.card_roots' p
    · exact hcardlower.trans (Multiset.toFinset_card_le _)
  have hRcard : p.roots.toFinset.card = d := by
    apply Nat.le_antisymm
    · exact (Multiset.toFinset_card_le _).trans_eq hrootcard
    · exact hcardlower
  have hs : p.Splits := Polynomial.splits_iff_card_roots.2 (by simpa [hnat, hrootcard])
  refine ⟨hnat, hs, ?_⟩
  intro x hx
  have hSeq : S = p.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by simp [hScard, hRcard])
  have hxS : x ∈ S := by rw [hSeq]; simpa using hx
  simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hxS
  obtain ⟨i, rfl⟩ := hxS
  have hi := (hrspec i).1
  constructor
  · exact le_trans (by positivity : (0 : ℝ) ≤ (i : ℕ)) hi.1.le
  · exact hi.2.le.trans (by
      exact_mod_cast (show (i : ℕ) + 1 ≤ d from i.isLt))

namespace Transfer

noncomputable section

abbrev PR := Polynomial ℝ

def p (u : PR) : PR := 5 * u^2 - 5 * u + 1
def pm (u : PR) : PR := u^2 - u + C (1/5 : ℝ)
def a (u : PR) : PR := (2*u+1) * (2*u+2) * p u
def c (u : PR) : PR := 4 * (55*u^4 - 34*u^2 + 3)

structure M where
  e00 : PR
  e01 : PR
  e10 : PR
  e11 : PR

def M.one : M := ⟨1, 0, 0, 1⟩
def M.mul (u v : M) : M :=
  ⟨u.e00*v.e00 + u.e01*v.e10, u.e00*v.e01 + u.e01*v.e11,
   u.e10*v.e00 + u.e11*v.e10, u.e10*v.e01 + u.e11*v.e11⟩

def t (u : PR) : M := ⟨c u, a (-u), a u, 0⟩

def block : ℕ → M
  | 0 => M.one
  | j+1 => (block j).mul (t (X - C (j+1 : ℝ)))

def B (j : ℕ) : PR := (block j).e01

def E (j : ℕ) : PR :=
  (X - C (j+1 : ℝ)) * (X - C ((j : ℝ) + 1/2)) *
    (Finset.range (j-1)).prod (fun k => pm (X - C (k+1 : ℝ)))

def F (j : ℕ) : PR := B j /ₘ E j

lemma pm_X_sub_C_monic (x : ℝ) : (pm (X - C x)).Monic := by
  rw [show pm (X-C x) = X^2 + (-(2*C x+1)*X + C (x^2+x+(1/5:ℝ))) by
    simp [pm]; ring]
  apply monic_X_pow_add
  compute_degree
  norm_num

lemma five_pm (u : PR) : 5 * pm u = p u := by
  have hc : (5 : PR) * C (1/5 : ℝ) = 1 := by
    rw [show (5 : PR) = C 5 by simpa using (C_ofNat (R := ℝ) 5).symm, ← C_mul]
    norm_num
  simp [pm, p]
  norm_num
  linear_combination hc

lemma E_monic (j : ℕ) : (E j).Monic := by
  unfold E
  apply Polynomial.Monic.mul
  · exact (monic_X_sub_C _).mul (monic_X_sub_C _)
  · induction (Finset.range (j-1)) using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      rw [Finset.prod_insert hk]
      exact (pm_X_sub_C_monic _).mul ih

lemma pair_divisible (u : PR) :
    pm u ∣ ((t u).mul (t (u - 1))).e00 ∧
      pm u ∣ ((t u).mul (t (u - 1))).e01 ∧
      pm u ∣ ((t u).mul (t (u - 1))).e10 ∧
      pm u ∣ ((t u).mul (t (u - 1))).e11 := by
  let q0 := 2440*u^6 - 7320*u^5 + 3813*u^4 + 4574*u^3 - 3112*u^2 - 395*u + 288
  let q1 := 55*u^4 - 34*u^2 + 3
  let q2 := 55*u^4 - 220*u^3 + 296*u^2 - 152*u + 24
  constructor
  · refine ⟨20*q0, ?_⟩
    rw [show ((t u).mul (t (u-1))).e00 = 4*p u*q0 by simp [M.mul,t,a,c,p,q0]; ring,
      ← five_pm]
    ring
  constructor
  · refine ⟨40*(u-2)*(2*u-3)*q1, ?_⟩
    rw [show ((t u).mul (t (u-1))).e01 = 8*(u-2)*(2*u-3)*p u*q1 by
      simp [M.mul,t,a,c,p,q1]; ring, ← five_pm]
    ring
  constructor
  · refine ⟨40*(u+1)*(2*u+1)*q2, ?_⟩
    rw [show ((t u).mul (t (u-1))).e10 = 8*(u+1)*(2*u+1)*p u*q2 by
      simp [M.mul,t,a,c,p,q2]; ring, ← five_pm]
    ring
  · refine ⟨20*(u-2)*(u+1)*(2*u-3)*(2*u+1)*p u, ?_⟩
    rw [show ((t u).mul (t (u-1))).e11 =
        4*(u-2)*(u+1)*(2*u-3)*(2*u+1)*(p u)^2 by
      simp [M.mul,t,a,c,p]; ring, ← five_pm]
    ring

end

end Transfer

namespace Transfer
noncomputable section

noncomputable def sp (k : ℕ) : PR := pm (X-C (k : ℝ))
@[simp] theorem sp_eq (k : ℕ) : sp k = pm (X-C (k : ℝ)) := by rfl

private noncomputable def rootGap : ℝ := Real.sqrt 5 / 5
private noncomputable def rootLo : ℝ := (1 - rootGap) / 2
private noncomputable def rootHi : ℝ := (1 + rootGap) / 2

private lemma rootGap_pos : 0 < rootGap := by
  unfold rootGap
  positivity

private lemma rootGap_lt_one : rootGap < 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 5 by norm_num)
  unfold rootGap
  nlinarith

private lemma rootLo_unit : 0 < rootLo ∧ rootLo < 1 := by
  unfold rootLo
  constructor <;> nlinarith [rootGap_pos, rootGap_lt_one]

private lemma rootHi_unit : 0 < rootHi ∧ rootHi < 1 := by
  unfold rootHi
  constructor <;> nlinarith [rootGap_pos, rootGap_lt_one]

private lemma nat_add_unit_ne {a b : ℕ} (hab : a ≠ b) {u v : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    (a : ℝ) + u ≠ (b : ℝ) + v := by
  intro h
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hi : a + 1 ≤ b := by omega
    have hiR : (a : ℝ) + 1 ≤ b := by exact_mod_cast hi
    linarith
  · have hi : b + 1 ≤ a := by omega
    have hiR : (b : ℝ) + 1 ≤ a := by exact_mod_cast hi
    linarith

private lemma pm_shift_factor (a : ℕ) :
    pm (X - C (a : ℝ)) =
      (X - C ((a : ℝ) + rootLo)) * (X - C ((a : ℝ) + rootHi)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  apply Polynomial.funext
  intro x
  simp [pm, rootLo, rootHi, rootGap]
  nlinarith

lemma pm_shift_coprime {a b : ℕ} (hab : a ≠ b) :
    IsCoprime (pm (X - C (a : ℝ))) (pm (X - C (b : ℝ))) := by
  rw [pm_shift_factor a, pm_shift_factor b]
  apply IsCoprime.mul_left
  · apply IsCoprime.mul_right
    · apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr (nat_add_unit_ne hab rootLo_unit.1 rootLo_unit.2
        rootLo_unit.1 rootLo_unit.2)).isUnit
    · apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr (nat_add_unit_ne hab rootLo_unit.1 rootLo_unit.2
        rootHi_unit.1 rootHi_unit.2)).isUnit
  · apply IsCoprime.mul_right
    · apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr (nat_add_unit_ne hab rootHi_unit.1 rootHi_unit.2
        rootLo_unit.1 rootLo_unit.2)).isUnit
    · apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr (nat_add_unit_ne hab rootHi_unit.1 rootHi_unit.2
        rootHi_unit.1 rootHi_unit.2)).isUnit

lemma sp_coprime {a b : ℕ} (h : a ≠ b) : IsCoprime (sp a) (sp b) := by
  simpa using pm_shift_coprime h

lemma prod_pm_dvd {N : ℕ} {z : PR}
    (hz : ∀ k < N, sp (k+1) ∣ z) : (Finset.range N).prod (fun k => sp (k+1)) ∣ z := by
  apply Finset.prod_dvd_of_coprime
  · intro k hk l hl hkl
    exact sp_coprime (fun h => hkl (Nat.add_right_cancel h))
  · intro k hk
    exact hz k (Finset.mem_range.mp hk)

lemma M.mul_assoc (u v w : M) : (u.mul v).mul w = u.mul (v.mul w) := by
  cases u with | mk a b c d =>
  cases v with | mk e f g h =>
  cases w with | mk i j k l =>
  simp only [M.mul]
  rw [M.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

lemma M.one_mul (u : M) : M.one.mul u = u := by cases u <;> simp [M.one, M.mul]
lemma M.mul_one (u : M) : u.mul M.one = u := by cases u <;> simp [M.one, M.mul]

private def DvdM (q : PR) (u : M) : Prop :=
  q ∣ u.e00 ∧ q ∣ u.e01 ∧ q ∣ u.e10 ∧ q ∣ u.e11

private lemma DvdM.mul_left {q : PR} {u : M} (h : DvdM q u) (v : M) :
    DvdM q (v.mul u) := by
  rcases h with ⟨h00,h01,h10,h11⟩
  simp only [DvdM, M.mul]
  exact ⟨dvd_add (dvd_mul_of_dvd_right h00 _) (dvd_mul_of_dvd_right h10 _),
    dvd_add (dvd_mul_of_dvd_right h01 _) (dvd_mul_of_dvd_right h11 _),
    dvd_add (dvd_mul_of_dvd_right h00 _) (dvd_mul_of_dvd_right h10 _),
    dvd_add (dvd_mul_of_dvd_right h01 _) (dvd_mul_of_dvd_right h11 _)⟩

private lemma DvdM.mul_right {q : PR} {u : M} (h : DvdM q u) (v : M) :
    DvdM q (u.mul v) := by
  rcases h with ⟨h00,h01,h10,h11⟩
  simp only [DvdM, M.mul]
  exact ⟨dvd_add (dvd_mul_of_dvd_left h00 _) (dvd_mul_of_dvd_left h01 _),
    dvd_add (dvd_mul_of_dvd_left h00 _) (dvd_mul_of_dvd_left h01 _),
    dvd_add (dvd_mul_of_dvd_left h10 _) (dvd_mul_of_dvd_left h11 _),
    dvd_add (dvd_mul_of_dvd_left h10 _) (dvd_mul_of_dvd_left h11 _)⟩

private lemma pair_DvdM (u : PR) : DvdM (pm u) ((t u).mul (t (u-1))) :=
  pair_divisible u

lemma block_succ_succ (j : ℕ) :
    block (j+2) = (block j).mul ((t (X-C (j+1 : ℝ))).mul (t (X-C (j+2 : ℝ)))) := by
  rw [show j+2 = (j+1)+1 by omega, block, block, M.mul_assoc]
  congr 2
  apply congrArg t
  apply Polynomial.funext
  intro x
  simp
  push_cast
  ring

lemma internal_prod_dvd_block (j : ℕ) :
    DvdM ((Finset.range (j-1)).prod (fun k => sp (k+1))) (block j) := by
  induction j using Nat.twoStepInduction with
  | zero => simp [DvdM, block, M.one]
  | one => simp [DvdM, block, M.one, M.mul, t]
  | more j ih0 ih1 =>
    have hG : DvdM ((Finset.range j).prod (fun k => sp (k+1)))
        (block (j+2)) := by
      rw [show j+2=(j+1)+1 by omega, block]
      exact ih1.mul_right _
    have hnew : DvdM (sp (j+1)) (block (j+2)) := by
      rw [block_succ_succ]
      have hp := pair_DvdM (X-C (j+1 : ℝ))
      have heq : X-C (j+2 : ℝ) = (X-C (j+1 : ℝ))-1 := by
        apply Polynomial.funext; intro x; simp; ring
      rw [heq]
      rw [sp_eq]
      simpa only [Nat.cast_add, Nat.cast_one] using hp.mul_left (block j)
    rcases hG with ⟨hg0,hg1,hg2,hg3⟩
    rcases hnew with ⟨hn0,hn1,hn2,hn3⟩
    have combine {z : PR} (hg : (Finset.range j).prod
        (fun k => sp (k+1)) ∣ z)
        (hn : sp (j+1) ∣ z) :
        (Finset.range (j+1)).prod (fun k => sp (k+1)) ∣ z := by
      apply prod_pm_dvd
      intro k hk
      by_cases hkj : k < j
      · exact (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hkj)).trans hg
      · have : k = j := by omega
        simpa [this] using hn
    exact ⟨combine hg0 hn0, combine hg1 hn1, combine hg2 hn2, combine hg3 hn3⟩

lemma E_eq_sp (j : ℕ) : E j =
    (X-C (j+1 : ℝ)) * (X-C ((j:ℝ)+1/2)) *
      (Finset.range (j-1)).prod (fun k => sp (k+1)) := by
  simp [E]

lemma a_reflect_factor (n : ℕ) :
    a (-(X-C (n+1 : ℝ))) =
      20 * (X-C (n+2 : ℝ)) * (X-C ((n:ℝ)+3/2)) * sp n := by
  rw [sp_eq]
  apply Polynomial.funext
  intro x
  simp [a, p, pm]
  push_cast
  ring

lemma E_dvd_B (j : ℕ) : E j ∣ B j := by
  cases j with
  | zero => exact dvd_zero _
  | succ n =>
    have hd := internal_prod_dvd_block n
    rcases hd.1 with ⟨q, hq⟩
    rw [E_eq_sp, B, block, M.mul]
    simp only [t]
    rw [a_reflect_factor]
    by_cases hn : n = 0
    · subst n
      refine ⟨20 * sp 0, ?_⟩
      apply Polynomial.funext
      intro x
      simp [block, M.one]
      ring
    · refine ⟨20*q, ?_⟩
      rw [hq]
      rw [show n+1-1=n by omega, show n=(n-1)+1 by omega, Finset.prod_range_succ]
      apply Polynomial.funext
      intro x
      simp
      push_cast
      ring

lemma E_mul_F (j : ℕ) : E j * F j = B j := by
  have hm : B j %ₘ E j = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (E_monic j)).mpr (E_dvd_B j)
  have ha := Polynomial.modByMonic_add_div (B j) (E_monic j)
  rw [hm, zero_add] at ha
  simpa [F] using ha

end
end Transfer
set_option Elab.async true



namespace Transfer
noncomputable section

private def DegM (n : ℕ) (u : M) : Prop :=
  u.e00.natDegree ≤ n ∧ u.e01.natDegree ≤ n ∧ u.e10.natDegree ≤ n ∧ u.e11.natDegree ≤ n

lemma t_degree (x : ℝ) : DegM 4 (t (X-C x)) := by
  simp only [DegM, t]
  simp [a, c, p]
  repeat' apply And.intro
  all_goals compute_degree <;> norm_num

private lemma DegM.mul {m n : ℕ} {u v : M} (hu : DegM m u) (hv : DegM n v) :
    DegM (m+n) (u.mul v) := by
  rcases hu with ⟨hu0,hu1,hu2,hu3⟩
  rcases hv with ⟨hv0,hv1,hv2,hv3⟩
  simp only [DegM, M.mul]
  constructor
  · exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_mul_le).trans (Nat.add_le_add hu0 hv0))
      ((natDegree_mul_le).trans (Nat.add_le_add hu1 hv2)))
  constructor
  · exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_mul_le).trans (Nat.add_le_add hu0 hv1))
      ((natDegree_mul_le).trans (Nat.add_le_add hu1 hv3)))
  constructor
  · exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_mul_le).trans (Nat.add_le_add hu2 hv0))
      ((natDegree_mul_le).trans (Nat.add_le_add hu3 hv2)))
  · exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_mul_le).trans (Nat.add_le_add hu2 hv1))
      ((natDegree_mul_le).trans (Nat.add_le_add hu3 hv3)))

lemma block_degree (j : ℕ) : DegM (4*j) (block j) := by
  induction j with
  | zero => simp [DegM, block, M.one]
  | succ j ih =>
    rw [block]
    have := ih.mul (t_degree (j+1))
    simpa [Nat.mul_succ] using this

lemma F_natDegree_le (j : ℕ) : (F j).natDegree ≤ 2*j := by
  cases j with
  | zero => change (0 /ₘ E 0).natDegree ≤ 0; simp
  | succ j =>
    rw [F, natDegree_divByMonic _ (E_monic (j+1))]
    have hB : (B (j+1)).natDegree ≤ 4*(j+1) := (block_degree (j+1)).2.1
    have hpm (x : ℝ) : (pm (X-C x)).natDegree = 2 := by
      simp [pm]
      compute_degree
      norm_num
    have hE : (E (j+1)).natDegree = 2*(j+1) := by
      unfold E
      rw [natDegree_mul (monic_X_sub_C _ |>.mul (monic_X_sub_C _) |>.ne_zero)
        (Finset.prod_ne_zero_iff.mpr (fun k hk => (pm_X_sub_C_monic _).ne_zero))]
      rw [natDegree_mul (monic_X_sub_C _).ne_zero (monic_X_sub_C _).ne_zero]
      rw [natDegree_prod _ _ (fun k hk => (pm_X_sub_C_monic _).ne_zero)]
      simp_rw [natDegree_X_sub_C, hpm]
      simp
      omega
    rw [hE]
    omega

end
end Transfer

namespace Transfer

structure RM where
  e00 : ℝ
  e01 : ℝ
  e10 : ℝ
  e11 : ℝ

def RM.one : RM := ⟨1,0,0,1⟩
def RM.mul (u v : RM) : RM :=
  ⟨u.e00*v.e00+u.e01*v.e10, u.e00*v.e01+u.e01*v.e11,
   u.e10*v.e00+u.e11*v.e10, u.e10*v.e01+u.e11*v.e11⟩
def RM.eval (x : ℝ) (u : M) : RM := ⟨u.e00.eval x, u.e01.eval x, u.e10.eval x, u.e11.eval x⟩

def rp (x : ℝ) := 5*x^2-5*x+1
def ra (x : ℝ) := (2*x+1)*(2*x+2)*rp x
def rc (x : ℝ) := 4*(55*x^4-34*x^2+3)
def rt (x : ℝ) : RM := ⟨rc x, ra (-x), ra x, 0⟩

def RM.NN (u : RM) : Prop := 0 ≤ u.e00 ∧ 0 ≤ u.e01 ∧ 0 ≤ u.e10 ∧ 0 ≤ u.e11
def RM.Pos (u : RM) : Prop := 0 < u.e00 ∧ 0 < u.e01 ∧ 0 < u.e10 ∧ 0 < u.e11
def RM.SPos (u : RM) : Prop := 0 < u.e00 ∧ 0 < u.e01 ∧ 0 < u.e10 ∧ 0 ≤ u.e11
def RM.NegRow (u : RM) : Prop := u.e00 < 0 ∧ u.e01 < 0 ∧ u.e10 = 0 ∧ u.e11 = 0
def RM.NegCol (u : RM) : Prop := u.e00 < 0 ∧ u.e01 = 0 ∧ u.e10 < 0 ∧ u.e11 = 0

lemma eval_t (x y : ℝ) : RM.eval x (t (X-C y)) = rt (x-y) := by
  simp [RM.eval, t, rt, a, c, p, ra, rc, rp]

lemma eval_mul (x : ℝ) (u v : M) : RM.eval x (u.mul v) = (RM.eval x u).mul (RM.eval x v) := by
  simp [RM.eval, RM.mul, M.mul]

lemma eval_block_succ (x : ℝ) (j : ℕ) :
    RM.eval x (block (j+1)) = (RM.eval x (block j)).mul (rt (x-(j+1))) := by
  rw [block, eval_mul, eval_t]

lemma rp_pos_of_one_le {x : ℝ} (h : 1 ≤ x) : 0 < rp x := by
  simp [rp]
  nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x-1 by linarith)]
lemma rp_pos_of_nonpos {x : ℝ} (h : x ≤ 0) : 0 < rp x := by
  simp [rp]
  nlinarith [mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ 1-x by linarith)]
lemma ra_pos_of_one_le {x : ℝ} (h : 1 ≤ x) : 0 < ra x := by
  have := rp_pos_of_one_le h
  simp [ra]
  positivity
lemma ra_pos_of_le_neg_three_halves {x : ℝ} (h : x ≤ -(3/2 : ℝ)) : 0 < ra x := by
  have hp := rp_pos_of_nonpos (le_trans h (by norm_num))
  simp [ra]
  have h1 : 2*x+1 < 0 := by linarith
  have h2 : 2*x+2 < 0 := by linarith
  nlinarith [mul_pos_of_neg_of_neg h1 h2]
lemma rc_pos_of_sq_one_le {x : ℝ} (h : 1 ≤ x^2) : 0 < rc x := by
  simp [rc]
  have : 0 ≤ x^2 := sq_nonneg x
  nlinarith [mul_nonneg (show 0 ≤ x^2-1 by linarith) (show 0 ≤ 55*x^2+21 by positivity)]

lemma rt_spos_of_three_halves_le {x : ℝ} (h : (3/2:ℝ) ≤ x) : RM.SPos (rt x) := by
  have hc := rc_pos_of_sq_one_le (x := x) (by nlinarith [mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ x+1 by linarith)])
  have ha := ra_pos_of_one_le (x := x) (by linarith)
  have had := ra_pos_of_le_neg_three_halves (x := -x) (by linarith)
  exact ⟨hc, had, ha, by norm_num [rt]⟩

lemma rt_spos_of_le_neg_three_halves {x : ℝ} (h : x ≤ -(3/2:ℝ)) : RM.SPos (rt x) := by
  have hc := rc_pos_of_sq_one_le (x := x) (by nlinarith [mul_nonneg_of_nonpos_of_nonpos (show x-1 ≤ 0 by linarith) (show x+1 ≤ 0 by linarith)])
  have ha := ra_pos_of_le_neg_three_halves h
  have had := ra_pos_of_one_le (x := -x) (by linarith)
  exact ⟨hc, had, ha, by norm_num [rt]⟩

lemma rt_neg_half : RM.NegRow (rt (-1/2)) := by norm_num [RM.NegRow, rt, rc, ra, rp]
lemma rt_pos_half : RM.NegCol (rt (1/2)) := by norm_num [RM.NegCol, rt, rc, ra, rp]

lemma RM.SPos.mul (hu : RM.SPos u) (hv : RM.SPos v) : RM.Pos (u.mul v) := by
  rcases hu with ⟨a,b,c,d⟩; rcases hv with ⟨e,f,g,h⟩
  simp only [RM.Pos, RM.mul]
  exact ⟨add_pos (mul_pos a e) (mul_pos b g),
    add_pos_of_pos_of_nonneg (mul_pos a f) (mul_nonneg b.le h),
    add_pos_of_pos_of_nonneg (mul_pos c e) (mul_nonneg d g.le),
    add_pos_of_pos_of_nonneg (mul_pos c f) (mul_nonneg d h)⟩
lemma RM.Pos.spos (h : RM.Pos u) : RM.SPos u := ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.le⟩
lemma RM.Pos.mul_spos (hu : RM.Pos u) (hv : RM.SPos v) : RM.Pos (u.mul v) := hu.spos.mul hv
lemma RM.SPos.mul_pos (hu : RM.SPos u) (hv : RM.Pos v) : RM.Pos (u.mul v) := hu.mul hv.spos

lemma RM.Pos.mul (hu : RM.Pos u) (hv : RM.Pos v) : RM.Pos (u.mul v) := by
  rcases hu with ⟨a,b,c,d⟩; rcases hv with ⟨e,f,g,h⟩
  simp only [RM.Pos, RM.mul]
  exact ⟨add_pos (mul_pos a e) (mul_pos b g), add_pos (mul_pos a f) (mul_pos b h),
    add_pos (mul_pos c e) (mul_pos d g), add_pos (mul_pos c f) (mul_pos d h)⟩
lemma RM.NegCol.mul_negRow (hu : RM.NegCol u) (hv : RM.NegRow v) : RM.Pos (u.mul v) := by
  rcases hu with ⟨a,b,c,d⟩; rcases hv with ⟨e,f,g,h⟩
  simp only [RM.Pos, RM.mul]
  rw [b, d, g, h]
  simp only [mul_zero, zero_mul, add_zero]
  exact ⟨mul_pos_of_neg_of_neg a e, mul_pos_of_neg_of_neg a f,
    mul_pos_of_neg_of_neg c e, mul_pos_of_neg_of_neg c f⟩
lemma RM.SPos.mul_negCol (hu : RM.SPos u) (hv : RM.NegCol v) : RM.NegCol (u.mul v) := by
  rcases hu with ⟨a,b,c,d⟩; rcases hv with ⟨e,f,g,h⟩
  simp only [RM.NegCol, RM.mul]
  rw [f, h]
  simp only [mul_zero, add_zero]
  exact ⟨add_neg (mul_neg_of_pos_of_neg a e) (mul_neg_of_pos_of_neg b g), True.intro,
    add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg c e) (mul_nonpos_of_nonneg_of_nonpos d g.le), True.intro⟩
lemma RM.NegRow.mul_spos (hu : RM.NegRow u) (hv : RM.SPos v) : RM.NegRow (u.mul v) := by
  rcases hu with ⟨a,b,c,d⟩; rcases hv with ⟨e,f,g,h⟩
  simp only [RM.NegRow, RM.mul]
  rw [c, d]
  simp only [zero_mul, zero_add]
  exact ⟨add_neg (mul_neg_of_neg_of_pos a e) (mul_neg_of_neg_of_pos b g),
    add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos a f) (mul_nonpos_of_nonpos_of_nonneg b.le h), True.intro, True.intro⟩

end Transfer

namespace Transfer

lemma RM.mul_assoc (u v w : RM) : (u.mul v).mul w = u.mul (v.mul w) := by
  cases u; cases v; cases w
  simp only [RM.mul]
  rw [RM.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩
lemma RM.one_mul (u : RM) : RM.one.mul u = u := by cases u <;> simp [RM.one, RM.mul]
lemma RM.mul_one (u : RM) : u.mul RM.one = u := by cases u <;> simp [RM.one, RM.mul]
lemma eval_one (x : ℝ) : RM.eval x M.one = RM.one := by simp [RM.eval, M.one, RM.one]

def rb (x : ℝ) : ℕ → RM
  | 0 => RM.one
  | j+1 => (rb x j).mul (rt (x-(j+1)))

lemma eval_block_eq_rb (x : ℝ) (j : ℕ) : RM.eval x (block j) = rb x j := by
  induction j with
  | zero => simp [block, rb, eval_one]
  | succ j ih => rw [eval_block_succ, ih, rb]

lemma rb_succ_shift (x : ℝ) (j : ℕ) : rb (x+1) (j+1) = (rt x).mul (rb x j) := by
  induction j with
  | zero => simp [rb, RM.mul_one, RM.one_mul]
  | succ j ih =>
    rw [rb, ih, rb, RM.mul_assoc]
    congr 2
    push_cast
    congr 1
    ring

lemma half_prefix_negCol {l : ℕ} (hl : 1 ≤ l) :
    RM.NegCol (rb ((l:ℝ)+1/2) l) := by
  induction l with
  | zero => omega
  | succ l ih =>
    rw [show ((l+1:ℕ):ℝ)+1/2 = ((l:ℝ)+1/2)+1 by push_cast; ring,
      rb_succ_shift]
    by_cases h0 : l = 0
    · subst l
      simpa [rb, RM.mul_one] using rt_pos_half
    · have hs : RM.SPos (rt ((l:ℝ)+1/2)) :=
        rt_spos_of_three_halves_le (by
          have : (1:ℝ) ≤ l := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h0)
          linarith)
      exact hs.mul_negCol (ih (Nat.one_le_iff_ne_zero.mpr h0))

lemma half_pair_pos {l : ℕ} (hl : 1 ≤ l) :
    RM.Pos (rb ((l:ℝ)+1/2) (l+1)) := by
  rw [rb]
  have he : (l:ℝ)+1/2-(↑l+1) = (-1/2:ℝ) := by push_cast; ring
  rw [he]
  exact (half_prefix_negCol hl).mul_negRow rt_neg_half

lemma half_after_pair_pos {l q : ℕ} (hl : 1 ≤ l) :
    RM.Pos (rb ((l:ℝ)+1/2) (l+1+q)) := by
  induction q with
  | zero => simpa using half_pair_pos hl
  | succ q ih =>
    rw [show l+1+(q+1)=(l+1+q)+1 by omega, rb]
    apply ih.mul_spos
    apply rt_spos_of_le_neg_three_halves
    push_cast
    have hq : (0 : ℝ) ≤ q := by positivity
    linarith

lemma half_zero_negRow (q : ℕ) :
    RM.NegRow (rb (1/2) (1+q)) := by
  induction q with
  | zero =>
    norm_num only [Nat.add_zero]
    simp only [rb, RM.one_mul]
    norm_num
    convert rt_neg_half using 1 <;> norm_num
  | succ q ih =>
    rw [show 1+(q+1)=(1+q)+1 by omega, rb]
    apply ih.mul_spos
    apply rt_spos_of_le_neg_three_halves
    push_cast
    have hq : (0 : ℝ) ≤ q := by positivity
    linarith

lemma B_half_sign {j k : ℕ} (hj : 1 ≤ j) (hk : k ≤ 2*j) (hodd : Odd k) :
    if k = 1 then (B j).eval ((k:ℝ)/2) < 0 else 0 < (B j).eval ((k:ℝ)/2) := by
  obtain ⟨l, rfl⟩ := hodd
  have hjl : l+1 ≤ j := by omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hjl
  simp only [B]
  have hx : ((2*l+1:ℕ):ℝ)/2 = (l:ℝ)+1/2 := by push_cast; ring
  rw [hx]
  by_cases hl : l = 0
  · subst l
    rw [if_pos (by omega)]
    have hh := (half_zero_negRow q).2.1
    rw [← eval_block_eq_rb] at hh
    simpa [RM.eval] using hh
  · rw [if_neg (by omega)]
    have hh := (half_after_pair_pos (l:=l) (q:=q) (Nat.one_le_iff_ne_zero.mpr hl)).2.1
    rw [← eval_block_eq_rb] at hh
    simpa [RM.eval] using hh

end Transfer

namespace Transfer

lemma ra_nonneg_of_le_neg_one {x : ℝ} (h : x ≤ -1) : 0 ≤ ra x := by
  have hp := rp_pos_of_nonpos (le_trans h (by norm_num))
  have h1 : 2*x+1 < 0 := by linarith
  have h2 : 2*x+2 ≤ 0 := by linarith
  simp [ra]
  exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos h1.le h2) hp.le

lemma ra_int_nonneg (z : ℤ) : 0 ≤ ra (z : ℝ) := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hz' : z ≤ -1 := by omega
    exact ra_nonneg_of_le_neg_one (by exact_mod_cast hz')
  · norm_num [ra, rp]
  · exact (ra_pos_of_one_le (by exact_mod_cast hz)).le

lemma rc_int_pos (z : ℤ) : 0 < rc (z : ℝ) := by
  by_cases hz : z = 0
  · subst z; norm_num [rc]
  · apply rc_pos_of_sq_one_le
    have h := Int.one_le_abs hz
    have hr : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast h
    nlinarith [sq_abs (z:ℝ)]

lemma rt_int_nn (z : ℤ) : RM.NN (rt (z : ℝ)) :=
  ⟨(rc_int_pos z).le, by simpa using ra_int_nonneg (-z), ra_int_nonneg z, by norm_num [rt]⟩

def RM.Good (u : RM) : Prop := RM.NN u ∧ 0 < u.e00

lemma RM.NN.mul (hu : RM.NN u) (hv : RM.NN v) : RM.NN (u.mul v) := by
  rcases hu with ⟨a,b,c,d⟩; rcases hv with ⟨e,f,g,h⟩
  simp only [RM.NN, RM.mul]
  exact ⟨add_nonneg (mul_nonneg a e) (mul_nonneg b g),
    add_nonneg (mul_nonneg a f) (mul_nonneg b h),
    add_nonneg (mul_nonneg c e) (mul_nonneg d g),
    add_nonneg (mul_nonneg c f) (mul_nonneg d h)⟩

lemma RM.Good.mul_int (hu : RM.Good u) (z : ℤ) : RM.Good (u.mul (rt (z:ℝ))) := by
  refine ⟨hu.1.mul (rt_int_nn z), ?_⟩
  simp only [RM.mul]
  exact add_pos_of_pos_of_nonneg (mul_pos hu.2 (rc_int_pos z))
    (mul_nonneg hu.1.2.1 (ra_int_nonneg z))

lemma rb_int_good (r : ℤ) (j : ℕ) : RM.Good (rb (r:ℝ) j) := by
  induction j with
  | zero => exact ⟨by norm_num [rb, RM.NN, RM.one], by norm_num [rb, RM.one]⟩
  | succ j ih =>
    rw [rb]
    let z : ℤ := r-(j+1)
    have he : (r:ℝ)-(j+1) = (z:ℝ) := by simp [z]
    rw [he]
    exact ih.mul_int z

lemma ra_nat_pos (n : ℕ) : 0 < ra (n:ℝ) := by
  cases n with
  | zero => norm_num [ra, rp]
  | succ n => exact ra_pos_of_one_le (by exact_mod_cast Nat.le_add_left 1 n)

lemma B_even_pos {j k : ℕ} (hj : 1 ≤ j) (hk : k ≤ 2*j) (heven : Even k) :
    0 < (B j).eval ((k:ℝ)/2) := by
  obtain ⟨r, rfl⟩ := heven
  have hrj : r ≤ j := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hr : r ≤ n+1 := hrj
  have he : (((r+r:ℕ):ℝ))/2 = (r:ℝ) := by push_cast; ring
  rw [he]
  simp only [B]
  have hb := eval_block_eq_rb (r:ℝ) (n+1)
  have hg := rb_int_good (r:ℤ) n
  rw [rb] at hb
  have hx : (r:ℝ)-(n+1) = -((n+1-r:ℕ):ℝ) := by
    rw [Nat.cast_sub hr]
    push_cast
    ring
  rw [hx] at hb
  have hp := ra_nat_pos (n+1-r)
  have hv : 0 < (rb (r:ℝ) n).e00 * (rt (-((n+1-r:ℕ):ℝ))).e01 := by
    simp only [rt]
    exact mul_pos hg.2 (by simpa using hp)
  change 0 < (RM.eval (r:ℝ) (block (n+1))).e01
  rw [hb]
  simpa [RM.mul, rt] using hv

end Transfer
set_option Elab.async false

namespace Transfer

noncomputable def rpm (x : ℝ) := x^2-x+1/5
lemma rpm_pos_of_one_le {x : ℝ} (h : 1 ≤ x) : 0 < rpm x := by
  simp [rpm]
  nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x-1 by linarith)]
lemma rpm_pos_of_nonpos {x : ℝ} (h : x ≤ 0) : 0 < rpm x := by
  simp [rpm]
  nlinarith [mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ 1-x by linarith)]
lemma rpm_int_pos (z : ℤ) : 0 < rpm (z:ℝ) := by
  rcases le_total z 0 with h | h
  · exact rpm_pos_of_nonpos (by exact_mod_cast h)
  · by_cases hz : z = 0
    · subst z; norm_num [rpm]
    · exact rpm_pos_of_one_le (by
        have : 1 ≤ z := by omega
        exact_mod_cast this)
lemma rpm_int_half_pos {z : ℤ} (hz : z ≠ 0) : 0 < rpm ((z:ℝ)+1/2) := by
  rcases lt_or_gt_of_ne hz with h | h
  · apply rpm_pos_of_nonpos
    have hz1 : z ≤ -1 := by omega
    have hzR : (z:ℝ) ≤ -1 := by exact_mod_cast hz1
    linarith
  · apply rpm_pos_of_one_le
    have : 1 ≤ z := by omega
    have : (1:ℝ) ≤ z := by exact_mod_cast this
    linarith
lemma rpm_half_neg : rpm (1/2) < 0 := by norm_num [rpm]
lemma eval_pm (x y : ℝ) : (pm (X-C y)).eval x = rpm (x-y) := by simp [pm, rpm]

lemma E_even_pos {j k : ℕ} (hj : 1 ≤ j) (hk : k ≤ 2*j) (he : Even k) :
    0 < (E j).eval ((k:ℝ)/2) := by
  obtain ⟨r, rfl⟩ := he
  have hrj : r ≤ j := by omega
  have hx : (((r+r:ℕ):ℝ))/2 = (r:ℝ) := by push_cast; ring
  rw [hx]
  unfold E
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have hline1 : (r:ℝ)-(j+1) < 0 := by
    have hh : (r:ℝ) < j+1 := by exact_mod_cast (show r < j+1 by omega)
    linarith
  have hline2 : (r:ℝ)-((j:ℝ)+1/2) < 0 := by
    have : (r:ℝ) ≤ j := by exact_mod_cast hrj
    linarith
  apply mul_pos (mul_pos_of_neg_of_neg hline1 hline2)
  apply Finset.prod_pos
  intro i hi
  rw [eval_pm]
  convert rpm_int_pos ((r:ℤ)-(i+1:ℕ)) using 1 <;> push_cast <;> ring

lemma E_one_pos (j : ℕ) (hj : 1 ≤ j) : 0 < (E j).eval (1/2) := by
  unfold E
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have h1 : (1/2:ℝ)-(j+1) < 0 := by
    have hh : (1:ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have h2 : (1/2:ℝ)-((j:ℝ)+1/2) < 0 := by
    have hh : (1:ℝ) ≤ j := by exact_mod_cast hj
    linarith
  apply mul_pos (mul_pos_of_neg_of_neg h1 h2)
  apply Finset.prod_pos
  intro i hi
  rw [eval_pm]
  apply rpm_pos_of_nonpos
  have : (0:ℝ) ≤ i := by positivity
  push_cast
  linarith

lemma E_odd_neg {j l : ℕ} (hj : 1 ≤ j) (hl : 1 ≤ l) (hlj : 2*l+1 ≤ 2*j) :
    (E j).eval (((2*l+1:ℕ):ℝ)/2) < 0 := by
  have hlj' : l ≤ j-1 := by omega
  have hx : (((2*l+1:ℕ):ℝ)/2) = (l:ℝ)+1/2 := by push_cast; ring
  rw [hx]
  unfold E
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have hline1 : (l:ℝ)+1/2-(j+1) < 0 := by
    have : (l:ℝ) ≤ j-1 := by exact_mod_cast hlj'
    linarith
  have hline2 : (l:ℝ)+1/2-((j:ℝ)+1/2) < 0 := by
    have : (l:ℝ) < j := by exact_mod_cast (show l < j by omega)
    linarith
  have hmem : l-1 ∈ Finset.range (j-1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.prod_erase_mul _ _ hmem]
  have hrest : 0 < ∏ i ∈ (Finset.range (j-1)).erase (l-1),
      (pm (X-C (i+1:ℝ))).eval ((l:ℝ)+1/2) := by
    apply Finset.prod_pos
    intro i hi
    rw [eval_pm]
    have hil : i ≠ l-1 := Finset.ne_of_mem_erase hi
    let z : ℤ := (l:ℤ)-(i+1:ℕ)
    have hz0 : z ≠ 0 := by
      simp [z]
      omega
    have heq : (l:ℝ)+1/2-(i+1:ℕ) = (z:ℝ)+1/2 := by simp [z]; push_cast; ring
    change 0 < rpm ((l:ℝ)+1/2-((i:ℝ)+1))
    have heq' : (l:ℝ)+1/2-((i:ℝ)+1) = (z:ℝ)+1/2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using heq
    rw [heq']
    exact rpm_int_half_pos hz0
  have hbad : (pm (X-C ((l-1)+1:ℝ))).eval ((l:ℝ)+1/2) < 0 := by
    rw [eval_pm]
    convert rpm_half_neg using 1 <;> push_cast <;> ring
  have hbad' : (pm (X-C (((l-1:ℕ):ℝ)+1))).eval ((l:ℝ)+1/2) < 0 := by
    rw [eval_pm]
    convert rpm_half_neg using 1
    rw [Nat.cast_sub hl]
    ring
  exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hline1 hline2)
    (mul_neg_of_pos_of_neg hrest hbad')

end Transfer
set_option Elab.async true

namespace Transfer

lemma eval_E_mul_F (j : ℕ) (x : ℝ) : (E j).eval x * (F j).eval x = (B j).eval x := by
  simpa [Polynomial.eval_mul] using congrArg (Polynomial.eval x) (E_mul_F j)

lemma F_even_pos {j k : ℕ} (hj : 1 ≤ j) (hk : k ≤ 2*j) (he : Even k) :
    0 < (F j).eval ((k:ℝ)/2) := by
  have hE := E_even_pos hj hk he
  have hB := B_even_pos hj hk he
  have heq := eval_E_mul_F j ((k:ℝ)/2)
  have hp : 0 < (E j).eval ((k:ℝ)/2) * (F j).eval ((k:ℝ)/2) := by linarith
  exact pos_of_mul_pos_right hp hE.le

lemma F_odd_neg {j k : ℕ} (hj : 1 ≤ j) (hk : k ≤ 2*j) (ho : Odd k) :
    (F j).eval ((k:ℝ)/2) < 0 := by
  have hB := B_half_sign hj hk ho
  have heq := eval_E_mul_F j ((k:ℝ)/2)
  by_cases hk1 : k = 1
  · subst k
    have hE := E_one_pos j hj
    have hb : (B j).eval (1/2) < 0 := by simpa using hB
    have hp : (E j).eval (1/2) * (F j).eval (1/2) < 0 := by linarith
    simpa using neg_of_mul_neg_right hp hE.le
  · obtain ⟨l, rfl⟩ := ho
    have hl : 1 ≤ l := by omega
    have hE := E_odd_neg hj hl hk
    have hk1' : 2*l+1 ≠ 1 := by omega
    rw [if_neg hk1'] at hB
    have hb : 0 < (B j).eval (((2*l+1:ℕ):ℝ)/2) := hB
    have hp : 0 < (E j).eval (((2*l+1:ℕ):ℝ)/2) *
        (F j).eval (((2*l+1:ℕ):ℝ)/2) := by linarith
    exact neg_of_mul_pos_right hp hE.le

lemma F_alternating (j : ℕ) (hj : 1 ≤ j) :
    ∀ k < 2*j, (F j).eval ((k:ℝ)/2) * (F j).eval (((k+1:ℕ):ℝ)/2) < 0 := by
  intro k hk
  rcases even_or_odd k with he | ho
  · have h0 := F_even_pos hj (by omega) he
    have h1 := F_odd_neg hj (by omega) he.add_one
    exact mul_neg_of_pos_of_neg h0 h1
  · have h0 := F_odd_neg hj (by omega) ho
    have h1 := F_even_pos hj (by omega) ho.add_one
    exact mul_neg_of_neg_of_pos h0 h1

end Transfer
set_option Elab.async false



namespace Transfer
noncomputable section

def G (j : ℕ) : PR := (F j).comp (C (1/2:ℝ) * X)
lemma eval_G (j k : ℕ) : (G j).eval (k:ℝ) = (F j).eval ((k:ℝ)/2) := by
  simp [G, Polynomial.eval_comp]
  ring_nf

lemma G_natDegree_le (j : ℕ) : (G j).natDegree ≤ 2*j := by
  have hlin : (C (1/2:ℝ) * X : PR).natDegree = 1 := by
    compute_degree
    norm_num
  calc
    (G j).natDegree ≤ (F j).natDegree * (C (1/2:ℝ) * X : PR).natDegree := natDegree_comp_le
    _ = (F j).natDegree := by rw [hlin]; simp
    _ ≤ 2*j := F_natDegree_le j

lemma G_properties (j : ℕ) (hj : 1 ≤ j) :
    (G j).natDegree = 2*j ∧ (G j).Splits ∧
      ∀ x ∈ (G j).roots, x ∈ Set.Icc (0:ℝ) ((2*j:ℕ):ℝ) := by
  apply splits_and_roots_mem_Icc_of_alternating (G j) (2*j) (by omega) (G_natDegree_le j)
  intro k hk
  rw [eval_G j k, eval_G j (k+1)]
  exact F_alternating j hj k hk

lemma G_complex_roots (j : ℕ) (hj : 1 ≤ j) :
    ∀ z : ℂ, ((G j).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) ((2*j:ℕ):ℝ) := by
  have h := G_properties j hj
  exact complex_root_of_real_splits_mem_Icc (by
    intro hz
    have hh := h.1
    rw [hz] at hh
    simp at hh
    omega) h.2.1 h.2.2

lemma F_complex_roots (j : ℕ) (hj : 1 ≤ j) :
    ∀ z : ℂ, ((F j).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) j := by
  intro z hz
  have hG : ((G j).map (algebraMap ℝ ℂ)).eval (2*z) = 0 := by
    simpa [G, Polynomial.map_comp, Polynomial.eval_comp] using hz
  have h := G_complex_roots j hj (2*z) hG
  have him : (2*z).im = 2*z.im := by simp
  have hre : (2*z).re = 2*z.re := by simp
  have hjcast : ((2*j:ℕ):ℝ) = 2*(j:ℝ) := by push_cast; ring
  rw [him, hre, hjcast] at h
  constructor
  · linarith [h.1]
  · constructor <;> linarith [h.2.1, h.2.2]

lemma F_natDegree_eq (j : ℕ) (hj : 1 ≤ j) : (F j).natDegree = 2*j := by
  have hg := (G_properties j hj).1
  rw [G, natDegree_comp] at hg
  have hlin : (C (1/2:ℝ) * X : PR).natDegree = 1 := by
    compute_degree
    norm_num
  simpa [hlin] using hg

end


noncomputable section

-- Reflection of the transfer product.
def RM.tr (u : RM) : RM := ⟨u.e00, u.e10, u.e01, u.e11⟩

lemma RM.tr_mul (u v : RM) : RM.tr (u.mul v) = (RM.tr v).mul (RM.tr u) := by
  cases u; cases v
  simp only [RM.tr, RM.mul]
  rw [RM.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

lemma RM.tr_rt (x : ℝ) : RM.tr (rt x) = rt (-x) := by
  simp only [RM.tr, rt]
  rw [RM.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [rc, ra, rp] <;> ring

lemma rb_reflect (x : ℝ) (j : ℕ) : rb ((j : ℝ) - x) j = RM.tr (rb (x+1) j) := by
  induction j with
  | zero => simp [rb, RM.tr, RM.one]
  | succ j ih =>
      calc
        rb (((j+1:ℕ):ℝ)-x) (j+1) =
            (rt ((j:ℝ)-x)).mul (rb ((j:ℝ)-x) j) := by
              convert rb_succ_shift ((j:ℝ)-x) j using 1 <;> push_cast <;> ring
        _ = (rt ((j:ℝ)-x)).mul (RM.tr (rb (x+1) j)) := by rw [ih]
        _ = RM.tr ((rb (x+1) j).mul (rt (x-(j:ℝ)))) := by
              rw [RM.tr_mul, RM.tr_rt]
              congr 2
              congr 1
              ring
        _ = RM.tr (rb (x+1) (j+1)) := by
              congr 1
              have h : rb (x+1) (j+1) =
                  (rb (x+1) j).mul (rt ((x+1)-((j+1:ℕ):ℝ))) := by
                    simp only [rb]
                    congr 2 <;> push_cast <;> ring
              rw [h]
              have ht : rt (x-(j:ℝ)) = rt ((x+1)-((j+1:ℕ):ℝ)) := by
                congr 1
                push_cast
                ring
              rw [ht]

lemma rb_overlap (x : ℝ) (j : ℕ) :
    (rt x).mul (rb x j) = (rb (x+1) j).mul (rt (x-j)) := by
  calc
    (rt x).mul (rb x j) = rb (x+1) (j+1) := (rb_succ_shift x j).symm
    _ = (rb (x+1) j).mul (rt (x-j)) := by
      have h : rb (x+1) (j+1) =
          (rb (x+1) j).mul (rt ((x+1)-((j+1:ℕ):ℝ))) := by
            simp only [rb]
            congr 2 <;> push_cast <;> ring
      rw [h]
      have ht : rt ((x+1)-((j+1:ℕ):ℝ)) = rt (x-(j:ℝ)) := by
        congr 1
        push_cast
        ring
      rw [ht]

lemma B_weighted_reflect_eval (j : ℕ) (x : ℝ) :
    ra x * (B j).eval x = ra ((j:ℝ)-x) * (B j).eval ((j:ℝ)-x) := by
  have ho := congrArg RM.e11 (rb_overlap x j)
  have hr := congrArg RM.e01 (rb_reflect x j)
  simp only [RM.mul, rt, RM.tr] at ho hr
  have hx : (B j).eval x = (rb x j).e01 := by
    rw [← eval_block_eq_rb x j]
    rfl
  have hy : (B j).eval ((j:ℝ)-x) = (rb ((j:ℝ)-x) j).e01 := by
    rw [← eval_block_eq_rb ((j:ℝ)-x) j]
    rfl
  rw [hx, hy, hr]
  simpa [mul_comm] using ho

lemma eval_a (x : ℝ) : (a X).eval x = ra x := by simp [a, p, ra, rp]

def reflect (j : ℕ) (q : PR) : PR := q.comp (C (j:ℝ) - X)

@[simp] lemma eval_reflect (j : ℕ) (q : PR) (x : ℝ) :
    (reflect j q).eval x = q.eval ((j:ℝ)-x) := by
  simp [reflect, Polynomial.eval_comp]

lemma B_weighted_reflect (j : ℕ) :
    a X * B j = reflect j (a X * B j) := by
  apply Polynomial.funext
  intro x
  rw [eval_reflect]
  simp only [Polynomial.eval_mul, eval_a]
  exact B_weighted_reflect_eval j x

private lemma rpm_reflect (x : ℝ) : rpm (1-x) = rpm x := by simp [rpm]; ring

private lemma prod_rpm_reflect (j : ℕ) (x : ℝ) :
    (Finset.range j).prod (fun k => rpm ((j:ℝ)-x-(k:ℝ))) =
      (Finset.range j).prod (fun k => rpm (x-(k:ℝ))) := by
  simp_rw [← Fin.prod_univ_eq_prod_range]
  calc
    (∏ k : Fin j, rpm ((j:ℝ)-x-(k:ℕ))) =
        ∏ k : Fin j, rpm (x-((Fin.rev k:Fin j):ℕ)) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [← rpm_reflect, Fin.val_rev]
          rw [Nat.cast_sub (by omega : (k:ℕ)+1 ≤ j)]
          push_cast
          congr 1
          ring
    _ = ∏ k : Fin j, rpm (x-(k:ℕ)) :=
      by simpa [Fin.revPerm] using
        (Equiv.prod_comp Fin.revPerm (fun k : Fin j => rpm (x-(k:ℕ))))

private lemma rpm_mul_prod_shift (n : ℕ) (x : ℝ) :
    rpm x * (Finset.range n).prod (fun k => rpm (x-((k+1:ℕ):ℝ))) =
      (Finset.range (n+1)).prod (fun k => rpm (x-(k:ℝ))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih]
      ring

lemma a_mul_E_eval_formula (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    (a X * E j).eval x = 20 * (x+1/2) * (x+1) *
      (x-(j:ℝ)-1) * (x-(j:ℝ)-1/2) *
      (Finset.range j).prod (fun k => rpm (x-(k:ℝ))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp only [Polynomial.eval_mul, eval_a, E, Polynomial.eval_sub, eval_X, eval_C]
  rw [Polynomial.eval_prod]
  simp_rw [eval_pm]
  rw [show ra x = 20*(x+1/2)*(x+1)*rpm x by simp [ra, rp, rpm]; ring]
  rw [show n+1-1=n by omega, ← rpm_mul_prod_shift]
  push_cast
  ring

lemma E_weighted_reflect_eval (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    ra x * (E j).eval x = ra ((j:ℝ)-x) * (E j).eval ((j:ℝ)-x) := by
  rw [← eval_a, ← Polynomial.eval_mul, a_mul_E_eval_formula j hj,
      ← eval_a, ← Polynomial.eval_mul, a_mul_E_eval_formula j hj]
  rw [prod_rpm_reflect]
  ring

lemma E_weighted_reflect (j : ℕ) (hj : 1 ≤ j) :
    a X * E j = reflect j (a X * E j) := by
  apply Polynomial.funext
  intro x
  rw [eval_reflect]
  simp only [Polynomial.eval_mul, eval_a]
  exact E_weighted_reflect_eval j hj x

lemma reflect_mul (j : ℕ) (q r : PR) : reflect j (q*r) = reflect j q * reflect j r := by
  simp [reflect]

lemma F_reflect (j : ℕ) (hj : 1 ≤ j) : F j = reflect j (F j) := by
  have hB := B_weighted_reflect j
  have hE := E_weighted_reflect j hj
  rw [← E_mul_F j, ← mul_assoc, reflect_mul, reflect_mul] at hB
  rw [← reflect_mul, ← hE] at hB
  have ha : (a X : PR) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval 0) h
    norm_num [a, p] at hh
  apply mul_left_cancel₀ (mul_ne_zero ha (E_monic j).ne_zero)
  exact hB

lemma F_symmetry (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    (F j).eval x = (F j).eval ((j:ℝ)-x) := by
  have h := congrArg (Polynomial.eval x) (F_reflect j hj)
  simpa using h

end
end Transfer

namespace Transfer
noncomputable section

def finalP (m : ℕ) : PR := (F m).comp (C (m:ℝ) * X)

def finalH (m : ℕ) : PR := C ((1/5:ℝ)^m) *
  (F (2*m)).comp (C (m:ℝ) * (X+1))

def finalQ (m : ℕ) : PR := (finalH m).contract 2

lemma finalP_eval (m : ℕ) (x : ℝ) :
    (finalP m).eval x = (F m).eval ((m:ℝ)*x) := by
  simp [finalP, Polynomial.eval_comp]

lemma finalP_natDegree (m : ℕ) (hm : 1 ≤ m) : (finalP m).natDegree = 2*m := by
  rw [finalP, natDegree_comp, F_natDegree_eq m hm]
  rw [natDegree_C_mul_X _ (by positivity)]
  simp

lemma finalP_symmetry (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (finalP m).eval x = (finalP m).eval (1-x) := by
  rw [finalP_eval, finalP_eval, F_symmetry m hm]
  congr 1
  push_cast
  ring

lemma finalP_complex_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : ((finalP m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) 1 := by
  have hzF : ((F m).map (algebraMap ℝ ℂ)).eval ((m:ℂ)*z) = 0 := by
    simpa [finalP, Polynomial.map_comp, Polynomial.eval_comp] using hz
  have h := F_complex_roots m hm ((m:ℂ)*z) hzF
  have him : ((m:ℂ)*z).im = (m:ℝ)*z.im := by simp
  have hre : ((m:ℂ)*z).re = (m:ℝ)*z.re := by simp
  rw [him, hre] at h
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  constructor
  · exact (mul_eq_zero.mp h.1).resolve_left hmR.ne'
  · constructor <;> nlinarith [h.2.1, h.2.2]

lemma finalH_natDegree (m : ℕ) (hm : 1 ≤ m) : (finalH m).natDegree = 4*m := by
  have hlin : (C (m:ℝ) * (X+1) : PR).natDegree = 1 := by
    compute_degree
    norm_num
    positivity
  have hcompnat : ((F (2*m)).comp (C (m:ℝ) * (X+1))).natDegree = 4*m := by
    rw [natDegree_comp, F_natDegree_eq (2*m) (by omega), hlin]
    omega
  have hc : (C ((1/5:ℝ)^m) : PR) ≠ 0 := C_ne_zero.mpr (by positivity)
  have hq : (F (2*m)).comp (C (m:ℝ) * (X+1)) ≠ 0 := by
    intro h
    rw [h] at hcompnat
    simp at hcompnat
    omega
  rw [finalH, natDegree_mul hc hq, natDegree_C, hcompnat]
  simp

lemma finalH_even_eval (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (finalH m).eval (-x) = (finalH m).eval x := by
  simp [finalH, Polynomial.eval_comp]
  rw [F_symmetry (2*m) (by omega) ((m:ℝ)*(-x+1))]
  congr 2
  push_cast
  ring

lemma finalH_even_poly (m : ℕ) (hm : 1 ≤ m) :
    (finalH m).comp (C (-1:ℝ)*X) = finalH m := by
  apply Polynomial.funext
  intro x
  simp [Polynomial.eval_comp, finalH_even_eval m hm]

lemma finalH_coeff_odd (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : Odd n) :
    (finalH m).coeff n = 0 := by
  have h := congrArg (fun q : PR => q.coeff n) (finalH_even_poly m hm)
  simp only [comp_C_mul_X_coeff] at h
  rw [hn.neg_one_pow] at h
  linarith

lemma expand_finalQ (m : ℕ) (hm : 1 ≤ m) :
    Polynomial.expand ℝ 2 (finalQ m) = finalH m := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_expand (by omega : 0 < 2)]
  split_ifs with hd
  · rw [finalQ, Polynomial.coeff_contract (by omega : 2 ≠ 0)]
    congr 1
    omega
  · symm
    apply (finalH_coeff_odd m hm n)
    exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hd)

lemma finalQ_natDegree (m : ℕ) (hm : 1 ≤ m) : (finalQ m).natDegree = 2*m := by
  have hH := finalH_natDegree m hm
  have hupper : (finalQ m).natDegree ≤ 2*m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [finalQ, Polynomial.coeff_contract (by omega : 2 ≠ 0)]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  apply Nat.le_antisymm hupper
  apply Polynomial.le_natDegree_of_ne_zero
  rw [finalQ, Polynomial.coeff_contract (by omega : 2 ≠ 0)]
  have hne : finalH m ≠ 0 := by
    intro h
    rw [h] at hH
    simp at hH
    omega
  rw [show (2*m)*2 = 4*m by omega, ← hH, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hne

lemma finalH_complex_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : ((finalH m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1 := by
  have hs : ((1/5:ℂ)^m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzmul : ((1/5:ℂ)^m) *
      ((F (2*m)).map (algebraMap ℝ ℂ)).eval ((m:ℂ)*(z+1)) = 0 := by
    simpa [finalH, Polynomial.map_comp, Polynomial.eval_comp] using hz
  have hzF : ((F (2*m)).map (algebraMap ℝ ℂ)).eval ((m:ℂ)*(z+1)) = 0 :=
    (mul_eq_zero.mp hzmul).resolve_left hs
  have h := F_complex_roots (2*m) (by omega) ((m:ℂ)*(z+1)) hzF
  have him : ((m:ℂ)*(z+1)).im = (m:ℝ)*z.im := by simp
  have hre : ((m:ℂ)*(z+1)).re = (m:ℝ)*(z.re+1) := by simp
  rw [him, hre] at h
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hcast : ((2*m:ℕ):ℝ) = 2*(m:ℝ) := by push_cast; ring
  rw [hcast] at h

  constructor
  · exact (mul_eq_zero.mp h.1).resolve_left hmR.ne'
  · constructor <;> nlinarith [h.2.1, h.2.2]

lemma finalQ_complex_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : ((finalQ m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1 := by
  have he := congrArg (Polynomial.map (algebraMap ℝ ℂ)) (expand_finalQ m hm)
  have hev := congrArg (Polynomial.eval z) he
  simp [Polynomial.expand_eq_comp_X_pow, Polynomial.map_comp,
    Polynomial.eval_comp] at hev
  apply finalH_complex_roots m hm z
  have hh : aeval z (finalH m) = 0 := by
    rw [← hev]
    simpa [aeval_def] using hz
  simpa [Polynomial.eval_map, aeval_def] using hh

end
end Transfer


namespace Transfer
noncomputable section

abbrev RV := ℝ × ℝ

def RM.act (A : RM) (v : RV) : RV :=
  (A.e00*v.1 + A.e01*v.2, A.e10*v.1 + A.e11*v.2)

def vscale (c : ℝ) (v : RV) : RV := (c*v.1, c*v.2)

lemma RM.mul_act (A D : RM) (v : RV) : (A.mul D).act v = A.act (D.act v) := by
  cases A; cases D; cases v
  simp only [RM.mul, RM.act]
  apply Prod.ext <;> simp <;> ring

lemma RM.act_scale (A : RM) (c : ℝ) (v : RV) :
    A.act (vscale c v) = vscale c (A.act v) := by
  cases A; cases v
  simp [RM.act, vscale]
  constructor <;> ring

lemma vscale_mul (a b : ℝ) (v : RV) :
    vscale a (vscale b v) = vscale (a*b) v := by
  cases v
  simp [vscale]
  constructor <;> ring



def BaseRec (u : ℕ → ℝ) : Prop := ∀ n : ℕ, 1 ≤ n →
  ra n * u (n+1) = rc n * u n + ra (-(n:ℝ)) * u (n-1)


def prevValue (u : ℕ → ℝ) : ℝ := u 1 - 6*u 0

def state (u : ℕ → ℝ) (n : ℕ) : RV :=
  (u n, if n = 0 then prevValue u else u (n-1))

lemma one_step (u : ℕ → ℝ) (hu : BaseRec u) (n : ℕ) :
    vscale (ra n) (state u (n+1)) = (rt n).act (state u n) := by
  apply Prod.ext
  · simp only [vscale, state, Prod.fst, RM.act, rt]
    by_cases hn : n = 0
    · subst n
      norm_num [prevValue, ra, rp, rc]
      ring
    · rw [if_neg hn]
      simpa using hu n (Nat.one_le_iff_ne_zero.mpr hn)
  · simp only [vscale, state, Prod.snd, RM.act, rt]
    rw [if_neg (by omega : n+1 ≠ 0)]
    simp


def denom (t j : ℕ) : ℝ := (Finset.range j).prod (fun i => ra (t+i))

lemma denom_zero (t : ℕ) : denom t 0 = 1 := by simp [denom]
lemma denom_succ (t j : ℕ) : denom t (j+1) = denom t j * ra (t+j) := by
  simp [denom, Finset.prod_range_succ]

lemma rb_append (x : ℝ) (j k : ℕ) :
    rb x (j+k) = (rb x j).mul (rb (x-j) k) := by
  induction k with
  | zero => simp [rb, RM.mul_one]
  | succ k ih =>
      rw [show j+(k+1)=j+k+1 by omega, rb, ih, rb, RM.mul_assoc]
      congr 2
      push_cast
      congr 1
      ring

lemma block_state (u : ℕ → ℝ) (hu : BaseRec u) (t j : ℕ) :
    vscale (denom t j) (state u (t+j)) = (rb (t+j) j).act (state u t) := by
  induction j with
  | zero => simp [denom, rb, vscale, RM.act, RM.one]
  | succ j ih =>
      have hs := one_step u hu (t+j)
      push_cast at ih hs ⊢
      have hr : (rt ((t:ℝ)+j)).mul (rb ((t:ℝ)+j) j) =
          rb ((t:ℝ)+(j+1)) (j+1) := by
        simpa [add_assoc] using (rb_succ_shift ((t:ℝ)+j) j).symm
      calc
        vscale (denom t (j+1)) (state u (t+(j+1))) =
            vscale (denom t j) (vscale (ra (t+j)) (state u ((t+j)+1))) := by
              rw [vscale_mul, denom_succ]
              congr 2 <;> omega
        _ = vscale (denom t j) ((rt (t+j)).act (state u (t+j))) := by rw [hs]
        _ = (rt (t+j)).act (vscale (denom t j) (state u (t+j))) := by
              rw [RM.act_scale]
        _ = (rt (t+j)).act ((rb (t+j) j).act (state u t)) := by rw [ih]
        _ = ((rt (t+j)).mul (rb (t+j) j)).act (state u t) := by rw [RM.mul_act]
        _ = (rb (t+(j+1)) (j+1)).act (state u t) := by rw [hr]


def RM.det (A : RM) : ℝ := A.e00*A.e11 - A.e01*A.e10

lemma eliminate_states (L U : RM) (dm dp : ℝ) (vm vr vp : RV)
    (hm : vscale dm vr = L.act vm)
    (hp : vscale dp vp = U.act vr) :
    L.e01*dm*dp*vp.1 + U.e01*L.det*vm.1 =
      dm*((U.mul L).e01)*vr.1 := by
  have hm0 := congrArg Prod.fst hm
  have hm1 := congrArg Prod.snd hm
  have hp0 := congrArg Prod.fst hp
  simp only [vscale, RM.act, RM.mul, RM.det] at hm0 hm1 hp0 ⊢
  linear_combination L.e01*dm*hp0 + U.e01*L.e01*hm1 - U.e01*L.e11*hm0

lemma subsequence_raw (u : ℕ → ℝ) (hu : BaseRec u) (m n : ℕ) (hn : 1 ≤ n) :
  let r := m*n
  let tm := m*(n-1)
  let L := rb r m
  let U := rb (r+m) m
  L.e01 * denom tm m * denom r m * u (r+m) +
    U.e01 * L.det * u tm =
      denom tm m * (rb (r+m) (2*m)).e01 * u r := by
  dsimp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
  have htm : m*((1+q)-1)+m = m*(1+q) := by simp; ring
  have hp : m*(1+q)+m = m*((1+q)+1) := by ring
  have hback := block_state u hu (m*((1+q)-1)) m
  have hfwd := block_state u hu (m*(1+q)) m
  rw [htm] at hback
  push_cast at hback hfwd
  have hback' : vscale (denom (m*((1+q)-1)) m) (state u (m*(1+q))) =
      (rb (m*(1+q)) m).act (state u (m*((1+q)-1))) := by
    convert hback using 1 <;> push_cast <;> simp <;> ring
  have helim := eliminate_states (rb (m*(1+q)) m) (rb (m*(1+q)+m) m)
    (denom (m*((1+q)-1)) m) (denom (m*(1+q)) m)
    (state u (m*((1+q)-1))) (state u (m*(1+q)))
    (state u (m*(1+q)+m)) hback' hfwd
  have happ := rb_append (m*(1+q)+m) m m
  rw [show (m*(1+q)+m:ℝ)-m = m*(1+q) by push_cast; ring] at happ
  rw [← happ] at helim
  simpa [state, two_mul] using helim

end
end Transfer



namespace Transfer
noncomputable section


def outerPlus (m : ℕ) (r : ℝ) : ℝ :=
  (Finset.range (2*m)).prod (fun k => 2*r+(k+1:ℕ))
def outerMinus (m : ℕ) (r : ℝ) : ℝ :=
  (Finset.range (2*m)).prod (fun k => 2*r-(k+1:ℕ))

def rpmProd (N : ℕ) (x : ℝ) : ℝ :=
  (Finset.range N).prod (fun k => rpm (x-k))

lemma rpmProd_add (a b : ℕ) (x : ℝ) :
    rpmProd (a+b) x = rpmProd a x * rpmProd b (x-a) := by
  rw [rpmProd, Finset.prod_range_add]
  simp only [rpmProd]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  push_cast
  congr 1
  ring

private lemma prod_rev (m : ℕ) (f : ℕ → ℝ) :
    (∏ i : Fin m, f (m-1-i)) = ∏ i : Fin m, f i := by
  calc
    (∏ i : Fin m, f (m-1-i)) = ∏ i : Fin m, f (Fin.rev i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Fin.val_rev]
      congr 1
      omega
    _ = ∏ i : Fin m, f i := by
      simpa [Fin.revPerm] using (Equiv.prod_comp Fin.revPerm (fun i : Fin m => f i))

lemma rpmProd_reverse (m : ℕ) (r : ℝ) :
    (Finset.range m).prod (fun i => rpm (r+i)) = rpmProd m (r+m-1) := by
  cases m with
  | zero => simp [rpmProd]
  | succ m =>
      push_cast
      simp_rw [← Fin.prod_univ_eq_prod_range]
      rw [rpmProd]
      simp_rw [← Fin.prod_univ_eq_prod_range]
      calc
        (∏ i : Fin (m+1), rpm (r+(i:ℕ))) =
            ∏ i : Fin (m+1), rpm ((r+((m+1):ℝ)-1) - (((m+1)-1-(i:ℕ)):ℕ)) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [Nat.cast_sub (by omega : (i:ℕ) ≤ (m+1)-1)]
              push_cast
              congr 1
              ring
        _ = ∏ i : Fin (m+1), rpm ((r+((m+1):ℝ)-1) - (i:ℕ)) :=
          prod_rev (m+1) (fun i => rpm ((r+((m+1):ℝ)-1)-i))

lemma eval_E_formula (j : ℕ) (x : ℝ) :
    (E j).eval x = (x-(j:ℝ)-1) * (x-(j:ℝ)-1/2) * rpmProd (j-1) (x-1) := by
  simp only [E, Polynomial.eval_mul, Polynomial.eval_sub, eval_X, eval_C]
  rw [Polynomial.eval_prod]
  simp_rw [eval_pm]
  simp only [rpmProd]
  apply congrArg₂ (· * ·)
  · ring
  · apply Finset.prod_congr rfl
    intro k hk
    push_cast
    congr 1
    ring

lemma E_double (m : ℕ) (r : ℝ) :
    (E (2*m)).eval (r+m) = (E m).eval r *
      (Finset.range m).prod (fun i => rpm (r+i)) := by
  rw [eval_E_formula, eval_E_formula, rpmProd_reverse]
  rw [show 2*m-1 = m+(m-1) by omega, rpmProd_add]
  push_cast
  ring

private lemma prod_pairs (m : ℕ) (f : ℕ → ℝ) :
    (Finset.range m).prod (fun i => f (2*i)*f (2*i+1)) =
      (Finset.range (2*m)).prod f := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      rw [show 2*(m+1)=2*m+2 by omega, Finset.prod_range_succ,
        Finset.prod_range_succ]
      ring

lemma ra_factor (x : ℝ) : ra x = 5*(2*x+1)*(2*x+2)*rpm x := by
  simp [ra, rp, rpm]
  ring

lemma denom_plus_factor (m : ℕ) (r : ℕ) :
    denom r m = 5^m * outerPlus m r *
      (Finset.range m).prod (fun i => rpm ((r:ℝ)+i)) := by
  rw [denom, outerPlus]
  have hfac (i : ℕ) : ra ((r:ℝ)+(i:ℝ)) =
      5 * (((2*((r:ℝ)+i)+1)*(2*((r:ℝ)+i)+2)) * rpm ((r:ℝ)+i)) := by
    rw [ra_factor]
    ring
  calc
    (Finset.range m).prod (fun i => ra ((r:ℝ)+(i:ℝ))) =
        5^m * (Finset.range m).prod
          (fun i => (2*((r:ℝ)+i)+1)*(2*((r:ℝ)+i)+2)) *
          (Finset.range m).prod (fun i => rpm ((r:ℝ)+i)) := by
            simp_rw [hfac]
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
              Finset.prod_mul_distrib]
            ring
    _ = 5^m * (Finset.range (2*m)).prod (fun k => 2*(r:ℝ)+(k+1:ℕ)) *
          (Finset.range m).prod (fun i => rpm ((r:ℝ)+i)) := by
            congr 2
            calc
              (Finset.range m).prod
                  (fun i => (2*((r:ℝ)+i)+1)*(2*((r:ℝ)+i)+2)) =
                  (Finset.range (2*m)).prod (fun k => 2*(r:ℝ)+((k:ℝ)+1)) := by
                    rw [← prod_pairs m (fun k => 2*(r:ℝ)+((k:ℝ)+1))]
                    apply Finset.prod_congr rfl
                    intro i hi
                    push_cast
                    ring
              _ = (Finset.range (2*m)).prod (fun k => 2*(r:ℝ)+(k+1:ℕ)) := by
                    apply Finset.prod_congr rfl
                    intro k hk
                    push_cast
                    rfl

lemma det_mul (A D : RM) : (A.mul D).det = A.det*D.det := by
  simp [RM.det, RM.mul]
  ring

lemma det_rt (x : ℝ) : (rt x).det = -ra (-x)*ra x := by
  simp [RM.det, rt]

lemma det_rb (x : ℝ) (m : ℕ) :
    (rb x m).det = (-1:ℝ)^m *
      (Finset.range m).prod (fun i => ra (-(x-(i+1)))) *
      (Finset.range m).prod (fun i => ra (x-(i+1))) := by
  induction m with
  | zero => simp [rb, RM.det, RM.one]
  | succ m ih =>
      rw [rb, det_mul, ih, det_rt, Finset.prod_range_succ, Finset.prod_range_succ]
      push_cast
      ring

lemma denom_minus_as_prod (m r : ℕ) (hmr : m ≤ r) :
    denom (r-m) m = (Finset.range m).prod (fun i => ra ((r:ℝ)-(i+1))) := by
  cases m with
  | zero => simp [denom]
  | succ m =>
      rw [denom]
      simp_rw [← Fin.prod_univ_eq_prod_range]
      push_cast
      calc
        (∏ i : Fin (m+1), ra (((r-(m+1):ℕ):ℝ)+(i:ℕ))) =
            ∏ i : Fin (m+1), ra ((r:ℝ)-(((m+1)-1-(i:ℕ)):ℕ)-1) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [Nat.cast_sub hmr, Nat.cast_sub (by omega : (i:ℕ) ≤ (m+1)-1)]
              push_cast
              congr 1
              ring
        _ = ∏ i : Fin (m+1), ra ((r:ℝ)-(i:ℕ)-1) :=
          prod_rev (m+1) (fun i => ra ((r:ℝ)-i-1))
        _ = ∏ i : Fin (m+1), ra ((r:ℝ)-((i:ℝ)+1)) := by
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
          ring

lemma B_eval_factor (j : ℕ) (x : ℝ) :
    (rb x j).e01 = (E j).eval x * (F j).eval x := by
  rw [← eval_block_eq_rb]
  change (B j).eval x = _
  rw [← eval_E_mul_F]

end
end Transfer


namespace Transfer
noncomputable section

private lemma linear_shift_identity (m : ℕ) (r : ℝ) :
    (r-1)*(r-1/2) *
      (Finset.range (2*m)).prod (fun k => 2*r-(k+3:ℕ)) =
    (r-(m:ℝ)-1)*(r-(m:ℝ)-1/2) * outerMinus m r := by
  induction m with
  | zero => simp [outerMinus]
  | succ m ih =>
      rw [outerMinus] at ih ⊢
      rw [show 2*(m+1)=2*m+2 by omega,
        Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ]
      push_cast at ih ⊢
      linear_combination
        ((2*r-(2*(m:ℝ)+3))*(2*r-(2*(m:ℝ)+4))) * ih

lemma neg_ra_prod_factor (m : ℕ) (r : ℝ) :
    (Finset.range m).prod (fun i => ra (-(r-(i+1)))) =
      5^m * (Finset.range (2*m)).prod (fun k => 2*r-(k+3:ℕ)) *
        rpmProd m r := by
  push_cast
  have hfac (i : ℕ) : ra (-(r-(i+1:ℕ))) =
      5 * (((2*r-(2*i+3:ℕ))*(2*r-(2*i+4:ℕ))) * rpm (r-i)) := by
    rw [ra_factor]
    rw [show rpm (-(r-(i+1:ℕ))) = rpm (r-i) by
      rw [← rpm_reflect]
      push_cast
      congr 1
      ring]
    push_cast
    ring
  rw [show (Finset.range m).prod (fun i => ra (-(r-((i:ℝ)+1)))) =
      (Finset.range m).prod (fun i =>
        5 * (((2*r-(2*i+3:ℕ))*(2*r-(2*i+4:ℕ))) * rpm (r-i))) by
        apply Finset.prod_congr rfl
        intro i hi
        simpa using hfac i]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_mul_distrib]
  rw [show (Finset.range m).prod (fun i =>
      (2*r-(2*i+3:ℕ))*(2*r-(2*i+4:ℕ))) =
      (Finset.range (2*m)).prod (fun k => 2*r-(k+3:ℕ)) by
        rw [← prod_pairs m (fun k => 2*r-(k+3:ℕ))]]
  rw [rpmProd]
  simp_rw [Nat.cast_add, Nat.cast_ofNat]
  ring

lemma E_neg_ra_identity (m : ℕ) (r : ℝ) :
    (E m).eval (r+m) *
      (Finset.range m).prod (fun i => ra (-(r-(i+1)))) =
    5^m * (E (2*m)).eval (r+m) * outerMinus m r := by
  by_cases hm : m = 0
  · subst m
    simp [outerMinus]
  rw [eval_E_formula, eval_E_formula, neg_ra_prod_factor]
  rw [show 2*m-1=(m-1)+m by omega, rpmProd_add]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hs : r+(m:ℝ)-1-(m-1:ℕ) = r := by
    rw [Nat.cast_sub hm1]
    push_cast
    ring
  rw [hs]
  have hl := linear_shift_identity m r
  push_cast at hl ⊢
  linear_combination 5^m * rpmProd (m-1) (r+(m:ℝ)-1) * rpmProd m r * hl

end
end Transfer



namespace Transfer
noncomputable section

lemma finalQ_eval_sq (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (finalQ m).eval (x^2) = (1/5:ℝ)^m *
      (F (2*m)).eval ((m:ℝ)*(x+1)) := by
  have he := congrArg (Polynomial.eval x) (expand_finalQ m hm)
  simp [Polynomial.expand_eq_comp_X_pow, finalH, Polynomial.eval_comp] at he
  simpa [pow_two] using he

lemma E_double_ne_zero (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hex : ¬ (m = 1 ∧ n = 2)) : (E (2*m)).eval ((m*n+m:ℕ):ℝ) ≠ 0 := by
  rw [eval_E_formula]
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro h
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
      have hcast : (m:ℝ) * (n-1:ℕ) = 1 := by
        rw [Nat.cast_sub hn]
        push_cast
        nlinarith
      have hnat : m*(n-1)=1 := by exact_mod_cast hcast
      have hmone : m = 1 := Nat.eq_one_of_dvd_one ⟨n-1, hnat.symm⟩
      have hnsub : n-1 = 1 := by
        rw [hmone] at hnat
        simpa using hnat
      exact hex ⟨hmone, by omega⟩
    · intro h
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
      have hrel : (m:ℝ)*(n-1:ℕ) = 1/2 := by
        rw [Nat.cast_sub hn]
        push_cast
        nlinarith
      rcases Nat.eq_zero_or_pos (m*(n-1)) with hz | hz
      · have : (m:ℝ)*(n-1:ℕ) = 0 := by exact_mod_cast hz
        linarith
      · have : (1:ℝ) ≤ (m:ℝ)*(n-1:ℕ) := by exact_mod_cast hz
        linarith
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply (rpm_pos_of_one_le ?_).ne'
    have hk' := Finset.mem_range.mp hk
    have hmn : m ≤ m*n := Nat.le_mul_of_pos_right m hn
    have harg : k+2 ≤ m*n+m := by omega
    have hargR : (k:ℝ)+2 ≤ (m*n+m:ℕ) := by exact_mod_cast harg
    push_cast at hargR ⊢
    linarith

lemma denom_ne_zero_nat (t m : ℕ) : denom t m ≠ 0 := by
  rw [denom]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simpa only [Nat.cast_add] using (ra_nat_pos (t+i)).ne'

lemma normalized_recurrence (u : ℕ → ℝ) (hu : BaseRec u)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hex : ¬ (m=1 ∧ n=2)) :
    outerPlus m (m*n) * (finalP m).eval (n:ℝ) * u (m*(n+1)) +
      (-1:ℝ)^m * outerMinus m (m*n) * (finalP m).eval (-(n:ℝ)) *
        u (m*(n-1)) =
      (finalQ m).eval ((n:ℝ)^2) * u (m*n) := by
  let r : ℕ := m*n
  let tm : ℕ := m*(n-1)
  let dm := denom tm m
  let K : ℝ := 5^m * dm * (E (2*m)).eval ((r+m:ℕ):ℝ)
  have htm : tm = r-m := by
    dsimp [tm, r]
    rw [Nat.mul_sub_left_distrib]
    simp [hn]
  have hmr : m ≤ r := by
    dsimp [r]
    exact Nat.le_mul_of_pos_right m hn
  have hraw := subsequence_raw u hu m n hn
  dsimp only at hraw
  have hplus : (rb r m).e01 * dm * denom r m =
      K * (outerPlus m r * (finalP m).eval (n:ℝ)) := by
    rw [B_eval_factor, denom_plus_factor, finalP_eval]
    have hE := E_double m (r:ℝ)
    dsimp [K, dm]
    push_cast at hE ⊢
    have harg : (m:ℝ)*(n:ℝ) = (r:ℝ) := by dsimp [r]; push_cast; rfl
    rw [harg]
    linear_combination -((5:ℝ)^m * denom tm m * outerPlus m (r:ℝ) *
      (F m).eval (r:ℝ)) * hE
  have hminus : (rb (r+m) m).e01 * (rb r m).det =
      K * ((-1:ℝ)^m * outerMinus m r * (finalP m).eval (-(n:ℝ))) := by
    rw [B_eval_factor, det_rb]
    rw [← denom_minus_as_prod m r hmr, ← htm]
    rw [finalP_eval]
    have hsym : (F m).eval ((r:ℝ)+m) = (F m).eval (-(r:ℝ)) := by
      rw [F_symmetry m hm]
      congr 1
      push_cast
      ring
    rw [hsym]
    have harg : (m:ℝ) * (-(n:ℝ)) = -(r:ℝ) := by
      dsimp [r]
      push_cast
      ring
    rw [harg]
    have hE := E_neg_ra_identity m (r:ℝ)
    dsimp [K, dm]
    push_cast at hE ⊢
    linear_combination ((-1:ℝ)^m * denom tm m * (F m).eval (-(r:ℝ))) * hE
  have hright : dm * (rb (r+m) (2*m)).e01 =
      K * (finalQ m).eval ((n:ℝ)^2) := by
    rw [B_eval_factor, finalQ_eval_sq m hm]
    dsimp [K]
    have hpow : (5:ℝ)^m * (1/5:ℝ)^m = 1 := by
      rw [← mul_pow]
      norm_num
    have harg : (m:ℝ)*((n:ℝ)+1) = (r:ℝ)+(m:ℝ) := by
      dsimp [r]
      push_cast
      ring
    rw [harg]
    push_cast
    linear_combination -(dm * (E (2*m)).eval ((r:ℝ)+(m:ℝ)) *
      (F (2*m)).eval ((r:ℝ)+(m:ℝ))) * hpow
  rw [hplus, hminus, hright] at hraw
  have hK : K ≠ 0 := by
    dsimp [K, dm]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (denom_ne_zero_nat tm m))
      (E_double_ne_zero m n hm hn hex)
  have hrR : (r:ℝ) = (m:ℝ)*(n:ℝ) := by
    dsimp [r]
    push_cast
    rfl
  rw [hrR] at hraw
  apply (mul_left_cancel₀ hK)
  push_cast at hraw ⊢
  simp only [Nat.mul_add, Nat.mul_one] at hraw ⊢
  linear_combination hraw

end
end Transfer


namespace Transfer
noncomputable section

lemma F_one_explicit : F 1 = 4 * p X := by
  apply mul_left_cancel₀ (E_monic 1).ne_zero
  rw [E_mul_F]
  apply Polynomial.funext
  intro x
  simp [E, B, block, M.one, M.mul, t, a, c, p, pm]
  ring

lemma F_two_explicit : F 2 =
    80 * (55*X^4 - 220*X^3 + 296*X^2 - 152*X + 24) := by
  apply mul_left_cancel₀ (E_monic 2).ne_zero
  rw [E_mul_F]
  apply Polynomial.funext
  intro x
  simp [E, B, block, M.one, M.mul, t, a, c, p, pm]
  ring


lemma normalized_recurrence_exception (u : ℕ → ℝ) (hu : BaseRec u) :
    outerPlus 1 2 * (finalP 1).eval 2 * u 3 +
      (-1:ℝ)^1 * outerMinus 1 2 * (finalP 1).eval (-2) * u 1 =
      (finalQ 1).eval ((2:ℝ)^2) * u 2 := by
  have h := hu 2 (by omega)
  rw [finalP_eval, finalP_eval, finalQ_eval_sq 1 (by omega),
    F_one_explicit, F_two_explicit]
  norm_num [outerPlus, outerMinus, p, ra, rc, rp] at h ⊢
  linarith [h]

lemma normalized_recurrence_all (u : ℕ → ℝ) (hu : BaseRec u)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    outerPlus m (m*n) * (finalP m).eval (n:ℝ) * u (m*(n+1)) +
      (-1:ℝ)^m * outerMinus m (m*n) * (finalP m).eval (-(n:ℝ)) *
        u (m*(n-1)) =
      (finalQ m).eval ((n:ℝ)^2) * u (m*n) := by
  by_cases hex : m=1 ∧ n=2
  · rcases hex with ⟨rfl,rfl⟩
    convert normalized_recurrence_exception u hu using 1 <;> norm_num
  · exact normalized_recurrence u hu m n hm hn hex

end
end Transfer




namespace BaseProof

noncomputable def summand (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((2*n+k-1).choose (n-1) : ℝ)

noncomputable def seq (n : ℕ) : ℝ :=
  if n=0 then 1 else (Finset.range (n+1)).sum (summand n)

lemma summand_zero_of_lt {n k : ℕ} (h : n < k) : summand n k = 0 := by
  simp [summand, Nat.choose_eq_zero_of_lt h]

lemma summand_factorial {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    summand n k = (n:ℝ) * (2*n+k-1).factorial /
      (k.factorial * (n-k).factorial * (n+k).factorial) := by
  rw [summand, Nat.cast_choose ℝ hk]
  have hk2 : n-1 ≤ 2*n+k-1 := by omega
  rw [Nat.cast_choose ℝ hk2]
  have hsub : 2*n+k-1-(n-1)=n+k := by omega
  rw [hsub]
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hfac : ((q.factorial:ℕ):ℝ) ≠ 0 := by positivity
  have hnfac : (((1+q).factorial:ℕ):ℝ) = (1+(q:ℝ)) * q.factorial := by
    rw [show 1+q=q+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hnfac]
  field_simp

lemma summand_pos {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) : 0 < summand n k := by
  rw [summand_factorial hn hk]
  positivity

noncomputable def certA (n : ℕ) : ℝ :=
  110*n^5 + 30*n^4 - 68*n^3 - 20*n^2 + 6*n + 2
noncomputable def certB (n : ℕ) : ℝ :=
  410*n^6 - 260*n^5 - 258*n^4 + 150*n^3 + 30*n^2 - 10*n - 2
noncomputable def certC (n : ℕ) : ℝ :=
  290*n^6 - 265*n^5 - 187*n^4 + 138*n^3 + 33*n^2 - 5*n - 4
noncomputable def certR (n k : ℕ) : ℝ :=
  certA n*k^2 + certB n*k + n*certC n

noncomputable def certG (n k : ℕ) : ℝ :=
  if k=0 ∨ n+1 < k then 0 else
    - certR n k * (2*n+k-3).factorial /
      ((k-1).factorial * (n+1-k).factorial * (n+k).factorial)

lemma certG_zero (n : ℕ) : certG n 0 = 0 := by simp [certG]
lemma certG_far (n : ℕ) : certG n (n+2) = 0 := by simp [certG]

end BaseProof

namespace BaseProof

lemma ratio_n_succ {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    summand (n+1) k * ((n:ℝ)*(n+1-k)*(n+1+k)) =
      summand n k * ((n+1:ℝ)*(2*n+k)*(2*n+k+1)) := by
  rw [summand_factorial (by omega) (by omega), summand_factorial hn hk]
  field_simp
  repeat' first
    | rw [show (2*(n+1)+k-1) = (2*n+k-1)+2 by omega,
          show (2*n+k-1)+2 = ((2*n+k-1)+1)+1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
    | rw [show n+1-k=(n-k)+1 by omega, Nat.factorial_succ]
    | rw [show n+1+k=(n+k)+1 by omega, Nat.factorial_succ]
  push_cast
  rw [Nat.cast_sub hk, Nat.cast_sub (by omega : 1 ≤ 2*n+k)]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end BaseProof



namespace BaseProof

lemma ratio_n_pred {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n-1) :
    summand (n-1) k * ((n:ℝ)*(2*n+k-1)*(2*n+k-2)) =
      summand n k * ((n-1:ℝ)*(n^2-k^2)) := by
  rw [summand_factorial (by omega) hk, summand_factorial (by omega) (by omega)]
  field_simp
  repeat' first
    | rw [show 2*n+k-1=(2*(n-1)+k-1)+2 by omega,
          show (2*(n-1)+k-1)+2=((2*(n-1)+k-1)+1)+1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
    | rw [show n-k=(n-1-k)+1 by omega, Nat.factorial_succ]
    | rw [show n+k=(n-1+k)+1 by omega, Nat.factorial_succ]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : k ≤ n-1),
    Nat.cast_sub (by omega : 1 ≤ 2*(n-1)+k)]
  simp only [Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : k ≤ n-1),
    Nat.cast_sub (by omega : 1 ≤ 2*(n-1)+k),
    Nat.cast_sub (by omega : 1 ≤ 2*n+k),
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma ratio_k_succ {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) :
    summand n (k+1) * (((k+1:ℕ):ℝ)*(n+k+1)) =
      summand n k * ((2*n+k:ℕ)*(n-k)) := by
  rw [summand_factorial hn (by omega), summand_factorial hn (by omega)]
  field_simp
  repeat' first
    | rw [show 2*n+(k+1)-1=(2*n+k-1)+1 by omega, Nat.factorial_succ]
    | rw [show (k+1).factorial=(k+1)*k.factorial by rw [Nat.factorial_succ]]
    | rw [show n-k=(n-(k+1))+1 by omega, Nat.factorial_succ]
    | rw [show n+(k+1)=(n+k)+1 by omega, Nat.factorial_succ]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Nat.cast_sub (by omega : k+1 ≤ n)]
  simp only [Nat.cast_sub (by omega : k+1 ≤ n),
    Nat.cast_sub (by omega : k ≤ n),
    Nat.cast_sub (by omega : 1 ≤ 2*n+k),
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end BaseProof


namespace BaseProof

noncomputable def certRat (n k : ℕ) : ℝ :=
  ((k:ℝ) / n * certR n k) /
    ((k:ℝ)-n-1) / ((k:ℝ)+2*n-2) / ((k:ℝ)+2*n-1)

lemma certG_eq_rat_mul {n k : ℕ} (hn : 2 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n) :
    certG n k = certRat n k * summand n k := by
  rw [certG, if_neg (by omega : ¬(k=0 ∨ n+1<k)), certRat,
    summand_factorial (by omega) hk]
  have htop : 2*n+k-1=(2*n+k-3)+2 := by omega
  rw [htop, show 2*n+k-3+2=(2*n+k-3+1)+1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  rw [show k.factorial=k*(k-1).factorial by
    conv_lhs => rw [show k=(k-1)+1 by omega, Nat.factorial_succ]
    congr 1
    omega]
  rw [show n+1-k=(n-k)+1 by omega, Nat.factorial_succ]
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hkR : (k:ℝ) ≠ 0 := by positivity
  have hf1 : (((k-1).factorial:ℕ):ℝ) ≠ 0 := by positivity
  have hf2 : (((n-k).factorial:ℕ):ℝ) ≠ 0 := by positivity
  have hf3 : (((n+k).factorial:ℕ):ℝ) ≠ 0 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Nat.cast_sub hk]
  have hd1 : (k:ℝ)-(n:ℝ)-1 ≠ 0 := by
    have : (k:ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have hkpos : (1:ℝ) ≤ k := by exact_mod_cast hk0
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd2pos : 0 < (k:ℝ)+2*(n:ℝ)-2 := by linarith
  have hd3pos : 0 < (k:ℝ)+2*(n:ℝ)-1 := by linarith
  have hd2 : (k:ℝ)+2*(n:ℝ)-2 ≠ 0 := hd2pos.ne'
  have hd3 : (k:ℝ)+2*(n:ℝ)-1 ≠ 0 := hd3pos.ne'
  have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk
  have hnk : (1+(n:ℝ)-(k:ℝ)) ≠ 0 := by linarith
  have hnk' : (1-(k:ℝ)+(n:ℝ)) ≠ 0 := by linarith
  have hpoly : (2-(k:ℝ)*3+(k:ℝ)*(n:ℝ)*4+(k:ℝ)^2-(n:ℝ)*6+(n:ℝ)^2*4) ≠ 0 := by
    have hp := mul_pos hd2pos hd3pos
    intro h
    apply hp.ne'
    rw [show ((k:ℝ)+2*n-2)*((k:ℝ)+2*n-1) =
      2-k*3+k*n*4+k^2-n*6+n^2*4 by ring]
    exact h
  field_simp [hd1, hd2, hd3, hnk, hnk', hpoly]
  rw [Nat.cast_sub (by omega : 3 ≤ 2*n+k)]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring_nf at hnk' hpoly
  ring_nf
  field_simp [hnk', hpoly]
  ring

end BaseProof


namespace BaseProof

lemma clear_rational_certificate
    (a b c e f g r l s : ℝ)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : ℝ)
    (h0 : d0 ≠ 0) (h1 : d1 ≠ 0) (h2 : d2 ≠ 0) (h3 : d3 ≠ 0)
    (h4 : d4 ≠ 0) (h5 : d5 ≠ 0) (h6 : d6 ≠ 0) (h7 : d7 ≠ 0)
    (h8 : d8 ≠ 0) (h9 : d9 ≠ 0) (h10 : d10 ≠ 0) (h11 : d11 ≠ 0)
    (h12 : d12 ≠ 0)
    (hp :
      (a*b*d3*d4 - d1*d2*c*e - d0*d1*d2*d3*d4*f) *
          d6*d7*d8*d9*d10*d11*d12 =
        d1*d2*d3*d4 *
          (g*r*d10*d11*d12 - d6*d7*d8*d9*l*s)) :
    a * (b / d0 / d1 / d2) - c * (e / d0 / d3 / d4) - f =
      (g / d5 / d6) * ((d5 / d0 * r) / d7 / d8 / d9) -
        (l / d0 * s) / d10 / d11 / d12 := by
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12]
  exact hp

set_option maxRecDepth 10000 in
lemma certificate_identity {n k : ℕ} (hn : 2 ≤ n) (hk0 : 1 ≤ k) (hk : k < n) :
    Transfer.ra n *
        (((n+1:ℕ):ℝ)*(2*n+k)*(2*n+k+1) /
          (n:ℝ) / (n+1-k) / (n+1+k)) -
      Transfer.ra (-(n:ℝ)) *
        (((n-1:ℕ):ℝ)*(n^2-k^2) /
          (n:ℝ) / (2*n+k-1) / (2*n+k-2)) - Transfer.rc n =
      ((2*n+k:ℕ):ℝ)*(n-k) / ((k+1:ℕ):ℝ) / (n+k+1) * certRat n (k+1) -
        certRat n k := by
  unfold certRat
  simp only [Transfer.ra, Transfer.rp, Transfer.rc]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  simp only [Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : k ≤ n),
    Nat.cast_sub (by omega : k+1 ≤ n),
    Nat.cast_sub (Nat.pow_le_pow_left (Nat.le_of_lt hk) 2),
    Nat.cast_sub (by omega : 1 ≤ 2*n+k),
    Nat.cast_sub (by omega : 2 ≤ 2*n+k)]
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hnpk : (n+1-(k:ℝ)) ≠ 0 := by
    have : (k:ℝ) < n := by exact_mod_cast hk
    linarith
  have hnmk : (n-(k:ℝ)) ≠ 0 := by
    have : (k:ℝ) < n := by exact_mod_cast hk
    linarith
  have hkp : ((k:ℝ)+1) ≠ 0 := by positivity
  have hnpkplus : ((n:ℝ)+1+(k:ℝ)) ≠ 0 := by positivity
  have hnk : ((n:ℝ)+(k:ℝ)+1) ≠ 0 := by positivity
  have h2a : (2*(n:ℝ)+(k:ℝ)-1) ≠ 0 := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk0
    linarith
  have h2b : (2*(n:ℝ)+(k:ℝ)-2) ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    have : (1:ℝ) ≤ k := by exact_mod_cast hk0
    linarith
  have hd (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ n) :
      ((j:ℝ)-n-1) ≠ 0 ∧ ((j:ℝ)+2*n-2) ≠ 0 ∧ ((j:ℝ)+2*n-1) ≠ 0 := by
    have hjR : (j:ℝ) ≤ n := by exact_mod_cast hj
    have hjp : (1:ℝ) ≤ j := by exact_mod_cast hj0
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · linarith
    constructor <;> linarith
  have hd0 := hd k hk0 (by omega)
  have hd1 := hd (k+1) (by omega) (by omega)
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hd1 ⊢
  apply clear_rational_certificate
    (h0:=hn0) (h1:=hnpk) (h2:=hnpkplus) (h3:=h2a) (h4:=h2b)
    (h5:=hkp) (h6:=hnk) (h7:=hd1.1) (h8:=hd1.2.1) (h9:=hd1.2.2)
    (h10:=hd0.1) (h11:=hd0.2.1) (h12:=hd0.2.2)
  unfold certR certA certB certC
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  ring

end BaseProof




namespace BaseProof

lemma scale_certificate {a b c d e q r t s : ℝ}
    (h : a*b - c*d - e = q*r - t) :
    a*(b*s) - c*(d*s) - e*s = r*(q*s) - t*s := by
  calc
    a*(b*s) - c*(d*s) - e*s = (a*b-c*d-e)*s := by ring
    _ = (q*r-t)*s := congrArg (fun x : ℝ => x*s) h
    _ = r*(q*s)-t*s := by ring

lemma local_identity_interior {n k : ℕ} (hn : 2 ≤ n) (hk0 : 1 ≤ k) (hk : k < n) :
    Transfer.ra n * summand (n+1) k -
      Transfer.ra (-(n:ℝ)) * summand (n-1) k -
        Transfer.rc n * summand n k = certG n (k+1) - certG n k := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hnp : (n+1-(k:ℝ)) ≠ 0 := by
    have : (k:ℝ) < n := by exact_mod_cast hk
    linarith
  have hns : (n+1+(k:ℝ)) ≠ 0 := by positivity
  have hp : summand (n+1) k =
      (((n+1:ℕ):ℝ)*(2*n+k)*(2*n+k+1) /
        (n:ℝ) / (n+1-k) / (n+1+k)) * summand n k := by
    have h := ratio_n_succ (n:=n) (k:=k) (by omega) (by omega)
    field_simp [hn0, hnp, hns]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
    linear_combination h
  have hm : summand (n-1) k =
      (((n-1:ℕ):ℝ)*(n^2-k^2) /
        (n:ℝ) / (2*n+k-1) / (2*n+k-2)) * summand n k := by
    have h := ratio_n_pred (n:=n) (k:=k) hn (by omega)
    have h1 : (2*(n:ℝ)+(k:ℝ)-1) ≠ 0 := by
      have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
      have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    have h2 : (2*(n:ℝ)+(k:ℝ)-2) ≠ 0 := by
      have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
      have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    field_simp [hn0, h1, h2]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
    have hprod : (2-(n:ℝ)*6+(n:ℝ)*(k:ℝ)*4+(n:ℝ)^2*4-(k:ℝ)*3+(k:ℝ)^2) ≠ 0 := by
      have hp := mul_ne_zero h1 h2
      intro hz
      apply hp
      rw [show (2*(n:ℝ)+(k:ℝ)-1)*(2*(n:ℝ)+(k:ℝ)-2) =
        2-n*6+n*k*4+n^2*4-k*3+k^2 by ring]
      exact hz
    ring_nf at hprod
    ring_nf
    field_simp [hn0, hprod]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    linear_combination h
  have hq : summand n (k+1) =
      (((2*n+k:ℕ):ℝ)*(n-k) / ((k+1:ℕ):ℝ) / (n+k+1)) * summand n k := by
    have h := ratio_k_succ (n:=n) (k:=k) (by omega) hk
    have hk1 : (k:ℝ)+1 ≠ 0 := by positivity
    have hsum : (n:ℝ)+(k:ℝ)+1 ≠ 0 := by positivity
    field_simp [hk1, hsum]
    linear_combination h
  rw [certG_eq_rat_mul hn hk0 (by omega),
    certG_eq_rat_mul hn (by omega) (by omega), hp, hm, hq]
  have hc := certificate_identity hn hk0 hk
  exact scale_certificate hc

end BaseProof


namespace BaseProof

lemma local_identity_zero {n : ℕ} (hn : 2 ≤ n) :
    Transfer.ra n * summand (n+1) 0 -
      Transfer.ra (-(n:ℝ)) * summand (n-1) 0 -
        Transfer.rc n * summand n 0 = certG n 1 - certG n 0 := by
  rw [summand_factorial (by omega) (by omega),
    summand_factorial (by omega) (by omega),
    summand_factorial (by omega) (by omega), certG_zero]
  rw [certG, if_neg (by omega : ¬(1=0 ∨ n+1 < 1))]
  unfold certR certA certB certC
  simp only [Transfer.ra, Transfer.rp, Transfer.rc]
  norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, zero_add, add_zero,
    mul_zero, zero_mul, pow_zero, one_mul]
  simp only [Nat.sub_zero, Nat.add_zero]
  rw [show 2*(n+1)-1 = (2*n-3)+4 by omega]
  repeat' rw [Nat.factorial_succ]
  rw [show 2*(n-1)-1 = 2*n-3 by omega]
  rw [show 2*n-1 = (2*n-3)+2 by omega]
  repeat' rw [Nat.factorial_succ]
  rw [show 2*n+1-3 = 2*n-2 by omega,
    show 2*n-2 = (2*n-3)+1 by omega, Nat.factorial_succ]
  simp only [Nat.add_sub_cancel]
  rw [show n.factorial = n*(n-1).factorial by
    conv_lhs => rw [show n=(n-1)+1 by omega, Nat.factorial_succ]
    congr 1 <;> omega]
  field_simp
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  simp only [Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ 2*n), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end BaseProof

namespace BaseProof

lemma local_identity_at_n {n : ℕ} (hn : 2 ≤ n) :
    Transfer.ra n * summand (n+1) n -
      Transfer.ra (-(n:ℝ)) * summand (n-1) n -
        Transfer.rc n * summand n n = certG n (n+1) - certG n n := by
  rw [summand_factorial (by omega) (by omega),
    summand_zero_of_lt (by omega : n-1 < n),
    summand_factorial (by omega) (by omega)]
  rw [certG, if_neg (by omega : ¬(n+1=0 ∨ n+1 < n+1)),
    certG, if_neg (by omega : ¬(n=0 ∨ n+1 < n))]
  unfold certR certA certB certC
  simp only [Transfer.ra, Transfer.rp, Transfer.rc]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    sub_zero, mul_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    one_mul, mul_one]
  simp only [Nat.add_sub_cancel, Nat.sub_self]
  rw [show 2*(n+1)+n-1 = (3*n-3)+4 by omega]
  repeat' rw [Nat.factorial_succ]
  rw [show 2*n+n-1 = (3*n-3)+2 by omega]
  repeat' rw [Nat.factorial_succ]
  rw [show 2*n+(n+1)-3 = (3*n-3)+1 by omega, Nat.factorial_succ]
  rw [show 2*n+n-3 = 3*n-3 by omega]
  rw [show n.factorial = n*(n-1).factorial by
    conv_lhs => rw [show n=(n-1)+1 by omega, Nat.factorial_succ]
    congr 1 <;> omega]
  simp_rw [show n+1-n=1 by omega, show n+1+n=2*n+1 by omega,
    show n+(n+1)=2*n+1 by omega, show n+n=2*n by omega, Nat.factorial_one]
  simp_rw [show (2*n+1).factorial = (2*n+1)*(2*n).factorial by rw [Nat.factorial_succ]]
  field_simp
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  simp only [Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ 3*n), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma local_identity_after_n {n : ℕ} (hn : 2 ≤ n) :
    Transfer.ra n * summand (n+1) (n+1) -
      Transfer.ra (-(n:ℝ)) * summand (n-1) (n+1) -
        Transfer.rc n * summand n (n+1) = certG n (n+2) - certG n (n+1) := by
  rw [summand_factorial (by omega) (by omega),
    summand_zero_of_lt (by omega : n-1 < n+1),
    summand_zero_of_lt (by omega : n < n+1), certG_far]
  rw [certG, if_neg (by omega : ¬(n+1=0 ∨ n+1 < n+1))]
  unfold certR certA certB certC
  simp only [Transfer.ra, Transfer.rp, Transfer.rc]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    sub_zero, mul_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    one_mul, mul_one, zero_mul]
  simp only [Nat.add_sub_cancel, Nat.sub_self]
  rw [show 2*(n+1)+(n+1)-1 = (3*n-2)+4 by omega]
  repeat' rw [Nat.factorial_succ]
  rw [show 2*n+(n+1)-3 = 3*n-2 by omega]
  simp_rw [show n+1+(n+1)=2*n+2 by omega, show n+(n+1)=2*n+1 by omega]
  rw [show (2*n+2).factorial = (2*n+2)*(2*n+1).factorial by
    rw [show 2*n+2=(2*n+1)+1 by omega, Nat.factorial_succ]]
  field_simp
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  simp only [Nat.cast_sub (by omega : 2 ≤ 3*n), Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

end BaseProof

namespace BaseProof

lemma local_identity {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n+1) :
    Transfer.ra n * summand (n+1) k -
      Transfer.ra (-(n:ℝ)) * summand (n-1) k -
        Transfer.rc n * summand n k = certG n (k+1) - certG n k := by
  by_cases h0 : k=0
  · subst k
    exact local_identity_zero hn
  by_cases hlt : k<n
  · exact local_identity_interior hn (by omega) hlt
  have hkn : n ≤ k := by omega
  have hor : k=n ∨ k=n+1 := by omega
  rcases hor with rfl | rfl
  · exact local_identity_at_n hn
  · exact local_identity_after_n hn

lemma sum_summand_succ {n : ℕ} :
    (∑ k ∈ Finset.range (n+2), summand (n+1) k) = seq (n+1) := by
  simp only [seq, if_neg (by omega : n+1 ≠ 0)]

lemma sum_summand_self {n : ℕ} (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+2), summand n k) = seq n := by
  rw [show n+2=(n+1)+1 by omega, Finset.sum_range_succ,
    summand_zero_of_lt (by omega : n<n+1), add_zero]
  simp [seq, Nat.ne_of_gt hn]

lemma sum_summand_pred {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n+2), summand (n-1) k) = seq (n-1) := by
  rw [show n+2=(n+1)+1 by omega, Finset.sum_range_succ,
    summand_zero_of_lt (by omega : n-1<n+1), add_zero,
    show n+1=n+1 by rfl, Finset.sum_range_succ,
    summand_zero_of_lt (by omega : n-1<n), add_zero]
  simp only [seq, if_neg (show n-1≠0 by omega)]
  rw [show n-1+1=n by omega]

lemma seq_recurrence_ge_two {n : ℕ} (hn : 2 ≤ n) :
    Transfer.ra n * seq (n+1) =
      Transfer.rc n * seq n + Transfer.ra (-(n:ℝ)) * seq (n-1) := by
  have hsum :
      (∑ k ∈ Finset.range (n+2),
        (Transfer.ra n * summand (n+1) k -
          Transfer.ra (-(n:ℝ)) * summand (n-1) k -
            Transfer.rc n * summand n k)) =
      ∑ k ∈ Finset.range (n+2), (certG n (k+1) - certG n k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact local_identity hn (by have h := Finset.mem_range.1 hk; omega)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_summand_succ, sum_summand_pred hn,
    sum_summand_self (by omega : 1 ≤ n)] at hsum
  rw [Finset.sum_range_sub (certG n) (n+2), certG_far, certG_zero, sub_zero] at hsum
  linarith

end BaseProof



namespace BaseProof

lemma seq_recurrence_one :
    Transfer.ra (1:ℝ) * seq 2 =
      Transfer.rc (1:ℝ) * seq 1 + Transfer.ra (-1:ℝ) * seq 0 := by
  norm_num [seq, summand, Transfer.ra, Transfer.rp, Transfer.rc,
    Finset.sum_range_succ]

lemma seq_baseRec : Transfer.BaseRec seq := by
  intro n hn
  by_cases h : n=1
  · subst n
    simpa using seq_recurrence_one
  · exact seq_recurrence_ge_two (by omega)

end BaseProof

lemma A103885_cast_eq_seq (n : ℕ) : (A103885 n : ℝ) = BaseProof.seq n := by
  unfold A103885 BaseProof.seq BaseProof.summand
  by_cases h : n=0
  · simp [h]
  · simp only [h, if_false]
    push_cast
    rfl

lemma A103885_baseRec :
    Transfer.BaseRec (fun n => (A103885 n : ℝ)) := by
  intro n hn
  change Transfer.ra n * (A103885 (n+1) : ℝ) =
    Transfer.rc n * (A103885 n : ℝ) + Transfer.ra (-(n:ℝ)) * (A103885 (n-1) : ℝ)
  rw [A103885_cast_eq_seq, A103885_cast_eq_seq, A103885_cast_eq_seq]
  exact BaseProof.seq_baseRec n hn

lemma product_indices_eq_Ico (m : ℕ) :
    product_indices m = Finset.Ico 1 (2*m+1) := by
  ext k
  simp [product_indices]
  omega

lemma prod_factor_plus_eq_outer (m n : ℕ) :
    prod_factor_plus m n = Transfer.outerPlus m (m*n) := by
  rw [prod_factor_plus, product_indices_eq_Ico,
    Finset.prod_Ico_eq_prod_range]
  unfold Transfer.outerPlus
  congr 1
  funext k
  push_cast
  ring

lemma prod_factor_minus_eq_outer (m n : ℕ) :
    prod_factor_minus m n = Transfer.outerMinus m (m*n) := by
  rw [prod_factor_minus, product_indices_eq_Ico,
    Finset.prod_Ico_eq_prod_range]
  unfold Transfer.outerMinus
  congr 1
  funext k
  push_cast
  ring

lemma A103885_subsequence_real_eq (m n : ℕ) :
    A103885_subsequence_real m n = (A103885 (m*n) : ℝ) := rfl
/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) :=
  by
  refine ⟨Transfer.finalP m, Transfer.finalQ m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Polynomial.degree_eq_iff_natDegree_eq ?_).2 (Transfer.finalP_natDegree m hm)
    intro h
    have hd := Transfer.finalP_natDegree m hm
    simp [h] at hd
    omega
  · apply (Polynomial.degree_eq_iff_natDegree_eq ?_).2 (Transfer.finalQ_natDegree m hm)
    intro h
    have hd := Transfer.finalQ_natDegree m hm
    simp [h] at hd
    omega
  · intro n hn
    have hr := Transfer.normalized_recurrence_all
      (fun j => (A103885 j : ℝ)) A103885_baseRec m n hm hn
    rw [prod_factor_plus_eq_outer, prod_factor_minus_eq_outer]
    simp only [A103885_subsequence_real_eq]
    convert hr using 1 <;> ring
  · exact Transfer.finalP_symmetry m hm
  · intro z hz
    exact Transfer.finalP_complex_roots m hm z hz
  · intro z hz
    exact Transfer.finalQ_complex_roots m hm z hz
