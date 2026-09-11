import FormalConjectures.Util.ProblemImports

set_option linter.unusedSectionVars false

/-
Proof outline.

* Pairing the units modulo a prime power gives a relative factorial-ratio
  congruence of order three (the lemmas through `C_super`).
* A formal-exponential integrality criterion identifies the natural-number
  recursion in the question with the corresponding rational power series.
* For m ≥ 2, `carry_weight_bound` controls the valuation of every term in
  the exponential expansion. Splitting off the indices divisible by p^r
  then proves `framed_super_ge_two`.
* For m = 1 the diagonal coefficient is half a central binomial coefficient.

The final two bridge lemmas connect these power-series statements to the
original definitions, without changing those definitions.
-/

namespace Super
open scoped BigOperators

/-- Divisibility of a rational in the local ring at `p`, allowing integer exponents. -/
def V (p : ℕ) (k : ℤ) (x : ℚ) : Prop := x = 0 ∨ k ≤ padicValRat p x

namespace V
variable {p : ℕ} [Fact p.Prime] {k l : ℤ} {x y : ℚ}

lemma zero (p : ℕ) (k : ℤ) : V p k 0 := Or.inl rfl
lemma of_le (h : k ≤ padicValRat p x) : V p k x := Or.inr h
lemma mono (h : V p k x) (hkl : l ≤ k) : V p l x := h.imp_right hkl.trans
lemma natCast (n : ℕ) : V p 0 n := of_le (by simp)
lemma intCast (n : ℤ) : V p 0 n := of_le (by simp)
lemma add (hx : V p k x) (hy : V p k y) : V p k (x+y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · simpa using of_le hx
  by_cases h : x + y = 0
  · exact Or.inl h
  exact of_le ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add h))
lemma neg (hx : V p k x) : V p k (-x) := by simpa [V] using hx
lemma sub (hx : V p k x) (hy : V p k y) : V p k (x-y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg
lemma mul (hx : V p k x) (hy : V p l y) : V p (k+l) (x*y) := by
  by_cases hxy : x*y = 0
  · exact Or.inl hxy
  have hx0 := (mul_ne_zero_iff.mp hxy).1
  have hy0 := (mul_ne_zero_iff.mp hxy).2
  exact of_le (by rw [padicValRat.mul hx0 hy0]; exact add_le_add (hx.resolve_left hx0) (hy.resolve_left hy0))
lemma div (hx : V p k x) (hy : y ≠ 0) : V p (k - padicValRat p y) (x/y) := by
  rcases hx with rfl | hx
  · simp only [zero_div]; exact zero _ _
  by_cases hx0 : x = 0
  · simp only [hx0, zero_div]; exact zero _ _
  exact of_le (by rw [padicValRat.div hx0 hy]; omega)
lemma sum {α : Type*} (s : Finset α) (f : α → ℚ) (h : ∀ i ∈ s, V p k (f i)) :
    V p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero _ _
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
lemma prod {α : Type*} (s : Finset α) (f : α → ℚ) (w : α → ℤ)
    (h : ∀ i ∈ s, V p (w i) (f i)) : V p (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact of_le (by simp)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
lemma intCast_iff (k : ℕ) (z : ℤ) : V p k z ↔ (p:ℤ)^k ∣ z := by
  simp only [V, Int.cast_eq_zero, padicValRat.of_int, Nat.cast_le, padicValInt_dvd_iff]
lemma natCast_iff (k n : ℕ) : V p k n ↔ p^k ∣ n := by
  simpa only [Int.cast_natCast, ← Int.natCast_pow, Int.natCast_dvd_natCast] using intCast_iff (p := p) k n

lemma pow (hx : V p k x) (n : ℕ) : V p (n*k) (x^n) := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, pow_zero]; exact of_le (by simp)
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hx
lemma mul_right (hx : V p k x) (hy : V p 0 y) : V p k (x*y) := by
  simpa using hx.mul hy
lemma mul_left (hx : V p 0 x) (hy : V p k y) : V p k (x*y) := by
  simpa using hx.mul hy
lemma div_unit (hx : V p k x) (hy : y ≠ 0) (hv : padicValRat p y = 0) : V p k (x/y) := by
  simpa [hv] using hx.div hy
lemma mul_p_pow (hx : V p k x) (n : ℕ) : V p (k+n) (x*(p:ℚ)^n) := by
  have h : V p (n:ℤ) ((p:ℚ)^n) := of_le (by
    rw [padicValRat.pow (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
      padicValRat.self (Fact.out : p.Prime).one_lt, mul_one])
  exact hx.mul h
lemma inv_sub (hx : x ≠ 0) (hy : y ≠ 0) (vx : padicValRat p x = 0)
    (vy : padicValRat p y = 0) (h : V p k (x-y)) : V p k (x⁻¹-y⁻¹) := by
  have eq : x⁻¹-y⁻¹ = (y-x)/(x*y) := by field_simp <;> ring
  rw [eq]
  have h' : V p k (y-x) := by simpa [neg_sub] using h.neg
  exact h'.div_unit (mul_ne_zero hx hy) (by rw [padicValRat.mul hx hy, vx, vy, add_zero])
lemma prod_sub_prod {α : Type*} (s : Finset α) (f g : α → ℚ)
    (hf : ∀ i ∈ s, V p 0 (f i)) (hg : ∀ i ∈ s, V p 0 (g i))
    (h : ∀ i ∈ s, V p k (f i-g i)) : V p k ((∏ i ∈ s, f i)-(∏ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact zero _ _
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have eq : f i * ∏ j ∈ s, f j - g i * ∏ j ∈ s, g j =
        (f i-g i)*(∏ j ∈ s, f j) + g i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j)) := by ring
    rw [eq]
    apply add
    · apply (h i (Finset.mem_insert_self _ _)).mul_right
      simpa using prod s f (fun _ => 0) (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    · exact (hg i (Finset.mem_insert_self _ _)).mul_left
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma prod_one_add {α : Type*} (s : Finset α) (f : α → ℚ) (hk : 0 ≤ k)
    (h : ∀ i ∈ s, V p k (f i)) :
    V p (2*k) ((∏ i ∈ s, (1+f i)) - 1 - ∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, sub_self, sub_zero]; exact zero _ _
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hs := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have heq : (1+f i)*(∏ j ∈ s, (1+f j))-1-(f i+∑ j ∈ s, f j) =
      (1+f i)*((∏ j ∈ s, (1+f j))-1-∑ j ∈ s, f j) + f i*(∑ j ∈ s, f j) := by ring
    rw [heq]
    apply add
    · apply mul_left _ (ih hs)
      exact (natCast 1).add ((h i (Finset.mem_insert_self _ _)).mono hk)
    · simpa only [two_mul] using (h i (Finset.mem_insert_self _ _)).mul (sum s f hs)
end V

lemma val_nat_unit {p : ℕ} [Fact p.Prime] {n : ℕ} (h : ¬p ∣ n) :
    padicValRat p (n:ℚ) = 0 := by simp [padicValNat.eq_zero_of_not_dvd h]


lemma V_of_zmod {p r : ℕ} [Fact p.Prime] {a b : ℤ}
    (h : (a : ZMod (p^r)) = b) : V p r ((a:ℚ)-b) := by
  have hd : (p:ℤ)^r ∣ a-b := by
    rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using sub_eq_zero.mpr h
  simpa using (V.intCast_iff (p := p) r (a-b)).mpr hd


lemma val_add_small {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : V p 1 x) (hy : y ≠ 0) (vy : padicValRat p y = 0) :
    x+y ≠ 0 ∧ padicValRat p (x+y) = 0 := by
  rcases hx with rfl | hx
  · simpa using And.intro hy vy
  have hxy : x+y ≠ 0 := by
    intro h
    have he : x = -y := eq_neg_of_add_eq_zero_left h
    rw [he, padicValRat.neg, vy] at hx
    omega
  refine ⟨hxy, ?_⟩
  by_cases hx0 : x = 0
  · simpa [hx0] using vy
  rw [add_comm, padicValRat.add_eq_of_lt (by rwa [add_comm]) hy hx0 (by omega), vy]

section Units
variable {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
local instance powNZ : NeZero (p^r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

noncomputable def rep {q : ℕ} (u : (ZMod q)ˣ) : ℚ := (u : ZMod q).val

include hr in
lemma rep_val (u : (ZMod (p^r))ˣ) : padicValRat p (rep u) = 0 := by
  apply val_nat_unit
  apply hp.out.coprime_iff_not_dvd.mp
  have h := ZMod.val_coe_unit_coprime u
  exact ((Nat.coprime_pow_right_iff hr _ _).mp h).symm

include hr in
lemma rep_ne (u : (ZMod (p^r))ˣ) : rep u ≠ 0 := by
  letI : Fact (1 < p^r) := ⟨one_lt_pow₀ hp.out.one_lt (Nat.ne_of_gt hr)⟩
  apply Nat.cast_ne_zero.mpr
  intro h
  apply Units.ne_zero u
  have he := ZMod.natCast_zmod_val (u : ZMod (p^r))
  rw [h, Nat.cast_zero] at he
  exact he.symm

lemma rep_mul (u v : (ZMod (p^r))ˣ) : V p r (rep (u*v)-rep u*rep v) := by
  convert V_of_zmod (p := p) (r := r)
    (a := ((u*v : (ZMod (p^r))ˣ) : ZMod (p^r)).val)
    (b := ((u : ZMod (p^r)).val : ℤ)*(v : ZMod (p^r)).val) (by simp) using 1 <;>
    simp [rep]

lemma rep_small (n : ℕ) (hn : n < p^r) (hc : Nat.Coprime n (p^r)) :
    rep (ZMod.unitOfCoprime n hc) = n := by simp [rep, ZMod.val_natCast, Nat.mod_eq_of_lt hn]

include hr in
lemma reciprocal_square_sum (hp5 : 5 ≤ p) :
    V p r (∑ u : (ZMod (p^r))ˣ, (rep u)⁻¹^2) := by
  classical
  have h2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hcp : Nat.Coprime 2 (p^r) :=
    (hp.out.coprime_iff_not_dvd.mpr h2).symm.pow_right r
  let two : (ZMod (p^r))ˣ := ZMod.unitOfCoprime 2 hcp
  have htwo : rep two = 2 := rep_small 2 (lt_of_lt_of_le (by omega) (Nat.le_pow hr)) hcp
  let S : ℚ := ∑ u : (ZMod (p^r))ˣ, (rep u)⁻¹^2
  have he : (∑ u : (ZMod (p^r))ˣ, (rep (two*u))⁻¹^2) = S :=
    Equiv.sum_comp (Equiv.mulLeft two) (fun u => (rep u)⁻¹^2)
  have hi (u : (ZMod (p^r))ˣ) : V p r ((rep (two*u))⁻¹^2 - (2*rep u)⁻¹^2) := by
    have h := V.inv_sub (y := 2*rep u) (rep_ne hr (two*u)) (mul_ne_zero (by norm_num) (rep_ne hr u))
      (rep_val hr (two*u)) (by rw [padicValRat.mul (by norm_num : (2:ℚ) ≠ 0) (rep_ne hr u), ← htwo,
        rep_val hr two, rep_val hr u]; rfl) (by simpa [htwo] using rep_mul two u)
    have eq : (rep (two*u))⁻¹^2-(2*rep u)⁻¹^2 =
      ((rep (two*u))⁻¹-(2*rep u)⁻¹)*((rep (two*u))⁻¹+(2*rep u)⁻¹) := by ring
    rw [eq]
    apply h.mul_right
    apply V.add <;> apply V.of_le
    · simp [padicValRat.inv, rep_val hr]
    · rw [padicValRat.inv, padicValRat.mul (by norm_num : (2:ℚ) ≠ 0) (rep_ne hr u),
        ← htwo, rep_val hr two, rep_val hr u]; norm_num
  have hs := V.sum Finset.univ _ (fun u _ => hi u)
  rw [Finset.sum_sub_distrib, he] at hs
  have eq : (∑ u : (ZMod (p^r))ˣ, (2*rep u)⁻¹^2) = S/4 := by
    simp only [mul_inv_rev, mul_pow, ← Finset.sum_mul]
    dsimp [S]
    norm_num
    ring
  rw [eq] at hs
  have hv3 : padicValRat p (3:ℚ) = 0 := val_nat_unit h3
  have h := (hs.mul_right (V.natCast 4)).div_unit (by norm_num : (3:ℚ) ≠ 0) hv3
  convert h using 1 <;> ring

include hr in
lemma rep_neg (u : (ZMod (p^r))ˣ) : rep (-u) = (p:ℚ)^r-rep u := by
  letI : Fact (1 < p^r) := ⟨one_lt_pow₀ hp.out.one_lt (Nat.ne_of_gt hr)⟩
  letI : NeZero (u : ZMod (p^r)) := ⟨Units.ne_zero u⟩
  simp only [rep, Units.val_neg, ZMod.val_neg_of_ne_zero]
  rw [Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt _)), Nat.cast_pow]

include hr in
lemma reciprocal_pair_sum (hp5 : 5 ≤ p) :
    V p r (∑ u : (ZMod (p^r))ˣ, (rep u * rep (-u))⁻¹) := by
  classical
  have h (u : (ZMod (p^r))ˣ) :
      V p r ((rep u * rep (-u))⁻¹ + (rep u)⁻¹^2) := by
    have he : (rep u * rep (-u))⁻¹ + (rep u)⁻¹^2 =
        (p:ℚ)^r / (rep u ^ 2 * rep (-u)) := by
      field_simp [rep_ne hr u, rep_ne hr (-u)]
      have := rep_neg hr u
      nlinarith
    rw [he]
    apply V.div_unit
    · convert (V.natCast (p := p) 1).mul_p_pow r using 1 <;> simp
    · exact mul_ne_zero (pow_ne_zero _ (rep_ne hr u)) (rep_ne hr (-u))
    · rw [padicValRat.mul (pow_ne_zero _ (rep_ne hr u)) (rep_ne hr (-u)),
        padicValRat.pow (rep_ne hr u), rep_val hr u, rep_val hr (-u)]; simp
  have hs := V.sum Finset.univ _ (fun u _ => h u)
  rw [Finset.sum_add_distrib] at hs
  convert hs.sub (reciprocal_square_sum hr hp5) using 1 <;> ring

noncomputable def blockRatio (a : ℕ) : ℚ :=
  ∏ u : (ZMod (p^r))ˣ, (1+(a:ℚ)*(p:ℚ)^r/rep u)

include hr in
lemma blockRatio_mod (a : ℕ) : V p r (blockRatio (p := p) (r := r) a-1) := by
  classical
  have h (u : (ZMod (p^r))ˣ) : V p r ((a:ℚ)*(p:ℚ)^r/rep u) := by
    have hv : V p r ((a:ℚ)*(p:ℚ)^r) := by simpa using (V.natCast a).mul_p_pow r
    exact hv.div_unit (rep_ne hr u) (rep_val hr u)
  have hh := V.prod_sub_prod Finset.univ (fun u : (ZMod (p^r))ˣ => 1+(a:ℚ)*(p:ℚ)^r/rep u)
    (fun _ => 1) (fun u _ => (V.natCast 1).add ((h u).mono (by omega)))
    (fun _ _ => V.natCast 1) (fun u _ => by simpa using h u)
  simpa [blockRatio] using hh

include hr in
lemma blockRatio_square (hp5 : 5 ≤ p) (a : ℕ) :
    V p (3*r) (blockRatio (p := p) (r := r) a ^ 2-1) := by
  classical
  let f (u : (ZMod (p^r))ˣ) : ℚ :=
    (a:ℚ)*(a+1)*(p:ℚ)^(2*r)/(rep u * rep (-u))
  have hf (u : (ZMod (p^r))ˣ) : V p (2*r) (f u) := by
    apply V.div_unit
    · convert (V.natCast (p := p) (a*(a+1))).mul_p_pow (2*r) using 1 <;> simp [Nat.cast_mul, Nat.cast_add]
    · exact mul_ne_zero (rep_ne hr u) (rep_ne hr (-u))
    · rw [padicValRat.mul (rep_ne hr u) (rep_ne hr (-u)), rep_val hr u, rep_val hr (-u)]; rfl
  have hs : V p (3*r) (∑ u, f u) := by
    have he : (∑ u, f u) = ((a:ℚ)*(a+1)*(∑ u : (ZMod (p^r))ˣ, (rep u*rep (-u))⁻¹)) * (p:ℚ)^(2*r) := by
      simp only [f, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros
      ring
    rw [he]
    have ht := ((V.natCast (p := p) (a*(a+1))).mul_left (reciprocal_pair_sum hr hp5)).mul_p_pow (2*r)
    convert ht using 1 <;> push_cast <;> ring
  have he : blockRatio (p := p) (r := r) a ^ 2 = ∏ u, (1+f u) := by
    have hn : (∏ u : (ZMod (p^r))ˣ, (1+(a:ℚ)*(p:ℚ)^r/rep (-u))) = blockRatio (p := p) (r := r) a := by
      exact Equiv.prod_comp (Equiv.neg ((ZMod (p^r))ˣ)) (fun u => 1+(a:ℚ)*(p:ℚ)^r/rep u)
    rw [pow_two]
    nth_rw 2 [← hn]
    rw [blockRatio, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro u _
    dsimp [f]
    rw [show (2*r : ℕ) = r+r by omega, pow_add]
    field_simp [rep_ne hr u, rep_ne hr (-u)]
    rw [rep_neg hr u]
    ring
  rw [he]
  have hlin := V.prod_one_add Finset.univ f (by omega : (0:ℤ) ≤ 2*r) (fun u _ => hf u)
  have ht := (hlin.mono (by omega : (3:ℤ)*r ≤ 2*(2*r))).add hs
  convert ht using 1 <;> ring

include hr in
lemma blockRatio_super (hp5 : 5 ≤ p) (a : ℕ) :
    V p (3*r) (blockRatio (p := p) (r := r) a-1) := by
  have h2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h := val_add_small ((blockRatio_mod hr a).mono (by omega))
    (by norm_num : (2:ℚ) ≠ 0) (val_nat_unit h2)
  have he : blockRatio (p := p) (r := r) a-1+2 = blockRatio (p := p) (r := r) a+1 := by ring
  rw [he] at h
  have ht := (blockRatio_square hr hp5 a).div_unit h.1 h.2
  convert ht using 1
  exact (eq_div_iff h.1).mpr (by ring)
end Units

noncomputable def unitFact (p n : ℕ) : ℚ :=
  ∏ i ∈ Finset.range n, if p ∣ i+1 then 1 else (i+1:ℕ)

lemma unitFact_succ (p n : ℕ) : unitFact p (n+1) =
    unitFact p n * (if p ∣ n+1 then 1 else (n+1:ℕ)) := by
  simp only [unitFact, Finset.prod_range_succ, Nat.cast_ite, Nat.cast_one]

lemma unitFact_ne (p n : ℕ) : unitFact p n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · norm_num
  · exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)

lemma unitFact_val {p : ℕ} [Fact p.Prime] (n : ℕ) : padicValRat p (unitFact p n) = 0 := by
  induction n with
  | zero => simp [unitFact]
  | succ n ih =>
    rw [unitFact_succ]
    split_ifs with h
    · simpa using ih
    · rw [padicValRat.mul (unitFact_ne _ _) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)),
        ih, val_nat_unit h, add_zero]

lemma factorial_decomp {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    (n.factorial : ℚ) = (p:ℚ)^(n/p) * (n/p).factorial * unitFact p n := by
  induction n with
  | zero => simp [unitFact]
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, ih, unitFact_succ]
    by_cases h : p ∣ n+1
    · rw [if_pos h, Nat.succ_div_of_dvd h, Nat.factorial_succ, Nat.cast_mul, pow_succ]
      have he : (n+1:ℚ) = p*(n/p+1:ℕ) := by
        exact_mod_cast (by rw [← Nat.succ_div_of_dvd h, Nat.mul_div_cancel' h] : n+1 = p*((n/p)+1))
      push_cast
      rw [he]
      push_cast
      ring
    · rw [if_neg h, Nat.succ_div_of_not_dvd h]
      ring

section UnitBlocks
variable {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
local instance : NeZero (p^r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

include hr in
lemma unitFact_block (a : ℕ) :
    (∏ i ∈ Finset.range (p^r), if p ∣ i+1 then (1:ℚ) else (i+1+a*p^r:ℕ)) =
    ∏ u : (ZMod (p^r))ˣ, (rep u+(a:ℚ)*(p:ℚ)^r) := by
  classical
  conv_lhs =>
    arg 2
    intro i
    rw [← ite_not]
  rw [← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun (u : (ZMod (p^r))ˣ) _ => (u : ZMod (p^r)).val-1)
  · intro u _
    have hcp := ZMod.val_coe_unit_coprime u
    have hnd := hp.out.coprime_iff_not_dvd.mp (((Nat.coprime_pow_right_iff hr _ _).mp hcp).symm)
    have hpos : 0 < (u : ZMod (p^r)).val := Nat.pos_of_ne_zero (fun h => hnd (h ▸ dvd_zero p))
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have := ZMod.val_lt (u : ZMod (p^r)); omega
    · simpa [Nat.sub_add_cancel hpos] using hnd
  · intro u _ v _ huv
    apply Units.ext
    apply ZMod.val_injective
    have hu := Nat.cast_ne_zero.mp (rep_ne hr u)
    have hv := Nat.cast_ne_zero.mp (rep_ne hr v)
    change (u : ZMod (p^r)).val ≠ 0 at hu
    change (v : ZMod (p^r)).val ≠ 0 at hv
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hiq : i+1 < p^r := by
      have hpd : p ∣ p^r := dvd_pow_self _ (Nat.ne_of_gt hr)
      by_contra hn
      have he : i+1 = p^r := by omega
      exact hi.2 (he ▸ hpd)
    have hcp : Nat.Coprime (i+1) (p^r) :=
      (hp.out.coprime_iff_not_dvd.mpr hi.2).symm.pow_right r
    refine ⟨ZMod.unitOfCoprime (i+1) hcp, Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hiq]
    omega
  · intro u _
    have hu := Nat.cast_ne_zero.mp (rep_ne hr u)
    change (u : ZMod (p^r)).val ≠ 0 at hu
    rw [Nat.sub_add_cancel (by omega)]
    simp [rep, Nat.cast_add, Nat.cast_mul]

include hr in
lemma unitFact_block_succ (a : ℕ) :
    unitFact p ((a+1)*p^r) = unitFact p (a*p^r) *
      ∏ u : (ZMod (p^r))ˣ, (rep u+(a:ℚ)*(p:ℚ)^r) := by
  rw [Nat.add_mul, one_mul, unitFact, Finset.prod_range_add]
  congr 1
  rw [← unitFact_block hr a]
  apply Finset.prod_congr rfl
  intro i _
  have hpd : p ∣ a*p^r := dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.ne_of_gt hr)) _
  have he : p ∣ a*p^r+i+1 ↔ p ∣ i+1 := by rw [add_assoc, Nat.dvd_add_right hpd]
  simp only [he]
  split_ifs <;> push_cast <;> ring

include hr in
lemma unitFact_base : unitFact p (p^r) = ∏ u : (ZMod (p^r))ˣ, rep u := by
  simpa [unitFact] using unitFact_block hr (p := p) 0

include hr in
lemma unitFact_block_ratio (a : ℕ) :
    (∏ u : (ZMod (p^r))ˣ, (rep u+(a:ℚ)*(p:ℚ)^r)) =
      unitFact p (p^r) * blockRatio (p := p) (r := r) a := by
  rw [unitFact_base hr, blockRatio, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _
  field_simp [rep_ne hr u]

include hr in
lemma unitFact_cong (k : ℤ) (hk : 0 ≤ k)
    (hb : ∀ a, V p k (blockRatio (p := p) (r := r) a-1)) (a : ℕ) :
    V p k (unitFact p (a*p^r) - unitFact p (p^r)^a) := by
  induction a with
  | zero => simp [unitFact]; exact V.zero _ _
  | succ a ih =>
    rw [unitFact_block_succ hr, unitFact_block_ratio hr, pow_succ]
    have he : unitFact p (a*p^r)*(unitFact p (p^r)*blockRatio (p := p) (r := r) a)-
        unitFact p (p^r)^a*unitFact p (p^r) =
        unitFact p (a*p^r)*unitFact p (p^r)*(blockRatio (p := p) (r := r) a-1)+
        (unitFact p (a*p^r)-unitFact p (p^r)^a)*unitFact p (p^r) := by ring
    rw [he]
    apply V.add
    · apply V.mul_left _ (hb a)
      apply V.mul_left <;> exact V.of_le (by rw [unitFact_val])
    · exact ih.mul_right (V.of_le (by rw [unitFact_val]))
end UnitBlocks

lemma V.pow_sub_pow {p : ℕ} [Fact p.Prime] {k : ℤ} {x y : ℚ}
    (h : V p k (x-y)) (hx : V p 0 x) (hy : V p 0 y) (n : ℕ) : V p k (x^n-y^n) := by
  simpa using V.prod_sub_prod (Finset.range n) (fun _ => x) (fun _ => y)
    (fun _ _ => hx) (fun _ _ => hy) (fun _ _ => h)

lemma unitFact_ratio_cong {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    (k : ℤ) (hk : 0 ≤ k)
    (hb : ∀ a, V p k (blockRatio (p := p) (r := r) a-1))
    (m t : ℕ) (ht : p^r ∣ t) :
    V p k (unitFact p (m*t)/(unitFact p t)^m-1) := by
  obtain ⟨a, rfl⟩ := ht
  rw [mul_comm (p^r) a]
  have h1 := unitFact_cong hr k hk hb (m*a)
  have h2 := (unitFact_cong hr k hk hb a).pow_sub_pow
    (V.of_le (by rw [unitFact_val])) (by
      apply V.of_le
      rw [padicValRat.pow (unitFact_ne _ _), unitFact_val, mul_zero]) m
  rw [← pow_mul] at h2
  have he : V p k (unitFact p (m*(a*p^r))-unitFact p (a*p^r)^m) := by
    have := h1.sub h2
    convert this using 1
    simp only [Nat.mul_assoc, Nat.mul_comm m a]
    ring
  have hv : padicValRat p (unitFact p (a*p^r)^m) = 0 := by
    rw [padicValRat.pow (unitFact_ne _ _), unitFact_val, mul_zero]
  have h := he.div_unit (pow_ne_zero _ (unitFact_ne _ _)) hv
  convert h using 1
  field_simp [unitFact_ne p (a*p^r)]

noncomputable def C (m k : ℕ) : ℚ := (m*k).factorial / (k.factorial:ℚ)^m

lemma factorial_ratio_dvd (m k : ℕ) : k.factorial^m ∣ (m*k).factorial := by
  simpa using Nat.prod_factorial_dvd_factorial_sum (Finset.range m) (fun _ => k)

lemma C_nat (m k : ℕ) : C m k = (((m*k).factorial / k.factorial^m : ℕ):ℚ) := by
  rw [Nat.cast_div_charZero (factorial_ratio_dvd m k), Nat.cast_pow]
  rfl

lemma C_ne (m k : ℕ) : C m k ≠ 0 := by
  apply div_ne_zero
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

lemma C_integral {p : ℕ} [Fact p.Prime] (m k : ℕ) : V p 0 (C m k) := by
  rw [C_nat]; exact V.natCast _

lemma C_scale {p : ℕ} [hp : Fact p.Prime] (m k : ℕ) :
    C m (p*k) / C m k = unitFact p (m*(p*k)) / (unitFact p (p*k))^m := by
  have hp0 : (p:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hk0 : (k.factorial:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hmk0 : ((m*k).factorial:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold C
  rw [factorial_decomp (p := p) (m*(p*k)), factorial_decomp (p := p) (p*k)]
  rw [show m*(p*k) = p*(m*k) by ring, Nat.mul_div_right _ hp.out.pos,
    Nat.mul_div_right _ hp.out.pos]
  rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm k m]
  field_simp

lemma C_scale_val {p : ℕ} [hp : Fact p.Prime] (m k : ℕ) :
    padicValRat p (C m (p*k)) = padicValRat p (C m k) := by
  have h := congrArg (padicValRat p) (C_scale (p := p) m k)
  rw [padicValRat.div (C_ne _ _) (C_ne _ _),
    padicValRat.div (unitFact_ne _ _) (pow_ne_zero _ (unitFact_ne _ _)),
    padicValRat.pow (unitFact_ne _ _), unitFact_val, unitFact_val] at h
  omega

lemma C_relative_cong {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    (k : ℤ) (hk : 0 ≤ k)
    (hb : ∀ a, V p k (blockRatio (p := p) (r := r) a-1))
    (m n : ℕ) (hn : p^r ∣ p*n) : V p (k+padicValRat p (C m n)) (C m (p*n)-C m n) := by
  have h := unitFact_ratio_cong hr k hk hb m (p*n) hn
  rw [← C_scale] at h
  have hh := h.mul (V.of_le (le_refl (padicValRat p (C m n))))
  convert hh using 1
  field_simp [C_ne m n]

lemma C_super {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) (hp5 : 5 ≤ p)
    (m n : ℕ) (hn : p^r ∣ p*n) :
    V p (3*r+padicValRat p (C m n)) (C m (p*n)-C m n) :=
  C_relative_cong hr (3*r) (by omega) (blockRatio_super hr hp5) m n hn

lemma C_gauss {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    (m n : ℕ) (hn : p^r ∣ p*n) : V p r (C m (p*n)-C m n) := by
  have h := C_relative_cong hr r (by omega) (blockRatio_mod hr) m n hn
  apply h.mono
  have hv := (C_integral (p := p) m n).resolve_left (C_ne m n)
  omega

namespace Series
open PowerSeries
local notation "PS" => PowerSeries ℚ
local notation "D" => PowerSeries.derivative ℚ

noncomputable def E (f : PS) : PS :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n+1), coeff n (f^k) / (k.factorial:ℚ)
noncomputable def T (f : PS) (n : ℕ) : PS :=
  ∑ k ∈ Finset.range n, (1/(k.factorial:ℚ)) • f^k

lemma coeff_E (f : PS) (n : ℕ) : coeff n (E f) =
    ∑ k ∈ Finset.range (n+1), coeff n (f^k) / (k.factorial:ℚ) := by simp [E]
lemma coeff_pow_zero {f : PS} (hf : constantCoeff f = 0) {n k : ℕ} (h : n < k) :
    coeff n (f^k) = 0 :=
  coeff_of_lt_order _ ((by exact_mod_cast h : (n:ℕ∞) < k).trans_le
    (le_order_pow_of_constantCoeff_eq_zero k hf))
lemma coeff_E_eq_T {f : PS} (hf : constantCoeff f = 0) {n b : ℕ} (h : n < b) :
    coeff n (E f) = coeff n (T f b) := by
  simp only [coeff_E, T, map_sum, coeff_smul, smul_eq_mul, one_div, div_eq_mul_inv]
  simp only [one_mul]
  simp_rw [mul_comm (_⁻¹ : ℚ)]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  have hi' : n < i := by simpa using hi
  rw [coeff_pow_zero hf hi', zero_mul]
lemma const_E (f : PS) : constantCoeff (E f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [coeff_E]
lemma T_zero (f : PS) : T f 0 = 0 := by simp [T]
lemma T_succ (f : PS) (n : ℕ) : T f (n+1) = T f n + (1/(n.factorial:ℚ)) • f^n := by
  simp only [T, Finset.sum_range_succ]
lemma inv_factorial_succ (n : ℕ) : (1/((n+1).factorial:ℚ))*(n+1) = 1/(n.factorial:ℚ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
lemma D_T (f : PS) (n : ℕ) : D (T f (n+1)) = D f * T f n := by
  simp only [T, map_sum, Derivation.map_smul, Derivation.leibniz_pow,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_eq_mul]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_smul, add_zero,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, inv_factorial_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_mul_assoc, mul_smul_comm, mul_comm]
lemma coeff_mul_congr_right {f g h : PS} {n : ℕ}
    (hh : ∀ i ≤ n, coeff i g = coeff i h) : coeff n (f*g) = coeff n (f*h) := by
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hh ij.2 (Finset.antidiagonal.snd_le hij)]
lemma D_E {f : PS} (hf : constantCoeff f = 0) : D (E f) = D f * E f := by
  ext n
  rw [coeff_derivative, coeff_E_eq_T hf (by omega : n+1 < n+2), ← coeff_derivative,
    show n+2 = (n+1)+1 by omega, D_T]
  exact coeff_mul_congr_right (fun i hi => (coeff_E_eq_T hf (by omega : i < n+1)).symm)
lemma ode_unique {f g h : PS} (hf : D f = h*f) (hg : D g = h*g)
    (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hc
    | succ n =>
      have he : coeff n (D f) = coeff n (D g) := by
        rw [hf, hg]
        exact coeff_mul_congr_right (fun i hi => ih i (by omega))
      rw [coeff_derivative, coeff_derivative] at he
      exact (mul_right_cancel₀ (by positivity : (n+1:ℚ) ≠ 0)) he
lemma E_add {f g : PS} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    E (f+g) = E f * E g := by
  apply ode_unique (h := D (f+g))
  · exact D_E (by simp [hf, hg])
  · rw [Derivation.leibniz, D_E hf, D_E hg, map_add]
    simp only [smul_eq_mul]
    ring
  · simp [const_E]
lemma E_zero : E (0:PS) = 1 := by
  apply ode_unique (h := (0:PS))
  · rw [D_E (f := 0) (by simp)]; simp
  · simp
  · simp [const_E]
lemma E_nsmul {f : PS} (hf : constantCoeff f = 0) (n : ℕ) : E (n • f) = E f ^ n := by
  induction n with
  | zero => simpa using E_zero
  | succ n ih =>
    rw [succ_nsmul, E_add (by simp [hf]) hf, ih, pow_succ]
lemma E_sub {f g : PS} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    E f = E g * E (f-g) := by
  rw [← E_add hg (by simp [hf, hg])]
  congr 1
  ring

lemma T_expand (q : ℕ) (hq : q ≠ 0) (f : PS) (n : ℕ) :
    T (expand q hq f) n = expand q hq (T f n) := by
  simp [T, map_sum, expand_smul, map_pow]
lemma E_expand (q : ℕ) (hq : q ≠ 0) {f : PS} (hf : constantCoeff f = 0) :
    E (expand q hq f) = expand q hq (E f) := by
  ext n
  rw [coeff_E_eq_T (by simpa using hf) (Nat.lt_succ_self n), T_expand, coeff_expand, coeff_expand]
  split_ifs
  · exact (coeff_E_eq_T hf (Nat.lt_succ_of_le (Nat.div_le_self _ _))).symm
  · rfl

def SV (p : ℕ) (k : ℤ) (f : PS) := ∀ n, V p k (coeff n f)
namespace SV
variable {p : ℕ} [hp : Fact p.Prime] {k l : ℤ} {f g : PS}
lemma zero : SV p k 0 := by intro n; simp only [map_zero]; exact V.zero _ _
lemma one : SV p 0 1 := by
  intro n
  rw [coeff_one]
  split_ifs <;> first | exact V.natCast 1 | exact V.zero _ _
lemma mono (hf : SV p k f) (h : l ≤ k) : SV p l f := fun n => (hf n).mono h
lemma add (hf : SV p k f) (hg : SV p k g) : SV p k (f+g) := by
  intro n; rw [map_add]; exact (hf n).add (hg n)
lemma sub (hf : SV p k f) (hg : SV p k g) : SV p k (f-g) := by
  intro n; rw [map_sub]; exact (hf n).sub (hg n)
lemma mul (hf : SV p k f) (hg : SV p l g) : SV p (k+l) (f*g) := by
  intro n
  rw [coeff_mul]
  apply V.sum
  intro ij _
  exact (hf ij.1).mul (hg ij.2)
lemma pow (hf : SV p k f) (n : ℕ) : SV p (n*k) (f^n) := by
  induction n with
  | zero => simpa using (one (p := p))
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf
lemma expand (hf : SV p k f) (q : ℕ) (hq : q ≠ 0) : SV p k (PowerSeries.expand q hq f) := by
  intro n; rw [coeff_expand]; split_ifs
  · exact hf _
  · exact V.zero _ _
lemma smul {a : ℚ} (ha : V p k a) (hf : SV p l f) : SV p (k+l) (a • f) := by
  intro n; rw [coeff_smul]; exact ha.mul (hf n)
lemma E_sub_one (hk : 1 ≤ k) (hf : SV p k f) : SV p k (E f-1) := by
  intro n
  rw [map_sub, coeff_E, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_sub_cancel_right]
  apply V.sum
  intro j _
  have hval := padicValNat_factorial_lt_of_ne_zero (p := p) (Nat.succ_ne_zero j)
  have h := ((hf.pow (j+1)) n).div
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j+1)))
  apply h.mono
  rw [padicValRat.of_nat]
  have hv : (padicValNat p (j+1).factorial:ℤ) < j+1 := by exact_mod_cast hval
  push_cast
  nlinarith
lemma E (hk : 1 ≤ k) (hf : SV p k f) : SV p 0 (Series.E f) := by
  have h := (hf.E_sub_one hk).mono (by omega : (0:ℤ) ≤ k)
  convert h.add (one (p := p)) using 1 <;> simp
end SV

lemma coeff_mul_initial {f g : PS} {n : ℕ} (hf : ∀ i < n, coeff i f = 0) :
    coeff n (f*g) = coeff n f * constantCoeff g := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (n,0) (by simp)]
  · simp
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 < n := by
      by_contra h
      have he : ij = (n,0) := by ext <;> simp only [Prod.fst, Prod.snd] <;> omega
      exact hne he
    rw [hf _ hi, zero_mul]
lemma coeff_pow_difference {f g : PS} {n : ℕ} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (hfg : ∀ i < n, coeff i f = coeff i g) (k : ℕ) :
    coeff n (f^k) - coeff n (g^k) = k*(coeff n f-coeff n g) := by
  rw [← map_sub, ← (Commute.all f g).mul_geom_sum₂ k,
    coeff_mul_initial (by intro i hi; simp [hfg i hi])]
  simp [hf, hg, mul_comm]

lemma int_power_gauss {p : ℕ} [hp : Fact p.Prime] (g : PowerSeries ℤ) (n : ℕ) :
    V p 1 (coeff n ((PowerSeries.map (Int.castRingHom ℚ) g)^p) -
      coeff n (expand p hp.out.ne_zero (PowerSeries.map (Int.castRingHom ℚ) g))) := by
  let gm : PowerSeries (ZMod p) := PowerSeries.map (Int.castRingHom (ZMod p)) g
  have he : expand p hp.out.ne_zero gm = gm^p := by
    have h := MvPowerSeries.map_frobenius_expand p hp.out.ne_zero (f := gm)
    have hfrob : frobenius (ZMod p) p = RingHom.id _ := by ext x; simp [frobenius_def]
    rw [hfrob, MvPowerSeries.map_id] at h
    exact h
  have h := congrArg (coeff n) he.symm
  change coeff n ((PowerSeries.map (Int.castRingHom (ZMod p)) g)^p) =
    coeff n (expand p hp.out.ne_zero (PowerSeries.map (Int.castRingHom (ZMod p)) g)) at h
  rw [← map_pow, ← map_expand, coeff_map, coeff_map] at h
  have hv : V p 1 (((coeff n (g^p):ℤ):ℚ)-(coeff n (expand p hp.out.ne_zero g):ℤ)) := by
    rw [← Int.cast_sub]
    apply (V.intCast_iff (p := p) 1 _).mpr
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    exact sub_eq_zero.mpr h
  simpa only [← map_pow, ← map_expand, coeff_map, Int.coe_castRingHom, Nat.cast_one] using hv

lemma integral_of_local (x : ℚ) (h : ∀ p : ℕ, ∀ hp : p.Prime, @V p 0 x) :
    ∃ z : ℤ, (z:ℚ) = x := by
  have hd : x.den = 1 := by
    by_contra hd
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hd
    letI : Fact p.Prime := ⟨hp⟩
    have hv := h p hp
    rcases hv with hx | hv
    · simp [hx] at hd
    have hnd : ¬p ∣ x.num.natAbs := hp.coprime_iff_not_dvd.mp (x.reduced.of_dvd_right hpd).symm
    have hvn : padicValInt p x.num = 0 := padicValNat.eq_zero_of_not_dvd hnd
    have hvd := one_le_padicValNat_of_dvd (Nat.ne_of_gt x.den_pos) hpd
    rw [padicValRat_def, hvn] at hv
    omega
  exact ⟨x.num, (Rat.den_eq_one_iff x).mp hd⟩

lemma V_coeff_mul {p : ℕ} [Fact p.Prime] {k l : ℤ} {f g : PS} (n : ℕ)
    (hf : ∀ i ≤ n, V p k (coeff i f)) (hg : ∀ i ≤ n, V p l (coeff i g)) :
    V p (k+l) (coeff n (f*g)) := by
  rw [coeff_mul]
  apply V.sum
  intro ij hij
  exact (hf _ (Finset.antidiagonal.fst_le hij)).mul (hg _ (Finset.antidiagonal.snd_le hij))

lemma E_integral {f : PS} (hf : constantCoeff f = 0)
    (hF : ∀ p : ℕ, ∀ hp : p.Prime, SV p 1 (p • f - expand p hp.ne_zero f)) :
    ∀ n : ℕ, ∃ z : ℤ, (z:ℚ) = coeff n (E f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨1, by simp [coeff_E]⟩
    apply integral_of_local
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    classical
    let A := E f
    let gz : PowerSeries ℤ := PowerSeries.mk fun i => if hi : i < n then Classical.choose (ih i hi) else 0
    let g : PS := PowerSeries.map (Int.castRingHom ℚ) gz
    have hg (i : ℕ) (hi : i < n) : coeff i g = coeff i A := by
      simp only [g, gz, coeff_map, coeff_mk, dif_pos hi, Int.coe_castRingHom]
      exact Classical.choose_spec (ih i hi)
    have hgn : coeff n g = 0 := by simp [g, gz]
    have hg0 : constantCoeff g = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hg 0 hn]
      simpa [A] using const_E f
    have hAn : ∀ i ≤ n, V p 0 (coeff i (expand p hp.ne_zero A)) := by
      intro i hi
      rw [coeff_expand]
      split_ifs with hpi
      · have hin : i/p < n := by
          by_cases hi0 : i = 0
          · simpa [hi0] using hn
          exact (Nat.div_lt_self (Nat.pos_of_ne_zero hi0) hp.one_lt).trans_le hi
        obtain ⟨z,hz⟩ := ih (i/p) hin
        rw [← hz]; exact V.intCast z
      · exact V.zero _ _
    have hge : coeff n (expand p hp.ne_zero g) = coeff n (expand p hp.ne_zero A) := by
      rw [coeff_expand, coeff_expand]
      split_ifs
      · exact hg _ (Nat.div_lt_self hn hp.one_lt)
      · rfl
    have he : A^p = expand p hp.ne_zero A * E (p • f-expand p hp.ne_zero f) := by
      dsimp [A]
      rw [← E_nsmul hf p, E_sub (g := expand p hp.ne_zero f) (by simp [hf]) (by simp [hf]), E_expand p hp.ne_zero hf]
    have hsmall := SV.E_sub_one (by norm_num : (1:ℤ) ≤ 1) (hF p hp)
    have hfirst : V p 1 (coeff n (A^p)-coeff n (expand p hp.ne_zero A)) := by
      rw [← map_sub, he]
      convert V_coeff_mul n hAn (fun i _ => hsmall i) using 1 <;> simp [mul_sub]
    have hsecond : V p 1 (coeff n (g^p)-coeff n (expand p hp.ne_zero A)) := by
      rw [← hge]
      exact int_power_gauss gz n
    have hdiff := hfirst.sub hsecond
    have hd : V p 1 (coeff n (A^p)-coeff n (g^p)) := by
      convert hdiff using 1 <;> ring
    rw [coeff_pow_difference (const_E f) hg0 (fun i hi => (hg i hi).symm) p, hgn, sub_zero] at hd
    have hquot := hd.div (Nat.cast_ne_zero.mpr hp.ne_zero)
    rw [padicValRat.self hp.one_lt, sub_self] at hquot
    convert hquot using 1
    field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]

noncomputable def L (m s n : ℕ) : PS :=
  PowerSeries.mk fun k => (n:ℚ)*Super.C m (s*k)/(k:ℚ)
lemma coeff_L (m s n k : ℕ) : coeff k (L m s n) = (n:ℚ)*Super.C m (s*k)/(k:ℚ) := by
  simp [L]
lemma const_L (m s n : ℕ) : constantCoeff (L m s n) = 0 := by simp [L]

lemma L_dwork (m s n p : ℕ) (hp : p.Prime) : SV p 1 (p • L m s n - expand p hp.ne_zero (L m s n)) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro k
  rw [map_sub, map_nsmul, nsmul_eq_mul, coeff_expand, coeff_L]
  split_ifs with hpk
  · obtain ⟨j,rfl⟩ := hpk
    rw [Nat.mul_div_right _ hp.pos, coeff_L]
    rcases j.eq_zero_or_pos with rfl | hj
    · simp; exact V.zero _ _
    have hdiv : p^(padicValNat p j+1) ∣ p*(s*j) := by
      rw [pow_succ]
      have h := Nat.mul_dvd_mul_right (pow_padicValNat_dvd (p := p) (n := j)) p
      have hh := dvd_mul_left (p*j) s
      apply h.trans
      convert hh using 1 <;> ring
    have hc := C_gauss (by omega : 0 < padicValNat p j+1) m (s*j) hdiv
    have hc' := ((V.natCast (p := p) n).mul_left hc).div
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hj))
    have hv : V p 1 ((n:ℚ)*(Super.C m (p*(s*j))-Super.C m (s*j))/(j:ℚ)) := by
      convert hc' using 1 <;> simp
    convert hv using 1
    rw [show s*(p*j) = p*(s*j) by ring]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]
  · simp only [sub_zero]
    have hc := (V.natCast (p := p) n).mul_left (C_integral (p := p) m (s*k))
    have hk0 : (k:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hpk (h ▸ dvd_zero p))
    have hd := hc.div_unit hk0 (val_nat_unit hpk)
    have h := hd.mul_p_pow 1
    convert h using 1 <;> simp [mul_comm]

lemma E_L_integral (m s n k : ℕ) : ∃ z : ℤ, (z:ℚ) = coeff k (E (L m s n)) :=
  E_integral (const_L m s n) (L_dwork m s n) k
lemma E_L_local {p : ℕ} [Fact p.Prime] (m s n : ℕ) : SV p 0 (E (L m s n)) := by
  intro k
  obtain ⟨z,hz⟩ := E_L_integral m s n k
  rw [← hz]
  exact V.intCast z

lemma D_L_coeff (m s n j : ℕ) : coeff j (D (L m s n)) = (n:ℚ)*Super.C m (s*(j+1)) := by
  rw [coeff_derivative, coeff_L]
  push_cast
  field_simp
lemma E_L_rec (m s n k : ℕ) :
    (k+1:ℚ)*coeff (k+1) (E (L m s n)) =
      ∑ j ∈ Finset.range (k+1), (n:ℚ)*Super.C m (s*(j+1))*coeff (k+1-(j+1)) (E (L m s n)) := by
  rw [mul_comm, ← coeff_derivative, D_E (const_L m s n), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [D_L_coeff, show k+1-(j+1) = k-j by omega]
end Series

lemma C_val_formula {p : ℕ} [hp : Fact p.Prime] (m j b : ℕ)
    (hj : Nat.log p j < b) (hmj : Nat.log p (m*j) < b) :
    padicValRat p (C m j) = ∑ e ∈ Finset.Ico 1 b, ((m*(j%p^e))/p^e:ℕ) := by
  rw [C, padicValRat.div (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))),
    padicValRat.pow (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    padicValRat.of_nat, padicValRat.of_nat, padicValNat_factorial hmj, padicValNat_factorial hj]
  simp only [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have he : m*j/p^e = m*(j/p^e)+(m*(j%p^e))/p^e := by
    calc
      m*j/p^e = ((p^e)*(m*(j/p^e))+m*(j%p^e))/p^e := by
        congr 1
        have := Nat.mod_add_div j (p^e)
        nlinarith
      _ = _ := Nat.mul_add_div (pow_pos hp.out.pos _) _ _
  rw [he, Nat.cast_add, Nat.cast_mul]
  ring

lemma C_val_bound {p : ℕ} [hp : Fact p.Prime] (m j s r : ℕ) :
    (∑ e ∈ Finset.Ico (s+1) (r+1), (((m*(j%p^e))/p^e:ℕ):ℤ)) ≤ padicValRat p (C m j) := by
  let b := max (r+1) (max (Nat.log p j+1) (Nat.log p (m*j)+1))
  rw [C_val_formula m j b (by dsimp [b]; omega) (by dsimp [b]; omega)]
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_Ico] at he ⊢
    dsimp [b]
    omega
  · intros; positivity

lemma residue_carry {α : Type*} (I : Finset α) (a : α → ℕ) (q m : ℕ)
    (hq : 0 < q) (hm : 2 ≤ m) (hdiv : q ∣ ∑ i ∈ I, a i)
    (hne : ∃ i ∈ I, a i % q ≠ 0) :
    3 ≤ ∑ i ∈ I, ((if a i % q ≠ 0 then 1 else 0) + m*(a i%q)/q) := by
  classical
  have hdiv' : q ∣ ∑ i ∈ I, a i % q := by
    rw [Nat.dvd_iff_mod_eq_zero, ← Finset.sum_nat_mod]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hpos : 0 < ∑ i ∈ I, a i % q := by
    obtain ⟨i,hi,hai⟩ := hne
    exact (Nat.pos_of_ne_zero hai).trans_le (Finset.single_le_sum (f := fun i => a i%q) (fun _ _ => Nat.zero_le _) hi)
  have hqsum : q ≤ ∑ i ∈ I, a i % q := Nat.le_of_dvd hpos hdiv'
  have hlt (i : α) (hi : i ∈ I) (ha : a i % q ≠ 0) :
      m*(a i%q) < q*((if a i%q ≠ 0 then 1 else 0)+m*(a i%q)/q) := by
    rw [if_pos ha]
    have hmod := Nat.mod_lt (m*(a i%q)) hq
    have he := Nat.mod_add_div (m*(a i%q)) q
    nlinarith
  have hs := Finset.sum_lt_sum (s := I) (f := fun i => m*(a i%q))
    (g := fun i => q*((if a i%q ≠ 0 then 1 else 0)+m*(a i%q)/q))
    (fun i hi => by
      by_cases ha : a i%q = 0
      · simp [ha]
      · exact (hlt i hi ha).le)
    (by obtain ⟨i,hi,ha⟩ := hne; exact ⟨i,hi,hlt i hi ha⟩)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  nlinarith

lemma factorial_val_three {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (k : ℕ) :
    padicValNat p k.factorial + 3 ≤ max k 3 := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) (Nat.ne_of_gt hk)
  have hvb : 4 * padicValNat p k.factorial < k :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega : 4 ≤ p-1)) h
  by_cases hk3 : k ≤ 3
  · rw [max_eq_right hk3]
    omega
  · rw [max_eq_left (by omega)]
    omega

lemma residue_ne_iff {p : ℕ} [Fact p.Prime] {a e : ℕ} (ha : a ≠ 0) :
    a % p^e ≠ 0 ↔ padicValNat p a < e := by
  rw [ne_eq, ← Nat.dvd_iff_mod_eq_zero, padicValNat_dvd_iff_le ha, not_le]

lemma carry_weight_bound {α : Type*} {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (I : Finset α) (a : α → ℕ) (m r s : ℕ) (hm : 2 ≤ m)
    (ha : ∀ i ∈ I, a i ≠ 0)
    (hv : ∀ i ∈ I, s ≤ padicValNat p (a i) ∧ padicValNat p (a i) < r)
    (hmin : ∃ i ∈ I, padicValNat p (a i) = s)
    (hdiv : p^r ∣ ∑ i ∈ I, a i) :
    3*((r:ℤ)-s) + padicValNat p I.card.factorial ≤
      ∑ i ∈ I, ((r:ℤ)-padicValNat p (a i)+padicValRat p (C m (a i))) := by
  classical
  have hsr : s < r := by obtain ⟨i,hi,he⟩ := hmin; have := hv i hi; omega
  let es := Finset.Ico (s+1) (r+1)
  let w (e : ℕ) := ∑ i ∈ I, ((if padicValNat p (a i) < e then 1 else 0)+m*(a i%p^e)/p^e)
  have heq (i : α) (hi : i ∈ I) :
      (∑ e ∈ es, (if padicValNat p (a i) < e then (1:ℤ) else 0)) = (r:ℤ)-padicValNat p (a i) := by
    have hset : es.filter (fun e => padicValNat p (a i) < e) =
        Finset.Ico (padicValNat p (a i)+1) (r+1) := by
      ext e
      simp only [es, Finset.mem_filter, Finset.mem_Ico]
      have := hv i hi
      omega
    rw [Finset.sum_boole, hset]
    simp only [Nat.card_Ico, Nat.add_sub_add_right]
    rw [Nat.cast_sub (Nat.le_of_lt (hv i hi).2)]
  have hsum : (∑ e ∈ es, (w e:ℤ)) ≤
      ∑ i ∈ I, ((r:ℤ)-padicValNat p (a i)+padicValRat p (C m (a i))) := by
    simp only [w, Nat.cast_sum, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.sum_add_distrib, heq i hi]
    exact add_le_add (le_refl _) (C_val_bound (p := p) m (a i) s r)
  have hw (e : ℕ) (he : e ∈ es) : 3 ≤ w e := by
    have he' : s+1 ≤ e ∧ e < r+1 := Finset.mem_Ico.mp he
    have hqd : p^e ∣ ∑ i ∈ I, a i :=
      (pow_dvd_pow p (by omega : e ≤ r)).trans hdiv
    have hn : ∃ i ∈ I, a i%p^e ≠ 0 := by
      obtain ⟨i,hi,heq⟩ := hmin
      exact ⟨i,hi,(residue_ne_iff (ha i hi)).mpr (by omega)⟩
    have h := residue_carry I a (p^e) m (pow_pos hp.out.pos _) hm hqd hn
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [residue_ne_iff (ha i hi)]
  have hwr : I.card ≤ w r := by
    change I.card ≤ ∑ i ∈ I, ((if padicValNat p (a i) < r then 1 else 0)+m*(a i%p^r)/p^r)
    calc
      I.card = ∑ i ∈ I, (1:ℕ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [if_pos (hv i hi).2]
        exact Nat.le_add_right _ _
  have hrmem : r ∈ es := by simp only [es, Finset.mem_Ico]; omega
  have hlow : (∑ e ∈ es, ((3:ℤ)+(if e=r then (padicValNat p I.card.factorial:ℤ) else 0))) ≤
      ∑ e ∈ es, (w e:ℤ) := by
    apply Finset.sum_le_sum
    intro e he
    by_cases her : e = r
    · subst e
      rw [if_pos rfl]
      have h := (factorial_val_three hp5 I.card).trans (max_le hwr (hw r hrmem))
      omega
    · rw [if_neg her, add_zero]
      exact_mod_cast hw e he
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite_eq', if_pos hrmem] at hlow
  have hcard : es.card = r-s := by simp [es, Nat.card_Ico]
  rw [hcard, Nat.cast_sub (by omega)] at hlow
  have h := hlow.trans hsum
  nlinarith

lemma V.prod_sub_prod_weighted {α : Type*} {p : ℕ} [Fact p.Prime]
    (I : Finset α) (f g : α → ℚ) (w : α → ℤ) (t : ℤ)
    (hf : ∀ i ∈ I, V p (w i) (f i)) (hg : ∀ i ∈ I, V p (w i) (g i))
    (hd : ∀ i ∈ I, V p (w i+t) (f i-g i)) :
    V p ((∑ i ∈ I, w i)+t) ((∏ i ∈ I, f i)-(∏ i ∈ I, g i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact V.zero _ _
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have he : f i*(∏ j ∈ I, f j)-g i*(∏ j ∈ I, g j) =
        (f i-g i)*(∏ j ∈ I, f j)+g i*((∏ j ∈ I, f j)-(∏ j ∈ I, g j)) := by ring
    rw [he]
    apply V.add
    · have h := (hd i (Finset.mem_insert_self _ _)).mul
        (V.prod I f w (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      convert h using 1 <;> ring
    · have h := (hg i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hd j (Finset.mem_insert_of_mem hj)))
      convert h using 1 <;> ring

namespace Series
open PowerSeries
local notation "PS" => PowerSeries ℚ

noncomputable def lowF (m n p r : ℕ) : PS := PowerSeries.mk fun j =>
  if p^r ∣ j then 0 else (n*p^r:ℕ)*Super.C m j/(j:ℚ)
noncomputable def lowG (m n p r : ℕ) : PS := PowerSeries.mk fun j =>
  if p^r ∣ j then 0 else if p ∣ j then (n*p^r:ℕ)*Super.C m (j/p)/(j:ℚ) else 0
lemma const_lowF (m n p r : ℕ) : constantCoeff (lowF m n p r) = 0 := by simp [lowF]
lemma const_lowG (m n p r : ℕ) : constantCoeff (lowG m n p r) = 0 := by simp [lowG]

lemma low_bound {p : ℕ} [hp : Fact p.Prime] (m n r j : ℕ) (hj : ¬p^r ∣ j) :
    V p ((r:ℤ)-padicValNat p j+padicValRat p (Super.C m j)) (coeff j (lowF m n p r)) := by
  rw [lowF, coeff_mk, if_neg hj]
  have hN : V p r ((n*p^r:ℕ):ℚ) := by simpa using (V.natCast (p := p) n).mul_p_pow r
  have h := (hN.mul (V.of_le (le_refl (padicValRat p (Super.C m j))))).div
    (Nat.cast_ne_zero.mpr (show j ≠ 0 from fun h => hj (h ▸ dvd_zero _)))
  convert h using 1 <;> simp [padicValRat.of_nat] <;> ring

lemma lowG_bound {p : ℕ} [hp : Fact p.Prime] (m n r j : ℕ) (hj : ¬p^r ∣ j) :
    V p ((r:ℤ)-padicValNat p j+padicValRat p (Super.C m j)) (coeff j (lowG m n p r)) := by
  rw [lowG, coeff_mk, if_neg hj]
  split_ifs with hpj
  · have hj0 : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
    have hN : V p r ((n*p^r:ℕ):ℚ) := by simpa using (V.natCast (p := p) n).mul_p_pow r
    have hc : padicValRat p (Super.C m (j/p)) = padicValRat p (Super.C m j) := by
      rw [← C_scale_val (p := p) m (j/p), Nat.mul_div_cancel' hpj]
    have h := (hN.mul (V.of_le (le_refl (padicValRat p (Super.C m (j/p)))))).div (Nat.cast_ne_zero.mpr hj0)
    convert h using 1 <;> simp [padicValRat.of_nat, hc] <;> ring
  · exact V.zero _ _

lemma low_difference_bound {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (m n r j : ℕ) (hj : ¬p^r ∣ j) :
    V p ((r:ℤ)-padicValNat p j+padicValRat p (Super.C m j)+3*padicValNat p j)
      (coeff j (lowF m n p r)-coeff j (lowG m n p r)) := by
  by_cases hpj : p ∣ j
  · have hj0 : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
    have hvj : 0 < padicValNat p j := one_le_padicValNat_of_dvd hj0 hpj
    have hc := C_super hvj hp5 m (j/p) (by rw [Nat.mul_div_cancel' hpj]; exact pow_padicValNat_dvd)
    rw [Nat.mul_div_cancel' hpj] at hc
    have hval : padicValRat p (Super.C m (j/p)) = padicValRat p (Super.C m j) := by
      rw [← C_scale_val (p := p) m (j/p), Nat.mul_div_cancel' hpj]
    rw [hval] at hc
    have hN : V p r ((n*p^r:ℕ):ℚ) := by simpa using (V.natCast (p := p) n).mul_p_pow r
    have h := (hN.mul hc).div (Nat.cast_ne_zero.mpr hj0)
    simp only [lowF, lowG, coeff_mk, if_neg hj, if_pos hpj]
    convert h using 1
    · simp only [padicValRat.of_nat]; ring
    · ring
  · have hvj : padicValNat p j = 0 := padicValNat.eq_zero_of_not_dvd hpj
    have h := low_bound m n r j hj
    simpa [lowG, hj, hpj, hvj] using h

lemma low_local {p : ℕ} [hp : Fact p.Prime] (m n r : ℕ) : SV p 1 (lowF m n p r) := by
  intro j
  by_cases hj : p^r ∣ j
  · simp [lowF, hj]; exact V.zero _ _
  · have hj0 : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
    have hvj : padicValNat p j < r := by simpa [padicValNat_dvd_iff_le hj0] using hj
    have hc := (C_integral (p := p) m j).resolve_left (C_ne m j)
    exact (low_bound m n r j hj).mono (by omega)

lemma low_power_cong {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (m n r M k : ℕ) (hm : 2 ≤ m) (hM : p^r ∣ M) :
    V p (3*r) ((coeff M ((lowF m n p r)^k)-coeff M ((lowG m n p r)^k))/(k.factorial:ℚ)) := by
  classical
  rcases k.eq_zero_or_pos with rfl | hk
  · simp only [pow_zero, sub_self, zero_div]; exact V.zero _ _
  rw [coeff_pow, coeff_pow, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply V.sum
  intro a ha
  have hasum : ∑ i ∈ Finset.range k, a i = M := (Finset.mem_finsuppAntidiag.mp ha).1
  by_cases hgood : ∀ i ∈ Finset.range k, ¬ p^r ∣ a i
  · have ha0 : ∀ i ∈ Finset.range k, a i ≠ 0 := fun i hi h => hgood i hi (h ▸ dvd_zero _)
    obtain ⟨i0,hi0,hmin⟩ := Finset.exists_min_image (Finset.range k) (fun i => padicValNat p (a i))
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hk))
    let s := padicValNat p (a i0)
    let w (i : ℕ) : ℤ := (r:ℤ)-padicValNat p (a i)+padicValRat p (Super.C m (a i))
    have hv (i : ℕ) (hi : i ∈ Finset.range k) : s ≤ padicValNat p (a i) ∧ padicValNat p (a i) < r := by
      refine ⟨hmin i hi, ?_⟩
      simpa [padicValNat_dvd_iff_le (ha0 i hi)] using hgood i hi
    have hcarry := carry_weight_bound hp5 (Finset.range k) a m r s hm ha0 hv ⟨i0,hi0,rfl⟩
      (by rw [hasum]; exact hM)
    simp only [Finset.card_range] at hcarry
    have hprod := V.prod_sub_prod_weighted (Finset.range k)
      (fun i => coeff (a i) (lowF m n p r)) (fun i => coeff (a i) (lowG m n p r)) w (3*s)
      (fun i hi => low_bound m n r (a i) (hgood i hi))
      (fun i hi => lowG_bound m n r (a i) (hgood i hi))
      (fun i hi => (low_difference_bound hp5 m n r (a i) (hgood i hi)).mono (by
        dsimp [w]; have := hv i hi; omega))
    have h := hprod.div (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
    apply h.mono
    rw [padicValRat.of_nat]
    dsimp [w]
    nlinarith
  · push_neg at hgood
    obtain ⟨i,hi,hdiv⟩ := hgood
    have hf : coeff (a i) (lowF m n p r) = 0 := by simp [lowF, hdiv]
    have hg : coeff (a i) (lowG m n p r) = 0 := by simp [lowG, hdiv]
    rw [Finset.prod_eq_zero hi hf, Finset.prod_eq_zero hi hg, sub_self, zero_div]
    exact V.zero _ _

lemma low_exp_cong {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (m n r M : ℕ) (hm : 2 ≤ m) (hM : p^r ∣ M) :
    V p (3*r) (coeff M (E (lowF m n p r))-coeff M (E (lowG m n p r))) := by
  rw [coeff_E, coeff_E, ← Finset.sum_sub_distrib]
  apply V.sum
  intro k _
  convert low_power_cong hp5 m n r M k hm hM using 1 <;> ring

lemma E_cong {p : ℕ} [Fact p.Prime] {k : ℤ} (hk : 1 ≤ k) {f g : PS}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hlocal : SV p 0 (E g)) (hdelta : SV p k (f-g)) : SV p k (E f-E g) := by
  have h := hlocal.mul (hdelta.E_sub_one hk)
  rw [E_sub hf hg]
  convert h using 1 <;> simp [mul_sub]

lemma high_log_cong {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (m n t : ℕ) :
    SV p (3*(t+1)) (L m (p^(t+1)) n - L m (p^t) n) := by
  intro j
  rw [map_sub, coeff_L, coeff_L]
  rcases j.eq_zero_or_pos with rfl | hj
  · simp only [Nat.cast_zero, div_zero, sub_self]; exact V.zero _ _
  have hd : p^(t+1+padicValNat p j) ∣ p*(p^t*j) := by
    have h := Nat.mul_dvd_mul_left (p^(t+1)) (pow_padicValNat_dvd (p := p) (n := j))
    rw [pow_add] at h
    convert h using 1 <;> simp [pow_succ] <;> ring
  have h := C_super (by omega : 0 < t+1+padicValNat p j) hp5 m (p^t*j) hd
  have hc := ((V.natCast (p := p) n).mul_left h).div (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hj))
  have hv := (C_integral (p := p) m (p^t*j)).resolve_left (C_ne _ _)
  have hc' := hc.mono (show (3:ℤ)*(t+1) ≤ 3*(t+1+padicValNat p j)+padicValRat p (Super.C m (p^t*j))-padicValRat p (j:ℚ) by
    simp only [padicValRat.of_nat]; omega)
  convert hc' using 1
  · push_cast; ring

lemma L_splitF {p : ℕ} [hp : Fact p.Prime] (m n r : ℕ) :
    L m 1 (n*p^r) = expand (p^r) (pow_ne_zero _ hp.out.ne_zero) (L m (p^r) n) + lowF m n p r := by
  ext j
  rw [map_add]
  by_cases hj : p^r ∣ j
  · obtain ⟨k,rfl⟩ := hj
    simp only [coeff_L, one_mul, coeff_expand_mul, lowF, coeff_mk, dvd_mul_right, if_true, add_zero]
    rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · push_cast
      field_simp [Nat.cast_ne_zero.mpr hp.out.ne_zero]
  · simp [coeff_L, lowF, coeff_expand, hj]

lemma L_splitG {p : ℕ} [hp : Fact p.Prime] (m n t : ℕ) :
    expand p hp.out.ne_zero (L m 1 (n*p^t)) =
      expand (p^(t+1)) (pow_ne_zero _ hp.out.ne_zero) (L m (p^t) n) + lowG m n p (t+1) := by
  ext j
  rw [map_add]
  by_cases hj : p^(t+1) ∣ j
  · obtain ⟨k,rfl⟩ := hj
    have hd : p ∣ p^(t+1)*k := dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
    rw [coeff_expand, if_pos hd, coeff_expand_mul]
    simp only [coeff_L, one_mul, lowG, coeff_mk, dvd_mul_right, if_true, add_zero]
    have he : p^(t+1)*k/p = p^t*k := by
      rw [show p^(t+1)*k = p*(p^t*k) by rw [pow_succ]; ring, Nat.mul_div_right _ hp.out.pos]
    rw [he]
    rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · push_cast
      field_simp [Nat.cast_ne_zero.mpr hp.out.ne_zero]
  · rw [coeff_expand_of_not_dvd _ _ _ hj]
    rw [coeff_expand]
    simp only [lowG, coeff_mk, if_neg hj, zero_add]
    split_ifs with hpj
    · obtain ⟨k,rfl⟩ := hpj
      rw [Nat.mul_div_right _ hp.out.pos, coeff_L, one_mul]
      have hk : k ≠ 0 := fun h => hj (by simp [h])
      push_cast
      rw [pow_succ]
      field_simp [Nat.cast_ne_zero.mpr hp.out.ne_zero]
    · rfl

lemma framed_super_ge_two {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (m n t : ℕ) (hm : 2 ≤ m) :
    V p (3*(t+1)) (coeff (n*p^(t+1)) (E (L m 1 (n*p^(t+1))))-
      coeff (n*p^t) (E (L m 1 (n*p^t)))) := by
  let q := p^(t+1)
  have hq0 : q ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  let F := expand q hq0 (E (L m q n))
  let G := expand q hq0 (E (L m (p^t) n))
  let U := E (lowF m n p (t+1))
  let W := E (lowG m n p (t+1))
  have hd : SV p (3*(t+1)) (F-G) := by
    have h := (E_cong (by omega : (1:ℤ) ≤ 3*(t+1)) (const_L _ _ _) (const_L _ _ _)
      (E_L_local m (p^t) n) (high_log_cong hp5 m n t)).expand q hq0
    simpa [F, G, map_sub] using h
  have hU : SV p 0 U := (low_local m n (t+1)).E (by norm_num)
  have hG : SV p 0 G := (E_L_local m (p^t) n).expand q hq0
  have hfirst : V p (3*(t+1)) (coeff (n*q) ((F-G)*U)) := by simpa using (hd.mul hU) (n*q)
  have hsecond : V p (3*(t+1)) (coeff (n*q) (G*(U-W))) := by
    rw [coeff_mul]
    apply V.sum
    intro ij hij
    by_cases hqi : q ∣ ij.1
    · have hqj : q ∣ ij.2 := by
        have hnq : q ∣ ij.1+ij.2 := by rw [Finset.mem_antidiagonal.mp hij]; exact dvd_mul_left q n
        exact (Nat.dvd_add_right hqi).mp hnq
      have h := (hG ij.1).mul_left (low_exp_cong hp5 m n (t+1) ij.2 hm hqj)
      simpa [U, W, map_sub] using h
    · have hz : coeff ij.1 G = 0 := coeff_expand_of_not_dvd q hq0 _ hqi
      rw [hz, zero_mul]
      exact V.zero _ _
  have hprod : V p (3*(t+1)) (coeff (n*q) (F*U)-coeff (n*q) (G*W)) := by
    have he : F*U-G*W = (F-G)*U+G*(U-W) := by ring
    rw [← map_sub, he, map_add]
    exact hfirst.add hsecond
  have horig : E (L m 1 (n*q)) = F*U := by
    rw [L_splitF m n (t+1), E_add (by simp [const_L]) (const_lowF _ _ _ _), E_expand _ _ (const_L _ _ _)]
  have hprev : expand p hp.out.ne_zero (E (L m 1 (n*p^t))) = G*W := by
    rw [← E_expand _ _ (const_L _ _ _), L_splitG m n t,
      E_add (by simp [const_L]) (const_lowG _ _ _ _), E_expand _ _ (const_L _ _ _)]
  rw [← horig, ← hprev, show n*q = p*(n*p^t) by dsimp [q]; rw [pow_succ]; ring,
    coeff_expand_mul] at hprod
  convert hprod using 1 <;> congr 2 <;> simp [q, pow_succ] <;> ring

lemma C_one (j : ℕ) : Super.C 1 j = 1 := by
  simp [Super.C, Nat.factorial_ne_zero]
lemma E_L_one_base : E (L 1 1 1) = (PowerSeries.mk 1 : PS) := by
  have hD : PowerSeries.derivative ℚ (L 1 1 1) = (PowerSeries.mk 1 : PS) := by
    ext j
    simp [D_L_coeff, C_one]
  apply ode_unique (h := PowerSeries.mk 1)
  · rw [D_E (const_L _ _ _), hD]
  · ext j
    simp [coeff_derivative, coeff_mul, Finset.Nat.card_antidiagonal]
  · simp [const_E]
lemma E_L_one (n : ℕ) : E (L 1 1 n) = (PowerSeries.mk 1 : PS)^n := by
  have he : L 1 1 n = n • L 1 1 1 := by
    ext j
    rw [map_nsmul]
    simp [coeff_L, C_one, nsmul_eq_mul, div_eq_mul_inv]
  rw [he, E_nsmul (const_L _ _ _), E_L_one_base]
lemma C_two_choose (n : ℕ) : Super.C 2 n = ((2*n).choose n : ℚ) := by
  rw [C_nat, Nat.choose_eq_factorial_div_factorial (by omega)]
  congr 2
  rw [show 2*n-n = n by omega, pow_two]
lemma E_L_one_diagonal (n : ℕ) (hn : 0 < n) :
    coeff n (E (L 1 1 n)) = Super.C 2 n/2 := by
  have hpow := PowerSeries.mk_one_pow_eq_mk_choose_add ℚ (n-1)
  rw [Nat.sub_add_cancel hn] at hpow
  rw [E_L_one, hpow, coeff_mk]
  have he : (2*n).choose n = 2*((n-1+n).choose (n-1)) := by
    have h := Nat.choose_succ_succ (n-1+n) (n-1)
    have hn1 : n-1+1 = n := by omega
    have hn2 : n-1+n+1 = 2*n := by omega
    simp only [Nat.succ_eq_add_one, hn1, hn2] at h
    have hs := Nat.choose_symm (show n-1 ≤ n-1+n by omega)
    rw [show n-1+n-(n-1) = n by omega] at hs
    rw [hs] at h
    omega
  rw [C_two_choose, he]
  push_cast
  field_simp

lemma framed_super_one {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (n t : ℕ) (hn : 0 < n) :
    V p (3*(t+1)) (coeff (n*p^(t+1)) (E (L 1 1 (n*p^(t+1))))-
      coeff (n*p^t) (E (L 1 1 (n*p^t)))) := by
  rw [E_L_one_diagonal _ (Nat.mul_pos hn (pow_pos hp.out.pos _)),
    E_L_one_diagonal _ (Nat.mul_pos hn (pow_pos hp.out.pos _)), ← sub_div]
  have hdiv : p^(t+1) ∣ p*(n*p^t) := by
    rw [pow_succ]
    have h := dvd_mul_left (p^t*p) n
    convert h using 1 <;> ring
  have h := C_super (by omega : 0 < t+1) hp5 2 (n*p^t) hdiv
  have hv := (C_integral (p := p) 2 (n*p^t)).resolve_left (C_ne _ _)
  have hh := (h.mono (show (3:ℤ)*(t+1) ≤ 3*(t+1)+padicValRat p (Super.C 2 (n*p^t)) by omega)).div_unit
    (by norm_num : (2:ℚ) ≠ 0) (val_nat_unit (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)))
  convert hh using 1
  · push_cast; ring
end Series
end Super


open Nat BigOperators Int

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

/--
A generalized recursive definition for the coefficients of any exponential series $\exp(\sum d_k \frac{x^k}{k})$.
The coefficients $a_k$ satisfy $k \cdot a_k = \sum_{j=1}^k d_j \cdot a_{k-j}$.
This is a local helper function inside `b_m_int`.
-/
noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

/--
The sequence $b_m(n)$ is defined by $b_m(n) := [x^n] A_m(x)^n$ for $n \ge 1$.
We define $b_m(n)$ as the $n$-th coefficient of the series $\exp(L_{m,n}(x))$, where the driving coefficients are $d_k = n \cdot c_m(k)$.
Since this sequence is in $\mathbb{N}$, we define it in $\mathbb{Z}$ for the congruence.
-/
noncomputable def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0 -- Not in the domain of the conjecture, but required for total function.
  else
    let d (k : ℕ) : ℕ := n * coeff_of_log_gf_gen m k
    (generalized_exp_coeff d n : ℤ)

namespace Super
open PowerSeries
open Series

lemma generalized_eq_series (m n k : ℕ) :
    (generalized_exp_coeff (fun j => n * coeff_of_log_gf_gen m j) k : ℚ) =
      coeff k (E (L m 1 n)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [generalized_exp_coeff]
      simpa using (const_E (L m 1 n)).symm
    | succ k =>
      rw [generalized_exp_coeff]
      let S : ℕ := ∑ j ∈ Finset.range (k+1), (n * coeff_of_log_gf_gen m (j+1)) *
        generalized_exp_coeff (fun j => n * coeff_of_log_gf_gen m j) (k+1-(j+1))
      change (S / (k+1) : ℕ) = (coeff (k+1) (E (L m 1 n)) : ℚ)
      have hs : (S:ℚ) = (k+1:ℚ)*coeff (k+1) (E (L m 1 n)) := by
        dsimp [S]
        rw [Nat.cast_sum]
        calc
          _ = ∑ j ∈ Finset.range (k+1), (n:ℚ)*Super.C m (j+1)*coeff (k+1-(j+1)) (E (L m 1 n)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Nat.cast_mul, ih (k+1-(j+1)) (by omega), Nat.cast_mul]
            rw [show (coeff_of_log_gf_gen m (j+1):ℚ) = Super.C m (j+1) from (C_nat m (j+1)).symm]
          _ = _ := by simpa only [one_mul] using (E_L_rec m 1 n k).symm
      obtain ⟨z,hz⟩ := E_L_integral m 1 n (k+1)
      have he : (S:ℤ) = (k+1:ℤ)*z := by
        apply Int.cast_injective (α := ℚ)
        push_cast
        rw [hz]
        exact hs
      have hd : k+1 ∣ S := Int.ofNat_dvd.mp ⟨z, by simpa using he⟩
      rw [Nat.cast_div_charZero hd, hs]
      push_cast
      field_simp

lemma b_eq_series (m n : ℕ) (hn : n ≠ 0) :
    (b_m_int m n : ℚ) = coeff n (E (L m 1 n)) := by
  simp only [b_m_int, if_neg hn, Int.cast_natCast]
  exact generalized_eq_series m n n
end Super

/--
oeis_333042_conjecture_1:
More generally, for a positive integer $m$, set $A_m(x) = \exp( \sum_{n \ge 1} (m*n)!/(n!^m) * x^n/n )$
and define a sequence $\{b_m(n): n \ge 1\}$ by $b_m(n) := [x^n] A_m(x)^n$.
Then we conjecture that $b_m(n)$ is an integer sequence satisfying the supercongruences
$b_m(n p^r) \equiv b_m(n p^{r-1}) \pmod{p^{3r}}$ for prime $p \ge 5$ and all positive integers $m, n, r$.
-/
theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] :=
by
  letI : Fact p.Prime := ⟨hp⟩
  cases r with
  | zero => omega
  | succ t =>
    have h : Super.V p (3*(t+1))
        (PowerSeries.coeff (n*p^(t+1)) (Super.Series.E (Super.Series.L m 1 (n*p^(t+1)))) -
          PowerSeries.coeff (n*p^t) (Super.Series.E (Super.Series.L m 1 (n*p^t)))) := by
      by_cases hm1 : m = 1
      · subst m
        exact Super.Series.framed_super_one hp5 n t (by omega)
      · exact Super.Series.framed_super_ge_two hp5 m n t (by omega)
    rw [← Super.b_eq_series m (n*p^(t+1)) (Nat.ne_of_gt (Nat.mul_pos (by omega) (pow_pos hp.pos _))),
      ← Super.b_eq_series m (n*p^t) (Nat.ne_of_gt (Nat.mul_pos (by omega) (pow_pos hp.pos _)))] at h
    have hd : (p:ℤ)^(3*(t+1)) ∣ b_m_int m (n*p^(t+1))-b_m_int m (n*p^t) := by
      apply (Super.V.intCast_iff (p := p) (3*(t+1)) _).mp
      simpa only [Int.cast_sub, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h
    simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one] using (Int.modEq_iff_dvd.mpr hd).symm


theorem general_supercongruence_conjecture.disproof : ¬ (type_of% @general_supercongruence_conjecture) := sorry
