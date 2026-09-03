import Submission.ReturnDisplacementObstruction

/-! Uniform recurrence and highly divisible return displacements are compatible.
This explicit bounded-step path is not claimed to satisfy admissibility or
Gaussian primality; it tests only a possible recurrence-based shortcut. -/
namespace Erdos952Investigation
namespace RecurrenceDivisibilityCountermodel

open RecurrentIncrementObstruction
set_option maxHeartbeats 0

lemma exists_factorial_not_dvd (n : ℕ) : ∃ k : ℕ, ¬ k.factorial ∣ n+1 := by
  refine ⟨n+4,?_⟩
  intro h
  have hle := Nat.le_of_dvd (by omega : 0 < n+1) h
  have hlt := Nat.lt_factorial_self (by omega : 3 ≤ n+4)
  omega

/-- The first factorial which fails to divide n+1. -/
def level (n : ℕ) : ℕ := Nat.find (exists_factorial_not_dvd n)

def colour (n : ℕ) : ℤ := (level n % 2 : ℕ)

lemma level_eq_iff (n k : ℕ) : level n = k ↔
    ¬ k.factorial ∣ n+1 ∧ ∀ j < k, j.factorial ∣ n+1 := by
  simp only [level,Nat.find_eq_iff,not_not]

lemma level_le (n : ℕ) : level n ≤ n+4 := by
  apply Nat.find_min'
  intro h
  have hle := Nat.le_of_dvd (by omega : 0 < n+1) h
  have hlt := Nat.lt_factorial_self (by omega : 3 ≤ n+4)
  omega

lemma level_add_period (n q : ℕ) (hq : (level n).factorial ∣ q) :
    level (n+q) = level n := by
  apply (level_eq_iff _ _).mpr
  have hn := (level_eq_iff n (level n)).mp rfl
  constructor
  · intro h
    apply hn.1
    have hh : (level n).factorial ∣ n+1+q := by convert h using 1; omega
    exact (Nat.dvd_add_left hq).mp hh
  · intro j hj
    have hqd := (Nat.factorial_dvd_factorial hj.le).trans hq
    have hh := Nat.dvd_add (hn.2 j hj) hqd
    convert hh using 1; omega

lemma level_factorial_pred (k : ℕ) (hk : 2 ≤ k) :
    level (k.factorial-1) = k+1 := by
  apply (level_eq_iff _ _).mpr
  have hpos := Nat.factorial_pos k
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k.factorial)]
  constructor
  · intro h
    have hl := Nat.le_of_dvd hpos h
    rw [Nat.factorial_succ] at hl
    nlinarith
  · intro j hj
    exact Nat.factorial_dvd_factorial (by omega)

lemma colour_zero : colour 0 = 0 := by
  have hlevel : level 0 = 2 := by
    apply (level_eq_iff _ _).mpr
    constructor
    · norm_num
    · intro j hj
      interval_cases j <;> norm_num
  simp [colour,hlevel]

lemma colour_one : colour 1 = 1 := by
  have hlevel : level 1 = 3 := by
    apply (level_eq_iff _ _).mpr
    constructor
    · norm_num
    · intro j hj
      interval_cases j <;> norm_num
  simp [colour,hlevel]

lemma colour_bounds (n : ℕ) : 0 ≤ colour n ∧ colour n ≤ 1 := by
  have hh := Nat.mod_lt (level n) (by decide : 0 < 2)
  dsimp [colour]
  omega

/-- Every finite prefix repeats at every multiple of a suitable factorial. -/
lemma colour_prefix_periodic (L : ℕ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ t i : ℕ, i ≤ L → colour (Q*t+i) = colour i := by
  refine ⟨(L+4).factorial,Nat.factorial_pos _,?_⟩
  intro t i hi
  have hd : (level i).factorial ∣ (L+4).factorial*t :=
    dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial ((level_le i).trans (by omega))) t
  have hh := level_add_period i ((L+4).factorial*t) hd
  have he : (L+4).factorial*t+i = i+(L+4).factorial*t := by omega
  simp only [colour,he,hh]

/-- Conversely, matching a sufficiently long prefix detects divisibility of
the shift by any prescribed factorial. -/
lemma colour_return_divisible (S n : ℕ)
    (hreturn : ∀ i < S.factorial+2, colour (n+i) = colour i) :
    S.factorial ∣ n := by
  by_contra hn
  have hbad : ∃ j : ℕ, ¬ j.factorial ∣ n := ⟨S,hn⟩
  let j := Nat.find hbad
  have hj : ¬ j.factorial ∣ n := Nat.find_spec hbad
  have hjS : j ≤ S := Nat.find_min' hbad hn
  have hjmin (k : ℕ) (hk : k < j) : k.factorial ∣ n := by
    exact not_not.mp (Nat.find_min hbad hk)
  have hj2 : 2 ≤ j := by
    by_contra hh
    have hsmall : j = 0 ∨ j = 1 := by omega
    rcases hsmall with he | he <;> simp [he] at hj
  let i := j.factorial-1
  have hipos := Nat.factorial_pos j
  have hi : i+1 = j.factorial := by dsimp [i]; omega
  have hlevel : level (n+i) = j := by
    apply (level_eq_iff _ _).mpr
    rw [Nat.add_assoc,hi]
    constructor
    · exact fun hh => hj ((Nat.dvd_add_left (dvd_refl j.factorial)).mp hh)
    · intro k hk
      exact Nat.dvd_add (hjmin k hk) (Nat.factorial_dvd_factorial hk.le)
  have hiL : i < S.factorial+2 := by
    have hh := Nat.factorial_le hjS
    dsimp [i]
    omega
  have hc := hreturn i hiL
  rw [colour,colour,hlevel,level_factorial_pred j hj2] at hc
  omega

/-- A walk in a strip of width one, with increments in a fixed finite set. -/
def walk (n : ℕ) : GaussianInt := ⟨n,colour n⟩

lemma walk_injective : Function.Injective walk := by
  intro i j he
  exact Int.natCast_inj.mp (congrArg Zsqrtd.re he)

lemma walk_step_bound (n : ℕ) : (walk (n+1)-walk n).norm < 3 := by
  have hn := colour_bounds n
  have hn1 := colour_bounds (n+1)
  have hcases : colour n = 0 ∨ colour n = 1 := by omega
  have hcases1 : colour (n+1) = 0 ∨ colour (n+1) = 1 := by omega
  rcases hcases with h | h <;> rcases hcases1 with h' | h' <;>
    norm_num [walk,gaussian_norm_sq,h,h']

lemma increment_prefix_periodic (L : ℕ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ t i : ℕ, i < L →
      walk (Q*t+i+1)-walk (Q*t+i) = walk (i+1)-walk i := by
  obtain ⟨Q,hQ,hperiod⟩ := colour_prefix_periodic (L+1)
  refine ⟨Q,hQ,?_⟩
  intro t i hi
  apply Zsqrtd.ext
  · simp [walk]
  · change colour (Q*t+i+1)-colour (Q*t+i) = colour (i+1)-colour i
    rw [Nat.add_assoc,hperiod t (i+1) (by omega),hperiod t i (by omega)]

/-- Uniform recurrence means bounded gaps between occurrences of each prefix.
It does not impose a common bound for prefixes of different lengths. -/
def UniformlyRecurrentIncrements (x : ℕ → GaussianInt) : Prop :=
  ∀ L : ℕ, ∃ R : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ n ≤ N+R ∧
    ∀ i < L, x (n+i+1)-x (n+i) = x (i+1)-x i

lemma walk_uniformly_recurrent : UniformlyRecurrentIncrements walk := by
  intro L
  obtain ⟨Q,hQ,hperiod⟩ := increment_prefix_periodic L
  refine ⟨Q,?_⟩
  intro N
  refine ⟨Q*(N/Q+1),?_,?_,hperiod (N/Q+1)⟩
  · have he := Nat.mod_add_div N Q
    have hm := Nat.mod_lt N hQ
    rw [Nat.mul_add,Nat.mul_one]
    omega
  · have he := Nat.mod_add_div N Q
    rw [Nat.mul_add,Nat.mul_one]
    omega

lemma walk_return_divisible (S : ℕ) : ∃ L : ℕ, ∀ n : ℕ,
    (∀ i < L, walk (n+i+1)-walk (n+i) = walk (i+1)-walk i) →
    (S.factorial : ℤ) ∣ (walk n-walk 0).re ∧
      (S.factorial : ℤ) ∣ (walk n-walk 0).im := by
  refine ⟨S.factorial+2,?_⟩
  intro n hreturn
  have hform := block_position_formula walk n (S.factorial+2) hreturn
  have hfirst := congrArg Zsqrtd.im (hform 1 (by omega))
  change colour (n+1) = colour n+(colour 1-colour 0) at hfirst
  rw [colour_zero,colour_one] at hfirst
  have hcn : colour n = 0 := by
    have hn := colour_bounds n
    have hn1 := colour_bounds (n+1)
    omega
  have hc (i : ℕ) (hi : i < S.factorial+2) : colour (n+i) = colour i := by
    have hh := congrArg Zsqrtd.im (hform i hi.le)
    change colour (n+i) = colour n+(colour i-colour 0) at hh
    simpa only [hcn,colour_zero,zero_add,sub_zero] using hh
  have hd := colour_return_divisible S n hc
  constructor
  · simpa [walk] using (show (S.factorial : ℤ) ∣ (n : ℤ) by exact_mod_cast hd)
  · simp [walk,hcn,colour_zero]

/-- This satisfies uniform recurrence and factorial divisibility of long
returns simultaneously. It is not a counterexample to the conjecture. -/
theorem recurrence_divisibility_counterexample :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm < 3) ∧ UniformlyRecurrentIncrements x ∧
      ∀ S : ℕ, ∃ L : ℕ, ∀ n : ℕ,
        (∀ i < L, x (n+i+1)-x (n+i) = x (i+1)-x i) →
        (S.factorial : ℤ) ∣ (x n-x 0).re ∧
          (S.factorial : ℤ) ∣ (x n-x 0).im := by
  exact ⟨walk,walk_injective,walk_step_bound,walk_uniformly_recurrent,walk_return_divisible⟩

lemma colour_even (n : ℕ) : colour (2*n) = 0 := by
  have hlevel : level (2*n) = 2 := by
    apply (level_eq_iff _ _).mpr
    constructor
    · norm_num only [Nat.factorial_succ,Nat.factorial_zero] at *
      omega
    · intro j hj
      interval_cases j <;> simp
  simp [colour,hlevel]

/-- The walk fails a single split-prime admissibility test. The countermodel
therefore cannot be mistaken for an admissible ray or a prime ray. -/
theorem walk_not_admissible_mod_five :
    ¬ ∃ a b : ZMod 5, ∀ n, AdmissibleRay.Good 5 a b (walk n) := by
  have hbad : ∀ a b : ZMod 5, ∃ n : Fin 5,
      (a+(2*n.val : ℕ))^2+b^2 = 0 := by decide +kernel
  rintro ⟨a,b,hab⟩
  obtain ⟨n,hn⟩ := hbad a b
  have hh := hab (2*n.val)
  apply hh
  simpa only [AdmissibleRay.Good,walk,colour_even,
    Int.cast_natCast,Int.cast_zero,add_zero] using hn

/-- Uniform recurrence promotes an eventual period to a period of the whole
increment word; it does not itself assert that any period exists. -/
lemma uniform_recurrence_promotes_period (x : ℕ → GaussianInt)
    (hr : UniformlyRecurrentIncrements x) (N k : ℕ)
    (hp : ∀ n ≥ N, x (n+k+1)-x (n+k) = x (n+1)-x n) :
    ∀ i : ℕ, x (i+k+1)-x (i+k) = x (i+1)-x i := by
  intro i
  obtain ⟨R,hR⟩ := hr (i+k+1)
  obtain ⟨n,hn,hnR,hmatch⟩ := hR N
  have hleft := hmatch (i+k) (by omega)
  have hright := hmatch i (by omega)
  have hmid := hp (n+i) (by omega)
  rw [Nat.add_assoc n i k] at hmid
  exact hleft.symm.trans (hmid.trans hright)

/-- Periodic repetition of every finite prefix is compatible with an
increment word that is not eventually periodic. Hence compactness cannot
supply the periodicity required by the arithmetic progression obstruction. -/
theorem walk_increments_not_eventually_periodic (N k : ℕ) (hk : 0 < k) :
    ¬ ∀ n ≥ N, walk (n+k+1)-walk (n+k) = walk (n+1)-walk n := by
  intro hp
  have hperiod := uniform_recurrence_promotes_period walk walk_uniformly_recurrent N k hp
  obtain ⟨L,hL⟩ := walk_return_divisible (k+4)
  have hm : ∀ i < L, walk (k+i+1)-walk (k+i) = walk (i+1)-walk i := by
    intro i hi
    simpa only [Nat.add_comm k i] using hperiod i
  have hd := (hL k hm).1
  have hdn : (k+4).factorial ∣ k := by
    apply Int.natCast_dvd_natCast.mp
    simpa [walk] using hd
  have hle := Nat.le_of_dvd hk hdn
  have hlt := Nat.lt_factorial_self (by omega : 3 ≤ k+4)
  omega

#print axioms walk_increments_not_eventually_periodic

#print axioms walk_not_admissible_mod_five

#print axioms colour_return_divisible
#print axioms recurrence_divisibility_counterexample

end RecurrenceDivisibilityCountermodel
end Erdos952Investigation
