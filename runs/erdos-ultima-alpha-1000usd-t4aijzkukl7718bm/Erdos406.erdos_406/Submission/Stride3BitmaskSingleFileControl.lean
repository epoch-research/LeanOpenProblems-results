import FormalConjecturesUtil

/-! Self-contained conditional backward-simulation criterion. No certificate witness. -/
namespace Erdos406BackwardStandalone

def evalNat {σ : Type*} (D : DFA ℕ σ) (n : ℕ) : σ :=
  D.eval (Nat.digits 3 n).reverse

lemma evalNat_zero {σ : Type*} (D : DFA ℕ σ) : evalNat D 0 = D.start := by
  simp [evalNat]

lemma evalNat_pos {σ : Type*} (D : DFA ℕ σ) {n : ℕ} (hn : 0 < n) :
    evalNat D n = D.step (evalNat D (n / 3)) (n % 3) := by
  rw [evalNat, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn,
    List.reverse_cons, DFA.eval_append_singleton]
  rfl

lemma affine_div_mod (q n c : ℕ) :
    (q * n + c) / 3 = q * (n / 3) + (q * (n % 3) + c) / 3 ∧
    (q * n + c) % 3 = (q * (n % 3) + c) % 3 := by
  have he : q * n + c = q * (n % 3) + c + 3 * (q * (n / 3)) := by
    calc
      _ = q * (n % 3 + 3 * (n / 3)) + c := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [he, Nat.add_mul_div_left _ _ (by decide), Nat.add_mul_mod_self_left]
  exact ⟨by omega, rfl⟩

lemma even_exponent {k : ℕ} (h : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) : Even k := by
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by positivity : 0 < 2 ^ k)] at h
  have hm : 2 ^ k % 3 = 0 ∨ 2 ^ k % 3 = 1 := by
    simpa using h (List.mem_cons_self ..)
  rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
  · exact he
  · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at hm

theorem finite_of_backward (E : ℕ) (Q : ℕ → Prop)
    (hseed : ¬ Q (4 ^ E))
    (hback : ∀ n, Q (4 * n) → Q n)
    (hcover : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have htail : ∀ j : ℕ, ¬ Q (4 ^ (E + j)) := by
    intro j
    induction j with
    | zero => simpa using hseed
    | succ j ih =>
      intro hq
      apply ih
      apply hback
      simpa only [Nat.add_succ, pow_succ'] using hq
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨4 ^ E, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hg⟩
  obtain ⟨m, hm⟩ := even_exponent hg
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hg ⊢
  by_cases hEm : E ≤ m
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hEm
    exact False.elim (htail j (hcover _ (by positivity) hg))
  · exact Nat.pow_le_pow_right (by decide) (by omega)

def acceptsNat {σ : Type*} (M : NFA ℕ σ) (n : ℕ) : Prop :=
  ∃ q ∈ evalNat M.toDFA n, q ∈ M.accept

lemma good_state_reachable {σ : Type*} (M : NFA ℕ σ) (g : σ)
    (hfirst : g ∈ M.stepSet M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ M.step g d)
    (n : ℕ) (hn : 0 < n) (hgood : Nat.digits 3 n ⊆ [0, 1]) :
    g ∈ evalNat M.toDFA n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd : n % 3 ≤ 1 := by
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn] at hgood
      have hm := hgood (List.mem_cons_self ..)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    by_cases hsmall : n < 3
    · rw [Nat.mod_eq_of_lt hsmall] at hd
      have he : n = 1 := by omega
      subst n
      rw [evalNat_pos M.toDFA (by decide : 0 < (1 : ℕ))]
      change g ∈ M.stepSet (evalNat M.toDFA 0) 1
      rw [evalNat_zero]
      exact hfirst
    · have hnq : 0 < n / 3 := by omega
      have hlt : n / 3 < n := Nat.div_lt_self hn (by decide)
      have hgq : Nat.digits 3 (n / 3) ⊆ [0, 1] := by
        intro d hmem
        apply hgood
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn]
        exact List.mem_cons_of_mem _ hmem
      rw [evalNat_pos M.toDFA hn]
      exact NFA.mem_stepSet.mpr ⟨g, ih (n / 3) hlt hnq hgq, hloop _ (by omega)⟩

lemma covers_positive_good {σ : Type*} (M : NFA ℕ σ) (g : σ)
    (hfirst : g ∈ M.stepSet M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ M.step g d)
    (haccept : g ∈ M.accept) (n : ℕ) (hn : 0 < n)
    (hgood : Nat.digits 3 n ⊆ [0, 1]) : acceptsNat M n :=
  ⟨g, good_state_reachable M g hfirst hloop n hn hgood, haccept⟩

structure Simulation (σ : Type*) where
  M : NFA ℕ σ
  R : σ → σ → ℕ → Prop
  initial : ∀ c, c < 4 → ∀ p ∈ evalNat M.toDFA c, ∃ q ∈ M.start, R p q c
  step : ∀ p q c d e c' r,
    c < 4 → d < 3 → e < 3 → c' < 4 → 4 * d + c' = 3 * c + e →
    R p q c → r ∈ M.step p e → ∃ s ∈ M.step q d, R r s c'
  finish : ∀ p q, R p q 0 → p ∈ M.accept → q ∈ M.accept

namespace Simulation
variable {σ : Type*} (C : Simulation σ)

/-- Match an arbitrary output state, not just an accepting one. -/
theorem match_output : ∀ n c, c < 4 → ∀ p ∈ evalNat C.M.toDFA (4 * n + c),
    ∃ q ∈ evalNat C.M.toDFA n, C.R p q c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c hc p hp
    by_cases hn : n = 0
    · subst n
      simp only [mul_zero, zero_add] at hp
      obtain ⟨q, hq, hr⟩ := C.initial c hc p hp
      exact ⟨q, by simpa only [evalNat_zero, NFA.toDFA] using hq, hr⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let d := n % 3
      let a := (4 * d + c) / 3
      let e := (4 * d + c) % 3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have ha : a < 4 := by dsimp [a]; omega
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcarry : 4 * d + c = 3 * a + e := by
        dsimp [a, e]
        omega
      have hdiv : (4 * n + c) / 3 = 4 * (n / 3) + a :=
        (affine_div_mod 4 n c).1
      have hmod : (4 * n + c) % 3 = e := (affine_div_mod 4 n c).2
      rw [evalNat_pos C.M.toDFA (by omega : 0 < 4 * n + c), hdiv, hmod] at hp
      obtain ⟨r, hr, hrp⟩ := NFA.mem_stepSet.mp hp
      obtain ⟨q, hq, hrq⟩ := ih (n / 3) (Nat.div_lt_self hnpos (by decide)) a ha r hr
      obtain ⟨s, hqs, hps⟩ := C.step r q a d e c p ha hd he hc hcarry hrq hrp
      refine ⟨s, ?_, hps⟩
      rw [evalNat_pos C.M.toDFA hnpos]
      exact NFA.mem_stepSet.mpr ⟨q, hq, hqs⟩

theorem backward (n : ℕ) : acceptsNat C.M (4 * n) → acceptsNat C.M n := by
  rintro ⟨p, hp, hpa⟩
  obtain ⟨q, hq, hpq⟩ := C.match_output n 0 (by decide) p (by simpa using hp)
  exact ⟨q, hq, C.finish p q hpq hpa⟩

/-- A checked simulation and rejected seed would settle the conjecture.
Their existence is not asserted by this theorem. -/
theorem finite_of_cover (g : σ)
    (hfirst : g ∈ C.M.stepSet C.M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ C.M.step g d)
    (haccept : g ∈ C.M.accept) (E : ℕ)
    (hseed : ¬ acceptsNat C.M (4 ^ E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  exact finite_of_backward E (acceptsNat C.M)
    hseed (fun n => C.backward n) (covers_positive_good C.M g hfirst hloop haccept)

end Simulation
variable {σ : Type*} [DecidableEq σ]

structure Data (σ : Type*) [DecidableEq σ] where
  step : σ → ℕ → Finset σ
  start : Finset σ
  accept : Finset σ
  relation : σ → ℕ → Finset σ

namespace Data
variable (D : Data σ)

def toNFA : NFA ℕ σ where
  step q d := D.step q d
  start := D.start
  accept := D.accept

def stepStates (U : Finset σ) (d : ℕ) : Finset σ := U.biUnion (fun q => D.step q d)

def evalStates (n : ℕ) : Finset σ :=
  (Nat.digits 3 n).reverse.foldl D.stepStates D.start

lemma stepStates_coe (U : Finset σ) (d : ℕ) :
    (D.stepStates U d : Set σ) = D.toNFA.stepSet U d := by
  ext r
  simp [stepStates, NFA.mem_stepSet, toNFA]

lemma evalFrom_coe (w : List ℕ) (U : Finset σ) :
    ((w.foldl D.stepStates U : Finset σ) : Set σ) = D.toNFA.evalFrom U w := by
  induction w generalizing U with
  | nil => rfl
  | cons d w ih =>
    rw [List.foldl_cons, NFA.evalFrom_cons, ih, stepStates_coe]

lemma evalStates_coe (n : ℕ) :
    (D.evalStates n : Set σ) = evalNat D.toNFA.toDFA n := by
  exact D.evalFrom_coe (Nat.digits 3 n).reverse D.start

def toSimulation
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p c, c < 4 → ∀ q ∈ D.relation p c,
      ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 →
      4 * d + c' = 3 * c + e → ∀ r ∈ D.step p e,
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept) : Simulation σ where
  M := D.toNFA
  R p q c := q ∈ D.relation p c
  initial := by
    intro c hc p hp
    rw [← D.evalStates_coe] at hp
    obtain ⟨q, hq⟩ := hinit c hc p hp
    exact ⟨q, (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
  step := by
    intro p q c d e c' r hc hd he hc' hcarry hpq hr
    obtain ⟨s, hs⟩ := hstep p c hc q hpq d hd e he c' hc' hcarry r hr
    exact ⟨s, (Finset.mem_inter.mp hs).1, (Finset.mem_inter.mp hs).2⟩
  finish := by
    intro p q hpq hp
    exact hfinish p hp hpq

/-- A finite simulation, a good-digit state, and a rejected actual seed
would imply exactly the conjecture. All hypotheses remain explicit. -/
theorem finite_of_checks
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p c, c < 4 → ∀ q ∈ D.relation p c,
      ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 →
      4 * d + c' = 3 * c + e → ∀ r ∈ D.step p e,
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept)
    (g : σ) (hfirst : g ∈ D.stepStates D.start 1)
    (hloop : ∀ d, d < 2 → g ∈ D.step g d)
    (haccept : g ∈ D.accept) (E : ℕ)
    (hseed : Disjoint (D.evalStates (4 ^ E)) D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let C := D.toSimulation hinit hstep hfinish
  refine C.finite_of_cover g ?_ hloop haccept E ?_
  · change g ∈ D.toNFA.stepSet (D.start : Set σ) 1
    rw [← D.stepStates_coe]
    exact hfirst
  · rintro ⟨p, hp, hpa⟩
    change p ∈ evalNat D.toNFA.toDFA (4 ^ E) at hp
    rw [← D.evalStates_coe] at hp
    exact Finset.disjoint_left.mp hseed hp hpa

/-- The carry equation determines the old carry and output digit. This form
avoids checking the numerous impossible carry tuples in concrete data. -/
def toSimulation_fast
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p d, d < 3 → ∀ c', c' < 4 →
      ∀ r ∈ D.step p ((4 * d + c') % 3),
      ∀ q ∈ D.relation p ((4 * d + c') / 3),
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept) : Simulation σ :=
  D.toSimulation hinit (by
    intro p c hc q hpq d hd e he c' hc' hcarry r hr
    have hv : (4 * d + c') / 3 = c := by omega
    have hm : (4 * d + c') % 3 = e := by omega
    refine hstep p d hd c' hc' r ?_ q ?_
    · simpa only [hm] using hr
    · simpa only [hv] using hpq) hfinish

theorem finite_of_fast_checks
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p d, d < 3 → ∀ c', c' < 4 →
      ∀ r ∈ D.step p ((4 * d + c') % 3),
      ∀ q ∈ D.relation p ((4 * d + c') / 3),
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept)
    (g : σ) (hfirst : g ∈ D.stepStates D.start 1)
    (hloop : ∀ d, d < 2 → g ∈ D.step g d)
    (haccept : g ∈ D.accept) (E : ℕ)
    (hseed : Disjoint (D.evalStates (4 ^ E)) D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let C := D.toSimulation_fast hinit hstep hfinish
  refine C.finite_of_cover g ?_ hloop haccept E ?_
  · change g ∈ D.toNFA.stepSet (D.start : Set σ) 1
    rw [← D.stepStates_coe]
    exact hfirst
  · rintro ⟨p, hp, hpa⟩
    change p ∈ evalNat D.toNFA.toDFA (4 ^ E) at hp
    rw [← D.evalStates_coe] at hp
    exact Finset.disjoint_left.mp hseed hp hpa

end Data

#print axioms Data.finite_of_fast_checks
end Erdos406BackwardStandalone


/-! Strided backward NFA simulations. The covering automaton may be different
for each exponent residue class. No rejected-seed certificate is supplied. -/
namespace Erdos406BackwardStrided
open Erdos406BackwardStandalone

theorem finite_of_backward_family (s E : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → Prop)
    (hseed : ∀ r, r < s → ¬ Q r (4 ^ (E + r)))
    (hback : ∀ r, r < s → ∀ n, Q r (4 ^ s * n) → Q r n)
    (hcover : ∀ r, r < s → ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q r n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have htail : ∀ r, r < s → ∀ j : ℕ, ¬ Q r (4 ^ (E + r + s * j)) := by
    intro r hr j
    induction j with
    | zero => simpa using hseed r hr
    | succ j ih =>
      intro hq
      apply ih
      apply hback r hr
      have he : E + r + s * (j + 1) = s + (E + r + s * j) := by ring
      simpa only [he, pow_add] using hq
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨4 ^ E, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hg⟩
  obtain ⟨m, hm⟩ := even_exponent hg
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hg ⊢
  by_cases hEm : E ≤ m
  · have hr : (m - E) % s < s := Nat.mod_lt _ hs
    have heq : E + (m - E) % s + s * ((m - E) / s) = m := by
      have hdiv := Nat.mod_add_div (m - E) s
      omega
    apply False.elim
    apply htail ((m - E) % s) hr ((m - E) / s)
    rw [heq]
    exact hcover _ hr _ (by positivity) hg
  · exact Nat.pow_le_pow_right (by decide) (by omega)

theorem finite_of_backward_pair (E : ℕ) (Q₀ Q₁ : ℕ → Prop)
    (hseed₀ : ¬ Q₀ (4 ^ E)) (hseed₁ : ¬ Q₁ (4 ^ (E + 1)))
    (hback₀ : ∀ n, Q₀ (16 * n) → Q₀ n)
    (hback₁ : ∀ n, Q₁ (16 * n) → Q₁ n)
    (hcover₀ : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q₀ n)
    (hcover₁ : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q₁ n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply finite_of_backward_family 2 E (by decide) (fun r => if r = 0 then Q₀ else Q₁)
  · intro r hr
    interval_cases r <;> simpa using (by first | exact hseed₀ | exact hseed₁)
  · intro r hr
    interval_cases r <;> simpa using (by first | exact hback₀ | exact hback₁)
  · intro r hr
    interval_cases r <;> simpa using (by first | exact hcover₀ | exact hcover₁)

structure Simulation (σ : Type*) (K : ℕ) where
  factor_pos : 0 < K
  M : NFA ℕ σ
  R : σ → σ → ℕ → Prop
  initial : ∀ c, c < K → ∀ p ∈ evalNat M.toDFA c, ∃ q ∈ M.start, R p q c
  step : ∀ p q c d e c' r,
    c < K → d < 3 → e < 3 → c' < K → K * d + c' = 3 * c + e →
    R p q c → r ∈ M.step p e → ∃ t ∈ M.step q d, R r t c'
  finish : ∀ p q, R p q 0 → p ∈ M.accept → q ∈ M.accept

namespace Simulation
variable {σ : Type*} {K : ℕ} (C : Simulation σ K)

theorem match_output : ∀ n c, c < K → ∀ p ∈ evalNat C.M.toDFA (K * n + c),
    ∃ q ∈ evalNat C.M.toDFA n, C.R p q c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c hc p hp
    by_cases hn : n = 0
    · subst n
      simp only [mul_zero, zero_add] at hp
      obtain ⟨q, hq, hr⟩ := C.initial c hc p hp
      exact ⟨q, by simpa only [evalNat_zero, NFA.toDFA] using hq, hr⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hK := C.factor_pos
      let d := n % 3
      let a := (K * d + c) / 3
      let e := (K * d + c) % 3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have ha : a < K := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
        nlinarith
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcarry : K * d + c = 3 * a + e := by dsimp [a, e]; omega
      have hdiv : (K * n + c) / 3 = K * (n / 3) + a := (affine_div_mod K n c).1
      have hmod : (K * n + c) % 3 = e := (affine_div_mod K n c).2
      rw [evalNat_pos C.M.toDFA (by positivity : 0 < K * n + c), hdiv, hmod] at hp
      obtain ⟨r, hr, hrp⟩ := NFA.mem_stepSet.mp hp
      obtain ⟨q, hq, hrq⟩ := ih (n / 3) (Nat.div_lt_self hnpos (by decide)) a ha r hr
      obtain ⟨t, hqt, hpt⟩ := C.step r q a d e c p ha hd he hc hcarry hrq hrp
      refine ⟨t, ?_, hpt⟩
      rw [evalNat_pos C.M.toDFA hnpos]
      exact NFA.mem_stepSet.mpr ⟨q, hq, hqt⟩

theorem backward (n : ℕ) : acceptsNat C.M (K * n) → acceptsNat C.M n := by
  rintro ⟨p, hp, hpa⟩
  obtain ⟨q, hq, hpq⟩ := C.match_output n 0 C.factor_pos p (by simpa using hp)
  exact ⟨q, hq, C.finish p q hpq hpa⟩

theorem rejects_mul_orbit (x : ℕ) (hseed : ¬ acceptsNat C.M x) (j : ℕ) :
    ¬ acceptsNat C.M (K ^ j * x) := by
  induction j with
  | zero => simpa using hseed
  | succ j ih =>
    intro hq
    apply ih
    apply C.backward
    simpa only [pow_succ', mul_assoc] using hq

end Simulation

variable {σ : Type*} [DecidableEq σ]
/-- Finite data use the same evaluation interface as one-step simulations. -/
def checkedSimulation (D : Data σ) (K : ℕ) (hK : 0 < K)
    (hinit : ∀ c, c < K → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p d, d < 3 → ∀ c', c' < K →
      ∀ r ∈ D.step p ((K * d + c') % 3),
      ∀ q ∈ D.relation p ((K * d + c') / 3),
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept) : Simulation σ K where
  factor_pos := hK
  M := D.toNFA
  R p q c := q ∈ D.relation p c
  initial := by
    intro c hc p hp
    rw [← D.evalStates_coe] at hp
    obtain ⟨q, hq⟩ := hinit c hc p hp
    exact ⟨q, (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
  step := by
    intro p q c d e c' r hc hd he hc' hcarry hpq hr
    have hv : (K * d + c') / 3 = c := by omega
    have hm : (K * d + c') % 3 = e := by omega
    obtain ⟨t, ht⟩ := hstep p d hd c' hc' r (by simpa only [hm] using hr)
      q (by simpa only [hv] using hpq)
    exact ⟨t, (Finset.mem_inter.mp ht).1, (Finset.mem_inter.mp ht).2⟩
  finish := by
    intro p q hpq hp
    exact hfinish p hp hpq

#print axioms finite_of_backward_family
#print axioms finite_of_backward_pair
#print axioms Simulation.match_output
#print axioms checkedSimulation
end Erdos406BackwardStrided


/-! Bitmask checks for strided simulations. This file supplies no missing-class witness. -/
namespace Erdos406BackwardBitmask
open Erdos406BackwardStandalone Erdos406BackwardStrided

def maskSet (N m : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun q => m.testBit q.val)

@[simp] lemma mem_maskSet {N m : ℕ} {q : Fin N} :
    q ∈ maskSet N m ↔ m.testBit q.val = true := by
  simp [maskSet]

lemma land_nonempty {N a b : ℕ} (ha : a < 2 ^ N) (hab : a &&& b ≠ 0) :
    (maskSet N a ∩ maskSet N b).Nonempty := by
  by_contra h
  apply hab
  apply Nat.zero_of_testBit_eq_false
  intro i
  by_cases hi : i < N
  · have hn : ¬ ((a &&& b).testBit i = true) := by
      intro ht
      rw [Nat.testBit_land, Bool.and_eq_true] at ht
      apply h
      exact ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨mem_maskSet.mpr ht.1, mem_maskSet.mpr ht.2⟩⟩
    exact Bool.eq_false_iff.mpr hn
  · have hai : a < 2 ^ i := ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_eq_false_of_lt hai]

def allBelow (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).all f

lemma allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true)
    {i : ℕ} (hi : i < n) : f i = true := by
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

lemma allBelow_of_forall {n : ℕ} {f : ℕ → Bool}
    (h : ∀ i, i < n → f i = true) : allBelow n f = true := by
  exact List.all_eq_true.mpr (fun i hi => h i (List.mem_range.mp hi))

lemma allBelow_succ_intro {n : ℕ} {f : ℕ → Bool}
    (h : allBelow n f = true) (hn : f n = true) : allBelow (n + 1) f = true := by
  simp only [allBelow, List.range_succ, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]
  change (allBelow n f && f n) = true
  rw [h, hn]
  rfl

def rawStepCell (N K : ℕ) (T R : ℕ → ℕ → ℕ) (p d c' : ℕ) : Bool :=
  decide (R p ((K * d + c') / 3) = 0) ||
    allBelow N fun r => !(T p ((K * d + c') % 3)).testBit r ||
      allBelow N fun q => !(R p ((K * d + c') / 3)).testBit q ||
        decide (T q d &&& R r c' ≠ 0)

def rawStepRow (N K : ℕ) (T R : ℕ → ℕ → ℕ) (p : ℕ) : Bool :=
  allBelow 3 fun d => allBelow K fun c' => rawStepCell N K T R p d c'

lemma rawStepRow_of_cells {N K : ℕ} {T R : ℕ → ℕ → ℕ} {p : ℕ}
    (h : ∀ d, d < 3 → ∀ c', c' < K → rawStepCell N K T R p d c' = true) :
    rawStepRow N K T R p = true := by
  exact allBelow_of_forall (fun d hd => allBelow_of_forall (h d hd))

lemma rawStepRow_sound {N K : ℕ} {T R : ℕ → ℕ → ℕ}
    (hbound : ∀ q d, q < N → d < 3 → T q d < 2 ^ N)
    {p : Fin N} (h : rawStepRow N K T R p = true)
    (d : ℕ) (hd : d < 3) (c' : ℕ) (hc' : c' < K)
    (r : Fin N) (hr : r ∈ maskSet N (T p ((K * d + c') % 3)))
    (q : Fin N) (hq : q ∈ maskSet N (R p ((K * d + c') / 3))) :
    (maskSet N (T q d) ∩ maskSet N (R r c')).Nonempty := by
  have hh := allBelow_spec (allBelow_spec h hd) hc'
  unfold rawStepCell at hh
  have hR : R p ((K * d + c') / 3) ≠ 0 := by
    intro hz
    have hb := mem_maskSet.mp hq
    simp [hz] at hb
  have hh' : allBelow N (fun r => !(T p ((K * d + c') % 3)).testBit r ||
      allBelow N (fun q => !(R p ((K * d + c') / 3)).testBit q ||
        decide (T q d &&& R r c' ≠ 0))) = true := by
    simpa only [decide_eq_false hR, Bool.false_or] using hh
  have h₁ := allBelow_spec hh' r.isLt
  have h₂ : allBelow N (fun q => !(R p ((K * d + c') / 3)).testBit q ||
      decide (T q d &&& R r c' ≠ 0)) = true := by
    simpa only [mem_maskSet.mp hr, Bool.not_true, Bool.false_or] using h₁
  have h₃ := allBelow_spec h₂ q.isLt
  have hne : T q d &&& R r c' ≠ 0 := by
    simpa only [mem_maskSet.mp hq, Bool.not_true, Bool.false_or, decide_eq_true_eq] using h₃
  exact land_nonempty (hbound q d q.isLt hd) hne


def stepMaskList (T : ℕ → ℕ → ℕ) (U d : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun q V => if U.testBit q then T q d ||| V else V) 0

lemma stepMaskList_spec (T : ℕ → ℕ → ℕ) (U d r : ℕ) (l : List ℕ) :
    (stepMaskList T U d l).testBit r = true ↔
      ∃ q ∈ l, U.testBit q = true ∧ (T q d).testBit r = true := by
  induction l with
  | nil => simp [stepMaskList]
  | cons a l ih =>
    simp only [stepMaskList, List.foldr_cons]
    split <;> rename_i h
    · simp only [Nat.testBit_lor, Bool.or_eq_true]
      change ((T a d).testBit r = true ∨ (stepMaskList T U d l).testBit r = true) ↔ _
      rw [ih]
      simp [h]
    · change (stepMaskList T U d l).testBit r = true ↔ _
      rw [ih]
      simp [h]

def stepMask (N : ℕ) (T : ℕ → ℕ → ℕ) (U d : ℕ) : ℕ :=
  stepMaskList T U d (List.range N)

def fromMasks (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A : ℕ) : Data (Fin N) where
  step p d := maskSet N (T p d)
  start := maskSet N S
  accept := maskSet N A
  relation p c := maskSet N (R p c)

lemma stepStates_maskSet (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A U d : ℕ) :
    (fromMasks N T R S A).stepStates (maskSet N U) d =
      maskSet N (stepMask N T U d) := by
  ext r
  simp only [Data.stepStates, Finset.mem_biUnion, mem_maskSet,
    fromMasks, stepMask, stepMaskList_spec, List.mem_range]
  constructor
  · rintro ⟨q, hq, hr⟩
    exact ⟨q.val, q.isLt, hq, hr⟩
  · rintro ⟨q, hq, hu, ht⟩
    exact ⟨⟨q, hq⟩, hu, ht⟩

def evalMask (N : ℕ) (T : ℕ → ℕ → ℕ) (S n : ℕ) : ℕ :=
  (Nat.digits 3 n).reverse.foldl (stepMask N T) S

lemma foldl_maskSet (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A U : ℕ) (w : List ℕ) :
    w.foldl (fromMasks N T R S A).stepStates (maskSet N U) =
      maskSet N (w.foldl (stepMask N T) U) := by
  induction w generalizing U with
  | nil => rfl
  | cons d w ih =>
    simp only [List.foldl_cons, stepStates_maskSet, ih]

lemma evalStates_maskSet (N : ℕ) (T R : ℕ → ℕ → ℕ) (S A n : ℕ) :
    (fromMasks N T R S A).evalStates n = maskSet N (evalMask N T S n) := by
  exact foldl_maskSet N T R S A S (Nat.digits 3 n).reverse

def rawInitRow (N : ℕ) (T R : ℕ → ℕ → ℕ) (S c : ℕ) : Bool :=
  allBelow N fun p => !(evalMask N T S c).testBit p || decide (S &&& R p c ≠ 0)

lemma rawInitRow_sound {N : ℕ} {T R : ℕ → ℕ → ℕ} {S A c : ℕ}
    (hS : S < 2 ^ N) (h : rawInitRow N T R S c = true) :
    ∀ p ∈ (fromMasks N T R S A).evalStates c,
      ((fromMasks N T R S A).start ∩ (fromMasks N T R S A).relation p c).Nonempty := by
  intro p hp
  rw [evalStates_maskSet, mem_maskSet] at hp
  have hh := allBelow_spec h p.isLt
  have hne : S &&& R p c ≠ 0 := by
    simpa only [hp, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
  exact land_nonempty hS hne

lemma land_disjoint {N a b : ℕ} (h : a &&& b = 0) :
    Disjoint (maskSet N a) (maskSet N b) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hx : (a &&& b).testBit p = true := by
    rw [Nat.testBit_land, mem_maskSet.mp hp, mem_maskSet.mp hq]
    rfl
  simp [h] at hx

lemma ldiff_subset {N a b : ℕ} (h : Nat.ldiff a b = 0) :
    maskSet N a ⊆ maskSet N b := by
  intro q hq
  have ht := congrArg (fun n => Nat.testBit n q.val) h
  have ha := mem_maskSet.mp hq
  simp [Nat.testBit_ldiff, ha] at ht
  exact mem_maskSet.mpr ht

def rawFinishRow (A : ℕ) (R : ℕ → ℕ → ℕ) (p : ℕ) : Bool :=
  !A.testBit p || decide (Nat.ldiff (R p 0) A = 0)

lemma rawFinishRow_sound {N A : ℕ} {R : ℕ → ℕ → ℕ} {p : Fin N}
    (h : rawFinishRow A R p = true) (hp : p ∈ maskSet N A) :
    maskSet N (R p 0) ⊆ maskSet N A := by
  have hh : Nat.ldiff (R p 0) A = 0 := by
    simpa only [rawFinishRow, mem_maskSet.mp hp, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] using h
  exact ldiff_subset hh

#print axioms rawStepRow_sound
#print axioms rawInitRow_sound
#print axioms rawFinishRow_sound
#print axioms evalStates_maskSet
end Erdos406BackwardBitmask

namespace Erdos406StandaloneBitmaskControl
open Erdos406BackwardStandalone Erdos406BackwardStrided Erdos406BackwardBitmask
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 20000

def stepRow0 (d : ℕ) : ℕ := if d = 0 then 1 else if d = 1 then 6 else if d = 2 then 8 else 0
def stepRow1 (d : ℕ) : ℕ := if d = 0 then 2 else if d = 1 then 2 else 0
def stepRow2 (d : ℕ) : ℕ := if d = 0 then 4 else if d = 1 then 4 else if d = 2 then 8 else 0
def stepRow3 (d : ℕ) : ℕ := if d = 0 then 4 else if d = 1 then 16 else if d = 2 then 8 else 0
def stepRow4 (d : ℕ) : ℕ := if d = 0 then 4 else if d = 1 then 4 else if d = 2 then 8 else 0
def relationRow0 (c : ℕ) : ℕ := if c = 0 then 29 else if c = 1 then 29 else if c = 2 then 29 else if c = 3 then 29 else if c = 4 then 29 else if c = 5 then 29 else if c = 6 then 29 else if c = 7 then 29 else if c = 8 then 29 else if c = 9 then 29 else if c = 10 then 29 else if c = 11 then 29 else if c = 12 then 29 else if c = 13 then 29 else if c = 14 then 29 else if c = 15 then 29 else if c = 16 then 29 else if c = 17 then 29 else if c = 18 then 29 else if c = 19 then 29 else if c = 20 then 29 else if c = 21 then 21 else if c = 22 then 29 else if c = 23 then 29 else if c = 24 then 29 else if c = 25 then 29 else if c = 26 then 29 else if c = 27 then 29 else if c = 28 then 29 else if c = 29 then 29 else if c = 30 then 29 else if c = 31 then 29 else if c = 32 then 29 else if c = 33 then 29 else if c = 34 then 29 else if c = 35 then 29 else if c = 36 then 29 else if c = 37 then 29 else if c = 38 then 29 else if c = 39 then 29 else if c = 40 then 29 else if c = 41 then 29 else if c = 42 then 29 else if c = 43 then 29 else if c = 44 then 29 else if c = 45 then 29 else if c = 46 then 29 else if c = 47 then 29 else if c = 48 then 29 else if c = 49 then 29 else if c = 50 then 29 else if c = 51 then 29 else if c = 52 then 29 else if c = 53 then 29 else if c = 54 then 29 else if c = 55 then 29 else if c = 56 then 29 else if c = 57 then 29 else if c = 58 then 29 else if c = 59 then 29 else if c = 60 then 29 else if c = 61 then 29 else if c = 62 then 29 else if c = 63 then 29 else 0
def relationRow1 (c : ℕ) : ℕ := if c = 0 then 12 else if c = 1 then 29 else if c = 2 then 29 else if c = 3 then 29 else if c = 4 then 29 else if c = 5 then 29 else if c = 6 then 29 else if c = 7 then 29 else if c = 8 then 29 else if c = 9 then 29 else if c = 10 then 29 else if c = 11 then 29 else if c = 12 then 29 else if c = 13 then 29 else if c = 14 then 29 else if c = 15 then 29 else if c = 16 then 29 else if c = 17 then 29 else if c = 18 then 29 else if c = 19 then 29 else if c = 20 then 29 else if c = 21 then 21 else if c = 22 then 29 else if c = 23 then 29 else if c = 24 then 29 else if c = 25 then 29 else if c = 26 then 29 else if c = 27 then 29 else if c = 28 then 29 else if c = 29 then 29 else if c = 30 then 29 else if c = 31 then 29 else if c = 32 then 29 else if c = 33 then 29 else if c = 34 then 29 else if c = 35 then 29 else if c = 36 then 29 else if c = 37 then 29 else if c = 38 then 29 else if c = 39 then 29 else if c = 40 then 29 else if c = 41 then 29 else if c = 42 then 29 else if c = 43 then 29 else if c = 44 then 29 else if c = 45 then 29 else if c = 46 then 29 else if c = 47 then 29 else if c = 48 then 29 else if c = 49 then 29 else if c = 50 then 29 else if c = 51 then 29 else if c = 52 then 29 else if c = 53 then 29 else if c = 54 then 29 else if c = 55 then 29 else if c = 56 then 29 else if c = 57 then 29 else if c = 58 then 29 else if c = 59 then 29 else if c = 60 then 29 else if c = 61 then 29 else if c = 62 then 29 else if c = 63 then 29 else 0
def relationRow2 (c : ℕ) : ℕ := if c = 0 then 12 else if c = 1 then 29 else if c = 2 then 29 else if c = 3 then 29 else if c = 4 then 29 else if c = 5 then 29 else if c = 6 then 29 else if c = 7 then 29 else if c = 8 then 29 else if c = 9 then 29 else if c = 10 then 29 else if c = 11 then 29 else if c = 12 then 29 else if c = 13 then 29 else if c = 14 then 29 else if c = 15 then 29 else if c = 16 then 29 else if c = 17 then 29 else if c = 18 then 29 else if c = 19 then 29 else if c = 20 then 29 else if c = 21 then 21 else if c = 22 then 29 else if c = 23 then 29 else if c = 24 then 29 else if c = 25 then 29 else if c = 26 then 29 else if c = 27 then 29 else if c = 28 then 29 else if c = 29 then 29 else if c = 30 then 29 else if c = 31 then 29 else if c = 32 then 29 else if c = 33 then 29 else if c = 34 then 29 else if c = 35 then 29 else if c = 36 then 29 else if c = 37 then 29 else if c = 38 then 29 else if c = 39 then 29 else if c = 40 then 29 else if c = 41 then 29 else if c = 42 then 29 else if c = 43 then 29 else if c = 44 then 29 else if c = 45 then 29 else if c = 46 then 29 else if c = 47 then 29 else if c = 48 then 29 else if c = 49 then 29 else if c = 50 then 29 else if c = 51 then 29 else if c = 52 then 29 else if c = 53 then 29 else if c = 54 then 29 else if c = 55 then 29 else if c = 56 then 29 else if c = 57 then 29 else if c = 58 then 29 else if c = 59 then 29 else if c = 60 then 29 else if c = 61 then 29 else if c = 62 then 29 else if c = 63 then 29 else 0
def relationRow3 (c : ℕ) : ℕ := if c = 0 then 12 else if c = 1 then 29 else if c = 2 then 29 else if c = 3 then 29 else if c = 4 then 29 else if c = 5 then 29 else if c = 6 then 29 else if c = 7 then 29 else if c = 8 then 29 else if c = 9 then 29 else if c = 10 then 29 else if c = 11 then 29 else if c = 12 then 29 else if c = 13 then 29 else if c = 14 then 29 else if c = 15 then 29 else if c = 16 then 29 else if c = 17 then 29 else if c = 18 then 29 else if c = 19 then 29 else if c = 20 then 29 else if c = 21 then 29 else if c = 22 then 29 else if c = 23 then 29 else if c = 24 then 29 else if c = 25 then 29 else if c = 26 then 29 else if c = 27 then 29 else if c = 28 then 29 else if c = 29 then 29 else if c = 30 then 29 else if c = 31 then 29 else if c = 32 then 29 else if c = 33 then 29 else if c = 34 then 29 else if c = 35 then 29 else if c = 36 then 29 else if c = 37 then 29 else if c = 38 then 29 else if c = 39 then 29 else if c = 40 then 29 else if c = 41 then 29 else if c = 42 then 29 else if c = 43 then 29 else if c = 44 then 29 else if c = 45 then 29 else if c = 46 then 29 else if c = 47 then 29 else if c = 48 then 29 else if c = 49 then 29 else if c = 50 then 29 else if c = 51 then 29 else if c = 52 then 29 else if c = 53 then 29 else if c = 54 then 29 else if c = 55 then 29 else if c = 56 then 29 else if c = 57 then 29 else if c = 58 then 29 else if c = 59 then 29 else if c = 60 then 29 else if c = 61 then 29 else if c = 62 then 29 else if c = 63 then 29 else 0
def relationRow4 (c : ℕ) : ℕ := if c = 0 then 28 else if c = 1 then 29 else if c = 2 then 29 else if c = 3 then 29 else if c = 4 then 29 else if c = 5 then 29 else if c = 6 then 29 else if c = 7 then 29 else if c = 8 then 29 else if c = 9 then 29 else if c = 10 then 29 else if c = 11 then 29 else if c = 12 then 29 else if c = 13 then 29 else if c = 14 then 29 else if c = 15 then 29 else if c = 16 then 29 else if c = 17 then 29 else if c = 18 then 29 else if c = 19 then 29 else if c = 20 then 29 else if c = 21 then 21 else if c = 22 then 29 else if c = 23 then 29 else if c = 24 then 29 else if c = 25 then 29 else if c = 26 then 29 else if c = 27 then 29 else if c = 28 then 29 else if c = 29 then 29 else if c = 30 then 29 else if c = 31 then 29 else if c = 32 then 29 else if c = 33 then 29 else if c = 34 then 29 else if c = 35 then 29 else if c = 36 then 29 else if c = 37 then 29 else if c = 38 then 29 else if c = 39 then 29 else if c = 40 then 29 else if c = 41 then 29 else if c = 42 then 29 else if c = 43 then 29 else if c = 44 then 29 else if c = 45 then 29 else if c = 46 then 29 else if c = 47 then 29 else if c = 48 then 29 else if c = 49 then 29 else if c = 50 then 29 else if c = 51 then 29 else if c = 52 then 29 else if c = 53 then 29 else if c = 54 then 29 else if c = 55 then 29 else if c = 56 then 29 else if c = 57 then 29 else if c = 58 then 29 else if c = 59 then 29 else if c = 60 then 29 else if c = 61 then 29 else if c = 62 then 29 else if c = 63 then 29 else 0
def stepTable : List (ℕ → ℕ) := [stepRow0, stepRow1, stepRow2, stepRow3, stepRow4]
def relationTable : List (ℕ → ℕ) := [relationRow0, relationRow1, relationRow2, relationRow3, relationRow4]
def T (p d : ℕ) : ℕ := (stepTable.getD p (fun _ => 0)) d
def R (p c : ℕ) : ℕ := (relationTable.getD p (fun _ => 0)) c

def data := fromMasks 5 T R 1 14

lemma bound_0 : allBelow 3 (fun d => decide (T 0 d < 2 ^ 5)) = true := by decide +kernel
lemma bound_1 : allBelow 3 (fun d => decide (T 1 d < 2 ^ 5)) = true := by decide +kernel
lemma bound_2 : allBelow 3 (fun d => decide (T 2 d < 2 ^ 5)) = true := by decide +kernel
lemma bound_3 : allBelow 3 (fun d => decide (T 3 d < 2 ^ 5)) = true := by decide +kernel
lemma bound_4 : allBelow 3 (fun d => decide (T 4 d < 2 ^ 5)) = true := by decide +kernel
lemma checked_bound_raw : allBelow 5 (fun q => allBelow 3 (fun d => decide (T q d < 2 ^ 5))) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (fun q => allBelow 3 (fun d => decide (T q d < 2 ^ 5))) = true from rfl)) bound_0) bound_1) bound_2) bound_3) bound_4
lemma checked_bound : ∀ q d, q < 5 → d < 3 → T q d < 2 ^ 5 := by
  intro q d hq hd
  exact of_decide_eq_true (allBelow_spec (allBelow_spec checked_bound_raw hq) hd)
#print axioms checked_bound
lemma eval_step_0 : stepMask 5 T 1 1 = 6 := by decide +kernel
lemma eval_step_1 : stepMask 5 T 1 2 = 8 := by decide +kernel
lemma eval_step_2 : stepMask 5 T 6 0 = 6 := by decide +kernel
lemma eval_step_3 : stepMask 5 T 6 1 = 6 := by decide +kernel
lemma eval_step_4 : stepMask 5 T 6 2 = 8 := by decide +kernel
lemma eval_step_5 : stepMask 5 T 8 0 = 4 := by decide +kernel
lemma eval_step_6 : stepMask 5 T 8 1 = 16 := by decide +kernel
lemma eval_step_7 : stepMask 5 T 8 2 = 8 := by decide +kernel
lemma eval_step_8 : stepMask 5 T 4 0 = 4 := by decide +kernel
lemma eval_step_9 : stepMask 5 T 4 1 = 4 := by decide +kernel
lemma eval_step_10 : stepMask 5 T 4 2 = 8 := by decide +kernel
lemma eval_step_11 : stepMask 5 T 16 0 = 4 := by decide +kernel
lemma eval_step_12 : stepMask 5 T 16 1 = 4 := by decide +kernel
lemma eval_step_13 : stepMask 5 T 16 2 = 8 := by decide +kernel
lemma eval_carry_0 : evalMask 5 T 1 0 = 1 := by
  unfold evalMask
  rw [show (Nat.digits 3 0).reverse = [] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil]
lemma eval_carry_1 : evalMask 5 T 1 1 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 1).reverse = [1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0]
lemma eval_carry_2 : evalMask 5 T 1 2 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 2).reverse = [2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1]
lemma eval_carry_3 : evalMask 5 T 1 3 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 3).reverse = [1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2]
lemma eval_carry_4 : evalMask 5 T 1 4 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 4).reverse = [1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3]
lemma eval_carry_5 : evalMask 5 T 1 5 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 5).reverse = [1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4]
lemma eval_carry_6 : evalMask 5 T 1 6 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 6).reverse = [2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5]
lemma eval_carry_7 : evalMask 5 T 1 7 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 7).reverse = [2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_6]
lemma eval_carry_8 : evalMask 5 T 1 8 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 8).reverse = [2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_7]
lemma eval_carry_9 : evalMask 5 T 1 9 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 9).reverse = [1, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2]
lemma eval_carry_10 : evalMask 5 T 1 10 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 10).reverse = [1, 0, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_3]
lemma eval_carry_11 : evalMask 5 T 1 11 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 11).reverse = [1, 0, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_4]
lemma eval_carry_12 : evalMask 5 T 1 12 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 12).reverse = [1, 1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_2]
lemma eval_carry_13 : evalMask 5 T 1 13 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 13).reverse = [1, 1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3]
lemma eval_carry_14 : evalMask 5 T 1 14 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 14).reverse = [1, 1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_4]
lemma eval_carry_15 : evalMask 5 T 1 15 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 15).reverse = [1, 2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_5]
lemma eval_carry_16 : evalMask 5 T 1 16 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 16).reverse = [1, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_6]
lemma eval_carry_17 : evalMask 5 T 1 17 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 17).reverse = [1, 2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_7]
lemma eval_carry_18 : evalMask 5 T 1 18 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 18).reverse = [2, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_8]
lemma eval_carry_19 : evalMask 5 T 1 19 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 19).reverse = [2, 0, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_9]
lemma eval_carry_20 : evalMask 5 T 1 20 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 20).reverse = [2, 0, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_10]
lemma eval_carry_21 : evalMask 5 T 1 21 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 21).reverse = [2, 1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_6, eval_step_11]
lemma eval_carry_22 : evalMask 5 T 1 22 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 22).reverse = [2, 1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_6, eval_step_12]
lemma eval_carry_23 : evalMask 5 T 1 23 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 23).reverse = [2, 1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_6, eval_step_13]
lemma eval_carry_24 : evalMask 5 T 1 24 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 24).reverse = [2, 2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_7, eval_step_5]
lemma eval_carry_25 : evalMask 5 T 1 25 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 25).reverse = [2, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_7, eval_step_6]
lemma eval_carry_26 : evalMask 5 T 1 26 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 26).reverse = [2, 2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_7]
lemma eval_carry_27 : evalMask 5 T 1 27 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 27).reverse = [1, 0, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2]
lemma eval_carry_28 : evalMask 5 T 1 28 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 28).reverse = [1, 0, 0, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_3]
lemma eval_carry_29 : evalMask 5 T 1 29 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 29).reverse = [1, 0, 0, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_4]
lemma eval_carry_30 : evalMask 5 T 1 30 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 30).reverse = [1, 0, 1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_3]
lemma eval_carry_31 : evalMask 5 T 1 31 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 31).reverse = [1, 0, 1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_3]
lemma eval_carry_32 : evalMask 5 T 1 32 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 32).reverse = [1, 0, 1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_3, eval_step_4]
lemma eval_carry_33 : evalMask 5 T 1 33 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 33).reverse = [1, 0, 2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_4, eval_step_5]
lemma eval_carry_34 : evalMask 5 T 1 34 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 34).reverse = [1, 0, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_4, eval_step_6]
lemma eval_carry_35 : evalMask 5 T 1 35 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 35).reverse = [1, 0, 2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_4, eval_step_7]
lemma eval_carry_36 : evalMask 5 T 1 36 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 36).reverse = [1, 1, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_2]
lemma eval_carry_37 : evalMask 5 T 1 37 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 37).reverse = [1, 1, 0, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_2]
lemma eval_carry_38 : evalMask 5 T 1 38 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 38).reverse = [1, 1, 0, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_2, eval_step_4]
lemma eval_carry_39 : evalMask 5 T 1 39 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 39).reverse = [1, 1, 1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_2]
lemma eval_carry_40 : evalMask 5 T 1 40 = 6 := by
  unfold evalMask
  rw [show (Nat.digits 3 40).reverse = [1, 1, 1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3]
lemma eval_carry_41 : evalMask 5 T 1 41 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 41).reverse = [1, 1, 1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_4]
lemma eval_carry_42 : evalMask 5 T 1 42 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 42).reverse = [1, 1, 2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_4, eval_step_5]
lemma eval_carry_43 : evalMask 5 T 1 43 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 43).reverse = [1, 1, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_4, eval_step_6]
lemma eval_carry_44 : evalMask 5 T 1 44 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 44).reverse = [1, 1, 2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_3, eval_step_4, eval_step_7]
lemma eval_carry_45 : evalMask 5 T 1 45 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 45).reverse = [1, 2, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_5, eval_step_8]
lemma eval_carry_46 : evalMask 5 T 1 46 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 46).reverse = [1, 2, 0, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_5, eval_step_9]
lemma eval_carry_47 : evalMask 5 T 1 47 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 47).reverse = [1, 2, 0, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_5, eval_step_10]
lemma eval_carry_48 : evalMask 5 T 1 48 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 48).reverse = [1, 2, 1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_6, eval_step_11]
lemma eval_carry_49 : evalMask 5 T 1 49 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 49).reverse = [1, 2, 1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_6, eval_step_12]
lemma eval_carry_50 : evalMask 5 T 1 50 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 50).reverse = [1, 2, 1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_6, eval_step_13]
lemma eval_carry_51 : evalMask 5 T 1 51 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 51).reverse = [1, 2, 2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_7, eval_step_5]
lemma eval_carry_52 : evalMask 5 T 1 52 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 52).reverse = [1, 2, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_7, eval_step_6]
lemma eval_carry_53 : evalMask 5 T 1 53 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 53).reverse = [1, 2, 2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_4, eval_step_7]
lemma eval_carry_54 : evalMask 5 T 1 54 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 54).reverse = [2, 0, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_8]
lemma eval_carry_55 : evalMask 5 T 1 55 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 55).reverse = [2, 0, 0, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_8, eval_step_9]
lemma eval_carry_56 : evalMask 5 T 1 56 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 56).reverse = [2, 0, 0, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_8, eval_step_10]
lemma eval_carry_57 : evalMask 5 T 1 57 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 57).reverse = [2, 0, 1, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_9, eval_step_8]
lemma eval_carry_58 : evalMask 5 T 1 58 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 58).reverse = [2, 0, 1, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_9]
lemma eval_carry_59 : evalMask 5 T 1 59 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 59).reverse = [2, 0, 1, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_9, eval_step_10]
lemma eval_carry_60 : evalMask 5 T 1 60 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 60).reverse = [2, 0, 2, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_10]
lemma eval_carry_61 : evalMask 5 T 1 61 = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 61).reverse = [2, 0, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_10, eval_step_6]
lemma eval_carry_62 : evalMask 5 T 1 62 = 8 := by
  unfold evalMask
  rw [show (Nat.digits 3 62).reverse = [2, 0, 2, 2] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_5, eval_step_10, eval_step_7]
lemma eval_carry_63 : evalMask 5 T 1 63 = 4 := by
  unfold evalMask
  rw [show (Nat.digits 3 63).reverse = [2, 1, 0, 0] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_1, eval_step_6, eval_step_11, eval_step_8]
lemma eval_seed : evalMask 5 T 1 (4 ^ 8) = 16 := by
  unfold evalMask
  rw [show (Nat.digits 3 (4 ^ 8)).reverse = [1, 0, 0, 2, 2, 2, 2, 0, 0, 2, 1] by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, eval_step_0, eval_step_2, eval_step_4, eval_step_7, eval_step_5, eval_step_8, eval_step_10, eval_step_6]

lemma checked_first : (1 : Fin 5) ∈ data.stepStates data.start 1 := by
  change (1 : Fin 5) ∈ (fromMasks 5 T R 1 14).stepStates (maskSet 5 1) 1
  rw [stepStates_maskSet]
  apply mem_maskSet.mpr
  decide +kernel
lemma checked_loop : ∀ d, d < 2 → (1 : Fin 5) ∈ data.step 1 d := by
  intro d hd
  interval_cases d <;> exact mem_maskSet.mpr (by decide +kernel)
lemma checked_accept : (1 : Fin 5) ∈ data.accept := mem_maskSet.mpr (by decide +kernel)
lemma checked_seed : Disjoint (data.evalStates (4 ^ 8)) data.accept := by
  change Disjoint ((fromMasks 5 T R 1 14).evalStates (4 ^ 8)) (maskSet 5 14)
  rw [evalStates_maskSet, eval_seed]
  apply land_disjoint
  decide +kernel
#print axioms checked_seed
lemma init_0 : rawInitRow 5 T R 1 0 = true := by
  unfold rawInitRow
  rw [eval_carry_0]
  decide +kernel
lemma init_1 : rawInitRow 5 T R 1 1 = true := by
  unfold rawInitRow
  rw [eval_carry_1]
  decide +kernel
lemma init_2 : rawInitRow 5 T R 1 2 = true := by
  unfold rawInitRow
  rw [eval_carry_2]
  decide +kernel
lemma init_3 : rawInitRow 5 T R 1 3 = true := by
  unfold rawInitRow
  rw [eval_carry_3]
  decide +kernel
lemma init_4 : rawInitRow 5 T R 1 4 = true := by
  unfold rawInitRow
  rw [eval_carry_4]
  decide +kernel
lemma init_5 : rawInitRow 5 T R 1 5 = true := by
  unfold rawInitRow
  rw [eval_carry_5]
  decide +kernel
lemma init_6 : rawInitRow 5 T R 1 6 = true := by
  unfold rawInitRow
  rw [eval_carry_6]
  decide +kernel
lemma init_7 : rawInitRow 5 T R 1 7 = true := by
  unfold rawInitRow
  rw [eval_carry_7]
  decide +kernel
lemma init_8 : rawInitRow 5 T R 1 8 = true := by
  unfold rawInitRow
  rw [eval_carry_8]
  decide +kernel
lemma init_9 : rawInitRow 5 T R 1 9 = true := by
  unfold rawInitRow
  rw [eval_carry_9]
  decide +kernel
lemma init_10 : rawInitRow 5 T R 1 10 = true := by
  unfold rawInitRow
  rw [eval_carry_10]
  decide +kernel
lemma init_11 : rawInitRow 5 T R 1 11 = true := by
  unfold rawInitRow
  rw [eval_carry_11]
  decide +kernel
lemma init_12 : rawInitRow 5 T R 1 12 = true := by
  unfold rawInitRow
  rw [eval_carry_12]
  decide +kernel
lemma init_13 : rawInitRow 5 T R 1 13 = true := by
  unfold rawInitRow
  rw [eval_carry_13]
  decide +kernel
lemma init_14 : rawInitRow 5 T R 1 14 = true := by
  unfold rawInitRow
  rw [eval_carry_14]
  decide +kernel
lemma init_15 : rawInitRow 5 T R 1 15 = true := by
  unfold rawInitRow
  rw [eval_carry_15]
  decide +kernel
lemma init_16 : rawInitRow 5 T R 1 16 = true := by
  unfold rawInitRow
  rw [eval_carry_16]
  decide +kernel
lemma init_17 : rawInitRow 5 T R 1 17 = true := by
  unfold rawInitRow
  rw [eval_carry_17]
  decide +kernel
lemma init_18 : rawInitRow 5 T R 1 18 = true := by
  unfold rawInitRow
  rw [eval_carry_18]
  decide +kernel
lemma init_19 : rawInitRow 5 T R 1 19 = true := by
  unfold rawInitRow
  rw [eval_carry_19]
  decide +kernel
lemma init_20 : rawInitRow 5 T R 1 20 = true := by
  unfold rawInitRow
  rw [eval_carry_20]
  decide +kernel
lemma init_21 : rawInitRow 5 T R 1 21 = true := by
  unfold rawInitRow
  rw [eval_carry_21]
  decide +kernel
lemma init_22 : rawInitRow 5 T R 1 22 = true := by
  unfold rawInitRow
  rw [eval_carry_22]
  decide +kernel
lemma init_23 : rawInitRow 5 T R 1 23 = true := by
  unfold rawInitRow
  rw [eval_carry_23]
  decide +kernel
lemma init_24 : rawInitRow 5 T R 1 24 = true := by
  unfold rawInitRow
  rw [eval_carry_24]
  decide +kernel
lemma init_25 : rawInitRow 5 T R 1 25 = true := by
  unfold rawInitRow
  rw [eval_carry_25]
  decide +kernel
lemma init_26 : rawInitRow 5 T R 1 26 = true := by
  unfold rawInitRow
  rw [eval_carry_26]
  decide +kernel
lemma init_27 : rawInitRow 5 T R 1 27 = true := by
  unfold rawInitRow
  rw [eval_carry_27]
  decide +kernel
lemma init_28 : rawInitRow 5 T R 1 28 = true := by
  unfold rawInitRow
  rw [eval_carry_28]
  decide +kernel
lemma init_29 : rawInitRow 5 T R 1 29 = true := by
  unfold rawInitRow
  rw [eval_carry_29]
  decide +kernel
lemma init_30 : rawInitRow 5 T R 1 30 = true := by
  unfold rawInitRow
  rw [eval_carry_30]
  decide +kernel
lemma init_31 : rawInitRow 5 T R 1 31 = true := by
  unfold rawInitRow
  rw [eval_carry_31]
  decide +kernel
lemma init_32 : rawInitRow 5 T R 1 32 = true := by
  unfold rawInitRow
  rw [eval_carry_32]
  decide +kernel
lemma init_33 : rawInitRow 5 T R 1 33 = true := by
  unfold rawInitRow
  rw [eval_carry_33]
  decide +kernel
lemma init_34 : rawInitRow 5 T R 1 34 = true := by
  unfold rawInitRow
  rw [eval_carry_34]
  decide +kernel
lemma init_35 : rawInitRow 5 T R 1 35 = true := by
  unfold rawInitRow
  rw [eval_carry_35]
  decide +kernel
lemma init_36 : rawInitRow 5 T R 1 36 = true := by
  unfold rawInitRow
  rw [eval_carry_36]
  decide +kernel
lemma init_37 : rawInitRow 5 T R 1 37 = true := by
  unfold rawInitRow
  rw [eval_carry_37]
  decide +kernel
lemma init_38 : rawInitRow 5 T R 1 38 = true := by
  unfold rawInitRow
  rw [eval_carry_38]
  decide +kernel
lemma init_39 : rawInitRow 5 T R 1 39 = true := by
  unfold rawInitRow
  rw [eval_carry_39]
  decide +kernel
lemma init_40 : rawInitRow 5 T R 1 40 = true := by
  unfold rawInitRow
  rw [eval_carry_40]
  decide +kernel
lemma init_41 : rawInitRow 5 T R 1 41 = true := by
  unfold rawInitRow
  rw [eval_carry_41]
  decide +kernel
lemma init_42 : rawInitRow 5 T R 1 42 = true := by
  unfold rawInitRow
  rw [eval_carry_42]
  decide +kernel
lemma init_43 : rawInitRow 5 T R 1 43 = true := by
  unfold rawInitRow
  rw [eval_carry_43]
  decide +kernel
lemma init_44 : rawInitRow 5 T R 1 44 = true := by
  unfold rawInitRow
  rw [eval_carry_44]
  decide +kernel
lemma init_45 : rawInitRow 5 T R 1 45 = true := by
  unfold rawInitRow
  rw [eval_carry_45]
  decide +kernel
lemma init_46 : rawInitRow 5 T R 1 46 = true := by
  unfold rawInitRow
  rw [eval_carry_46]
  decide +kernel
lemma init_47 : rawInitRow 5 T R 1 47 = true := by
  unfold rawInitRow
  rw [eval_carry_47]
  decide +kernel
lemma init_48 : rawInitRow 5 T R 1 48 = true := by
  unfold rawInitRow
  rw [eval_carry_48]
  decide +kernel
lemma init_49 : rawInitRow 5 T R 1 49 = true := by
  unfold rawInitRow
  rw [eval_carry_49]
  decide +kernel
lemma init_50 : rawInitRow 5 T R 1 50 = true := by
  unfold rawInitRow
  rw [eval_carry_50]
  decide +kernel
lemma init_51 : rawInitRow 5 T R 1 51 = true := by
  unfold rawInitRow
  rw [eval_carry_51]
  decide +kernel
lemma init_52 : rawInitRow 5 T R 1 52 = true := by
  unfold rawInitRow
  rw [eval_carry_52]
  decide +kernel
lemma init_53 : rawInitRow 5 T R 1 53 = true := by
  unfold rawInitRow
  rw [eval_carry_53]
  decide +kernel
lemma init_54 : rawInitRow 5 T R 1 54 = true := by
  unfold rawInitRow
  rw [eval_carry_54]
  decide +kernel
lemma init_55 : rawInitRow 5 T R 1 55 = true := by
  unfold rawInitRow
  rw [eval_carry_55]
  decide +kernel
lemma init_56 : rawInitRow 5 T R 1 56 = true := by
  unfold rawInitRow
  rw [eval_carry_56]
  decide +kernel
lemma init_57 : rawInitRow 5 T R 1 57 = true := by
  unfold rawInitRow
  rw [eval_carry_57]
  decide +kernel
lemma init_58 : rawInitRow 5 T R 1 58 = true := by
  unfold rawInitRow
  rw [eval_carry_58]
  decide +kernel
lemma init_59 : rawInitRow 5 T R 1 59 = true := by
  unfold rawInitRow
  rw [eval_carry_59]
  decide +kernel
lemma init_60 : rawInitRow 5 T R 1 60 = true := by
  unfold rawInitRow
  rw [eval_carry_60]
  decide +kernel
lemma init_61 : rawInitRow 5 T R 1 61 = true := by
  unfold rawInitRow
  rw [eval_carry_61]
  decide +kernel
lemma init_62 : rawInitRow 5 T R 1 62 = true := by
  unfold rawInitRow
  rw [eval_carry_62]
  decide +kernel
lemma init_63 : rawInitRow 5 T R 1 63 = true := by
  unfold rawInitRow
  rw [eval_carry_63]
  decide +kernel
lemma checked_init_raw : allBelow 64 (rawInitRow 5 T R 1) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawInitRow 5 T R 1) = true from rfl)) init_0) init_1) init_2) init_3) init_4) init_5) init_6) init_7) init_8) init_9) init_10) init_11) init_12) init_13) init_14) init_15) init_16) init_17) init_18) init_19) init_20) init_21) init_22) init_23) init_24) init_25) init_26) init_27) init_28) init_29) init_30) init_31) init_32) init_33) init_34) init_35) init_36) init_37) init_38) init_39) init_40) init_41) init_42) init_43) init_44) init_45) init_46) init_47) init_48) init_49) init_50) init_51) init_52) init_53) init_54) init_55) init_56) init_57) init_58) init_59) init_60) init_61) init_62) init_63
lemma checked_init : ∀ c, c < 64 → ∀ p ∈ data.evalStates c,
    (data.start ∩ data.relation p c).Nonempty := by
  intro c hc
  exact rawInitRow_sound (by decide : (1 : ℕ) < 2 ^ 5) (allBelow_spec checked_init_raw hc)
#print axioms checked_init
lemma cell_0_0_0 : rawStepCell 5 64 T R 0 0 0 = true := by decide +kernel
lemma cell_0_0_1 : rawStepCell 5 64 T R 0 0 1 = true := by decide +kernel
lemma cell_0_0_2 : rawStepCell 5 64 T R 0 0 2 = true := by decide +kernel
lemma cell_0_0_3 : rawStepCell 5 64 T R 0 0 3 = true := by decide +kernel
lemma cell_0_0_4 : rawStepCell 5 64 T R 0 0 4 = true := by decide +kernel
lemma cell_0_0_5 : rawStepCell 5 64 T R 0 0 5 = true := by decide +kernel
lemma cell_0_0_6 : rawStepCell 5 64 T R 0 0 6 = true := by decide +kernel
lemma cell_0_0_7 : rawStepCell 5 64 T R 0 0 7 = true := by decide +kernel
lemma cell_0_0_8 : rawStepCell 5 64 T R 0 0 8 = true := by decide +kernel
lemma cell_0_0_9 : rawStepCell 5 64 T R 0 0 9 = true := by decide +kernel
lemma cell_0_0_10 : rawStepCell 5 64 T R 0 0 10 = true := by decide +kernel
lemma cell_0_0_11 : rawStepCell 5 64 T R 0 0 11 = true := by decide +kernel
lemma cell_0_0_12 : rawStepCell 5 64 T R 0 0 12 = true := by decide +kernel
lemma cell_0_0_13 : rawStepCell 5 64 T R 0 0 13 = true := by decide +kernel
lemma cell_0_0_14 : rawStepCell 5 64 T R 0 0 14 = true := by decide +kernel
lemma cell_0_0_15 : rawStepCell 5 64 T R 0 0 15 = true := by decide +kernel
lemma cell_0_0_16 : rawStepCell 5 64 T R 0 0 16 = true := by decide +kernel
lemma cell_0_0_17 : rawStepCell 5 64 T R 0 0 17 = true := by decide +kernel
lemma cell_0_0_18 : rawStepCell 5 64 T R 0 0 18 = true := by decide +kernel
lemma cell_0_0_19 : rawStepCell 5 64 T R 0 0 19 = true := by decide +kernel
lemma cell_0_0_20 : rawStepCell 5 64 T R 0 0 20 = true := by decide +kernel
lemma cell_0_0_21 : rawStepCell 5 64 T R 0 0 21 = true := by decide +kernel
lemma cell_0_0_22 : rawStepCell 5 64 T R 0 0 22 = true := by decide +kernel
lemma cell_0_0_23 : rawStepCell 5 64 T R 0 0 23 = true := by decide +kernel
lemma cell_0_0_24 : rawStepCell 5 64 T R 0 0 24 = true := by decide +kernel
lemma cell_0_0_25 : rawStepCell 5 64 T R 0 0 25 = true := by decide +kernel
lemma cell_0_0_26 : rawStepCell 5 64 T R 0 0 26 = true := by decide +kernel
lemma cell_0_0_27 : rawStepCell 5 64 T R 0 0 27 = true := by decide +kernel
lemma cell_0_0_28 : rawStepCell 5 64 T R 0 0 28 = true := by decide +kernel
lemma cell_0_0_29 : rawStepCell 5 64 T R 0 0 29 = true := by decide +kernel
lemma cell_0_0_30 : rawStepCell 5 64 T R 0 0 30 = true := by decide +kernel
lemma cell_0_0_31 : rawStepCell 5 64 T R 0 0 31 = true := by decide +kernel
lemma cell_0_0_32 : rawStepCell 5 64 T R 0 0 32 = true := by decide +kernel
lemma cell_0_0_33 : rawStepCell 5 64 T R 0 0 33 = true := by decide +kernel
lemma cell_0_0_34 : rawStepCell 5 64 T R 0 0 34 = true := by decide +kernel
lemma cell_0_0_35 : rawStepCell 5 64 T R 0 0 35 = true := by decide +kernel
lemma cell_0_0_36 : rawStepCell 5 64 T R 0 0 36 = true := by decide +kernel
lemma cell_0_0_37 : rawStepCell 5 64 T R 0 0 37 = true := by decide +kernel
lemma cell_0_0_38 : rawStepCell 5 64 T R 0 0 38 = true := by decide +kernel
lemma cell_0_0_39 : rawStepCell 5 64 T R 0 0 39 = true := by decide +kernel
lemma cell_0_0_40 : rawStepCell 5 64 T R 0 0 40 = true := by decide +kernel
lemma cell_0_0_41 : rawStepCell 5 64 T R 0 0 41 = true := by decide +kernel
lemma cell_0_0_42 : rawStepCell 5 64 T R 0 0 42 = true := by decide +kernel
lemma cell_0_0_43 : rawStepCell 5 64 T R 0 0 43 = true := by decide +kernel
lemma cell_0_0_44 : rawStepCell 5 64 T R 0 0 44 = true := by decide +kernel
lemma cell_0_0_45 : rawStepCell 5 64 T R 0 0 45 = true := by decide +kernel
lemma cell_0_0_46 : rawStepCell 5 64 T R 0 0 46 = true := by decide +kernel
lemma cell_0_0_47 : rawStepCell 5 64 T R 0 0 47 = true := by decide +kernel
lemma cell_0_0_48 : rawStepCell 5 64 T R 0 0 48 = true := by decide +kernel
lemma cell_0_0_49 : rawStepCell 5 64 T R 0 0 49 = true := by decide +kernel
lemma cell_0_0_50 : rawStepCell 5 64 T R 0 0 50 = true := by decide +kernel
lemma cell_0_0_51 : rawStepCell 5 64 T R 0 0 51 = true := by decide +kernel
lemma cell_0_0_52 : rawStepCell 5 64 T R 0 0 52 = true := by decide +kernel
lemma cell_0_0_53 : rawStepCell 5 64 T R 0 0 53 = true := by decide +kernel
lemma cell_0_0_54 : rawStepCell 5 64 T R 0 0 54 = true := by decide +kernel
lemma cell_0_0_55 : rawStepCell 5 64 T R 0 0 55 = true := by decide +kernel
lemma cell_0_0_56 : rawStepCell 5 64 T R 0 0 56 = true := by decide +kernel
lemma cell_0_0_57 : rawStepCell 5 64 T R 0 0 57 = true := by decide +kernel
lemma cell_0_0_58 : rawStepCell 5 64 T R 0 0 58 = true := by decide +kernel
lemma cell_0_0_59 : rawStepCell 5 64 T R 0 0 59 = true := by decide +kernel
lemma cell_0_0_60 : rawStepCell 5 64 T R 0 0 60 = true := by decide +kernel
lemma cell_0_0_61 : rawStepCell 5 64 T R 0 0 61 = true := by decide +kernel
lemma cell_0_0_62 : rawStepCell 5 64 T R 0 0 62 = true := by decide +kernel
lemma cell_0_0_63 : rawStepCell 5 64 T R 0 0 63 = true := by decide +kernel
lemma cell_0_1_0 : rawStepCell 5 64 T R 0 1 0 = true := by decide +kernel
lemma cell_0_1_1 : rawStepCell 5 64 T R 0 1 1 = true := by decide +kernel
lemma cell_0_1_2 : rawStepCell 5 64 T R 0 1 2 = true := by decide +kernel
lemma cell_0_1_3 : rawStepCell 5 64 T R 0 1 3 = true := by decide +kernel
lemma cell_0_1_4 : rawStepCell 5 64 T R 0 1 4 = true := by decide +kernel
lemma cell_0_1_5 : rawStepCell 5 64 T R 0 1 5 = true := by decide +kernel
lemma cell_0_1_6 : rawStepCell 5 64 T R 0 1 6 = true := by decide +kernel
lemma cell_0_1_7 : rawStepCell 5 64 T R 0 1 7 = true := by decide +kernel
lemma cell_0_1_8 : rawStepCell 5 64 T R 0 1 8 = true := by decide +kernel
lemma cell_0_1_9 : rawStepCell 5 64 T R 0 1 9 = true := by decide +kernel
lemma cell_0_1_10 : rawStepCell 5 64 T R 0 1 10 = true := by decide +kernel
lemma cell_0_1_11 : rawStepCell 5 64 T R 0 1 11 = true := by decide +kernel
lemma cell_0_1_12 : rawStepCell 5 64 T R 0 1 12 = true := by decide +kernel
lemma cell_0_1_13 : rawStepCell 5 64 T R 0 1 13 = true := by decide +kernel
lemma cell_0_1_14 : rawStepCell 5 64 T R 0 1 14 = true := by decide +kernel
lemma cell_0_1_15 : rawStepCell 5 64 T R 0 1 15 = true := by decide +kernel
lemma cell_0_1_16 : rawStepCell 5 64 T R 0 1 16 = true := by decide +kernel
lemma cell_0_1_17 : rawStepCell 5 64 T R 0 1 17 = true := by decide +kernel
lemma cell_0_1_18 : rawStepCell 5 64 T R 0 1 18 = true := by decide +kernel
lemma cell_0_1_19 : rawStepCell 5 64 T R 0 1 19 = true := by decide +kernel
lemma cell_0_1_20 : rawStepCell 5 64 T R 0 1 20 = true := by decide +kernel
lemma cell_0_1_21 : rawStepCell 5 64 T R 0 1 21 = true := by decide +kernel
lemma cell_0_1_22 : rawStepCell 5 64 T R 0 1 22 = true := by decide +kernel
lemma cell_0_1_23 : rawStepCell 5 64 T R 0 1 23 = true := by decide +kernel
lemma cell_0_1_24 : rawStepCell 5 64 T R 0 1 24 = true := by decide +kernel
lemma cell_0_1_25 : rawStepCell 5 64 T R 0 1 25 = true := by decide +kernel
lemma cell_0_1_26 : rawStepCell 5 64 T R 0 1 26 = true := by decide +kernel
lemma cell_0_1_27 : rawStepCell 5 64 T R 0 1 27 = true := by decide +kernel
lemma cell_0_1_28 : rawStepCell 5 64 T R 0 1 28 = true := by decide +kernel
lemma cell_0_1_29 : rawStepCell 5 64 T R 0 1 29 = true := by decide +kernel
lemma cell_0_1_30 : rawStepCell 5 64 T R 0 1 30 = true := by decide +kernel
lemma cell_0_1_31 : rawStepCell 5 64 T R 0 1 31 = true := by decide +kernel
lemma cell_0_1_32 : rawStepCell 5 64 T R 0 1 32 = true := by decide +kernel
lemma cell_0_1_33 : rawStepCell 5 64 T R 0 1 33 = true := by decide +kernel
lemma cell_0_1_34 : rawStepCell 5 64 T R 0 1 34 = true := by decide +kernel
lemma cell_0_1_35 : rawStepCell 5 64 T R 0 1 35 = true := by decide +kernel
lemma cell_0_1_36 : rawStepCell 5 64 T R 0 1 36 = true := by decide +kernel
lemma cell_0_1_37 : rawStepCell 5 64 T R 0 1 37 = true := by decide +kernel
lemma cell_0_1_38 : rawStepCell 5 64 T R 0 1 38 = true := by decide +kernel
lemma cell_0_1_39 : rawStepCell 5 64 T R 0 1 39 = true := by decide +kernel
lemma cell_0_1_40 : rawStepCell 5 64 T R 0 1 40 = true := by decide +kernel
lemma cell_0_1_41 : rawStepCell 5 64 T R 0 1 41 = true := by decide +kernel
lemma cell_0_1_42 : rawStepCell 5 64 T R 0 1 42 = true := by decide +kernel
lemma cell_0_1_43 : rawStepCell 5 64 T R 0 1 43 = true := by decide +kernel
lemma cell_0_1_44 : rawStepCell 5 64 T R 0 1 44 = true := by decide +kernel
lemma cell_0_1_45 : rawStepCell 5 64 T R 0 1 45 = true := by decide +kernel
lemma cell_0_1_46 : rawStepCell 5 64 T R 0 1 46 = true := by decide +kernel
lemma cell_0_1_47 : rawStepCell 5 64 T R 0 1 47 = true := by decide +kernel
lemma cell_0_1_48 : rawStepCell 5 64 T R 0 1 48 = true := by decide +kernel
lemma cell_0_1_49 : rawStepCell 5 64 T R 0 1 49 = true := by decide +kernel
lemma cell_0_1_50 : rawStepCell 5 64 T R 0 1 50 = true := by decide +kernel
lemma cell_0_1_51 : rawStepCell 5 64 T R 0 1 51 = true := by decide +kernel
lemma cell_0_1_52 : rawStepCell 5 64 T R 0 1 52 = true := by decide +kernel
lemma cell_0_1_53 : rawStepCell 5 64 T R 0 1 53 = true := by decide +kernel
lemma cell_0_1_54 : rawStepCell 5 64 T R 0 1 54 = true := by decide +kernel
lemma cell_0_1_55 : rawStepCell 5 64 T R 0 1 55 = true := by decide +kernel
lemma cell_0_1_56 : rawStepCell 5 64 T R 0 1 56 = true := by decide +kernel
lemma cell_0_1_57 : rawStepCell 5 64 T R 0 1 57 = true := by decide +kernel
lemma cell_0_1_58 : rawStepCell 5 64 T R 0 1 58 = true := by decide +kernel
lemma cell_0_1_59 : rawStepCell 5 64 T R 0 1 59 = true := by decide +kernel
lemma cell_0_1_60 : rawStepCell 5 64 T R 0 1 60 = true := by decide +kernel
lemma cell_0_1_61 : rawStepCell 5 64 T R 0 1 61 = true := by decide +kernel
lemma cell_0_1_62 : rawStepCell 5 64 T R 0 1 62 = true := by decide +kernel
lemma cell_0_1_63 : rawStepCell 5 64 T R 0 1 63 = true := by decide +kernel
lemma cell_0_2_0 : rawStepCell 5 64 T R 0 2 0 = true := by decide +kernel
lemma cell_0_2_1 : rawStepCell 5 64 T R 0 2 1 = true := by decide +kernel
lemma cell_0_2_2 : rawStepCell 5 64 T R 0 2 2 = true := by decide +kernel
lemma cell_0_2_3 : rawStepCell 5 64 T R 0 2 3 = true := by decide +kernel
lemma cell_0_2_4 : rawStepCell 5 64 T R 0 2 4 = true := by decide +kernel
lemma cell_0_2_5 : rawStepCell 5 64 T R 0 2 5 = true := by decide +kernel
lemma cell_0_2_6 : rawStepCell 5 64 T R 0 2 6 = true := by decide +kernel
lemma cell_0_2_7 : rawStepCell 5 64 T R 0 2 7 = true := by decide +kernel
lemma cell_0_2_8 : rawStepCell 5 64 T R 0 2 8 = true := by decide +kernel
lemma cell_0_2_9 : rawStepCell 5 64 T R 0 2 9 = true := by decide +kernel
lemma cell_0_2_10 : rawStepCell 5 64 T R 0 2 10 = true := by decide +kernel
lemma cell_0_2_11 : rawStepCell 5 64 T R 0 2 11 = true := by decide +kernel
lemma cell_0_2_12 : rawStepCell 5 64 T R 0 2 12 = true := by decide +kernel
lemma cell_0_2_13 : rawStepCell 5 64 T R 0 2 13 = true := by decide +kernel
lemma cell_0_2_14 : rawStepCell 5 64 T R 0 2 14 = true := by decide +kernel
lemma cell_0_2_15 : rawStepCell 5 64 T R 0 2 15 = true := by decide +kernel
lemma cell_0_2_16 : rawStepCell 5 64 T R 0 2 16 = true := by decide +kernel
lemma cell_0_2_17 : rawStepCell 5 64 T R 0 2 17 = true := by decide +kernel
lemma cell_0_2_18 : rawStepCell 5 64 T R 0 2 18 = true := by decide +kernel
lemma cell_0_2_19 : rawStepCell 5 64 T R 0 2 19 = true := by decide +kernel
lemma cell_0_2_20 : rawStepCell 5 64 T R 0 2 20 = true := by decide +kernel
lemma cell_0_2_21 : rawStepCell 5 64 T R 0 2 21 = true := by decide +kernel
lemma cell_0_2_22 : rawStepCell 5 64 T R 0 2 22 = true := by decide +kernel
lemma cell_0_2_23 : rawStepCell 5 64 T R 0 2 23 = true := by decide +kernel
lemma cell_0_2_24 : rawStepCell 5 64 T R 0 2 24 = true := by decide +kernel
lemma cell_0_2_25 : rawStepCell 5 64 T R 0 2 25 = true := by decide +kernel
lemma cell_0_2_26 : rawStepCell 5 64 T R 0 2 26 = true := by decide +kernel
lemma cell_0_2_27 : rawStepCell 5 64 T R 0 2 27 = true := by decide +kernel
lemma cell_0_2_28 : rawStepCell 5 64 T R 0 2 28 = true := by decide +kernel
lemma cell_0_2_29 : rawStepCell 5 64 T R 0 2 29 = true := by decide +kernel
lemma cell_0_2_30 : rawStepCell 5 64 T R 0 2 30 = true := by decide +kernel
lemma cell_0_2_31 : rawStepCell 5 64 T R 0 2 31 = true := by decide +kernel
lemma cell_0_2_32 : rawStepCell 5 64 T R 0 2 32 = true := by decide +kernel
lemma cell_0_2_33 : rawStepCell 5 64 T R 0 2 33 = true := by decide +kernel
lemma cell_0_2_34 : rawStepCell 5 64 T R 0 2 34 = true := by decide +kernel
lemma cell_0_2_35 : rawStepCell 5 64 T R 0 2 35 = true := by decide +kernel
lemma cell_0_2_36 : rawStepCell 5 64 T R 0 2 36 = true := by decide +kernel
lemma cell_0_2_37 : rawStepCell 5 64 T R 0 2 37 = true := by decide +kernel
lemma cell_0_2_38 : rawStepCell 5 64 T R 0 2 38 = true := by decide +kernel
lemma cell_0_2_39 : rawStepCell 5 64 T R 0 2 39 = true := by decide +kernel
lemma cell_0_2_40 : rawStepCell 5 64 T R 0 2 40 = true := by decide +kernel
lemma cell_0_2_41 : rawStepCell 5 64 T R 0 2 41 = true := by decide +kernel
lemma cell_0_2_42 : rawStepCell 5 64 T R 0 2 42 = true := by decide +kernel
lemma cell_0_2_43 : rawStepCell 5 64 T R 0 2 43 = true := by decide +kernel
lemma cell_0_2_44 : rawStepCell 5 64 T R 0 2 44 = true := by decide +kernel
lemma cell_0_2_45 : rawStepCell 5 64 T R 0 2 45 = true := by decide +kernel
lemma cell_0_2_46 : rawStepCell 5 64 T R 0 2 46 = true := by decide +kernel
lemma cell_0_2_47 : rawStepCell 5 64 T R 0 2 47 = true := by decide +kernel
lemma cell_0_2_48 : rawStepCell 5 64 T R 0 2 48 = true := by decide +kernel
lemma cell_0_2_49 : rawStepCell 5 64 T R 0 2 49 = true := by decide +kernel
lemma cell_0_2_50 : rawStepCell 5 64 T R 0 2 50 = true := by decide +kernel
lemma cell_0_2_51 : rawStepCell 5 64 T R 0 2 51 = true := by decide +kernel
lemma cell_0_2_52 : rawStepCell 5 64 T R 0 2 52 = true := by decide +kernel
lemma cell_0_2_53 : rawStepCell 5 64 T R 0 2 53 = true := by decide +kernel
lemma cell_0_2_54 : rawStepCell 5 64 T R 0 2 54 = true := by decide +kernel
lemma cell_0_2_55 : rawStepCell 5 64 T R 0 2 55 = true := by decide +kernel
lemma cell_0_2_56 : rawStepCell 5 64 T R 0 2 56 = true := by decide +kernel
lemma cell_0_2_57 : rawStepCell 5 64 T R 0 2 57 = true := by decide +kernel
lemma cell_0_2_58 : rawStepCell 5 64 T R 0 2 58 = true := by decide +kernel
lemma cell_0_2_59 : rawStepCell 5 64 T R 0 2 59 = true := by decide +kernel
lemma cell_0_2_60 : rawStepCell 5 64 T R 0 2 60 = true := by decide +kernel
lemma cell_0_2_61 : rawStepCell 5 64 T R 0 2 61 = true := by decide +kernel
lemma cell_0_2_62 : rawStepCell 5 64 T R 0 2 62 = true := by decide +kernel
lemma cell_0_2_63 : rawStepCell 5 64 T R 0 2 63 = true := by decide +kernel
lemma digit_0_0 : allBelow 64 (rawStepCell 5 64 T R 0 0) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 0 0) = true from rfl)) cell_0_0_0) cell_0_0_1) cell_0_0_2) cell_0_0_3) cell_0_0_4) cell_0_0_5) cell_0_0_6) cell_0_0_7) cell_0_0_8) cell_0_0_9) cell_0_0_10) cell_0_0_11) cell_0_0_12) cell_0_0_13) cell_0_0_14) cell_0_0_15) cell_0_0_16) cell_0_0_17) cell_0_0_18) cell_0_0_19) cell_0_0_20) cell_0_0_21) cell_0_0_22) cell_0_0_23) cell_0_0_24) cell_0_0_25) cell_0_0_26) cell_0_0_27) cell_0_0_28) cell_0_0_29) cell_0_0_30) cell_0_0_31) cell_0_0_32) cell_0_0_33) cell_0_0_34) cell_0_0_35) cell_0_0_36) cell_0_0_37) cell_0_0_38) cell_0_0_39) cell_0_0_40) cell_0_0_41) cell_0_0_42) cell_0_0_43) cell_0_0_44) cell_0_0_45) cell_0_0_46) cell_0_0_47) cell_0_0_48) cell_0_0_49) cell_0_0_50) cell_0_0_51) cell_0_0_52) cell_0_0_53) cell_0_0_54) cell_0_0_55) cell_0_0_56) cell_0_0_57) cell_0_0_58) cell_0_0_59) cell_0_0_60) cell_0_0_61) cell_0_0_62) cell_0_0_63
lemma digit_0_1 : allBelow 64 (rawStepCell 5 64 T R 0 1) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 0 1) = true from rfl)) cell_0_1_0) cell_0_1_1) cell_0_1_2) cell_0_1_3) cell_0_1_4) cell_0_1_5) cell_0_1_6) cell_0_1_7) cell_0_1_8) cell_0_1_9) cell_0_1_10) cell_0_1_11) cell_0_1_12) cell_0_1_13) cell_0_1_14) cell_0_1_15) cell_0_1_16) cell_0_1_17) cell_0_1_18) cell_0_1_19) cell_0_1_20) cell_0_1_21) cell_0_1_22) cell_0_1_23) cell_0_1_24) cell_0_1_25) cell_0_1_26) cell_0_1_27) cell_0_1_28) cell_0_1_29) cell_0_1_30) cell_0_1_31) cell_0_1_32) cell_0_1_33) cell_0_1_34) cell_0_1_35) cell_0_1_36) cell_0_1_37) cell_0_1_38) cell_0_1_39) cell_0_1_40) cell_0_1_41) cell_0_1_42) cell_0_1_43) cell_0_1_44) cell_0_1_45) cell_0_1_46) cell_0_1_47) cell_0_1_48) cell_0_1_49) cell_0_1_50) cell_0_1_51) cell_0_1_52) cell_0_1_53) cell_0_1_54) cell_0_1_55) cell_0_1_56) cell_0_1_57) cell_0_1_58) cell_0_1_59) cell_0_1_60) cell_0_1_61) cell_0_1_62) cell_0_1_63
lemma digit_0_2 : allBelow 64 (rawStepCell 5 64 T R 0 2) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 0 2) = true from rfl)) cell_0_2_0) cell_0_2_1) cell_0_2_2) cell_0_2_3) cell_0_2_4) cell_0_2_5) cell_0_2_6) cell_0_2_7) cell_0_2_8) cell_0_2_9) cell_0_2_10) cell_0_2_11) cell_0_2_12) cell_0_2_13) cell_0_2_14) cell_0_2_15) cell_0_2_16) cell_0_2_17) cell_0_2_18) cell_0_2_19) cell_0_2_20) cell_0_2_21) cell_0_2_22) cell_0_2_23) cell_0_2_24) cell_0_2_25) cell_0_2_26) cell_0_2_27) cell_0_2_28) cell_0_2_29) cell_0_2_30) cell_0_2_31) cell_0_2_32) cell_0_2_33) cell_0_2_34) cell_0_2_35) cell_0_2_36) cell_0_2_37) cell_0_2_38) cell_0_2_39) cell_0_2_40) cell_0_2_41) cell_0_2_42) cell_0_2_43) cell_0_2_44) cell_0_2_45) cell_0_2_46) cell_0_2_47) cell_0_2_48) cell_0_2_49) cell_0_2_50) cell_0_2_51) cell_0_2_52) cell_0_2_53) cell_0_2_54) cell_0_2_55) cell_0_2_56) cell_0_2_57) cell_0_2_58) cell_0_2_59) cell_0_2_60) cell_0_2_61) cell_0_2_62) cell_0_2_63
lemma row_0 : rawStepRow 5 64 T R 0 = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (fun d => allBelow 64 (rawStepCell 5 64 T R 0 d)) = true from rfl)) digit_0_0) digit_0_1) digit_0_2
#print axioms row_0
lemma cell_1_0_0 : rawStepCell 5 64 T R 1 0 0 = true := by decide +kernel
lemma cell_1_0_1 : rawStepCell 5 64 T R 1 0 1 = true := by decide +kernel
lemma cell_1_0_2 : rawStepCell 5 64 T R 1 0 2 = true := by decide +kernel
lemma cell_1_0_3 : rawStepCell 5 64 T R 1 0 3 = true := by decide +kernel
lemma cell_1_0_4 : rawStepCell 5 64 T R 1 0 4 = true := by decide +kernel
lemma cell_1_0_5 : rawStepCell 5 64 T R 1 0 5 = true := by decide +kernel
lemma cell_1_0_6 : rawStepCell 5 64 T R 1 0 6 = true := by decide +kernel
lemma cell_1_0_7 : rawStepCell 5 64 T R 1 0 7 = true := by decide +kernel
lemma cell_1_0_8 : rawStepCell 5 64 T R 1 0 8 = true := by decide +kernel
lemma cell_1_0_9 : rawStepCell 5 64 T R 1 0 9 = true := by decide +kernel
lemma cell_1_0_10 : rawStepCell 5 64 T R 1 0 10 = true := by decide +kernel
lemma cell_1_0_11 : rawStepCell 5 64 T R 1 0 11 = true := by decide +kernel
lemma cell_1_0_12 : rawStepCell 5 64 T R 1 0 12 = true := by decide +kernel
lemma cell_1_0_13 : rawStepCell 5 64 T R 1 0 13 = true := by decide +kernel
lemma cell_1_0_14 : rawStepCell 5 64 T R 1 0 14 = true := by decide +kernel
lemma cell_1_0_15 : rawStepCell 5 64 T R 1 0 15 = true := by decide +kernel
lemma cell_1_0_16 : rawStepCell 5 64 T R 1 0 16 = true := by decide +kernel
lemma cell_1_0_17 : rawStepCell 5 64 T R 1 0 17 = true := by decide +kernel
lemma cell_1_0_18 : rawStepCell 5 64 T R 1 0 18 = true := by decide +kernel
lemma cell_1_0_19 : rawStepCell 5 64 T R 1 0 19 = true := by decide +kernel
lemma cell_1_0_20 : rawStepCell 5 64 T R 1 0 20 = true := by decide +kernel
lemma cell_1_0_21 : rawStepCell 5 64 T R 1 0 21 = true := by decide +kernel
lemma cell_1_0_22 : rawStepCell 5 64 T R 1 0 22 = true := by decide +kernel
lemma cell_1_0_23 : rawStepCell 5 64 T R 1 0 23 = true := by decide +kernel
lemma cell_1_0_24 : rawStepCell 5 64 T R 1 0 24 = true := by decide +kernel
lemma cell_1_0_25 : rawStepCell 5 64 T R 1 0 25 = true := by decide +kernel
lemma cell_1_0_26 : rawStepCell 5 64 T R 1 0 26 = true := by decide +kernel
lemma cell_1_0_27 : rawStepCell 5 64 T R 1 0 27 = true := by decide +kernel
lemma cell_1_0_28 : rawStepCell 5 64 T R 1 0 28 = true := by decide +kernel
lemma cell_1_0_29 : rawStepCell 5 64 T R 1 0 29 = true := by decide +kernel
lemma cell_1_0_30 : rawStepCell 5 64 T R 1 0 30 = true := by decide +kernel
lemma cell_1_0_31 : rawStepCell 5 64 T R 1 0 31 = true := by decide +kernel
lemma cell_1_0_32 : rawStepCell 5 64 T R 1 0 32 = true := by decide +kernel
lemma cell_1_0_33 : rawStepCell 5 64 T R 1 0 33 = true := by decide +kernel
lemma cell_1_0_34 : rawStepCell 5 64 T R 1 0 34 = true := by decide +kernel
lemma cell_1_0_35 : rawStepCell 5 64 T R 1 0 35 = true := by decide +kernel
lemma cell_1_0_36 : rawStepCell 5 64 T R 1 0 36 = true := by decide +kernel
lemma cell_1_0_37 : rawStepCell 5 64 T R 1 0 37 = true := by decide +kernel
lemma cell_1_0_38 : rawStepCell 5 64 T R 1 0 38 = true := by decide +kernel
lemma cell_1_0_39 : rawStepCell 5 64 T R 1 0 39 = true := by decide +kernel
lemma cell_1_0_40 : rawStepCell 5 64 T R 1 0 40 = true := by decide +kernel
lemma cell_1_0_41 : rawStepCell 5 64 T R 1 0 41 = true := by decide +kernel
lemma cell_1_0_42 : rawStepCell 5 64 T R 1 0 42 = true := by decide +kernel
lemma cell_1_0_43 : rawStepCell 5 64 T R 1 0 43 = true := by decide +kernel
lemma cell_1_0_44 : rawStepCell 5 64 T R 1 0 44 = true := by decide +kernel
lemma cell_1_0_45 : rawStepCell 5 64 T R 1 0 45 = true := by decide +kernel
lemma cell_1_0_46 : rawStepCell 5 64 T R 1 0 46 = true := by decide +kernel
lemma cell_1_0_47 : rawStepCell 5 64 T R 1 0 47 = true := by decide +kernel
lemma cell_1_0_48 : rawStepCell 5 64 T R 1 0 48 = true := by decide +kernel
lemma cell_1_0_49 : rawStepCell 5 64 T R 1 0 49 = true := by decide +kernel
lemma cell_1_0_50 : rawStepCell 5 64 T R 1 0 50 = true := by decide +kernel
lemma cell_1_0_51 : rawStepCell 5 64 T R 1 0 51 = true := by decide +kernel
lemma cell_1_0_52 : rawStepCell 5 64 T R 1 0 52 = true := by decide +kernel
lemma cell_1_0_53 : rawStepCell 5 64 T R 1 0 53 = true := by decide +kernel
lemma cell_1_0_54 : rawStepCell 5 64 T R 1 0 54 = true := by decide +kernel
lemma cell_1_0_55 : rawStepCell 5 64 T R 1 0 55 = true := by decide +kernel
lemma cell_1_0_56 : rawStepCell 5 64 T R 1 0 56 = true := by decide +kernel
lemma cell_1_0_57 : rawStepCell 5 64 T R 1 0 57 = true := by decide +kernel
lemma cell_1_0_58 : rawStepCell 5 64 T R 1 0 58 = true := by decide +kernel
lemma cell_1_0_59 : rawStepCell 5 64 T R 1 0 59 = true := by decide +kernel
lemma cell_1_0_60 : rawStepCell 5 64 T R 1 0 60 = true := by decide +kernel
lemma cell_1_0_61 : rawStepCell 5 64 T R 1 0 61 = true := by decide +kernel
lemma cell_1_0_62 : rawStepCell 5 64 T R 1 0 62 = true := by decide +kernel
lemma cell_1_0_63 : rawStepCell 5 64 T R 1 0 63 = true := by decide +kernel
lemma cell_1_1_0 : rawStepCell 5 64 T R 1 1 0 = true := by decide +kernel
lemma cell_1_1_1 : rawStepCell 5 64 T R 1 1 1 = true := by decide +kernel
lemma cell_1_1_2 : rawStepCell 5 64 T R 1 1 2 = true := by decide +kernel
lemma cell_1_1_3 : rawStepCell 5 64 T R 1 1 3 = true := by decide +kernel
lemma cell_1_1_4 : rawStepCell 5 64 T R 1 1 4 = true := by decide +kernel
lemma cell_1_1_5 : rawStepCell 5 64 T R 1 1 5 = true := by decide +kernel
lemma cell_1_1_6 : rawStepCell 5 64 T R 1 1 6 = true := by decide +kernel
lemma cell_1_1_7 : rawStepCell 5 64 T R 1 1 7 = true := by decide +kernel
lemma cell_1_1_8 : rawStepCell 5 64 T R 1 1 8 = true := by decide +kernel
lemma cell_1_1_9 : rawStepCell 5 64 T R 1 1 9 = true := by decide +kernel
lemma cell_1_1_10 : rawStepCell 5 64 T R 1 1 10 = true := by decide +kernel
lemma cell_1_1_11 : rawStepCell 5 64 T R 1 1 11 = true := by decide +kernel
lemma cell_1_1_12 : rawStepCell 5 64 T R 1 1 12 = true := by decide +kernel
lemma cell_1_1_13 : rawStepCell 5 64 T R 1 1 13 = true := by decide +kernel
lemma cell_1_1_14 : rawStepCell 5 64 T R 1 1 14 = true := by decide +kernel
lemma cell_1_1_15 : rawStepCell 5 64 T R 1 1 15 = true := by decide +kernel
lemma cell_1_1_16 : rawStepCell 5 64 T R 1 1 16 = true := by decide +kernel
lemma cell_1_1_17 : rawStepCell 5 64 T R 1 1 17 = true := by decide +kernel
lemma cell_1_1_18 : rawStepCell 5 64 T R 1 1 18 = true := by decide +kernel
lemma cell_1_1_19 : rawStepCell 5 64 T R 1 1 19 = true := by decide +kernel
lemma cell_1_1_20 : rawStepCell 5 64 T R 1 1 20 = true := by decide +kernel
lemma cell_1_1_21 : rawStepCell 5 64 T R 1 1 21 = true := by decide +kernel
lemma cell_1_1_22 : rawStepCell 5 64 T R 1 1 22 = true := by decide +kernel
lemma cell_1_1_23 : rawStepCell 5 64 T R 1 1 23 = true := by decide +kernel
lemma cell_1_1_24 : rawStepCell 5 64 T R 1 1 24 = true := by decide +kernel
lemma cell_1_1_25 : rawStepCell 5 64 T R 1 1 25 = true := by decide +kernel
lemma cell_1_1_26 : rawStepCell 5 64 T R 1 1 26 = true := by decide +kernel
lemma cell_1_1_27 : rawStepCell 5 64 T R 1 1 27 = true := by decide +kernel
lemma cell_1_1_28 : rawStepCell 5 64 T R 1 1 28 = true := by decide +kernel
lemma cell_1_1_29 : rawStepCell 5 64 T R 1 1 29 = true := by decide +kernel
lemma cell_1_1_30 : rawStepCell 5 64 T R 1 1 30 = true := by decide +kernel
lemma cell_1_1_31 : rawStepCell 5 64 T R 1 1 31 = true := by decide +kernel
lemma cell_1_1_32 : rawStepCell 5 64 T R 1 1 32 = true := by decide +kernel
lemma cell_1_1_33 : rawStepCell 5 64 T R 1 1 33 = true := by decide +kernel
lemma cell_1_1_34 : rawStepCell 5 64 T R 1 1 34 = true := by decide +kernel
lemma cell_1_1_35 : rawStepCell 5 64 T R 1 1 35 = true := by decide +kernel
lemma cell_1_1_36 : rawStepCell 5 64 T R 1 1 36 = true := by decide +kernel
lemma cell_1_1_37 : rawStepCell 5 64 T R 1 1 37 = true := by decide +kernel
lemma cell_1_1_38 : rawStepCell 5 64 T R 1 1 38 = true := by decide +kernel
lemma cell_1_1_39 : rawStepCell 5 64 T R 1 1 39 = true := by decide +kernel
lemma cell_1_1_40 : rawStepCell 5 64 T R 1 1 40 = true := by decide +kernel
lemma cell_1_1_41 : rawStepCell 5 64 T R 1 1 41 = true := by decide +kernel
lemma cell_1_1_42 : rawStepCell 5 64 T R 1 1 42 = true := by decide +kernel
lemma cell_1_1_43 : rawStepCell 5 64 T R 1 1 43 = true := by decide +kernel
lemma cell_1_1_44 : rawStepCell 5 64 T R 1 1 44 = true := by decide +kernel
lemma cell_1_1_45 : rawStepCell 5 64 T R 1 1 45 = true := by decide +kernel
lemma cell_1_1_46 : rawStepCell 5 64 T R 1 1 46 = true := by decide +kernel
lemma cell_1_1_47 : rawStepCell 5 64 T R 1 1 47 = true := by decide +kernel
lemma cell_1_1_48 : rawStepCell 5 64 T R 1 1 48 = true := by decide +kernel
lemma cell_1_1_49 : rawStepCell 5 64 T R 1 1 49 = true := by decide +kernel
lemma cell_1_1_50 : rawStepCell 5 64 T R 1 1 50 = true := by decide +kernel
lemma cell_1_1_51 : rawStepCell 5 64 T R 1 1 51 = true := by decide +kernel
lemma cell_1_1_52 : rawStepCell 5 64 T R 1 1 52 = true := by decide +kernel
lemma cell_1_1_53 : rawStepCell 5 64 T R 1 1 53 = true := by decide +kernel
lemma cell_1_1_54 : rawStepCell 5 64 T R 1 1 54 = true := by decide +kernel
lemma cell_1_1_55 : rawStepCell 5 64 T R 1 1 55 = true := by decide +kernel
lemma cell_1_1_56 : rawStepCell 5 64 T R 1 1 56 = true := by decide +kernel
lemma cell_1_1_57 : rawStepCell 5 64 T R 1 1 57 = true := by decide +kernel
lemma cell_1_1_58 : rawStepCell 5 64 T R 1 1 58 = true := by decide +kernel
lemma cell_1_1_59 : rawStepCell 5 64 T R 1 1 59 = true := by decide +kernel
lemma cell_1_1_60 : rawStepCell 5 64 T R 1 1 60 = true := by decide +kernel
lemma cell_1_1_61 : rawStepCell 5 64 T R 1 1 61 = true := by decide +kernel
lemma cell_1_1_62 : rawStepCell 5 64 T R 1 1 62 = true := by decide +kernel
lemma cell_1_1_63 : rawStepCell 5 64 T R 1 1 63 = true := by decide +kernel
lemma cell_1_2_0 : rawStepCell 5 64 T R 1 2 0 = true := by decide +kernel
lemma cell_1_2_1 : rawStepCell 5 64 T R 1 2 1 = true := by decide +kernel
lemma cell_1_2_2 : rawStepCell 5 64 T R 1 2 2 = true := by decide +kernel
lemma cell_1_2_3 : rawStepCell 5 64 T R 1 2 3 = true := by decide +kernel
lemma cell_1_2_4 : rawStepCell 5 64 T R 1 2 4 = true := by decide +kernel
lemma cell_1_2_5 : rawStepCell 5 64 T R 1 2 5 = true := by decide +kernel
lemma cell_1_2_6 : rawStepCell 5 64 T R 1 2 6 = true := by decide +kernel
lemma cell_1_2_7 : rawStepCell 5 64 T R 1 2 7 = true := by decide +kernel
lemma cell_1_2_8 : rawStepCell 5 64 T R 1 2 8 = true := by decide +kernel
lemma cell_1_2_9 : rawStepCell 5 64 T R 1 2 9 = true := by decide +kernel
lemma cell_1_2_10 : rawStepCell 5 64 T R 1 2 10 = true := by decide +kernel
lemma cell_1_2_11 : rawStepCell 5 64 T R 1 2 11 = true := by decide +kernel
lemma cell_1_2_12 : rawStepCell 5 64 T R 1 2 12 = true := by decide +kernel
lemma cell_1_2_13 : rawStepCell 5 64 T R 1 2 13 = true := by decide +kernel
lemma cell_1_2_14 : rawStepCell 5 64 T R 1 2 14 = true := by decide +kernel
lemma cell_1_2_15 : rawStepCell 5 64 T R 1 2 15 = true := by decide +kernel
lemma cell_1_2_16 : rawStepCell 5 64 T R 1 2 16 = true := by decide +kernel
lemma cell_1_2_17 : rawStepCell 5 64 T R 1 2 17 = true := by decide +kernel
lemma cell_1_2_18 : rawStepCell 5 64 T R 1 2 18 = true := by decide +kernel
lemma cell_1_2_19 : rawStepCell 5 64 T R 1 2 19 = true := by decide +kernel
lemma cell_1_2_20 : rawStepCell 5 64 T R 1 2 20 = true := by decide +kernel
lemma cell_1_2_21 : rawStepCell 5 64 T R 1 2 21 = true := by decide +kernel
lemma cell_1_2_22 : rawStepCell 5 64 T R 1 2 22 = true := by decide +kernel
lemma cell_1_2_23 : rawStepCell 5 64 T R 1 2 23 = true := by decide +kernel
lemma cell_1_2_24 : rawStepCell 5 64 T R 1 2 24 = true := by decide +kernel
lemma cell_1_2_25 : rawStepCell 5 64 T R 1 2 25 = true := by decide +kernel
lemma cell_1_2_26 : rawStepCell 5 64 T R 1 2 26 = true := by decide +kernel
lemma cell_1_2_27 : rawStepCell 5 64 T R 1 2 27 = true := by decide +kernel
lemma cell_1_2_28 : rawStepCell 5 64 T R 1 2 28 = true := by decide +kernel
lemma cell_1_2_29 : rawStepCell 5 64 T R 1 2 29 = true := by decide +kernel
lemma cell_1_2_30 : rawStepCell 5 64 T R 1 2 30 = true := by decide +kernel
lemma cell_1_2_31 : rawStepCell 5 64 T R 1 2 31 = true := by decide +kernel
lemma cell_1_2_32 : rawStepCell 5 64 T R 1 2 32 = true := by decide +kernel
lemma cell_1_2_33 : rawStepCell 5 64 T R 1 2 33 = true := by decide +kernel
lemma cell_1_2_34 : rawStepCell 5 64 T R 1 2 34 = true := by decide +kernel
lemma cell_1_2_35 : rawStepCell 5 64 T R 1 2 35 = true := by decide +kernel
lemma cell_1_2_36 : rawStepCell 5 64 T R 1 2 36 = true := by decide +kernel
lemma cell_1_2_37 : rawStepCell 5 64 T R 1 2 37 = true := by decide +kernel
lemma cell_1_2_38 : rawStepCell 5 64 T R 1 2 38 = true := by decide +kernel
lemma cell_1_2_39 : rawStepCell 5 64 T R 1 2 39 = true := by decide +kernel
lemma cell_1_2_40 : rawStepCell 5 64 T R 1 2 40 = true := by decide +kernel
lemma cell_1_2_41 : rawStepCell 5 64 T R 1 2 41 = true := by decide +kernel
lemma cell_1_2_42 : rawStepCell 5 64 T R 1 2 42 = true := by decide +kernel
lemma cell_1_2_43 : rawStepCell 5 64 T R 1 2 43 = true := by decide +kernel
lemma cell_1_2_44 : rawStepCell 5 64 T R 1 2 44 = true := by decide +kernel
lemma cell_1_2_45 : rawStepCell 5 64 T R 1 2 45 = true := by decide +kernel
lemma cell_1_2_46 : rawStepCell 5 64 T R 1 2 46 = true := by decide +kernel
lemma cell_1_2_47 : rawStepCell 5 64 T R 1 2 47 = true := by decide +kernel
lemma cell_1_2_48 : rawStepCell 5 64 T R 1 2 48 = true := by decide +kernel
lemma cell_1_2_49 : rawStepCell 5 64 T R 1 2 49 = true := by decide +kernel
lemma cell_1_2_50 : rawStepCell 5 64 T R 1 2 50 = true := by decide +kernel
lemma cell_1_2_51 : rawStepCell 5 64 T R 1 2 51 = true := by decide +kernel
lemma cell_1_2_52 : rawStepCell 5 64 T R 1 2 52 = true := by decide +kernel
lemma cell_1_2_53 : rawStepCell 5 64 T R 1 2 53 = true := by decide +kernel
lemma cell_1_2_54 : rawStepCell 5 64 T R 1 2 54 = true := by decide +kernel
lemma cell_1_2_55 : rawStepCell 5 64 T R 1 2 55 = true := by decide +kernel
lemma cell_1_2_56 : rawStepCell 5 64 T R 1 2 56 = true := by decide +kernel
lemma cell_1_2_57 : rawStepCell 5 64 T R 1 2 57 = true := by decide +kernel
lemma cell_1_2_58 : rawStepCell 5 64 T R 1 2 58 = true := by decide +kernel
lemma cell_1_2_59 : rawStepCell 5 64 T R 1 2 59 = true := by decide +kernel
lemma cell_1_2_60 : rawStepCell 5 64 T R 1 2 60 = true := by decide +kernel
lemma cell_1_2_61 : rawStepCell 5 64 T R 1 2 61 = true := by decide +kernel
lemma cell_1_2_62 : rawStepCell 5 64 T R 1 2 62 = true := by decide +kernel
lemma cell_1_2_63 : rawStepCell 5 64 T R 1 2 63 = true := by decide +kernel
lemma digit_1_0 : allBelow 64 (rawStepCell 5 64 T R 1 0) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 1 0) = true from rfl)) cell_1_0_0) cell_1_0_1) cell_1_0_2) cell_1_0_3) cell_1_0_4) cell_1_0_5) cell_1_0_6) cell_1_0_7) cell_1_0_8) cell_1_0_9) cell_1_0_10) cell_1_0_11) cell_1_0_12) cell_1_0_13) cell_1_0_14) cell_1_0_15) cell_1_0_16) cell_1_0_17) cell_1_0_18) cell_1_0_19) cell_1_0_20) cell_1_0_21) cell_1_0_22) cell_1_0_23) cell_1_0_24) cell_1_0_25) cell_1_0_26) cell_1_0_27) cell_1_0_28) cell_1_0_29) cell_1_0_30) cell_1_0_31) cell_1_0_32) cell_1_0_33) cell_1_0_34) cell_1_0_35) cell_1_0_36) cell_1_0_37) cell_1_0_38) cell_1_0_39) cell_1_0_40) cell_1_0_41) cell_1_0_42) cell_1_0_43) cell_1_0_44) cell_1_0_45) cell_1_0_46) cell_1_0_47) cell_1_0_48) cell_1_0_49) cell_1_0_50) cell_1_0_51) cell_1_0_52) cell_1_0_53) cell_1_0_54) cell_1_0_55) cell_1_0_56) cell_1_0_57) cell_1_0_58) cell_1_0_59) cell_1_0_60) cell_1_0_61) cell_1_0_62) cell_1_0_63
lemma digit_1_1 : allBelow 64 (rawStepCell 5 64 T R 1 1) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 1 1) = true from rfl)) cell_1_1_0) cell_1_1_1) cell_1_1_2) cell_1_1_3) cell_1_1_4) cell_1_1_5) cell_1_1_6) cell_1_1_7) cell_1_1_8) cell_1_1_9) cell_1_1_10) cell_1_1_11) cell_1_1_12) cell_1_1_13) cell_1_1_14) cell_1_1_15) cell_1_1_16) cell_1_1_17) cell_1_1_18) cell_1_1_19) cell_1_1_20) cell_1_1_21) cell_1_1_22) cell_1_1_23) cell_1_1_24) cell_1_1_25) cell_1_1_26) cell_1_1_27) cell_1_1_28) cell_1_1_29) cell_1_1_30) cell_1_1_31) cell_1_1_32) cell_1_1_33) cell_1_1_34) cell_1_1_35) cell_1_1_36) cell_1_1_37) cell_1_1_38) cell_1_1_39) cell_1_1_40) cell_1_1_41) cell_1_1_42) cell_1_1_43) cell_1_1_44) cell_1_1_45) cell_1_1_46) cell_1_1_47) cell_1_1_48) cell_1_1_49) cell_1_1_50) cell_1_1_51) cell_1_1_52) cell_1_1_53) cell_1_1_54) cell_1_1_55) cell_1_1_56) cell_1_1_57) cell_1_1_58) cell_1_1_59) cell_1_1_60) cell_1_1_61) cell_1_1_62) cell_1_1_63
lemma digit_1_2 : allBelow 64 (rawStepCell 5 64 T R 1 2) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 1 2) = true from rfl)) cell_1_2_0) cell_1_2_1) cell_1_2_2) cell_1_2_3) cell_1_2_4) cell_1_2_5) cell_1_2_6) cell_1_2_7) cell_1_2_8) cell_1_2_9) cell_1_2_10) cell_1_2_11) cell_1_2_12) cell_1_2_13) cell_1_2_14) cell_1_2_15) cell_1_2_16) cell_1_2_17) cell_1_2_18) cell_1_2_19) cell_1_2_20) cell_1_2_21) cell_1_2_22) cell_1_2_23) cell_1_2_24) cell_1_2_25) cell_1_2_26) cell_1_2_27) cell_1_2_28) cell_1_2_29) cell_1_2_30) cell_1_2_31) cell_1_2_32) cell_1_2_33) cell_1_2_34) cell_1_2_35) cell_1_2_36) cell_1_2_37) cell_1_2_38) cell_1_2_39) cell_1_2_40) cell_1_2_41) cell_1_2_42) cell_1_2_43) cell_1_2_44) cell_1_2_45) cell_1_2_46) cell_1_2_47) cell_1_2_48) cell_1_2_49) cell_1_2_50) cell_1_2_51) cell_1_2_52) cell_1_2_53) cell_1_2_54) cell_1_2_55) cell_1_2_56) cell_1_2_57) cell_1_2_58) cell_1_2_59) cell_1_2_60) cell_1_2_61) cell_1_2_62) cell_1_2_63
lemma row_1 : rawStepRow 5 64 T R 1 = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (fun d => allBelow 64 (rawStepCell 5 64 T R 1 d)) = true from rfl)) digit_1_0) digit_1_1) digit_1_2
lemma cell_2_0_0 : rawStepCell 5 64 T R 2 0 0 = true := by decide +kernel
lemma cell_2_0_1 : rawStepCell 5 64 T R 2 0 1 = true := by decide +kernel
lemma cell_2_0_2 : rawStepCell 5 64 T R 2 0 2 = true := by decide +kernel
lemma cell_2_0_3 : rawStepCell 5 64 T R 2 0 3 = true := by decide +kernel
lemma cell_2_0_4 : rawStepCell 5 64 T R 2 0 4 = true := by decide +kernel
lemma cell_2_0_5 : rawStepCell 5 64 T R 2 0 5 = true := by decide +kernel
lemma cell_2_0_6 : rawStepCell 5 64 T R 2 0 6 = true := by decide +kernel
lemma cell_2_0_7 : rawStepCell 5 64 T R 2 0 7 = true := by decide +kernel
lemma cell_2_0_8 : rawStepCell 5 64 T R 2 0 8 = true := by decide +kernel
lemma cell_2_0_9 : rawStepCell 5 64 T R 2 0 9 = true := by decide +kernel
lemma cell_2_0_10 : rawStepCell 5 64 T R 2 0 10 = true := by decide +kernel
lemma cell_2_0_11 : rawStepCell 5 64 T R 2 0 11 = true := by decide +kernel
lemma cell_2_0_12 : rawStepCell 5 64 T R 2 0 12 = true := by decide +kernel
lemma cell_2_0_13 : rawStepCell 5 64 T R 2 0 13 = true := by decide +kernel
lemma cell_2_0_14 : rawStepCell 5 64 T R 2 0 14 = true := by decide +kernel
lemma cell_2_0_15 : rawStepCell 5 64 T R 2 0 15 = true := by decide +kernel
lemma cell_2_0_16 : rawStepCell 5 64 T R 2 0 16 = true := by decide +kernel
lemma cell_2_0_17 : rawStepCell 5 64 T R 2 0 17 = true := by decide +kernel
lemma cell_2_0_18 : rawStepCell 5 64 T R 2 0 18 = true := by decide +kernel
lemma cell_2_0_19 : rawStepCell 5 64 T R 2 0 19 = true := by decide +kernel
lemma cell_2_0_20 : rawStepCell 5 64 T R 2 0 20 = true := by decide +kernel
lemma cell_2_0_21 : rawStepCell 5 64 T R 2 0 21 = true := by decide +kernel
lemma cell_2_0_22 : rawStepCell 5 64 T R 2 0 22 = true := by decide +kernel
lemma cell_2_0_23 : rawStepCell 5 64 T R 2 0 23 = true := by decide +kernel
lemma cell_2_0_24 : rawStepCell 5 64 T R 2 0 24 = true := by decide +kernel
lemma cell_2_0_25 : rawStepCell 5 64 T R 2 0 25 = true := by decide +kernel
lemma cell_2_0_26 : rawStepCell 5 64 T R 2 0 26 = true := by decide +kernel
lemma cell_2_0_27 : rawStepCell 5 64 T R 2 0 27 = true := by decide +kernel
lemma cell_2_0_28 : rawStepCell 5 64 T R 2 0 28 = true := by decide +kernel
lemma cell_2_0_29 : rawStepCell 5 64 T R 2 0 29 = true := by decide +kernel
lemma cell_2_0_30 : rawStepCell 5 64 T R 2 0 30 = true := by decide +kernel
lemma cell_2_0_31 : rawStepCell 5 64 T R 2 0 31 = true := by decide +kernel
lemma cell_2_0_32 : rawStepCell 5 64 T R 2 0 32 = true := by decide +kernel
lemma cell_2_0_33 : rawStepCell 5 64 T R 2 0 33 = true := by decide +kernel
lemma cell_2_0_34 : rawStepCell 5 64 T R 2 0 34 = true := by decide +kernel
lemma cell_2_0_35 : rawStepCell 5 64 T R 2 0 35 = true := by decide +kernel
lemma cell_2_0_36 : rawStepCell 5 64 T R 2 0 36 = true := by decide +kernel
lemma cell_2_0_37 : rawStepCell 5 64 T R 2 0 37 = true := by decide +kernel
lemma cell_2_0_38 : rawStepCell 5 64 T R 2 0 38 = true := by decide +kernel
lemma cell_2_0_39 : rawStepCell 5 64 T R 2 0 39 = true := by decide +kernel
lemma cell_2_0_40 : rawStepCell 5 64 T R 2 0 40 = true := by decide +kernel
lemma cell_2_0_41 : rawStepCell 5 64 T R 2 0 41 = true := by decide +kernel
lemma cell_2_0_42 : rawStepCell 5 64 T R 2 0 42 = true := by decide +kernel
lemma cell_2_0_43 : rawStepCell 5 64 T R 2 0 43 = true := by decide +kernel
lemma cell_2_0_44 : rawStepCell 5 64 T R 2 0 44 = true := by decide +kernel
lemma cell_2_0_45 : rawStepCell 5 64 T R 2 0 45 = true := by decide +kernel
lemma cell_2_0_46 : rawStepCell 5 64 T R 2 0 46 = true := by decide +kernel
lemma cell_2_0_47 : rawStepCell 5 64 T R 2 0 47 = true := by decide +kernel
lemma cell_2_0_48 : rawStepCell 5 64 T R 2 0 48 = true := by decide +kernel
lemma cell_2_0_49 : rawStepCell 5 64 T R 2 0 49 = true := by decide +kernel
lemma cell_2_0_50 : rawStepCell 5 64 T R 2 0 50 = true := by decide +kernel
lemma cell_2_0_51 : rawStepCell 5 64 T R 2 0 51 = true := by decide +kernel
lemma cell_2_0_52 : rawStepCell 5 64 T R 2 0 52 = true := by decide +kernel
lemma cell_2_0_53 : rawStepCell 5 64 T R 2 0 53 = true := by decide +kernel
lemma cell_2_0_54 : rawStepCell 5 64 T R 2 0 54 = true := by decide +kernel
lemma cell_2_0_55 : rawStepCell 5 64 T R 2 0 55 = true := by decide +kernel
lemma cell_2_0_56 : rawStepCell 5 64 T R 2 0 56 = true := by decide +kernel
lemma cell_2_0_57 : rawStepCell 5 64 T R 2 0 57 = true := by decide +kernel
lemma cell_2_0_58 : rawStepCell 5 64 T R 2 0 58 = true := by decide +kernel
lemma cell_2_0_59 : rawStepCell 5 64 T R 2 0 59 = true := by decide +kernel
lemma cell_2_0_60 : rawStepCell 5 64 T R 2 0 60 = true := by decide +kernel
lemma cell_2_0_61 : rawStepCell 5 64 T R 2 0 61 = true := by decide +kernel
lemma cell_2_0_62 : rawStepCell 5 64 T R 2 0 62 = true := by decide +kernel
lemma cell_2_0_63 : rawStepCell 5 64 T R 2 0 63 = true := by decide +kernel
lemma cell_2_1_0 : rawStepCell 5 64 T R 2 1 0 = true := by decide +kernel
lemma cell_2_1_1 : rawStepCell 5 64 T R 2 1 1 = true := by decide +kernel
lemma cell_2_1_2 : rawStepCell 5 64 T R 2 1 2 = true := by decide +kernel
lemma cell_2_1_3 : rawStepCell 5 64 T R 2 1 3 = true := by decide +kernel
lemma cell_2_1_4 : rawStepCell 5 64 T R 2 1 4 = true := by decide +kernel
lemma cell_2_1_5 : rawStepCell 5 64 T R 2 1 5 = true := by decide +kernel
lemma cell_2_1_6 : rawStepCell 5 64 T R 2 1 6 = true := by decide +kernel
lemma cell_2_1_7 : rawStepCell 5 64 T R 2 1 7 = true := by decide +kernel
lemma cell_2_1_8 : rawStepCell 5 64 T R 2 1 8 = true := by decide +kernel
lemma cell_2_1_9 : rawStepCell 5 64 T R 2 1 9 = true := by decide +kernel
lemma cell_2_1_10 : rawStepCell 5 64 T R 2 1 10 = true := by decide +kernel
lemma cell_2_1_11 : rawStepCell 5 64 T R 2 1 11 = true := by decide +kernel
lemma cell_2_1_12 : rawStepCell 5 64 T R 2 1 12 = true := by decide +kernel
lemma cell_2_1_13 : rawStepCell 5 64 T R 2 1 13 = true := by decide +kernel
lemma cell_2_1_14 : rawStepCell 5 64 T R 2 1 14 = true := by decide +kernel
lemma cell_2_1_15 : rawStepCell 5 64 T R 2 1 15 = true := by decide +kernel
lemma cell_2_1_16 : rawStepCell 5 64 T R 2 1 16 = true := by decide +kernel
lemma cell_2_1_17 : rawStepCell 5 64 T R 2 1 17 = true := by decide +kernel
lemma cell_2_1_18 : rawStepCell 5 64 T R 2 1 18 = true := by decide +kernel
lemma cell_2_1_19 : rawStepCell 5 64 T R 2 1 19 = true := by decide +kernel
lemma cell_2_1_20 : rawStepCell 5 64 T R 2 1 20 = true := by decide +kernel
lemma cell_2_1_21 : rawStepCell 5 64 T R 2 1 21 = true := by decide +kernel
lemma cell_2_1_22 : rawStepCell 5 64 T R 2 1 22 = true := by decide +kernel
lemma cell_2_1_23 : rawStepCell 5 64 T R 2 1 23 = true := by decide +kernel
lemma cell_2_1_24 : rawStepCell 5 64 T R 2 1 24 = true := by decide +kernel
lemma cell_2_1_25 : rawStepCell 5 64 T R 2 1 25 = true := by decide +kernel
lemma cell_2_1_26 : rawStepCell 5 64 T R 2 1 26 = true := by decide +kernel
lemma cell_2_1_27 : rawStepCell 5 64 T R 2 1 27 = true := by decide +kernel
lemma cell_2_1_28 : rawStepCell 5 64 T R 2 1 28 = true := by decide +kernel
lemma cell_2_1_29 : rawStepCell 5 64 T R 2 1 29 = true := by decide +kernel
lemma cell_2_1_30 : rawStepCell 5 64 T R 2 1 30 = true := by decide +kernel
lemma cell_2_1_31 : rawStepCell 5 64 T R 2 1 31 = true := by decide +kernel
lemma cell_2_1_32 : rawStepCell 5 64 T R 2 1 32 = true := by decide +kernel
lemma cell_2_1_33 : rawStepCell 5 64 T R 2 1 33 = true := by decide +kernel
lemma cell_2_1_34 : rawStepCell 5 64 T R 2 1 34 = true := by decide +kernel
lemma cell_2_1_35 : rawStepCell 5 64 T R 2 1 35 = true := by decide +kernel
lemma cell_2_1_36 : rawStepCell 5 64 T R 2 1 36 = true := by decide +kernel
lemma cell_2_1_37 : rawStepCell 5 64 T R 2 1 37 = true := by decide +kernel
lemma cell_2_1_38 : rawStepCell 5 64 T R 2 1 38 = true := by decide +kernel
lemma cell_2_1_39 : rawStepCell 5 64 T R 2 1 39 = true := by decide +kernel
lemma cell_2_1_40 : rawStepCell 5 64 T R 2 1 40 = true := by decide +kernel
lemma cell_2_1_41 : rawStepCell 5 64 T R 2 1 41 = true := by decide +kernel
lemma cell_2_1_42 : rawStepCell 5 64 T R 2 1 42 = true := by decide +kernel
lemma cell_2_1_43 : rawStepCell 5 64 T R 2 1 43 = true := by decide +kernel
lemma cell_2_1_44 : rawStepCell 5 64 T R 2 1 44 = true := by decide +kernel
lemma cell_2_1_45 : rawStepCell 5 64 T R 2 1 45 = true := by decide +kernel
lemma cell_2_1_46 : rawStepCell 5 64 T R 2 1 46 = true := by decide +kernel
lemma cell_2_1_47 : rawStepCell 5 64 T R 2 1 47 = true := by decide +kernel
lemma cell_2_1_48 : rawStepCell 5 64 T R 2 1 48 = true := by decide +kernel
lemma cell_2_1_49 : rawStepCell 5 64 T R 2 1 49 = true := by decide +kernel
lemma cell_2_1_50 : rawStepCell 5 64 T R 2 1 50 = true := by decide +kernel
lemma cell_2_1_51 : rawStepCell 5 64 T R 2 1 51 = true := by decide +kernel
lemma cell_2_1_52 : rawStepCell 5 64 T R 2 1 52 = true := by decide +kernel
lemma cell_2_1_53 : rawStepCell 5 64 T R 2 1 53 = true := by decide +kernel
lemma cell_2_1_54 : rawStepCell 5 64 T R 2 1 54 = true := by decide +kernel
lemma cell_2_1_55 : rawStepCell 5 64 T R 2 1 55 = true := by decide +kernel
lemma cell_2_1_56 : rawStepCell 5 64 T R 2 1 56 = true := by decide +kernel
lemma cell_2_1_57 : rawStepCell 5 64 T R 2 1 57 = true := by decide +kernel
lemma cell_2_1_58 : rawStepCell 5 64 T R 2 1 58 = true := by decide +kernel
lemma cell_2_1_59 : rawStepCell 5 64 T R 2 1 59 = true := by decide +kernel
lemma cell_2_1_60 : rawStepCell 5 64 T R 2 1 60 = true := by decide +kernel
lemma cell_2_1_61 : rawStepCell 5 64 T R 2 1 61 = true := by decide +kernel
lemma cell_2_1_62 : rawStepCell 5 64 T R 2 1 62 = true := by decide +kernel
lemma cell_2_1_63 : rawStepCell 5 64 T R 2 1 63 = true := by decide +kernel
lemma cell_2_2_0 : rawStepCell 5 64 T R 2 2 0 = true := by decide +kernel
lemma cell_2_2_1 : rawStepCell 5 64 T R 2 2 1 = true := by decide +kernel
lemma cell_2_2_2 : rawStepCell 5 64 T R 2 2 2 = true := by decide +kernel
lemma cell_2_2_3 : rawStepCell 5 64 T R 2 2 3 = true := by decide +kernel
lemma cell_2_2_4 : rawStepCell 5 64 T R 2 2 4 = true := by decide +kernel
lemma cell_2_2_5 : rawStepCell 5 64 T R 2 2 5 = true := by decide +kernel
lemma cell_2_2_6 : rawStepCell 5 64 T R 2 2 6 = true := by decide +kernel
lemma cell_2_2_7 : rawStepCell 5 64 T R 2 2 7 = true := by decide +kernel
lemma cell_2_2_8 : rawStepCell 5 64 T R 2 2 8 = true := by decide +kernel
lemma cell_2_2_9 : rawStepCell 5 64 T R 2 2 9 = true := by decide +kernel
lemma cell_2_2_10 : rawStepCell 5 64 T R 2 2 10 = true := by decide +kernel
lemma cell_2_2_11 : rawStepCell 5 64 T R 2 2 11 = true := by decide +kernel
lemma cell_2_2_12 : rawStepCell 5 64 T R 2 2 12 = true := by decide +kernel
lemma cell_2_2_13 : rawStepCell 5 64 T R 2 2 13 = true := by decide +kernel
lemma cell_2_2_14 : rawStepCell 5 64 T R 2 2 14 = true := by decide +kernel
lemma cell_2_2_15 : rawStepCell 5 64 T R 2 2 15 = true := by decide +kernel
lemma cell_2_2_16 : rawStepCell 5 64 T R 2 2 16 = true := by decide +kernel
lemma cell_2_2_17 : rawStepCell 5 64 T R 2 2 17 = true := by decide +kernel
lemma cell_2_2_18 : rawStepCell 5 64 T R 2 2 18 = true := by decide +kernel
lemma cell_2_2_19 : rawStepCell 5 64 T R 2 2 19 = true := by decide +kernel
lemma cell_2_2_20 : rawStepCell 5 64 T R 2 2 20 = true := by decide +kernel
lemma cell_2_2_21 : rawStepCell 5 64 T R 2 2 21 = true := by decide +kernel
lemma cell_2_2_22 : rawStepCell 5 64 T R 2 2 22 = true := by decide +kernel
lemma cell_2_2_23 : rawStepCell 5 64 T R 2 2 23 = true := by decide +kernel
lemma cell_2_2_24 : rawStepCell 5 64 T R 2 2 24 = true := by decide +kernel
lemma cell_2_2_25 : rawStepCell 5 64 T R 2 2 25 = true := by decide +kernel
lemma cell_2_2_26 : rawStepCell 5 64 T R 2 2 26 = true := by decide +kernel
lemma cell_2_2_27 : rawStepCell 5 64 T R 2 2 27 = true := by decide +kernel
lemma cell_2_2_28 : rawStepCell 5 64 T R 2 2 28 = true := by decide +kernel
lemma cell_2_2_29 : rawStepCell 5 64 T R 2 2 29 = true := by decide +kernel
lemma cell_2_2_30 : rawStepCell 5 64 T R 2 2 30 = true := by decide +kernel
lemma cell_2_2_31 : rawStepCell 5 64 T R 2 2 31 = true := by decide +kernel
lemma cell_2_2_32 : rawStepCell 5 64 T R 2 2 32 = true := by decide +kernel
lemma cell_2_2_33 : rawStepCell 5 64 T R 2 2 33 = true := by decide +kernel
lemma cell_2_2_34 : rawStepCell 5 64 T R 2 2 34 = true := by decide +kernel
lemma cell_2_2_35 : rawStepCell 5 64 T R 2 2 35 = true := by decide +kernel
lemma cell_2_2_36 : rawStepCell 5 64 T R 2 2 36 = true := by decide +kernel
lemma cell_2_2_37 : rawStepCell 5 64 T R 2 2 37 = true := by decide +kernel
lemma cell_2_2_38 : rawStepCell 5 64 T R 2 2 38 = true := by decide +kernel
lemma cell_2_2_39 : rawStepCell 5 64 T R 2 2 39 = true := by decide +kernel
lemma cell_2_2_40 : rawStepCell 5 64 T R 2 2 40 = true := by decide +kernel
lemma cell_2_2_41 : rawStepCell 5 64 T R 2 2 41 = true := by decide +kernel
lemma cell_2_2_42 : rawStepCell 5 64 T R 2 2 42 = true := by decide +kernel
lemma cell_2_2_43 : rawStepCell 5 64 T R 2 2 43 = true := by decide +kernel
lemma cell_2_2_44 : rawStepCell 5 64 T R 2 2 44 = true := by decide +kernel
lemma cell_2_2_45 : rawStepCell 5 64 T R 2 2 45 = true := by decide +kernel
lemma cell_2_2_46 : rawStepCell 5 64 T R 2 2 46 = true := by decide +kernel
lemma cell_2_2_47 : rawStepCell 5 64 T R 2 2 47 = true := by decide +kernel
lemma cell_2_2_48 : rawStepCell 5 64 T R 2 2 48 = true := by decide +kernel
lemma cell_2_2_49 : rawStepCell 5 64 T R 2 2 49 = true := by decide +kernel
lemma cell_2_2_50 : rawStepCell 5 64 T R 2 2 50 = true := by decide +kernel
lemma cell_2_2_51 : rawStepCell 5 64 T R 2 2 51 = true := by decide +kernel
lemma cell_2_2_52 : rawStepCell 5 64 T R 2 2 52 = true := by decide +kernel
lemma cell_2_2_53 : rawStepCell 5 64 T R 2 2 53 = true := by decide +kernel
lemma cell_2_2_54 : rawStepCell 5 64 T R 2 2 54 = true := by decide +kernel
lemma cell_2_2_55 : rawStepCell 5 64 T R 2 2 55 = true := by decide +kernel
lemma cell_2_2_56 : rawStepCell 5 64 T R 2 2 56 = true := by decide +kernel
lemma cell_2_2_57 : rawStepCell 5 64 T R 2 2 57 = true := by decide +kernel
lemma cell_2_2_58 : rawStepCell 5 64 T R 2 2 58 = true := by decide +kernel
lemma cell_2_2_59 : rawStepCell 5 64 T R 2 2 59 = true := by decide +kernel
lemma cell_2_2_60 : rawStepCell 5 64 T R 2 2 60 = true := by decide +kernel
lemma cell_2_2_61 : rawStepCell 5 64 T R 2 2 61 = true := by decide +kernel
lemma cell_2_2_62 : rawStepCell 5 64 T R 2 2 62 = true := by decide +kernel
lemma cell_2_2_63 : rawStepCell 5 64 T R 2 2 63 = true := by decide +kernel
lemma digit_2_0 : allBelow 64 (rawStepCell 5 64 T R 2 0) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 2 0) = true from rfl)) cell_2_0_0) cell_2_0_1) cell_2_0_2) cell_2_0_3) cell_2_0_4) cell_2_0_5) cell_2_0_6) cell_2_0_7) cell_2_0_8) cell_2_0_9) cell_2_0_10) cell_2_0_11) cell_2_0_12) cell_2_0_13) cell_2_0_14) cell_2_0_15) cell_2_0_16) cell_2_0_17) cell_2_0_18) cell_2_0_19) cell_2_0_20) cell_2_0_21) cell_2_0_22) cell_2_0_23) cell_2_0_24) cell_2_0_25) cell_2_0_26) cell_2_0_27) cell_2_0_28) cell_2_0_29) cell_2_0_30) cell_2_0_31) cell_2_0_32) cell_2_0_33) cell_2_0_34) cell_2_0_35) cell_2_0_36) cell_2_0_37) cell_2_0_38) cell_2_0_39) cell_2_0_40) cell_2_0_41) cell_2_0_42) cell_2_0_43) cell_2_0_44) cell_2_0_45) cell_2_0_46) cell_2_0_47) cell_2_0_48) cell_2_0_49) cell_2_0_50) cell_2_0_51) cell_2_0_52) cell_2_0_53) cell_2_0_54) cell_2_0_55) cell_2_0_56) cell_2_0_57) cell_2_0_58) cell_2_0_59) cell_2_0_60) cell_2_0_61) cell_2_0_62) cell_2_0_63
lemma digit_2_1 : allBelow 64 (rawStepCell 5 64 T R 2 1) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 2 1) = true from rfl)) cell_2_1_0) cell_2_1_1) cell_2_1_2) cell_2_1_3) cell_2_1_4) cell_2_1_5) cell_2_1_6) cell_2_1_7) cell_2_1_8) cell_2_1_9) cell_2_1_10) cell_2_1_11) cell_2_1_12) cell_2_1_13) cell_2_1_14) cell_2_1_15) cell_2_1_16) cell_2_1_17) cell_2_1_18) cell_2_1_19) cell_2_1_20) cell_2_1_21) cell_2_1_22) cell_2_1_23) cell_2_1_24) cell_2_1_25) cell_2_1_26) cell_2_1_27) cell_2_1_28) cell_2_1_29) cell_2_1_30) cell_2_1_31) cell_2_1_32) cell_2_1_33) cell_2_1_34) cell_2_1_35) cell_2_1_36) cell_2_1_37) cell_2_1_38) cell_2_1_39) cell_2_1_40) cell_2_1_41) cell_2_1_42) cell_2_1_43) cell_2_1_44) cell_2_1_45) cell_2_1_46) cell_2_1_47) cell_2_1_48) cell_2_1_49) cell_2_1_50) cell_2_1_51) cell_2_1_52) cell_2_1_53) cell_2_1_54) cell_2_1_55) cell_2_1_56) cell_2_1_57) cell_2_1_58) cell_2_1_59) cell_2_1_60) cell_2_1_61) cell_2_1_62) cell_2_1_63
lemma digit_2_2 : allBelow 64 (rawStepCell 5 64 T R 2 2) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 2 2) = true from rfl)) cell_2_2_0) cell_2_2_1) cell_2_2_2) cell_2_2_3) cell_2_2_4) cell_2_2_5) cell_2_2_6) cell_2_2_7) cell_2_2_8) cell_2_2_9) cell_2_2_10) cell_2_2_11) cell_2_2_12) cell_2_2_13) cell_2_2_14) cell_2_2_15) cell_2_2_16) cell_2_2_17) cell_2_2_18) cell_2_2_19) cell_2_2_20) cell_2_2_21) cell_2_2_22) cell_2_2_23) cell_2_2_24) cell_2_2_25) cell_2_2_26) cell_2_2_27) cell_2_2_28) cell_2_2_29) cell_2_2_30) cell_2_2_31) cell_2_2_32) cell_2_2_33) cell_2_2_34) cell_2_2_35) cell_2_2_36) cell_2_2_37) cell_2_2_38) cell_2_2_39) cell_2_2_40) cell_2_2_41) cell_2_2_42) cell_2_2_43) cell_2_2_44) cell_2_2_45) cell_2_2_46) cell_2_2_47) cell_2_2_48) cell_2_2_49) cell_2_2_50) cell_2_2_51) cell_2_2_52) cell_2_2_53) cell_2_2_54) cell_2_2_55) cell_2_2_56) cell_2_2_57) cell_2_2_58) cell_2_2_59) cell_2_2_60) cell_2_2_61) cell_2_2_62) cell_2_2_63
lemma row_2 : rawStepRow 5 64 T R 2 = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (fun d => allBelow 64 (rawStepCell 5 64 T R 2 d)) = true from rfl)) digit_2_0) digit_2_1) digit_2_2
lemma cell_3_0_0 : rawStepCell 5 64 T R 3 0 0 = true := by decide +kernel
lemma cell_3_0_1 : rawStepCell 5 64 T R 3 0 1 = true := by decide +kernel
lemma cell_3_0_2 : rawStepCell 5 64 T R 3 0 2 = true := by decide +kernel
lemma cell_3_0_3 : rawStepCell 5 64 T R 3 0 3 = true := by decide +kernel
lemma cell_3_0_4 : rawStepCell 5 64 T R 3 0 4 = true := by decide +kernel
lemma cell_3_0_5 : rawStepCell 5 64 T R 3 0 5 = true := by decide +kernel
lemma cell_3_0_6 : rawStepCell 5 64 T R 3 0 6 = true := by decide +kernel
lemma cell_3_0_7 : rawStepCell 5 64 T R 3 0 7 = true := by decide +kernel
lemma cell_3_0_8 : rawStepCell 5 64 T R 3 0 8 = true := by decide +kernel
lemma cell_3_0_9 : rawStepCell 5 64 T R 3 0 9 = true := by decide +kernel
lemma cell_3_0_10 : rawStepCell 5 64 T R 3 0 10 = true := by decide +kernel
lemma cell_3_0_11 : rawStepCell 5 64 T R 3 0 11 = true := by decide +kernel
lemma cell_3_0_12 : rawStepCell 5 64 T R 3 0 12 = true := by decide +kernel
lemma cell_3_0_13 : rawStepCell 5 64 T R 3 0 13 = true := by decide +kernel
lemma cell_3_0_14 : rawStepCell 5 64 T R 3 0 14 = true := by decide +kernel
lemma cell_3_0_15 : rawStepCell 5 64 T R 3 0 15 = true := by decide +kernel
lemma cell_3_0_16 : rawStepCell 5 64 T R 3 0 16 = true := by decide +kernel
lemma cell_3_0_17 : rawStepCell 5 64 T R 3 0 17 = true := by decide +kernel
lemma cell_3_0_18 : rawStepCell 5 64 T R 3 0 18 = true := by decide +kernel
lemma cell_3_0_19 : rawStepCell 5 64 T R 3 0 19 = true := by decide +kernel
lemma cell_3_0_20 : rawStepCell 5 64 T R 3 0 20 = true := by decide +kernel
lemma cell_3_0_21 : rawStepCell 5 64 T R 3 0 21 = true := by decide +kernel
lemma cell_3_0_22 : rawStepCell 5 64 T R 3 0 22 = true := by decide +kernel
lemma cell_3_0_23 : rawStepCell 5 64 T R 3 0 23 = true := by decide +kernel
lemma cell_3_0_24 : rawStepCell 5 64 T R 3 0 24 = true := by decide +kernel
lemma cell_3_0_25 : rawStepCell 5 64 T R 3 0 25 = true := by decide +kernel
lemma cell_3_0_26 : rawStepCell 5 64 T R 3 0 26 = true := by decide +kernel
lemma cell_3_0_27 : rawStepCell 5 64 T R 3 0 27 = true := by decide +kernel
lemma cell_3_0_28 : rawStepCell 5 64 T R 3 0 28 = true := by decide +kernel
lemma cell_3_0_29 : rawStepCell 5 64 T R 3 0 29 = true := by decide +kernel
lemma cell_3_0_30 : rawStepCell 5 64 T R 3 0 30 = true := by decide +kernel
lemma cell_3_0_31 : rawStepCell 5 64 T R 3 0 31 = true := by decide +kernel
lemma cell_3_0_32 : rawStepCell 5 64 T R 3 0 32 = true := by decide +kernel
lemma cell_3_0_33 : rawStepCell 5 64 T R 3 0 33 = true := by decide +kernel
lemma cell_3_0_34 : rawStepCell 5 64 T R 3 0 34 = true := by decide +kernel
lemma cell_3_0_35 : rawStepCell 5 64 T R 3 0 35 = true := by decide +kernel
lemma cell_3_0_36 : rawStepCell 5 64 T R 3 0 36 = true := by decide +kernel
lemma cell_3_0_37 : rawStepCell 5 64 T R 3 0 37 = true := by decide +kernel
lemma cell_3_0_38 : rawStepCell 5 64 T R 3 0 38 = true := by decide +kernel
lemma cell_3_0_39 : rawStepCell 5 64 T R 3 0 39 = true := by decide +kernel
lemma cell_3_0_40 : rawStepCell 5 64 T R 3 0 40 = true := by decide +kernel
lemma cell_3_0_41 : rawStepCell 5 64 T R 3 0 41 = true := by decide +kernel
lemma cell_3_0_42 : rawStepCell 5 64 T R 3 0 42 = true := by decide +kernel
lemma cell_3_0_43 : rawStepCell 5 64 T R 3 0 43 = true := by decide +kernel
lemma cell_3_0_44 : rawStepCell 5 64 T R 3 0 44 = true := by decide +kernel
lemma cell_3_0_45 : rawStepCell 5 64 T R 3 0 45 = true := by decide +kernel
lemma cell_3_0_46 : rawStepCell 5 64 T R 3 0 46 = true := by decide +kernel
lemma cell_3_0_47 : rawStepCell 5 64 T R 3 0 47 = true := by decide +kernel
lemma cell_3_0_48 : rawStepCell 5 64 T R 3 0 48 = true := by decide +kernel
lemma cell_3_0_49 : rawStepCell 5 64 T R 3 0 49 = true := by decide +kernel
lemma cell_3_0_50 : rawStepCell 5 64 T R 3 0 50 = true := by decide +kernel
lemma cell_3_0_51 : rawStepCell 5 64 T R 3 0 51 = true := by decide +kernel
lemma cell_3_0_52 : rawStepCell 5 64 T R 3 0 52 = true := by decide +kernel
lemma cell_3_0_53 : rawStepCell 5 64 T R 3 0 53 = true := by decide +kernel
lemma cell_3_0_54 : rawStepCell 5 64 T R 3 0 54 = true := by decide +kernel
lemma cell_3_0_55 : rawStepCell 5 64 T R 3 0 55 = true := by decide +kernel
lemma cell_3_0_56 : rawStepCell 5 64 T R 3 0 56 = true := by decide +kernel
lemma cell_3_0_57 : rawStepCell 5 64 T R 3 0 57 = true := by decide +kernel
lemma cell_3_0_58 : rawStepCell 5 64 T R 3 0 58 = true := by decide +kernel
lemma cell_3_0_59 : rawStepCell 5 64 T R 3 0 59 = true := by decide +kernel
lemma cell_3_0_60 : rawStepCell 5 64 T R 3 0 60 = true := by decide +kernel
lemma cell_3_0_61 : rawStepCell 5 64 T R 3 0 61 = true := by decide +kernel
lemma cell_3_0_62 : rawStepCell 5 64 T R 3 0 62 = true := by decide +kernel
lemma cell_3_0_63 : rawStepCell 5 64 T R 3 0 63 = true := by decide +kernel
lemma cell_3_1_0 : rawStepCell 5 64 T R 3 1 0 = true := by decide +kernel
lemma cell_3_1_1 : rawStepCell 5 64 T R 3 1 1 = true := by decide +kernel
lemma cell_3_1_2 : rawStepCell 5 64 T R 3 1 2 = true := by decide +kernel
lemma cell_3_1_3 : rawStepCell 5 64 T R 3 1 3 = true := by decide +kernel
lemma cell_3_1_4 : rawStepCell 5 64 T R 3 1 4 = true := by decide +kernel
lemma cell_3_1_5 : rawStepCell 5 64 T R 3 1 5 = true := by decide +kernel
lemma cell_3_1_6 : rawStepCell 5 64 T R 3 1 6 = true := by decide +kernel
lemma cell_3_1_7 : rawStepCell 5 64 T R 3 1 7 = true := by decide +kernel
lemma cell_3_1_8 : rawStepCell 5 64 T R 3 1 8 = true := by decide +kernel
lemma cell_3_1_9 : rawStepCell 5 64 T R 3 1 9 = true := by decide +kernel
lemma cell_3_1_10 : rawStepCell 5 64 T R 3 1 10 = true := by decide +kernel
lemma cell_3_1_11 : rawStepCell 5 64 T R 3 1 11 = true := by decide +kernel
lemma cell_3_1_12 : rawStepCell 5 64 T R 3 1 12 = true := by decide +kernel
lemma cell_3_1_13 : rawStepCell 5 64 T R 3 1 13 = true := by decide +kernel
lemma cell_3_1_14 : rawStepCell 5 64 T R 3 1 14 = true := by decide +kernel
lemma cell_3_1_15 : rawStepCell 5 64 T R 3 1 15 = true := by decide +kernel
lemma cell_3_1_16 : rawStepCell 5 64 T R 3 1 16 = true := by decide +kernel
lemma cell_3_1_17 : rawStepCell 5 64 T R 3 1 17 = true := by decide +kernel
lemma cell_3_1_18 : rawStepCell 5 64 T R 3 1 18 = true := by decide +kernel
lemma cell_3_1_19 : rawStepCell 5 64 T R 3 1 19 = true := by decide +kernel
lemma cell_3_1_20 : rawStepCell 5 64 T R 3 1 20 = true := by decide +kernel
lemma cell_3_1_21 : rawStepCell 5 64 T R 3 1 21 = true := by decide +kernel
lemma cell_3_1_22 : rawStepCell 5 64 T R 3 1 22 = true := by decide +kernel
lemma cell_3_1_23 : rawStepCell 5 64 T R 3 1 23 = true := by decide +kernel
lemma cell_3_1_24 : rawStepCell 5 64 T R 3 1 24 = true := by decide +kernel
lemma cell_3_1_25 : rawStepCell 5 64 T R 3 1 25 = true := by decide +kernel
lemma cell_3_1_26 : rawStepCell 5 64 T R 3 1 26 = true := by decide +kernel
lemma cell_3_1_27 : rawStepCell 5 64 T R 3 1 27 = true := by decide +kernel
lemma cell_3_1_28 : rawStepCell 5 64 T R 3 1 28 = true := by decide +kernel
lemma cell_3_1_29 : rawStepCell 5 64 T R 3 1 29 = true := by decide +kernel
lemma cell_3_1_30 : rawStepCell 5 64 T R 3 1 30 = true := by decide +kernel
lemma cell_3_1_31 : rawStepCell 5 64 T R 3 1 31 = true := by decide +kernel
lemma cell_3_1_32 : rawStepCell 5 64 T R 3 1 32 = true := by decide +kernel
lemma cell_3_1_33 : rawStepCell 5 64 T R 3 1 33 = true := by decide +kernel
lemma cell_3_1_34 : rawStepCell 5 64 T R 3 1 34 = true := by decide +kernel
lemma cell_3_1_35 : rawStepCell 5 64 T R 3 1 35 = true := by decide +kernel
lemma cell_3_1_36 : rawStepCell 5 64 T R 3 1 36 = true := by decide +kernel
lemma cell_3_1_37 : rawStepCell 5 64 T R 3 1 37 = true := by decide +kernel
lemma cell_3_1_38 : rawStepCell 5 64 T R 3 1 38 = true := by decide +kernel
lemma cell_3_1_39 : rawStepCell 5 64 T R 3 1 39 = true := by decide +kernel
lemma cell_3_1_40 : rawStepCell 5 64 T R 3 1 40 = true := by decide +kernel
lemma cell_3_1_41 : rawStepCell 5 64 T R 3 1 41 = true := by decide +kernel
lemma cell_3_1_42 : rawStepCell 5 64 T R 3 1 42 = true := by decide +kernel
lemma cell_3_1_43 : rawStepCell 5 64 T R 3 1 43 = true := by decide +kernel
lemma cell_3_1_44 : rawStepCell 5 64 T R 3 1 44 = true := by decide +kernel
lemma cell_3_1_45 : rawStepCell 5 64 T R 3 1 45 = true := by decide +kernel
lemma cell_3_1_46 : rawStepCell 5 64 T R 3 1 46 = true := by decide +kernel
lemma cell_3_1_47 : rawStepCell 5 64 T R 3 1 47 = true := by decide +kernel
lemma cell_3_1_48 : rawStepCell 5 64 T R 3 1 48 = true := by decide +kernel
lemma cell_3_1_49 : rawStepCell 5 64 T R 3 1 49 = true := by decide +kernel
lemma cell_3_1_50 : rawStepCell 5 64 T R 3 1 50 = true := by decide +kernel
lemma cell_3_1_51 : rawStepCell 5 64 T R 3 1 51 = true := by decide +kernel
lemma cell_3_1_52 : rawStepCell 5 64 T R 3 1 52 = true := by decide +kernel
lemma cell_3_1_53 : rawStepCell 5 64 T R 3 1 53 = true := by decide +kernel
lemma cell_3_1_54 : rawStepCell 5 64 T R 3 1 54 = true := by decide +kernel
lemma cell_3_1_55 : rawStepCell 5 64 T R 3 1 55 = true := by decide +kernel
lemma cell_3_1_56 : rawStepCell 5 64 T R 3 1 56 = true := by decide +kernel
lemma cell_3_1_57 : rawStepCell 5 64 T R 3 1 57 = true := by decide +kernel
lemma cell_3_1_58 : rawStepCell 5 64 T R 3 1 58 = true := by decide +kernel
lemma cell_3_1_59 : rawStepCell 5 64 T R 3 1 59 = true := by decide +kernel
lemma cell_3_1_60 : rawStepCell 5 64 T R 3 1 60 = true := by decide +kernel
lemma cell_3_1_61 : rawStepCell 5 64 T R 3 1 61 = true := by decide +kernel
lemma cell_3_1_62 : rawStepCell 5 64 T R 3 1 62 = true := by decide +kernel
lemma cell_3_1_63 : rawStepCell 5 64 T R 3 1 63 = true := by decide +kernel
lemma cell_3_2_0 : rawStepCell 5 64 T R 3 2 0 = true := by decide +kernel
lemma cell_3_2_1 : rawStepCell 5 64 T R 3 2 1 = true := by decide +kernel
lemma cell_3_2_2 : rawStepCell 5 64 T R 3 2 2 = true := by decide +kernel
lemma cell_3_2_3 : rawStepCell 5 64 T R 3 2 3 = true := by decide +kernel
lemma cell_3_2_4 : rawStepCell 5 64 T R 3 2 4 = true := by decide +kernel
lemma cell_3_2_5 : rawStepCell 5 64 T R 3 2 5 = true := by decide +kernel
lemma cell_3_2_6 : rawStepCell 5 64 T R 3 2 6 = true := by decide +kernel
lemma cell_3_2_7 : rawStepCell 5 64 T R 3 2 7 = true := by decide +kernel
lemma cell_3_2_8 : rawStepCell 5 64 T R 3 2 8 = true := by decide +kernel
lemma cell_3_2_9 : rawStepCell 5 64 T R 3 2 9 = true := by decide +kernel
lemma cell_3_2_10 : rawStepCell 5 64 T R 3 2 10 = true := by decide +kernel
lemma cell_3_2_11 : rawStepCell 5 64 T R 3 2 11 = true := by decide +kernel
lemma cell_3_2_12 : rawStepCell 5 64 T R 3 2 12 = true := by decide +kernel
lemma cell_3_2_13 : rawStepCell 5 64 T R 3 2 13 = true := by decide +kernel
lemma cell_3_2_14 : rawStepCell 5 64 T R 3 2 14 = true := by decide +kernel
lemma cell_3_2_15 : rawStepCell 5 64 T R 3 2 15 = true := by decide +kernel
lemma cell_3_2_16 : rawStepCell 5 64 T R 3 2 16 = true := by decide +kernel
lemma cell_3_2_17 : rawStepCell 5 64 T R 3 2 17 = true := by decide +kernel
lemma cell_3_2_18 : rawStepCell 5 64 T R 3 2 18 = true := by decide +kernel
lemma cell_3_2_19 : rawStepCell 5 64 T R 3 2 19 = true := by decide +kernel
lemma cell_3_2_20 : rawStepCell 5 64 T R 3 2 20 = true := by decide +kernel
lemma cell_3_2_21 : rawStepCell 5 64 T R 3 2 21 = true := by decide +kernel
lemma cell_3_2_22 : rawStepCell 5 64 T R 3 2 22 = true := by decide +kernel
lemma cell_3_2_23 : rawStepCell 5 64 T R 3 2 23 = true := by decide +kernel
lemma cell_3_2_24 : rawStepCell 5 64 T R 3 2 24 = true := by decide +kernel
lemma cell_3_2_25 : rawStepCell 5 64 T R 3 2 25 = true := by decide +kernel
lemma cell_3_2_26 : rawStepCell 5 64 T R 3 2 26 = true := by decide +kernel
lemma cell_3_2_27 : rawStepCell 5 64 T R 3 2 27 = true := by decide +kernel
lemma cell_3_2_28 : rawStepCell 5 64 T R 3 2 28 = true := by decide +kernel
lemma cell_3_2_29 : rawStepCell 5 64 T R 3 2 29 = true := by decide +kernel
lemma cell_3_2_30 : rawStepCell 5 64 T R 3 2 30 = true := by decide +kernel
lemma cell_3_2_31 : rawStepCell 5 64 T R 3 2 31 = true := by decide +kernel
lemma cell_3_2_32 : rawStepCell 5 64 T R 3 2 32 = true := by decide +kernel
lemma cell_3_2_33 : rawStepCell 5 64 T R 3 2 33 = true := by decide +kernel
lemma cell_3_2_34 : rawStepCell 5 64 T R 3 2 34 = true := by decide +kernel
lemma cell_3_2_35 : rawStepCell 5 64 T R 3 2 35 = true := by decide +kernel
lemma cell_3_2_36 : rawStepCell 5 64 T R 3 2 36 = true := by decide +kernel
lemma cell_3_2_37 : rawStepCell 5 64 T R 3 2 37 = true := by decide +kernel
lemma cell_3_2_38 : rawStepCell 5 64 T R 3 2 38 = true := by decide +kernel
lemma cell_3_2_39 : rawStepCell 5 64 T R 3 2 39 = true := by decide +kernel
lemma cell_3_2_40 : rawStepCell 5 64 T R 3 2 40 = true := by decide +kernel
lemma cell_3_2_41 : rawStepCell 5 64 T R 3 2 41 = true := by decide +kernel
lemma cell_3_2_42 : rawStepCell 5 64 T R 3 2 42 = true := by decide +kernel
lemma cell_3_2_43 : rawStepCell 5 64 T R 3 2 43 = true := by decide +kernel
lemma cell_3_2_44 : rawStepCell 5 64 T R 3 2 44 = true := by decide +kernel
lemma cell_3_2_45 : rawStepCell 5 64 T R 3 2 45 = true := by decide +kernel
lemma cell_3_2_46 : rawStepCell 5 64 T R 3 2 46 = true := by decide +kernel
lemma cell_3_2_47 : rawStepCell 5 64 T R 3 2 47 = true := by decide +kernel
lemma cell_3_2_48 : rawStepCell 5 64 T R 3 2 48 = true := by decide +kernel
lemma cell_3_2_49 : rawStepCell 5 64 T R 3 2 49 = true := by decide +kernel
lemma cell_3_2_50 : rawStepCell 5 64 T R 3 2 50 = true := by decide +kernel
lemma cell_3_2_51 : rawStepCell 5 64 T R 3 2 51 = true := by decide +kernel
lemma cell_3_2_52 : rawStepCell 5 64 T R 3 2 52 = true := by decide +kernel
lemma cell_3_2_53 : rawStepCell 5 64 T R 3 2 53 = true := by decide +kernel
lemma cell_3_2_54 : rawStepCell 5 64 T R 3 2 54 = true := by decide +kernel
lemma cell_3_2_55 : rawStepCell 5 64 T R 3 2 55 = true := by decide +kernel
lemma cell_3_2_56 : rawStepCell 5 64 T R 3 2 56 = true := by decide +kernel
lemma cell_3_2_57 : rawStepCell 5 64 T R 3 2 57 = true := by decide +kernel
lemma cell_3_2_58 : rawStepCell 5 64 T R 3 2 58 = true := by decide +kernel
lemma cell_3_2_59 : rawStepCell 5 64 T R 3 2 59 = true := by decide +kernel
lemma cell_3_2_60 : rawStepCell 5 64 T R 3 2 60 = true := by decide +kernel
lemma cell_3_2_61 : rawStepCell 5 64 T R 3 2 61 = true := by decide +kernel
lemma cell_3_2_62 : rawStepCell 5 64 T R 3 2 62 = true := by decide +kernel
lemma cell_3_2_63 : rawStepCell 5 64 T R 3 2 63 = true := by decide +kernel
lemma digit_3_0 : allBelow 64 (rawStepCell 5 64 T R 3 0) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 3 0) = true from rfl)) cell_3_0_0) cell_3_0_1) cell_3_0_2) cell_3_0_3) cell_3_0_4) cell_3_0_5) cell_3_0_6) cell_3_0_7) cell_3_0_8) cell_3_0_9) cell_3_0_10) cell_3_0_11) cell_3_0_12) cell_3_0_13) cell_3_0_14) cell_3_0_15) cell_3_0_16) cell_3_0_17) cell_3_0_18) cell_3_0_19) cell_3_0_20) cell_3_0_21) cell_3_0_22) cell_3_0_23) cell_3_0_24) cell_3_0_25) cell_3_0_26) cell_3_0_27) cell_3_0_28) cell_3_0_29) cell_3_0_30) cell_3_0_31) cell_3_0_32) cell_3_0_33) cell_3_0_34) cell_3_0_35) cell_3_0_36) cell_3_0_37) cell_3_0_38) cell_3_0_39) cell_3_0_40) cell_3_0_41) cell_3_0_42) cell_3_0_43) cell_3_0_44) cell_3_0_45) cell_3_0_46) cell_3_0_47) cell_3_0_48) cell_3_0_49) cell_3_0_50) cell_3_0_51) cell_3_0_52) cell_3_0_53) cell_3_0_54) cell_3_0_55) cell_3_0_56) cell_3_0_57) cell_3_0_58) cell_3_0_59) cell_3_0_60) cell_3_0_61) cell_3_0_62) cell_3_0_63
lemma digit_3_1 : allBelow 64 (rawStepCell 5 64 T R 3 1) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 3 1) = true from rfl)) cell_3_1_0) cell_3_1_1) cell_3_1_2) cell_3_1_3) cell_3_1_4) cell_3_1_5) cell_3_1_6) cell_3_1_7) cell_3_1_8) cell_3_1_9) cell_3_1_10) cell_3_1_11) cell_3_1_12) cell_3_1_13) cell_3_1_14) cell_3_1_15) cell_3_1_16) cell_3_1_17) cell_3_1_18) cell_3_1_19) cell_3_1_20) cell_3_1_21) cell_3_1_22) cell_3_1_23) cell_3_1_24) cell_3_1_25) cell_3_1_26) cell_3_1_27) cell_3_1_28) cell_3_1_29) cell_3_1_30) cell_3_1_31) cell_3_1_32) cell_3_1_33) cell_3_1_34) cell_3_1_35) cell_3_1_36) cell_3_1_37) cell_3_1_38) cell_3_1_39) cell_3_1_40) cell_3_1_41) cell_3_1_42) cell_3_1_43) cell_3_1_44) cell_3_1_45) cell_3_1_46) cell_3_1_47) cell_3_1_48) cell_3_1_49) cell_3_1_50) cell_3_1_51) cell_3_1_52) cell_3_1_53) cell_3_1_54) cell_3_1_55) cell_3_1_56) cell_3_1_57) cell_3_1_58) cell_3_1_59) cell_3_1_60) cell_3_1_61) cell_3_1_62) cell_3_1_63
lemma digit_3_2 : allBelow 64 (rawStepCell 5 64 T R 3 2) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 3 2) = true from rfl)) cell_3_2_0) cell_3_2_1) cell_3_2_2) cell_3_2_3) cell_3_2_4) cell_3_2_5) cell_3_2_6) cell_3_2_7) cell_3_2_8) cell_3_2_9) cell_3_2_10) cell_3_2_11) cell_3_2_12) cell_3_2_13) cell_3_2_14) cell_3_2_15) cell_3_2_16) cell_3_2_17) cell_3_2_18) cell_3_2_19) cell_3_2_20) cell_3_2_21) cell_3_2_22) cell_3_2_23) cell_3_2_24) cell_3_2_25) cell_3_2_26) cell_3_2_27) cell_3_2_28) cell_3_2_29) cell_3_2_30) cell_3_2_31) cell_3_2_32) cell_3_2_33) cell_3_2_34) cell_3_2_35) cell_3_2_36) cell_3_2_37) cell_3_2_38) cell_3_2_39) cell_3_2_40) cell_3_2_41) cell_3_2_42) cell_3_2_43) cell_3_2_44) cell_3_2_45) cell_3_2_46) cell_3_2_47) cell_3_2_48) cell_3_2_49) cell_3_2_50) cell_3_2_51) cell_3_2_52) cell_3_2_53) cell_3_2_54) cell_3_2_55) cell_3_2_56) cell_3_2_57) cell_3_2_58) cell_3_2_59) cell_3_2_60) cell_3_2_61) cell_3_2_62) cell_3_2_63
lemma row_3 : rawStepRow 5 64 T R 3 = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (fun d => allBelow 64 (rawStepCell 5 64 T R 3 d)) = true from rfl)) digit_3_0) digit_3_1) digit_3_2
lemma cell_4_0_0 : rawStepCell 5 64 T R 4 0 0 = true := by decide +kernel
lemma cell_4_0_1 : rawStepCell 5 64 T R 4 0 1 = true := by decide +kernel
lemma cell_4_0_2 : rawStepCell 5 64 T R 4 0 2 = true := by decide +kernel
lemma cell_4_0_3 : rawStepCell 5 64 T R 4 0 3 = true := by decide +kernel
lemma cell_4_0_4 : rawStepCell 5 64 T R 4 0 4 = true := by decide +kernel
lemma cell_4_0_5 : rawStepCell 5 64 T R 4 0 5 = true := by decide +kernel
lemma cell_4_0_6 : rawStepCell 5 64 T R 4 0 6 = true := by decide +kernel
lemma cell_4_0_7 : rawStepCell 5 64 T R 4 0 7 = true := by decide +kernel
lemma cell_4_0_8 : rawStepCell 5 64 T R 4 0 8 = true := by decide +kernel
lemma cell_4_0_9 : rawStepCell 5 64 T R 4 0 9 = true := by decide +kernel
lemma cell_4_0_10 : rawStepCell 5 64 T R 4 0 10 = true := by decide +kernel
lemma cell_4_0_11 : rawStepCell 5 64 T R 4 0 11 = true := by decide +kernel
lemma cell_4_0_12 : rawStepCell 5 64 T R 4 0 12 = true := by decide +kernel
lemma cell_4_0_13 : rawStepCell 5 64 T R 4 0 13 = true := by decide +kernel
lemma cell_4_0_14 : rawStepCell 5 64 T R 4 0 14 = true := by decide +kernel
lemma cell_4_0_15 : rawStepCell 5 64 T R 4 0 15 = true := by decide +kernel
lemma cell_4_0_16 : rawStepCell 5 64 T R 4 0 16 = true := by decide +kernel
lemma cell_4_0_17 : rawStepCell 5 64 T R 4 0 17 = true := by decide +kernel
lemma cell_4_0_18 : rawStepCell 5 64 T R 4 0 18 = true := by decide +kernel
lemma cell_4_0_19 : rawStepCell 5 64 T R 4 0 19 = true := by decide +kernel
lemma cell_4_0_20 : rawStepCell 5 64 T R 4 0 20 = true := by decide +kernel
lemma cell_4_0_21 : rawStepCell 5 64 T R 4 0 21 = true := by decide +kernel
lemma cell_4_0_22 : rawStepCell 5 64 T R 4 0 22 = true := by decide +kernel
lemma cell_4_0_23 : rawStepCell 5 64 T R 4 0 23 = true := by decide +kernel
lemma cell_4_0_24 : rawStepCell 5 64 T R 4 0 24 = true := by decide +kernel
lemma cell_4_0_25 : rawStepCell 5 64 T R 4 0 25 = true := by decide +kernel
lemma cell_4_0_26 : rawStepCell 5 64 T R 4 0 26 = true := by decide +kernel
lemma cell_4_0_27 : rawStepCell 5 64 T R 4 0 27 = true := by decide +kernel
lemma cell_4_0_28 : rawStepCell 5 64 T R 4 0 28 = true := by decide +kernel
lemma cell_4_0_29 : rawStepCell 5 64 T R 4 0 29 = true := by decide +kernel
lemma cell_4_0_30 : rawStepCell 5 64 T R 4 0 30 = true := by decide +kernel
lemma cell_4_0_31 : rawStepCell 5 64 T R 4 0 31 = true := by decide +kernel
lemma cell_4_0_32 : rawStepCell 5 64 T R 4 0 32 = true := by decide +kernel
lemma cell_4_0_33 : rawStepCell 5 64 T R 4 0 33 = true := by decide +kernel
lemma cell_4_0_34 : rawStepCell 5 64 T R 4 0 34 = true := by decide +kernel
lemma cell_4_0_35 : rawStepCell 5 64 T R 4 0 35 = true := by decide +kernel
lemma cell_4_0_36 : rawStepCell 5 64 T R 4 0 36 = true := by decide +kernel
lemma cell_4_0_37 : rawStepCell 5 64 T R 4 0 37 = true := by decide +kernel
lemma cell_4_0_38 : rawStepCell 5 64 T R 4 0 38 = true := by decide +kernel
lemma cell_4_0_39 : rawStepCell 5 64 T R 4 0 39 = true := by decide +kernel
lemma cell_4_0_40 : rawStepCell 5 64 T R 4 0 40 = true := by decide +kernel
lemma cell_4_0_41 : rawStepCell 5 64 T R 4 0 41 = true := by decide +kernel
lemma cell_4_0_42 : rawStepCell 5 64 T R 4 0 42 = true := by decide +kernel
lemma cell_4_0_43 : rawStepCell 5 64 T R 4 0 43 = true := by decide +kernel
lemma cell_4_0_44 : rawStepCell 5 64 T R 4 0 44 = true := by decide +kernel
lemma cell_4_0_45 : rawStepCell 5 64 T R 4 0 45 = true := by decide +kernel
lemma cell_4_0_46 : rawStepCell 5 64 T R 4 0 46 = true := by decide +kernel
lemma cell_4_0_47 : rawStepCell 5 64 T R 4 0 47 = true := by decide +kernel
lemma cell_4_0_48 : rawStepCell 5 64 T R 4 0 48 = true := by decide +kernel
lemma cell_4_0_49 : rawStepCell 5 64 T R 4 0 49 = true := by decide +kernel
lemma cell_4_0_50 : rawStepCell 5 64 T R 4 0 50 = true := by decide +kernel
lemma cell_4_0_51 : rawStepCell 5 64 T R 4 0 51 = true := by decide +kernel
lemma cell_4_0_52 : rawStepCell 5 64 T R 4 0 52 = true := by decide +kernel
lemma cell_4_0_53 : rawStepCell 5 64 T R 4 0 53 = true := by decide +kernel
lemma cell_4_0_54 : rawStepCell 5 64 T R 4 0 54 = true := by decide +kernel
lemma cell_4_0_55 : rawStepCell 5 64 T R 4 0 55 = true := by decide +kernel
lemma cell_4_0_56 : rawStepCell 5 64 T R 4 0 56 = true := by decide +kernel
lemma cell_4_0_57 : rawStepCell 5 64 T R 4 0 57 = true := by decide +kernel
lemma cell_4_0_58 : rawStepCell 5 64 T R 4 0 58 = true := by decide +kernel
lemma cell_4_0_59 : rawStepCell 5 64 T R 4 0 59 = true := by decide +kernel
lemma cell_4_0_60 : rawStepCell 5 64 T R 4 0 60 = true := by decide +kernel
lemma cell_4_0_61 : rawStepCell 5 64 T R 4 0 61 = true := by decide +kernel
lemma cell_4_0_62 : rawStepCell 5 64 T R 4 0 62 = true := by decide +kernel
lemma cell_4_0_63 : rawStepCell 5 64 T R 4 0 63 = true := by decide +kernel
lemma cell_4_1_0 : rawStepCell 5 64 T R 4 1 0 = true := by decide +kernel
lemma cell_4_1_1 : rawStepCell 5 64 T R 4 1 1 = true := by decide +kernel
lemma cell_4_1_2 : rawStepCell 5 64 T R 4 1 2 = true := by decide +kernel
lemma cell_4_1_3 : rawStepCell 5 64 T R 4 1 3 = true := by decide +kernel
lemma cell_4_1_4 : rawStepCell 5 64 T R 4 1 4 = true := by decide +kernel
lemma cell_4_1_5 : rawStepCell 5 64 T R 4 1 5 = true := by decide +kernel
lemma cell_4_1_6 : rawStepCell 5 64 T R 4 1 6 = true := by decide +kernel
lemma cell_4_1_7 : rawStepCell 5 64 T R 4 1 7 = true := by decide +kernel
lemma cell_4_1_8 : rawStepCell 5 64 T R 4 1 8 = true := by decide +kernel
lemma cell_4_1_9 : rawStepCell 5 64 T R 4 1 9 = true := by decide +kernel
lemma cell_4_1_10 : rawStepCell 5 64 T R 4 1 10 = true := by decide +kernel
lemma cell_4_1_11 : rawStepCell 5 64 T R 4 1 11 = true := by decide +kernel
lemma cell_4_1_12 : rawStepCell 5 64 T R 4 1 12 = true := by decide +kernel
lemma cell_4_1_13 : rawStepCell 5 64 T R 4 1 13 = true := by decide +kernel
lemma cell_4_1_14 : rawStepCell 5 64 T R 4 1 14 = true := by decide +kernel
lemma cell_4_1_15 : rawStepCell 5 64 T R 4 1 15 = true := by decide +kernel
lemma cell_4_1_16 : rawStepCell 5 64 T R 4 1 16 = true := by decide +kernel
lemma cell_4_1_17 : rawStepCell 5 64 T R 4 1 17 = true := by decide +kernel
lemma cell_4_1_18 : rawStepCell 5 64 T R 4 1 18 = true := by decide +kernel
lemma cell_4_1_19 : rawStepCell 5 64 T R 4 1 19 = true := by decide +kernel
lemma cell_4_1_20 : rawStepCell 5 64 T R 4 1 20 = true := by decide +kernel
lemma cell_4_1_21 : rawStepCell 5 64 T R 4 1 21 = true := by decide +kernel
lemma cell_4_1_22 : rawStepCell 5 64 T R 4 1 22 = true := by decide +kernel
lemma cell_4_1_23 : rawStepCell 5 64 T R 4 1 23 = true := by decide +kernel
lemma cell_4_1_24 : rawStepCell 5 64 T R 4 1 24 = true := by decide +kernel
lemma cell_4_1_25 : rawStepCell 5 64 T R 4 1 25 = true := by decide +kernel
lemma cell_4_1_26 : rawStepCell 5 64 T R 4 1 26 = true := by decide +kernel
lemma cell_4_1_27 : rawStepCell 5 64 T R 4 1 27 = true := by decide +kernel
lemma cell_4_1_28 : rawStepCell 5 64 T R 4 1 28 = true := by decide +kernel
lemma cell_4_1_29 : rawStepCell 5 64 T R 4 1 29 = true := by decide +kernel
lemma cell_4_1_30 : rawStepCell 5 64 T R 4 1 30 = true := by decide +kernel
lemma cell_4_1_31 : rawStepCell 5 64 T R 4 1 31 = true := by decide +kernel
lemma cell_4_1_32 : rawStepCell 5 64 T R 4 1 32 = true := by decide +kernel
lemma cell_4_1_33 : rawStepCell 5 64 T R 4 1 33 = true := by decide +kernel
lemma cell_4_1_34 : rawStepCell 5 64 T R 4 1 34 = true := by decide +kernel
lemma cell_4_1_35 : rawStepCell 5 64 T R 4 1 35 = true := by decide +kernel
lemma cell_4_1_36 : rawStepCell 5 64 T R 4 1 36 = true := by decide +kernel
lemma cell_4_1_37 : rawStepCell 5 64 T R 4 1 37 = true := by decide +kernel
lemma cell_4_1_38 : rawStepCell 5 64 T R 4 1 38 = true := by decide +kernel
lemma cell_4_1_39 : rawStepCell 5 64 T R 4 1 39 = true := by decide +kernel
lemma cell_4_1_40 : rawStepCell 5 64 T R 4 1 40 = true := by decide +kernel
lemma cell_4_1_41 : rawStepCell 5 64 T R 4 1 41 = true := by decide +kernel
lemma cell_4_1_42 : rawStepCell 5 64 T R 4 1 42 = true := by decide +kernel
lemma cell_4_1_43 : rawStepCell 5 64 T R 4 1 43 = true := by decide +kernel
lemma cell_4_1_44 : rawStepCell 5 64 T R 4 1 44 = true := by decide +kernel
lemma cell_4_1_45 : rawStepCell 5 64 T R 4 1 45 = true := by decide +kernel
lemma cell_4_1_46 : rawStepCell 5 64 T R 4 1 46 = true := by decide +kernel
lemma cell_4_1_47 : rawStepCell 5 64 T R 4 1 47 = true := by decide +kernel
lemma cell_4_1_48 : rawStepCell 5 64 T R 4 1 48 = true := by decide +kernel
lemma cell_4_1_49 : rawStepCell 5 64 T R 4 1 49 = true := by decide +kernel
lemma cell_4_1_50 : rawStepCell 5 64 T R 4 1 50 = true := by decide +kernel
lemma cell_4_1_51 : rawStepCell 5 64 T R 4 1 51 = true := by decide +kernel
lemma cell_4_1_52 : rawStepCell 5 64 T R 4 1 52 = true := by decide +kernel
lemma cell_4_1_53 : rawStepCell 5 64 T R 4 1 53 = true := by decide +kernel
lemma cell_4_1_54 : rawStepCell 5 64 T R 4 1 54 = true := by decide +kernel
lemma cell_4_1_55 : rawStepCell 5 64 T R 4 1 55 = true := by decide +kernel
lemma cell_4_1_56 : rawStepCell 5 64 T R 4 1 56 = true := by decide +kernel
lemma cell_4_1_57 : rawStepCell 5 64 T R 4 1 57 = true := by decide +kernel
lemma cell_4_1_58 : rawStepCell 5 64 T R 4 1 58 = true := by decide +kernel
lemma cell_4_1_59 : rawStepCell 5 64 T R 4 1 59 = true := by decide +kernel
lemma cell_4_1_60 : rawStepCell 5 64 T R 4 1 60 = true := by decide +kernel
lemma cell_4_1_61 : rawStepCell 5 64 T R 4 1 61 = true := by decide +kernel
lemma cell_4_1_62 : rawStepCell 5 64 T R 4 1 62 = true := by decide +kernel
lemma cell_4_1_63 : rawStepCell 5 64 T R 4 1 63 = true := by decide +kernel
lemma cell_4_2_0 : rawStepCell 5 64 T R 4 2 0 = true := by decide +kernel
lemma cell_4_2_1 : rawStepCell 5 64 T R 4 2 1 = true := by decide +kernel
lemma cell_4_2_2 : rawStepCell 5 64 T R 4 2 2 = true := by decide +kernel
lemma cell_4_2_3 : rawStepCell 5 64 T R 4 2 3 = true := by decide +kernel
lemma cell_4_2_4 : rawStepCell 5 64 T R 4 2 4 = true := by decide +kernel
lemma cell_4_2_5 : rawStepCell 5 64 T R 4 2 5 = true := by decide +kernel
lemma cell_4_2_6 : rawStepCell 5 64 T R 4 2 6 = true := by decide +kernel
lemma cell_4_2_7 : rawStepCell 5 64 T R 4 2 7 = true := by decide +kernel
lemma cell_4_2_8 : rawStepCell 5 64 T R 4 2 8 = true := by decide +kernel
lemma cell_4_2_9 : rawStepCell 5 64 T R 4 2 9 = true := by decide +kernel
lemma cell_4_2_10 : rawStepCell 5 64 T R 4 2 10 = true := by decide +kernel
lemma cell_4_2_11 : rawStepCell 5 64 T R 4 2 11 = true := by decide +kernel
lemma cell_4_2_12 : rawStepCell 5 64 T R 4 2 12 = true := by decide +kernel
lemma cell_4_2_13 : rawStepCell 5 64 T R 4 2 13 = true := by decide +kernel
lemma cell_4_2_14 : rawStepCell 5 64 T R 4 2 14 = true := by decide +kernel
lemma cell_4_2_15 : rawStepCell 5 64 T R 4 2 15 = true := by decide +kernel
lemma cell_4_2_16 : rawStepCell 5 64 T R 4 2 16 = true := by decide +kernel
lemma cell_4_2_17 : rawStepCell 5 64 T R 4 2 17 = true := by decide +kernel
lemma cell_4_2_18 : rawStepCell 5 64 T R 4 2 18 = true := by decide +kernel
lemma cell_4_2_19 : rawStepCell 5 64 T R 4 2 19 = true := by decide +kernel
lemma cell_4_2_20 : rawStepCell 5 64 T R 4 2 20 = true := by decide +kernel
lemma cell_4_2_21 : rawStepCell 5 64 T R 4 2 21 = true := by decide +kernel
lemma cell_4_2_22 : rawStepCell 5 64 T R 4 2 22 = true := by decide +kernel
lemma cell_4_2_23 : rawStepCell 5 64 T R 4 2 23 = true := by decide +kernel
lemma cell_4_2_24 : rawStepCell 5 64 T R 4 2 24 = true := by decide +kernel
lemma cell_4_2_25 : rawStepCell 5 64 T R 4 2 25 = true := by decide +kernel
lemma cell_4_2_26 : rawStepCell 5 64 T R 4 2 26 = true := by decide +kernel
lemma cell_4_2_27 : rawStepCell 5 64 T R 4 2 27 = true := by decide +kernel
lemma cell_4_2_28 : rawStepCell 5 64 T R 4 2 28 = true := by decide +kernel
lemma cell_4_2_29 : rawStepCell 5 64 T R 4 2 29 = true := by decide +kernel
lemma cell_4_2_30 : rawStepCell 5 64 T R 4 2 30 = true := by decide +kernel
lemma cell_4_2_31 : rawStepCell 5 64 T R 4 2 31 = true := by decide +kernel
lemma cell_4_2_32 : rawStepCell 5 64 T R 4 2 32 = true := by decide +kernel
lemma cell_4_2_33 : rawStepCell 5 64 T R 4 2 33 = true := by decide +kernel
lemma cell_4_2_34 : rawStepCell 5 64 T R 4 2 34 = true := by decide +kernel
lemma cell_4_2_35 : rawStepCell 5 64 T R 4 2 35 = true := by decide +kernel
lemma cell_4_2_36 : rawStepCell 5 64 T R 4 2 36 = true := by decide +kernel
lemma cell_4_2_37 : rawStepCell 5 64 T R 4 2 37 = true := by decide +kernel
lemma cell_4_2_38 : rawStepCell 5 64 T R 4 2 38 = true := by decide +kernel
lemma cell_4_2_39 : rawStepCell 5 64 T R 4 2 39 = true := by decide +kernel
lemma cell_4_2_40 : rawStepCell 5 64 T R 4 2 40 = true := by decide +kernel
lemma cell_4_2_41 : rawStepCell 5 64 T R 4 2 41 = true := by decide +kernel
lemma cell_4_2_42 : rawStepCell 5 64 T R 4 2 42 = true := by decide +kernel
lemma cell_4_2_43 : rawStepCell 5 64 T R 4 2 43 = true := by decide +kernel
lemma cell_4_2_44 : rawStepCell 5 64 T R 4 2 44 = true := by decide +kernel
lemma cell_4_2_45 : rawStepCell 5 64 T R 4 2 45 = true := by decide +kernel
lemma cell_4_2_46 : rawStepCell 5 64 T R 4 2 46 = true := by decide +kernel
lemma cell_4_2_47 : rawStepCell 5 64 T R 4 2 47 = true := by decide +kernel
lemma cell_4_2_48 : rawStepCell 5 64 T R 4 2 48 = true := by decide +kernel
lemma cell_4_2_49 : rawStepCell 5 64 T R 4 2 49 = true := by decide +kernel
lemma cell_4_2_50 : rawStepCell 5 64 T R 4 2 50 = true := by decide +kernel
lemma cell_4_2_51 : rawStepCell 5 64 T R 4 2 51 = true := by decide +kernel
lemma cell_4_2_52 : rawStepCell 5 64 T R 4 2 52 = true := by decide +kernel
lemma cell_4_2_53 : rawStepCell 5 64 T R 4 2 53 = true := by decide +kernel
lemma cell_4_2_54 : rawStepCell 5 64 T R 4 2 54 = true := by decide +kernel
lemma cell_4_2_55 : rawStepCell 5 64 T R 4 2 55 = true := by decide +kernel
lemma cell_4_2_56 : rawStepCell 5 64 T R 4 2 56 = true := by decide +kernel
lemma cell_4_2_57 : rawStepCell 5 64 T R 4 2 57 = true := by decide +kernel
lemma cell_4_2_58 : rawStepCell 5 64 T R 4 2 58 = true := by decide +kernel
lemma cell_4_2_59 : rawStepCell 5 64 T R 4 2 59 = true := by decide +kernel
lemma cell_4_2_60 : rawStepCell 5 64 T R 4 2 60 = true := by decide +kernel
lemma cell_4_2_61 : rawStepCell 5 64 T R 4 2 61 = true := by decide +kernel
lemma cell_4_2_62 : rawStepCell 5 64 T R 4 2 62 = true := by decide +kernel
lemma cell_4_2_63 : rawStepCell 5 64 T R 4 2 63 = true := by decide +kernel
lemma digit_4_0 : allBelow 64 (rawStepCell 5 64 T R 4 0) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 4 0) = true from rfl)) cell_4_0_0) cell_4_0_1) cell_4_0_2) cell_4_0_3) cell_4_0_4) cell_4_0_5) cell_4_0_6) cell_4_0_7) cell_4_0_8) cell_4_0_9) cell_4_0_10) cell_4_0_11) cell_4_0_12) cell_4_0_13) cell_4_0_14) cell_4_0_15) cell_4_0_16) cell_4_0_17) cell_4_0_18) cell_4_0_19) cell_4_0_20) cell_4_0_21) cell_4_0_22) cell_4_0_23) cell_4_0_24) cell_4_0_25) cell_4_0_26) cell_4_0_27) cell_4_0_28) cell_4_0_29) cell_4_0_30) cell_4_0_31) cell_4_0_32) cell_4_0_33) cell_4_0_34) cell_4_0_35) cell_4_0_36) cell_4_0_37) cell_4_0_38) cell_4_0_39) cell_4_0_40) cell_4_0_41) cell_4_0_42) cell_4_0_43) cell_4_0_44) cell_4_0_45) cell_4_0_46) cell_4_0_47) cell_4_0_48) cell_4_0_49) cell_4_0_50) cell_4_0_51) cell_4_0_52) cell_4_0_53) cell_4_0_54) cell_4_0_55) cell_4_0_56) cell_4_0_57) cell_4_0_58) cell_4_0_59) cell_4_0_60) cell_4_0_61) cell_4_0_62) cell_4_0_63
lemma digit_4_1 : allBelow 64 (rawStepCell 5 64 T R 4 1) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 4 1) = true from rfl)) cell_4_1_0) cell_4_1_1) cell_4_1_2) cell_4_1_3) cell_4_1_4) cell_4_1_5) cell_4_1_6) cell_4_1_7) cell_4_1_8) cell_4_1_9) cell_4_1_10) cell_4_1_11) cell_4_1_12) cell_4_1_13) cell_4_1_14) cell_4_1_15) cell_4_1_16) cell_4_1_17) cell_4_1_18) cell_4_1_19) cell_4_1_20) cell_4_1_21) cell_4_1_22) cell_4_1_23) cell_4_1_24) cell_4_1_25) cell_4_1_26) cell_4_1_27) cell_4_1_28) cell_4_1_29) cell_4_1_30) cell_4_1_31) cell_4_1_32) cell_4_1_33) cell_4_1_34) cell_4_1_35) cell_4_1_36) cell_4_1_37) cell_4_1_38) cell_4_1_39) cell_4_1_40) cell_4_1_41) cell_4_1_42) cell_4_1_43) cell_4_1_44) cell_4_1_45) cell_4_1_46) cell_4_1_47) cell_4_1_48) cell_4_1_49) cell_4_1_50) cell_4_1_51) cell_4_1_52) cell_4_1_53) cell_4_1_54) cell_4_1_55) cell_4_1_56) cell_4_1_57) cell_4_1_58) cell_4_1_59) cell_4_1_60) cell_4_1_61) cell_4_1_62) cell_4_1_63
lemma digit_4_2 : allBelow 64 (rawStepCell 5 64 T R 4 2) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepCell 5 64 T R 4 2) = true from rfl)) cell_4_2_0) cell_4_2_1) cell_4_2_2) cell_4_2_3) cell_4_2_4) cell_4_2_5) cell_4_2_6) cell_4_2_7) cell_4_2_8) cell_4_2_9) cell_4_2_10) cell_4_2_11) cell_4_2_12) cell_4_2_13) cell_4_2_14) cell_4_2_15) cell_4_2_16) cell_4_2_17) cell_4_2_18) cell_4_2_19) cell_4_2_20) cell_4_2_21) cell_4_2_22) cell_4_2_23) cell_4_2_24) cell_4_2_25) cell_4_2_26) cell_4_2_27) cell_4_2_28) cell_4_2_29) cell_4_2_30) cell_4_2_31) cell_4_2_32) cell_4_2_33) cell_4_2_34) cell_4_2_35) cell_4_2_36) cell_4_2_37) cell_4_2_38) cell_4_2_39) cell_4_2_40) cell_4_2_41) cell_4_2_42) cell_4_2_43) cell_4_2_44) cell_4_2_45) cell_4_2_46) cell_4_2_47) cell_4_2_48) cell_4_2_49) cell_4_2_50) cell_4_2_51) cell_4_2_52) cell_4_2_53) cell_4_2_54) cell_4_2_55) cell_4_2_56) cell_4_2_57) cell_4_2_58) cell_4_2_59) cell_4_2_60) cell_4_2_61) cell_4_2_62) cell_4_2_63
lemma row_4 : rawStepRow 5 64 T R 4 = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (fun d => allBelow 64 (rawStepCell 5 64 T R 4 d)) = true from rfl)) digit_4_0) digit_4_1) digit_4_2
#print axioms row_4
lemma checked_step_raw : allBelow 5 (rawStepRow 5 64 T R) = true :=
  allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro (allBelow_succ_intro ((show allBelow 0 (rawStepRow 5 64 T R) = true from rfl)) row_0) row_1) row_2) row_3) row_4
lemma checked_step : ∀ p d, d < 3 → ∀ c', c' < 64 →
    ∀ r ∈ data.step p ((64 * d + c') % 3),
    ∀ q ∈ data.relation p ((64 * d + c') / 3),
    (data.step q d ∩ data.relation r c').Nonempty := by
  intro p d hd c hc r hr q hq
  exact rawStepRow_sound checked_bound (allBelow_spec checked_step_raw p.isLt) d hd c hc r hr q hq
lemma checked_finish_raw : allBelow 5 (rawFinishRow 14 R) = true := by decide +kernel
lemma checked_finish : ∀ p ∈ data.accept, data.relation p 0 ⊆ data.accept := by
  intro p hp
  exact rawFinishRow_sound (allBelow_spec checked_finish_raw p.isLt) hp
#print axioms checked_step
def simulation := checkedSimulation data 64 (by decide) checked_init checked_step checked_finish

theorem backward (n : ℕ) : acceptsNat data.toNFA (64 * n) → acceptsNat data.toNFA n :=
  simulation.backward n

theorem covers (n : ℕ) (hn : 0 < n) (hg : Nat.digits 3 n ⊆ [0, 1]) :
    acceptsNat data.toNFA n := by
  apply covers_positive_good data.toNFA 1 _ checked_loop checked_accept n hn hg
  change (1 : Fin 5) ∈ data.toNFA.stepSet (data.start : Set (Fin 5)) 1
  rw [← data.stepStates_coe]
  exact checked_first

theorem rejected_seed : ¬ acceptsNat data.toNFA (4 ^ 8) := by
  rintro ⟨p, hp, ha⟩
  rw [← data.evalStates_coe] at hp
  exact Finset.disjoint_left.mp checked_seed hp ha

/-- This excludes ONE exponent class, not all sufficiently large exponents. -/
theorem excludes (j : ℕ) : ¬ Nat.digits 3 (4 ^ (8 + 3 * j)) ⊆ [0, 1] := by
  intro hg
  have hn := simulation.rejects_mul_orbit (4 ^ 8) rejected_seed j
  apply hn
  have he : (64 : ℕ) ^ j * 4 ^ 8 = 4 ^ (8 + 3 * j) := by
    rw [show (64 : ℕ) = 4 ^ 3 by decide, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  exact covers _ (by positivity) hg

#print axioms excludes
end Erdos406StandaloneBitmaskControl
