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


namespace Erdos406StrideExport
open Erdos406BackwardStandalone Erdos406BackwardStrided
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 20000

def maskSet (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun q => m.testBit q.val)
def stepTable : List (List ℕ) := [[1, 6, 8], [2, 2, 0], [4, 4, 8], [4, 16, 8], [4, 4, 8]]
def relationTable : List (List ℕ) := [[29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [12, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [12, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [12, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 21, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29]]
def data : Data (Fin 5) where
  step q d := maskSet 5 ((stepTable.getD q.val []).getD d 0)
  start := {0}
  accept := maskSet 5 14
  relation p c := maskSet 5 ((relationTable.getD p.val []).getD c 0)

lemma checked_init : ∀ c, c < 64 → ∀ p ∈ data.evalStates c,
    (data.start ∩ data.relation p c).Nonempty := by decide +kernel
lemma checked_step : ∀ p d, d < 3 → ∀ c', c' < 64 →
    ∀ r ∈ data.step p ((64 * d + c') % 3),
    ∀ q ∈ data.relation p ((64 * d + c') / 3),
    (data.step q d ∩ data.relation r c').Nonempty := by decide +kernel
lemma checked_finish : ∀ p ∈ data.accept, data.relation p 0 ⊆ data.accept := by decide +kernel
lemma checked_first : (1 : Fin 5) ∈ data.stepStates data.start 1 := by decide +kernel
lemma checked_loop : ∀ d, d < 2 → (1 : Fin 5) ∈ data.step 1 d := by decide +kernel
lemma checked_accept : (1 : Fin 5) ∈ data.accept := by decide +kernel
lemma checked_seed : Disjoint (data.evalStates (4 ^ 8)) data.accept := by decide +kernel

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
end Erdos406StrideExport
