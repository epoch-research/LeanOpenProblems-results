import Submission.IntervalHullSoundness

/-! Exact period-30 integer lower and upper bounds, including compatibility
and soundness for every residue vector at the primes 2,3,5. -/
namespace Erdos970.IntervalRescaling.IntegerHull.WheelThirty

/-- Extend one period with a fixed additive increment. -/
def extend (Q : ℕ) (A : ℤ) (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n / Q : ℕ) * A + f (n % Q)

lemma extend_add_mul (Q : ℕ) (hQ : 0 < Q) (A : ℤ) (f : ℕ → ℤ) (n t : ℕ) :
    extend Q A f (n + Q * t) = extend Q A f n + (t : ℤ) * A := by
  simp only [extend, Nat.add_mul_div_left n t hQ, Nat.add_mul_mod_self_left, Nat.cast_add]
  ring

lemma extend_defect (Q : ℕ) (hQ : 0 < Q) (A : ℤ) (f g : ℕ → ℤ) (m n : ℕ) :
    extend Q A f (m + n) - extend Q A f m - extend Q A g n =
      extend Q A f (m % Q + n % Q) - extend Q A f (m % Q) - extend Q A g (n % Q) := by
  have hm := extend_add_mul Q hQ A f (m % Q) (m / Q)
  have hn := extend_add_mul Q hQ A g (n % Q) (n / Q)
  have hmn := extend_add_mul Q hQ A f (m % Q + n % Q) (m / Q + n / Q)
  rw [Nat.mod_add_div] at hm hn
  have heq : m % Q + n % Q + Q * (m / Q + n / Q) = m + n := by
    have hh₁ := Nat.mod_add_div m Q
    have hh₂ := Nat.mod_add_div n Q
    nlinarith
  rw [heq, Nat.cast_add] at hmn
  rw [hm, hn, hmn]
  ring

def loTable : List ℤ :=
  [0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,6,6,6,6,7,7]

def hiTable : List ℤ :=
  [0,1,1,2,2,2,2,3,3,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,8]

def lo : ℕ → ℤ := extend 30 8 (fun n => loTable[n]!)
def hi : ℕ → ℤ := extend 30 8 (fun n => hiTable[n]!)

private lemma finite_shape : ∀ m n : Fin 30,
    lo n ≤ lo (m + n) - lo m ∧ lo (m + n) - lo m ≤ hi n ∧
    lo n ≤ hi (m + n) - hi m ∧ hi (m + n) - hi m ≤ hi n := by
  decide +kernel

private lemma tables_nonneg : ∀ n : Fin 30, 0 ≤ loTable[n.val]! ∧ 0 ≤ hiTable[n.val]! := by
  decide +kernel

theorem nonneg (n : ℕ) : 0 ≤ lo n ∧ 0 ≤ hi n := by
  have hh := tables_nonneg ⟨n % 30, Nat.mod_lt n (by omega)⟩
  constructor
  · exact add_nonneg (by positivity) hh.1
  · exact add_nonneg (by positivity) hh.2

theorem compatible : Compatible (fun n => (lo n : ℝ)) (fun n => (hi n : ℝ)) := by
  have hshape (m n : ℕ) : lo n ≤ lo (m+n)-lo m ∧ lo (m+n)-lo m ≤ hi n ∧
      lo n ≤ hi (m+n)-hi m ∧ hi (m+n)-hi m ≤ hi n := by
    have hh := finite_shape ⟨m % 30, Nat.mod_lt _ (by omega)⟩
      ⟨n % 30, Nat.mod_lt _ (by omega)⟩
    have hll := extend_defect 30 (by omega) 8 (fun n => loTable[n]!) (fun n => loTable[n]!) m n
    have hlu := extend_defect 30 (by omega) 8 (fun n => loTable[n]!) (fun n => hiTable[n]!) m n
    have hul := extend_defect 30 (by omega) 8 (fun n => hiTable[n]!) (fun n => loTable[n]!) m n
    have huu := extend_defect 30 (by omega) 8 (fun n => hiTable[n]!) (fun n => hiTable[n]!) m n
    change lo (m+n)-lo m-lo n = lo (m%30+n%30)-lo (m%30)-lo (n%30) at hll
    change lo (m+n)-lo m-hi n = lo (m%30+n%30)-lo (m%30)-hi (n%30) at hlu
    change hi (m+n)-hi m-lo n = hi (m%30+n%30)-hi (m%30)-lo (n%30) at hul
    change hi (m+n)-hi m-hi n = hi (m%30+n%30)-hi (m%30)-hi (n%30) at huu
    dsimp only at hh
    omega
  refine ⟨by norm_num [lo, extend, loTable], by norm_num [hi, extend, hiTable],
    fun n => by exact_mod_cast (nonneg n).2, ?_, ?_⟩
  · intro m n
    constructor
    · exact_mod_cast (hshape m n).1
    · exact_mod_cast (hshape m n).2.1
  · intro m n
    exact_mod_cast (hshape m n).2.2


def moduli (i : ℕ) : ℕ := if i = 0 then 2 else if i = 1 then 3 else 5
private def residues (a b c : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then a else if i = 1 then b else c

private theorem finite_bounds : ∀ (a : Fin 2) (b : Fin 3) (c : Fin 5) (n : Fin 31),
    lo n ≤ (count moduli (residues a b c) 3 n : ℤ) ∧
    (count moduli (residues a b c) 3 n : ℤ) ≤ hi n ∧
    (n.val = 30 → count moduli (residues a b c) 3 n = 8) := by
  decide +kernel

private theorem normalized (r : ℕ → ℕ) (m : ℕ) :
    count moduli r 3 m = count moduli (residues (r 0 % 2) (r 1 % 3) (r 2 % 5)) 3 m := by
  simp [count, Nat.forall_lt_succ_right, moduli, residues, Nat.ModEq]

private theorem finite_bounds_all (r : ℕ → ℕ) (m : ℕ) (hm : m ≤ 30) :
    lo m ≤ (count moduli r 3 m : ℤ) ∧ (count moduli r 3 m : ℤ) ≤ hi m ∧
      (m = 30 → count moduli r 3 m = 8) := by
  have hh := finite_bounds ⟨r 0 % 2, Nat.mod_lt _ (by omega)⟩
    ⟨r 1 % 3, Nat.mod_lt _ (by omega)⟩ ⟨r 2 % 5, Nat.mod_lt _ (by omega)⟩ ⟨m, by omega⟩
  simpa only [← normalized r m] using hh

private theorem count_period (r : ℕ → ℕ) (m : ℕ) :
    count moduli r 3 (m + 30) = count moduli r 3 m + 8 := by
  let f : ℕ → Prop := fun x => ∀ j < 3, ¬x ≡ r j [MOD moduli j]
  have hshift : (fun x => f (30 + x)) = f := by
    funext x
    simp [f, Nat.forall_lt_succ_right, moduli, Nat.ModEq, Nat.add_mod]
  have h30 : Nat.count f 30 = 8 := by
    simpa only [f, Nat.count_eq_card_filter_range, count] using
      (finite_bounds_all r 30 le_rfl).2.2 rfl
  simp only [count, ← Nat.count_eq_card_filter_range]
  change Nat.count f (m + 30) = Nat.count f m + 8
  rw [Nat.add_comm m 30, Nat.count_add]
  simp only [hshift, h30]
  omega

lemma lo_period (m : ℕ) : lo (m + 30) = lo m + 8 := by
  simpa only [Nat.mul_one, Nat.cast_one, one_mul] using
    extend_add_mul 30 (by omega) 8 (fun n => loTable[n]!) m 1

lemma hi_period (m : ℕ) : hi (m + 30) = hi m + 8 := by
  simpa only [Nat.mul_one, Nat.cast_one, one_mul] using
    extend_add_mul 30 (by omega) 8 (fun n => hiTable[n]!) m 1

theorem bounds_int (r : ℕ → ℕ) (m : ℕ) :
    lo m ≤ (count moduli r 3 m : ℤ) ∧ (count moduli r 3 m : ℤ) ≤ hi m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 30
    · exact ⟨(finite_bounds_all r m hm).1, (finite_bounds_all r m hm).2.1⟩
    · have hi := ih (m - 30) (by omega)
      have he : m - 30 + 30 = m := by omega
      have hc := count_period r (m - 30)
      have hl := lo_period (m - 30)
      have hu := hi_period (m - 30)
      rw [he] at hc hl hu
      rw [hc, hl, hu]
      push_cast
      omega

theorem bounds : Bounds moduli 3 (fun n => (lo n : ℝ)) (fun n => (hi n : ℝ)) := by
  intro m r
  dsimp only
  exact_mod_cast bounds_int r m


private theorem finite_attainment : ∀ n : Fin 31,
    (∃ (a : Fin 2) (b : Fin 3) (c : Fin 5),
      (count moduli (residues a b c) 3 n : ℤ) = lo n) ∧
    (∃ (a : Fin 2) (b : Fin 3) (c : Fin 5),
      (count moduli (residues a b c) 3 n : ℤ) = hi n) := by
  decide +kernel

/-- Both bounds are attained; the seed is the exact extremal count pair. -/
theorem attained (m : ℕ) :
    (∃ r, (count moduli r 3 m : ℤ) = lo m) ∧
    (∃ r, (count moduli r 3 m : ℤ) = hi m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 30
    · obtain ⟨⟨a,b,c,hlo⟩, ⟨d,e,f,hhi⟩⟩ := finite_attainment ⟨m, by omega⟩
      exact ⟨⟨residues a b c, hlo⟩, ⟨residues d e f, hhi⟩⟩
    · obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := ih (m - 30) (by omega)
      have he : m - 30 + 30 = m := by omega
      refine ⟨⟨r, ?_⟩, ⟨s, ?_⟩⟩
      · rw [← he, count_period, lo_period]
        push_cast
        rw [hr]
      · rw [← he, count_period, hi_period]
        push_cast
        rw [hs]

#print axioms compatible
#print axioms bounds
#print axioms attained
end Erdos970.IntervalRescaling.IntegerHull.WheelThirty
