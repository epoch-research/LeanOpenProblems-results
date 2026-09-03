import Submission.SieveInfiniteUniqueness

/-! Walk bounds and detours in the complement of a finite box. -/
namespace Erdos952Investigation.PeriodicSieveEnds
open FiniteSieveReduction PeriodicSieveComponents SieveInfiniteUniqueness PeriodicSievePlanarity
set_option maxHeartbeats 0

def Outside (R : ℤ) (z : GaussianInt) : Prop := R < |z.re| ∨ R < |z.im|

def shift (N : ℕ) (k l : ℤ) : GaussianInt := ⟨(N.factorial : ℤ)*k,(N.factorial : ℤ)*l⟩

lemma shift_period (N : ℕ) (k l : ℤ) : IsPeriod N (shift N k l) :=
  ⟨dvd_mul_right _ _,dvd_mul_right _ _⟩

lemma shift_zero (N : ℕ) : shift N 0 0 = 0 := by
  apply Zsqrtd.ext <;> simp [shift]

lemma shift_x_succ (N : ℕ) (k l : ℤ) : shift N 1 0+shift N k l = shift N (k+1) l := by
  apply Zsqrtd.ext <;> simp [shift] <;> ring

lemma shift_y_succ (N : ℕ) (k l : ℤ) : shift N 0 1+shift N k l = shift N k (l+1) := by
  apply Zsqrtd.ext <;> simp [shift] <;> ring

def walkRadius {G : SimpleGraph GaussianInt} {a b : GaussianInt} : G.Walk a b → ℤ
  | .nil => max |a.re| |a.im|
  | .cons _ p => max (max |a.re| |a.im|) (walkRadius p)

lemma walkRadius_nonneg {G : SimpleGraph GaussianInt} {a b : GaussianInt} (p : G.Walk a b) :
    0 ≤ walkRadius p := by
  cases p with
  | nil => exact (abs_nonneg _).trans (le_max_left _ _)
  | cons h p => exact ((abs_nonneg _).trans (le_max_left _ _)).trans (le_max_left _ _)

lemma coordinates_le_walkRadius {G : SimpleGraph GaussianInt} {a b : GaussianInt}
    (p : G.Walk a b) {v : GaussianInt} (hv : v ∈ p.support) :
    |v.re| ≤ walkRadius p ∧ |v.im| ≤ walkRadius p := by
  induction p with
  | @nil a =>
    have he : v = a := by simpa using hv
    subst v
    exact ⟨le_max_left _ _,le_max_right _ _⟩
  | @cons a b c hab p ih =>
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨(le_max_left _ _).trans (le_max_left _ _),(le_max_right _ _).trans (le_max_left _ _)⟩
    · exact ⟨(ih hv).1.trans (le_max_right _ _),(ih hv).2.trans (le_max_right _ _)⟩

lemma coordinate_shift_outside (N : ℕ) (R B k l : ℤ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hlarge : R+B < |k| ∨ R+B < |l|) (a : GaussianInt)
    (ha : |a.re| ≤ B ∧ |a.im| ≤ B) : Outside R (a+shift N k l) := by
  have hM : (1 : ℤ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hkr : |k| ≤ |(N.factorial : ℤ)*k| := by
    rw [abs_mul,abs_of_nonneg (by omega : (0 : ℤ) ≤ N.factorial)]
    nlinarith [abs_nonneg k]
  have hlr : |l| ≤ |(N.factorial : ℤ)*l| := by
    rw [abs_mul,abs_of_nonneg (by omega : (0 : ℤ) ≤ N.factorial)]
    nlinarith [abs_nonneg l]
  have habsr := abs_add_le (a.re+(N.factorial : ℤ)*k) (-a.re)
  have habsi := abs_add_le (a.im+(N.factorial : ℤ)*l) (-a.im)
  have her : a.re+(N.factorial : ℤ)*k+ -a.re = (N.factorial : ℤ)*k := by ring
  have hei : a.im+(N.factorial : ℤ)*l+ -a.im = (N.factorial : ℤ)*l := by ring
  rw [her,abs_neg] at habsr
  rw [hei,abs_neg] at habsi
  rcases hlarge with hk | hl
  · exact Or.inl (by dsimp [Outside,shift]; linarith)
  · exact Or.inr (by dsimp [Outside,shift]; linarith)

lemma translate_walk_avoiding {C : ℤ} {N : ℕ} (H : SimpleGraph GaussianInt)
    (R B : ℤ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hH : ∀ {a b}, (sieveGraph C N).Adj a b → Outside R a → Outside R b → H.Adj a b)
    {a b : GaussianInt} (p : (sieveGraph C N).Walk a b)
    (hp : walkRadius p ≤ B) (k l : ℤ) (hlarge : R+B < |k| ∨ R+B < |l|) :
    H.Reachable (a+shift N k l) (b+shift N k l) := by
  have hout {v : GaussianInt} (hv : v ∈ p.support) : Outside R (v+shift N k l) :=
    coordinate_shift_outside N R B k l hR hB hlarge v
      ⟨(coordinates_le_walkRadius p hv).1.trans hp,(coordinates_le_walkRadius p hv).2.trans hp⟩
  clear hp
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hstep : H.Adj (a+shift N k l) (b+shift N k l) :=
      hH (adj_add_period hab (shift_period N k l))
        (hout (by simp)) (hout (by simp [p.start_mem_support]))
    exact hstep.reachable.trans (ih (fun hv => hout (by simp [hv])))

/-- Consecutive vertices on an integer-indexed line connect any two indices. -/
lemma reachable_int_line {V : Type*} {H : SimpleGraph V} (f : ℤ → V)
    (h : ∀ k : ℤ, H.Reachable (f k) (f (k+1))) (i j : ℤ) : H.Reachable (f i) (f j) := by
  have hzero (k : ℤ) : H.Reachable (f 0) (f k) := by
    induction k using Int.induction_on with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (h _)
    | pred n ih =>
      have hh := h (-(n : ℤ)-1)
      have he : -(n : ℤ)-1+1 = -(n : ℤ) := by ring
      rw [he] at hh
      simpa using ih.trans hh.symm
  exact (hzero i).symm.trans (hzero j)

#print axioms translate_walk_avoiding
#print axioms reachable_int_line
end Erdos952Investigation.PeriodicSieveEnds
