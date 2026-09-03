import Submission.PairBoxRamsey

/-!
No unrestricted countably infinite product-box Ramsey theorem is available:
for EVERY family of coordinate types, a countable coloring is unbounded on
any nonempty box with nontrivial factors at arbitrarily large coordinates.
This is a limitation on a possible Ramsey method, not Erdős 595 itself.
-/
set_option autoImplicit false
open Set
namespace Erdos595InfiniteBoxObstruction

variable (A : ℕ → Type*)

/-- Equality except for a finite initial segment. -/
def tailSetoid : Setoid (∀ n, A n) where
  r x y := ∃ N, ∀ n, N ≤ n → x n = y n
  iseqv := ⟨fun _ => ⟨0,fun _ _ => rfl⟩,
    fun ⟨N,h⟩ => ⟨N,fun n hn => (h n hn).symm⟩,
    fun ⟨N,h⟩ ⟨M,k⟩ => ⟨max N M,fun n hn =>
      (h n ((le_max_left N M).trans hn)).trans
        (k n ((le_max_right N M).trans hn))⟩⟩

noncomputable def representative (x : ∀ n, A n) : ∀ n, A n :=
  (Quotient.mk (tailSetoid A) x).out

lemma representative_tail (x : ∀ n, A n) :
    ∃ N, ∀ n, N ≤ n → x n = representative A x n := by
  obtain ⟨N,h⟩ := Quotient.mk_out (s := tailSetoid A) x
  exact ⟨N,fun n hn => (h n hn).symm⟩

lemma representative_eq {x y : ∀ n, A n} (h : (tailSetoid A).r x y) :
    representative A x = representative A y :=
  congrArg Quotient.out (Quotient.sound h)

noncomputable def color (x : ∀ n, A n) : ℕ := by
  classical
  exact Nat.find (representative_tail A x)

lemma color_spec (x : ∀ n, A n) {n : ℕ} (hn : color A x ≤ n) :
    x n = representative A x n := by
  classical
  exact (Nat.find_spec (representative_tail A x)) n hn

lemma representative_update (x : ∀ n, A n) (n : ℕ) (a : A n) :
    representative A (Function.update x n a) = representative A x := by
  apply representative_eq
  refine ⟨n+1,?_⟩
  intro m hm
  exact Function.update_of_ne (by omega) a x

/-- This SINGLE coloring works simultaneously against all such boxes. -/
theorem unbounded_on_box (S : ∀ n, Set (A n))
    (hS : ∀ n, (S n).Nonempty)
    (hlarge : ∀ N, ∃ n, N ≤ n ∧ ∃ a ∈ S n, ∃ b ∈ S n, a ≠ b) :
    ∀ N, ∃ x : ∀ n, A n, (∀ n, x n ∈ S n) ∧ N < color A x := by
  classical
  let x : ∀ n, A n := fun n => (hS n).some
  intro N
  obtain ⟨n,hn,a,ha,b,hb,hab⟩ := hlarge N
  have hex : ∃ v ∈ S n, v ≠ representative A x n := by
    by_cases h : a = representative A x n
    · exact ⟨b,hb,fun hb' => hab (h.trans hb'.symm)⟩
    · exact ⟨a,ha,h⟩
  obtain ⟨v,hv,hne⟩ := hex
  let y := Function.update x n v
  refine ⟨y,?_,?_⟩
  · intro m
    by_cases hm : m = n
    · subst m
      simpa only [y,Function.update_self] using hv
    · simpa only [y,Function.update_of_ne hm] using (hS m).some_mem
  · have hy : n < color A y := by
      by_contra h
      have he := color_spec A y (le_of_not_gt h)
      rw [show y = Function.update x n v from rfl,
        Function.update_self,representative_update] at he
      exact hne he
    exact hn.trans_lt hy

/-- In particular no full product of two-point choices is monochromatic. -/
theorem no_mono_binary_box (f : ∀ n, Fin 2 ↪ A n) (k : ℕ) :
    ¬∀ p : ℕ → Fin 2, color A (fun n => f n (p n)) = k := by
  classical
  intro h
  let S : ∀ n, Set (A n) := fun n => Set.range (f n)
  have hS : ∀ n, (S n).Nonempty := fun n => ⟨f n 0,⟨0,rfl⟩⟩
  have hl : ∀ N, ∃ n, N ≤ n ∧ ∃ a ∈ S n, ∃ b ∈ S n, a ≠ b := by
    intro N
    exact ⟨N,le_rfl,f N 0,⟨0,rfl⟩,f N 1,⟨1,rfl⟩,
      fun he => (by decide : (0 : Fin 2) ≠ 1) ((f N).injective he)⟩
  obtain ⟨x,hx,hk⟩ := unbounded_on_box A S hS hl k
  choose p hp using hx
  have he : (fun n => f n (p n)) = x := funext hp
  exact (ne_of_gt hk) (he ▸ h p)

open Erdos595PairBoxRamsey

/-- The finite-coordinate box theorem cannot simply be extended to N,
regardless of how large its ordered axes are chosen. -/
theorem no_countable_pair_box (axes : ℕ → Axis) :
    ∃ c : Family axes → ℕ,
      ∀ (f : ∀ n, Fin 4 ↪o (axes n).Carrier) (k : ℕ),
        ¬∀ p : ℕ → SmallPair, c (boxMap f p) = k := by
  let A : ℕ → Type _ := fun n => Pair (axes n)
  refine ⟨color A,?_⟩
  intro f k h
  let p₀ : SmallPair := ⟨(0,1),by decide⟩
  let p₁ : SmallPair := ⟨(2,3),by decide⟩
  let e : ∀ n, Fin 2 ↪ A n := fun n =>
    ⟨fun b => if b = 0 then pairMap (f n) p₀ else pairMap (f n) p₁,by
      intro a b he
      fin_cases a <;> fin_cases b
      · rfl
      · have hh := congrArg (fun z : A n => z.val.1) he
        have hh' : f n 0 = f n 2 := hh
        exact False.elim ((by decide : (0 : Fin 4) ≠ 2) ((f n).injective hh'))
      · have hh := congrArg (fun z : A n => z.val.1) he
        have hh' : f n 2 = f n 0 := hh
        exact False.elim ((by decide : (2 : Fin 4) ≠ 0) ((f n).injective hh'))
      · rfl⟩
  apply no_mono_binary_box A e k
  intro p
  have hh := h (fun n => if p n = 0 then p₀ else p₁)
  convert hh using 1
  congr 1
  funext n
  by_cases hp : p n = 0 <;> simp [e,boxMap,hp]


#print axioms unbounded_on_box
#print axioms no_mono_binary_box
#print axioms no_countable_pair_box
end Erdos595InfiniteBoxObstruction
