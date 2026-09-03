import FormalConjecturesUtil

/-!
Coverage-dependent midpoint constraints on private points of odd congruence
classes. These are necessary conditions only, not a resolution of Erdős 7.
-/

namespace Erdos7PrivateMidpoint

/-- Private representatives, with the class membership on the diagonal included. -/
def PrivateFrame {I : Type*} (m : I → ℕ) (a x : I → ℤ) : Prop :=
  ∀ i j, (m j : ℤ) ∣ x i-a j ↔ i=j

lemma exists_modular_midpoint (N u v : ℤ) (hN : Odd N) :
    ∃ z : ℤ, N ∣ 2*z-u-v := by
  rcases hN with ⟨t, rfl⟩
  refine ⟨(t+1)*(u+v), u+v, ?_⟩
  ring

lemma endpoint_excluded {I : Type*} (m : I → ℕ) (a x : I → ℤ)
    (hx : PrivateFrame m a x) (i j : I)
    (h : (m i : ℤ) ∣ x i+x j-2*a i) : i=j := by
  have hi : (m i : ℤ) ∣ x i-a i := (hx i i).mpr rfl
  have hj : (m i : ℤ) ∣ x j-a i := by
    convert dvd_sub h hi using 1; ring
  exact ((hx j i).mp hj).symm

/-- Full coverage forces every pair of distinct private representatives to
have a modular midpoint in some class other than the two endpoint classes. -/
theorem cover_forces_third {I : Type*} (m : I → ℕ) (a x : I → ℤ)
    (N : ℤ) (hN : Odd N) (hd : ∀ i, (m i : ℤ) ∣ N)
    (hx : PrivateFrame m a x)
    (hc : ∀ z : ℤ, ∃ k, (m k : ℤ) ∣ z-a k)
    (i j : I) (hij : i ≠ j) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ (m k : ℤ) ∣ x i+x j-2*a k := by
  obtain ⟨z, hz⟩ := exists_modular_midpoint N (x i) (x j) hN
  obtain ⟨k, hk⟩ := hc z
  have he : (m k : ℤ) ∣ x i+x j-2*a k := by
    have h₁ := dvd_mul_of_dvd_right hk 2
    have h₂ := (hd k).trans hz
    convert dvd_sub h₁ h₂ using 1; ring
  refine ⟨k, ?_, ?_, he⟩
  · intro hki
    subst k
    exact hij (endpoint_excluded m a x hx i j he)
  · intro hkj
    subst k
    have he' : (m j : ℤ) ∣ x j+x i-2*a j := by simpa [add_comm] using he
    exact hij (endpoint_excluded m a x hx j i he').symm

lemma cancel_two {m : ℕ} (hm : Odd m) {z : ℤ}
    (hz : (m : ℤ) ∣ 2*z) : (m : ℤ) ∣ z := by
  have hcop : IsCoprime (m : ℤ) (2 : ℤ) := (Nat.coprime_two_right.mpr hm).isCoprime
  exact hcop.dvd_of_dvd_mul_left hz

/-- Along edges whose endpoint residues are opposite, signs alternate. -/
lemma alternating_path {m : ℕ} (f : ℕ → ℤ) (n : ℕ)
    (h : ∀ k < n, (m : ℤ) ∣ f k+f (k+1)) :
    (m : ℤ) ∣ f 0-(-1 : ℤ)^n*f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := ih (fun k hk => h k (by omega))
      have he := dvd_mul_of_dvd_right (h n (by omega)) ((-1 : ℤ)^n)
      convert dvd_add hh he using 1; rw [pow_succ]; ring

/-- An odd closed walk of opposite residues in an odd modulus has zero residue. -/
theorem odd_closed_walk_zero {m : ℕ} (hm : Odd m) (f : ℕ → ℤ)
    (n : ℕ) (hn : Odd n) (hclose : f n = f 0)
    (hedge : ∀ k < n, (m : ℤ) ∣ f k+f (k+1)) : (m : ℤ) ∣ f 0 := by
  have h := alternating_path f n hedge
  rw [hn.neg_one_pow, hclose] at h
  apply cancel_two hm
  convert h using 1; ring

/-- In a private frame, a class's midpoint edges cannot form an odd closed
walk on vertices other than that class's own representative. -/
theorem no_odd_midpoint_walk {I : Type*} (m : I → ℕ) (a x : I → ℤ)
    (hx : PrivateFrame m a x) (i : I) (hm : Odd (m i))
    (v : ℕ → I) (n : ℕ) (hn : Odd n) (hclose : v n=v 0)
    (hstart : v 0 ≠ i) :
    ¬ (∀ k < n, (m i : ℤ) ∣ x (v k)+x (v (k+1))-2*a i) := by
  intro he
  have hh := odd_closed_walk_zero hm (fun k => x (v k)-a i) n hn
    (by dsimp; rw [hclose]) (fun k hk => by convert he k hk using 1; ring)
  exact hstart ((hx (v 0) i).mp hh)

section Control

/-- This family is NOT a cover. -/
def modulus : Fin 3 → ℕ := ![3,5,7]
def residue : Fin 3 → ℤ := fun _ => 0
def point : Fin 3 → ℤ := ![36,55,14]

lemma modulus_injective : Function.Injective modulus := by decide +kernel
lemma odd_nontrivial : ∀ i, Odd (modulus i) ∧ 1 < modulus i := by decide +kernel
lemma private_frame : PrivateFrame modulus residue point := by
  unfold PrivateFrame
  decide +kernel
lemma point_midpoints : ∀ i j : Fin 3, i ≠ j →
    ∃ k, k ≠ i ∧ k ≠ j ∧ (modulus k : ℤ) ∣ point i+point j-2*residue k := by
  decide +kernel
/-- Another private frame of the same partial family has midpoint1, uncovered.
Thus the first frame does not satisfy the all-frames quantifier of a true cover. -/
def alternatePoint : Fin 3 → ℤ := ![12,-10,7]
lemma alternate_private_frame : PrivateFrame modulus residue alternatePoint := by
  unfold PrivateFrame
  decide +kernel
lemma alternate_midpoint_uncovered : ∀ k : Fin 3,
    ¬ (modulus k : ℤ) ∣ alternatePoint 0+alternatePoint 1-2*residue k := by
  decide +kernel

lemma period_odd : Odd (105 : ℤ) := by decide +kernel
lemma moduli_dvd_period : ∀ i, (modulus i : ℤ) ∣ 105 := by decide +kernel
lemma one_uncovered : ∀ i, ¬ (modulus i : ℤ) ∣ 1-residue i := by decide +kernel

theorem control_not_cover : ¬ ∀ z : ℤ, ∃ i, (modulus i : ℤ) ∣ z-residue i := by
  intro h
  obtain ⟨i, hi⟩ := h 1
  exact one_uncovered i hi

end Control

#print axioms cover_forces_third
#print axioms odd_closed_walk_zero
#print axioms no_odd_midpoint_walk
#print axioms private_frame
#print axioms point_midpoints
#print axioms alternate_private_frame
#print axioms alternate_midpoint_uncovered
#print axioms control_not_cover

end Erdos7PrivateMidpoint
