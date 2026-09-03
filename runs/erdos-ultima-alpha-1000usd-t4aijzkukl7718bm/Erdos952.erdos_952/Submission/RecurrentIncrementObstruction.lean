import Submission.Investigation

/-! Even recurrence, not only eventual periodicity, is impossible for the
increment word of an injective Gaussian-prime sequence. This does not imply
that every bounded-step sequence is recurrent. -/
namespace Erdos952Investigation
namespace RecurrentIncrementObstruction

set_option maxHeartbeats 0

lemma finite_group_prefix_return {G : Type*} [AddCommGroup G] [Finite G] (f : ℕ → G) :
    ∃ L : ℕ, ∀ n : ℕ, ∀ d : G,
      (∀ i ≤ L, f (n + i) = f i + d) → ∃ i ≤ L, f (n + i) = f 0 := by
  classical
  let S : Set G := Set.range f
  letI : Fintype S := Fintype.ofFinite S
  let rep : S → ℕ := fun s => Classical.choose s.property
  have hrep (s : S) : f (rep s) = s.val := Classical.choose_spec s.property
  let L : ℕ := Finset.univ.sup rep
  have hle (s : S) : rep s ≤ L := Finset.le_sup (Finset.mem_univ s)
  refine ⟨L, ?_⟩
  intro n d hform
  have hshift (s : S) : f (n + rep s) = s.val + d := by
    rw [hform _ (hle s), hrep s]
  let t : S → S := fun s => ⟨s.val + d, ⟨n + rep s, hshift s⟩⟩
  have hti : Function.Injective t := by
    intro s u he
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val he)
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hti (⟨f 0, ⟨0, rfl⟩⟩ : S)
  exact ⟨rep s, hle s, (hshift s).trans (congrArg Subtype.val hs)⟩

lemma block_position_formula (x : ℕ → GaussianInt) (n L : ℕ)
    (h : ∀ i < L, x (n + i + 1) - x (n + i) = x (i + 1) - x i) :
    ∀ i ≤ L, x (n + i) = x n + (x i - x 0) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have ht := h i (by omega)
    calc
      x (n + (i + 1)) = (x (i + 1) - x i) + x (n + i) := by
        rw [← Nat.add_assoc]
        exact eq_add_of_sub_eq ht
      _ = x n + (x (i + 1) - x 0) := by rw [ih (by omega)]; abel

def residue (p : ℕ) : GaussianInt →+ (ZMod p × ZMod p) where
  toFun z := (z.re, z.im)
  map_zero' := by simp
  map_add' := by intro z w; simp

lemma norm_cast_eq_of_residue_eq {p : ℕ} {z w : GaussianInt}
    (h : residue p z = residue p w) : (z.norm : ZMod p) = (w.norm : ZMod p) := by
  have hr := congrArg Prod.fst h
  have hi := congrArg Prod.snd h
  change (z.re : ZMod p) = w.re at hr
  change (z.im : ZMod p) = w.im at hi
  simp only [gaussian_norm_sq, Int.cast_add, Int.cast_pow]
  rw [hr, hi]

/-- Some initial increment block fails to recur beyond a finite index.
No bound on the jumps is needed for this obstruction. -/
theorem exists_nonrecurrent_increment_prefix (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ∃ L N : ℕ, ∀ n ≥ N, ∃ i < L,
      x (n + i + 1) - x (n + i) ≠ x (i + 1) - x i := by
  have hn1 : (x 0).norm.natAbs ≠ 1 := by
    intro he
    have hnorm : (x 0).norm = 1 := by
      have hc := congrArg (fun n : ℕ => (n : ℤ)) he
      simpa using hc
    exact (hprime 0).not_unit
      ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) (x 0)).mp hnorm)
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hn1
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv : (p : ℤ) ∣ (x 0).norm := Int.natCast_dvd.mpr hpdiv
  obtain ⟨L, hreturn⟩ := finite_group_prefix_return (fun n => residue p (x n))
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx ((p : ℤ)^2)
  refine ⟨L, N, ?_⟩
  intro n hn
  by_contra! hword
  let d := residue p (x n) - residue p (x 0)
  have hform (i : ℕ) (hi : i ≤ L) :
      residue p (x (n + i)) = residue p (x i) + d := by
    rw [block_position_formula x n L hword i hi, map_add, map_sub]
    dsimp [d]
    abel
  obtain ⟨i, hi, hres⟩ := hreturn n d hform
  have he := norm_cast_eq_of_residue_eq hres
  have hzero : ((x (n + i)).norm : ZMod p) = 0 := by
    rw [he]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  have hsmall := prime_norm_divisor_bound (hprime (n + i)) hp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero)
  have hlarge := hN (n + i) (by omega)
  omega

/-- Recurrence here means that every initial increment block occurs at
arbitrarily late positions. It is weaker than uniform recurrence. -/
def RecurrentIncrements (x : ℕ → GaussianInt) : Prop :=
  ∀ L N : ℕ, ∃ n ≥ N, ∀ i < L,
    x (n + i + 1) - x (n + i) = x (i + 1) - x i

theorem prime_increments_not_recurrent (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ¬ RecurrentIncrements x := by
  intro hrec
  obtain ⟨L, N, hbad⟩ := exists_nonrecurrent_increment_prefix x hx hprime
  obtain ⟨n, hn, hword⟩ := hrec L N
  obtain ⟨i, hi, hne⟩ := hbad n hn
  exact hne (hword i hi)

/-- In fact no suffix has a recurrent increment word. -/
theorem no_recurrent_suffix (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) (K : ℕ) :
    ¬ RecurrentIncrements (fun n => x (K + n)) := by
  apply prime_increments_not_recurrent
  · intro i j he
    exact Nat.add_left_cancel (hx he)
  · intro n
    exact hprime (K + n)

#print axioms exists_nonrecurrent_increment_prefix
#print axioms prime_increments_not_recurrent
#print axioms no_recurrent_suffix

end RecurrentIncrementObstruction
end Erdos952Investigation
