import FormalConjectures.Util.ProblemImports

open Finset Nat Set

set_option maxRecDepth 10000

/-- A distinct zero-sum atom in the additive monoid `ℕ / Lℕ`, represented by
natural numbers.  This is the same specialized notion used in the scratch files:
`A` is nonempty, its sum is `0 mod L`, and no nonempty proper sub-finset has
sum `0 mod L`. -/
def IsZeroSumAtom (L : ℕ) (A : Finset ℕ) : Prop :=
  A.Nonempty ∧ L ∣ A.sum id ∧
    ∀ B : Finset ℕ, B ⊂ A → B.Nonempty → ¬ L ∣ B.sum id

namespace CyclicAtomSkeleton

/-- Elements of `A` divisible by the prime being peeled off.  The definition is
not restricted to primes, since the elementary lemmas only need a modulus `p`. -/
def pDivPart (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun d => p ∣ d

/-- Elements of `A` not divisible by `p`. -/
def pNondivPart (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun d => ¬ p ∣ d

/-- The quotient image of the `p`-divisible part under `d ↦ d / p`.  For a
prime descent from `L` to `L/p`, this is the part whose cross-number denominator
is unchanged after cancelling `p`. -/
def pDivQuot (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (pDivPart p A).image fun d => d / p

lemma pDivPart_subset (p : ℕ) (A : Finset ℕ) : pDivPart p A ⊆ A := by
  intro d hd
  exact (Finset.mem_filter.mp hd).1

lemma pNondivPart_subset (p : ℕ) (A : Finset ℕ) : pNondivPart p A ⊆ A := by
  intro d hd
  exact (Finset.mem_filter.mp hd).1

lemma sum_pDivPart_add_sum_pNondivPart (p : ℕ) (A : Finset ℕ) :
    (pDivPart p A).sum id + (pNondivPart p A).sum id = A.sum id := by
  classical
  simpa [pDivPart, pNondivPart] using
    (Finset.sum_filter_add_sum_filter_not (s := A) (p := fun d => p ∣ d) (f := id))

lemma sum_pNondivPart_add_sum_pDivPart (p : ℕ) (A : Finset ℕ) :
    (pNondivPart p A).sum id + (pDivPart p A).sum id = A.sum id := by
  rw [add_comm, sum_pDivPart_add_sum_pNondivPart]

lemma div_injective_on_pDivPart (p : ℕ) (A : Finset ℕ) :
    Set.InjOn (fun d => d / p) (↑(pDivPart p A) : Set ℕ) := by
  intro x hx y hy hxy
  have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
  have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
  calc
    x = x / p * p := (Nat.div_mul_cancel hpx).symm
    _ = y / p * p := congrArg (fun z => z * p) hxy
    _ = y := Nat.div_mul_cancel hpy

lemma sum_pDivPart_eq_p_mul_sum_pDivQuot (p : ℕ) (A : Finset ℕ) :
    (pDivPart p A).sum id = p * (pDivQuot p A).sum id := by
  classical
  calc
    (pDivPart p A).sum id
        = (pDivPart p A).sum (fun d => p * (d / p)) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hpd : p ∣ d := (Finset.mem_filter.mp hd).2
            change d = p * (d / p)
            rw [mul_comm, Nat.div_mul_cancel hpd]
    _ = p * (pDivPart p A).sum (fun d => d / p) := by
            rw [Finset.mul_sum]
    _ = p * (pDivQuot p A).sum id := by
            have himage : (pDivQuot p A).sum id =
                (pDivPart p A).sum (fun d => d / p) := by
              exact Finset.sum_image (f := id) (s := pDivPart p A)
                (g := fun d => d / p) (div_injective_on_pDivPart p A)
            rw [himage]

lemma p_dvd_sum_pDivPart (p : ℕ) (A : Finset ℕ) :
    p ∣ (pDivPart p A).sum id := by
  classical
  apply Finset.dvd_sum
  intro d hd
  exact (Finset.mem_filter.mp hd).2

/-- If a total sum is divisible by a multiple `L` of `p`, then after removing
all terms already divisible by `p`, the remaining `p`-free part still has sum
`0 mod p`.  This is the first concrete congruence forced by the quotient-by-`p`
descent. -/
lemma p_dvd_sum_pNondivPart_of_dvd_total {p L : ℕ} {A : Finset ℕ}
    (hpL : p ∣ L) (hLsum : L ∣ A.sum id) :
    p ∣ (pNondivPart p A).sum id := by
  classical
  have htotal : p ∣ A.sum id := dvd_trans hpL hLsum
  have hsplit : (pDivPart p A).sum id + (pNondivPart p A).sum id = A.sum id :=
    sum_pDivPart_add_sum_pNondivPart p A
  have hdiv : p ∣ (pDivPart p A).sum id := p_dvd_sum_pDivPart p A
  rw [← hsplit] at htotal
  exact (Nat.dvd_add_iff_right hdiv).mpr htotal

lemma div_of_dvd_of_dvd {p d L : ℕ} (hp0 : p ≠ 0) (hpd : p ∣ d) (hdL : d ∣ L) :
    d / p ∣ L / p := by
  rcases hpd with ⟨a, rfl⟩
  rcases hdL with ⟨b, rfl⟩
  have hpPos : 0 < p := Nat.pos_of_ne_zero hp0
  refine ⟨b, ?_⟩
  rw [mul_assoc]
  rw [Nat.mul_div_right (a * b) hpPos]
  rw [Nat.mul_div_right a hpPos]

lemma pDivQuot_subset_divisors_div {p L : ℕ} {A : Finset ℕ}
    (hp0 : p ≠ 0) (hA : A ⊆ Nat.divisors L) :
    pDivQuot p A ⊆ Nat.divisors (L / p) := by
  classical
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨d, hd, rfl⟩
  have hdA : d ∈ A := pDivPart_subset p A hd
  have hpd : p ∣ d := (Finset.mem_filter.mp hd).2
  have hdvdL : d ∣ L := (Nat.mem_divisors.mp (hA hdA)).1
  have hLne : L ≠ 0 := (Nat.mem_divisors.mp (hA hdA)).2
  have hpL : p ∣ L := dvd_trans hpd hdvdL
  rw [Nat.mem_divisors]
  constructor
  · exact div_of_dvd_of_dvd hp0 hpd hdvdL
  · intro hzero
    have hquotdvd : L / p ∣ L := Nat.div_dvd_of_dvd hpL
    rw [hzero] at hquotdvd
    rcases hquotdvd with ⟨c, hc⟩
    omega

lemma dvd_div_of_prime_not_dvd {p d L : ℕ} (hp : p.Prime) (hpL : p ∣ L)
    (hdL : d ∣ L) (hpn : ¬ p ∣ d) : d ∣ L / p := by
  have hcop_pd : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpn
  have hcop_dp : Nat.Coprime d p := hcop_pd.symm
  have hLmul : L = p * (L / p) := by
    rw [mul_comm, Nat.div_mul_cancel hpL]
  rw [hLmul] at hdL
  exact (hcop_dp.dvd_mul_left).mp hdL

lemma pNondivPart_subset_divisors_div {p L : ℕ} {A : Finset ℕ}
    (hp : p.Prime) (hpL : p ∣ L) (hLpos : 0 < L) (hA : A ⊆ Nat.divisors L) :
    pNondivPart p A ⊆ Nat.divisors (L / p) := by
  intro d hd
  have hdA : d ∈ A := pNondivPart_subset p A hd
  have hpn : ¬ p ∣ d := (Finset.mem_filter.mp hd).2
  have hdvdL : d ∣ L := (Nat.mem_divisors.mp (hA hdA)).1
  rw [Nat.mem_divisors]
  constructor
  · exact dvd_div_of_prime_not_dvd hp hpL hdvdL hpn
  · exact (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hLpos hpL) hp.pos))

/-- The two images produced by the first step of a prime descent both live over
`L/p`: the non-`p` part without changing entries, and the `p`-divisible part
after dividing entries by `p`.  This is a useful partition skeleton, but by
itself it does not say either piece is an atom modulo `L/p`. -/
lemma quotient_step_subsets {p L : ℕ} {A : Finset ℕ}
    (hp : p.Prime) (hpL : p ∣ L) (hLpos : 0 < L) (hA : A ⊆ Nat.divisors L) :
    pNondivPart p A ⊆ Nat.divisors (L / p) ∧
      pDivQuot p A ⊆ Nat.divisors (L / p) := by
  exact ⟨pNondivPart_subset_divisors_div hp hpL hLpos hA,
    pDivQuot_subset_divisors_div hp.ne_zero hA⟩

/-- A fully proved base case for the desired atom theorem.  The nontrivial
inductive step would need to turn the congruence/partition lemmas above into an
extraction of a nonempty proper zero-sum sub-finset when `A.sum id > L`. -/
lemma atom_sum_le_one {A : Finset ℕ}
    (hA : A ⊆ Nat.divisors 1) (hAtom : IsZeroSumAtom 1 A) : A.sum id ≤ 1 := by
  have hsubsingleton : A ⊆ ({1} : Finset ℕ) := by
    intro d hd
    have hd' := hA hd
    simpa using hd'
  rcases hAtom.1 with ⟨a, ha⟩
  have ha1 : a = 1 := by
    have : a ∈ ({1} : Finset ℕ) := hsubsingleton ha
    simpa using this
  have hAeq : A = {1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨by simpa [ha1] using ha, ?_⟩
    intro y hy
    have : y ∈ ({1} : Finset ℕ) := hsubsingleton hy
    simpa using this
  rw [hAeq]
  simp

end CyclicAtomSkeleton
