import Submission.StripObstruction

/-! CRT composite patches recurring in a two-dimensional period lattice. -/
namespace Erdos952Investigation
namespace PeriodicCompositePatches

set_option maxHeartbeats 0

lemma periodic_patch {ι : Type*} [Fintype ι] (f : ι → GaussianInt) :
    ∃ A P : ℕ, 0 < P ∧ ∀ k l : ℤ, ∀ i,
      (P : ℤ) < ((⟨(A : ℤ) + (P : ℤ)*k, (P : ℤ)*l⟩ : GaussianInt) + f i).norm →
      ¬ Prime ((⟨(A : ℤ) + (P : ℤ)*k, (P : ℤ)*l⟩ : GaussianInt) + f i) := by
  classical
  let e : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin ι).injective
  let t : ι → ℕ := fun i => Nat.fermatNumber (e i) - 1
  let m : ι → ℕ := fun i => Nat.fermatNumber (e i + 1)
  have hm (i : ι) : (m i : ℤ) = (t i : ℤ)^2 + 1 := by
    exact_mod_cast Nat.fermatNumber_succ (e i)
  have hmpos (i : ι) : 0 < m i := lt_of_lt_of_le (by decide : 0 < 3)
    (Nat.three_le_fermatNumber _)
  have hmone (i : ι) : (1 : ℤ) < m i := by
    have ht := Nat.three_le_fermatNumber (e i + 1)
    change 1 < (Nat.fermatNumber (e i + 1) : ℤ)
    omega
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact Nat.coprime_fermatNumber_fermatNumber (fun h => hij (he (by omega)))
  let r : ι → ℕ := fun i => (((t i : ℤ) * (f i).im - (f i).re) % (m i : ℤ)).toNat
  let a := Nat.chineseRemainderOfFinset r m Finset.univ
    (fun i _ => (hmpos i).ne') hcop
  let P : ℕ := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos fun i _ => hmpos i
  refine ⟨a.val, P, hP, ?_⟩
  intro k l i hlarge
  have hmiP : m i ∣ P := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hmiP' : (m i : ℤ) ∣ P := by exact_mod_cast hmiP
  have hmle : (m i : ℤ) ≤ P := by exact_mod_cast Nat.le_of_dvd hP hmiP
  have hr : (r i : ℤ) = ((t i : ℤ) * (f i).im - (f i).re) % m i := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (hmpos i).ne'))
  have hmod : (a.val : ℤ) ≡ (t i : ℤ) * (f i).im - (f i).re [ZMOD m i] := by
    calc
      _ = (r i : ℤ) % m i := Int.natCast_modEq_iff.mpr (a.property i (Finset.mem_univ i))
      _ = _ := by rw [hr, Int.emod_emod]
  have hbase : (m i : ℤ) ∣ (a.val : ℤ) + (f i).re - (t i : ℤ) * (f i).im := by
    convert dvd_neg.mpr (Int.modEq_iff_dvd.mp hmod) using 1; ring
  let z : GaussianInt := ⟨(a.val : ℤ) + (P : ℤ)*k, (P : ℤ)*l⟩ + f i
  let d : GaussianInt := ⟨t i, 1⟩
  have hd : d.norm = (m i : ℤ) := by simp [d, gaussian_norm_sq, hm]
  apply not_prime_of_small_divisor (a := d)
  · apply gaussian_linear_divisor
    rw [← hm]
    change (m i : ℤ) ∣ ((a.val : ℤ) + (P : ℤ)*k + (f i).re) -
      (t i : ℤ)*((P : ℤ)*l + (f i).im)
    have hper : (m i : ℤ) ∣ (P : ℤ)*(k - (t i : ℤ)*l) := dvd_mul_of_dvd_left hmiP' _
    convert dvd_add hbase hper using 1; ring
  · rw [hd]
    exact hmone i
  · rw [hd]
    exact hmle.trans_lt hlarge

lemma periodic_rectangle (W H : ℕ) :
    ∃ A P : ℕ, 0 < P ∧ ∀ k l : ℤ, ∀ z : GaussianInt,
      |z.re - ((A : ℤ) + (P : ℤ)*k)| ≤ W → |z.im - (P : ℤ)*l| ≤ H →
      (P : ℤ) < z.norm → ¬ Prime z := by
  let f : Fin (2*W + 1) × Fin (2*H + 1) → GaussianInt :=
    fun i => ⟨(i.1.val : ℤ) - W, (i.2.val : ℤ) - H⟩
  obtain ⟨A, P, hP, hf⟩ := periodic_patch f
  refine ⟨A, P, hP, ?_⟩
  intro k l z hr hi hn
  let i : Fin (2*W + 1) := ⟨(z.re - ((A : ℤ) + (P : ℤ)*k) + W).toNat, by
    have := abs_le.mp hr
    omega⟩
  let j : Fin (2*H + 1) := ⟨(z.im - (P : ℤ)*l + H).toNat, by
    have := abs_le.mp hi
    omega⟩
  have he : (⟨(A : ℤ) + (P : ℤ)*k, (P : ℤ)*l⟩ : GaussianInt) + f (i, j) = z := by
    have := abs_le.mp hr
    have := abs_le.mp hi
    apply Zsqrtd.ext <;> simp [f, i, j] <;> omega
  rw [← he] at hn ⊢
  exact hf k l (i, j) hn

#print axioms periodic_rectangle

end PeriodicCompositePatches
end Erdos952Investigation
