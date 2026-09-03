import Submission.GaussianSelbergMainOptimization

/-! Canonical Selberg support: all squarefree products from a fixed finite
prime family whose Gaussian norm is at most A. The support is downward
closed; its construction introduces no local-density assumption. -/
namespace Erdos952Investigation.GaussianLevelSupports
open GaussianSelbergMainOptimization FiniteSelbergOptimization
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

lemma modulus_norm_mono {ι : Type*} (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    {s t : Finset ι} (hst : s ⊆ t) : (modulus g s).norm.natAbs ≤ (modulus g t).norm.natAbs := by
  have hp : 0 < (modulus g t).norm.natAbs :=
    Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr (modulus_ne_zero g h0 t))
  have hd : modulus g s ∣ modulus g t := Finset.prod_dvd_prod_of_subset s t g hst
  exact Nat.le_of_dvd hp (Int.natAbsHom.map_dvd (Zsqrtd.normMonoidHom.map_dvd hd))

def levelSupports {ι : Type*} [Fintype ι] (g : ι → GaussianInt) (A : ℕ) : Finset (Finset ι) :=
  Finset.univ.powerset.filter (fun s => (modulus g s).norm.natAbs ≤ A)

lemma mem_levelSupports {ι : Type*} [Fintype ι] (g : ι → GaussianInt) (A : ℕ) (s : Finset ι) :
    s ∈ levelSupports g A ↔ (modulus g s).norm.natAbs ≤ A := by
  simp [levelSupports]

lemma levelSupports_downClosed {ι : Type*} [Fintype ι] (g : ι → GaussianInt)
    (h0 : ∀ i, g i ≠ 0) (A : ℕ) : DownClosed (levelSupports g A) := by
  intro s hs t hts
  rw [mem_levelSupports] at hs ⊢
  exact (modulus_norm_mono g h0 hts).trans hs

lemma empty_mem_levelSupports {ι : Type*} [Fintype ι] (g : ι → GaussianInt)
    (A : ℕ) (hA : 1 ≤ A) : ∅ ∈ levelSupports g A := by
  simpa only [mem_levelSupports,modulus,Finset.prod_empty,Zsqrtd.norm_one,Int.natAbs_one] using hA

#print axioms levelSupports_downClosed
end
end Erdos952Investigation.GaussianLevelSupports
