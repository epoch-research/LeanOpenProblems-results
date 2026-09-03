import FormalConjecturesUtil

/-!
A finite obstruction to arbitrary prime-by-prime extension of odd ZMod 4
characters. The old witness roots have Sidon cubes even before coloring,
but prescribed colors cannot extend over the next prime. The separate full-box
enumeration is an external check, not claimed as a theorem in this file. This
does not rule out recoloring or settle the positive-density conjecture.
-/
namespace Erdos1206.OddPrimeBoxExtensionObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- All products of subsets of a finite prime list, retaining list order. -/
def products : List ℕ → List ℕ
  | [] => [1]
  | p :: ps => let L := products ps; L ++ L.map (p * ·)

def oldPrimes : List ℕ := [2,7,31,199,397,677,773,1861]
def oldRoots : List ℕ := products oldPrimes

def oldWitnesses : Finset ℕ := {2,7,31,199,397,398,677,773,1861,4739,5411}

/-- The old roots used by the obstruction, including all eight old primes,
have Sidon cubes before imposing any colors. -/
theorem old_witnesses_sidon :
    IsSidon ((fun n : ℕ => n^3) '' (oldWitnesses : Set ℕ)) := by
  rw [← Finset.coe_image]
  decide +kernel

/-- Every old witness is a subset product of the eight prescribed primes. -/
theorem old_witnesses_in_box : ∀ n ∈ oldWitnesses, n ∈ oldRoots := by
  decide +kernel

/-- Any coloring is proper on the old witness set. -/
theorem old_witness_fibers_sidon (c : ℕ → ZMod 4) (r : ZMod 4) :
    IsSidon ((fun n : ℕ => n^3) '' {n | n ∈ oldWitnesses ∧ c n=r}) := by
  apply Set.IsSidon.subset old_witnesses_sidon
  rintro _ ⟨n,hn,rfl⟩
  exact ⟨n,hn.1,rfl⟩

private lemma odd_cases : ∀ x : ZMod 4, 2*x=2 → x=1 ∨ x=3 := by
  decide +kernel

private lemma squarefree_roots :
    Squarefree 31 ∧ Squarefree 397 ∧ Squarefree 1861 ∧ Squarefree 1867 ∧
    Squarefree 398 ∧ Squarefree 3734 ∧ Squarefree 4739 ∧ Squarefree 5411 := by
  norm_num only [Nat.squarefree_iff_minSqFac]
  decide +kernel

/-- The new prime cannot be colored 1 or 3 compatibly with these old colors.
This does not obstruct recoloring the old primes. -/
theorem prescribed_odd_colors_obstruct (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a*b)=c a+c b)
    (h2 : c 2=1) (h7 : c 7=1) (h31 : c 31=1) (h199 : c 199=3)
    (h397 : c 397=1) (h677 : c 677=3) (h773 : c 773=3) (h1861 : c 1861=1)
    (hnew : 2*c 1867=2) :
    ¬ (∀ r : ZMod 4,
      IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ c n=r})) := by
  intro hs
  obtain ⟨hs31,hs397,hs1861,hs1867,hs398,hs3734,hs4739,hs5411⟩ := squarefree_roots
  rcases odd_cases (c 1867) hnew with h1 | h3
  · have hh := hs 1
      _ ⟨31,⟨hs31,h31⟩,rfl⟩ _ ⟨397,⟨hs397,h397⟩,rfl⟩
      _ ⟨1867,⟨hs1867,h1⟩,rfl⟩ _ ⟨1861,⟨hs1861,h1861⟩,rfl⟩
      (by norm_num : (31:ℕ)^3+1867^3=397^3+1861^3)
    norm_num at hh
  · have h398 : c 398=0 := by
      rw [show 398=2*199 by norm_num,hmul 2 199 (by omega) (by omega),h2,h199]
      decide +kernel
    have h3734 : c 3734=0 := by
      rw [show 3734=2*1867 by norm_num,hmul 2 1867 (by omega) (by omega),h2,h3]
      decide +kernel
    have h4739 : c 4739=0 := by
      rw [show 4739=7*677 by norm_num,hmul 7 677 (by omega) (by omega),h7,h677]
      decide +kernel
    have h5411 : c 5411=0 := by
      rw [show 5411=7*773 by norm_num,hmul 7 773 (by omega) (by omega),h7,h773]
      decide +kernel
    have hh := hs 0
      _ ⟨398,⟨hs398,h398⟩,rfl⟩ _ ⟨3734,⟨hs3734,h3734⟩,rfl⟩
      _ ⟨5411,⟨hs5411,h5411⟩,rfl⟩ _ ⟨4739,⟨hs4739,h4739⟩,rfl⟩
      (by norm_num : (398:ℕ)^3+5411^3=3734^3+4739^3)
    norm_num at hh

#print axioms old_witnesses_sidon
#print axioms old_witnesses_in_box
#print axioms old_witness_fibers_sidon
#print axioms prescribed_odd_colors_obstruct
end Erdos1206.OddPrimeBoxExtensionObstruction
