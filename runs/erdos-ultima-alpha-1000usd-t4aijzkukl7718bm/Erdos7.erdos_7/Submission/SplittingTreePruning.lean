import Submission.SharedTreeCover

/-! Subtree pruning for the finite splitting-tree certificate format.
This is a normalization of a sufficient construction model, not a
nonexistence theorem for arbitrary odd covering systems. -/
namespace Erdos7SplittingTreePruning
open Erdos7SplittingTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Tree

/-- No split node has a descendant label already dividing its starting modulus. -/
def Reduced : Erdos7SplittingTreeCover.Tree → ℕ → Prop
  | .leaf _, _ => True
  | .split q children, m =>
      (∀ k : (Erdos7SplittingTreeCover.Tree.split q children).Leaf,
        ¬ (Erdos7SplittingTreeCover.Tree.split q children).modulus k ∣ m) ∧
      ∀ r, Reduced (children r) (m*q)

/-- Every leaf residue remains in the starting congruence class. -/
theorem residue_base_dvd (T : Erdos7SplittingTreeCover.Tree) (m : ℕ)
    (a : ℤ) (k : T.Leaf) : (m : ℤ) ∣ T.residue m a k-a := by
  induction T generalizing m a with
  | leaf d => simp [Erdos7SplittingTreeCover.Tree.residue]
  | split q children ih =>
      rcases k with ⟨r,k⟩
      have hh := ih r (m*q) (a+(m : ℤ)*r.val) k
      rw [Nat.cast_mul] at hh
      have hh' := (dvd_mul_right (m : ℤ) (q : ℤ)).trans hh
      have h := dvd_add hh' (dvd_mul_right (m : ℤ) (r.val : ℤ))
      convert h using 1 <;> simp only [Erdos7SplittingTreeCover.Tree.residue] <;> ring

/-- Pruning retains a subfamily of the original labels. A chosen descendant
label can replace a whole subtree precisely when it divides the starting
modulus of that subtree. -/
theorem exists_reduced (T : Erdos7SplittingTreeCover.Tree) (m : ℕ)
    (hT : T.Valid m) :
    ∃ U : Erdos7SplittingTreeCover.Tree, U.Valid m ∧ Reduced U m ∧
      ∃ f : U.Leaf ↪ T.Leaf, (∀ k, U.modulus k = T.modulus (f k)) ∧
        ∀ a k, (T.modulus (f k) : ℤ) ∣ U.residue m a k-T.residue m a (f k) := by
  classical
  induction T generalizing m with
  | leaf d =>
      refine ⟨.leaf d, hT, trivial, Function.Embedding.refl _, fun _ => rfl, ?_⟩
      intro a k
      simp [Erdos7SplittingTreeCover.Tree.residue]
  | split q children ih =>
      by_cases hex : ∃ k : (Erdos7SplittingTreeCover.Tree.split q children).Leaf,
          (Erdos7SplittingTreeCover.Tree.split q children).modulus k ∣ m
      · obtain ⟨k,hk⟩ := hex
        let F : Unit ↪ (Erdos7SplittingTreeCover.Tree.split q children).Leaf :=
          ⟨fun _ => k,fun _ _ _ => Subsingleton.elim _ _⟩
        refine ⟨.leaf ((Erdos7SplittingTreeCover.Tree.split q children).modulus k),
          ⟨?_,hk⟩,trivial,F,(fun _ => rfl),?_⟩
        · exact (Erdos7SplittingTreeCover.Tree.split q children).nontrivial m hT k
        · intro a u
          have hkm : ((Erdos7SplittingTreeCover.Tree.split q children).modulus k : ℤ) ∣ m := by
            exact_mod_cast hk
          have hh := dvd_neg.mpr (hkm.trans
            (residue_base_dvd (.split q children) m a k))
          simpa only [Erdos7SplittingTreeCover.Tree.residue,neg_sub] using hh
      · choose U hvalid hred f hf hc using fun r => ih r (m*q) (hT.2 r)
        let F : (Erdos7SplittingTreeCover.Tree.split q U).Leaf ↪
            (Erdos7SplittingTreeCover.Tree.split q children).Leaf :=
          ⟨fun k => ⟨k.1,f k.1 k.2⟩,by
            rintro ⟨r,x⟩ ⟨s,y⟩ h
            have hrs : r=s := congrArg Sigma.fst h
            subst s
            have hxy : f r x=f r y := by
              exact eq_of_heq (Sigma.mk.inj h).2
            exact congrArg (Sigma.mk r) ((f r).injective hxy)⟩
        have hF : ∀ k, (Erdos7SplittingTreeCover.Tree.split q U).modulus k =
            (Erdos7SplittingTreeCover.Tree.split q children).modulus (F k) := by
          rintro ⟨r,k⟩
          exact hf r k
        refine ⟨.split q U,⟨hT.1,hvalid⟩,⟨?_,hred⟩,F,hF,?_⟩
        · intro k hk
          exact hex ⟨F k,(hF k) ▸ hk⟩
        · rintro a ⟨r,k⟩
          exact hc r (a+(m : ℤ)*r.val) k

/-- Every valid strictly labelled odd tree can be reduced without losing
validity, injectivity, or oddness. -/
theorem exists_reduced_odd (T : Erdos7SplittingTreeCover.Tree) (m : ℕ)
    (hT : T.Valid m) (hinj : Function.Injective T.modulus)
    (hodd : ∀ k, Odd (T.modulus k)) :
    ∃ U : Erdos7SplittingTreeCover.Tree, U.Valid m ∧ Reduced U m ∧
      Function.Injective U.modulus ∧ (∀ k, Odd (U.modulus k)) := by
  obtain ⟨U,hU,hred,f,hf,_⟩ := exists_reduced T m hT
  refine ⟨U,hU,hred,?_,?_⟩
  · intro x y hxy
    apply f.injective
    apply hinj
    simpa only [←hf] using hxy
  · intro k
    rw [hf]
    exact hodd (f k)

/-- At a terminal child, the assigned divisor is genuinely new: it was
not already available before the final split. -/
theorem terminal_new (q m : ℕ) (children : Fin q → Erdos7SplittingTreeCover.Tree)
    (hred : Reduced (.split q children) m) (r : Fin q) (d : ℕ)
    (hr : children r = .leaf d) : ¬ d ∣ m := by
  have hh : ∀ k : (children r).Leaf, ¬ (children r).modulus k ∣ m :=
    fun k => hred.1 ⟨r,k⟩
  rw [hr] at hh
  exact hh ()

/-- For a prime final split, the divisor quotient is coprime to that prime.
Thus a reduced terminal label retains its full prime-power exponent. -/
theorem terminal_quotient_coprime (p m : ℕ) (hp : Nat.Prime p)
    (children : Fin p → Erdos7SplittingTreeCover.Tree)
    (hvalid : (Erdos7SplittingTreeCover.Tree.split p children).Valid m)
    (hred : Reduced (.split p children) m) (r : Fin p) (d : ℕ)
    (hr : children r = .leaf d) : p.Coprime ((m*p)/d) := by
  have hnew := terminal_new p m children hred r d hr
  have hd : d ∣ m*p := by
    have hh := hvalid.2 r
    rw [hr] at hh
    exact hh.2
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hmul : d*p ∣ m*p := (Nat.dvd_div_iff_mul_dvd hd).mp hdiv
  exact hnew (Nat.dvd_of_mul_dvd_mul_right hp.pos hmul)

/-- The strengthened finite certificate condition is equivalent to the old
one. It remains only a sufficient model of the original conjecture. -/
theorem reduced_odd_certificate_iff :
    (∃ T : Erdos7SplittingTreeCover.Tree, T.Valid 1 ∧
      Function.Injective T.modulus ∧ (∀ k, Odd (T.modulus k))) ↔
    (∃ T : Erdos7SplittingTreeCover.Tree, T.Valid 1 ∧ Reduced T 1 ∧
      Function.Injective T.modulus ∧ (∀ k, Odd (T.modulus k))) := by
  constructor
  · rintro ⟨T,hT,hinj,hodd⟩
    exact exists_reduced_odd T 1 hT hinj hodd
  · rintro ⟨T,hT,_,hinj,hodd⟩
    exact ⟨T,hT,hinj,hodd⟩

/-- Coherence is preserved as well: the retained classes do not change.
This allows pruning in the complete shared-tree certificate model. -/
theorem exists_reduced_consistent (T : Erdos7SplittingTreeCover.Tree)
    (m : ℕ) (a : ℤ) (hT : T.Valid m)
    (hodd : ∀ k, Odd (T.modulus k))
    (hcoh : Erdos7SharedTreeCover.Consistent T m a) :
    ∃ U : Erdos7SplittingTreeCover.Tree, U.Valid m ∧ Reduced U m ∧
      (∀ k, Odd (U.modulus k)) ∧ Erdos7SharedTreeCover.Consistent U m a := by
  obtain ⟨U,hU,hred,f,hf,hc⟩ := exists_reduced T m hT
  refine ⟨U,hU,hred,?_,?_⟩
  · intro k
    rw [hf]
    exact hodd (f k)
  · intro i j hij
    have hm : T.modulus (f i)=T.modulus (f j) :=
      (hf i).symm.trans (hij.trans (hf j))
    have hi := hc a i
    have hj := hc a j
    have hmid := hcoh (f i) (f j) hm
    rw [←hf i] at hi hmid
    rw [←hf j,←hij] at hj
    have hh := dvd_sub (dvd_add hi hmid) hj
    convert hh using 1 <;> ring

/-- Pruning is also available for the coherent model that characterizes
arbitrary covers. This equivalence supplies no witness and no contradiction. -/
theorem reduced_shared_characterization :
    (∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤) ↔
    ∃ T : Erdos7SplittingTreeCover.Tree, T.Valid 1 ∧ Reduced T 1 ∧
      (∀ i, Odd (T.modulus i)) ∧ Erdos7SharedTreeCover.Consistent T 1 0 := by
  constructor
  · intro h
    obtain ⟨T,hT,ho,hc⟩ := Erdos7SharedTreeCover.shared_tree_characterization.mp h
    exact exists_reduced_consistent T 1 0 hT ho hc
  · rintro ⟨T,hT,_,ho,hc⟩
    exact Erdos7SharedTreeCover.shared_tree_characterization.mpr ⟨T,hT,ho,hc⟩

end Tree
#print axioms Tree.reduced_shared_characterization
#print axioms Tree.exists_reduced_consistent
#print axioms Tree.exists_reduced
#print axioms Tree.exists_reduced_odd
#print axioms Tree.terminal_quotient_coprime
#print axioms Tree.terminal_new
#print axioms Tree.reduced_odd_certificate_iff
end Erdos7SplittingTreePruning
