import Submission.No9Certificates

/-! Mathematical projections of the verified integer transition checks. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

structure PrefixChecked (a : PrefixControl) (s v : State) : Prop where
  p_three : 3 ≤ a.p
  R_pos : 1 ≤ a.R
  R_le : a.R ≤ 18
  cap_le : a.A ≤ a.B*a.p
  cut_lt : a.cut < nodes
  geometry : LossGeometry a.A a.B (denominator a.p) a.lossIndex
  loss_lt : loss a s.values < s.mass
  top : ∀ j,j < nodes → s.values j ≤ s.values 0
  mass : v.mass=(step a s).mass
  cubic : v.cubic=(step a s).cubic
  values : realValues v.values=realValues (step a s).values

lemma prefix_checked (i : ℕ) (hi : i < prefixLength) :
    PrefixChecked (prefixControl i) (prefixState i) (prefixState (i+1)) := by
  have hh := prefix_checks_all i hi
  simp only [prefixTransitionCheck,prefixStaticCheck,Bool.and_eq_true,decide_eq_true_eq,
    lossGeometryCheck_iff,topCheck_iff,checkState_iff,and_assoc] at hh
  rcases hh with ⟨hp,hR0,hR1,hA,hcut,hgeom,hL,htop,hm,hC,hv⟩
  exact ⟨hp,hR0,hR1,hA,hcut,hgeom,hL,htop,hm.symm,hC.symm,
    (realValues_congr _ _ hv).symm⟩

structure BlockChecked (b : BlockControl) (s v : State) (y1 y2 y3 : ℕ → ℕ) : Prop where
  analytic : BlockAnalyticBounds b
  lo_lt_hi : b.lo < b.hi
  cut_lt : b.cut < nodes
  geometry : LossGeometry 5 4 (b.lo-1) b.lossIndex
  loss_lt : b.count*blockLoss b s.values y1 y2 y3 < s.mass
  top : ∀ j,j < nodes → s.values j ≤ s.values 0
  power1 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 s.values j=y1 j
  power2 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y1 j=y2 j
  power3 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y2 j=y3 j
  mass : v.mass=(blockStep b s y1 y2 y3).mass
  cubic : v.cubic=(blockStep b s y1 y2 y3).cubic
  values : realValues v.values=realValues (blockStep b s y1 y2 y3).values

lemma block_checked (i : ℕ) (hi : i < blockLength) :
    BlockChecked (blockControl i) (blockState i) (blockState (i+1)) (blockY1 i) (blockY2 i) (blockY3 i) := by
  have hh := block_checks_all i hi
  simp only [blockTransitionCheck,blockStaticCheck,Bool.and_eq_true,decide_eq_true_eq,
    blockIntegerCheck_iff,lossGeometryCheck_iff,topCheck_iff,checkValues_iff,checkState_iff,
    Nat.zero_le,true_implies,Nat.zero_add,and_assoc] at hh
  rcases hh with ⟨hb,hlo,hcut,hgeom,hL,htop,hy1,hy2,hy3,hm,hC,hv⟩
  exact ⟨blockIntegerBounds_sound _ hb,hlo,hcut,hgeom,hL,htop,hy1,hy2,hy3,hm.symm,hC.symm,
    (realValues_congr _ _ hv).symm⟩

lemma prefix_mass_pos (i : ℕ) (hi : i ≤ prefixLength) : 0 < (prefixState i).mass := by
  by_cases hlast : i=prefixLength
  · subst i
    rw [prefix_block_state_agree]
    exact (block_checked 0 (by decide +kernel)).loss_lt.trans_le' (Nat.zero_le _)
  · exact (prefix_checked i (by omega)).loss_lt.trans_le' (Nat.zero_le _)

lemma block_mass_pos (i : ℕ) (hi : i ≤ blockLength) : 0 < (blockState i).mass := by
  by_cases hlast : i=blockLength
  · subst i; exact final_mass_positive
  · exact (block_checked i (by omega)).loss_lt.trans_le' (Nat.zero_le _)

#print axioms prefix_checked
#print axioms block_checked
end Erdos7No9Certificate
