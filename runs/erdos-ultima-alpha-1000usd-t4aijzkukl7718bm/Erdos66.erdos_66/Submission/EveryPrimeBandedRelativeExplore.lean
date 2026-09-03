import Submission.BandedRepairFamilyExplore
import Submission.EveryPrimeRelativeFamilyExplore

/-! Relative mixed-sum flat families with a banded origin repair. The field
size bound for the repair is linear in the maximum parameter count. This is
still a finite-group construction, with no integer-prefix compatibility. -/
namespace Erdos66EveryPrimeBandedRelative
open Erdos66BandedRepairFamily Erdos66EveryPrimeRelativeFamily
  Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy
  Erdos66TranslatedMixedFiber Erdos66OriginRepair Erdos66CrossGraph
open scoped Classical
set_option maxHeartbeats 1500000

lemma banded_cost_bound (a b g m n : ℝ) (hg : 1 ≤ g) (ha : g ≤ a) (hb : g ≤ b)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hma : m*g ≤ 2*a) (hnb : n*g ≤ 2*b) :
    (2*a+2*b+8*a*n+8*m*b+8*m*n)*g ≤ 68*a*b := by
  have hg0 : 0 ≤ g := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hb ha0
  have h₂ := mul_le_mul_of_nonneg_left ha hb0
  have h₃ := mul_le_mul_of_nonneg_left hnb ha0
  have h₄ := mul_le_mul_of_nonneg_right hma hb0
  have h₅ : (m*g)*(n*g) ≤ (2*a)*(2*b) := mul_le_mul hma hnb (by positivity) (by positivity)
  have h₆ : m*n*g ≤ m*n*g^2 := by
    have hh : g ≤ g^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hh (mul_nonneg hm hn)
  nlinarith

lemma natural_banded_cost (a b g : ℕ) (hg : 0 < g) (ha : g ≤ a) (hb : g ≤ b) :
    2*(a : ℝ)+2*b+8*a*((b/g : ℕ)+1)+8*((a/g : ℕ)+1)*b+
      8*((a/g : ℕ)+1)*((b/g : ℕ)+1) ≤ (17/(g : ℝ))*(4*(a : ℝ)*b) := by
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hgr1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have har : (g : ℝ) ≤ a := by exact_mod_cast ha
  have hbr : (g : ℝ) ≤ b := by exact_mod_cast hb
  have hma : (((a/g : ℕ) : ℝ)+1)*g ≤ 2*a := by
    have hh : ((a/g : ℕ) : ℝ)*(g : ℝ) ≤ a := by exact_mod_cast Nat.div_mul_le_self a g
    linarith
  have hnb : (((b/g : ℕ) : ℝ)+1)*g ≤ 2*b := by
    have hh : ((b/g : ℕ) : ℝ)*(g : ℝ) ≤ b := by exact_mod_cast Nat.div_mul_le_self b g
    linarith
  have hh := banded_cost_bound a b g (((a/g : ℕ) : ℝ)+1) (((b/g : ℕ) : ℝ)+1)
    hgr1 har hbr (by positivity) (by positivity) hma hnb
  apply (mul_le_mul_iff_left₀ hgr).mp
  calc
    _ ≤ 68*(a : ℝ)*b := hh
    _ = _ := by field_simp; ring

/-- For fixed precision, a band width g and a spacing D work at every prime
above max(8DH+3,4gDH). In particular the repair no longer needs p>2(DH)^2. -/
theorem every_prime_banded_relative_family (η : ℝ) (hη : 0 < η) (H : ℕ) :
    ∃ D g : ℕ, 0 < D ∧ 0 < g ∧ ∀ p : ℕ, ∀ hp : p.Prime,
      max (8*(D*H)+3) (4*g*(D*H)) < p →
      ∃ B : ℕ → Finset (ZMod p × ZMod p), B 0=∅ ∧ Monotone B ∧
        ∀ i ≤ H, ∀ j ≤ H, ∀ z,
          |(pairCount (B i) (B j) z : ℝ)-4*(D : ℝ)^2*i*j| ≤
            η*(4*(D : ℝ)^2*i*j) := by
  obtain ⟨T,hTbig⟩ := exists_nat_gt (max (1 : ℝ) (1/η))
  have hT : (1 : ℝ) ≤ T := (lt_of_le_of_lt (le_max_left _ _) hTbig).le
  have hT0 : (0 : ℝ) < T := by linarith
  have hTnat : 0 < T := by exact_mod_cast hT0
  have hηT : 1 < η*T := by
    have hh := (div_lt_iff₀ hη).mp (lt_of_le_of_lt (le_max_right _ _) hTbig)
    linarith
  let D : ℕ := 1024*(H+1)*T^2
  let g : ℕ := 68*T
  have hD : 0 < D := by dsimp [D]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hDg : g ≤ D := by
    dsimp [D,g]
    have hh : T ≤ T^2 := by nlinarith
    nlinarith
  refine ⟨D,g,hD,hg,fun p hp hprime ↦ ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hp1 : 8*(D*H)+3 < p := lt_of_le_of_lt (le_max_left _ _) hprime
  have hp2 : 4*g*(D*H) < p := lt_of_le_of_lt (le_max_right _ _) hprime
  have hpne : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hpne
  obtain ⟨a,hzero,hopp,henergy⟩ := exists_admissible_interval_translates p hpne (2*(D*H)) (by omega)
    (Finset.range (H+1)) (fun i ↦ 2*(D*i)) (fun i hi ↦ by
      have hh : i ≤ H := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left D hh))
  let U := fun i ↦ intervalTranslate p a (2*i)
  have hcard : ∀ i ≤ D*H, (U i).card=2*i := by
    intro i hi
    exact intervalTranslate_card p a (by omega)
  have hspace : 2*(2*(D*H)+(D*H/g+1))+1 < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have hh : D*H/g ≤ D*H := Nat.div_le_self _ _
    omega
  obtain ⟨C,hCmono,hC⟩ := banded_origin_repair hF (D*H) g hg (by simpa using hp2) U
    (fun i j hij ↦ intervalTranslate_mono p a (by omega)) hcard hzero hopp hspace
  let B : ℕ → Finset (ZMod p × ZMod p) := fun i ↦ if i=0 then ∅ else C (D*i)
  refine ⟨B,by simp [B],?_,?_⟩
  · intro i j hij
    by_cases hi : i=0
    · simp [B,hi]
    · have hj : j ≠ 0 := by omega
      simp only [B,if_neg hi,if_neg hj]
      exact hCmono (Nat.mul_le_mul_left D hij)
  · intro i hiH j hjH z
    by_cases hi : i=0
    · subst i; simp [B,pairCount]
    by_cases hj : j=0
    · subst j; simp [B,pairCount]
    have hi0 : 0 < i := by omega
    have hj0 : 0 < j := by omega
    have hiD : 0 < D*i := Nat.mul_pos hD hi0
    have hjD : 0 < D*j := Nat.mul_pos hD hj0
    have hiDH : D*i ≤ D*H := Nat.mul_le_mul_left D hiH
    have hjDH : D*j ≤ D*H := Nat.mul_le_mul_left D hjH
    have hgi : g ≤ D*i := by nlinarith
    have hgj : g ≤ D*j := by nlinarith
    let E : ℝ := ∑ w : ZMod p, |(crossCharFiber (U (D*i)) (U (D*j)) w : ℝ)|
    have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hei := henergy i (Finset.mem_range.mpr (by omega))
    have hej := henergy j (Finset.mem_range.mpr (by omega))
    simp only [Finset.card_range,Nat.cast_add,Nat.cast_one] at hei hej
    obtain ⟨hes,_⟩ := interval_mixed_l1_sq a (2*(D*i)) (2*(D*j)) (8*(H+1))
      (by positivity) hei hej
    have hEsq : E^2 ≤ 32*((H : ℝ)+1)*(2*D*i)*(2*D*j)*(2*D*i+2*D*j+1) := by
      change E^2 ≤ _ at hes
      push_cast at hes
      have hh : 0 ≤ ((H : ℝ)+1)*(2*D*i)*(2*D*j)*(2*D*i+2*D*j+1) := by positivity
      have hb0 : 0 ≤ ((H : ℝ)+1)*(2*D*i)*(2*D*j) := by positivity
      nlinarith
    have hTE := scaled_error_bound T D H i j E hT (Nat.cast_nonneg H)
      (by dsimp [D]; push_cast; rfl) (by exact_mod_cast hi0) (by exact_mod_cast hj0) hEsq
    have hTE' : (T : ℝ)*E ≤ 2*(D : ℝ)^2*i*j := by
      have hh : 0 ≤ (T : ℝ)*(12*D*i+12*D*j+8) := by positivity
      nlinarith
    have hcost := natural_banded_cost (D*i) (D*j) g hg hgi hgj
    have hCerr : |(pairCount (C (D*i)) (C (D*j)) z : ℝ)-4*(D : ℝ)^2*i*j| ≤
        E+(17/(g : ℝ))*(4*(D : ℝ)^2*i*j) := by
      obtain ⟨hzeroC,hother⟩ := hC (D*i) hiD hiDH (D*j) hjD hjDH
      by_cases hz : z=0
      · subst z
        rw [hzeroC]
        push_cast
        have he : (1 : ℝ)+4*((D : ℝ)*i)*((D : ℝ)*j)-4*(D : ℝ)^2*i*j=1 := by ring
        rw [he,abs_one]
        have hgR : (0 : ℝ) < g := by exact_mod_cast hg
        have hgiR : (g : ℝ) ≤ D*i := by exact_mod_cast hgi
        have hjR : (1 : ℝ) ≤ D*j := by exact_mod_cast hjD
        have hh : 1 ≤ (17/(g : ℝ))*(4*(D : ℝ)^2*i*j) := by
          apply (mul_le_mul_iff_left₀ hgR).mp
          have hmul := mul_le_mul_of_nonneg_left hjR (show 0 ≤ (D : ℝ)*i by positivity)
          have heq : ((17/(g : ℝ))*(4*(D : ℝ)^2*i*j))*g=68*(D : ℝ)^2*i*j := by field_simp; ring
          rw [heq]
          nlinarith
        linarith
      · have hUi : ∀ u∈U (D*i), u ≠ 0 := fun u hu ↦ hzero u
          (intervalTranslate_mono p a (by omega) hu)
        have hUj : ∀ u∈U (D*j), u ≠ 0 := fun u hu ↦ hzero u
          (intervalTranslate_mono p a (by omega) hu)
        have hUij : ∀ u∈U (D*i), ∀ v∈U (D*j), u+v ≠ 0 := fun u hu v hv ↦ hopp u
          (intervalTranslate_mono p a (by omega) hu) v (intervalTranslate_mono p a (by omega) hv)
        have hnei : (U (D*i)).Nonempty := Finset.card_pos.mp (by rw [hcard _ hiDH]; omega)
        have hnej : (U (D*j)).Nonempty := Finset.card_pos.mp (by rw [hcard _ hjDH]; omega)
        have hbase := cross_graph_error hF (U (D*i)) (U (D*j)) hUi hUj hUij hnei hnej z hz
        rw [hcard _ hiDH,hcard _ hjDH] at hbase
        have hbaser : |(pairCount (parabolaSet (U (D*i))) (parabolaSet (U (D*j))) z : ℝ)-
            4*(D : ℝ)^2*i*j| ≤ E+2*(D*i)+2*(D*j) := by
          have hh : |(pairCount (parabolaSet (U (D*i))) (parabolaSet (U (D*j))) z : ℝ)-
              (2*(D*i : ℕ))*(2*(D*j : ℕ))| ≤ E+2*(D*i)+2*(D*j) := by
            dsimp [E]
            exact_mod_cast hbase
          convert hh using 1 <;> push_cast <;> ring
        obtain ⟨hlo,hhi⟩ := hother z hz
        have hlor : (pairCount (parabolaSet (U (D*i))) (parabolaSet (U (D*j))) z : ℝ) ≤
            pairCount (C (D*i)) (C (D*j)) z := by exact_mod_cast hlo
        have hhir : (pairCount (C (D*i)) (C (D*j)) z : ℝ) ≤
            pairCount (parabolaSet (U (D*i))) (parabolaSet (U (D*j))) z+
            8*(D*i)*((D*j/g : ℕ)+1)+8*((D*i/g : ℕ)+1)*(D*j)+
              8*((D*i/g : ℕ)+1)*((D*j/g : ℕ)+1) := by exact_mod_cast hhi
        push_cast at hcost
        rw [abs_le] at hbaser ⊢
        constructor <;> nlinarith
    simp only [B,if_neg hi,if_neg hj]
    apply hCerr.trans
    apply (mul_le_mul_iff_right₀ hT0).mp
    have heq : (T : ℝ)*(17/(g : ℝ))=1/4 := by dsimp [g]; push_cast; field_simp; ring
    have hm := mul_le_mul_of_nonneg_right hηT.le (show 0 ≤ 4*(D : ℝ)^2*i*j by positivity)
    have hh : (T : ℝ)*(E+(17/(g : ℝ))*(4*(D : ℝ)^2*i*j))=
        T*E+(D : ℝ)^2*i*j := by rw [mul_add,← mul_assoc,heq]; ring
    rw [hh]
    nlinarith [show 0 ≤ (D : ℝ)^2*i*j by positivity]

end Erdos66EveryPrimeBandedRelative
