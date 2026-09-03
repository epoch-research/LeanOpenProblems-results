import Submission.QuadraticPrimeTail
import Submission.QuadraticSquareTail

/-! Natural-box versions of the fixed-form prime estimates. -/
namespace Erdos1206.QuadraticNaturalPrime
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticPrimeDivisibility
  QuadraticSquarefreeSieve
open scoped Classical
set_option maxHeartbeats 1000000

def lift (x : ℕ × ℕ) : Vec := ((x.1:ℤ),(x.2:ℤ))

lemma lift_injective : Function.Injective lift := by
  intro x y h
  exact Prod.ext (Int.ofNat.inj (congrArg Prod.fst h)) (Int.ofNat.inj (congrArg Prod.snd h))

lemma lift_mem_box {N : ℕ} {x : ℕ × ℕ} (hx : x∈range N ×ˢ range N) :
    lift x∈QuadraticLatticeLines.box N := by
  apply mem_box_iff.mpr
  obtain ⟨hx1,hx2⟩ := mem_product.mp hx
  dsimp [ht,lift]
  rw [abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
  exact max_le (by exact_mod_cast (mem_range.mp hx1).le) (by exact_mod_cast (mem_range.mp hx2).le)

lemma form_lift (a b c : ℕ) (x : ℕ × ℕ) :
    form c b a (lift x)=(quad a b c x.1 x.2:ℤ) := by
  dsimp [form,lift,quad]
  ring

lemma prime_box_bound (a b c N p : ℕ) (hQ : Anisotropic c b a) (hp : p.Prime) :
    ((((range N ×ˢ range N).filter (fun x => p ∣ quad a b c x.1 x.2)).card):ℝ) ≤
      48*mass c b a*(N:ℝ)^2/p+1 := by
  let S := (range N ×ˢ range N).filter (fun x => p∣quad a b c x.1 x.2)
  have hmap : ∀ x∈S.erase 0, lift x∈points c b a N p := by
    intro x hx
    obtain ⟨hx0,hx⟩ := mem_erase.mp hx
    obtain ⟨hxbox,hdiv⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨lift_mem_box hxbox,?_,?_⟩
    · exact fun he => hx0 (lift_injective he)
    · rw [form_lift]
      exact_mod_cast hdiv
  have hcard := card_le_card_of_injOn lift hmap (lift_injective.injOn)
  have hrem : S.card ≤ (S.erase 0).card+1 := by
    by_cases hz : 0∈S
    · exact (card_erase_add_one hz).symm.le
    · simp [erase_eq_of_notMem hz]
  have hbound := prime_divisibility_bound hQ N p hp
  have hcardR : ((S.erase 0).card:ℝ) ≤ (points c b a N p).card := by exact_mod_cast hcard
  have hremR : (S.card:ℝ) ≤ (S.erase 0).card+1 := by exact_mod_cast hrem
  have hboundR : (p:ℝ)*(points c b a N p).card ≤ 48*mass c b a*(N:ℝ)^2 := by
    exact_mod_cast hbound
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hh : ((points c b a N p).card:ℝ) ≤ 48*mass c b a*(N:ℝ)^2/p :=
    (le_div_iff₀ hpR).mpr (by simpa only [mul_comm] using hboundR)
  change (S.card:ℝ) ≤ _
  linarith

noncomputable def badTail (a b c : ℕ) (B : Set ℕ) (H N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter (fun x => 0 < x.1 ∧
    ∃ p∈B, H < p ∧ p∣quad a b c x.1 x.2)

lemma badTail_card_le (a b c : ℕ) (B : Set ℕ) (H N : ℕ) :
    (badTail a b c B H N).card ≤ (QuadraticPrimeTail.badTail c b a B H N).card := by
  apply card_le_card_of_injOn lift _ lift_injective.injOn
  intro x hx
  obtain ⟨hxbox,hxpos,p,hp,hH,hdiv⟩ := mem_filter.mp hx
  apply mem_filter.mpr
  refine ⟨lift_mem_box hxbox,?_,p,hp,hH,?_⟩
  · intro he
    have hh : x.1=0 := Int.ofNat.inj (congrArg Prod.fst he)
    omega
  · rw [form_lift]
    exact_mod_cast hdiv

lemma badTail_mono {a b c H K N : ℕ} {B : Set ℕ} (hHK : H ≤ K) :
    badTail a b c B K N ⊆ badTail a b c B H N := by
  intro x hx
  obtain ⟨hxbox,hxpos,p,hp,hKp,hdiv⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hxbox,hxpos,p,hp,lt_of_le_of_lt hHK hKp,hdiv⟩

#print axioms prime_box_bound
#print axioms badTail_card_le
end Erdos1206.QuadraticNaturalPrime
