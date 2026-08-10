import FormalConjectures.Util.ProblemImports
open Nat Finset

theorem all_even (x y z w : ℕ) (h : 8 ∣ (x^2+y^2+z^2+w^2)) :
    2∣x ∧ 2∣y ∧ 2∣z ∧ 2∣w := by
  have key : ∀ a b c d : ZMod 8, a^2+b^2+c^2+d^2 = 0 →
      (a=0∨a=2∨a=4∨a=6)∧(b=0∨b=2∨b=4∨b=6)∧(c=0∨c=2∨c=4∨c=6)∧(d=0∨d=2∨d=4∨d=6) := by decide
  have hcast : ∀ a : ZMod 8, (a=0∨a=2∨a=4∨a=6) →
      (ZMod.castHom (show (2:ℕ)∣8 by norm_num) (ZMod 2)) a = 0 := by decide
  have hz : ((x^2+y^2+z^2+w^2 : ℕ) : ZMod 8) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact h
  push_cast at hz
  obtain ⟨hx, hy, hz2, hw⟩ := key _ _ _ _ hz
  have lift : ∀ t : ℕ, ((t:ZMod 8)=0∨(t:ZMod 8)=2∨(t:ZMod 8)=4∨(t:ZMod 8)=6) → 2∣t := by
    intro t ht
    have h2 : (ZMod.castHom (show (2:ℕ)∣8 by norm_num) (ZMod 2)) (t:ZMod 8) = 0 := hcast _ ht
    rw [map_natCast] at h2
    exact (ZMod.natCast_eq_zero_iff t 2).mp h2
  exact ⟨lift x hx, lift y hy, lift z hz2, lift w hw⟩

-- A perfect-square predicate transfer helper
theorem sq4 (c : ℕ) : (4*c).sqrt * (4*c).sqrt = 4*c ↔ c.sqrt * c.sqrt = c := by
  rw [← Nat.exists_mul_self, ← Nat.exists_mul_self]
  constructor
  · rintro ⟨s, hs⟩
    have h2 : 2 ∣ s := by
      have : 2 ∣ s*s := by rw [hs]; exact ⟨2*c, by ring⟩
      exact (Nat.Prime.dvd_mul Nat.prime_two).mp this |>.elim id id
    obtain ⟨d, rfl⟩ := h2
    exact ⟨d, by nlinarith [hs]⟩
  · rintro ⟨d, rfl⟩
    exact ⟨2*d, by ring⟩

theorem all_div4 (x y z w N : ℕ) (hN : 2 ∣ N) (h : x^2+y^2+z^2+w^2 = 16*N) :
    4∣x ∧ 4∣y ∧ 4∣z ∧ 4∣w := by
  have h8 : 8 ∣ (x^2+y^2+z^2+w^2) := by rw [h]; exact ⟨2*N, by ring⟩
  obtain ⟨ex, ey, ez, ew⟩ := all_even x y z w h8
  obtain ⟨x', rfl⟩ := ex; obtain ⟨y', rfl⟩ := ey
  obtain ⟨z', rfl⟩ := ez; obtain ⟨w', rfl⟩ := ew
  have h4 : x'^2+y'^2+z'^2+w'^2 = 4*N := by nlinarith [h]
  have h8' : 8 ∣ (x'^2+y'^2+z'^2+w'^2) := by
    rw [h4]; obtain ⟨k, rfl⟩ := hN; exact ⟨k, by ring⟩
  obtain ⟨ex', ey', ez', ew'⟩ := all_even x' y' z' w' h8'
  obtain ⟨x'', rfl⟩ := ex'; obtain ⟨y'', rfl⟩ := ey'
  obtain ⟨z'', rfl⟩ := ez'; obtain ⟨w'', rfl⟩ := ew'
  exact ⟨⟨x'', by ring⟩, ⟨y'', by ring⟩, ⟨z'', by ring⟩, ⟨w'', by ring⟩⟩

def a (n : ℕ) : ℕ :=
  let M := n.sqrt
  let R := range (M + 1)
  let BoundingBox := (R.product R).product (R.product R)
  Finset.card
    (BoundingBox.filter (fun p =>
      let ((x, y), (z, w)) := p
      x^2 + y^2 + z^2 + w^2 = n ∧
      let c := 3 * x + 10 * y + 36 * z
      c > 0 ∧ c.sqrt * c.sqrt = c))


def boxf (n : ℕ) : Finset (ℕ×ℕ) :=
  (range (n.sqrt+1)).product (range (n.sqrt+1))

theorem a_eq (n : ℕ) :
    a n = Finset.card
      (((boxf n).product (boxf n)).filter (fun p =>
        let ((x, y), (z, w)) := p
        x^2 + y^2 + z^2 + w^2 = n ∧
        0 < 3*x+10*y+36*z ∧ (3*x+10*y+36*z).sqrt * (3*x+10*y+36*z).sqrt = 3*x+10*y+36*z)) := by
  rfl

theorem mem_iff (n : ℕ) (x y z w : ℕ) :
    (((x,y),(z,w)) ∈ (((boxf n).product (boxf n)).filter (fun p =>
        let ((x, y), (z, w)) := p
        x^2 + y^2 + z^2 + w^2 = n ∧
        0 < 3*x+10*y+36*z ∧ (3*x+10*y+36*z).sqrt * (3*x+10*y+36*z).sqrt = 3*x+10*y+36*z)))
    ↔ (x^2+y^2+z^2+w^2 = n ∧ 0 < 3*x+10*y+36*z ∧
        (3*x+10*y+36*z).sqrt * (3*x+10*y+36*z).sqrt = 3*x+10*y+36*z) := by
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨hsum, _, _⟩ := h
    have hx : x ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith [hsum])
    have hy : y ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith [hsum])
    have hz : z ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith [hsum])
    have hw : w ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith [hsum])
    refine Finset.mk_mem_product (Finset.mk_mem_product ?_ ?_) (Finset.mk_mem_product ?_ ?_) <;>
      (rw [Finset.mem_range]; omega)

-- Filter finset
def F (n : ℕ) : Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  ((boxf n).product (boxf n)).filter (fun p =>
    let ((x, y), (z, w)) := p
    x^2 + y^2 + z^2 + w^2 = n ∧
    0 < 3*x+10*y+36*z ∧ (3*x+10*y+36*z).sqrt * (3*x+10*y+36*z).sqrt = 3*x+10*y+36*z)

theorem a_eq2 (n : ℕ) : a n = (F n).card := a_eq n

theorem memF (n x y z w : ℕ) :
    ((x,y),(z,w)) ∈ F n ↔
      (x^2+y^2+z^2+w^2 = n ∧ 0 < 3*x+10*y+36*z ∧
        (3*x+10*y+36*z).sqrt * (3*x+10*y+36*z).sqrt = 3*x+10*y+36*z) := mem_iff n x y z w

theorem descent (N : ℕ) (hN : 2 ∣ N) : a (16 * N) = a N := by
  rw [a_eq2, a_eq2]
  apply Finset.card_nbij'
    (i := fun p => ((p.1.1/4, p.1.2/4),(p.2.1/4, p.2.2/4)))
    (j := fun q => ((q.1.1*4, q.1.2*4),(q.2.1*4, q.2.2*4)))
  · -- MapsTo i (F 16N) (F N)
    rintro ⟨⟨x,y⟩,⟨z,w⟩⟩ hp
    rw [Finset.mem_coe, memF] at hp
    obtain ⟨hsum, hpos, hsq⟩ := hp
    obtain ⟨⟨x',rfl⟩,⟨y',rfl⟩,⟨z',rfl⟩,⟨w',rfl⟩⟩ := all_div4 x y z w N hN hsum
    simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    rw [Finset.mem_coe, memF]
    refine ⟨by nlinarith [hsum], ?_, ?_⟩
    · nlinarith [hpos]
    · have : 3*(4*x')+10*(4*y')+36*(4*z') = 4*(3*x'+10*y'+36*z') := by ring
      rw [this] at hsq
      exact (sq4 _).mp hsq
  · -- MapsTo j (F N) (F 16N)
    rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hq
    rw [Finset.mem_coe, memF] at hq
    obtain ⟨hsum, hpos, hsq⟩ := hq
    rw [Finset.mem_coe, memF]
    refine ⟨by nlinarith [hsum], by nlinarith [hpos], ?_⟩
    have : 3*(a*4)+10*(b*4)+36*(c*4) = 4*(3*a+10*b+36*c) := by ring
    rw [this]
    exact (sq4 _).mpr hsq
  · -- LeftInvOn
    rintro ⟨⟨x,y⟩,⟨z,w⟩⟩ hp
    rw [Finset.mem_coe, memF] at hp
    obtain ⟨hsum, _, _⟩ := hp
    obtain ⟨⟨x',rfl⟩,⟨y',rfl⟩,⟨z',rfl⟩,⟨w',rfl⟩⟩ := all_div4 x y z w N hN hsum
    simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4), Prod.mk.injEq]
    omega
  · -- RightInvOn
    rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hq
    simp only [Nat.mul_div_cancel _ (by norm_num : 0 < 4)]

theorem base8 : a 8 = 0 := by native_decide
theorem base24 : a 24 = 0 := by native_decide
theorem base40 : a 40 = 0 := by native_decide
theorem base488 : a 488 = 0 := by native_decide

theorem reverse (k m : ℕ) (hm : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) :
    a (2^(4*k+3) * m) = 0 := by
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    rcases hm with rfl|rfl|rfl|rfl
    · exact base8
    · exact base24
    · exact base40
    · exact base488
  | succ n ih =>
    have e1 : 2^(4*(n+1)+3) * m = 16 * (2^(4*n+3) * m) := by
      rw [show 4*(n+1)+3 = (4*n+3)+4 by ring, pow_add]; ring
    rw [e1]
    rw [descent (2^(4*n+3) * m) ⟨2^(4*n+2)*m, by rw [show 4*n+3 = (4*n+2)+1 by ring, pow_add]; ring⟩]
    exact ih

theorem oeis_338019_conjecture_0 (n : ℕ) (h_n_pos : n > 0) :
  (a n = 0 ↔ ∃ k : ℕ, ∃ m : ℕ,
    (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) ∧ n = 2^(4 * k + 3) * m) ∧
  (¬ (8 ∣ n) → a n > 0) := by
  constructor
  · constructor
    · intro h
      sorry
    · rintro ⟨k, m, hm, rfl⟩
      exact reverse k m hm
  · intro h
    sorry
