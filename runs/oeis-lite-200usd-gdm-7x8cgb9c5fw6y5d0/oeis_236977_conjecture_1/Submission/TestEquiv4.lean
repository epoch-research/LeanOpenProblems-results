import FormalConjectures.Util.ProblemImports



set_option maxRecDepth 8000

open Nat Finset

def totient_range_acc (n : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, L, R, acc =>
    if L = R ∧ L.Coprime n then acc + 1 else acc
  | fuel + 1, L, R, acc =>
    if L > R then acc
    else if L = R then
      if L.Coprime n then acc + 1 else acc
    else
      let mid := (L + R) / 2
      let acc' := totient_range_acc n fuel L mid acc
      totient_range_acc n fuel (mid + 1) R acc'

lemma Ico_split {L mid R : ℕ} (h1 : L ≤ mid) (h2 : mid < R) :
    Ico L R = Ico L (mid + 1) ∪ Ico (mid + 1) R := by
  ext x
  simp only [mem_Ico, mem_union]
  omega

lemma card_filter_union_disjoint {α : Type _} [DecidableEq α] (s1 s2 : Finset α) (p : α → Prop) [DecidablePred p]
    (h : Disjoint s1 s2) :
    (filter p (s1 ∪ s2)).card = (filter p s1).card + (filter p s2).card := by
  rw [filter_union, card_union_of_disjoint]
  rw [disjoint_iff_ne]
  intro x hx y hy hxy
  simp only [mem_filter] at hx hy
  rw [disjoint_iff_ne] at h
  exact @h x hx.left y hy.left hxy

lemma totient_range_acc_eq (n : Nat) (fuel : Nat) : ∀ L R acc, R - L < 2 ^ fuel →
    (L > R → totient_range_acc n fuel L R acc = acc) ∧
    (L ≤ R → totient_range_acc n fuel L R acc = acc + ((Ico L (R + 1)).filter (·.Coprime n)).card) := by
  induction fuel with
  | zero =>
    intro L R acc h_lt
    simp only [Nat.pow_zero] at h_lt
    constructor
    · intro h_gt; dsimp [totient_range_acc]
      have : ¬ (L = R ∧ L.Coprime n) := by omega
      rw [if_neg this]
    · intro h_le
      have h_eq : L = R := by omega
      dsimp [totient_range_acc]
      rw [h_eq]
      have h_range : Ico R (R + 1) = {R} := by
        ext x
        simp only [mem_Ico, mem_singleton]
        omega
      rw [h_range, filter_singleton]
      by_cases h_cop : R.Coprime n
      · have : R = R ∧ R.Coprime n := ⟨rfl, h_cop⟩
        rw [if_pos this, if_pos h_cop]
        simp
      · have : ¬ (R = R ∧ R.Coprime n) := by tauto
        rw [if_neg this, if_neg h_cop]
        simp
  | succ fuel ih =>
    intro L R acc h_lt
    constructor
    · intro h_gt
      dsimp [totient_range_acc]
      rw [if_pos h_gt]
    · intro h_le
      dsimp [totient_range_acc]
      by_cases h_eq : L = R
      · rw [if_neg (by omega), if_pos h_eq]
        rw [h_eq]
        have h_range : Ico R (R + 1) = {R} := by
          ext x
          simp only [mem_Ico, mem_singleton]
          omega
        rw [h_range, filter_singleton]
        by_cases h_cop : R.Coprime n
        · rw [if_pos h_cop, if_pos h_cop]
          simp
        · rw [if_neg h_cop, if_neg h_cop]
          simp
      · have h_lt_R : L < R := by omega
        rw [if_neg (by omega), if_neg h_eq]
        let mid := (L + R) / 2
        have h_mid_ge : L ≤ mid := by omega
        have h_mid_lt : mid < R := by omega
        have h_lt_left : mid - L < 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := by ring
          omega
        have h_lt_right : R - (mid + 1) < 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := by ring
          omega
        have ih_left := (ih L mid acc h_lt_left).right h_mid_ge
        rw [ih_left]
        have ih_right := (ih (mid + 1) R (acc + ((Ico L (mid + 1)).filter (·.Coprime n)).card) h_lt_right).right (by omega)
        rw [ih_right]
        have h_split : Ico L (R + 1) = Ico L (mid + 1) ∪ Ico (mid + 1) (R + 1) := by
          apply Ico_split h_mid_ge (by omega)
        rw [h_split]
        rw [card_filter_union_disjoint]
        · ring
        · rw [disjoint_iff_ne]
          intro x hx y hy hxy
          simp only [mem_Ico] at hx hy
          omega

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_range_acc n 25 1 (n - 1) 0

theorem totient_fast_eq_totient (n : Nat) (h_lim : n ≤ 2 * 10^6) : totient_fast n = Nat.totient n := by
  by_cases h0 : n = 0
  · rw [h0]
    rfl
  · by_cases h1 : n = 1
    · rw [h1]
      rfl
    · have hn : n > 1 := by omega
      dsimp [totient_fast]
      rw [if_neg h0, if_neg h1]
      have h_eq := (totient_range_acc_eq n 25 1 (n - 1) 0 (by omega)).right (by omega)
      rw [h_eq]
      rw [zero_add]
      have h_sub : n - 1 + 1 = n := by omega
      rw [h_sub]
      rw [Nat.totient]
      have h_range : range n = insert 0 (Ico 1 n) := by
        ext x
        simp only [mem_range, mem_insert, mem_Ico]
        omega
      rw [h_range, filter_insert]
      have h_not_cop : ¬ n.Coprime 0 := by
        intro hc
        rw [Nat.Coprime] at hc
        rw [Nat.gcd_zero_right] at hc
        omega
      rw [if_neg h_not_cop]
      congr 1
      ext x
      simp only [mem_filter, mem_Ico]
      rw [Nat.coprime_comm]

def get_index (n : Nat) : Nat :=
  let q := n / 30
  let r := n % 30
  let val := match r with
    | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 4 | 8 => 5 | 9 => 6
    | 10 => 6 | 11 => 6 | 12 => 7 | 13 => 7 | 14 => 8 | 15 => 9 | 16 => 9 | 17 => 10 | 18 => 11 | 19 => 11
    | 20 => 12 | 21 => 12 | 22 => 12 | 23 => 13 | 24 => 14 | 25 => 14 | 26 => 15 | 27 => 16 | 28 => 16
    | _ => 17
  18 * q + val - 6

def hex_char_val (c : Char) : Nat :=
  let val := c.toNat
  if val ≥ 48 ∧ val ≤ 57 then val - 48
  else if val ≥ 97 ∧ val ≤ 102 then val - 87
  else 0

def decode_witness (s : String) (idx : Nat) : Nat :=
  let p0 := 4 * idx
  let c0 := s.get ⟨p0⟩
  let c1 := s.get ⟨p0 + 1⟩
  let c2 := s.get ⟨p0 + 2⟩
  let c3 := s.get ⟨p0 + 3⟩
  hex_char_val c0 * 4096 + hex_char_val c1 * 256 + hex_char_val c2 * 16 + hex_char_val c3

def check_single (s : String) (n : Nat) : Bool :=
  if n % 6 = 3 ∨ n % 10 = 0 ∨ n % 6 = 0 then true
  else
    let idx := get_index n
    let k := decode_witness s idx
    if k = 0 ∨ k > (n - 1) / 2 then false
    else
      let m := totient_fast k * totient_fast (n - k)
      sqrt m ^ 2 == m

def check_all_loop (s : String) : Nat → Nat → Nat → Bool
  | 0, L, R =>
    if L = R then check_single s L else true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then check_single s L
    else
      let mid := (L + R) / 2
      check_all_loop s fuel L mid && check_all_loop s fuel (mid + 1) R

def witnesses_str : String := "00010001000200070005000200030003000600060004000c0004000e00020001000500010001001000060007000a00010007000500040008000100020001000200010002000300040003000a00060002000100050008000300070001000700100007000e00030004000600030006000200070004001000010010000500010002000a0005000400080004000d000100020005000500080008000100040011000b0011000a000c00030003000400060003000d00060001000f00100003000400060002001b0005000e00080010000d000c000d0003000200060029000100020006000500020005000100010002000e000500550008000a0007000900300002000d000500040008000a000400090013001100040015000100020010000500040008000100130007000400110002000500140008000700090009000f001000010002001200030006000a00220001000200090014000100070018000200170005000a000800010004000c00090007000a00010002000700130003000a000300200003004100060007000f000d000f000e000300040006000e00220009001b000d00100007001300120015001800010007000300010075000a000c001d00040002001a0005002300040018000d000c0013000100070022000d0002000a0005000300080004000c0029001c000b000e000b00160010001600070014001b00010002006000050001000a000500010002000a0005000b0001000a000d00010002000500040008000a002100010022000500100008000a0014001c001b00040011005900200002001f000500090008000a000b000300010001000e0005003c000800010001000500050008000a000a000c00090011000e000d0050001200220007000100020020000100010002000500030004000600110004002a0011000f0010000100020001000200130005000a00010015001900110007000300040030000e000300040006000f0010000700090014000f00070003001200060018000d00120010000f000d00140014002600010002000500050008000800010033002600110011000300060001000700400021002c0007000a000c00130025000e000b00070022001e000e00020002001a0005000b0008000a0007000c001100090011000e00230015000b0003000400060020002200160009000f0010000e0013002a0012000d003000030003000400060021003c001c0003000f000600140013004a00180004000f001b001e003d000300040003000400010007000500040008000a00070009000700090009001000260003000d00060044001c003d002200010007001a001400010023000a000c001b000100020005002c0008000100020032000d0008000a00160087000700090011002c0019000b00200050000d003800280020002200250045000b001a000400360027006100010002002900050008000a00090003000400060004000900130014000e0010004c00120002000900050014001d000300040004002e000d0004000e000f001000100013001300140010002700130014002d00170023000b0040002c0010004e0013000700090007000100020036000500120008000200010002002900050001000a000500040001000a0011001a00120022000a000c0024000100040016001f001f0015000200270005001c00080014000100020010000500010002000300300006000a000e000f000d000f0014002600140009001b0018000e001a00040001004c0025001c0026000a000c000100020023000500210008000a00360004001500410011000300440006000100020013000200080005002a0008000b0013000c0004001b0011000d0044005f0054001000070009000700160001000200120005002400080004003d0019002600110037000d0002000400050008003f0007000c000f00010007000e0004001f0018000a0038001e0060000200230005000800230046000c0010000900040014000e002500040012000900010002000e00010004000a"

theorem check_all_verified : check_all_loop witnesses_str 25 9 100 = true := by
  decide
