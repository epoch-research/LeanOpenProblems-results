import Submission.OddCycleColoring

/-!
A finite source with no three distinct ordered representations of a cube sum
or positive cube difference, but with an odd-incidence coloring obstruction.
This does not rule out ordinary proper coloring or settle the density problem.
All certificate checks use kernel reduction.
-/
namespace Erdos1206.HigherCycleObstruction
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alternating {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: alternating l

private lemma count_alternating (n : ℕ) (l : List ℕ) :
    l.count n = (alternating l).count n + (alternating l.tail).count n := by
  induction l using List.twoStepInduction with
  | nil => simp [alternating]
  | singleton a => simp [alternating]
  | cons_cons a b l ih _ =>
    have hh := ih
    cases l with
    | nil => simp [alternating, List.count_cons, Nat.add_comm]
    | cons z l =>
      simp only [alternating, List.tail_cons, List.count_cons] at hh ⊢
      omega

private lemma count_le_two (l : List ℕ)
    (h₀ : (alternating l).IsChain (· < ·))
    (h₁ : (alternating l.tail).IsChain (· < ·)) (n : ℕ) :
    l.count n ≤ 2 := by
  have hnd₀ : (alternating l).Nodup := h₀.pairwise.imp (fun h => h.ne)
  have hnd₁ : (alternating l.tail).Nodup := h₁.pairwise.imp (fun h => h.ne)
  have h₀' := List.nodup_iff_count_le_one.mp hnd₀ n
  have h₁' := List.nodup_iff_count_le_one.mp hnd₁ n
  rw [count_alternating]
  omega

def rootsList : List ℕ :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 15, 17, 18, 19, 20, 21, 22, 24, 25, 27, 30, 31, 32, 33, 35, 36, 38, 40, 41, 42, 44, 45, 47, 48, 49, 50, 51, 54, 55, 57, 58, 59, 60, 62, 63, 64, 66, 67, 72, 73, 75, 76, 80, 81, 82, 84, 87, 90, 92, 93, 94, 96, 97, 99, 100, 101, 103, 105, 107, 108, 110, 112, 113, 114, 115, 116, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 132, 133, 135, 138, 140, 144, 145, 147, 150, 151, 152, 153, 159, 160, 161, 164, 166, 167, 168, 171, 174, 175, 176, 177, 180, 184, 188, 189, 190, 192, 194, 196, 197, 198, 200, 206, 210, 212, 214, 216, 217, 219, 220, 225, 228, 229, 231, 233, 235, 236, 240, 243, 244, 248, 249, 250, 252, 254, 256, 257, 258, 261, 264, 265, 266, 267, 270, 271, 276, 279, 280, 282, 285, 288, 290, 292, 294, 295, 298, 300, 303, 309, 310, 311, 315, 316, 318, 319, 320, 328, 332, 334, 336, 339, 341, 342, 348, 350, 354, 358, 360, 363, 368, 369, 376, 378, 379, 380, 386, 387, 388, 392, 394, 396, 399, 401, 405, 412, 420, 423, 432, 435, 438, 440, 441, 443, 444, 447, 450, 460, 462, 463, 464, 465, 467, 470, 472, 477, 479, 480, 484, 486, 487, 490, 496, 498, 500, 503, 504, 508, 514, 528, 530, 532, 540, 545, 561, 564, 567, 568, 570, 576, 584, 588, 590, 591, 600, 615, 617, 618, 625, 630, 633, 638, 640, 645, 654, 656, 658, 668, 672, 690, 695, 696, 699, 700, 729, 730, 736, 751, 752, 756, 760, 762, 765, 784]

def data : List (ℕ × ℕ × ℕ × ℕ) :=
  [
    (1, 9, 10, 12),
    (4, 18, 30, 32),
    (12, 31, 33, 40),
    (6, 27, 45, 48),
    (20, 38, 48, 54),
    (17, 24, 54, 55),
    (9, 22, 57, 58),
    (5, 45, 50, 60),
    (8, 36, 60, 64),
    (17, 38, 73, 76),
    (10, 45, 75, 80),
    (30, 57, 72, 81),
    (51, 64, 75, 82),
    (50, 59, 93, 96),
    (47, 66, 90, 97),
    (20, 33, 96, 97),
    (40, 76, 96, 108),
    (9, 81, 90, 108),
    (4, 67, 101, 110),
    (14, 63, 105, 112),
    (55, 92, 94, 113),
    (36, 93, 99, 120),
    (42, 49, 120, 121),
    (84, 112, 122, 138),
    (18, 81, 135, 144),
    (4, 41, 151, 152),
    (36, 114, 129, 153),
    (18, 121, 122, 153),
    (24, 87, 150, 159),
    (48, 124, 132, 160),
    (20, 90, 150, 160),
    (10, 84, 153, 161),
    (32, 129, 135, 166),
    (25, 64, 164, 167),
    (14, 126, 140, 168),
    (27, 66, 171, 174),
    (15, 135, 150, 180),
    (9, 66, 177, 180),
    (66, 105, 175, 184),
    (40, 66, 192, 194),
    (94, 132, 180, 194),
    (45, 133, 174, 196),
    (2, 128, 188, 206),
    (116, 147, 197, 210),
    (32, 116, 200, 212),
    (80, 152, 192, 216),
    (84, 145, 198, 217),
    (19, 171, 190, 228),
    (51, 114, 219, 228),
    (10, 108, 225, 233),
    (47, 176, 194, 233),
    (30, 135, 225, 240),
    (20, 180, 200, 240),
    (90, 171, 216, 243),
    (1, 135, 235, 249),
    (21, 189, 210, 252),
    (4, 190, 212, 254),
    (5, 197, 206, 254),
    (32, 144, 240, 256),
    (21, 167, 231, 257),
    (22, 198, 220, 264),
    (40, 145, 250, 265),
    (6, 123, 258, 267),
    (73, 177, 244, 270),
    (84, 217, 231, 280),
    (35, 99, 276, 280),
    (24, 216, 240, 288),
    (150, 177, 279, 288),
    (107, 235, 236, 292),
    (105, 177, 276, 294),
    (72, 189, 267, 294),
    (35, 219, 252, 298),
    (188, 225, 279, 298),
    (25, 225, 250, 300),
    (4, 166, 282, 300),
    (15, 110, 295, 300),
    (24, 151, 290, 303),
    (3, 192, 282, 309),
    (5, 66, 309, 310),
    (5, 248, 252, 315),
    (41, 72, 318, 319),
    (80, 194, 295, 319),
    (96, 248, 264, 320),
    (64, 258, 270, 332),
    (62, 243, 285, 334),
    (50, 128, 328, 334),
    (81, 107, 339, 341),
    (54, 132, 342, 348),
    (3, 115, 354, 358),
    (80, 214, 332, 358),
    (30, 270, 300, 360),
    (18, 132, 354, 360),
    (126, 147, 360, 363),
    (132, 210, 350, 368),
    (92, 252, 336, 376),
    (140, 266, 336, 378),
    (125, 216, 368, 387),
    (123, 180, 379, 388),
    (90, 266, 348, 392),
    (103, 164, 394, 401),
    (150, 285, 360, 405),
    (120, 271, 386, 423),
    (113, 320, 354, 423),
    (100, 334, 354, 432),
    (54, 243, 405, 432),
    (62, 125, 435, 438),
    (132, 341, 363, 440),
    (160, 332, 379, 443),
    (45, 318, 380, 443),
    (64, 127, 444, 447),
    (105, 328, 401, 462),
    (58, 261, 435, 464),
    (115, 315, 420, 470),
    (150, 229, 464, 477),
    (72, 261, 450, 477),
    (250, 295, 465, 480),
    (168, 196, 480, 484),
    (180, 342, 432, 486),
    (153, 316, 444, 487),
    (175, 295, 460, 490),
    (96, 387, 405, 498),
    (2, 270, 470, 498),
    (64, 159, 498, 503),
    (350, 392, 479, 503),
    (264, 369, 463, 508),
    (31, 250, 487, 508),
    (10, 394, 412, 508),
    (42, 334, 462, 514),
    (44, 396, 440, 528),
    (80, 290, 500, 530),
    (40, 236, 514, 530),
    (45, 405, 450, 540),
    (171, 339, 498, 540),
    (310, 450, 465, 545),
    (229, 447, 463, 561),
    (138, 378, 504, 564),
    (210, 399, 504, 567),
    (40, 412, 484, 568),
    (48, 432, 480, 576),
    (19, 460, 467, 584),
    (214, 470, 472, 584),
    (49, 441, 490, 588),
    (108, 311, 561, 590),
    (36, 103, 590, 591),
    (4, 292, 576, 600),
    (8, 332, 564, 600),
    (30, 220, 590, 600),
    (127, 316, 590, 617),
    (257, 450, 545, 618),
    (10, 496, 504, 630),
    (135, 500, 508, 633),
    (244, 311, 625, 638),
    (160, 388, 590, 638),
    (80, 360, 600, 640),
    (192, 496, 528, 640),
    (243, 360, 618, 645),
    (120, 303, 633, 654),
    (82, 369, 615, 656),
    (161, 441, 588, 658),
    (124, 486, 570, 668),
    (100, 256, 656, 668),
    (271, 399, 658, 690),
    (101, 467, 617, 695),
    (90, 470, 615, 695),
    (44, 386, 654, 696),
    (96, 133, 699, 700),
    (396, 590, 625, 729),
    (87, 568, 591, 730),
    (264, 420, 700, 736),
    (265, 376, 730, 751),
    (67, 438, 699, 752),
    (184, 504, 672, 752),
    (63, 567, 630, 756),
    (280, 532, 672, 756),
    (50, 480, 690, 760),
    (30, 249, 751, 760),
    (380, 479, 729, 762),
    (59, 176, 762, 765),
    (180, 570, 645, 765),
    (280, 472, 736, 784),
    (180, 532, 696, 784)
  ]

def roots : Finset ℕ := rootsList.toFinset

private def coords (e : ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  [e.1,e.2.1,e.2.2.1,e.2.2.2]

private def Good (e : ℕ × ℕ × ℕ × ℕ) : Prop :=
  e.1 ∈ rootsList ∧ e.2.1 ∈ rootsList ∧ e.2.2.1 ∈ rootsList ∧ e.2.2.2 ∈ rootsList ∧
  0 < e.1 ∧ e.1 < e.2.1 ∧ e.2.1 < e.2.2.1 ∧ e.2.2.1 < e.2.2.2 ∧
  e.1^3+e.2.2.2^3=e.2.1^3+e.2.2.1^3

private instance (e : ℕ × ℕ × ℕ × ℕ) : Decidable (Good e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private lemma roots_nodup : rootsList.Nodup := by
  have h : rootsList.IsChain (· < ·) := by decide +kernel
  exact h.pairwise.imp (fun h => h.ne)

private lemma data_good : ∀ e ∈ data, Good e := by
  have h : data.all (fun e => decide (Good e)) = true := by decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

private def vertexList : List ℕ := data.flatMap coords

private def halfVertices : List ℕ :=
  [1, 2, 3, 4, 4, 4, 5, 5, 6, 8, 9, 9, 10, 10, 10, 12, 14, 15, 17, 18, 18, 19, 20, 20, 21, 22, 24, 24, 25, 27, 30, 30, 30, 31, 32, 32, 33, 35, 36, 36, 38, 40, 40, 40, 41, 42, 44, 45, 45, 45, 47, 48, 48, 49, 50, 50, 51, 54, 54, 55, 57, 58, 59, 60, 62, 63, 64, 64, 64, 66, 66, 66, 67, 72, 72, 73, 75, 76, 80, 80, 80, 81, 81, 82, 84, 84, 87, 90, 90, 90, 92, 93, 94, 96, 96, 96, 97, 99, 100, 101, 103, 105, 105, 107, 108, 108, 110, 112, 113, 114, 115, 116, 120, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 132, 132, 132, 133, 135, 135, 135, 138, 140, 144, 145, 147, 150, 150, 150, 151, 152, 153, 153, 159, 160, 160, 161, 164, 166, 167, 168, 171, 171, 174, 175, 176, 177, 177, 180, 180, 180, 180, 184, 188, 189, 190, 192, 192, 194, 194, 196, 197, 198, 200, 206, 210, 210, 212, 214, 216, 216, 217, 219, 220, 225, 225, 228, 229, 231, 233, 235, 236, 240, 240, 243, 243, 244, 248, 249, 250, 250, 252, 252, 254, 256, 257, 258, 261, 264, 264, 265, 266, 267, 270, 270, 271, 276, 279, 280, 280, 282, 285, 288, 290, 292, 294, 295, 295, 298, 300, 300, 303, 309, 310, 311, 315, 316, 318, 319, 320, 328, 332, 332, 334, 334, 336, 339, 341, 342, 348, 350, 354, 354, 358, 360, 360, 360, 363, 368, 369, 376, 378, 379, 380, 386, 387, 388, 392, 394, 396, 399, 401, 405, 405, 412, 420, 423, 432, 432, 435, 438, 440, 441, 443, 444, 447, 450, 450, 460, 462, 463, 464, 465, 467, 470, 470, 472, 477, 479, 480, 480, 484, 486, 487, 490, 496, 498, 498, 500, 503, 504, 504, 508, 508, 514, 528, 530, 532, 540, 545, 561, 564, 567, 568, 570, 576, 584, 588, 590, 590, 590, 591, 600, 600, 615, 617, 618, 625, 630, 633, 638, 640, 645, 654, 656, 658, 668, 672, 690, 695, 696, 699, 700, 729, 730, 736, 751, 752, 756, 760, 762, 765, 784]

private lemma incidence_certificate : vertexList.Perm (halfVertices ++ halfVertices) := by
  decide +kernel

/-- The prescribed odd edge sums are inconsistent, although this does not
assert that an ordinary proper coloring is impossible. -/
theorem no_odd_parity_coloring :
    ¬ ∃ c : ℕ → ZMod 2, ∀ e ∈ OddCycleColoring.CubicEdges (roots : Set ℕ),
      ∑ n ∈ e, c n = 1 := by
  rintro ⟨c,hc⟩
  have hr (e : ℕ × ℕ × ℕ × ℕ) (he : e ∈ data) : ((coords e).map c).sum = 1 := by
    rcases e with ⟨a,b,d,e⟩
    obtain ⟨ha,hb,hd,he',hpos,hab,hbd,hde,hs⟩ := data_good _ he
    have ham : a ∈ roots := List.mem_toFinset.mpr ha
    have hbm : b ∈ roots := List.mem_toFinset.mpr hb
    have hdm : d ∈ roots := List.mem_toFinset.mpr hd
    have hem : e ∈ roots := List.mem_toFinset.mpr he'
    have hh := hc {a,b,d,e} ⟨a,ham,b,hbm,d,hdm,e,hem,hpos,hab,hbd,hde,hs,rfl⟩
    simpa [coords,hab.ne,(hab.trans hbd).ne,(hab.trans (hbd.trans hde)).ne,
      hbd.ne,(hbd.trans hde).ne,hde.ne] using hh
  have hsum : (vertexList.map c).sum = (181 : ZMod 2) := by
    calc
      _ = (data.map (fun e => ((coords e).map c).sum)).sum := by
        rw [vertexList,List.map_flatMap,List.flatMap_def,List.sum_flatten,List.map_map]
        rfl
      _ = (data.map (fun _ => (1 : ZMod 2))).sum := by
        congr 1
        apply List.map_congr_left
        exact hr
      _ = 181 := by
        change (data.map (Function.const _ (1 : ZMod 2))).sum = 181
        rw [List.map_const,List.sum_replicate,nsmul_eq_mul,mul_one]
        rfl
  have hp := (incidence_certificate.map c).sum_eq
  rw [List.map_append,List.sum_append] at hp
  have hz : (halfVertices.map c).sum + (halfVertices.map c).sum = 0 := by
    simpa [ZMod.neg_eq_self_mod_two] using neg_add_cancel (halfVertices.map c).sum
  rw [hz] at hp
  have hh : (181 : ZMod 2) = 0 := hsum.symm.trans hp
  exact (by decide +kernel : (181 : ZMod 2) ≠ 0) hh


def pairsList : List (ℕ × ℕ) :=
  (rootsList.product rootsList).filter fun p => p.1 < p.2

/-- A structurally recursive merge; insufficient fuel still gives a permutation. -/
private def mergeFuel : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | k+1, x::xs, y::ys =>
    if x ≤ y then x :: mergeFuel k xs (y::ys)
    else y :: mergeFuel k (x::xs) ys

private lemma move_front (x : ℕ) (xs ys : List ℕ) :
    (x :: (xs ++ ys)).Perm (xs ++ x :: ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    exact (List.Perm.swap _ _ _).trans (ih.cons a)

private lemma mergeFuel_perm (k : ℕ) (xs ys : List ℕ) :
    (mergeFuel k xs ys).Perm (xs ++ ys) := by
  induction k generalizing xs ys with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split_ifs
        · exact (ih xs (y::ys)).cons x
        · exact ((ih (x::xs) ys).cons y).trans (move_front y (x::xs) ys)

private def sortFuel : ℕ → List ℕ → List ℕ
  | 0, l => l
  | k+1, l =>
    let a := sortFuel k (l.take (l.length/2))
    let b := sortFuel k (l.drop (l.length/2))
    mergeFuel l.length a b

private lemma sortFuel_perm (k : ℕ) (l : List ℕ) : (sortFuel k l).Perm l := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    simp only [sortFuel]
    exact (mergeFuel_perm _ _ _).trans
      ((ih (l.take (l.length/2))).append (ih (l.drop (l.length/2)))) |>.trans
        (by rw [List.take_append_drop])

private def rootsResidue : ℕ → List ℕ
  | 0 => [59, 177, 236, 295, 354, 472, 590]
  | 1 => [1, 60, 532, 591]
  | 2 => [38, 97, 392]
  | 3 => [49, 108, 167, 285, 462]
  | 4 => [87, 264, 441, 500, 618, 736]
  | 5 => [4, 63, 122, 240, 358]
  | 6 => [33, 92, 151, 210, 328, 387, 564]
  | 7 => [5, 64, 123, 300, 477, 654]
  | 8 => [2, 120]
  | 9 => [41, 100, 159, 336, 690]
  | 10 => [93, 152, 270, 388, 447]
  | 11 => [229, 288, 465, 760]
  | 12 => [15, 133, 192, 310, 369, 487]
  | 13 => [82, 200, 318, 672]
  | 14 => [72, 190, 249]
  | 15 => [19, 196, 432, 668]
  | 16 => [17, 76, 135, 194, 784]
  | 17 => [12, 189, 248, 484]
  | 18 => [24, 319, 378, 496]
  | 19 => [51, 110, 228, 405, 464, 700]
  | 20 => [112, 171, 348, 584]
  | 21 => [9, 127, 363, 540, 658]
  | 22 => [147, 206, 265]
  | 23 => [32, 150, 386, 504]
  | 24 => [216, 334, 570]
  | 25 => [75, 252, 311]
  | 26 => [48, 107, 166, 225, 638, 756]
  | 27 => [3, 62, 121, 180, 298]
  | 28 => [22, 81, 140, 258, 376, 435, 730]
  | 29 => [45, 399, 576]
  | 30 => [14, 73, 132, 250, 309, 368, 486, 545]
  | 31 => [96, 214, 332, 450, 568]
  | 32 => [115, 174, 233, 292, 528]
  | 33 => [129, 188]
  | 34 => [161, 220, 279, 633, 751]
  | 35 => [20, 138, 197, 256, 315]
  | 36 => [27, 145, 440, 617]
  | 37 => [30, 266, 443, 561]
  | 38 => [50, 168, 463, 640, 699]
  | 39 => [6, 124, 360]
  | 40 => [8, 67, 126, 244, 303, 480]
  | 41 => [35, 94, 153, 212, 271, 625]
  | 42 => [47, 342, 401, 460, 696]
  | 43 => [42, 101, 160, 219, 396, 514]
  | 44 => [40, 99, 217, 276, 394, 630]
  | 45 => [105, 164, 282, 341, 695]
  | 46 => [36, 508, 567]
  | 47 => [44, 103, 280, 339, 752]
  | 48 => [66, 125, 184, 243, 420, 479, 656]
  | 49 => [25, 84, 261, 320, 379, 438, 615]
  | 50 => [18, 254, 490]
  | 51 => [57, 116, 175, 470, 588, 765]
  | 52 => [54, 113, 231, 290, 467, 762]
  | 53 => [144, 380, 498]
  | 54 => [55, 114, 350, 645]
  | 55 => [31, 90, 267, 444, 503]
  | 56 => [10, 128, 423, 600]
  | 57 => [21, 80, 198, 257, 316, 729]
  | 58 => [58, 176, 235, 294, 412, 530]
  | _ => []

private lemma rootsResidue_eq (r : Fin 59) :
    rootsList.filter (fun b => b^3 % 59 == r.val) = rootsResidue r.val := by
  have h : ∀ r : Fin 59,
      rootsList.filter (fun b => b^3 % 59 == r.val) = rootsResidue r.val := by
    decide +kernel
  exact h r

private def key (kind : Bool) (p : ℕ × ℕ) : ℕ :=
  if kind then p.1^3+p.2^3 else p.2^3-p.1^3

private def target (kind : Bool) (a r : ℕ) : ℕ :=
  if kind then (r+59-a^3 % 59) % 59 else (r+a^3) % 59

private lemma target_lt (kind : Bool) (a r : ℕ) : target kind a r < 59 := by
  cases kind <;> exact Nat.mod_lt _ (by decide)

private lemma key_mod_iff (kind : Bool) (a b r : ℕ) (hr : r < 59) (hab : a < b) :
    key kind (a,b) % 59 = r ↔ b^3 % 59 = target kind a r := by
  have hab' : a^3 ≤ b^3 := Nat.pow_le_pow_left hab.le 3
  cases kind <;> simp only [key,target,Bool.false_eq_true,if_false,if_true] <;> omega

private lemma filter_product (xs ys : List ℕ) (p : ℕ × ℕ → Bool) :
    (xs.product ys).filter p =
      xs.flatMap (fun a => (ys.filter (fun b => p (a,b))).map (fun b => (a,b))) := by
  simp only [List.product,List.filter_flatMap,List.filter_map,Function.comp_def]

private def bucketPairs (kind : Bool) (r : ℕ) : List (ℕ × ℕ) :=
  rootsList.flatMap fun a =>
    ((rootsResidue (target kind a r)).filter (fun b => a < b)).map (fun b => (a,b))

private lemma bucketPairs_eq (kind : Bool) {r : ℕ} (hr : r < 59) :
    bucketPairs kind r = pairsList.filter (fun p => key kind p % 59 == r) := by
  rw [pairsList,List.filter_filter,filter_product]
  apply List.flatMap_congr
  intro a ha
  rw [← rootsResidue_eq ⟨target kind a r,target_lt kind a r⟩,List.filter_filter]
  congr 1
  apply List.filter_congr
  intro b hb
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · rintro ⟨hab,he⟩
    exact ⟨(key_mod_iff kind a b r hr hab).mpr he,hab⟩
  · rintro ⟨he,hab⟩
    exact ⟨hab,(key_mod_iff kind a b r hr hab).mp he⟩

private lemma bucket_map_eq (kind : Bool) {r : ℕ} (hr : r < 59) :
    (bucketPairs kind r).map (key kind) =
      (pairsList.map (key kind)).filter (fun n => n % 59 == r) := by
  rw [bucketPairs_eq kind hr,List.filter_map]
  rfl

def sumKeys (r : ℕ) : List ℕ := sortFuel 12 ((bucketPairs true r).map (key true))

def diffKeys (r : ℕ) : List ℕ := sortFuel 12 ((bucketPairs false r).map (key false))

private lemma sum_check_0 :
    (alternating (sumKeys 0)).IsChain (· < ·) ∧
    (alternating (sumKeys 0).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_1 :
    (alternating (sumKeys 1)).IsChain (· < ·) ∧
    (alternating (sumKeys 1).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_2 :
    (alternating (sumKeys 2)).IsChain (· < ·) ∧
    (alternating (sumKeys 2).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_3 :
    (alternating (sumKeys 3)).IsChain (· < ·) ∧
    (alternating (sumKeys 3).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_4 :
    (alternating (sumKeys 4)).IsChain (· < ·) ∧
    (alternating (sumKeys 4).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_5 :
    (alternating (sumKeys 5)).IsChain (· < ·) ∧
    (alternating (sumKeys 5).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_6 :
    (alternating (sumKeys 6)).IsChain (· < ·) ∧
    (alternating (sumKeys 6).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_7 :
    (alternating (sumKeys 7)).IsChain (· < ·) ∧
    (alternating (sumKeys 7).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_8 :
    (alternating (sumKeys 8)).IsChain (· < ·) ∧
    (alternating (sumKeys 8).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_9 :
    (alternating (sumKeys 9)).IsChain (· < ·) ∧
    (alternating (sumKeys 9).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_10 :
    (alternating (sumKeys 10)).IsChain (· < ·) ∧
    (alternating (sumKeys 10).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_11 :
    (alternating (sumKeys 11)).IsChain (· < ·) ∧
    (alternating (sumKeys 11).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_12 :
    (alternating (sumKeys 12)).IsChain (· < ·) ∧
    (alternating (sumKeys 12).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_13 :
    (alternating (sumKeys 13)).IsChain (· < ·) ∧
    (alternating (sumKeys 13).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_14 :
    (alternating (sumKeys 14)).IsChain (· < ·) ∧
    (alternating (sumKeys 14).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_15 :
    (alternating (sumKeys 15)).IsChain (· < ·) ∧
    (alternating (sumKeys 15).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_16 :
    (alternating (sumKeys 16)).IsChain (· < ·) ∧
    (alternating (sumKeys 16).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_17 :
    (alternating (sumKeys 17)).IsChain (· < ·) ∧
    (alternating (sumKeys 17).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_18 :
    (alternating (sumKeys 18)).IsChain (· < ·) ∧
    (alternating (sumKeys 18).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_19 :
    (alternating (sumKeys 19)).IsChain (· < ·) ∧
    (alternating (sumKeys 19).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_20 :
    (alternating (sumKeys 20)).IsChain (· < ·) ∧
    (alternating (sumKeys 20).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_21 :
    (alternating (sumKeys 21)).IsChain (· < ·) ∧
    (alternating (sumKeys 21).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_22 :
    (alternating (sumKeys 22)).IsChain (· < ·) ∧
    (alternating (sumKeys 22).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_23 :
    (alternating (sumKeys 23)).IsChain (· < ·) ∧
    (alternating (sumKeys 23).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_24 :
    (alternating (sumKeys 24)).IsChain (· < ·) ∧
    (alternating (sumKeys 24).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_25 :
    (alternating (sumKeys 25)).IsChain (· < ·) ∧
    (alternating (sumKeys 25).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_26 :
    (alternating (sumKeys 26)).IsChain (· < ·) ∧
    (alternating (sumKeys 26).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_27 :
    (alternating (sumKeys 27)).IsChain (· < ·) ∧
    (alternating (sumKeys 27).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_28 :
    (alternating (sumKeys 28)).IsChain (· < ·) ∧
    (alternating (sumKeys 28).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_29 :
    (alternating (sumKeys 29)).IsChain (· < ·) ∧
    (alternating (sumKeys 29).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_30 :
    (alternating (sumKeys 30)).IsChain (· < ·) ∧
    (alternating (sumKeys 30).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_31 :
    (alternating (sumKeys 31)).IsChain (· < ·) ∧
    (alternating (sumKeys 31).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_32 :
    (alternating (sumKeys 32)).IsChain (· < ·) ∧
    (alternating (sumKeys 32).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_33 :
    (alternating (sumKeys 33)).IsChain (· < ·) ∧
    (alternating (sumKeys 33).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_34 :
    (alternating (sumKeys 34)).IsChain (· < ·) ∧
    (alternating (sumKeys 34).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_35 :
    (alternating (sumKeys 35)).IsChain (· < ·) ∧
    (alternating (sumKeys 35).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_36 :
    (alternating (sumKeys 36)).IsChain (· < ·) ∧
    (alternating (sumKeys 36).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_37 :
    (alternating (sumKeys 37)).IsChain (· < ·) ∧
    (alternating (sumKeys 37).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_38 :
    (alternating (sumKeys 38)).IsChain (· < ·) ∧
    (alternating (sumKeys 38).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_39 :
    (alternating (sumKeys 39)).IsChain (· < ·) ∧
    (alternating (sumKeys 39).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_40 :
    (alternating (sumKeys 40)).IsChain (· < ·) ∧
    (alternating (sumKeys 40).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_41 :
    (alternating (sumKeys 41)).IsChain (· < ·) ∧
    (alternating (sumKeys 41).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_42 :
    (alternating (sumKeys 42)).IsChain (· < ·) ∧
    (alternating (sumKeys 42).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_43 :
    (alternating (sumKeys 43)).IsChain (· < ·) ∧
    (alternating (sumKeys 43).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_44 :
    (alternating (sumKeys 44)).IsChain (· < ·) ∧
    (alternating (sumKeys 44).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_45 :
    (alternating (sumKeys 45)).IsChain (· < ·) ∧
    (alternating (sumKeys 45).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_46 :
    (alternating (sumKeys 46)).IsChain (· < ·) ∧
    (alternating (sumKeys 46).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_47 :
    (alternating (sumKeys 47)).IsChain (· < ·) ∧
    (alternating (sumKeys 47).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_48 :
    (alternating (sumKeys 48)).IsChain (· < ·) ∧
    (alternating (sumKeys 48).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_49 :
    (alternating (sumKeys 49)).IsChain (· < ·) ∧
    (alternating (sumKeys 49).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_50 :
    (alternating (sumKeys 50)).IsChain (· < ·) ∧
    (alternating (sumKeys 50).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_51 :
    (alternating (sumKeys 51)).IsChain (· < ·) ∧
    (alternating (sumKeys 51).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_52 :
    (alternating (sumKeys 52)).IsChain (· < ·) ∧
    (alternating (sumKeys 52).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_53 :
    (alternating (sumKeys 53)).IsChain (· < ·) ∧
    (alternating (sumKeys 53).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_54 :
    (alternating (sumKeys 54)).IsChain (· < ·) ∧
    (alternating (sumKeys 54).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_55 :
    (alternating (sumKeys 55)).IsChain (· < ·) ∧
    (alternating (sumKeys 55).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_56 :
    (alternating (sumKeys 56)).IsChain (· < ·) ∧
    (alternating (sumKeys 56).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_57 :
    (alternating (sumKeys 57)).IsChain (· < ·) ∧
    (alternating (sumKeys 57).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_check_58 :
    (alternating (sumKeys 58)).IsChain (· < ·) ∧
    (alternating (sumKeys 58).tail).IsChain (· < ·) := by decide +kernel

private lemma sum_checks (r : Fin 59) :
    (alternating (sumKeys r.val)).IsChain (· < ·) ∧
    (alternating (sumKeys r.val).tail).IsChain (· < ·) := by
  fin_cases r
  · exact sum_check_0
  · exact sum_check_1
  · exact sum_check_2
  · exact sum_check_3
  · exact sum_check_4
  · exact sum_check_5
  · exact sum_check_6
  · exact sum_check_7
  · exact sum_check_8
  · exact sum_check_9
  · exact sum_check_10
  · exact sum_check_11
  · exact sum_check_12
  · exact sum_check_13
  · exact sum_check_14
  · exact sum_check_15
  · exact sum_check_16
  · exact sum_check_17
  · exact sum_check_18
  · exact sum_check_19
  · exact sum_check_20
  · exact sum_check_21
  · exact sum_check_22
  · exact sum_check_23
  · exact sum_check_24
  · exact sum_check_25
  · exact sum_check_26
  · exact sum_check_27
  · exact sum_check_28
  · exact sum_check_29
  · exact sum_check_30
  · exact sum_check_31
  · exact sum_check_32
  · exact sum_check_33
  · exact sum_check_34
  · exact sum_check_35
  · exact sum_check_36
  · exact sum_check_37
  · exact sum_check_38
  · exact sum_check_39
  · exact sum_check_40
  · exact sum_check_41
  · exact sum_check_42
  · exact sum_check_43
  · exact sum_check_44
  · exact sum_check_45
  · exact sum_check_46
  · exact sum_check_47
  · exact sum_check_48
  · exact sum_check_49
  · exact sum_check_50
  · exact sum_check_51
  · exact sum_check_52
  · exact sum_check_53
  · exact sum_check_54
  · exact sum_check_55
  · exact sum_check_56
  · exact sum_check_57
  · exact sum_check_58

private lemma diff_check_0 :
    (alternating (diffKeys 0)).IsChain (· < ·) ∧
    (alternating (diffKeys 0).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_1 :
    (alternating (diffKeys 1)).IsChain (· < ·) ∧
    (alternating (diffKeys 1).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_2 :
    (alternating (diffKeys 2)).IsChain (· < ·) ∧
    (alternating (diffKeys 2).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_3 :
    (alternating (diffKeys 3)).IsChain (· < ·) ∧
    (alternating (diffKeys 3).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_4 :
    (alternating (diffKeys 4)).IsChain (· < ·) ∧
    (alternating (diffKeys 4).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_5 :
    (alternating (diffKeys 5)).IsChain (· < ·) ∧
    (alternating (diffKeys 5).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_6 :
    (alternating (diffKeys 6)).IsChain (· < ·) ∧
    (alternating (diffKeys 6).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_7 :
    (alternating (diffKeys 7)).IsChain (· < ·) ∧
    (alternating (diffKeys 7).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_8 :
    (alternating (diffKeys 8)).IsChain (· < ·) ∧
    (alternating (diffKeys 8).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_9 :
    (alternating (diffKeys 9)).IsChain (· < ·) ∧
    (alternating (diffKeys 9).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_10 :
    (alternating (diffKeys 10)).IsChain (· < ·) ∧
    (alternating (diffKeys 10).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_11 :
    (alternating (diffKeys 11)).IsChain (· < ·) ∧
    (alternating (diffKeys 11).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_12 :
    (alternating (diffKeys 12)).IsChain (· < ·) ∧
    (alternating (diffKeys 12).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_13 :
    (alternating (diffKeys 13)).IsChain (· < ·) ∧
    (alternating (diffKeys 13).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_14 :
    (alternating (diffKeys 14)).IsChain (· < ·) ∧
    (alternating (diffKeys 14).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_15 :
    (alternating (diffKeys 15)).IsChain (· < ·) ∧
    (alternating (diffKeys 15).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_16 :
    (alternating (diffKeys 16)).IsChain (· < ·) ∧
    (alternating (diffKeys 16).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_17 :
    (alternating (diffKeys 17)).IsChain (· < ·) ∧
    (alternating (diffKeys 17).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_18 :
    (alternating (diffKeys 18)).IsChain (· < ·) ∧
    (alternating (diffKeys 18).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_19 :
    (alternating (diffKeys 19)).IsChain (· < ·) ∧
    (alternating (diffKeys 19).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_20 :
    (alternating (diffKeys 20)).IsChain (· < ·) ∧
    (alternating (diffKeys 20).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_21 :
    (alternating (diffKeys 21)).IsChain (· < ·) ∧
    (alternating (diffKeys 21).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_22 :
    (alternating (diffKeys 22)).IsChain (· < ·) ∧
    (alternating (diffKeys 22).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_23 :
    (alternating (diffKeys 23)).IsChain (· < ·) ∧
    (alternating (diffKeys 23).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_24 :
    (alternating (diffKeys 24)).IsChain (· < ·) ∧
    (alternating (diffKeys 24).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_25 :
    (alternating (diffKeys 25)).IsChain (· < ·) ∧
    (alternating (diffKeys 25).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_26 :
    (alternating (diffKeys 26)).IsChain (· < ·) ∧
    (alternating (diffKeys 26).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_27 :
    (alternating (diffKeys 27)).IsChain (· < ·) ∧
    (alternating (diffKeys 27).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_28 :
    (alternating (diffKeys 28)).IsChain (· < ·) ∧
    (alternating (diffKeys 28).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_29 :
    (alternating (diffKeys 29)).IsChain (· < ·) ∧
    (alternating (diffKeys 29).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_30 :
    (alternating (diffKeys 30)).IsChain (· < ·) ∧
    (alternating (diffKeys 30).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_31 :
    (alternating (diffKeys 31)).IsChain (· < ·) ∧
    (alternating (diffKeys 31).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_32 :
    (alternating (diffKeys 32)).IsChain (· < ·) ∧
    (alternating (diffKeys 32).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_33 :
    (alternating (diffKeys 33)).IsChain (· < ·) ∧
    (alternating (diffKeys 33).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_34 :
    (alternating (diffKeys 34)).IsChain (· < ·) ∧
    (alternating (diffKeys 34).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_35 :
    (alternating (diffKeys 35)).IsChain (· < ·) ∧
    (alternating (diffKeys 35).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_36 :
    (alternating (diffKeys 36)).IsChain (· < ·) ∧
    (alternating (diffKeys 36).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_37 :
    (alternating (diffKeys 37)).IsChain (· < ·) ∧
    (alternating (diffKeys 37).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_38 :
    (alternating (diffKeys 38)).IsChain (· < ·) ∧
    (alternating (diffKeys 38).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_39 :
    (alternating (diffKeys 39)).IsChain (· < ·) ∧
    (alternating (diffKeys 39).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_40 :
    (alternating (diffKeys 40)).IsChain (· < ·) ∧
    (alternating (diffKeys 40).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_41 :
    (alternating (diffKeys 41)).IsChain (· < ·) ∧
    (alternating (diffKeys 41).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_42 :
    (alternating (diffKeys 42)).IsChain (· < ·) ∧
    (alternating (diffKeys 42).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_43 :
    (alternating (diffKeys 43)).IsChain (· < ·) ∧
    (alternating (diffKeys 43).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_44 :
    (alternating (diffKeys 44)).IsChain (· < ·) ∧
    (alternating (diffKeys 44).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_45 :
    (alternating (diffKeys 45)).IsChain (· < ·) ∧
    (alternating (diffKeys 45).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_46 :
    (alternating (diffKeys 46)).IsChain (· < ·) ∧
    (alternating (diffKeys 46).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_47 :
    (alternating (diffKeys 47)).IsChain (· < ·) ∧
    (alternating (diffKeys 47).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_48 :
    (alternating (diffKeys 48)).IsChain (· < ·) ∧
    (alternating (diffKeys 48).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_49 :
    (alternating (diffKeys 49)).IsChain (· < ·) ∧
    (alternating (diffKeys 49).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_50 :
    (alternating (diffKeys 50)).IsChain (· < ·) ∧
    (alternating (diffKeys 50).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_51 :
    (alternating (diffKeys 51)).IsChain (· < ·) ∧
    (alternating (diffKeys 51).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_52 :
    (alternating (diffKeys 52)).IsChain (· < ·) ∧
    (alternating (diffKeys 52).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_53 :
    (alternating (diffKeys 53)).IsChain (· < ·) ∧
    (alternating (diffKeys 53).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_54 :
    (alternating (diffKeys 54)).IsChain (· < ·) ∧
    (alternating (diffKeys 54).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_55 :
    (alternating (diffKeys 55)).IsChain (· < ·) ∧
    (alternating (diffKeys 55).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_56 :
    (alternating (diffKeys 56)).IsChain (· < ·) ∧
    (alternating (diffKeys 56).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_57 :
    (alternating (diffKeys 57)).IsChain (· < ·) ∧
    (alternating (diffKeys 57).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_check_58 :
    (alternating (diffKeys 58)).IsChain (· < ·) ∧
    (alternating (diffKeys 58).tail).IsChain (· < ·) := by decide +kernel

private lemma diff_checks (r : Fin 59) :
    (alternating (diffKeys r.val)).IsChain (· < ·) ∧
    (alternating (diffKeys r.val).tail).IsChain (· < ·) := by
  fin_cases r
  · exact diff_check_0
  · exact diff_check_1
  · exact diff_check_2
  · exact diff_check_3
  · exact diff_check_4
  · exact diff_check_5
  · exact diff_check_6
  · exact diff_check_7
  · exact diff_check_8
  · exact diff_check_9
  · exact diff_check_10
  · exact diff_check_11
  · exact diff_check_12
  · exact diff_check_13
  · exact diff_check_14
  · exact diff_check_15
  · exact diff_check_16
  · exact diff_check_17
  · exact diff_check_18
  · exact diff_check_19
  · exact diff_check_20
  · exact diff_check_21
  · exact diff_check_22
  · exact diff_check_23
  · exact diff_check_24
  · exact diff_check_25
  · exact diff_check_26
  · exact diff_check_27
  · exact diff_check_28
  · exact diff_check_29
  · exact diff_check_30
  · exact diff_check_31
  · exact diff_check_32
  · exact diff_check_33
  · exact diff_check_34
  · exact diff_check_35
  · exact diff_check_36
  · exact diff_check_37
  · exact diff_check_38
  · exact diff_check_39
  · exact diff_check_40
  · exact diff_check_41
  · exact diff_check_42
  · exact diff_check_43
  · exact diff_check_44
  · exact diff_check_45
  · exact diff_check_46
  · exact diff_check_47
  · exact diff_check_48
  · exact diff_check_49
  · exact diff_check_50
  · exact diff_check_51
  · exact diff_check_52
  · exact diff_check_53
  · exact diff_check_54
  · exact diff_check_55
  · exact diff_check_56
  · exact diff_check_57
  · exact diff_check_58

/-- There are at most two distinct ordered pairs with a given cube sum. -/
theorem sum_multiplicity (n : ℕ) :
    ((pairsList.map fun p => p.1^3+p.2^3).count n) ≤ 2 := by
  have hchecks := sum_checks ⟨n % 59,Nat.mod_lt n (by decide)⟩
  have h := count_le_two (sumKeys (n % 59)) hchecks.1 hchecks.2 n
  rw [sumKeys,bucket_map_eq true (Nat.mod_lt n (by decide)), (sortFuel_perm _ _).count_eq,
    List.count_filter (by simp)] at h
  exact h

/-- There are at most two distinct ordered pairs with a given positive cube difference. -/
theorem difference_multiplicity (n : ℕ) :
    ((pairsList.map fun p => p.2^3-p.1^3).count n) ≤ 2 := by
  have hchecks := diff_checks ⟨n % 59,Nat.mod_lt n (by decide)⟩
  have h := count_le_two (diffKeys (n % 59)) hchecks.1 hchecks.2 n
  rw [diffKeys,bucket_map_eq false (Nat.mod_lt n (by decide)), (sortFuel_perm _ _).count_eq,
    List.count_filter (by simp)] at h
  exact h

lemma pairs_nodup : pairsList.Nodup :=
  (roots_nodup.product roots_nodup).filter _

lemma mem_pairs {a b : ℕ} : (a,b) ∈ pairsList ↔ a ∈ roots ∧ b ∈ roots ∧ a < b := by
  simp [pairsList,roots,and_assoc]

private lemma fibre_card (f : ℕ × ℕ → ℕ) (n : ℕ) :
    (pairsList.toFinset.filter (fun p => f p = n)).card =
      (pairsList.map f).count n := by
  have h : ((pairsList.filter (fun p => decide (f p = n))).toFinset).card =
      (pairsList.filter (fun p => decide (f p = n))).length :=
    List.toFinset_card_of_nodup (pairs_nodup.filter _)
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  simpa only [List.toFinset_filter, decide_eq_true_eq, Function.comp_def, beq_iff_eq] using h

private lemma no_three_of_count (f : ℕ × ℕ → ℕ)
    (hf : ∀ n, (pairsList.map f).count n ≤ 2)
    {p q r : ℕ × ℕ} (hp : p ∈ pairsList) (hq : q ∈ pairsList) (hr : r ∈ pairsList)
    (hpq : f p = f q) (hpr : f p = f r) :
    p = q ∨ p = r ∨ q = r := by
  by_contra hh
  push_neg at hh
  have hsub : ({p,q,r} : Finset (ℕ × ℕ)) ⊆
      pairsList.toFinset.filter (fun v => f v = f p) := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr hp,rfl⟩
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr hq,hpq.symm⟩
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hpr.symm⟩
  have hc := card_le_card hsub
  have he : ({p,q,r} : Finset (ℕ × ℕ)).card = 3 := by
    simp [hh.1,hh.2.1,hh.2.2]
  rw [he, fibre_card] at hc
  have hb := hf (f p)
  omega

/-- No three distinct ordered pairs in this source have the same cube sum. -/
theorem no_three_sum_pairs {p q r : ℕ × ℕ}
    (hp : p ∈ pairsList) (hq : q ∈ pairsList) (hr : r ∈ pairsList)
    (hpq : p.1^3+p.2^3 = q.1^3+q.2^3)
    (hpr : p.1^3+p.2^3 = r.1^3+r.2^3) :
    p = q ∨ p = r ∨ q = r :=
  no_three_of_count (fun v => v.1^3+v.2^3) sum_multiplicity hp hq hr hpq hpr

/-- No three distinct ordered pairs in this source have the same positive cube difference. -/
theorem no_three_difference_pairs {p q r : ℕ × ℕ}
    (hp : p ∈ pairsList) (hq : q ∈ pairsList) (hr : r ∈ pairsList)
    (hpq : p.2^3-p.1^3 = q.2^3-q.1^3)
    (hpr : p.2^3-p.1^3 = r.2^3-r.1^3) :
    p = q ∨ p = r ∨ q = r :=
  no_three_of_count (fun v => v.2^3-v.1^3) difference_multiplicity hp hq hr hpq hpr

#print axioms no_odd_parity_coloring
#print axioms no_three_sum_pairs
#print axioms no_three_difference_pairs
#print axioms sum_multiplicity
#print axioms difference_multiplicity
end Erdos1206.HigherCycleObstruction
