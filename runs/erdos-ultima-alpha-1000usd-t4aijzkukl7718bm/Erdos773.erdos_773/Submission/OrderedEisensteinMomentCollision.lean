import FormalConjecturesUtil

/-!
An auxiliary carry obstruction with common Gaussian--Eisenstein endpoint
conditions, increasing lower digits, and common first two digit-value moments.
This is NOT a disproof of Erdős 773.
-/
namespace Erdos773.OrderedEisensteinMomentCollision
open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def base (u : ℕ) : ℕ := 600*u-1

/-- Constant coefficient first. The last digit is the monic leading digit. -/
def digit (u : ℕ) : Fin 4 → Fin 43 → ℕ := ![
  ![6, 78, 174, 210, 258, 318, 1368, 7800, 17400, 21000, 25800, 31800, 137400, 787800, 1756200, 2122200, 2607000, 3210600, 13756194, 77992122, 173983638, 209977578, 257972730, 317969094, 1367922438, 7800000078, 17400000162, 21000000222, 25800000270, 31800000306, 136800000768, 780000000000, 1740000000000, 2100000000000, 2580000000000, 3180000000000, 6*u + 7680000000000, 72*u, 102*u, 108*u, 150*u, 168*u, 1],
  ![6, 78, 162, 222, 270, 306, 1368, 7800, 16200, 22200, 27000, 30600, 136200, 772200, 1602600, 2199000, 2674200, 3028200, 13603806, 78007878, 162017574, 222021210, 270026058, 306032118, 1368077562, 7799999922, 16199999826, 22199999790, 26999999742, 30599999682, 136799999232, 780000000000, 1620000000000, 2220000000000, 2700000000000, 3060000000000, 6*u + 7680000000000, 72*u, 90*u, 132*u, 138*u, 168*u, 1],
  ![6, 78, 174, 210, 258, 318, 1368, 7800, 17400, 21000, 25800, 31800, 136200, 772200, 1723800, 2077800, 2553000, 3149400, 13603806, 78007878, 174016362, 210022422, 258027270, 318030906, 1368077562, 7799999922, 17399999838, 20999999778, 25799999730, 31799999694, 136799999232, 780000000000, 1740000000000, 2100000000000, 2580000000000, 3180000000000, 6*u + 7680000000000, 72*u, 102*u, 108*u, 150*u, 168*u, 1],
  ![6, 78, 162, 222, 270, 306, 1368, 7800, 16200, 22200, 27000, 30600, 137400, 787800, 1637400, 2241000, 2725800, 3091800, 13756194, 77992122, 161982426, 221978790, 269973942, 305967882, 1367922438, 7800000078, 16200000174, 22200000210, 27000000258, 30600000318, 136800000768, 780000000000, 1620000000000, 2220000000000, 2700000000000, 3060000000000, 6*u + 7680000000000, 72*u, 90*u, 132*u, 138*u, 168*u, 1]]

def word (u : ℕ) (j : Fin 4) : List ℕ := List.ofFn (digit u j)

def root (u : ℕ) (j : Fin 4) : ℕ := Nat.ofDigits (base u) (word u j)

lemma endpoint_digits (u : ℕ) (j : Fin 4) :
    digit u j 0 = 6 ∧ digit u j 42 = 1 := by
  fin_cases j <;> exact ⟨rfl, rfl⟩

lemma lower_increasing (u : ℕ) (hu : 1000000000000 ≤ u) (j : Fin 4) :
    StrictMono (fun i : Fin 42 => digit u j i.castSucc) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases j <;> fin_cases i
  · change 6 < 78
    omega
  · change 78 < 174
    omega
  · change 174 < 210
    omega
  · change 210 < 258
    omega
  · change 258 < 318
    omega
  · change 318 < 1368
    omega
  · change 1368 < 7800
    omega
  · change 7800 < 17400
    omega
  · change 17400 < 21000
    omega
  · change 21000 < 25800
    omega
  · change 25800 < 31800
    omega
  · change 31800 < 137400
    omega
  · change 137400 < 787800
    omega
  · change 787800 < 1756200
    omega
  · change 1756200 < 2122200
    omega
  · change 2122200 < 2607000
    omega
  · change 2607000 < 3210600
    omega
  · change 3210600 < 13756194
    omega
  · change 13756194 < 77992122
    omega
  · change 77992122 < 173983638
    omega
  · change 173983638 < 209977578
    omega
  · change 209977578 < 257972730
    omega
  · change 257972730 < 317969094
    omega
  · change 317969094 < 1367922438
    omega
  · change 1367922438 < 7800000078
    omega
  · change 7800000078 < 17400000162
    omega
  · change 17400000162 < 21000000222
    omega
  · change 21000000222 < 25800000270
    omega
  · change 25800000270 < 31800000306
    omega
  · change 31800000306 < 136800000768
    omega
  · change 136800000768 < 780000000000
    omega
  · change 780000000000 < 1740000000000
    omega
  · change 1740000000000 < 2100000000000
    omega
  · change 2100000000000 < 2580000000000
    omega
  · change 2580000000000 < 3180000000000
    omega
  · change 3180000000000 < 6*u + 7680000000000
    omega
  · change 6*u + 7680000000000 < 72*u
    omega
  · change 72*u < 102*u
    omega
  · change 102*u < 108*u
    omega
  · change 108*u < 150*u
    omega
  · change 150*u < 168*u
    omega
  · change 6 < 78
    omega
  · change 78 < 162
    omega
  · change 162 < 222
    omega
  · change 222 < 270
    omega
  · change 270 < 306
    omega
  · change 306 < 1368
    omega
  · change 1368 < 7800
    omega
  · change 7800 < 16200
    omega
  · change 16200 < 22200
    omega
  · change 22200 < 27000
    omega
  · change 27000 < 30600
    omega
  · change 30600 < 136200
    omega
  · change 136200 < 772200
    omega
  · change 772200 < 1602600
    omega
  · change 1602600 < 2199000
    omega
  · change 2199000 < 2674200
    omega
  · change 2674200 < 3028200
    omega
  · change 3028200 < 13603806
    omega
  · change 13603806 < 78007878
    omega
  · change 78007878 < 162017574
    omega
  · change 162017574 < 222021210
    omega
  · change 222021210 < 270026058
    omega
  · change 270026058 < 306032118
    omega
  · change 306032118 < 1368077562
    omega
  · change 1368077562 < 7799999922
    omega
  · change 7799999922 < 16199999826
    omega
  · change 16199999826 < 22199999790
    omega
  · change 22199999790 < 26999999742
    omega
  · change 26999999742 < 30599999682
    omega
  · change 30599999682 < 136799999232
    omega
  · change 136799999232 < 780000000000
    omega
  · change 780000000000 < 1620000000000
    omega
  · change 1620000000000 < 2220000000000
    omega
  · change 2220000000000 < 2700000000000
    omega
  · change 2700000000000 < 3060000000000
    omega
  · change 3060000000000 < 6*u + 7680000000000
    omega
  · change 6*u + 7680000000000 < 72*u
    omega
  · change 72*u < 90*u
    omega
  · change 90*u < 132*u
    omega
  · change 132*u < 138*u
    omega
  · change 138*u < 168*u
    omega
  · change 6 < 78
    omega
  · change 78 < 174
    omega
  · change 174 < 210
    omega
  · change 210 < 258
    omega
  · change 258 < 318
    omega
  · change 318 < 1368
    omega
  · change 1368 < 7800
    omega
  · change 7800 < 17400
    omega
  · change 17400 < 21000
    omega
  · change 21000 < 25800
    omega
  · change 25800 < 31800
    omega
  · change 31800 < 136200
    omega
  · change 136200 < 772200
    omega
  · change 772200 < 1723800
    omega
  · change 1723800 < 2077800
    omega
  · change 2077800 < 2553000
    omega
  · change 2553000 < 3149400
    omega
  · change 3149400 < 13603806
    omega
  · change 13603806 < 78007878
    omega
  · change 78007878 < 174016362
    omega
  · change 174016362 < 210022422
    omega
  · change 210022422 < 258027270
    omega
  · change 258027270 < 318030906
    omega
  · change 318030906 < 1368077562
    omega
  · change 1368077562 < 7799999922
    omega
  · change 7799999922 < 17399999838
    omega
  · change 17399999838 < 20999999778
    omega
  · change 20999999778 < 25799999730
    omega
  · change 25799999730 < 31799999694
    omega
  · change 31799999694 < 136799999232
    omega
  · change 136799999232 < 780000000000
    omega
  · change 780000000000 < 1740000000000
    omega
  · change 1740000000000 < 2100000000000
    omega
  · change 2100000000000 < 2580000000000
    omega
  · change 2580000000000 < 3180000000000
    omega
  · change 3180000000000 < 6*u + 7680000000000
    omega
  · change 6*u + 7680000000000 < 72*u
    omega
  · change 72*u < 102*u
    omega
  · change 102*u < 108*u
    omega
  · change 108*u < 150*u
    omega
  · change 150*u < 168*u
    omega
  · change 6 < 78
    omega
  · change 78 < 162
    omega
  · change 162 < 222
    omega
  · change 222 < 270
    omega
  · change 270 < 306
    omega
  · change 306 < 1368
    omega
  · change 1368 < 7800
    omega
  · change 7800 < 16200
    omega
  · change 16200 < 22200
    omega
  · change 22200 < 27000
    omega
  · change 27000 < 30600
    omega
  · change 30600 < 137400
    omega
  · change 137400 < 787800
    omega
  · change 787800 < 1637400
    omega
  · change 1637400 < 2241000
    omega
  · change 2241000 < 2725800
    omega
  · change 2725800 < 3091800
    omega
  · change 3091800 < 13756194
    omega
  · change 13756194 < 77992122
    omega
  · change 77992122 < 161982426
    omega
  · change 161982426 < 221978790
    omega
  · change 221978790 < 269973942
    omega
  · change 269973942 < 305967882
    omega
  · change 305967882 < 1367922438
    omega
  · change 1367922438 < 7800000078
    omega
  · change 7800000078 < 16200000174
    omega
  · change 16200000174 < 22200000210
    omega
  · change 22200000210 < 27000000258
    omega
  · change 27000000258 < 30600000318
    omega
  · change 30600000318 < 136800000768
    omega
  · change 136800000768 < 780000000000
    omega
  · change 780000000000 < 1620000000000
    omega
  · change 1620000000000 < 2220000000000
    omega
  · change 2220000000000 < 2700000000000
    omega
  · change 2700000000000 < 3060000000000
    omega
  · change 3060000000000 < 6*u + 7680000000000
    omega
  · change 6*u + 7680000000000 < 72*u
    omega
  · change 72*u < 90*u
    omega
  · change 90*u < 132*u
    omega
  · change 132*u < 138*u
    omega
  · change 138*u < 168*u
    omega

lemma lower_divisible (u : ℕ) (j : Fin 4) (i : Fin 42) :
    6 ∣ digit u j i.castSucc := by
  fin_cases j <;> fin_cases i
  · change 6 ∣ 6
    exact ⟨1, by ring⟩
  · change 6 ∣ 78
    exact ⟨13, by ring⟩
  · change 6 ∣ 174
    exact ⟨29, by ring⟩
  · change 6 ∣ 210
    exact ⟨35, by ring⟩
  · change 6 ∣ 258
    exact ⟨43, by ring⟩
  · change 6 ∣ 318
    exact ⟨53, by ring⟩
  · change 6 ∣ 1368
    exact ⟨228, by ring⟩
  · change 6 ∣ 7800
    exact ⟨1300, by ring⟩
  · change 6 ∣ 17400
    exact ⟨2900, by ring⟩
  · change 6 ∣ 21000
    exact ⟨3500, by ring⟩
  · change 6 ∣ 25800
    exact ⟨4300, by ring⟩
  · change 6 ∣ 31800
    exact ⟨5300, by ring⟩
  · change 6 ∣ 137400
    exact ⟨22900, by ring⟩
  · change 6 ∣ 787800
    exact ⟨131300, by ring⟩
  · change 6 ∣ 1756200
    exact ⟨292700, by ring⟩
  · change 6 ∣ 2122200
    exact ⟨353700, by ring⟩
  · change 6 ∣ 2607000
    exact ⟨434500, by ring⟩
  · change 6 ∣ 3210600
    exact ⟨535100, by ring⟩
  · change 6 ∣ 13756194
    exact ⟨2292699, by ring⟩
  · change 6 ∣ 77992122
    exact ⟨12998687, by ring⟩
  · change 6 ∣ 173983638
    exact ⟨28997273, by ring⟩
  · change 6 ∣ 209977578
    exact ⟨34996263, by ring⟩
  · change 6 ∣ 257972730
    exact ⟨42995455, by ring⟩
  · change 6 ∣ 317969094
    exact ⟨52994849, by ring⟩
  · change 6 ∣ 1367922438
    exact ⟨227987073, by ring⟩
  · change 6 ∣ 7800000078
    exact ⟨1300000013, by ring⟩
  · change 6 ∣ 17400000162
    exact ⟨2900000027, by ring⟩
  · change 6 ∣ 21000000222
    exact ⟨3500000037, by ring⟩
  · change 6 ∣ 25800000270
    exact ⟨4300000045, by ring⟩
  · change 6 ∣ 31800000306
    exact ⟨5300000051, by ring⟩
  · change 6 ∣ 136800000768
    exact ⟨22800000128, by ring⟩
  · change 6 ∣ 780000000000
    exact ⟨130000000000, by ring⟩
  · change 6 ∣ 1740000000000
    exact ⟨290000000000, by ring⟩
  · change 6 ∣ 2100000000000
    exact ⟨350000000000, by ring⟩
  · change 6 ∣ 2580000000000
    exact ⟨430000000000, by ring⟩
  · change 6 ∣ 3180000000000
    exact ⟨530000000000, by ring⟩
  · change 6 ∣ 6*u + 7680000000000
    exact ⟨u + 1280000000000, by ring⟩
  · change 6 ∣ 72*u
    exact ⟨12*u, by ring⟩
  · change 6 ∣ 102*u
    exact ⟨17*u, by ring⟩
  · change 6 ∣ 108*u
    exact ⟨18*u, by ring⟩
  · change 6 ∣ 150*u
    exact ⟨25*u, by ring⟩
  · change 6 ∣ 168*u
    exact ⟨28*u, by ring⟩
  · change 6 ∣ 6
    exact ⟨1, by ring⟩
  · change 6 ∣ 78
    exact ⟨13, by ring⟩
  · change 6 ∣ 162
    exact ⟨27, by ring⟩
  · change 6 ∣ 222
    exact ⟨37, by ring⟩
  · change 6 ∣ 270
    exact ⟨45, by ring⟩
  · change 6 ∣ 306
    exact ⟨51, by ring⟩
  · change 6 ∣ 1368
    exact ⟨228, by ring⟩
  · change 6 ∣ 7800
    exact ⟨1300, by ring⟩
  · change 6 ∣ 16200
    exact ⟨2700, by ring⟩
  · change 6 ∣ 22200
    exact ⟨3700, by ring⟩
  · change 6 ∣ 27000
    exact ⟨4500, by ring⟩
  · change 6 ∣ 30600
    exact ⟨5100, by ring⟩
  · change 6 ∣ 136200
    exact ⟨22700, by ring⟩
  · change 6 ∣ 772200
    exact ⟨128700, by ring⟩
  · change 6 ∣ 1602600
    exact ⟨267100, by ring⟩
  · change 6 ∣ 2199000
    exact ⟨366500, by ring⟩
  · change 6 ∣ 2674200
    exact ⟨445700, by ring⟩
  · change 6 ∣ 3028200
    exact ⟨504700, by ring⟩
  · change 6 ∣ 13603806
    exact ⟨2267301, by ring⟩
  · change 6 ∣ 78007878
    exact ⟨13001313, by ring⟩
  · change 6 ∣ 162017574
    exact ⟨27002929, by ring⟩
  · change 6 ∣ 222021210
    exact ⟨37003535, by ring⟩
  · change 6 ∣ 270026058
    exact ⟨45004343, by ring⟩
  · change 6 ∣ 306032118
    exact ⟨51005353, by ring⟩
  · change 6 ∣ 1368077562
    exact ⟨228012927, by ring⟩
  · change 6 ∣ 7799999922
    exact ⟨1299999987, by ring⟩
  · change 6 ∣ 16199999826
    exact ⟨2699999971, by ring⟩
  · change 6 ∣ 22199999790
    exact ⟨3699999965, by ring⟩
  · change 6 ∣ 26999999742
    exact ⟨4499999957, by ring⟩
  · change 6 ∣ 30599999682
    exact ⟨5099999947, by ring⟩
  · change 6 ∣ 136799999232
    exact ⟨22799999872, by ring⟩
  · change 6 ∣ 780000000000
    exact ⟨130000000000, by ring⟩
  · change 6 ∣ 1620000000000
    exact ⟨270000000000, by ring⟩
  · change 6 ∣ 2220000000000
    exact ⟨370000000000, by ring⟩
  · change 6 ∣ 2700000000000
    exact ⟨450000000000, by ring⟩
  · change 6 ∣ 3060000000000
    exact ⟨510000000000, by ring⟩
  · change 6 ∣ 6*u + 7680000000000
    exact ⟨u + 1280000000000, by ring⟩
  · change 6 ∣ 72*u
    exact ⟨12*u, by ring⟩
  · change 6 ∣ 90*u
    exact ⟨15*u, by ring⟩
  · change 6 ∣ 132*u
    exact ⟨22*u, by ring⟩
  · change 6 ∣ 138*u
    exact ⟨23*u, by ring⟩
  · change 6 ∣ 168*u
    exact ⟨28*u, by ring⟩
  · change 6 ∣ 6
    exact ⟨1, by ring⟩
  · change 6 ∣ 78
    exact ⟨13, by ring⟩
  · change 6 ∣ 174
    exact ⟨29, by ring⟩
  · change 6 ∣ 210
    exact ⟨35, by ring⟩
  · change 6 ∣ 258
    exact ⟨43, by ring⟩
  · change 6 ∣ 318
    exact ⟨53, by ring⟩
  · change 6 ∣ 1368
    exact ⟨228, by ring⟩
  · change 6 ∣ 7800
    exact ⟨1300, by ring⟩
  · change 6 ∣ 17400
    exact ⟨2900, by ring⟩
  · change 6 ∣ 21000
    exact ⟨3500, by ring⟩
  · change 6 ∣ 25800
    exact ⟨4300, by ring⟩
  · change 6 ∣ 31800
    exact ⟨5300, by ring⟩
  · change 6 ∣ 136200
    exact ⟨22700, by ring⟩
  · change 6 ∣ 772200
    exact ⟨128700, by ring⟩
  · change 6 ∣ 1723800
    exact ⟨287300, by ring⟩
  · change 6 ∣ 2077800
    exact ⟨346300, by ring⟩
  · change 6 ∣ 2553000
    exact ⟨425500, by ring⟩
  · change 6 ∣ 3149400
    exact ⟨524900, by ring⟩
  · change 6 ∣ 13603806
    exact ⟨2267301, by ring⟩
  · change 6 ∣ 78007878
    exact ⟨13001313, by ring⟩
  · change 6 ∣ 174016362
    exact ⟨29002727, by ring⟩
  · change 6 ∣ 210022422
    exact ⟨35003737, by ring⟩
  · change 6 ∣ 258027270
    exact ⟨43004545, by ring⟩
  · change 6 ∣ 318030906
    exact ⟨53005151, by ring⟩
  · change 6 ∣ 1368077562
    exact ⟨228012927, by ring⟩
  · change 6 ∣ 7799999922
    exact ⟨1299999987, by ring⟩
  · change 6 ∣ 17399999838
    exact ⟨2899999973, by ring⟩
  · change 6 ∣ 20999999778
    exact ⟨3499999963, by ring⟩
  · change 6 ∣ 25799999730
    exact ⟨4299999955, by ring⟩
  · change 6 ∣ 31799999694
    exact ⟨5299999949, by ring⟩
  · change 6 ∣ 136799999232
    exact ⟨22799999872, by ring⟩
  · change 6 ∣ 780000000000
    exact ⟨130000000000, by ring⟩
  · change 6 ∣ 1740000000000
    exact ⟨290000000000, by ring⟩
  · change 6 ∣ 2100000000000
    exact ⟨350000000000, by ring⟩
  · change 6 ∣ 2580000000000
    exact ⟨430000000000, by ring⟩
  · change 6 ∣ 3180000000000
    exact ⟨530000000000, by ring⟩
  · change 6 ∣ 6*u + 7680000000000
    exact ⟨u + 1280000000000, by ring⟩
  · change 6 ∣ 72*u
    exact ⟨12*u, by ring⟩
  · change 6 ∣ 102*u
    exact ⟨17*u, by ring⟩
  · change 6 ∣ 108*u
    exact ⟨18*u, by ring⟩
  · change 6 ∣ 150*u
    exact ⟨25*u, by ring⟩
  · change 6 ∣ 168*u
    exact ⟨28*u, by ring⟩
  · change 6 ∣ 6
    exact ⟨1, by ring⟩
  · change 6 ∣ 78
    exact ⟨13, by ring⟩
  · change 6 ∣ 162
    exact ⟨27, by ring⟩
  · change 6 ∣ 222
    exact ⟨37, by ring⟩
  · change 6 ∣ 270
    exact ⟨45, by ring⟩
  · change 6 ∣ 306
    exact ⟨51, by ring⟩
  · change 6 ∣ 1368
    exact ⟨228, by ring⟩
  · change 6 ∣ 7800
    exact ⟨1300, by ring⟩
  · change 6 ∣ 16200
    exact ⟨2700, by ring⟩
  · change 6 ∣ 22200
    exact ⟨3700, by ring⟩
  · change 6 ∣ 27000
    exact ⟨4500, by ring⟩
  · change 6 ∣ 30600
    exact ⟨5100, by ring⟩
  · change 6 ∣ 137400
    exact ⟨22900, by ring⟩
  · change 6 ∣ 787800
    exact ⟨131300, by ring⟩
  · change 6 ∣ 1637400
    exact ⟨272900, by ring⟩
  · change 6 ∣ 2241000
    exact ⟨373500, by ring⟩
  · change 6 ∣ 2725800
    exact ⟨454300, by ring⟩
  · change 6 ∣ 3091800
    exact ⟨515300, by ring⟩
  · change 6 ∣ 13756194
    exact ⟨2292699, by ring⟩
  · change 6 ∣ 77992122
    exact ⟨12998687, by ring⟩
  · change 6 ∣ 161982426
    exact ⟨26997071, by ring⟩
  · change 6 ∣ 221978790
    exact ⟨36996465, by ring⟩
  · change 6 ∣ 269973942
    exact ⟨44995657, by ring⟩
  · change 6 ∣ 305967882
    exact ⟨50994647, by ring⟩
  · change 6 ∣ 1367922438
    exact ⟨227987073, by ring⟩
  · change 6 ∣ 7800000078
    exact ⟨1300000013, by ring⟩
  · change 6 ∣ 16200000174
    exact ⟨2700000029, by ring⟩
  · change 6 ∣ 22200000210
    exact ⟨3700000035, by ring⟩
  · change 6 ∣ 27000000258
    exact ⟨4500000043, by ring⟩
  · change 6 ∣ 30600000318
    exact ⟨5100000053, by ring⟩
  · change 6 ∣ 136800000768
    exact ⟨22800000128, by ring⟩
  · change 6 ∣ 780000000000
    exact ⟨130000000000, by ring⟩
  · change 6 ∣ 1620000000000
    exact ⟨270000000000, by ring⟩
  · change 6 ∣ 2220000000000
    exact ⟨370000000000, by ring⟩
  · change 6 ∣ 2700000000000
    exact ⟨450000000000, by ring⟩
  · change 6 ∣ 3060000000000
    exact ⟨510000000000, by ring⟩
  · change 6 ∣ 6*u + 7680000000000
    exact ⟨u + 1280000000000, by ring⟩
  · change 6 ∣ 72*u
    exact ⟨12*u, by ring⟩
  · change 6 ∣ 90*u
    exact ⟨15*u, by ring⟩
  · change 6 ∣ 132*u
    exact ⟨22*u, by ring⟩
  · change 6 ∣ 138*u
    exact ⟨23*u, by ring⟩
  · change 6 ∣ 168*u
    exact ⟨28*u, by ring⟩

lemma canonical (u : ℕ) (hu : 1000000000000 ≤ u) (j : Fin 4) (i : Fin 43) :
    0 < digit u j i ∧ digit u j i < base u := by
  fin_cases j <;> fin_cases i <;> norm_num [digit, base] <;> omega

lemma common_sum (u : ℕ) (j : Fin 4) :
    (∑ i : Fin 43, digit u j i) = 606*u + 18303030303013 := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ, digit] <;> ring

lemma common_norm (u : ℕ) (j : Fin 4) :
    (∑ i : Fin 43, digit u j i ^ 2) =
      78012*u^2 + 92160000000000*u + 83818397839783995233264809 := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ, digit] <;> ring

lemma word_injective (u : ℕ) : Function.Injective (word u) := by
  intro i j h
  have he : digit u i = digit u j := List.ofFn_inj.mp h
  have h2 := congrFun he 2
  have h12 := congrFun he 12
  fin_cases i <;> fin_cases j
  · rfl
  · change 174 = 162 at h2
    omega
  · change 137400 = 136200 at h12
    omega
  · change 174 = 162 at h2
    omega
  · change 162 = 174 at h2
    omega
  · rfl
  · change 162 = 174 at h2
    omega
  · change 136200 = 137400 at h12
    omega
  · change 136200 = 137400 at h12
    omega
  · change 174 = 162 at h2
    omega
  · rfl
  · change 174 = 162 at h2
    omega
  · change 162 = 174 at h2
    omega
  · change 137400 = 136200 at h12
    omega
  · change 162 = 174 at h2
    omega
  · rfl

lemma word_digits (u : ℕ) (hu : 1000000000000 ≤ u) (j : Fin 4) :
    ∀ x ∈ word u j, x < base u := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (canonical u hu j i).2

lemma root_injective (u : ℕ) (hu : 1000000000000 ≤ u) :
    Function.Injective (root u) := by
  intro i j h
  apply word_injective u
  exact Nat.ofDigits_inj_of_len_eq (by dsimp [base]; omega)
    (by simp [word]) (word_digits u hu i) (word_digits u hu j) h

lemma root_positive (u : ℕ) (j : Fin 4) : 0 < root u j := by
  fin_cases j <;> simp [root, word, digit, List.ofFn_succ, Nat.ofDigits_cons]

lemma root_height (u : ℕ) (hu : 1000000000000 ≤ u) (j : Fin 4) :
    root u j < base u ^ 43 := by
  have h := Nat.ofDigits_lt_base_pow_length
    (by dsimp [base]; omega : 1 < base u) (word_digits u hu j)
  simpa [root, word] using h

/-- The exact discrepancy has the carry factor `600*u-B-1`. -/
lemma discrepancy (B u : ℕ) :
    (Nat.ofDigits B (word u 0) : ℤ)^2 + (Nat.ofDigits B (word u 1) : ℤ)^2 -
      (Nat.ofDigits B (word u 2) : ℤ)^2 - (Nat.ofDigits B (word u 3) : ℤ)^2 =
    8 * (6*(B:ℤ)^2-12*(B:ℤ)^3+6*(B:ℤ)^4) *
      (100*(B:ℤ)^12-101*(B:ℤ)^18+(B:ℤ)^24) * (B:ℤ)^42 *
      (600*(u:ℤ)-(B:ℤ)-1) := by
  change (Nat.ofDigits B [6, 78, 174, 210, 258, 318, 1368, 7800, 17400, 21000, 25800, 31800, 137400, 787800, 1756200, 2122200, 2607000, 3210600, 13756194, 77992122, 173983638, 209977578, 257972730, 317969094, 1367922438, 7800000078, 17400000162, 21000000222, 25800000270, 31800000306, 136800000768, 780000000000, 1740000000000, 2100000000000, 2580000000000, 3180000000000, 6*u + 7680000000000, 72*u, 102*u, 108*u, 150*u, 168*u, 1] : ℤ)^2 + (Nat.ofDigits B [6, 78, 162, 222, 270, 306, 1368, 7800, 16200, 22200, 27000, 30600, 136200, 772200, 1602600, 2199000, 2674200, 3028200, 13603806, 78007878, 162017574, 222021210, 270026058, 306032118, 1368077562, 7799999922, 16199999826, 22199999790, 26999999742, 30599999682, 136799999232, 780000000000, 1620000000000, 2220000000000, 2700000000000, 3060000000000, 6*u + 7680000000000, 72*u, 90*u, 132*u, 138*u, 168*u, 1] : ℤ)^2 - (Nat.ofDigits B [6, 78, 174, 210, 258, 318, 1368, 7800, 17400, 21000, 25800, 31800, 136200, 772200, 1723800, 2077800, 2553000, 3149400, 13603806, 78007878, 174016362, 210022422, 258027270, 318030906, 1368077562, 7799999922, 17399999838, 20999999778, 25799999730, 31799999694, 136799999232, 780000000000, 1740000000000, 2100000000000, 2580000000000, 3180000000000, 6*u + 7680000000000, 72*u, 102*u, 108*u, 150*u, 168*u, 1] : ℤ)^2 - (Nat.ofDigits B [6, 78, 162, 222, 270, 306, 1368, 7800, 16200, 22200, 27000, 30600, 137400, 787800, 1637400, 2241000, 2725800, 3091800, 13756194, 77992122, 161982426, 221978790, 269973942, 305967882, 1367922438, 7800000078, 16200000174, 22200000210, 27000000258, 30600000318, 136800000768, 780000000000, 1620000000000, 2220000000000, 2700000000000, 3060000000000, 6*u + 7680000000000, 72*u, 90*u, 132*u, 138*u, 168*u, 1] : ℤ)^2 = _
  simp only [Nat.ofDigits, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma square_collision (u : ℕ) (hu : 1 ≤ u) :
    root u 0 ^ 2 + root u 1 ^ 2 = root u 2 ^ 2 + root u 3 ^ 2 := by
  have hb : (base u : ℤ) + 1 = 600*(u:ℤ) := by
    have h : base u + 1 = 600*u := by dsimp [base]; omega
    exact_mod_cast h
  have hd := discrepancy (base u) u
  have hz : 600*(u:ℤ)-(base u:ℤ)-1 = 0 := by omega
  rw [hz, mul_zero] at hd
  change (root u 0 : ℤ)^2 + (root u 1 : ℤ)^2 -
    (root u 2 : ℤ)^2 - (root u 3 : ℤ)^2 = 0 at hd
  have he : (root u 0 : ℤ)^2 + (root u 1 : ℤ)^2 =
      (root u 2 : ℤ)^2 + (root u 3 : ℤ)^2 := by linarith
  exact_mod_cast he

private lemma image_not_sidon (f : Fin 4 → ℕ) (hf : Function.Injective f)
    (he : f 0 + f 1 = f 2 + f 3) :
    ¬ IsSidon ((univ.image f) : Set ℕ) := by
  intro h
  have hm (j : Fin 4) : f j ∈ (univ.image f : Finset ℕ) :=
    mem_image.mpr ⟨j, mem_univ j, rfl⟩
  rcases h _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) he with h | h
  · exact (by decide : (0 : Fin 4) ≠ 2) (hf h.1)
  · exact (by decide : (0 : Fin 4) ≠ 3) (hf h.1)

theorem not_sidon (u : ℕ) (hu : 1000000000000 ≤ u) :
    ¬ IsSidon ((univ.image (fun j : Fin 4 => root u j ^ 2)) : Set ℕ) := by
  apply image_not_sidon
  · intro i j h
    exact root_injective u hu (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h)
  · exact square_collision u (by omega)

#print axioms lower_increasing
#print axioms lower_divisible
#print axioms canonical
#print axioms common_sum
#print axioms common_norm
#print axioms discrepancy
#print axioms not_sidon
end Erdos773.OrderedEisensteinMomentCollision
